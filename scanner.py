#!/usr/bin/env python3
"""
BSE + NSE announcement scanner.

Runs once a night. Every run it:
  1. pulls all new equity announcements from BSE and NSE (catching up on any
     night that failed),
  2. opens preferential issue and board meeting documents and emails you only
     when a name on your allottee watchlist appears,
  3. does the same for SAST / takeover disclosures and your SAST watchlist,
  4. sends one summary email at the end, so you know it ran and what it covered.

All settings come from environment variables (GitHub Secrets) - see SETUP.md.
"""
import hashlib
import io
import json
import os
import re
import smtplib
import sys
import tempfile
import time
from datetime import datetime, timedelta, timezone
from email.message import EmailMessage

import requests

IST = timezone(timedelta(hours=5, minutes=30))
STATE_FILE = os.environ.get("STATE_FILE", "state.json")
DRY_RUN = os.environ.get("DRY_RUN") == "1"
TIME_BUDGET = int(os.environ.get("TIME_BUDGET_SECONDS", "210"))
MAX_DOCS = int(os.environ.get("MAX_DOCS_PER_RUN", "60"))
MAX_PDF_BYTES = 25 * 1024 * 1024
STALE_PAGE_LIMIT = int(os.environ.get("STALE_PAGE_LIMIT", "2"))
BSE_RETRIES = int(os.environ.get("BSE_RETRIES", "4"))
BSE_RETRY_WAIT = int(os.environ.get("BSE_RETRY_WAIT_SECONDS", "60"))
UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/130.0.0.0 Safari/537.36")

# --- what counts as what -----------------------------------------------------
PREF_META = re.compile(r"preferential", re.I)
PREF_TEXT = re.compile(
    r"preferential\s+(issue|allotment|basis|offer)|on\s+a?\s*preferential", re.I)
SAST_META = re.compile(r"\bSAST\b|substantial\s+acquisition|take\s?over", re.I)
SAST_SKIP = re.compile(r"trading\s+window", re.I)
# Announcements whose subject does not say "preferential" but whose document
# often does. These are opened and searched.
DEEP_META = re.compile(
    r"outcome\s+of\s+(the\s+)?board|board\s+meeting|allotment|issue\s+of\s+securities"
    r"|issuance\s+of|fund\s*rais|raising\s+of\s+funds|warrants"
    r"|extra.?ordinary\s+general|\bEGM\b|postal\s+ballot", re.I)


# --- settings ----------------------------------------------------------------
def name_list(var):
    raw = os.environ.get(var, "")
    names = [n.strip() for n in re.split(r"[\n;]+", raw)]
    return [n for n in names if n and not n.startswith("#")]


ALLOTTEE_NAMES = name_list("ALLOTTEE_NAMES")
SAST_NAMES = name_list("SAST_NAMES")
SAST_ALERT_ALL = os.environ.get("SAST_ALERT_ALL") == "1"
PREF_ALERT_ALL = os.environ.get("PREF_ALERT_ALL") == "1"
EMAIL_USER = os.environ.get("EMAIL_USER", "")
EMAIL_PASS = os.environ.get("EMAIL_APP_PASSWORD", "").replace(" ", "")
EMAIL_TO = [a.strip() for a in
            re.split(r"[,;\s]+", os.environ.get("EMAIL_TO", "") or EMAIL_USER)
            if a.strip()]
SMTP_HOST = os.environ.get("SMTP_HOST", "") or "smtp.gmail.com"
SMTP_PORT = int(os.environ.get("SMTP_PORT", "") or "465")


# --- name matching -----------------------------------------------------------
CANON = {"private": "pvt", "limited": "ltd", "&": "and"}
FILLER = {"pvt", "ltd", "llp", "llc", "inc", "mr", "mrs", "ms", "shri", "smt",
          "and", "the", "huf", "m", "s", "dr"}
# words that cannot sit in the middle of one person's name
BREAK = FILLER | {"of", "by", "for", "to", "with", "in", "on", "at", "or", "from",
                  "son", "wife", "daughter", "director", "name", "no"}


def norm(text):
    text = (text or "").lower().replace("&", " and ")
    words = re.sub(r"[^a-z0-9]+", " ", text).split()
    return " ".join(CANON.get(w, w) for w in words)


def match_names(names, text_norm):
    """Returns [(name, 'exact'|'possible', context)] for names found in text."""
    if not names or not text_norm:
        return []
    hay = " " + text_norm + " "
    words = text_norm.split()
    where = {}
    squashed = None
    hits = []
    for name in names:
        n = norm(name)
        if not n:
            continue
        pos = hay.find(" " + n + " ")
        if pos >= 0:
            ctx = hay[max(0, pos - 90): pos + len(n) + 90].strip()
            hits.append((name, "exact", ctx))
            continue
        # same letters with different spacing or hyphens ("Multi-Horizons")
        tight = n.replace(" ", "")
        if len(tight) >= 12:
            if squashed is None:
                squashed = text_norm.replace(" ", "")
            if tight in squashed:
                hits.append((name, "possible", "same letters, different spacing: " + name))
                continue
        # looser: the same words next to each other in any order, with at most one
        # extra word in between (surname first, a middle name, an initial spelt out)
        toks = [t for t in n.split() if t not in FILLER and len(t) > 1]
        if len(toks) < 2:
            continue
        if not where:
            for i, w in enumerate(words):
                where.setdefault(w, []).append(i)
        if any(t not in where for t in toks):
            continue
        rare = min(toks, key=lambda t: len(where[t]))
        for p in where[rare]:
            seg = near_match(toks, words, p)
            if seg:
                ctx = " ".join(words[max(0, p - 12): p + 12])
                hits.append((name, "possible", ctx))
                break
    return hits


def near_match(toks, words, p):
    """True if every word of the name sits in one short run of words around p."""
    n = len(toks)
    for start in range(max(0, p - n), p + 1):
        win = words[start: start + n + 1]
        idx = [i for i, w in enumerate(win) if w in toks]
        if not idx:
            continue
        seg = win[idx[0]: idx[-1] + 1]
        if any(t not in seg for t in toks):
            continue
        extra = [w for w in seg if w not in toks]
        if len(extra) <= 1 and all(w.isalpha() and w not in BREAK for w in extra):
            return True
    return False


# --- reading documents -------------------------------------------------------
def download(urls, referer):
    for url in urls:
        try:
            if url.startswith("file://"):
                with open(url[7:], "rb") as fh:
                    return fh.read()
            r = requests.get(url, timeout=40, stream=True,
                             headers={"User-Agent": UA, "Referer": referer})
            if r.status_code != 200:
                continue
            buf = io.BytesIO()
            for chunk in r.iter_content(65536):
                buf.write(chunk)
                if buf.tell() > MAX_PDF_BYTES:
                    break
            data = buf.getvalue()
            if data[:1024].lstrip().startswith(b"%PDF"):
                return data
        except Exception:
            continue
    return None


def ocr_pages(data, page_numbers):
    """OCR for scanned pages. Quietly returns {} if OCR is not installed."""
    out = {}
    try:
        import pypdfium2
        import pytesseract
        pdf = pypdfium2.PdfDocument(data)
        for i in page_numbers:
            image = pdf[i].render(scale=2).to_pil()
            out[i] = pytesseract.image_to_string(image)
    except Exception:
        pass
    return out


def read_document(item, deadline, ocr_limit=10):
    """Returns (text, readable). readable is False when we could not get text."""
    referer = ("https://www.bseindia.com/" if item["exch"] == "BSE"
               else "https://www.nseindia.com/")
    data = download(item.get("pdfs") or [], referer)
    if not data:
        return "", False
    pages, blank = [], []
    try:
        from pypdf import PdfReader
        reader = PdfReader(io.BytesIO(data))
        for i, page in enumerate(reader.pages[:40]):
            if time.time() > deadline:
                break
            try:
                t = page.extract_text() or ""
            except Exception:
                t = ""
            pages.append(t)
            if len(t.strip()) < 60:
                blank.append(i)
    except Exception:
        return "", False
    if blank and time.time() < deadline:
        for i, t in ocr_pages(data, blank[:ocr_limit]).items():
            pages[i] = t
    text = "\n".join(pages)
    return text, len(text.strip()) >= 300


# --- fetching announcements --------------------------------------------------
def short_id(prefix, raw):
    return prefix + hashlib.sha1(str(raw).encode()).hexdigest()[:12]


def bse_row(r, sid):
    att = (r.get("ATTACHMENTNAME") or "").strip()
    base = "https://www.bseindia.com/xml-data/corpfiling/"
    return {
        "id": sid, "exch": "BSE",
        "company": (r.get("SLONGNAME") or "").strip(),
        "code": str(r.get("SCRIP_CD") or ""),
        "subject": r.get("NEWSSUB") or "",
        "summary": " ".join(filter(None, [r.get("HEADLINE"), r.get("MORE")])),
        "category": " ".join(filter(None, [r.get("CATEGORYNAME"), r.get("SUBCATNAME")])),
        "time": str(r.get("DissemDT") or r.get("NEWS_DT") or "")[:19],
        "pdfs": [base + "AttachLive/" + att, base + "AttachHis/" + att] if att else [],
        "page": r.get("NSURL") or "",
    }


def fetch_bse_day(day, seen):
    """All equity announcements BSE lists for one date. Returns (new items, rows listed)."""
    from bse import BSE
    when = datetime(day.year, day.month, day.day)
    items, fetched, stale_pages = [], 0, 0
    with BSE(download_folder=tempfile.mkdtemp()) as api:
        for page in range(1, 301):
            data = None
            for attempt in range(3):
                try:
                    data = api.announcements(page_no=page, from_date=when, to_date=when)
                    break
                except Exception:
                    if attempt == 2:
                        raise
                    time.sleep(5)
            rows = data.get("Table") or []
            if not rows:
                break
            fetched += len(rows)
            fresh = 0
            for r in rows:
                sid = short_id("B", r.get("NEWSID"))
                if sid in seen:
                    continue
                fresh += 1
                items.append(bse_row(r, sid))
            stale_pages = 0 if fresh else stale_pages + 1
            total = ((data.get("Table1") or [{}])[0] or {}).get("ROWCNT") or 0
            if stale_pages >= STALE_PAGE_LIMIT or (total and fetched >= total):
                break
    return items, fetched


def fetch_bse(seen, days):
    """Each date is asked for separately. A past date that comes back empty is
    retried, because BSE sometimes answers a cloud server with nothing. The last
    date may honestly be empty (the run often starts just after midnight)."""
    items, counts = [], {}
    for n, day in enumerate(days):
        tries = BSE_RETRIES if n < len(days) - 1 else 1
        got, listed = [], 0
        for attempt in range(tries):
            got, listed = fetch_bse_day(day, seen)
            if listed:
                break
            if attempt < tries - 1:
                time.sleep(BSE_RETRY_WAIT)
        counts[day.strftime("%d-%b")] = listed
        known = {i["id"] for i in items}
        items += [i for i in got if i["id"] not in known]
    if not sum(counts.values()):
        raise RuntimeError("BSE returned no announcements at all: %s" % counts)
    return items, counts


def nse_open():
    """Opens NSE. If the site answers that it has moved to another nseindia
    address, every request is pointed at that address and it is tried again."""
    from nse import NSE
    try:
        return NSE(download_folder=tempfile.mkdtemp())
    except Exception as exc:
        resp = getattr(exc, "response", None)
        target = resp.headers.get("location", "") if resp is not None else ""
        host = re.match(r"https://(www\.nseindia\.[a-z.]{2,6})(/|$)", target)
        if not host or host.group(1) == "www.nseindia.com" or NSE_MOVED:
            raise
        NSE_MOVED.append(host.group(1))
        from nse import transport
        original = transport.Transport.request

        def request(self, url, params=None):
            return original(self, url.replace("//www.nseindia.com", "//" + NSE_MOVED[0]), params)
        transport.Transport.request = request
        print("NSE has moved to %s - using that address" % NSE_MOVED[0])
        return NSE(download_folder=tempfile.mkdtemp())


NSE_MOVED = []


def fetch_nse(seen, start, today):
    items, listed = [], {}
    with nse_open() as api:
        for index in ("equities", "sme"):
            rows = api.announcements(index=index, from_date=start, to_date=today)
            listed[index] = len(rows or [])
            for r in rows or []:
                raw = r.get("seq_id") or (r.get("symbol"), r.get("an_dt"), r.get("desc"))
                sid = short_id("N", raw)
                if sid in seen:
                    continue
                att = (r.get("attchmntFile") or "").strip()
                items.append({
                    "id": sid, "exch": "NSE",
                    "company": (r.get("sm_name") or r.get("symbol") or "").strip(),
                    "code": r.get("symbol") or "",
                    "subject": r.get("desc") or "",
                    "summary": r.get("attchmntText") or "",
                    "category": "",
                    "time": r.get("an_dt") or "",
                    "pdfs": [att] if att.lower().endswith(".pdf") else [],
                    "page": "",
                })
    return items, listed


def fetch_nse_sast(seen, start, today):
    """NSE keeps Regulation 29 (SAST) disclosures in their own list, with the
    acquirer's name as data, so names are matched without opening a document."""
    items, listed = [], 0
    with nse_open() as api:
        data = api._transport.request(
            api.base_url + "/corporate-sast-reg29",
            params={"index": "equities",
                    "from_date": start.strftime("%d-%m-%Y"),
                    "to_date": today.strftime("%d-%m-%Y")}).json()
    rows = data.get("data") if isinstance(data, dict) else data
    for r in rows or []:
        if not isinstance(r, dict):
            continue
        listed += 1
        values = [str(v) for v in r.values() if v not in (None, "")]
        sid = short_id("S", "|".join(sorted(values)))
        if sid in seen:
            continue
        pdfs = [v for v in values if v.lower().startswith("http") and ".pdf" in v.lower()]
        items.append({
            "id": sid, "exch": "NSE",
            "company": str(r.get("company") or r.get("sm_name") or r.get("symbol") or ""),
            "code": str(r.get("symbol") or ""),
            "subject": "Regulation 29 (SAST) disclosure",
            "summary": " | ".join(v for v in values if not v.lower().startswith("http"))[:900],
            "category": "SAST",
            "time": str(r.get("timestamp") or r.get("date") or r.get("acquirerDate") or ""),
            "pdfs": pdfs[:1], "page": "", "row": True,
        })
    return items, listed


# --- email -------------------------------------------------------------------
class Mailer:
    def __init__(self):
        self.conn = None
        self.sent = 0

    def send(self, subject, body):
        if DRY_RUN:
            print("\n=== EMAIL ===\nSubject: " + subject + "\n" + body)
            self.sent += 1
            return
        if not (EMAIL_USER and EMAIL_PASS and EMAIL_TO):
            raise RuntimeError("Email secrets are missing - see SETUP.md")
        msg = EmailMessage()
        msg["From"] = EMAIL_USER
        msg["To"] = ", ".join(EMAIL_TO)
        msg["Subject"] = subject[:240]
        msg.set_content(body)
        for attempt in range(2):
            try:
                if self.conn is None:
                    self.conn = smtplib.SMTP_SSL(SMTP_HOST, SMTP_PORT, timeout=30)
                    self.conn.login(EMAIL_USER, EMAIL_PASS)
                self.conn.send_message(msg)
                self.sent += 1
                return
            except Exception:
                self.conn = None
                if attempt == 1:
                    raise

    def close(self):
        try:
            if self.conn:
                self.conn.quit()
        except Exception:
            pass


def describe(item):
    lines = [
        "Company : %s (%s %s)" % (item["company"], item["exch"], item["code"]),
        "Filed   : %s" % item["time"],
        "Subject : %s" % item["subject"],
    ]
    if item["summary"]:
        lines.append("Summary : %s" % item["summary"][:600])
    if item["pdfs"]:
        lines.append("Document: %s" % item["pdfs"][0])
    if item["page"]:
        lines.append("Company page: %s" % item["page"])
    return "\n".join(lines)


def hit_lines(hits):
    out = []
    for name, kind, ctx in hits:
        label = "MATCH" if kind == "exact" else "POSSIBLE MATCH (words found close together)"
        out.append("%s: %s\n   ...%s..." % (label, name, ctx))
    return "\n".join(out)


# --- deciding and alerting ---------------------------------------------------
def filed_on(item):
    stamp = item.get("time") or ""
    for fmt, size in (("%Y-%m-%d", 10), ("%d-%b-%Y", 11)):
        try:
            return datetime.strptime(stamp[:size], fmt).strftime("%Y-%m-%d")
        except ValueError:
            pass
    return datetime.now(IST).strftime("%Y-%m-%d")


def already_alerted(state, group, item, hits):
    """Stops the same match being emailed twice (both exchanges, or repeat filings)."""
    names = ",".join(sorted(h[0] for h in hits))
    raw = "|".join([EMAIL_PASS or "x", group, norm(item["company"]), filed_on(item), names])
    key = hashlib.sha1(raw.encode()).hexdigest()[:14]
    if key in state["alerted"]:
        return True
    state["alerted"][key] = item["exch"][0]
    state["alerted_on"][key] = datetime.now(IST).strftime("%Y-%m-%d")
    return False


def match_label(hits):
    sure = any(h[1] == "exact" for h in hits)
    return ("MATCH" if sure else "POSSIBLE MATCH") + ": " + ", ".join(h[0] for h in hits)


def link_of(item):
    return (item["pdfs"] or [item["page"]])[0]


def handle(job, state, mailer, deadline, run):
    """Returns True if a document was opened."""
    item, kind = job["item"], job["kind"]
    meta = " ".join([item["subject"], item["summary"], item["category"]])

    if kind == "sast" and item.get("row"):
        # NSE's SAST list: the names are in the data itself
        run["sast_checked"] += 1
        hits = match_names(SAST_NAMES, norm(meta))
        if (hits or SAST_ALERT_ALL) and not already_alerted(state, "sast", item, hits):
            mailer.send("SAST %s - %s" % (match_label(hits), item["company"]) if hits
                        else "SAST filing: %s" % item["company"],
                        (hit_lines(hits) + "\n\n" if hits else "") + describe(item))
            run["sast_match"] += bool(hits)
        return False

    # board-meeting documents are numerous, so only their first pages get OCR
    text, readable = read_document(item, deadline, 2 if kind == "pref_deep" else 10)
    run["opened" if readable else "unopened"] += 1
    everything = norm(meta + " " + text)

    if kind == "sast":
        run["sast_checked"] += 1
        hits = match_names(SAST_NAMES, everything)
        if (hits or SAST_ALERT_ALL) and not already_alerted(state, "sast", item, hits):
            mailer.send("SAST %s - %s" % (match_label(hits), item["company"]) if hits
                        else "SAST filing: %s" % item["company"],
                        (hit_lines(hits) + "\n\n" if hits else "") + describe(item))
            run["sast_match"] += bool(hits)
        if not hits and not readable:
            run["unread_sast"].append([item["company"], link_of(item)])
        return True

    note = ""
    if kind == "pref_deep":
        found = PREF_TEXT.search(text)
        if not found:
            return True
        snippet = " ".join(text[max(0, found.start() - 200): found.end() + 250].split())
        note = ("The subject line does not say 'preferential' - it was found inside "
                "the document, so this may be a passing reference:\n   ..."
                + snippet + "...\n\n")
    run["pref_found"] += 1

    hits = match_names(ALLOTTEE_NAMES, everything)
    if not hits and not readable:
        run["unread_pref"].append([item["company"], link_of(item)])
    if not (hits or PREF_ALERT_ALL) or already_alerted(state, "pref", item, hits):
        return True
    if hits:
        mailer.send("PREF %s - %s" % (match_label(hits), item["company"]),
                    hit_lines(hits) + "\n\n" + note + describe(item))
        run["pref_match"] += 1
    else:
        mailer.send("PREF ISSUE: %s (no watchlist name)" % item["company"],
                    note + describe(item))
    return True


def classify(item):
    meta = " ".join([item["subject"], item["summary"], item["category"]])
    kinds = []
    if PREF_META.search(meta):
        kinds.append("pref_meta")
    elif DEEP_META.search(meta) and item["pdfs"]:
        kinds.append("pref_deep")
    if (SAST_META.search(meta) and not SAST_SKIP.search(meta)
            and (SAST_NAMES or SAST_ALERT_ALL)):
        kinds.append("sast")
    return kinds


# --- state -------------------------------------------------------------------
def load_state():
    state = {}
    try:
        with open(STATE_FILE) as fh:
            state = json.load(fh)
    except Exception:
        pass
    state.setdefault("seen", {})
    state.setdefault("pending", [])
    state.setdefault("alerted", {})
    state.setdefault("alerted_on", {})
    return state


def send_summary(run, mailer, when):
    def feed(status, counts):
        if status == "OK":
            return "OK - %s" % ", ".join("%s: %d" % kv for kv in counts.items())
        return status
    matches = run["pref_match"] + run["sast_match"]
    lines = [
        "Scanner run of %s IST." % when.strftime("%d %b %Y, %H:%M"),
        "",
        "Name matches emailed  : %d (preferential %d, SAST %d)" % (
            matches, run["pref_match"], run["sast_match"]),
        "New filings checked   : BSE %d, NSE %d" % (run["new_BSE"], run["new_NSE"]),
        "Preferential filings  : %d found and checked against your %d names" % (
            run["pref_found"], len(ALLOTTEE_NAMES)),
        "SAST filings          : %d checked against your %d names" % (
            run["sast_checked"], len(SAST_NAMES)),
        "Documents             : %d read, %d could not be read" % (
            run["opened"], run["unopened"]),
        "",
        "BSE feed              : %s" % feed(run["bse"], run["bse_counts"]),
        "NSE feed              : %s" % feed(run["nse"], run["nse_counts"]),
        "NSE SAST list         : %s" % run["nse_sast"],
    ]
    if run["bse"] != "OK":
        lines += ["", "BSE filings were NOT checked in this run. The next run catches "
                      "up automatically; you can also press Run workflow now."]
    if run["left"]:
        lines += ["", "%d documents were left for the next run (time limit)." % run["left"]]
    for title, rows in (("Preferential issue filings", run["unread_pref"]),
                        ("SAST filings", run["unread_sast"])):
        if rows:
            lines += ["", "%s whose document could not be read (%d) - names were NOT "
                          "checked, open these yourself:" % (title, len(rows))]
            lines += ["  %s  %s" % (c, u) for c, u in rows[:150]]
    flag = "" if run["bse"] == "OK" else "BSE FAILED - "
    mailer.send("%sScanner summary %s: %d name match%s" % (
        flag, when.strftime("%d %b"), matches, "" if matches == 1 else "es"),
        "\n".join(lines))


# --- main --------------------------------------------------------------------
def catch_up_days(last_ok, today, first_run):
    """Dates to ask for: from the last night that worked (so a failed night is
    caught up automatically), at most 5 days back."""
    start = today if first_run else today - timedelta(days=1)
    if last_ok:
        try:
            start = min(start, datetime.strptime(last_ok, "%Y-%m-%d").date())
        except ValueError:
            pass
    start = max(start, today - timedelta(days=5))
    return [start + timedelta(days=n) for n in range((today - start).days + 1)]


def main():
    started = time.time()
    deadline = started + TIME_BUDGET
    now = datetime.now(IST)
    today = now.date()
    today_str = today.strftime("%Y-%m-%d")
    state = load_state()
    first_run = not state["seen"]
    mailer = Mailer()
    failed = False

    run = {"new_BSE": 0, "new_NSE": 0, "pref_found": 0, "pref_match": 0,
           "sast_checked": 0, "sast_match": 0, "opened": 0, "unopened": 0,
           "unread_pref": [], "unread_sast": [], "left": 0,
           "bse": "not run", "nse": "not run", "nse_sast": "not run",
           "bse_counts": {}, "nse_counts": {}}
    state.pop("day", None)

    # 1. fetch
    items = []
    fixture = os.environ.get("SCANNER_FIXTURE")
    if fixture:
        with open(fixture) as fh:
            items = [i for i in json.load(fh) if i["id"] not in state["seen"]]
        run["bse"] = run["nse"] = "OK"
    else:
        try:
            days = catch_up_days(state.get("bse_ok"), today, first_run)
            got, run["bse_counts"] = fetch_bse(state["seen"], days)
            items += got
            state["bse_ok"] = today_str
            run["bse"] = "OK"
        except Exception as exc:
            failed = True
            run["bse"] = "FAILED"
            print("BSE fetch failed:", type(exc).__name__, str(exc)[:200])
        days = catch_up_days(state.get("nse_ok"), today, first_run)
        try:
            got, run["nse_counts"] = fetch_nse(state["seen"], days[0], today)
            items += got
            if sum(run["nse_counts"].values()):
                state["nse_ok"] = today_str
                run["nse"] = "OK"
                if NSE_MOVED:
                    run["nse_counts"]["via " + NSE_MOVED[0]] = 1
            else:
                run["nse"] = "connected but returned no filings - coverage was BSE only"
        except Exception as exc:
            run["nse"] = "NOT reachable - coverage was BSE only"
            print("NSE not reachable this run:", type(exc).__name__, str(exc)[:200])
        if SAST_NAMES or SAST_ALERT_ALL:
            try:
                got, n = fetch_nse_sast(state["seen"], days[0], today)
                items += got
                run["nse_sast"] = "OK - %d listed" % n
            except Exception as exc:
                run["nse_sast"] = "not available (%s)" % type(exc).__name__
                print("NSE SAST list not available:", type(exc).__name__, str(exc)[:150])
        else:
            run["nse_sast"] = "skipped (no SAST names set)"
    for exch in ("BSE", "NSE"):
        run["new_" + exch] = sum(1 for i in items if i["exch"] == exch)
    print("Filings listed by each feed for the dates checked (including ones seen "
          "before) - BSE: %s | NSE: %s | NSE SAST list: %s" % (
              run["bse_counts"] or run["bse"], run["nse_counts"] or run["nse"],
              run["nse_sast"]))

    # 2. queue the interesting ones
    jobs = state["pending"]
    for item in items:
        state["seen"][item["id"]] = today_str
        for kind in (["sast"] if item.get("row") else classify(item)):
            jobs.append({"item": item, "kind": kind, "queued": today_str})
    order = {"pref_meta": 0, "sast": 1, "pref_deep": 2}
    jobs.sort(key=lambda j: order.get(j["kind"], 9))

    # 3. work through the queue within the time budget
    remaining, opened = [], 0
    for idx, job in enumerate(jobs):
        if time.time() > deadline or opened >= MAX_DOCS:
            remaining = jobs[idx:]
            break
        try:
            if handle(job, state, mailer, deadline, run):
                opened += 1
        except Exception as exc:
            # most likely the email failed - keep the job and try again next run
            failed = True
            print("alert failed, will retry:", type(exc).__name__, str(exc)[:200])
            remaining = jobs[idx:]
            break
    cutoff = (today - timedelta(days=3)).strftime("%Y-%m-%d")
    state["pending"] = [j for j in remaining if j.get("queued", today_str) >= cutoff]

    run["left"] = len(state["pending"])

    # 4. summary of this run
    try:
        send_summary(run, mailer, now)
    except Exception as exc:
        failed = True
        print("summary email failed:", type(exc).__name__)

    # 5. tidy up and save
    keep = (today - timedelta(days=7)).strftime("%Y-%m-%d")
    state["seen"] = {k: v for k, v in state["seen"].items() if v >= keep}
    state["alerted_on"] = {k: v for k, v in state["alerted_on"].items() if v >= keep}
    state["alerted"] = {k: v for k, v in state["alerted"].items()
                        if k in state["alerted_on"]}
    with open(STATE_FILE, "w") as fh:
        json.dump(state, fh, separators=(",", ":"))
    mailer.close()
    print("new filings: %d | documents read: %d, unreadable: %d | name matches: %d | "
          "left for next run: %d | emails sent: %d | %.0fs" % (
              len(items), run["opened"], run["unopened"],
              run["pref_match"] + run["sast_match"], len(state["pending"]),
              mailer.sent, time.time() - started))
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
