#!/usr/bin/env python3
"""
BSE + NSE announcement scanner.

Runs once a night. Every run it:
  1. pulls all new equity announcements from BSE (and NSE when reachable),
  2. emails an alert for every preferential issue announcement and checks the
     document for the names on your allottee watchlist,
  3. emails an alert for SAST / takeover disclosures that mention a name on
     your SAST watchlist,
  4. sends one summary email a day so you know it is still running.

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
SUMMARY_HOUR = int(os.environ.get("SUMMARY_HOUR_IST", "21"))
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
        # looser: same words close together in any order (e.g. surname first)
        toks = [t for t in n.split() if t not in FILLER]
        if len(toks) < 2:
            continue
        if not where:
            for i, w in enumerate(words):
                where.setdefault(w, []).append(i)
        if any(t not in where for t in toks):
            continue
        span = len(toks) + 2
        rare = min(toks, key=lambda t: len(where[t]))
        for p in where[rare]:
            if all(any(abs(q - p) < span for q in where[t]) for t in toks):
                ctx = " ".join(words[max(0, p - 12): p + 12])
                hits.append((name, "possible", ctx))
                break
    return hits


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


def fetch_bse(seen, first_run, today):
    from bse import BSE
    start = today if first_run else today - timedelta(days=1)
    frm = datetime(start.year, start.month, start.day)
    to = datetime(today.year, today.month, today.day)
    items, fetched, stale_pages = [], 0, 0
    with BSE(download_folder=tempfile.mkdtemp()) as api:
        for page in range(1, 301):
            data = None
            for attempt in range(3):
                try:
                    data = api.announcements(page_no=page, from_date=frm, to_date=to)
                    break
                except Exception:
                    if attempt == 2:
                        raise
                    time.sleep(3)
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
                att = (r.get("ATTACHMENTNAME") or "").strip()
                base = "https://www.bseindia.com/xml-data/corpfiling/"
                items.append({
                    "id": sid, "exch": "BSE",
                    "company": (r.get("SLONGNAME") or "").strip(),
                    "code": str(r.get("SCRIP_CD") or ""),
                    "subject": r.get("NEWSSUB") or "",
                    "summary": " ".join(filter(None, [r.get("HEADLINE"), r.get("MORE")])),
                    "category": " ".join(filter(None, [r.get("CATEGORYNAME"),
                                                       r.get("SUBCATNAME")])),
                    "time": str(r.get("DissemDT") or r.get("NEWS_DT") or "")[:19],
                    "pdfs": [base + "AttachLive/" + att,
                             base + "AttachHis/" + att] if att else [],
                    "page": r.get("NSURL") or "",
                })
            stale_pages = 0 if fresh else stale_pages + 1
            total = ((data.get("Table1") or [{}])[0] or {}).get("ROWCNT") or 0
            # stop once everything is fetched (or, on frequent runs, once pages hold nothing new)
            if stale_pages >= STALE_PAGE_LIMIT or (total and fetched >= total):
                break
    return items


def fetch_nse(seen, first_run, today):
    from nse import NSE
    start = today if first_run else today - timedelta(days=1)
    items = []
    with NSE(download_folder=tempfile.mkdtemp()) as api:
        for index in ("equities", "sme"):
            rows = api.announcements(index=index, from_date=start, to_date=today)
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
    return items


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


def already_alerted(state, group, item, has_hit):
    """Stops the same filing being emailed twice when it is on both exchanges."""
    raw = "|".join([EMAIL_PASS or "x", group, norm(item["company"]), filed_on(item)])
    key = hashlib.sha1(raw.encode()).hexdigest()[:14]
    prev = state["alerted"].get(key)
    flag = item["exch"][0] + ("m" if has_hit else "n")
    if prev and prev[0] != flag[0] and (prev[1] == "m" or not has_hit):
        return True
    state["alerted"][key] = flag
    state["alerted_on"][key] = datetime.now(IST).strftime("%Y-%m-%d")
    return False


def handle(job, state, mailer, deadline):
    """Returns True if a document was opened."""
    item, kind = job["item"], job["kind"]
    day = state["day"]
    meta = " ".join([item["subject"], item["summary"], item["category"]])
    # board-meeting documents are numerous, so only their first pages get OCR
    text, readable = read_document(item, deadline, 2 if kind == "pref_deep" else 10)
    everything = norm(meta + " " + text)

    if kind == "sast":
        hits = match_names(SAST_NAMES, everything)
        if hits or SAST_ALERT_ALL:
            if not already_alerted(state, "sast", item, bool(hits)):
                who = ", ".join(h[0] for h in hits)
                subject = ("SAST MATCH: %s - %s" % (who, item["company"]) if hits
                           else "SAST filing: %s" % item["company"])
                body = describe(item)
                if hits:
                    body = hit_lines(hits) + "\n\n" + body
                elif not readable:
                    body += "\n\nDocument could not be read - names not checked."
                mailer.send(subject, body)
                day["sast"] += 1
        elif not readable and SAST_NAMES:
            day["unread_sast"].append(
                [item["company"], (item["pdfs"] or [item["page"]])[0]])
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

    hits = match_names(ALLOTTEE_NAMES, everything)
    if already_alerted(state, "pref", item, bool(hits)):
        return True
    if hits:
        status = "MATCH: " + ", ".join(h[0] for h in hits)
        top = hit_lines(hits) + "\n\n"
    elif not readable:
        status = "names not readable - check PDF"
        top = ("The document could not be read automatically (scanned or missing), "
               "so allottee names were NOT checked. Open it and check manually.\n\n")
    elif ALLOTTEE_NAMES:
        status = "no watchlist name"
        top = "None of your %d watchlist names appear in the document.\n\n" % len(ALLOTTEE_NAMES)
    else:
        status = "no watchlist set"
        top = ""
    mailer.send("PREF ISSUE: %s (%s)" % (item["company"], status),
                top + note + describe(item))
    day["pref"] += 1
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
def fresh_day(date_str):
    return {"date": date_str, "scanned": 0, "pref": 0, "sast": 0,
            "unread_sast": [], "nse_ok": 0, "nse_fail": 0, "summary_sent": False}


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


def send_summary(day, mailer, as_of):
    nse_total = day["nse_ok"] + day["nse_fail"]
    if not nse_total or day["nse_fail"] == nse_total:
        nse = "NOT reachable today - coverage was BSE only"
    elif day["nse_fail"]:
        nse = "reachable on %d of %d checks" % (day["nse_ok"], nse_total)
    else:
        nse = "OK"
    lines = [
        "Scanner is running. Summary for %s%s:" % (day["date"], as_of),
        "",
        "Announcements scanned : %d" % day["scanned"],
        "Preferential alerts   : %d" % day["pref"],
        "SAST alerts           : %d" % day["sast"],
        "NSE feed              : %s" % nse,
    ]
    unread = day["unread_sast"]
    if unread:
        lines += ["", "SAST filings that could not be read automatically (%d) - "
                      "names were not checked, open these yourself:" % len(unread)]
        lines += ["  %s  %s" % (c, u) for c, u in unread[:150]]
    mailer.send("Scanner daily summary %s: %d pref, %d SAST" %
                (day["date"], day["pref"], day["sast"]), "\n".join(lines))


# --- main --------------------------------------------------------------------
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

    # yesterday's summary if it never went out, then start a new day
    day = state.get("day") or fresh_day(today_str)
    if day["date"] != today_str:
        if not day["summary_sent"] and day["scanned"]:
            try:
                send_summary(day, mailer, "")
            except Exception as exc:
                print("summary email failed:", type(exc).__name__)
        day = fresh_day(today_str)
    state["day"] = day

    # 1. fetch
    items = []
    fixture = os.environ.get("SCANNER_FIXTURE")
    if fixture:
        with open(fixture) as fh:
            items = [i for i in json.load(fh) if i["id"] not in state["seen"]]
    else:
        try:
            items += fetch_bse(state["seen"], first_run, today)
        except Exception as exc:
            failed = True
            print("BSE fetch failed:", type(exc).__name__, str(exc)[:200])
        try:
            items += fetch_nse(state["seen"], first_run, today)
            day["nse_ok"] += 1
        except Exception as exc:
            day["nse_fail"] += 1
            print("NSE not reachable this run:", type(exc).__name__)
    day["scanned"] += len(items)

    # 2. queue the interesting ones
    jobs = state["pending"]
    for item in items:
        state["seen"][item["id"]] = today_str
        for kind in classify(item):
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
            if handle(job, state, mailer, deadline):
                opened += 1
        except Exception as exc:
            # most likely the email failed - keep the job and try again next run
            failed = True
            print("alert failed, will retry:", type(exc).__name__, str(exc)[:200])
            remaining = jobs[idx:]
            break
    cutoff = (today - timedelta(days=3)).strftime("%Y-%m-%d")
    state["pending"] = [j for j in remaining if j.get("queued", today_str) >= cutoff]

    # 4. daily summary
    if now.hour >= SUMMARY_HOUR and not day["summary_sent"] and not failed:
        try:
            send_summary(day, mailer, " (as of %s IST)" % now.strftime("%H:%M"))
            day["summary_sent"] = True
        except Exception as exc:
            print("summary email failed:", type(exc).__name__)

    # 5. tidy up and save
    keep = (today - timedelta(days=2)).strftime("%Y-%m-%d")
    state["seen"] = {k: v for k, v in state["seen"].items() if v >= keep}
    state["alerted_on"] = {k: v for k, v in state["alerted_on"].items() if v >= keep}
    state["alerted"] = {k: v for k, v in state["alerted"].items()
                        if k in state["alerted_on"]}
    with open(STATE_FILE, "w") as fh:
        json.dump(state, fh, separators=(",", ":"))
    mailer.close()
    print("new announcements: %d | documents opened: %d | queued for next run: %d | "
          "emails sent: %d | %.0fs" % (len(items), opened, len(state["pending"]),
                                       mailer.sent, time.time() - started))
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
