"""
Global alert system: visits and meetings between Russian officials and officials
of ANY other country (both directions), announced anywhere in the world.

Layers (each optional except GDELT):
  1. GDELT DOC API  - global news in 65+ languages, searchable with English keywords
  2. Google News    - local-language searches in many regional editions
  3. Direct RSS     - Russian agencies and government sites (often publish first)
  4. Telegram       - public channels read from their web preview (t.me/s/...), no login;
                      optional Telethon fallback for channels without a web preview
  5. X (Twitter)    - optional; follows chosen accounts via the official paid X API

Pipeline: collect -> dedupe -> AI screen headlines (high recall) ->
          AI verify full text + check against recent alerts -> Telegram alert.

Env vars:
  AI provider - choose ONE:
    Paid (default):  ANTHROPIC_API_KEY
    Free tiers:      LLM_PROVIDER=openai_compatible, LLM_BASE_URL, LLM_API_KEY,
                     SCREEN_MODEL (and optionally VERIFY_MODEL), AI_PAUSE_SECONDS
  TELEGRAM_BOT_TOKEN, TELEGRAM_CHAT_ID    (required, where alerts go)
  TG_API_ID, TG_API_HASH, TG_SESSION      (optional fallback only; see gen_session.py)
  X_BEARER_TOKEN                          (optional, turns on X/Twitter tracking)
  DB_PATH                                 (optional, default seen.db)
  HEARTBEAT_HOUR_UTC                      (optional, default 6)
"""
import datetime as dt
import hashlib
import json
import os
import re
import sqlite3
import time
import urllib.parse

import feedparser
import requests

try:
    import trafilatura
except ImportError:
    trafilatura = None

UA = {"User-Agent": "Mozilla/5.0 (compatible; visit-monitor/2.0)"}

# =============================================================================
# SOURCES - edit freely
# =============================================================================

# GDELT: English keywords match articles in all 65+ languages it translates.
# Each query returns at most 250 articles, so the topic is split across several.
GDELT_QUERIES = [
    '(Russia OR Russian OR Kremlin OR Moscow) (visit OR visiting OR "will visit" OR "official visit" OR "state visit" OR "working visit")',
    '(Russia OR Russian OR Kremlin OR Moscow) (talks OR delegation OR "intergovernmental commission" OR "will meet" OR "bilateral meeting")',
    '(Putin OR Mishustin OR Lavrov OR Siluanov OR Manturov OR Novak OR Overchuk OR Belousov OR Reshetnikov OR Shoigu OR Matviyenko OR Volodin OR Nabiullina OR Ushakov) (visit OR talks OR meet OR trip)',
]
GDELT_TIMESPAN = "1h"  # overlaps with a 15-min schedule so delayed runs don't leave gaps

# Google News: (language, country, edition, local-language query)
GNEWS = [
    ("ru", "RU", "RU:ru", '(визит OR посетит OR переговоры OR "прибудет" OR межправкомиссия OR делегация)'),
    ("en-US", "US", "US:en", "Russia (visit OR talks OR delegation OR \"will meet\")"),
    ("en-IN", "IN", "IN:en", "Russia (visit OR talks OR delegation)"),
    ("zh-CN", "CN", "CN:zh-Hans", "俄罗斯 (访问 OR 会谈 OR 会见 OR 代表团)"),
    ("ar", "EG", "EG:ar", "روسيا (زيارة OR مباحثات OR وفد)"),
    ("es-419", "MX", "MX:es-419", "Rusia (visita OR reunión OR delegación)"),
    ("fr", "FR", "FR:fr", "Russie (visite OR entretiens OR délégation)"),
    ("de", "DE", "DE:de", "Russland (Besuch OR Gespräche OR Delegation)"),
    ("tr", "TR", "TR:tr", "Rusya (ziyaret OR görüşme OR heyet)"),
    ("pt-BR", "BR", "BR:pt-419", "Rússia (visita OR reunião OR delegação)"),
    ("hi", "IN", "IN:hi", "रूस (यात्रा OR दौरा OR वार्ता)"),
    ("ja", "JP", "JP:ja", "ロシア (訪問 OR 会談)"),
    ("ko", "KR", "KR:ko", "러시아 (방문 OR 회담)"),
    ("vi", "VN", "VN:vi", "Nga (thăm OR \"hội đàm\")"),
    ("id", "ID", "ID:id", "Rusia (kunjungan OR pertemuan)"),
]

# Direct RSS feeds (add ministry or foreign-government feeds here)
FEEDS = {
    "TASS": "https://tass.ru/rss/v2.xml",
    "TASS (EN)": "https://tass.com/rss/v2.xml",
    "RIA Novosti": "https://ria.ru/export/rss2/archive/index.xml",
    "Interfax": "https://www.interfax.ru/rss.asp",
    "Kremlin": "http://kremlin.ru/events/all/feed",
    "Government": "http://government.ru/all/rss/",
}

# Public Telegram channels to read (usernames without @). Verify each name in Telegram.
# Add any public channel: foreign ministries, embassies, agencies, journalists.
TG_CHANNELS = ["MID_Russia", "tass_agency", "rian_ru"]

# X (Twitter) accounts to follow, without @. Only used if X_BEARER_TOKEN is set.
# Each new post read costs money (see README notes), so list accounts deliberately.
# Verify each handle on x.com before adding.
X_ACCOUNTS = ["mfa_russia", "MID_RF", "KremlinRussia_E"]

# =============================================================================
# STORAGE
# =============================================================================
db = sqlite3.connect(os.environ.get("DB_PATH", "seen.db"))
db.executescript("""
CREATE TABLE IF NOT EXISTS seen (h TEXT PRIMARY KEY, ts REAL);
CREATE TABLE IF NOT EXISTS alerts (id INTEGER PRIMARY KEY AUTOINCREMENT, ts REAL,
    summary TEXT, event_date TEXT, url TEXT);
CREATE TABLE IF NOT EXISTS meta (k TEXT PRIMARY KEY, v TEXT);
""")


def h(s: str) -> str:
    return hashlib.sha1(s.encode("utf-8", "ignore")).hexdigest()


def norm_title(t: str) -> str:
    t = re.sub(r"\s+[-–|]\s+[^-–|]{2,60}$", "", t or "")  # drop " - Source name"
    return re.sub(r"\W+", " ", t.lower()).strip()


def meta_get(k):
    row = db.execute("SELECT v FROM meta WHERE k=?", (k,)).fetchone()
    return row[0] if row else None


def meta_set(k, v):
    db.execute("INSERT OR REPLACE INTO meta (k, v) VALUES (?, ?)", (k, v))
    db.commit()


# =============================================================================
# COLLECTORS - each returns a list of {source, title, text, url, uid}
# =============================================================================
def fetch_gdelt():
    items = []
    for q in GDELT_QUERIES:
        params = {"query": q, "mode": "artlist", "format": "json", "maxrecords": "250",
                  "timespan": GDELT_TIMESPAN, "sort": "datedesc"}
        try:
            r = requests.get("https://api.gdeltproject.org/api/v2/doc/doc",
                             params=params, headers=UA, timeout=60)
            data = r.json() if r.text.strip().startswith("{") else {}
            if not data:
                print(f"[gdelt] non-JSON reply: {r.text[:150]}")
        except Exception as e:
            print(f"[gdelt error] {e}")
            data = {}
        for a in data.get("articles", []):
            items.append({
                "source": f"{a.get('domain', '')} ({a.get('sourcecountry', '')}, {a.get('language', '')})",
                "title": a.get("title", ""), "text": "", "url": a.get("url", ""),
                "uid": a.get("url", ""),
            })
        time.sleep(6)  # GDELT asks for gentle request rates
    return items


def fetch_gnews():
    items = []
    for hl, gl, ceid, q in GNEWS:
        url = "https://news.google.com/rss/search?" + urllib.parse.urlencode(
            {"q": f"{q} when:2h", "hl": hl, "gl": gl, "ceid": ceid})
        feed = feedparser.parse(url, request_headers=UA)
        for e in feed.entries:
            src = (e.get("source") or {}).get("title", "")
            items.append({
                "source": f"{src} (Google News {ceid})", "title": e.get("title", ""),
                "text": re.sub("<[^>]+>", " ", e.get("summary", "")),
                "url": e.get("link", ""), "uid": e.get("link", ""),
            })
        time.sleep(1)
    return items


def fetch_feeds():
    items = []
    for name, url in FEEDS.items():
        feed = feedparser.parse(url, request_headers=UA)
        if not feed.entries:
            print(f"[feed] {name}: no entries (blocked or URL changed?)")
        for e in feed.entries:
            items.append({
                "source": name, "title": e.get("title", ""),
                "text": re.sub("<[^>]+>", " ", e.get("summary", "")),
                "url": e.get("link", ""), "uid": e.get("link", "") or e.get("title", ""),
            })
    return items


def fetch_telegram_web():
    """Read public channels from their web preview page - no account or login needed."""
    from bs4 import BeautifulSoup

    items, failed = [], []
    for ch in TG_CHANNELS:
        try:
            r = requests.get(f"https://t.me/s/{ch}", headers=UA, timeout=30)
            soup = BeautifulSoup(r.text, "html.parser")
            posts = soup.select("div.tgme_widget_message[data-post]")
            if not posts:
                failed.append(ch)  # preview disabled, renamed, or private
                continue
            for post in posts:
                body = post.select_one("div.tgme_widget_message_text")
                text = body.get_text(" ", strip=True) if body else ""
                if not text:
                    continue
                path = post["data-post"]            # e.g. "MID_Russia/12345"
                msg_id = path.split("/")[-1]
                items.append({
                    "source": f"Telegram @{ch}", "title": text[:300], "text": text,
                    "url": f"https://t.me/{path}", "uid": f"tg:{ch}:{msg_id}",
                })
        except Exception as e:
            print(f"[telegram web error] {ch}: {e}")
            failed.append(ch)
        time.sleep(1)
    if failed:
        print(f"[telegram web] no posts read from: {', '.join(failed)}")
    fetch_telegram_web.failed = failed
    return items


def fetch_telegram_channels():
    """Optional fallback: log in as a user to read channels whose web preview failed."""
    api_id, api_hash, session = (os.environ.get(k) for k in ("TG_API_ID", "TG_API_HASH", "TG_SESSION"))
    channels = getattr(fetch_telegram_web, "failed", [])
    if not (api_id and api_hash and session) or not channels:
        return []
    from telethon.sessions import StringSession
    from telethon.sync import TelegramClient

    items = []
    with TelegramClient(StringSession(session), int(api_id), api_hash) as tg:
        for ch in channels:
            try:
                for m in tg.iter_messages(ch, limit=40):
                    if m.message:
                        items.append({
                            "source": f"Telegram @{ch}", "title": m.message[:300],
                            "text": m.message, "url": f"https://t.me/{ch}/{m.id}",
                            "uid": f"tg:{ch}:{m.id}",
                        })
            except Exception as e:
                print(f"[telegram channel error] {ch}: {e}")
    return items


def fetch_x():
    """Read new posts from chosen X accounts via the official API (pay-per-use).
    Uses since_id so only posts newer than the last one seen are fetched and billed."""
    token = os.environ.get("X_BEARER_TOKEN")
    if not token or not X_ACCOUNTS:
        return []
    api = "https://api.x.com/2"
    hdr = {"Authorization": f"Bearer {token}"}

    # Look up numeric user ids once and cache them (user lookups are billed too)
    ids = json.loads(meta_get("x_user_ids") or "{}")
    missing = [a for a in X_ACCOUNTS if a.lower() not in ids]
    if missing:
        r = requests.get(f"{api}/users/by", headers=hdr,
                         params={"usernames": ",".join(missing)}, timeout=30)
        if r.ok:
            for u in r.json().get("data", []):
                ids[u["username"].lower()] = u["id"]
            meta_set("x_user_ids", json.dumps(ids))
        else:
            print(f"[x user lookup error] {r.status_code} {r.text[:200]}")
        for a in missing:
            if a.lower() not in ids:
                print(f"[x] account not found: {a}")

    items = []
    for handle in X_ACCOUNTS:
        uid = ids.get(handle.lower())
        if not uid:
            continue
        since = meta_get(f"x_since:{uid}")
        params = {"exclude": "retweets,replies", "tweet.fields": "created_at"}
        if since:
            params.update({"since_id": since, "max_results": "100"})
        else:
            params["max_results"] = "5"  # first time: just set a starting point cheaply
        r = requests.get(f"{api}/users/{uid}/tweets", headers=hdr, params=params, timeout=30)
        if r.status_code == 429:
            print("[x] rate limited; will catch up next run")
            break
        if not r.ok:
            print(f"[x error] {handle}: {r.status_code} {r.text[:200]}")
            continue
        body = r.json()
        newest = (body.get("meta") or {}).get("newest_id")
        if newest:
            meta_set(f"x_since:{uid}", newest)
        for t in body.get("data", []):
            items.append({
                "source": f"X @{handle}", "title": t["text"][:300], "text": t["text"],
                "url": f"https://x.com/{handle}/status/{t['id']}", "uid": f"x:{t['id']}",
            })
    return items


# =============================================================================
# AI - works with Anthropic (paid) or any OpenAI-compatible provider (free tiers)
# =============================================================================
LLM_PROVIDER = os.environ.get("LLM_PROVIDER") or "anthropic"   # "anthropic" or "openai_compatible"
SCREEN_MODEL = os.environ.get("SCREEN_MODEL") or "claude-haiku-5-5"
if LLM_PROVIDER == "anthropic":
    VERIFY_MODEL = os.environ.get("VERIFY_MODEL") or "claude-sonnet-5-5"
else:
    VERIFY_MODEL = os.environ.get("VERIFY_MODEL") or SCREEN_MODEL
SCREEN_BATCH = int(os.environ.get("SCREEN_BATCH") or "150")  # headlines per AI call
VERIFY_BATCH = int(os.environ.get("VERIFY_BATCH") or "6")    # articles per AI call
AI_PAUSE = float(os.environ.get("AI_PAUSE_SECONDS") or "0")  # pause between calls (free tiers: 4-6)

_ai_down = False  # set when the AI quota is exhausted, so the rest of the run uses keywords


def _call_llm(model, system, user, max_tokens):
    if LLM_PROVIDER == "anthropic":
        import anthropic
        msg = anthropic.Anthropic().messages.create(
            model=model, max_tokens=max_tokens, system=system,
            messages=[{"role": "user", "content": user}])
        return "".join(b.text for b in msg.content if b.type == "text")
    r = requests.post(
        os.environ["LLM_BASE_URL"].rstrip("/") + "/chat/completions",
        headers={"Authorization": f"Bearer {os.environ['LLM_API_KEY']}"},
        json={"model": model, "max_tokens": max_tokens, "temperature": 0,
              "messages": [{"role": "system", "content": system},
                           {"role": "user", "content": user}]},
        timeout=120)
    if r.status_code == 429:
        raise RuntimeError("429 rate limit / quota")
    r.raise_for_status()
    return r.json()["choices"][0]["message"]["content"]


def ask_json(model, system, user, max_tokens=1500):
    global _ai_down
    if _ai_down:
        return None
    for attempt in range(3):
        try:
            if AI_PAUSE:
                time.sleep(AI_PAUSE)
            raw = _call_llm(model, system, user, max_tokens)
            raw = re.sub(r"```json|```", "", raw).strip()
            return json.loads(raw[raw.find("{"): raw.rfind("}") + 1])
        except Exception as e:
            print(f"[AI error, attempt {attempt + 1}] {e}")
            time.sleep(10 * (attempt + 1))
    _ai_down = True
    print("[AI] unavailable for the rest of this run; falling back to keyword matching")
    return None


# Free fallback when the AI is unavailable: headline must mention Russia AND a visit/meeting word
RUSSIA_RE = re.compile(
    r"росси|рф\b|кремл|москв|путин|лавров|мишустин|russia|kremlin|moscow|putin|lavrov|俄|روسي|"
    r"rusia|russie|russland|rusya|rússia|रूस|ロシア|러시아", re.IGNORECASE)
VISIT_RE = re.compile(
    r"визит|посет|переговор|встреч|делегаци|межправкомисс|прибуд|visit|talks|delegation|meet|summit|"
    r"访|会谈|会见|زيارة|مباحثات|وفد|visita|reuni|visite|entretien|besuch|gespräch|ziyaret|görüş|heyet|"
    r"यात्रा|दौरा|वार्ता|訪問|会談|방문|회담|kunjungan|pertemuan", re.IGNORECASE)


def keyword_match(it):
    s = f"{it['title']} {it.get('text', '')[:500]}"
    return bool(RUSSIA_RE.search(s) and VISIT_RE.search(s))


SCREEN_PROMPT = """You are a HIGH-RECALL filter for an analyst. You get numbered headlines in any language.
Return the numbers of every headline that MIGHT concern a visit, trip, talks, meeting, negotiations,
delegation, summit, intergovernmental commission or dialogue between officials of Russia and officials
of any other country - in either direction (Russians going abroad, or foreigners coming to Russia or
meeting Russians anywhere). Include announcements, plans, and events under way.
When in doubt, INCLUDE it. Missing a real event is far worse than a false positive.
Reply with ONLY JSON: {"keep": [numbers]}"""

VERIFY_PROMPT = """You verify news items for an analyst tracking visits and meetings between Russian
government officials and officials of other countries. You get several numbered ITEMS.

An item is RELEVANT if it announces or reports a visit/trip/meeting/talks/commission/dialogue that is
UPCOMING or UNDER WAY (not fully concluded), involving:
- a Russian state official (president, PM, deputy PMs, ministers, deputy ministers, heads of federal
  agencies, Kremlin staff, presidential envoys, ambassadors-at-large, Federal Assembly leadership,
  central bank leadership, heads of major state corporations acting officially), AND
- officials of any foreign country or international organization; in either direction.
NOT relevant: events that already ended, purely domestic trips, sports/culture tours, pure speculation,
battlefield news.

You also get RECENT ALERTS already sent. If an item is about the same event as one of them, set
duplicate_of to that alert id, and set new_info only if the item adds a materially new fact (date,
location, participants, agenda) not in the alert. If several items in this batch describe the same
event, return that event ONCE, using the number of the most informative item.

Return ONLY relevant items, as ONLY JSON:
{"results": [
 {"n": item number,
  "confidence": "high" | "medium",
  "duplicate_of": alert id number or null,
  "new_info": "",
  "status": "announced" | "under_way",
  "officials": "names and titles",
  "countries": "counterpart country/countries or organizations",
  "direction": "Russia -> abroad" | "foreign -> Russia" | "meeting elsewhere",
  "location": "city, country",
  "event_date": "as stated, or 'not stated'",
  "summary_en": "one or two sentence English summary"}
]}
If none are relevant: {"results": []}"""


def screen(items):
    """Stage 1: batch headlines through the AI (keyword fallback if AI unavailable)."""
    keep = []
    for i in range(0, len(items), SCREEN_BATCH):
        batch = items[i:i + SCREEN_BATCH]
        lines = "\n".join(f"{n}. {it['title'][:200]}" for n, it in enumerate(batch))
        res = ask_json(SCREEN_MODEL, SCREEN_PROMPT, lines, max_tokens=800)
        if res is None:
            keep.extend(it for it in batch if keyword_match(it))
            continue
        for n in res.get("keep", []):
            if isinstance(n, int) and 0 <= n < len(batch):
                keep.append(batch[n])
    return keep


def article_text(item, limit=2500):
    text = item.get("text") or ""
    if len(text) > 400 or not trafilatura or "news.google.com" in item["url"]:
        return text[:limit]
    try:
        html = requests.get(item["url"], headers=UA, timeout=20).text
        extracted = trafilatura.extract(html) or ""
        return (extracted or text)[:limit]
    except Exception:
        return text[:limit]


def recent_alerts_block():
    cutoff = time.time() - 21 * 86400
    rows = db.execute("SELECT id, summary, event_date FROM alerts WHERE ts > ? ORDER BY id DESC LIMIT 150",
                      (cutoff,)).fetchall()
    return "\n".join(f"[{r[0]}] {r[1]} (date: {r[2]})" for r in rows) or "(none)"


# =============================================================================
# TELEGRAM OUTPUT
# =============================================================================
def send(text):
    token, chat = os.environ["TELEGRAM_BOT_TOKEN"], os.environ["TELEGRAM_CHAT_ID"]
    for chunk in [text[i:i + 4000] for i in range(0, len(text), 4000)]:
        r = requests.post(f"https://api.telegram.org/bot{token}/sendMessage",
                          json={"chat_id": chat, "text": chunk, "disable_web_page_preview": True},
                          timeout=20)
        if not r.ok:
            print(f"[telegram send error] {r.status_code} {r.text}")


def heartbeat(n_collected):
    hour = int(os.environ.get("HEARTBEAT_HOUR_UTC") or "6")
    now = dt.datetime.now(dt.timezone.utc)
    today = now.date().isoformat()
    if now.hour >= hour and meta_get("heartbeat") != today:
        day_ago = time.time() - 86400
        scanned = db.execute("SELECT COUNT(*) FROM seen WHERE ts > ?", (day_ago,)).fetchone()[0]
        alerts = db.execute("SELECT COUNT(*) FROM alerts WHERE ts > ?", (day_ago,)).fetchone()[0]
        send(f"✅ Visit monitor is running.\nLast 24h: ~{scanned // 2} new items scanned, "
             f"{alerts} alerts sent.\nThis run collected {n_collected} items.")
        meta_set("heartbeat", today)


# =============================================================================
# MAIN
# =============================================================================
def run_once():
    first_run = meta_get("initialized") is None

    collected = []
    for fn in (fetch_feeds, fetch_telegram_web, fetch_telegram_channels, fetch_x, fetch_gnews, fetch_gdelt):
        try:
            got = fn()
            print(f"{fn.__name__}: {len(got)} items")
            collected += got
        except Exception as e:
            print(f"[{fn.__name__} failed] {e}")

    # Dedupe by URL and by normalized headline (same story across outlets/sources)
    new_items, now = [], time.time()
    for it in collected:
        keys = [h("u:" + it["uid"]), h("t:" + norm_title(it["title"]))]
        if any(db.execute("SELECT 1 FROM seen WHERE h=?", (k,)).fetchone() for k in keys):
            continue
        for k in keys:
            db.execute("INSERT OR IGNORE INTO seen (h, ts) VALUES (?, ?)", (k, now))
        if it["title"].strip():
            new_items.append(it)
    db.commit()
    print(f"New items: {len(new_items)}")

    if first_run:
        print("First run: recorded existing items, no alerts sent.")
        send("✅ Visit monitor started. Alerts begin from the next run.")
        meta_set("initialized", "1")
        meta_set("heartbeat", dt.datetime.now(dt.timezone.utc).date().isoformat())
        return

    shortlist = screen(new_items)
    print(f"Shortlisted: {len(shortlist)}")

    sent = 0
    for i in range(0, len(shortlist), VERIFY_BATCH):
        batch = shortlist[i:i + VERIFY_BATCH]
        user = f"RECENT ALERTS:\n{recent_alerts_block()}\n\n" + "\n\n".join(
            f"ITEM {n}\nSource: {it['source']}\nURL: {it['url']}\nTitle: {it['title']}\n"
            f"Text: {article_text(it)}" for n, it in enumerate(batch))
        res = ask_json(VERIFY_MODEL, VERIFY_PROMPT, user, max_tokens=2500)

        if res is None:
            # AI unavailable: still alert, clearly marked, so nothing is silently lost
            for it in batch:
                if not keyword_match(it):
                    continue
                db.execute("INSERT INTO alerts (ts, summary, event_date, url) VALUES (?, ?, ?, ?)",
                           (time.time(), it["title"][:300], "not checked", it["url"]))
                db.commit()
                send(f"❔ UNVERIFIED (AI unavailable, keyword match)\n\n{it['title']}\n\n"
                     f"Source: {it['source']}\n{it['url']}")
                sent += 1
            continue

        for r in res.get("results", []):
            n = r.get("n")
            if not isinstance(n, int) or not 0 <= n < len(batch):
                continue
            it = batch[n]
            dup = r.get("duplicate_of")
            if dup:
                if r.get("new_info"):
                    send(f"🔄 Update to an earlier alert\n{r['new_info']}\n\n"
                         f"Source: {it['source']}\n{it['url']}")
                    db.execute("UPDATE alerts SET summary = summary || ' | ' || ? WHERE id = ?",
                               (r["new_info"], dup))
                    db.commit()
                continue

            db.execute("INSERT INTO alerts (ts, summary, event_date, url) VALUES (?, ?, ?, ?)",
                       (time.time(), r.get("summary_en", ""), r.get("event_date", ""), it["url"]))
            db.commit()

            flag = "⚠️ UNCONFIRMED - " if r.get("confidence") == "medium" else ""
            status = "🟢 Under way" if r.get("status") == "under_way" else "🛬 Announced"
            send(f"{flag}{status}: Russia ⇄ {r.get('countries', '')}\n\n"
                 f"{r.get('summary_en', '')}\n\n"
                 f"Who: {r.get('officials', '')}\n"
                 f"Direction: {r.get('direction', '')}\n"
                 f"Where: {r.get('location', '')}\n"
                 f"When: {r.get('event_date', '')}\n\n"
                 f"Source: {it['source']}\n{it['title']}\n{it['url']}")
            sent += 1

    # Housekeeping
    db.execute("DELETE FROM seen WHERE ts < ?", (time.time() - 14 * 86400,))
    db.commit()
    heartbeat(len(collected))
    print(f"Done. Alerts sent: {sent}")


if __name__ == "__main__":
    run_once()
