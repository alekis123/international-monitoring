"""
Мониторинг визитов: визиты и встречи российских официальных лиц с представителями
других стран (в обоих направлениях), анонсируемые в мировых СМИ и на госсайтах.

Global alert system: visits/meetings between Russian officials and officials of other
countries (both directions). All Telegram messages are in Russian.

Layers:
  1. GDELT DOC API  - global news in 65+ languages, searchable with English keywords
  2. Google News    - local-language searches in many regional editions
  3. Direct RSS     - Russian agencies and government sites (often publish first)
  4. Telegram       - public channels read from their web preview (t.me/s/...), no login;
                      optional Telethon fallback for channels without a web preview
  5. X (Twitter)    - optional; follows chosen accounts via the official paid X API
  6. Web pages      - news list pages of official sites without RSS (Security Council, RDIF)

Pipeline: collect -> dedupe -> AI screen headlines (high recall) ->
          AI verify full text + check against recent alerts -> resolve dates -> Telegram.

Dates: the AI only describes WHAT the article says about timing ("on Tuesday",
"tomorrow", "24-26 November", "next week"). This program converts that into a calendar
date using the article's publication date (see resolve_ref).

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
  FEEDBACK_BUTTONS                        (optional, "off" removes the 👍/👎 buttons)
  DIGEST_WEEKDAY, DIGEST_HOUR_MSK         (optional, weekly digest; default Friday (4), 12:00 MSK)

Features: alerts in Russian with Russian headlines; follow-up messages (date confirmed/changed,
postponed, cancelled) sent as replies quoting the original alert; weekly digest + CSV archive;
👍/👎 feedback buttons used to teach the AI; instant alerts when a source or the AI stops working.
"""
import datetime as dt
import hashlib
import html
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

UA = {"User-Agent": "Mozilla/5.0 (compatible; visit-monitor/3.0)"}
UTC = dt.timezone.utc
MSK = dt.timezone(dt.timedelta(hours=3))  # weekday logic uses Moscow time

# =============================================================================
# SOURCES - edit freely
# =============================================================================

# Priority countries. Every one is named in at least one GDELT query and one
# Russian-language Google News query below; many also have a local-language edition.
# China, Hong Kong, Taiwan, Macao, Vietnam, Cambodia, Thailand, Myanmar, Japan,
# South Korea, North Korea, Armenia, Indonesia, Singapore, Laos, Malaysia, Mongolia,
# Russia, Brazil, South Africa, Nigeria, Mexico, Turkey, Azerbaijan, Bahrain, Qatar,
# Kuwait, UAE, Oman, Saudi Arabia, Egypt, Morocco, Algeria, Guyana, Jamaica, Hungary,
# Slovakia, Serbia, Belarus, Kazakhstan, Uzbekistan, Turkmenistan, Kyrgyzstan,
# Tajikistan, Moldova, Ghana, Madagascar, Guinea, Guinea-Bissau, India.

_RU = '(Russia OR Russian OR Kremlin OR Moscow)'
_ACT = '(visit OR visiting OR talks OR delegation OR meeting OR "will meet" OR "intergovernmental commission")'

# GDELT: English keywords match articles in all 65+ languages it translates.
# Each query returns at most 250 articles, so the topic is split across several.
GDELT_QUERIES = [
    f'{_RU} (visit OR visiting OR "will visit" OR "official visit" OR "state visit" OR "working visit")',
    f'{_RU} (talks OR delegation OR "intergovernmental commission" OR "will meet" OR "bilateral meeting")',
    '(Putin OR Mishustin OR Lavrov OR Siluanov OR Manturov OR Novak OR Overchuk OR Belousov OR Reshetnikov '
    'OR Shoigu OR Matviyenko OR Volodin OR Nabiullina OR Ushakov) (visit OR talks OR meet OR trip)',
    # Priority countries, in groups
    f'{_RU} {_ACT} (China OR "Hong Kong" OR Taiwan OR Macao OR Macau OR Vietnam OR Cambodia OR Thailand OR Myanmar OR Japan)',
    f'{_RU} {_ACT} ("South Korea" OR "North Korea" OR DPRK OR Indonesia OR Singapore OR Laos OR Malaysia OR Mongolia OR India)',
    f'{_RU} {_ACT} (Brazil OR "South Africa" OR Nigeria OR Mexico OR Guyana OR Jamaica OR Ghana OR Madagascar OR Guinea OR "Guinea-Bissau")',
    f'{_RU} {_ACT} (Turkey OR Turkiye OR Azerbaijan OR Bahrain OR Qatar OR Kuwait OR UAE OR Emirates OR Oman OR "Saudi Arabia" OR Egypt OR Morocco OR Algeria)',
    f'{_RU} {_ACT} (Armenia OR Hungary OR Slovakia OR Serbia OR Belarus OR Kazakhstan OR Uzbekistan OR Turkmenistan OR Kyrgyzstan OR Tajikistan OR Moldova)',
]
GDELT_TIMESPAN = "1h"  # overlaps with the schedule so delayed runs don't leave gaps

_RU_ACT = '(визит OR визитом OR посетит OR переговоры OR делегация OR межправкомиссия OR встреча)'

# Google News: (language, country, edition, query)
GNEWS = [
    # Russian edition: general + targeted by country group
    ("ru", "RU", "RU:ru", '(визит OR посетит OR переговоры OR "прибудет" OR межправкомиссия OR делегация)'),
    ("ru", "RU", "RU:ru", f'(Китай OR КНР OR Гонконг OR Тайвань OR Макао OR Вьетнам OR Камбоджа OR Таиланд OR Мьянма '
                          f'OR Япония OR Корея OR КНДР OR Индонезия OR Сингапур OR Лаос OR Малайзия OR Монголия OR Индия) {_RU_ACT}'),
    ("ru", "RU", "RU:ru", f'(Белоруссия OR Белоруссии OR Беларусь OR Казахстан OR Узбекистан OR Туркмения OR Туркменистан '
                          f'OR Киргизия OR Таджикистан OR Армения OR Азербайджан OR Молдавия OR Молдова OR Венгрия '
                          f'OR Словакия OR Сербия) {_RU_ACT}'),
    ("ru", "RU", "RU:ru", f'(Турция OR ОАЭ OR Катар OR Кувейт OR Оман OR Бахрейн OR "Саудовская Аравия" OR Египет OR Марокко '
                          f'OR Алжир OR Бразилия OR ЮАР OR Нигерия OR Мексика OR Гайана OR Ямайка OR Гана OR Мадагаскар '
                          f'OR Гвинея OR "Гвинея-Бисау") {_RU_ACT}'),
    # English
    ("en-US", "US", "US:en", 'Russia (visit OR talks OR delegation OR "will meet")'),
    ("en-IN", "IN", "IN:en", "Russia (visit OR talks OR delegation)"),
    ("en-SG", "SG", "SG:en", "Russia (visit OR talks OR delegation)"),
    ("en-MY", "MY", "MY:en", "Russia (visit OR talks OR delegation)"),
    ("en-NG", "NG", "NG:en", "Russia (visit OR talks OR delegation)"),
    ("en-ZA", "ZA", "ZA:en", "Russia (visit OR talks OR delegation)"),
    ("en-GH", "GH", "GH:en", "Russia (visit OR talks OR delegation)"),
    # Chinese (mainland, Hong Kong, Taiwan)
    ("zh-CN", "CN", "CN:zh-Hans", "俄罗斯 (访问 OR 会谈 OR 会见 OR 代表团)"),
    ("zh-HK", "HK", "HK:zh-Hant", "俄羅斯 (訪問 OR 會談 OR 會見 OR 代表團)"),
    ("zh-TW", "TW", "TW:zh-Hant", "俄羅斯 (訪問 OR 會談 OR 會見 OR 代表團)"),
    # Arabic
    ("ar", "EG", "EG:ar", "روسيا (زيارة OR مباحثات OR وفد)"),
    ("ar", "SA", "SA:ar", "روسيا (زيارة OR مباحثات OR وفد)"),
    ("ar", "AE", "AE:ar", "روسيا (زيارة OR مباحثات OR وفد)"),
    # Other languages
    ("fr", "MA", "MA:fr", "Russie (visite OR entretiens OR délégation)"),
    ("fr", "FR", "FR:fr", "Russie (visite OR entretiens OR délégation)"),
    ("es-419", "MX", "MX:es-419", "Rusia (visita OR reunión OR delegación)"),
    ("pt-BR", "BR", "BR:pt-419", "Rússia (visita OR reunião OR delegação)"),
    ("pt-PT", "PT", "PT:pt-150", "Rússia (visita OR reunião OR delegação)"),
    ("de", "DE", "DE:de", "Russland (Besuch OR Gespräche OR Delegation)"),
    ("tr", "TR", "TR:tr", "Rusya (ziyaret OR görüşme OR heyet)"),
    ("hu", "HU", "HU:hu", "(Oroszország OR orosz) (látogatás OR tárgyalás OR delegáció)"),
    ("sk", "SK", "SK:sk", "Rusko (návšteva OR rokovania OR delegácia)"),
    ("sr", "RS", "RS:sr", "(Русија OR Rusija) (посета OR poseta OR разговори OR razgovori)"),
    ("hi", "IN", "IN:hi", "रूस (यात्रा OR दौरा OR वार्ता)"),
    ("th", "TH", "TH:th", "รัสเซีย (เยือน OR หารือ OR คณะผู้แทน)"),
    ("ja", "JP", "JP:ja", "ロシア (訪問 OR 会談)"),
    ("ko", "KR", "KR:ko", "러시아 (방문 OR 회담)"),
    ("vi", "VN", "VN:vi", "Nga (thăm OR \"hội đàm\")"),
    ("id", "ID", "ID:id", "Rusia (kunjungan OR pertemuan)"),
]

# Direct RSS feeds (add ministry or foreign-government feeds here)
FEEDS = {
    "ТАСС": "https://tass.ru/rss/v2.xml",
    "TASS (EN)": "https://tass.com/rss/v2.xml",
    "РИА Новости": "https://ria.ru/export/rss2/archive/index.xml",
    "Интерфакс": "https://www.interfax.ru/rss.asp",
    "Кремль": "http://kremlin.ru/events/all/feed",
    "Правительство РФ": "http://government.ru/all/rss/",
}

# Official websites without an RSS feed: the program reads the news list page and picks
# links that match "link" (a regular expression). Each new link = one news item.
PAGE_SOURCES = [
    {"name": "Совет Безопасности РФ (сайт)", "url": "http://www.scrf.gov.ru/news/allnews/",
     "link": r"/news/allnews/\d+/?$"},
    {"name": "РФПИ (сайт)", "url": "https://rdif.ru/", "link": r"fullNews/\d+"},
]

# Public Telegram channels to read (usernames without @).
# CORE channels: every post goes to the AI. Channels from telegram_channels.csv (ministries,
# agencies, embassies, consulates, trade missions...): only posts containing visit/meeting
# words go to the AI, which saves the free AI quota. Edit the CSV to add or remove channels.
TG_CORE = ["MID_Russia", "tass_agency", "rian_ru"]
TG_CHANNELS_FILE = os.environ.get("TG_CHANNELS_FILE") or "telegram_channels.csv"


def load_tg_channels():
    """Returns (ordered list of usernames, {username_lower: display name})."""
    import csv
    labels = {"mid_russia": "МИД России", "tass_agency": "ТАСС", "rian_ru": "РИА Новости"}
    order = list(TG_CORE)
    try:
        with open(TG_CHANNELS_FILE, encoding="utf-8-sig") as f:
            for row in csv.DictReader(f, delimiter=";"):
                ch = (row.get("канал") or "").strip().lstrip("@")
                ch = re.sub(r"^https?://(www\.)?t\.me/(s/)?", "", ch).split("/")[0]
                if not re.fullmatch(r"[A-Za-z0-9_]{4,}", ch or ""):
                    continue
                if ch.lower() not in {c.lower() for c in order}:
                    order.append(ch)
                labels.setdefault(ch.lower(), (row.get("название") or "").strip() or f"@{ch}")
    except FileNotFoundError:
        print(f"[telegram] {TG_CHANNELS_FILE} not found - reading core channels only")
    return order, labels


TG_CHANNELS, TG_LABELS = load_tg_channels()
TG_CORE_LOWER = {c.lower() for c in TG_CORE}


def tg_label(ch):
    return f"{TG_LABELS.get(ch.lower(), '@' + ch)} (Telegram)"

# X (Twitter) accounts to follow, without @. Only used if X_BEARER_TOKEN is set.
# Each new post read costs money, so list accounts deliberately. Verify handles on x.com.
X_ACCOUNTS = ["mfa_russia", "MID_RF", "KremlinRussia_E"]

# =============================================================================
# STORAGE
# =============================================================================
db = sqlite3.connect(os.environ.get("DB_PATH", "seen.db"))
db.row_factory = sqlite3.Row
db.executescript("""
CREATE TABLE IF NOT EXISTS seen (h TEXT PRIMARY KEY, ts REAL);
CREATE TABLE IF NOT EXISTS alerts (id INTEGER PRIMARY KEY AUTOINCREMENT, ts REAL,
    summary TEXT, event_date TEXT, url TEXT);
CREATE TABLE IF NOT EXISTS meta (k TEXT PRIMARY KEY, v TEXT);
CREATE TABLE IF NOT EXISTS feedback (id INTEGER PRIMARY KEY AUTOINCREMENT, alert_id INTEGER,
    vote TEXT, user TEXT, ts REAL);
""")
# Add columns introduced in later versions (safe to run every time)
_ALERT_COLS = {"msg_id": "INTEGER", "countries": "TEXT", "officials": "TEXT", "direction": "TEXT",
               "location": "TEXT", "date_start": "TEXT", "date_end": "TEXT", "date_precision": "TEXT",
               "date_label": "TEXT", "date_text": "TEXT", "status": "TEXT", "title_ru": "TEXT",
               "short_ru": "TEXT", "source": "TEXT", "updates": "TEXT", "vote": "TEXT"}
_existing = {r[1] for r in db.execute("PRAGMA table_info(alerts)").fetchall()}
for _c, _t in _ALERT_COLS.items():
    if _c not in _existing:
        db.execute(f"ALTER TABLE alerts ADD COLUMN {_c} {_t}")
db.commit()

HEALTH = {}  # source name -> number of items it returned in this run


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
# PUBLICATION DATES (needed to interpret "on Tuesday", "tomorrow", etc.)
# =============================================================================
def from_struct(tp):
    """feedparser time tuple (UTC) -> aware datetime, or None."""
    try:
        return dt.datetime(*tp[:6], tzinfo=UTC) if tp else None
    except Exception:
        return None


def from_iso(s):
    try:
        return dt.datetime.fromisoformat(s.replace("Z", "+00:00")) if s else None
    except Exception:
        return None


def from_gdelt(s):
    """GDELT seendate like 20261126T081500Z."""
    try:
        return dt.datetime.strptime(s, "%Y%m%dT%H%M%SZ").replace(tzinfo=UTC) if s else None
    except Exception:
        return None


# =============================================================================
# COLLECTORS - each returns a list of {source, title, text, url, uid, published}
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
                print(f"[gdelt] non-JSON reply for query starting '{q[:60]}': {r.text[:150]}")
        except Exception as e:
            print(f"[gdelt error] {e}")
            data = {}
        for a in data.get("articles", []):
            items.append({
                "source": f"{a.get('domain', '')} ({a.get('sourcecountry', '')}, {a.get('language', '')})",
                "title": a.get("title", ""), "text": "", "url": a.get("url", ""),
                "uid": a.get("url", ""), "published": from_gdelt(a.get("seendate")),
            })
        time.sleep(6)  # GDELT asks for gentle request rates
    HEALTH["GDELT"] = len(items)
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
                "published": from_struct(e.get("published_parsed")),
            })
        time.sleep(1)
    HEALTH["Google News"] = len(items)
    return items


def fetch_feeds():
    items = []
    for name, url in FEEDS.items():
        feed = feedparser.parse(url, request_headers=UA)
        HEALTH[name] = len(feed.entries)
        if not feed.entries:
            print(f"[feed] {name}: no entries (blocked or URL changed?)")
        for e in feed.entries:
            items.append({
                "source": name, "title": e.get("title", ""),
                "text": re.sub("<[^>]+>", " ", e.get("summary", "")),
                "url": e.get("link", ""), "uid": e.get("link", "") or e.get("title", ""),
                "published": from_struct(e.get("published_parsed") or e.get("updated_parsed")),
            })
    return items


def fetch_pages():
    """Read news list pages of official websites that have no RSS feed."""
    from bs4 import BeautifulSoup

    items = []
    for src in PAGE_SOURCES:
        found = 0
        try:
            r = requests.get(src["url"], headers=UA, timeout=30)
            soup = BeautifulSoup(r.content, "html.parser")
            pattern = re.compile(src["link"])
            seen_urls = set()
            for a in soup.find_all("a", href=True):
                url = urllib.parse.urljoin(src["url"], a["href"])
                title = a.get_text(" ", strip=True)
                if not pattern.search(url) or len(title) < 20 or url in seen_urls:
                    continue
                seen_urls.add(url)
                found += 1
                items.append({"source": src["name"], "title": title[:300], "text": "", "url": url,
                              "uid": url, "published": None, "channel": "page:" + src["name"],
                              "keyword_filter": False})
        except Exception as ex:
            print(f"[page error] {src['name']}: {ex}")
        HEALTH[src["name"]] = found
        if not found:
            print(f"[page] {src['name']}: no news links found (blocked or page layout changed?)")
    return items


def fetch_telegram_web():
    """Read public channels from their web preview page - no account or login needed."""
    from bs4 import BeautifulSoup

    items, failed = [], []
    for ch in TG_CHANNELS:
        try:
            r = requests.get(f"https://t.me/s/{ch}", headers=UA, timeout=30)
            if r.status_code == 429:          # Telegram asks us to slow down
                time.sleep(15)
                r = requests.get(f"https://t.me/s/{ch}", headers=UA, timeout=30)
            soup = BeautifulSoup(r.text, "html.parser")
            posts = soup.select("div.tgme_widget_message[data-post]")
            HEALTH[f"Telegram @{ch}"] = len(posts)
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
                t = post.select_one("time[datetime]")
                items.append({
                    "source": tg_label(ch), "title": text[:300], "text": text,
                    "url": f"https://t.me/{path}", "uid": f"tg:{ch}:{msg_id}",
                    "published": from_iso(t["datetime"]) if t else None,
                    "channel": ch.lower(), "keyword_filter": ch.lower() not in TG_CORE_LOWER,
                })
        except Exception as e:
            print(f"[telegram web error] {ch}: {e}")
            HEALTH[f"Telegram @{ch}"] = 0
            failed.append(ch)
        time.sleep(0.5)
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
                got = 0
                for m in tg.iter_messages(ch, limit=40):
                    if m.message:
                        got += 1
                        items.append({
                            "source": tg_label(ch), "title": m.message[:300],
                            "text": m.message, "url": f"https://t.me/{ch}/{m.id}",
                            "uid": f"tg:{ch}:{m.id}", "published": m.date,
                            "channel": ch.lower(), "keyword_filter": ch.lower() not in TG_CORE_LOWER,
                        })
                if got:
                    HEALTH[f"Telegram @{ch}"] = got
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
                "published": from_iso(t.get("created_at")),
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
SCREEN_BATCH = int(os.environ.get("SCREEN_BATCH") or "250")  # headlines per AI call
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
    base = os.environ["LLM_BASE_URL"].rstrip("/")
    auth = {"Authorization": f"Bearer {os.environ['LLM_API_KEY']}"}
    # Instructions go inside the user message: works with every model, including
    # ones that reject a separate "system" message (e.g. Gemma).
    r = requests.post(
        base + "/chat/completions", headers=auth,
        json={"model": model, "max_tokens": max_tokens, "temperature": 0,
              "messages": [{"role": "user", "content": f"{system}\n\n=====\n\n{user}"}]},
        timeout=120)
    if r.status_code == 429:
        raise RuntimeError("429 rate limit / quota")
    if r.status_code in (400, 404) and "model" in r.text.lower():
        try:
            names = [m["id"] for m in requests.get(base + "/models", headers=auth, timeout=30).json()["data"]]
            print(f"[AI] model '{model}' was rejected. Model names your key can use:\n  " + "\n  ".join(names))
        except Exception:
            pass
    if not r.ok:
        raise RuntimeError(f"{r.status_code} {r.text[:300]}")
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
    today = dt.datetime.now(MSK).date().isoformat()
    if meta_get("ai_down_alert") != today:
        send("⚠️ <b>ИИ временно недоступен</b> (вероятно, исчерпан дневной лимит запросов).\n"
             "Мониторинг продолжается в резервном режиме: материалы отбираются по ключевым словам "
             "и помечаются «❔ НЕ ПРОВЕРЕНО». Это сообщение приходит не чаще раза в день.")
        meta_set("ai_down_alert", today)
    return None


# Free fallback when the AI is unavailable: text must mention Russia AND a visit/meeting word
RUSSIA_RE = re.compile(
    r"росси|рф\b|кремл|москв|путин|лавров|мишустин|russia|kremlin|moscow|putin|lavrov|俄|روسي|"
    r"rusia|russie|russland|rusya|rússia|रूस|ロシア|러시아|รัสเซีย|orosz|rusk|rusij|русиј", re.IGNORECASE)
VISIT_RE = re.compile(
    r"визит|посет|переговор|встреч|делегаци|межправкомисс|прибуд|посет|visit|talks|delegation|meet|summit|"
    r"访|訪|会谈|會談|会见|會見|زيارة|مباحثات|وفد|visita|reuni|visite|entretien|besuch|gespräch|ziyaret|görüş|heyet|"
    r"यात्रा|दौरा|वार्ता|会談|방문|회담|kunjungan|pertemuan|เยือน|หารือ|látogat|tárgyal|návštev|rokovan|poset|razgovor",
    re.IGNORECASE)


# Prefilter for posts from official channels (ministries, embassies...): a post must contain
# a visit/meeting word (Russian or the languages these channels post in) to reach the AI.
TG_VISIT_RE = re.compile(
    VISIT_RE.pattern + r"|встрет|прибыл|прибыв|поездк|командиров|консультаци|двусторон|межправ|саммит|"
    r"форум|посол|переговор|рабоч\w* визит|соглашени|меморандум", re.IGNORECASE)


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

VERIFY_PROMPT = """You verify news items for a Russian-speaking analyst tracking visits and meetings
between Russian government officials and officials of other countries. You get several numbered ITEMS,
each with its publication date.

An item is RELEVANT if it announces or reports a visit/trip/meeting/talks/commission/dialogue that is
UPCOMING or UNDER WAY (not fully concluded), involving:
- a Russian state official (president, PM, deputy PMs, ministers, deputy ministers, heads of federal
  agencies, Kremlin staff, presidential envoys, ambassadors-at-large, Federal Assembly leadership,
  central bank leadership, heads of major state corporations acting officially), AND
- officials of any foreign country or international organization; in either direction.
NOT relevant: events that already ended, purely domestic trips, sports/culture tours, pure speculation,
battlefield news.

You also get RECENT ALERTS already sent (with their known date and status). If an item is about the
same event as one of them, set duplicate_of to that alert id and set change_type:
  "date_confirmed" - the alert had no exact date (or only a week/month) and this item gives the day;
  "date_changed"   - the alert had an exact date and this item clearly gives a DIFFERENT date;
  "postponed"      - the item says the event is postponed/delayed (with or without a new date);
  "cancelled"      - the item says the event is cancelled / will not take place;
  "other_update"   - materially new facts (participants, location, agenda) - describe them in new_info;
  "none"           - nothing new.
For duplicates still fill the date fields with what THIS item says.
Items about postponement or cancellation of an event NOT in recent alerts are relevant too
(use status "announced" and say so in the summary).
If several items in this batch describe the same event, return it ONCE (most informative item).

If ANALYST FEEDBACK is provided, follow it: avoid alerts similar to ones marked NOT useful.

LANGUAGE: write summary, new_info, officials, countries, location, title_ru and short_ru IN RUSSIAN
(standard Russian spelling of names and countries, e.g. "Антон Силуанов, министр финансов РФ").
title_ru = the item's headline translated into natural Russian (if already Russian, copy it as is).
short_ru = a very short Russian label, max 8 words, e.g. "визит главы МИД Вьетнама в Москву".

DATES - do NOT calculate calendar dates yourself for weekdays or relative words. Only describe what
the text says, using these DATEREF objects; the program computes the actual date:
  {"kind":"absolute","day":24,"month":11,"year":2026}   (year null if the text gives none)
  {"kind":"weekday","weekday":"tuesday","modifier":"none"}
       modifier: "this" (this week / в этот вторник), "next" (next week's / в следующий вторник),
                 "last" (last week's), or "none" (just "on Tuesday" / "во вторник")
  {"kind":"relative","days":1}   (today 0, tomorrow 1, day after tomorrow 2, yesterday -1)
  {"kind":"week","modifier":"this"|"next"}   ("this week", "next week")
  {"kind":"month","month":12,"year":null,"part":"early"|"mid"|"late"|"whole"}
  {"kind":"unknown"}
tense: "future" if the text describes the event as upcoming, "present" if happening now/today,
"past" if it already took place (fully or partly).

Return ONLY relevant items, as ONLY JSON:
{"results": [
 {"n": item number,
  "confidence": "high" | "medium",
  "duplicate_of": alert id number or null,
  "change_type": "none" | "date_confirmed" | "date_changed" | "postponed" | "cancelled" | "other_update",
  "new_info": "",
  "title_ru": "заголовок на русском",
  "short_ru": "короткая метка",
  "status": "announced" | "under_way",
  "tense": "future" | "present" | "past",
  "officials": "имена и должности",
  "countries": "страна/страны или организации",
  "direction": "outbound" | "inbound" | "elsewhere",
  "location": "город, страна",
  "date_text": "the exact words about timing, as written in the article (original language), or empty",
  "date_start": DATEREF,
  "date_end": DATEREF or null,
  "summary": "одно-два предложения на русском"}
]}
direction: outbound = Russian officials travel abroad; inbound = foreign officials come to Russia;
elsewhere = meeting in a third country or online.
If none are relevant: {"results": []}"""


def screen(items):
    """Stage 1: batch headlines through the AI (keyword fallback if AI unavailable)."""
    keep = []
    for i in range(0, len(items), SCREEN_BATCH):
        batch = items[i:i + SCREEN_BATCH]
        lines = "\n".join(f"{n}. {it['title'][:200]}" for n, it in enumerate(batch))
        res = ask_json(SCREEN_MODEL, SCREEN_PROMPT, lines, max_tokens=1000)
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
        page = requests.get(item["url"], headers=UA, timeout=20).text
        extracted = trafilatura.extract(page) or ""
        return (extracted or text)[:limit]
    except Exception:
        return text[:limit]


def recent_alerts_block():
    cutoff = time.time() - 21 * 86400
    rows = db.execute("SELECT id, summary, event_date, date_label, status FROM alerts "
                      "WHERE ts > ? AND COALESCE(status,'active') != 'unverified' ORDER BY id DESC LIMIT 150",
                      (cutoff,)).fetchall()
    return "\n".join(f"[{r['id']}] {r['summary']} | known date: {r['date_label'] or r['event_date']} "
                     f"| status: {r['status'] or 'active'}" for r in rows) or "(none)"


def feedback_block():
    rows = db.execute("SELECT title_ru, summary, vote FROM alerts WHERE vote IS NOT NULL "
                      "ORDER BY id DESC LIMIT 30").fetchall()
    if not rows:
        return ""
    lines = ["ANALYST FEEDBACK on earlier alerts ('NOT useful' = do not send alerts like this):"]
    for r in rows:
        lines.append(f"- [{'useful' if r['vote'] == 'up' else 'NOT useful'}] {r['summary'] or r['title_ru']}")
    return "\n".join(lines) + "\n\n"


# =============================================================================
# DATE RESOLUTION
# =============================================================================
WEEKDAYS = {"monday": 0, "tuesday": 1, "wednesday": 2, "thursday": 3,
            "friday": 4, "saturday": 5, "sunday": 6}
WD_RU = ["понедельник", "вторник", "среда", "четверг", "пятница", "суббота", "воскресенье"]
MON_GEN = ["января", "февраля", "марта", "апреля", "мая", "июня", "июля", "августа",
           "сентября", "октября", "ноября", "декабря"]
MON_NOM = ["январь", "февраль", "март", "апрель", "май", "июнь", "июль", "август",
           "сентябрь", "октябрь", "ноябрь", "декабрь"]


def pub_date_msk(item):
    """Publication date of the item in Moscow time; falls back to 'now'."""
    p = item.get("published")
    if isinstance(p, dt.datetime):
        if p.tzinfo is None:
            p = p.replace(tzinfo=UTC)
        return p.astimezone(MSK).date()
    return dt.datetime.now(MSK).date()


def resolve_ref(ref, pub, tense):
    """Turn a DATEREF into ('day', date) / ('week', monday) / ('month', (y, m, part)) or None.

    Weekday rule ("во вторник" without "this/next/last"):
      - start from the weekday in the SAME Monday-Sunday week as the publication date;
      - if the event is described as upcoming (future tense) and that day is already
        before the publication day, move to the following week;
      - if the event is described in the past tense and that day is after the
        publication day, move to the previous week.
      Example: published Thursday 26 Nov 2026, "on Tuesday" about this week's news
      (present/past) -> Tuesday 24 Nov; an announcement "will visit on Tuesday" -> Tuesday 1 Dec.
    """
    if not isinstance(ref, dict):
        return None
    kind = ref.get("kind")
    try:
        if kind == "absolute":
            d, m, y = int(ref["day"]), int(ref["month"]), ref.get("year")
            if y:
                return ("day", dt.date(int(y), m, d))
            cands = []
            for yy in (pub.year - 1, pub.year, pub.year + 1):
                try:
                    cands.append(dt.date(yy, m, d))
                except ValueError:
                    pass
            if tense == "future":
                upcoming = [c for c in cands if c >= pub - dt.timedelta(days=3)]
                if upcoming:
                    return ("day", min(upcoming))
            return ("day", min(cands, key=lambda c: abs((c - pub).days)))

        if kind == "relative":
            return ("day", pub + dt.timedelta(days=int(ref["days"])))

        if kind == "weekday":
            wd = WEEKDAYS[str(ref["weekday"]).lower()]
            monday = pub - dt.timedelta(days=pub.weekday())
            cand = monday + dt.timedelta(days=wd)
            mod = ref.get("modifier") or "none"
            if mod == "next":
                cand += dt.timedelta(days=7)
            elif mod == "last":
                cand -= dt.timedelta(days=7)
            elif mod == "none":
                if tense == "future" and cand < pub:
                    cand += dt.timedelta(days=7)
                elif tense == "past" and cand > pub:
                    cand -= dt.timedelta(days=7)
            return ("day", cand)

        if kind == "week":
            monday = pub - dt.timedelta(days=pub.weekday())
            if ref.get("modifier") == "next":
                monday += dt.timedelta(days=7)
            return ("week", monday)

        if kind == "month":
            m = int(ref["month"])
            y = int(ref["year"]) if ref.get("year") else (pub.year + 1 if m < pub.month - 6 else pub.year)
            return ("month", (y, m, ref.get("part") or "whole"))
    except Exception as e:
        print(f"[date] could not resolve {ref}: {e}")
    return None


def fmt_day(d, with_year=True):
    s = f"{WD_RU[d.weekday()]}, {d.day} {MON_GEN[d.month - 1]}"
    return f"{s} {d.year}" if with_year else s


def fmt_resolved(r):
    kind, val = r
    if kind == "day":
        return fmt_day(val)
    if kind == "week":
        sun = val + dt.timedelta(days=6)
        return f"неделя с {val.day} {MON_GEN[val.month - 1]} по {sun.day} {MON_GEN[sun.month - 1]} {sun.year}"
    if kind == "month":
        y, m, part = val
        prefix = {"early": "начало", "mid": "середина", "late": "конец"}.get(part)
        return f"{prefix} {MON_GEN[m - 1]} {y}" if prefix else f"{MON_NOM[m - 1]} {y}"
    return ""


def resolve_when(res, item):
    """Resolve the AI's date description into stored fields.
    Returns {"label", "text", "start", "end", "precision"} where precision is
    "day" (exact day or day range), "week", "month" or "none"."""
    pub = pub_date_msk(item)
    tense = res.get("tense") or ("future" if res.get("status") == "announced" else "present")
    start = resolve_ref(res.get("date_start"), pub, tense)
    end = resolve_ref(res.get("date_end"), pub, tense) if res.get("date_end") else None
    out = {"text": (res.get("date_text") or "").strip(), "start": None, "end": None,
           "precision": "none", "label": "не указано"}
    if not start:
        return out
    kind, val = start
    if kind == "day":
        out.update(precision="day", start=val.isoformat(), end=val.isoformat(), label=fmt_day(val))
        if end and end[0] == "day" and end[1] > val:
            b = end[1]
            out.update(end=b.isoformat(),
                       label=f"с {fmt_day(val, with_year=(val.year != b.year))} по {fmt_day(b)}")
    elif kind == "week":
        sun = val + dt.timedelta(days=6)
        out.update(precision="week", start=val.isoformat(), end=sun.isoformat(), label=fmt_resolved(start))
    elif kind == "month":
        y, m, part = val
        last = (dt.date(y + (m == 12), m % 12 + 1, 1) - dt.timedelta(days=1)).day
        a, b = {"early": (1, 10), "mid": (11, 20), "late": (21, last)}.get(part, (1, last))
        out.update(precision="month", start=dt.date(y, m, a).isoformat(),
                   end=dt.date(y, m, b).isoformat(), label=fmt_resolved(start))
    return out


def when_with_text(w):
    return w["label"] + (f" (в тексте: «{w['text']}»)" if w.get("text") else "")


# =============================================================================
# TELEGRAM OUTPUT (HTML formatting, links as hyperlinks)
# =============================================================================
DIRECTION_RU = {
    "outbound": "Россия → за рубеж",
    "inbound": "визит в Россию",
    "elsewhere": "встреча в третьей стране / онлайн",
}
WD_SHORT = ["пн", "вт", "ср", "чт", "пт", "сб", "вс"]
MON_SHORT = ["янв", "фев", "мар", "апр", "мая", "июн", "июл", "авг", "сен", "окт", "ноя", "дек"]

FEEDBACK_ON = (os.environ.get("FEEDBACK_BUTTONS") or "on").strip().lower() not in ("off", "0", "no", "false", "нет")


def e(s):
    return html.escape(str(s or ""), quote=False)


def link(url, text):
    return f'<a href="{html.escape(url or "", quote=True)}">{e(text)}</a>'


def tg(method, payload=None, files=None):
    """Call the Telegram Bot API; returns the 'result' or None."""
    token = os.environ["TELEGRAM_BOT_TOKEN"]
    try:
        if files:
            r = requests.post(f"https://api.telegram.org/bot{token}/{method}", data=payload, files=files, timeout=60)
        else:
            r = requests.post(f"https://api.telegram.org/bot{token}/{method}", json=payload or {}, timeout=30)
        body = r.json()
        if not body.get("ok"):
            print(f"[telegram {method} error] {r.status_code} {body.get('description')}")
            return None
        return body.get("result")
    except Exception as ex:
        print(f"[telegram {method} error] {ex}")
        return None


def send(text_html, reply_to=None, markup=None):
    """Send an HTML message; returns its message_id (or None)."""
    payload = {"chat_id": os.environ["TELEGRAM_CHAT_ID"], "text": text_html[:4096],
               "parse_mode": "HTML", "disable_web_page_preview": True}
    if reply_to:
        payload["reply_parameters"] = {"message_id": int(reply_to), "allow_sending_without_reply": True}
    if markup:
        payload["reply_markup"] = markup
    res = tg("sendMessage", payload)
    return res.get("message_id") if res else None


def fb_markup(alert_id, vote=None):
    return {"inline_keyboard": [[
        {"text": "👍 Полезно" + (" ✓" if vote == "up" else ""), "callback_data": f"fb:up:{alert_id}"},
        {"text": "👎 Не то" + (" ✓" if vote == "down" else ""), "callback_data": f"fb:down:{alert_id}"},
    ]]}


def alert_message(r, it, w):
    status = "🟢 <b>Проходит сейчас</b>" if r.get("status") == "under_way" else "🛬 <b>Анонс визита</b>"
    lines = []
    if r.get("confidence") == "medium":
        lines.append("⚠️ <i>Не подтверждено — требует проверки</i>")
    lines += [
        f"{status}: Россия ⇄ {e(r.get('countries'))}",
        "",
        e(r.get("summary")),
        "",
        f"👤 <b>Кто:</b> {e(r.get('officials'))}",
        f"🧭 <b>Направление:</b> {e(DIRECTION_RU.get(r.get('direction'), r.get('direction')))}",
        f"📍 <b>Где:</b> {e(r.get('location'))}",
        f"📅 <b>Когда:</b> {e(when_with_text(w))}",
        "",
        f"🔗 {link(it['url'], (r.get('title_ru') or it['title'])[:200])} — {e(it['source'])}",
    ]
    return "\n".join(lines)


# =============================================================================
# ALERTS AND FOLLOW-UPS
# =============================================================================
def now_msk_str():
    return dt.datetime.now(MSK).strftime("%d.%m.%Y %H:%M")


def create_alert(r, it, w):
    cur = db.execute(
        "INSERT INTO alerts (ts, summary, event_date, url, countries, officials, direction, location, "
        "date_start, date_end, date_precision, date_label, date_text, status, title_ru, short_ru, source, updates) "
        "VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
        (time.time(), r.get("summary", ""), w["start"] or w["label"], it["url"], r.get("countries", ""),
         r.get("officials", ""), r.get("direction", ""), r.get("location", ""), w["start"], w["end"],
         w["precision"], w["label"], w["text"], "active", r.get("title_ru") or it["title"],
         r.get("short_ru") or "", it["source"], ""))
    aid = cur.lastrowid
    db.commit()
    mid = send(alert_message(r, it, w), markup=fb_markup(aid) if FEEDBACK_ON else None)
    db.execute("UPDATE alerts SET msg_id=? WHERE id=?", (mid, aid))
    db.commit()


def old_precision(row):
    if row["date_precision"]:
        return row["date_precision"]
    # alerts saved by older versions of this script
    ev = (row["event_date"] or "").strip().lower()
    return "none" if ev in ("", "не указано", "not stated", "не проверено") else "day"


def handle_update(row, r, it, w):
    """An item about an event we already alerted. Decide what changed and reply to the original."""
    ct = r.get("change_type") or "none"
    old_prec = old_precision(row)
    old_label = row["date_label"] or row["event_date"] or "не указано"
    new_day = w["precision"] == "day"
    date_differs = (w["start"], w["end"]) != (row["date_start"], row["date_end"])

    if ct == "cancelled":
        kind = "cancelled"
    elif ct == "postponed":
        kind = "postponed"
    elif new_day and old_prec != "day":
        kind = "confirmed"
    elif new_day and old_prec == "day" and ct == "date_changed" and date_differs:
        kind = "changed"
    elif ct in ("other_update", "date_changed") and r.get("new_info"):
        kind = "info"
    else:
        return
    if kind == "cancelled" and row["status"] == "cancelled":
        return  # already reported

    new_label = f"<b>{e(w['label'])}</b>" + (f" (в тексте: «{e(w['text'])}»)" if w.get("text") else "")
    old_l = e(old_label)
    headers = {"confirmed": "📅 <b>Дата подтверждена</b>", "changed": "🔁 <b>Дата изменена</b>",
               "postponed": "⏸ <b>Визит отложен</b>", "cancelled": "❌ <b>Визит отменён</b>",
               "info": "🔄 <b>Новые сведения</b>"}
    if kind == "confirmed":
        prev = " без точной даты" if old_prec == "none" else f" (ориентировочно: {old_l})"
        body = f"Этот визит был анонсирован ранее{prev}. Теперь дата подтверждена: {new_label}."
    elif kind == "changed":
        body = (f"Этот визит был анонсирован ранее, дата: <b>{old_l}</b>. "
                f"Теперь дата изменена: {new_label}.")
    elif kind == "postponed":
        body = (f"Этот визит был анонсирован ранее (дата: {old_l}). Теперь сообщается, что он отложен. "
                + (f"Новая дата: {new_label}." if new_day else "Новая дата пока не объявлена."))
    elif kind == "cancelled":
        body = f"Этот визит был анонсирован ранее (дата: {old_l}). Теперь сообщается об отмене."
    else:
        body = "Этот визит был анонсирован ранее. Появились новые сведения."

    lines = [f"{headers[kind]}: Россия ⇄ {e(row['countries'] or r.get('countries'))}", "", body]
    if r.get("new_info"):
        lines += ["", f"ℹ️ {e(r['new_info'])}"]
    lines += ["",
              f"<blockquote><b>Исходное оповещение:</b>\n{e(row['summary'])}\nКогда: {old_l}</blockquote>",
              f"🔗 {link(it['url'], (r.get('title_ru') or it['title'])[:200])} — {e(it['source'])}"]
    send("\n".join(lines), reply_to=row["msg_id"])

    # Update the stored event
    status = {"cancelled": "cancelled", "postponed": "active" if new_day else "postponed"}.get(kind, "active")
    if new_day or (kind == "confirmed"):
        db.execute("UPDATE alerts SET date_start=?, date_end=?, date_precision=?, date_label=?, date_text=?, "
                   "event_date=? WHERE id=?",
                   (w["start"], w["end"], w["precision"], w["label"], w["text"], w["start"], row["id"]))
    note = f"{now_msk_str()}: {headers[kind].replace('<b>', '').replace('</b>', '')}"
    if new_day:
        note += f" — {w['label']}"
    if r.get("new_info"):
        note += f" — {r['new_info']}"
    db.execute("UPDATE alerts SET status=?, updates=COALESCE(updates,'') || ? || ' | ' WHERE id=?",
               (status, note, row["id"]))
    db.commit()


# =============================================================================
# FEEDBACK BUTTONS
# =============================================================================
def process_feedback():
    """Read 👍/👎 clicks since the last run and store them."""
    offset = int(meta_get("tg_offset") or 0)
    updates = tg("getUpdates", {"offset": offset, "timeout": 0}) or []
    for u in updates:
        offset = max(offset, u["update_id"] + 1)
        cq = u.get("callback_query")
        if not cq:
            continue
        tg("answerCallbackQuery", {"callback_query_id": cq["id"], "text": "Спасибо, оценка учтена"})
        m = re.match(r"fb:(up|down):(\d+)$", cq.get("data", ""))
        if not m:
            continue
        vote, aid = m.group(1), int(m.group(2))
        who = (cq.get("from") or {}).get("first_name", "")
        db.execute("INSERT INTO feedback (alert_id, vote, user, ts) VALUES (?, ?, ?, ?)", (aid, vote, who, time.time()))
        db.execute("UPDATE alerts SET vote=? WHERE id=?", (vote, aid))
        msg = cq.get("message") or {}
        if FEEDBACK_ON and msg.get("message_id"):
            tg("editMessageReplyMarkup", {"chat_id": msg["chat"]["id"], "message_id": msg["message_id"],
                                          "reply_markup": fb_markup(aid, vote)})
    db.commit()
    meta_set("tg_offset", str(offset))


def remove_buttons_if_disabled():
    """When FEEDBACK_BUTTONS=off: remove the buttons from all earlier alerts, once."""
    if FEEDBACK_ON:
        if meta_get("buttons_removed"):
            meta_set("buttons_removed", "")
        return
    if meta_get("buttons_removed"):
        return
    chat = os.environ["TELEGRAM_CHAT_ID"]
    for row in db.execute("SELECT msg_id FROM alerts WHERE msg_id IS NOT NULL").fetchall():
        tg("editMessageReplyMarkup", {"chat_id": chat, "message_id": row["msg_id"],
                                      "reply_markup": {"inline_keyboard": []}})
        time.sleep(0.1)
    meta_set("buttons_removed", "1")


# =============================================================================
# HEALTH CHECKS (instant failure alerts)
# =============================================================================
HEALTH_THRESHOLD = 3  # consecutive runs with nothing from a source before alerting


def health_name(key):
    """Readable name for a source key; Telegram keys look like 'Telegram @channel'."""
    if key.startswith("Telegram @"):
        ch = key[len("Telegram @"):]
        return f"{TG_LABELS.get(ch.lower(), '@' + ch)} (@{ch})"
    return key


def check_health():
    """One combined message per run for sources that stopped / started working again."""
    state = json.loads(meta_get("health") or "{}")
    down, up = [], []
    for name, n in HEALTH.items():
        s = state.setdefault(name, {"zero": 0, "alerted": False})
        if n > 0:
            if s["alerted"]:
                up.append(name)
            s.update(zero=0, alerted=False)
        else:
            s["zero"] += 1
            if s["zero"] >= HEALTH_THRESHOLD and not s["alerted"]:
                down.append(name)
                s["alerted"] = True
    state = {k: v for k, v in state.items() if k in HEALTH}
    meta_set("health", json.dumps(state, ensure_ascii=False))

    def listing(names, limit=40):
        shown = [f"• {e(health_name(n))}" for n in names[:limit]]
        if len(names) > limit:
            shown.append(f"• … и ещё {len(names) - limit}")
        return "\n".join(shown)

    if down:
        send(f"⚠️ <b>Источники не отвечают</b> ({len(down)}) — нет данных {HEALTH_THRESHOLD} запуска подряд:\n"
             f"{listing(down)}\n\nОстальные источники работают. Сообщу, когда эти восстановятся.")
    if up:
        send(f"✅ <b>Источники снова работают</b> ({len(up)}):\n{listing(up)}")
    return [health_name(k) for k, v in state.items() if v["alerted"]]


def heartbeat(n_collected, broken):
    hour = int(os.environ.get("HEARTBEAT_HOUR_UTC") or "6")
    now = dt.datetime.now(UTC)
    today = now.date().isoformat()
    if now.hour >= hour and meta_get("heartbeat") != today:
        day_ago = time.time() - 86400
        scanned = db.execute("SELECT COUNT(*) FROM seen WHERE ts > ?", (day_ago,)).fetchone()[0]
        alerts = db.execute("SELECT COUNT(*) FROM alerts WHERE ts > ?", (day_ago,)).fetchone()[0]
        msg = (f"✅ <b>Мониторинг визитов работает.</b>\n"
               f"За последние 24 часа: проверено ~{scanned // 2} новых материалов, "
               f"отправлено оповещений: {alerts}.\n"
               f"В этом запуске собрано материалов: {n_collected}.")
        if broken:
            shown = ", ".join(broken[:15]) + (f" и ещё {len(broken) - 15}" if len(broken) > 15 else "")
            msg += f"\n⚠️ Не отвечают ({len(broken)}): {e(shown)}."
        send(msg)
        meta_set("heartbeat", today)


# =============================================================================
# WEEKLY DIGEST + ARCHIVE (no AI requests used)
# =============================================================================
def short_day(iso):
    d = dt.date.fromisoformat(iso)
    return f"{WD_SHORT[d.weekday()]}, {d.day} {MON_SHORT[d.month - 1]}"


def digest_line(row):
    label = row["short_ru"] or row["title_ru"] or row["summary"]
    return f"• {e(row['countries'])} — {link(row['url'], label)}"


def build_digest(today):
    start = today + dt.timedelta(days=1)                            # from tomorrow (Saturday)
    end = today + dt.timedelta(days=(7 - today.weekday()) + 6)      # to Sunday of next week
    rows = db.execute(
        "SELECT * FROM alerts WHERE status IN ('active','postponed') AND date_start IS NOT NULL "
        "AND date_start <= ? AND COALESCE(date_end, date_start) >= ? ORDER BY date_start",
        (end.isoformat(), start.isoformat())).fetchall()
    dated = [r for r in rows if r["date_precision"] == "day" and r["status"] == "active"]
    vague = [r for r in rows if r["date_precision"] in ("week", "month") or r["status"] == "postponed"]
    recent = time.time() - 14 * 86400
    vague += db.execute("SELECT * FROM alerts WHERE status IN ('active','postponed') AND "
                        "COALESCE(date_precision,'none')='none' AND ts > ? ORDER BY ts DESC LIMIT 8",
                        (recent,)).fetchall()

    title = (f"📋 <b>Визиты на предстоящую неделю</b> "
             f"({start.day} {MON_GEN[start.month - 1]} – {end.day} {MON_GEN[end.month - 1]})")
    lines = [title, ""]
    if not dated and not vague:
        lines.append("Анонсированных визитов на этот период нет.")
        return "\n".join(lines)

    current = None
    for r in dated:
        day = max(r["date_start"], start.isoformat())
        if day != current:
            if current:
                lines.append("")
            lines.append(f"<b>{short_day(day)}</b>")
            current = day
        extra = f" (до {short_day(r['date_end'])})" if r["date_end"] and r["date_end"] > r["date_start"] else ""
        lines.append(digest_line(r) + extra)

    if vague:
        lines += ["", "<b>Дата уточняется</b>"]
        for r in vague[:10]:
            note = "отложен" if r["status"] == "postponed" else (r["date_label"] or "дата не объявлена")
            lines.append(f"{digest_line(r)} ({e(note)})")

    text = "\n".join(lines)
    if len(text) > 4000:
        text = text[:3900].rsplit("\n", 1)[0] + "\n…список сокращён, полный перечень — в архиве ниже."
    return text


def send_archive():
    import csv
    path = "visit_archive.csv"
    cols = [("id", "№"), ("ts", "Отправлено"), ("status", "Статус"), ("countries", "Страны"),
            ("officials", "Участники"), ("direction", "Направление"), ("location", "Место"),
            ("date_start", "Дата начала"), ("date_end", "Дата окончания"), ("date_label", "Дата (текстом)"),
            ("date_text", "Формулировка в источнике"), ("summary", "Описание"), ("title_ru", "Заголовок"),
            ("source", "Источник"), ("url", "Ссылка"), ("vote", "Оценка"), ("updates", "История изменений")]
    status_ru = {"active": "активен", "postponed": "отложен", "cancelled": "отменён", "unverified": "не проверен"}
    rows = db.execute("SELECT * FROM alerts ORDER BY id").fetchall()
    with open(path, "w", newline="", encoding="utf-8-sig") as f:   # BOM + ';' = opens correctly in Excel
        w = csv.writer(f, delimiter=";")
        w.writerow([c[1] for c in cols])
        for r in rows:
            vals = []
            for c, _ in cols:
                v = r[c]
                if c == "ts" and v:
                    v = dt.datetime.fromtimestamp(v, MSK).strftime("%d.%m.%Y %H:%M")
                elif c in ("date_start", "date_end") and v:
                    try:
                        v = dt.date.fromisoformat(v).strftime("%d.%m.%Y")
                    except ValueError:
                        pass
                elif c == "status":
                    v = status_ru.get(v or "active", v)
                elif c == "direction":
                    v = DIRECTION_RU.get(v, v)
                elif c == "vote":
                    v = {"up": "👍", "down": "👎"}.get(v, "")
                vals.append(v if v is not None else "")
            w.writerow(vals)
    name = f"архив_визитов_{dt.datetime.now(MSK).date().isoformat()}.csv"
    with open(path, "rb") as f:
        tg("sendDocument", {"chat_id": os.environ["TELEGRAM_CHAT_ID"],
                            "caption": f"🗂 Архив всех оповещений ({len(rows)}). Открывается в Excel."},
           files={"document": (name, f, "text/csv")})


def weekly_digest():
    now = dt.datetime.now(MSK)
    weekday = int(os.environ.get("DIGEST_WEEKDAY") or "4")   # 0 = Monday ... 4 = Friday
    hour = int(os.environ.get("DIGEST_HOUR_MSK") or "12")
    today = now.date()
    if now.weekday() != weekday or now.hour < hour or meta_get("digest_sent") == today.isoformat():
        return
    send(build_digest(today))
    send_archive()
    meta_set("digest_sent", today.isoformat())


# =============================================================================
# MAIN
# =============================================================================
def run_once():
    first_run = meta_get("initialized") is None

    try:
        process_feedback()
        remove_buttons_if_disabled()
    except Exception as ex:
        print(f"[feedback error] {ex}")

    collected = []
    for fn in (fetch_feeds, fetch_pages, fetch_telegram_web, fetch_telegram_channels, fetch_x, fetch_gnews, fetch_gdelt):
        try:
            got = fn()
            print(f"{fn.__name__}: {len(got)} items")
            collected += got
        except Exception as ex:
            print(f"[{fn.__name__} failed] {ex}")
    broken = check_health()

    # Channels read successfully for the first time: record their existing posts silently,
    # so adding many channels at once doesn't produce a flood of old news.
    known = set(json.loads(meta_get("tg_known_channels") or "[]"))
    fresh_channels = {it["channel"] for it in collected if it.get("channel")} - known
    if fresh_channels and not first_run:
        print(f"[telegram] new channels, recording existing posts silently: {len(fresh_channels)}")

    # Dedupe by URL and by normalized headline (same story across outlets/sources)
    new_items, now, prefiltered = [], time.time(), 0
    for it in collected:
        keys = [h("u:" + it["uid"]), h("t:" + norm_title(it["title"]))]
        if any(db.execute("SELECT 1 FROM seen WHERE h=?", (k,)).fetchone() for k in keys):
            continue
        for k in keys:
            db.execute("INSERT OR IGNORE INTO seen (h, ts) VALUES (?, ?)", (k, now))
        if not it["title"].strip() or it.get("channel") in fresh_channels:
            continue
        if it.get("keyword_filter") and not TG_VISIT_RE.search(it.get("text") or it["title"]):
            prefiltered += 1
            continue
        new_items.append(it)
    db.commit()
    meta_set("tg_known_channels", json.dumps(sorted(known | fresh_channels)))
    print(f"New items: {len(new_items)} (official-channel posts skipped by keyword prefilter: {prefiltered})")

    if first_run:
        print("First run: recorded existing items, no alerts sent.")
        send("✅ <b>Мониторинг визитов запущен.</b> Оповещения начнутся со следующего запуска.")
        meta_set("initialized", "1")
        meta_set("heartbeat", dt.datetime.now(UTC).date().isoformat())
        return

    shortlist = screen(new_items)
    print(f"Shortlisted: {len(shortlist)}")

    sent = 0
    for i in range(0, len(shortlist), VERIFY_BATCH):
        batch = shortlist[i:i + VERIFY_BATCH]
        user = (feedback_block() + f"RECENT ALERTS:\n{recent_alerts_block()}\n\n" + "\n\n".join(
            f"ITEM {n}\nSource: {it['source']}\nPublished: "
            f"{pub_date_msk(it).isoformat()} ({WD_RU[pub_date_msk(it).weekday()]})\n"
            f"URL: {it['url']}\nTitle: {it['title']}\nText: {article_text(it)}"
            for n, it in enumerate(batch)))
        res = ask_json(VERIFY_MODEL, VERIFY_PROMPT, user, max_tokens=3500)

        if res is None:
            # AI unavailable: still alert, clearly marked, so nothing is silently lost
            for it in batch:
                if not keyword_match(it):
                    continue
                db.execute("INSERT INTO alerts (ts, summary, event_date, url, status, title_ru, source, "
                           "date_precision, date_label) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
                           (time.time(), it["title"][:300], "не проверено", it["url"], "unverified",
                            it["title"], it["source"], "none", "не проверено"))
                db.commit()
                send(f"❔ <b>НЕ ПРОВЕРЕНО</b> (ИИ недоступен, отбор по ключевым словам; "
                     f"заголовок на языке оригинала)\n\n"
                     f"🔗 {link(it['url'], it['title'][:200])} — {e(it['source'])}")
                sent += 1
            continue

        for r in res.get("results", []):
            n = r.get("n")
            if not isinstance(n, int) or not 0 <= n < len(batch):
                continue
            it = batch[n]
            w = resolve_when(r, it)
            dup = r.get("duplicate_of")
            row = db.execute("SELECT * FROM alerts WHERE id=?", (dup,)).fetchone() if isinstance(dup, int) else None
            if row:
                handle_update(row, r, it, w)
                continue
            create_alert(r, it, w)
            sent += 1

    # Housekeeping
    db.execute("DELETE FROM seen WHERE ts < ?", (time.time() - 14 * 86400,))
    db.commit()
    heartbeat(len(collected), broken)
    weekly_digest()
    print(f"Done. New alerts sent: {sent}")


if __name__ == "__main__":
    try:
        run_once()
    except Exception:
        import traceback
        tb = traceback.format_exc()
        print(tb)
        with open("monitor_error.txt", "w", encoding="utf-8") as f:   # read by the workflow's failure step
            f.write(tb[-700:])
        raise
