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
  6. Websites       - official sites (ministries, Duma, Federation Council, Security Council, RDIF):
                      the site's own RSS feed if it advertises one, otherwise news links on the page

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
_ACT_SHORT = '(visit OR talks OR delegation OR forum)'
_ACT = ('(visit OR visiting OR talks OR delegation OR meeting OR "will meet" OR "intergovernmental commission" '
        'OR "joint commission" OR "intergovernmental committee" OR "co-chair")')

# GDELT: English keywords match articles in all 65+ languages it translates.
# Each query returns at most 250 articles, so the topic is split across several.
GDELT_QUERIES = [
    f'{_RU} (visit OR visiting OR "will visit" OR "official visit" OR "state visit" OR "working visit")',
    f'{_RU} (talks OR delegation OR "intergovernmental commission" OR "joint commission" OR "will meet")',
    '(Putin OR Mishustin OR Lavrov OR Siluanov OR Manturov OR Novak OR Overchuk) (visit OR talks OR forum OR summit)',
    '(Belousov OR Reshetnikov OR Shoigu OR Matviyenko OR Volodin OR Ushakov OR Dmitriev) (visit OR talks OR forum OR summit)',
    # Priority countries, in small groups (GDELT rejects very long queries)
    f'{_RU} {_ACT_SHORT} (China OR "Hong Kong" OR Taiwan OR Macao OR Vietnam OR Cambodia)',
    f'{_RU} {_ACT_SHORT} (Thailand OR Myanmar OR Japan OR "South Korea" OR "North Korea" OR Laos)',
    f'{_RU} {_ACT_SHORT} (Indonesia OR Singapore OR Malaysia OR Mongolia OR India)',
    f'{_RU} {_ACT_SHORT} (Brazil OR "South Africa" OR Nigeria OR Mexico OR Guyana OR Jamaica)',
    f'{_RU} {_ACT_SHORT} (Ghana OR Madagascar OR Guinea OR "Guinea-Bissau" OR Egypt OR Morocco OR Algeria)',
    f'{_RU} {_ACT_SHORT} (Turkey OR Azerbaijan OR Armenia OR Bahrain OR Qatar OR Kuwait)',
    f'{_RU} {_ACT_SHORT} (UAE OR Oman OR "Saudi Arabia" OR Hungary OR Slovakia OR Serbia)',
    f'{_RU} {_ACT_SHORT} (Belarus OR Kazakhstan OR Uzbekistan OR Turkmenistan OR Kyrgyzstan OR Tajikistan OR Moldova)',
]
# Search windows: from the last successful run (plus a safety margin), at least 1 hour, at most 2 days.
# Set at the start of each run, so a skipped or delayed GitHub run never leaves a gap.
WINDOW_HOURS = 2

_RU_ACT = ('(визит OR визитом OR посетит OR переговоры OR делегация OR межправкомиссия OR "межправительственная комиссия" '
           'OR "межправительственной комиссии" OR МПК OR сопредседатель OR встреча)')

# Google News: (language, country, edition, query)
GNEWS = [
    # Russian edition: general + targeted by country group
    ("ru", "RU", "RU:ru", '(визит OR посетит OR переговоры OR "прибудет" OR межправкомиссия OR делегация)'),
    ("ru", "RU", "RU:ru", '("межправительственная комиссия" OR "межправительственной комиссии" OR "межправительственного комитета" '
                          'OR "совместной комиссии" OR сопредседатель OR "двусторонние консультации")'),
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

# Direct RSS feeds. FEEDS: every item goes to the AI. MEDIA_FEEDS: big general-news feeds,
# only items that mention a visit/meeting/forum word or a Russian official go to the AI.
FEEDS = {
    "ТАСС": "https://tass.ru/rss/v2.xml",
    "TASS (EN)": "https://tass.com/rss/v2.xml",
    "РИА Новости": "https://ria.ru/export/rss2/archive/index.xml",
    "Интерфакс": "https://www.interfax.ru/rss",
    "Кремль": "http://kremlin.ru/events/all/feed",
    "Правительство РФ": "http://government.ru/all/rss/",
}
MEDIA_FEEDS = {
    "Коммерсантъ": "https://www.kommersant.ru/RSS/news.xml",
    "Ведомости": "https://www.vedomosti.ru/rss/news",
    "РБК": "https://rssexport.rbc.ru/rbcnews/news/30/full.rss",
    "Известия": "https://iz.ru/xml/rss/all.xml",
    "Российская газета": "https://rg.ru/xml/index.xml",
    "Парламентская газета": "https://www.pnp.ru/rss/index.xml",
    "ПРАЙМ": "https://1prime.ru/export/rss2/index.xml",
    "RT на русском": "https://russian.rt.com/rss",
    "RT (EN)": "https://www.rt.com/rss/news/",
    "Лента.ру": "https://lenta.ru/rss/news",
    "Газета.Ru": "https://www.gazeta.ru/export/rss/first.xml",
}

# Official websites without an RSS feed: the program reads the news list page and picks
# links that match "link" (a regular expression). Each new link = one news item.
# Without "link", the program first looks for an RSS feed advertised by the page and uses it;
# otherwise it takes links to news articles from the page.
# "filter": False -> every item goes to the AI; default (True) -> keyword prefilter first.
PAGE_SOURCES = [
    {"name": "Совет Безопасности РФ (сайт)", "url": "http://www.scrf.gov.ru/news/allnews/",
     "link": r"/news/allnews/\d+/?$", "filter": False},
    {"name": "РФПИ (сайт)", "url": "https://rdif.ru/", "link": r"fullNews/\d+", "filter": False},
    # Full list of the day's news (the RSS feed only holds the last ~25 items)
    {"name": "Интерфакс — все новости за день", "url": "https://www.interfax.ru/news/{Y}/{m}/{d}",
     "link": r"interfax\.ru/(russia|world|business|moscow|culture|digital)/\d+$", "filter": False},
    # Parliament
    {"name": "Государственная Дума (сайт)", "url": "https://duma.gov.ru/news/"},
    {"name": "Совет Федерации (сайт)", "url": "https://council.gov.ru/"},
    # Ministries
    {"name": "Минэкономразвития России (сайт)", "url": "https://economy.gov.ru/"},
    {"name": "Минпромторг России (сайт)", "url": "https://minpromtorg.gov.ru/"},
    {"name": "Минкультуры России (сайт)", "url": "https://culture.gov.ru/"},
    {"name": "Минобрнауки России (сайт)", "url": "https://minobrnauki.gov.ru/"},
    {"name": "Минприроды России (сайт)", "url": "https://www.mnr.gov.ru/"},
    {"name": "Минпросвещения России (сайт)", "url": "https://edu.gov.ru/"},
    {"name": "Минвостокразвития России (сайт)", "url": "https://minvr.gov.ru/"},
    {"name": "Минсельхоз России (сайт)", "url": "https://mcx.gov.ru/"},
    {"name": "Минстрой России (сайт)", "url": "https://minstroyrf.gov.ru/"},
    {"name": "Минтранс России (сайт)", "url": "https://mintrans.gov.ru/press-center/news"},
    {"name": "Минтруд России (сайт)", "url": "https://mintrud.gov.ru/"},
    {"name": "Минфин России (сайт)", "url": "https://minfin.gov.ru/"},
    {"name": "Минцифры России (сайт)", "url": "https://digital.gov.ru/"},
    {"name": "Минэнерго России (сайт)", "url": "https://minenergo.gov.ru/"},
]
# Generic rule for news-article links (used when a source has no "link" and no RSS feed)
NEWS_LINK_RE = r"/(news|novost|press|presscenter|press-center|events|media|activity)\S*\d"

# Public Telegram channels to read (usernames without @).
# CORE channels: every post goes to the AI. Channels from telegram_channels.csv (ministries,
# agencies, embassies, consulates, trade missions...): only posts containing visit/meeting
# words go to the AI, which saves the free AI quota. Edit the CSV to add or remove channels.
TG_CORE = ["MID_Russia", "MariaVladimirovnaZakharova", "tass_agency", "rian_ru", "interfaxonline"]
TG_MAX_PAGES = 10   # busy channels: read up to 10 x ~20 older posts to reach the last post already seen
TG_CHANNELS_FILE = os.environ.get("TG_CHANNELS_FILE") or "telegram_channels.csv"


def load_tg_channels():
    """Returns (ordered list of usernames, {username_lower: display name})."""
    import csv
    labels = {"mid_russia": "МИД России", "tass_agency": "ТАСС", "rian_ru": "РИА Новости",
              "mariavladimirovnazakharova": "Мария Захарова, официальный представитель МИД",
              "interfaxonline": "Интерфакс"}
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
               "short_ru": "TEXT", "source": "TEXT", "updates": "TEXT", "vote": "TEXT",
               "participants_ru": "TEXT", "participants_foreign": "TEXT"}
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
                  "timespan": f"{WINDOW_HOURS}h", "sort": "datedesc"}
        data = {}
        for attempt in range(3):
            try:
                r = requests.get("https://api.gdeltproject.org/api/v2/doc/doc",
                                 params=params, headers=UA, timeout=60)
                if r.text.strip().startswith("{"):
                    data = r.json()
                    break
                if "limit requests" in r.text and attempt < 2:
                    time.sleep(15 * (attempt + 1))   # GDELT is busy (GitHub shares IP addresses)
                    continue
                print(f"[gdelt] no results for query starting '{q[:60]}': {r.text[:120]}")
                break
            except Exception as e:
                print(f"[gdelt error] {e}")
                break
        for a in data.get("articles", []):
            items.append({
                "source": f"{a.get('domain', '')} ({a.get('sourcecountry', '')}, {a.get('language', '')})",
                "title": a.get("title", ""), "text": "", "url": a.get("url", ""),
                "uid": a.get("url", ""), "published": from_gdelt(a.get("seendate")),
            })
        time.sleep(8)  # GDELT asks for at most one request every 5 seconds
    HEALTH["GDELT"] = len(items)
    return items


def fetch_gnews():
    items = []
    for hl, gl, ceid, q in GNEWS:
        url = "https://news.google.com/rss/search?" + urllib.parse.urlencode(
            {"q": f"{q} when:{WINDOW_HOURS}h", "hl": hl, "gl": gl, "ceid": ceid})
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
    for name, url in list(FEEDS.items()) + list(MEDIA_FEEDS.items()):
        flt = name in MEDIA_FEEDS
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
                "keyword_filter": flt, "channel": "feed:" + name,
            })
    return items


def _domain(url):
    host = urllib.parse.urlparse(url).netloc.lower()
    return host[4:] if host.startswith("www.") else host


def fetch_pages():
    """Read official websites: an advertised RSS feed if there is one, otherwise the news links
    on the page itself."""
    from bs4 import BeautifulSoup

    def expand(src):
        """URLs with {Y}/{m}/{d} = today's date (Moscow); shortly after midnight also yesterday."""
        if "{Y}" not in src["url"]:
            return [src]
        now = dt.datetime.now(MSK)
        days = [now.date()] + ([now.date() - dt.timedelta(days=1)] if now.hour < 3 else [])
        return [dict(src, url=src["url"].format(Y=d.year, m=f"{d.month:02d}", d=f"{d.day:02d}")) for d in days]

    from concurrent.futures import ThreadPoolExecutor
    sources = [x for src in PAGE_SOURCES for x in expand(src)]
    with ThreadPoolExecutor(max_workers=6) as pool:
        results = list(pool.map(_read_page, sources))
    items, totals = [], {}
    for src, got in zip(sources, results):
        items += got
        totals[src["name"]] = totals.get(src["name"], 0) + len(got)
    for name, n in totals.items():
        HEALTH[name] = n
        print(f"[page] {name}: {n} items" if n else f"[page] {name}: nothing found (blocked or layout changed?)")
    return items


def _read_page(src):
    from bs4 import BeautifulSoup
    items = []
    if True:
        found, how = 0, "page"
        flt = src.get("filter", True)
        base = {"source": src["name"], "channel": "page:" + src["name"], "keyword_filter": flt}
        try:
            try:
                r = requests.get(src["url"], headers=UA, timeout=(10, 30))
            except requests.exceptions.SSLError:
                # many .gov.ru sites use Russian state certificates that foreign servers don't trust;
                # we only read public news pages, so retry without the certificate check
                import urllib3
                urllib3.disable_warnings()
                r = requests.get(src["url"], headers=UA, timeout=(10, 30), verify=False)
            soup = BeautifulSoup(r.content, "html.parser")

            # 1) RSS feed advertised by the page
            if not src.get("link"):
                for tag in soup.find_all("link", href=True):
                    if re.search(r"rss|atom", str(tag.get("type", "")), re.I):
                        feed = feedparser.parse(urllib.parse.urljoin(src["url"], tag["href"]), request_headers=UA)
                        for e_ in feed.entries:
                            items.append(dict(base, title=e_.get("title", ""),
                                              text=re.sub("<[^>]+>", " ", e_.get("summary", "")),
                                              url=e_.get("link", ""), uid=e_.get("link", "") or e_.get("title", ""),
                                              published=from_struct(e_.get("published_parsed") or e_.get("updated_parsed"))))
                            found += 1
                        if found:
                            how = "rss"
                            break

            # 2) News links on the page
            if not found:
                pattern = re.compile(src.get("link") or NEWS_LINK_RE, re.I)
                same_site = _domain(src["url"])
                seen_urls = set()
                for a in soup.find_all("a", href=True):
                    url = urllib.parse.urljoin(src["url"], a["href"])
                    title = a.get_text(" ", strip=True)
                    if (not pattern.search(url) or len(title) < 20 or url in seen_urls
                            or not _domain(url).endswith(same_site)):
                        continue
                    seen_urls.add(url)
                    found += 1
                    items.append(dict(base, title=title[:300], text="", url=url, uid=url, published=None))
        except Exception as ex:
            print(f"[page error] {src['name']}: {ex}")
    return items


def _read_channel(ch, last_seen):
    """Read one public channel's web preview. If the channel posted more than one page since
    the last run, keep reading older pages until the last post already seen."""
    from bs4 import BeautifulSoup
    items, before, ok = [], None, False
    for _ in range(TG_MAX_PAGES):
        url = f"https://t.me/s/{ch}" + (f"?before={before}" if before else "")
        try:
            r = requests.get(url, headers=UA, timeout=30)
            if r.status_code == 429:          # Telegram asks us to slow down
                time.sleep(15)
                r = requests.get(url, headers=UA, timeout=30)
        except Exception as ex:
            print(f"[telegram web error] {ch}: {ex}")
            break
        posts = BeautifulSoup(r.text, "html.parser").select("div.tgme_widget_message[data-post]")
        if not posts:
            break
        ok = True
        ids = []
        for post in posts:
            path = post["data-post"]            # e.g. "MID_Russia/12345"
            try:
                msg_id = int(path.split("/")[-1])
            except ValueError:
                continue
            ids.append(msg_id)
            body = post.select_one("div.tgme_widget_message_text")
            text = body.get_text(" ", strip=True) if body else ""
            if not text or msg_id <= last_seen:
                continue
            t = post.select_one("time[datetime]")
            items.append({
                "source": tg_label(ch), "title": text[:300], "text": text,
                "url": f"https://t.me/{path}", "uid": f"tg:{ch}:{msg_id}", "msg_id": msg_id,
                "published": from_iso(t["datetime"]) if t else None,
                "channel": ch.lower(), "keyword_filter": ch.lower() not in TG_CORE_LOWER,
            })
        if not ids or not last_seen or min(ids) <= last_seen + 1:
            break
        before = min(ids)
        time.sleep(0.3)
    return ch, items, ok


def fetch_telegram_web():
    """Read public channels from their web preview pages (no account needed), 6 at a time."""
    from concurrent.futures import ThreadPoolExecutor
    last = {ch: int(meta_get(f"tg_last:{ch.lower()}") or 0) for ch in TG_CHANNELS}
    with ThreadPoolExecutor(max_workers=6) as pool:
        results = list(pool.map(lambda ch: _read_channel(ch, last[ch]), TG_CHANNELS))
    items, failed = [], []
    for ch, got, ok in results:
        HEALTH[f"Telegram @{ch}"] = 1 if ok else 0
        if not ok:
            failed.append(ch)
        items += got
        if got:
            meta_set(f"tg_last:{ch.lower()}", str(max(i["msg_id"] for i in got)))
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
SCREEN_BATCH = int(os.environ.get("SCREEN_BATCH") or "150")  # items per AI call (headline + lead)
VERIFY_BATCH = int(os.environ.get("VERIFY_BATCH") or "8")    # articles per AI call
SAFETY_NET_MAX = int(os.environ.get("SAFETY_NET_MAX") or "40")  # extra items per run sent to verification
MAX_AGE_HOURS = int(os.environ.get("MAX_AGE_HOURS") or "24")    # ignore news published earlier than this
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
    r"визит|посет|переговор|встреч|делегаци|межправ|межгосударствен|межпарламент|сопредседател|"
    r"совместн\w*\s+(российск\w*\s+)?комисс|комисси\w*\s+по\s+(торгово|экономическ|сотрудничеств)|\bмпк\b|"
    r"прибуд|visit|talks|delegation|meet|summit|intergovernmental|joint commission|co-chair|"
    r"访|訪|会谈|會談|会见|會見|زيارة|مباحثات|وفد|visita|reuni|visite|entretien|besuch|gespräch|ziyaret|görüş|heyet|"
    r"यात्रा|दौरा|वार्ता|会談|방문|회담|kunjungan|pertemuan|เยือน|หารือ|látogat|tárgyal|návštev|rokovan|poset|razgovor",
    re.IGNORECASE)


# Prefilter for posts from official channels (ministries, embassies...): a post must contain
# a visit/meeting word (Russian or the languages these channels post in) to reach the AI.
TG_VISIT_RE = re.compile(
    VISIT_RE.pattern + r"|встрет|прибыл|прибыв|поездк|командиров|консультаци|двусторон|саммит|"
    r"форум|посол|рабоч\w* визит|соглашени|меморандум|российско-\w+|\w+-российск", re.IGNORECASE)


# Russian officials (names and titles) and "takes part / travels / meets" words. Used for:
#  - the SAFETY NET: an item with a Russian official + such a word goes to verification even if
#    the headline screening dropped it (e.g. "Лавров примет участие в Дохийском форуме");
#  - prefilters and the keyword fallback when the AI is unavailable.
OFFICIAL_RE = re.compile(
    r"путин|мишустин|лавров|силуанов|мантуров|новак|оверчук|белоусов|решетников|шойгу|матвиенко|володин|"
    r"набиуллина|ушаков|песков|захаров|алиханов|цивилев|патрушев|голиков|хуснуллин|чернышенко|григоренко|"
    r"савельев|трутнев|дмитриев|лихачев|лихачёв|рябков|руденко|галузин|грушко|вершинин|бородавкин|"
    r"кожемяко|козак|орешкин|слуцк|косачев|косачёв|"
    r"putin|mishustin|lavrov|siluanov|manturov|novak|overchuk|belousov|reshetnikov|shoigu|matviyenko|volodin|"
    r"nabiullina|ushakov|peskov|zakharova|alikhanov|tsivilev|patrushev|golikova|khusnullin|chernyshenko|"
    r"dmitriev|likhachev|ryabkov|rudenko|galuzin|"
    r"министр|замминистра|заместител\w* министра|вице-премьер|зампред\w* правительства|глав\w* (мид|минфина|"
    r"минэк|минпром|минэнерго|минсельхоз|минтранс|минобр|минкульт|минцифр|правительства|кабмина|"
    r"госдумы|совфеда|совета федерации|росатом|ростех|роскосмос|рфпи|банка россии|цб)|"
    r"секретар\w* (совета безопасности|совбеза)|спикер|председател\w* (госдумы|государственной думы|"
    r"совета федерации|правительства)|посол\w* (россии|рф)|спецпредставител|российск\w* делегаци|"
    r"делегаци\w* (россии|рф)|russian (foreign |deputy )?minister|russian delegation|kremlin",
    re.IGNORECASE)
EVENT_RE = re.compile(
    r"визит|посет|прибуд|прибыл|прибыв|переговор|встрет|встреч|примет участие|принять участие|"
    r"примут участие|выступ|форум|саммит|конференц|заседани|сесси|на полях|поездк|отправит|вылет|"
    r"находиться с|межправ|консультаци|делегаци|"
    r"visit|talks|summit|forum|will attend|to attend|will meet|trip|arrive|conference|session",
    re.IGNORECASE)


def _all_text(it, n=600):
    return f"{it['title']} {(it.get('text') or '')[:n]}"


def safety_net(it):
    s = _all_text(it)
    return bool(OFFICIAL_RE.search(s) and EVENT_RE.search(s))


def keyword_match(it):
    """Keyword fallback used when the AI is unavailable."""
    s = _all_text(it)
    return bool((RUSSIA_RE.search(s) or OFFICIAL_RE.search(s)) and (VISIT_RE.search(s) or EVENT_RE.search(s)))


def prefilter_ok(it):
    """For sources marked keyword_filter (official channels, big media feeds, ministry sites)."""
    s = it.get("text") or it["title"]
    return bool(TG_VISIT_RE.search(s) or EVENT_RE.search(s) and OFFICIAL_RE.search(s))


SCREEN_PROMPT = """You are a HIGH-RECALL filter for an analyst. You get numbered news items in any
language, each as "headline — lead of the text". Return the numbers of every item that MIGHT concern:
- a Russian official travelling abroad for ANY reason: visit, talks, consultations, a forum, summit,
  conference, session, ministerial meeting, international organization event (UN, BRICS, SCO, CIS,
  EAEU, CSTO, G20, APEC...), "примет участие", "выступит", "посетит", "будет находиться с визитом";
- a foreign official coming to Russia (including to forums or conferences in Russia) or meeting
  Russian officials anywhere, including "on the sidelines" (на полях) of multilateral events;
- delegations, intergovernmental commissions (межправкомиссия / межправительственная комиссия,
  co-chairs, working groups), bilateral consultations or dialogues involving Russia.
Include announcements, plans, and events under way. The headline may not name the country or use
the word "visit" (e.g. "Лавров примет участие в Дохийском форуме" = a trip to Qatar) - read the lead.
When in doubt, INCLUDE it. Missing a real event is far worse than a false positive.
Reply with ONLY JSON: {"keep": [numbers]}"""

VERIFY_PROMPT = """You verify news items for a Russian-speaking analyst who tracks VISITS AND MEETINGS
OF RUSSIAN STATE OFFICIALS WITH FOREIGN STATE OFFICIALS. You get TODAY's date and several numbered
ITEMS, each with its publication date and (usually) the full article text. Read the full text.

RELEVANT only if ALL of these are true:
1. RUSSIA IS ONE OF THE SIDES: a named Russian state official or an official Russian state delegation
   takes part (president, PM, deputy PMs, ministers and deputies, heads of federal agencies and
   services, Kremlin officials, presidential envoys, Security Council officials, Federal Assembly
   leaders and official delegations, Bank of Russia, heads of state corporations such as Rosatom
   acting officially, ambassadors). Talks between two OTHER countries (e.g. Azerbaijan-Armenia) are
   NOT relevant, even if the article mentions Russia.
2. THE OTHER SIDE is a foreign state official/delegation or an international organization.
3. It is a concrete visit, trip, meeting, talks, consultations, intergovernmental commission,
   forum/summit/conference participation, etc. A Russian official's trip to a forum abroad counts.
4. TIMING: the event is upcoming, under way now, or took place TODAY (publication day). If the text
   shows the event took place before today (e.g. "23 ноября прошло заседание" in an article published
   26 November), it is NOT relevant - even if the article is new.
NOT relevant: an article that only COMMENTS on or recalls a meeting that took place earlier (e.g. an
interview two weeks after talks: "Кушнер назвал Путина великим политиком" about a mid-November meeting);
statements, interviews, opinions and policy announcements that do not announce a specific visit or meeting (e.g. "Пашинян объявил о прекращении работы пограничников"); business or
company consultations without a stated visit/meeting of officials (e.g. "Малайзия обсуждает с
Росатомом меморандум"); culture, singers, artists, art groups, schoolchildren, students, youth groups,
sports, NGOs and charities (e.g. Red Cross); regional/governor-level contacts; battlefield news;
speculation; the CSTO (ОДКБ) and military-technical cooperation (arms trade, defence industry, military
equipment, Rosoboronexport, ФСВТС), plus any topic in the analyst's IGNORED TOPICS list.

PARTICIPANTS: list only people who TAKE PART in the event, with names and positions if the text
gives them. Someone who merely announced or commented on the event (e.g. a spokesman, or an envoy
who "said a delegation may come") is NOT a participant - put them in announced_by instead.
participants_ru: the Russian participants (name + position, as precisely as the text allows, e.g.
"Александр Венедиктов, заместитель секретаря Совета Безопасности РФ"). Must not be empty for a
relevant item - if no Russian participant is identifiable, the item is not relevant.
participants_foreign: the foreign participants (name + position, or the position only).

You also get RECENT ALERTS already sent (with date, participants and status). If an item is about the
SAME event as one of them, set duplicate_of to that alert id and set change_type:
  "date_confirmed"     - the alert had no exact date (or only a week/month) and this item gives the day;
  "date_changed"       - the alert had an exact date and this item clearly gives a DIFFERENT date;
  "postponed"          - the item says the event is postponed (with or without a new date);
  "cancelled"          - the item says the event is cancelled / will not take place;
  "participants_added" - the item NAMES participants who were not known in the alert (e.g. the alert
                         said "делегация Минфина", now we learn the deputy minister's name). Put ONLY the
                         newly named people in new_info;
  "none"               - anything else: details of the agenda, results or atmosphere of the talks,
                         ceremonies, site visits, quotes, or a repeat of the same facts. These are NOT
                         worth a message.
Do not invent contradictions: "the invitation stands" and "I don't know if he accepted" are compatible.
Items about postponement or cancellation of an event NOT in recent alerts are relevant too.
If several items in this batch describe the same event, return it ONCE (most informative item).

If ANALYST FEEDBACK is provided, follow it.

Items marked "ANALYST CHECK" were sent by the analyst for a manual check: ALWAYS return them, with
"relevant": true or false and "reason_ru" (one sentence in Russian explaining the decision).

LANGUAGE: everything you write IN RUSSIAN (standard Russian spelling of names and countries).
title_ru = the item's headline translated into natural Russian (if already Russian, copy it as is).
short_ru = a very short Russian label, max 8 words, e.g. "визит главы МИД Вьетнама в Москву".
countries = list of the OTHER countries / organizations, WITHOUT Russia, e.g. ["Китай"] or ["МАГАТЭ"].

DATES - the date of the EVENT, never the publication date. If the text does not say when the event
happens, use {"kind":"unknown"} and leave date_text empty. date_text must be words quoted from the
article, never a date you made up. Do NOT calculate calendar dates for weekdays or relative words;
describe what the text says with these DATEREF objects (the program computes the date):
  {"kind":"absolute","day":24,"month":11,"year":2026}   (year null if the text gives none)
  {"kind":"weekday","weekday":"tuesday","modifier":"none"}
       modifier: "this" (this week / в этот вторник), "next" (next week's / в следующий вторник),
                 "last" (last week's), or "none" (just "on Tuesday" / "во вторник")
  {"kind":"relative","days":1}   (today 0, tomorrow 1, day after tomorrow 2, yesterday -1)
  {"kind":"week","modifier":"this"|"next"}   ("this week", "next week")
  {"kind":"month","month":12,"year":null,"part":"early"|"mid"|"late"|"whole"}
  {"kind":"unknown"}
tense: "future" if the event is upcoming, "present" if happening now/today, "past" if it already
took place (fully or partly).
article_date: if the text shows when the ARTICLE was written (a dateline, "published on...", or a year
in the text that dates it, e.g. a 2019 article), give it as YYYY-MM-DD; otherwise leave it empty.
The "Published" date you are given can be wrong for re-published old articles - trust the text.
Weekday words ("Friday", "в пятницу") refer to the article's own week, which may be years ago.
If the text gives an explicit calendar date ("в минувший четверг, 26 ноября"), use THAT date as an
"absolute" DATEREF. "минувший/прошедший/прошлый" = last. Vague phrases ("в эти же дни", "на днях",
"недавно", "soon") are NOT dates: use {"kind":"unknown"}.
location: the place of the EVENT as stated in the text (e.g. "Москва, Россия"); empty if not stated.

Return ONLY relevant items (plus every ANALYST CHECK item), as ONLY JSON:
{"results": [
 {"n": item number,
  "relevant": true | false,
  "reason_ru": "",
  "confidence": "high" | "medium",
  "duplicate_of": alert id number or null,
  "change_type": "none" | "date_confirmed" | "date_changed" | "postponed" | "cancelled" | "participants_added",
  "new_info": "",
  "title_ru": "заголовок на русском",
  "short_ru": "короткая метка",
  "status": "announced" | "under_way",
  "tense": "future" | "present" | "past",
  "article_date": "",
  "participants_ru": "российские участники",
  "participants_foreign": "иностранные участники",
  "announced_by": "кто сообщил о событии, если это не участник",
  "countries": ["страна или организация"],
  "direction": "outbound" | "inbound" | "elsewhere",
  "location": "город, страна",
  "date_text": "",
  "date_start": DATEREF,
  "date_end": DATEREF or null,
  "summary": "одно-два предложения на русском"}
]}
direction: outbound = Russian officials travel abroad; inbound = foreign officials come to Russia;
elsewhere = meeting in a third country or online.
If none are relevant: {"results": []}"""


def _lead(it, n=220):
    text = re.sub(r"\s+", " ", it.get("text") or "").strip()
    if not text or text.startswith(it["title"][:60]):
        text = text[len(it["title"]):] if text.startswith(it["title"]) else ""
    return text[:n]


def screen(items):
    """Stage 1: batch headline + lead through the AI (keyword fallback if AI unavailable)."""
    keep = []
    for i in range(0, len(items), SCREEN_BATCH):
        batch = items[i:i + SCREEN_BATCH]
        lines = "\n".join(f"{n}. {it['title'][:200]}" + (f" — {_lead(it)}" if _lead(it) else "")
                          for n, it in enumerate(batch))
        res = ask_json(SCREEN_MODEL, SCREEN_PROMPT, lines, max_tokens=1000)
        if res is None:
            keep.extend(it for it in batch if keyword_match(it))
            continue
        for n in res.get("keep", []):
            if isinstance(n, int) and 0 <= n < len(batch):
                keep.append(batch[n])
    return keep


def resolve_google_link(item):
    """Google News items point to news.google.com; find the real article address so the AI can read
    the full text (dates, places, names) and the alert links to the original site."""
    if "news.google.com" not in item.get("url", "") or item.get("_resolved"):
        return
    item["_resolved"] = True
    try:
        from googlenewsdecoder import gnewsdecoder
        res = gnewsdecoder(item["url"], interval=1)
        if res.get("success") or res.get("status"):
            item["url"] = res["decoded_url"]
    except Exception as ex:
        print(f"[google link] could not decode: {ex}")


URL_DATE_RE = re.compile(r"(?<!\d)(20\d{2}|19\d{2})[/_-]?(0[1-9]|1[0-2])[/_-]?(0[1-9]|[12]\d|3[01])(?!\d)")
META_DATE_RE = re.compile(
    r'(?:article:published_time|datePublished|pubdate|publish[_-]?date|dc\.date|og:published_time)'
    r'["\']?\s*(?:content|:)\s*=?\s*["\']\s*(\d{4}-\d{2}-\d{2})', re.I)


def date_from_url(url):
    m = URL_DATE_RE.search(urllib.parse.urlparse(url or "").path)
    if m:
        try:
            return dt.date(int(m.group(1)), int(m.group(2)), int(m.group(3)))
        except ValueError:
            pass
    return None


def date_from_page(page):
    """The article's own publication date from the page (meta tags / structured data)."""
    if trafilatura:
        try:
            md = trafilatura.extract_metadata(page)
            if md and md.date:
                return dt.date.fromisoformat(str(md.date)[:10])
        except Exception:
            pass
    m = META_DATE_RE.search(page)
    if m:
        try:
            return dt.date.fromisoformat(m.group(1))
        except ValueError:
            pass
    return None


def article_text(item, limit=4000):
    """Full text for the AI. Also records the article's REAL publication date (item['article_date']):
    aggregators such as Google News sometimes show years-old articles with a fresh date."""
    resolve_google_link(item)
    text = item.get("text") or ""
    if not item.get("article_date"):
        item["article_date"] = date_from_url(item["url"])
    if (len(text) > 1500 and item.get("article_date")) or not trafilatura or "news.google.com" in item["url"] \
            or item["url"].startswith("https://t.me/"):
        return text[:limit]
    try:
        page = requests.get(item["url"], headers=UA, timeout=20).text
        item["article_date"] = item.get("article_date") or date_from_page(page)
        extracted = trafilatura.extract(page) or ""
        return (extracted if len(extracted) > len(text) else text)[:limit]
    except Exception:
        return text[:limit]


def is_old_article(item):
    """True if the article itself was written more than MAX_AGE_HOURS (rounded up to days) ago."""
    d = item.get("article_date")
    if not d:
        return False
    max_days = max(1, -(-MAX_AGE_HOURS // 24))
    return (dt.datetime.now(MSK).date() - d).days > max_days


def recent_alerts_block():
    cutoff = time.time() - 21 * 86400
    rows = db.execute("SELECT id, summary, event_date, date_label, status, participants_ru, participants_foreign FROM alerts "
                      "WHERE ts > ? AND COALESCE(status,'active') != 'unverified' ORDER BY id DESC LIMIT 150",
                      (cutoff,)).fetchall()
    return "\n".join(f"[{r['id']}] {r['summary']} | known date: {r['date_label'] or r['event_date']} "
                     f"| participants: {r['participants_ru'] or '?'} / {r['participants_foreign'] or '?'} "
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
    """Publication date of the item in Moscow time: the article's own date if known, otherwise the
    date the source reported; falls back to 'now'."""
    if item.get("article_date"):
        return item["article_date"]
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
            if (val.year, val.month) == (b.year, b.month):
                span = f"{val.day}–{b.day} {MON_GEN[b.month - 1]} {b.year}"
            else:
                span = (f"{val.day} {MON_GEN[val.month - 1]}" + (f" {val.year}" if val.year != b.year else "")
                        + f" – {b.day} {MON_GEN[b.month - 1]} {b.year}")
            out.update(end=b.isoformat(), label=f"{span} ({WD_SHORT[val.weekday()]}–{WD_SHORT[b.weekday()]})")
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

# 👍/👎 buttons are switched off: the bot is not online between runs, so Telegram showed an endless
# "loading" after a click. Buttons already sent are removed automatically at the next run.
FEEDBACK_ON = False


def e(s):
    return html.escape(str(s or ""), quote=False)


FLAGS = {
    "китай": "🇨🇳", "кнр": "🇨🇳", "гонконг": "🇭🇰", "тайвань": "🇹🇼", "макао": "🇲🇴", "вьетнам": "🇻🇳",
    "камбоджа": "🇰🇭", "таиланд": "🇹🇭", "мьянма": "🇲🇲", "япония": "🇯🇵", "республика корея": "🇰🇷",
    "южная корея": "🇰🇷", "корея": "🇰🇷", "кндр": "🇰🇵", "северная корея": "🇰🇵", "армения": "🇦🇲",
    "индонезия": "🇮🇩", "сингапур": "🇸🇬", "лаос": "🇱🇦", "малайзия": "🇲🇾", "монголия": "🇲🇳",
    "бразилия": "🇧🇷", "юар": "🇿🇦", "южно-африканская": "🇿🇦", "нигерия": "🇳🇬", "мексика": "🇲🇽",
    "турция": "🇹🇷", "азербайджан": "🇦🇿", "бахрейн": "🇧🇭", "катар": "🇶🇦", "кувейт": "🇰🇼", "оаэ": "🇦🇪",
    "объединённые арабские": "🇦🇪", "объединенные арабские": "🇦🇪", "оман": "🇴🇲", "саудовская": "🇸🇦",
    "египет": "🇪🇬", "марокко": "🇲🇦", "алжир": "🇩🇿", "гайана": "🇬🇾", "ямайка": "🇯🇲", "венгрия": "🇭🇺",
    "словакия": "🇸🇰", "сербия": "🇷🇸", "белоруссия": "🇧🇾", "беларусь": "🇧🇾", "казахстан": "🇰🇿",
    "узбекистан": "🇺🇿", "туркменистан": "🇹🇲", "туркмения": "🇹🇲", "киргизия": "🇰🇬", "кыргызстан": "🇰🇬",
    "таджикистан": "🇹🇯", "молдавия": "🇲🇩", "молдова": "🇲🇩", "гана": "🇬🇭", "мадагаскар": "🇲🇬",
    "гвинея-бисау": "🇬🇼", "гвинея": "🇬🇳", "индия": "🇮🇳", "пакистан": "🇵🇰", "афганистан": "🇦🇫",
    "иран": "🇮🇷", "ирак": "🇮🇶", "сирия": "🇸🇾", "израиль": "🇮🇱", "палестина": "🇵🇸", "иордания": "🇯🇴",
    "ливан": "🇱🇧", "ливия": "🇱🇾", "тунис": "🇹🇳", "судан": "🇸🇩", "эфиопия": "🇪🇹", "кения": "🇰🇪",
    "танзания": "🇹🇿", "уганда": "🇺🇬", "мали": "🇲🇱", "буркина-фасо": "🇧🇫", "нигер": "🇳🇪", "чад": "🇹🇩",
    "цар": "🇨🇫", "центральноафриканская": "🇨🇫", "конго": "🇨🇬", "ангола": "🇦🇴", "мозамбик": "🇲🇿",
    "зимбабве": "🇿🇼", "сенегал": "🇸🇳", "эритрея": "🇪🇷", "сахарская": "🇪🇭", "садр": "🇪🇭",
    "грузия": "🇬🇪", "абхазия": "🏳️", "южная осетия": "🏳️", "украина": "🇺🇦", "сша": "🇺🇸",
    "соединённые штаты": "🇺🇸", "соединенные штаты": "🇺🇸", "канада": "🇨🇦", "великобритания": "🇬🇧",
    "франция": "🇫🇷", "германия": "🇩🇪", "италия": "🇮🇹", "испания": "🇪🇸", "австрия": "🇦🇹",
    "швейцария": "🇨🇭", "ватикан": "🇻🇦", "греция": "🇬🇷", "кипр": "🇨🇾", "болгария": "🇧🇬",
    "румыния": "🇷🇴", "польша": "🇵🇱", "финляндия": "🇫🇮", "норвегия": "🇳🇴", "швеция": "🇸🇪",
    "босния": "🇧🇦", "республика сербская": "🇧🇦", "черногория": "🇲🇪", "северная македония": "🇲🇰",
    "куба": "🇨🇺", "венесуэла": "🇻🇪", "никарагуа": "🇳🇮", "боливия": "🇧🇴", "аргентина": "🇦🇷",
    "чили": "🇨🇱", "колумбия": "🇨🇴", "перу": "🇵🇪", "эквадор": "🇪🇨", "уругвай": "🇺🇾", "парагвай": "🇵🇾",
    "бангладеш": "🇧🇩", "шри-ланка": "🇱🇰", "непал": "🇳🇵", "филиппины": "🇵🇭", "австралия": "🇦🇺",
    "новая зеландия": "🇳🇿", "бруней": "🇧🇳", "восточный тимор": "🇹🇱", "мальдивы": "🇲🇻",
}
ORG_WORDS = ("оон", "магатэ", "еаэс", "шос", "брикс", "снг", "одкб", "асеан", "атэс", "g20", "g7", "оопек",
             "опек", "ес", "евросоюз", "нато", "африканский союз", "лига арабских", "оис", "юнеско", "вто",
             "мвф", "всемирный банк", "мккк", "форум", "организация")


def country_list(value):
    """AI 'countries' (list or string) -> list of names without Russia."""
    items = value if isinstance(value, list) else re.split(r"[,;/]| и ", str(value or ""))
    out = []
    for c in items:
        c = re.sub(r"\s+", " ", str(c)).strip(" .")
        if not c or re.fullmatch(r"(россия|рф|российская федерация)", c, re.I):
            continue
        if c not in out:
            out.append(c)
    return out


def flag(name):
    low = name.lower()
    for key in sorted(FLAGS, key=len, reverse=True):
        if low.startswith(key) or f" {key}" in f" {low}":
            return FLAGS[key]
    return "🌐" if any(w in low for w in ORG_WORDS) else "🏳️"


def countries_line(value):
    """'🇷🇺 Россия ⇄ 🇨🇳 Китай'"""
    others = country_list(value)
    if not others:
        return "🇷🇺 Россия"
    return "🇷🇺 Россия ⇄ " + ", ".join(f"{flag(c)} {e(c)}" for c in others)


IGNORED_FILE = os.environ.get("IGNORED_COUNTRIES_FILE") or "ignored_countries.csv"


def load_ignored():
    """Countries the analyst doesn't care about (one per line in ignored_countries.csv)."""
    try:
        with open(IGNORED_FILE, encoding="utf-8-sig") as f:
            names = [line.split(";")[0].strip().lower() for line in f if line.strip()]
        return {n for n in names if n and n not in ("страна", "country")}
    except FileNotFoundError:
        return set()


IGNORED_COUNTRIES = load_ignored()

IGNORED_TOPICS_FILE = os.environ.get("IGNORED_TOPICS_FILE") or "ignored_topics.csv"
IGNORED_TOPIC_TERMS = []


def load_ignored_topics():
    """Topics/keywords the analyst doesn't want (one per line in ignored_topics.csv).
    A word matches anywhere it STARTS a word: 'военно-техническ' also matches 'военно-техническому'."""
    try:
        with open(IGNORED_TOPICS_FILE, encoding="utf-8-sig") as f:
            terms = [line.split(";")[0].strip() for line in f if line.strip()]
    except FileNotFoundError:
        terms = []
    terms = [t for t in terms if t and t.lower() not in ("тема или ключевое слово", "topic")]
    IGNORED_TOPIC_TERMS[:] = terms
    if not terms:
        return None
    return re.compile("|".join(r"(?<![\w-])" + re.escape(t) for t in terms), re.IGNORECASE)


IGNORED_TOPICS_RE = load_ignored_topics()


def ignored_topic(*texts):
    if not IGNORED_TOPICS_RE:
        return ""
    m = IGNORED_TOPICS_RE.search(" ".join(str(t or "") for t in texts))
    return m.group(0) if m else ""


def is_ignored(value):
    others = [c.lower() for c in country_list(value)]
    return bool(others) and all(any(c.startswith(i) for i in IGNORED_COUNTRIES) for c in others)


def link(url, text):
    return f'<a href="{html.escape(url or "", quote=True)}">{e(text)}</a>'


LAST_TG_ERROR = {}
DELIVERY = {"ok": 0, "failed": 0, "last_error": ""}


def chat_id():
    """The chat to send to. When Telegram turns a group into a 'supergroup', the group gets a NEW id;
    the bot then switches to it automatically (and asks you to update the TELEGRAM_CHAT_ID secret)."""
    env = str(os.environ["TELEGRAM_CHAT_ID"]).strip()
    mig = json.loads(meta_get("chat_migration") or "{}")
    return mig.get("to") if mig.get("from") == env else env


def tg(method, payload=None, files=None):
    """Call the Telegram Bot API; returns the 'result' or None."""
    global LAST_TG_ERROR
    LAST_TG_ERROR = {}
    token = os.environ["TELEGRAM_BOT_TOKEN"]
    try:
        if files:
            r = requests.post(f"https://api.telegram.org/bot{token}/{method}", data=payload, files=files, timeout=60)
        else:
            r = requests.post(f"https://api.telegram.org/bot{token}/{method}", json=payload or {}, timeout=30)
        body = r.json()
        if not body.get("ok"):
            LAST_TG_ERROR = body
            print(f"[telegram {method} error] {r.status_code} {body.get('description')}")
            return None
        return body.get("result")
    except Exception as ex:
        print(f"[telegram {method} error] {ex}")
        return None


def send(text_html, reply_to=None, markup=None):
    """Send an HTML message; returns its message_id (or None)."""
    payload = {"chat_id": chat_id(), "text": text_html[:4096],
               "parse_mode": "HTML", "disable_web_page_preview": True}
    if reply_to:
        payload["reply_parameters"] = {"message_id": int(reply_to), "allow_sending_without_reply": True}
    if markup:
        payload["reply_markup"] = markup
    res = tg("sendMessage", payload)
    new_id = ((LAST_TG_ERROR.get("parameters") or {}).get("migrate_to_chat_id")) if not res else None
    if new_id:
        # The group became a supergroup: remember the new id and resend
        old = str(os.environ["TELEGRAM_CHAT_ID"]).strip()
        meta_set("chat_migration", json.dumps({"from": old, "to": str(new_id)}))
        print(f"[telegram] group moved to new id {new_id}; switching automatically")
        payload["chat_id"] = str(new_id)
        payload.pop("reply_parameters", None)
        res = tg("sendMessage", payload)
        if res and not meta_get("chat_migration_notice"):
            tg("sendMessage", {"chat_id": str(new_id), "parse_mode": "HTML", "text":
                "ℹ️ <b>Telegram сменил ID этой группы</b> (группа стала «супергруппой»). Бот переключился "
                f"на новый ID автоматически.\nПожалуйста, обновите секрет <code>TELEGRAM_CHAT_ID</code> на GitHub: "
                f"<code>{new_id}</code>"})
            meta_set("chat_migration_notice", "1")
    if res:
        DELIVERY["ok"] += 1
        return res.get("message_id")
    DELIVERY["failed"] += 1
    DELIVERY["last_error"] = LAST_TG_ERROR.get("description", "network error")
    return None


def register_commands():
    """Show /check in Telegram's command menu (once)."""
    if meta_get("commands_v1"):
        return
    ok = tg("setMyCommands", {"commands": [
        {"command": "check", "description": "Проверить ссылку: /check https://..."}]})
    if ok:
        meta_set("commands_v1", "1")


def alert_message_from_row(row):
    """Rebuild an alert from the database (for alerts that were not delivered)."""
    lines = [f"🛬 <b>Анонс визита</b>" + (f": {countries_line(row['countries'])}" if row["countries"] else ""), "",
             e(row["summary"]), ""]
    if row["participants_ru"] or row["participants_foreign"]:
        lines += participant_lines(row["participants_ru"], row["participants_foreign"], row["countries"])
    elif row["officials"]:
        lines.append(f"👤 <b>Кто:</b> {e(row['officials'])}")
    if row["direction"]:
        lines.append(f"🧭 <b>Направление:</b> {e(DIRECTION_RU.get(row['direction'], row['direction']))}")
    if row["location"]:
        lines.append(f"📍 <b>Где:</b> {e(row['location'])}")
    when = row["date_label"] or row["event_date"] or "не указано"
    if row["date_text"]:
        when += f" (в тексте: «{row['date_text']}»)"
    lines += [f"📅 <b>Когда:</b> {e(when)}", "",
              f"🔗 {link(row['url'], (row['title_ru'] or row['summary'] or row['url'])[:200])}"
              + (f" — {e(row['source'])}" if row["source"] else "")]
    return "\n".join(lines)


def redeliver_undelivered():
    """Alerts saved but never delivered (e.g. while the chat ID was wrong): send them now.
    Only events that are not over yet; each alert is retried at most 3 times."""
    today = dt.datetime.now(MSK).date().isoformat()
    rows = db.execute(
        "SELECT * FROM alerts WHERE msg_id IS NULL AND COALESCE(status,'active') IN ('active','postponed') "
        "AND ts > ? AND (date_end IS NULL OR date_end >= ?) ORDER BY id LIMIT 60",
        (time.time() - 10 * 86400, today)).fetchall()
    tries = json.loads(meta_get("redeliver_tries") or "{}")
    rows = [r for r in rows if tries.get(str(r["id"]), 0) < 3]
    if not rows:
        return
    first = send(f"📬 <b>Оповещения, которые не удалось доставить раньше</b> ({len(rows)}).\n"
                 f"Причина: Telegram сменил ID группы, и сообщения не доходили. Ниже — все ещё актуальные события.")
    if not first:
        return
    for r in rows:
        mid = send(alert_message_from_row(r), markup=fb_markup(r["id"]) if FEEDBACK_ON else None)
        tries[str(r["id"])] = tries.get(str(r["id"]), 0) + 1
        if mid:
            db.execute("UPDATE alerts SET msg_id=? WHERE id=?", (mid, r["id"]))
        time.sleep(0.5)
    db.commit()
    meta_set("redeliver_tries", json.dumps(tries))


def fb_markup(alert_id, vote=None):
    return {"inline_keyboard": [[
        {"text": "👍 Полезно" + (" ✓" if vote == "up" else ""), "callback_data": f"fb:up:{alert_id}"},
        {"text": "👎 Не то" + (" ✓" if vote == "down" else ""), "callback_data": f"fb:down:{alert_id}"},
    ]]}


def participant_lines(p_ru, p_foreign, countries):
    lines = []
    if p_ru:
        lines.append(f"👤 <b>🇷🇺 Россия:</b> {e(p_ru)}")
    if p_foreign:
        others = country_list(countries)
        label = f"{flag(others[0])} {e(others[0])}" if len(others) == 1 else "Другая сторона"
        lines.append(f"👤 <b>{label}:</b> {e(p_foreign)}")
    return lines


def alert_message(r, it, w):
    if r.get("tense") == "past":
        status = "✅ <b>Состоялось сегодня</b>"
    elif r.get("status") == "under_way" or r.get("tense") == "present":
        status = "🟢 <b>Проходит сейчас</b>"
    else:
        status = "🛬 <b>Анонс визита</b>"
    when = when_with_text(w)
    if w["precision"] == "none" and status != "🛬 <b>Анонс визита</b>":
        when = f"{fmt_day(pub_date_msk(it))} (дата публикации)"
    lines = []
    if r.get("confidence") == "medium":
        lines.append("⚠️ <i>Не подтверждено — требует проверки</i>")
    lines += [f"{status}: {countries_line(r.get('countries'))}", "", e(r.get("summary")), ""]
    lines += participant_lines(r.get("participants_ru"), r.get("participants_foreign"), r.get("countries"))
    lines += [
        f"🧭 <b>Направление:</b> {e(DIRECTION_RU.get(r.get('direction'), r.get('direction')))}",
        f"📍 <b>Где:</b> {e(r.get('location') or 'не указано')}",
        f"📅 <b>Когда:</b> {e(when)}",
    ]
    if r.get("announced_by"):
        lines.append(f"🗣 <b>Сообщил:</b> {e(r['announced_by'])}")
    lines += ["", f"🔗 {link(it['url'], (r.get('title_ru') or it['title'])[:200])} — {e(it['source'])}"]
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
        (time.time(), r.get("summary", ""), w["start"] or w["label"], it["url"], ", ".join(country_list(r.get("countries"))),
         "; ".join(x for x in (r.get("participants_ru"), r.get("participants_foreign")) if x),
         r.get("direction", ""), r.get("location", ""), w["start"], w["end"],
         w["precision"], w["label"], w["text"], "active", r.get("title_ru") or it["title"],
         r.get("short_ru") or "", it["source"], ""))
    aid = cur.lastrowid
    db.execute("UPDATE alerts SET participants_ru=?, participants_foreign=? WHERE id=?",
               (r.get("participants_ru", ""), r.get("participants_foreign", ""), aid))
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
    # A new date is only trusted if the article states it in words (date_text). Follow-up reports often
    # carry their own publication day or "yesterday/today", which must not overwrite the event date.
    stated = bool(w.get("text"))
    explicit = (r.get("date_start") or {}).get("kind") == "absolute"
    new_day = w["precision"] == "day" and stated
    date_differs = (w["start"], w["end"]) != (row["date_start"], row["date_end"])

    if ct == "cancelled":
        kind = "cancelled"
    elif ct == "postponed":
        kind = "postponed"
    elif ct == "date_confirmed" and new_day and old_prec != "day":
        kind = "confirmed"
    elif ct == "date_changed" and new_day and explicit and old_prec == "day" and date_differs:
        kind = "changed"
    elif ct == "participants_added" and r.get("new_info"):
        kind = "participants"
    else:
        return
    if kind == "cancelled" and row["status"] == "cancelled":
        return  # already reported

    new_label = f"<b>{e(w['label'])}</b>" + (f" (в тексте: «{e(w['text'])}»)" if w.get("text") else "")
    old_l = e(old_label)
    headers = {"confirmed": "📅 <b>Дата подтверждена</b>", "changed": "🔁 <b>Дата изменена</b>",
               "postponed": "⏸ <b>Визит отложен</b>", "cancelled": "❌ <b>Визит отменён</b>",
               "participants": "👥 <b>Уточнён состав участников</b>"}
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
        body = "Этот визит был анонсирован ранее. Стали известны новые участники."

    lines = [f"{headers[kind]}: {countries_line(row['countries'] or r.get('countries'))}", "", body]
    if r.get("new_info") and kind != "participants":
        lines += ["", f"ℹ️ {e(r['new_info'])}"]
    elif kind == "participants":
        lines += ["", f"👤 {e(r['new_info'])}"]
    lines += ["",
              f"<blockquote><b>Исходное оповещение:</b>\n{e(row['summary'])}\nКогда: {old_l}</blockquote>",
              f"🔗 {link(it['url'], (r.get('title_ru') or it['title'])[:200])} — {e(it['source'])}"]
    send("\n".join(lines), reply_to=row["msg_id"])

    # Update the stored event
    status = {"cancelled": "cancelled", "postponed": "active" if new_day else "postponed"}.get(kind, "active")
    # The stored event date changes ONLY when the message is about the date itself
    if kind in ("confirmed", "changed") or (kind == "postponed" and new_day):
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
    if kind == "participants":
        db.execute("UPDATE alerts SET participants_ru = TRIM(COALESCE(participants_ru,'') || '; ' || ?, '; ') "
                   "WHERE id=?", (r["new_info"], row["id"]))
    db.commit()


# =============================================================================
# FEEDBACK BUTTONS
# =============================================================================
def process_feedback():
    """Read 👍/👎 clicks since the last run and store them."""
    offset = int(meta_get("tg_offset") or 0)
    updates = tg("getUpdates", {"offset": offset, "timeout": 0}) or []
    checks = json.loads(meta_get("manual_checks") or "[]")
    my_chats = {str(os.environ["TELEGRAM_CHAT_ID"]).strip(), chat_id()}
    for u in updates:
        offset = max(offset, u["update_id"] + 1)
        msg = u.get("message") or u.get("channel_post")
        mig = (msg or {}).get("migrate_to_chat_id")
        if mig and str(msg["chat"]["id"]) in my_chats:
            meta_set("chat_migration", json.dumps({"from": str(os.environ["TELEGRAM_CHAT_ID"]).strip(), "to": str(mig)}))
            print(f"[telegram] group moved to new id {mig}")
            my_chats.add(str(mig))
            continue
        if msg and str(msg.get("chat", {}).get("id")) in my_chats:
            text = msg.get("text") or msg.get("caption") or ""
            if re.match(r"^/(check|проверь)\b", text.strip(), re.I) or msg["chat"].get("type") == "private":
                for url in re.findall(r"https?://\S+", text)[:5]:
                    checks.append({"url": url.rstrip(").,»\"'"), "reply_to": msg.get("message_id")})
            continue
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
    meta_set("manual_checks", json.dumps(checks[-20:], ensure_ascii=False))
    meta_set("tg_offset", str(offset))


def manual_items():
    """Links sent to the bot with /check: turned into items that always go to verification."""
    checks = json.loads(meta_get("manual_checks") or "[]")
    items = []
    for c in checks:
        title, text = c["url"], ""
        try:
            page = requests.get(c["url"], headers=UA, timeout=25).text
            m = re.search(r"<title[^>]*>(.*?)</title>", page, re.S | re.I)
            if m:
                title = html.unescape(re.sub(r"\s+", " ", m.group(1))).strip()[:300]
            if trafilatura:
                text = (trafilatura.extract(page) or "")[:2500]
        except Exception as ex:
            print(f"[check] could not open {c['url']}: {ex}")
        items.append({"source": "проверка по запросу", "title": title, "text": text or title,
                      "url": c["url"], "uid": c["url"], "published": None,
                      "manual": True, "reply_to": c.get("reply_to")})
    meta_set("manual_checks", "[]")
    return items


def remove_buttons_if_disabled():
    """When FEEDBACK_BUTTONS=off: remove the buttons from all earlier alerts, once."""
    if FEEDBACK_ON:
        if meta_get("buttons_removed"):
            meta_set("buttons_removed", "")
        return
    if meta_get("buttons_removed"):
        return
    chat = chat_id()
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
    others = country_list(row["countries"])
    who = ", ".join(f"{flag(c)} {e(c)}" for c in others) or "🇷🇺"
    return f"• {who} — {link(row['url'], label)}"


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
        tg("sendDocument", {"chat_id": chat_id(),
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
VAGUE_DATE_RE = re.compile(
    r"в эти (же )?дни|на днях|недавно|в последнее время|в ближайшее время|скоро|вскоре|"
    r"these days|recently|lately|soon|in the coming days", re.IGNORECASE)
TODAY_WORD_RE = re.compile(r"сегодня|today|ныне|сейчас|в настоящее время|now", re.IGNORECASE)
MONTHS_RU_RE = "|".join(MON_GEN)
MONTHS_EN = ["january", "february", "march", "april", "may", "june", "july", "august", "september",
             "october", "november", "december"]
EXPLICIT_DATE_RE = re.compile(
    rf"(?<!\d)([0-3]?\d)(?:-?(?:го|е))?\s+({MONTHS_RU_RE})|"
    rf"({'|'.join(MONTHS_EN)})\s+([0-3]?\d)(?!\d)|(?<!\d)([0-3]?\d)\s+({'|'.join(MONTHS_EN)})", re.IGNORECASE)


def explicit_dates(text, ref):
    """Calendar dates written in the text ('26 ноября', 'November 26'), placed in the year closest to ref."""
    out = set()
    for m in EXPLICIT_DATE_RE.finditer(text or ""):
        try:
            if m.group(2):
                d, mon = int(m.group(1)), MON_GEN.index(m.group(2).lower()) + 1
            elif m.group(3):
                d, mon = int(m.group(4)), MONTHS_EN.index(m.group(3).lower()) + 1
            else:
                d, mon = int(m.group(5)), MONTHS_EN.index(m.group(6).lower()) + 1
            cands = [dt.date(y, mon, d) for y in (ref.year - 1, ref.year, ref.year + 1)]
            out.add(min(cands, key=lambda c: abs((c - ref).days)))
        except (ValueError, IndexError):
            pass
    return out


def clean_vague_date(r):
    """'в эти же дни', 'на днях', 'soon' are not dates: treat the date as unknown."""
    if VAGUE_DATE_RE.search(r.get("date_text") or "") and not EXPLICIT_DATE_RE.search(r.get("date_text") or ""):
        r["date_text"], r["date_start"], r["date_end"] = "", {"kind": "unknown"}, None


def reject_reason(r, it, w):
    """Deterministic checks on the AI's answer, based on the analyst's rules."""
    topic = ignored_topic(it["title"], r.get("title_ru"), r.get("summary"), r.get("short_ru"),
                          " ".join(country_list(r.get("countries"))), r.get("participants_foreign"))
    if topic:
        return f"ignored topic: {topic}"
    if not (r.get("participants_ru") or "").strip():
        return "no Russian participant"
    if is_ignored(r.get("countries")):
        return "ignored country"
    today = dt.datetime.now(MSK).date()
    ad = r.get("article_date") or ""
    if re.fullmatch(r"\d{4}-\d{2}-\d{2}", ad.strip()):
        try:
            if (today - dt.date.fromisoformat(ad.strip())).days > 1:
                return f"old article ({ad})"
        except ValueError:
            pass
    if w["end"] and dt.date.fromisoformat(w["end"]) < today:
        return "event already over"            # also 'mid-November', 'last week' etc.
    if r.get("tense") == "past":
        # something that already happened is only news if it happened TODAY
        if not (w["precision"] == "day" and w["end"] and dt.date.fromisoformat(w["end"]) >= today):
            return "past event, not today"
    if r.get("tense") in ("past", "present") and pub_date_msk(it) < today - dt.timedelta(days=1):
        return "report is not from today"
    if r.get("tense") in ("past", "present") and not TODAY_WORD_RE.search(r.get("date_text") or ""):
        # The text names calendar dates, none of them today, and the latest is in the past:
        # e.g. "состоялась в минувший четверг, 26 ноября" in an article published on the 27th.
        dates = explicit_dates(it.get("_fulltext") or it.get("text") or "", today)
        if dates and today not in dates and max(dates) < today:
            return f"text dates the event to {max(dates).isoformat()}"
    return ""


def run_once():
    global WINDOW_HOURS
    first_run = meta_get("initialized") is None
    run_started = time.time()
    last_ok = float(meta_get("last_run_ts") or 0)
    gap_h = (run_started - last_ok) / 3600 if last_ok else 1
    WINDOW_HOURS = int(min(48, max(1, gap_h + 0.5) + 0.999))
    print(f"Search window for Google News / GDELT: {WINDOW_HOURS} h "
          f"(last successful run {gap_h:.1f} h ago)" if last_ok else f"Search window: {WINDOW_HOURS} h")

    try:
        process_feedback()
        register_commands()
        remove_buttons_if_disabled()
    except Exception as ex:
        print(f"[feedback error] {ex}")
    if not first_run:
        redeliver_undelivered()

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
    new_items, now, prefiltered, too_old = [], time.time(), 0, 0
    for it in collected:
        keys = [h("u:" + it["uid"]), h("t:" + norm_title(it["title"]))]
        if any(db.execute("SELECT 1 FROM seen WHERE h=?", (k,)).fetchone() for k in keys):
            continue
        for k in keys:
            db.execute("INSERT OR IGNORE INTO seen (h, ts) VALUES (?, ?)", (k, now))
        if not it["title"].strip() or it.get("channel") in fresh_channels:
            continue
        pub = it.get("published")
        if isinstance(pub, dt.datetime) and (dt.datetime.now(UTC) - pub.astimezone(UTC)).total_seconds() > MAX_AGE_HOURS * 3600:
            too_old += 1
            continue
        if it.get("keyword_filter") and not prefilter_ok(it):
            prefiltered += 1
            continue
        if ignored_topic(it["title"]):
            prefiltered += 1
            continue
        new_items.append(it)
    db.commit()
    meta_set("tg_known_channels", json.dumps(sorted(known | fresh_channels)))
    print(f"New items: {len(new_items)} (skipped by keyword prefilter: {prefiltered}; "
          f"published more than {MAX_AGE_HOURS} h ago: {too_old})")

    if first_run:
        print("First run: recorded existing items, no alerts sent.")
        send("✅ <b>Мониторинг визитов запущен.</b> Оповещения начнутся со следующего запуска.")
        meta_set("initialized", "1")
        meta_set("heartbeat", dt.datetime.now(UTC).date().isoformat())
        meta_set("last_run_ts", str(run_started))
        return

    shortlist = screen(new_items)
    print(f"Shortlisted by AI screening: {len(shortlist)}")

    # SAFETY NET: Russian official + travel/meeting/forum word -> verify even if screening dropped it
    chosen = {id(it) for it in shortlist}
    net = [it for it in new_items if id(it) not in chosen and safety_net(it)]
    net.sort(key=lambda it: bool(it.get("keyword_filter")))      # main agencies first
    if len(net) > SAFETY_NET_MAX:
        print(f"[safety net] {len(net)} candidates, verifying the first {SAFETY_NET_MAX}")
    for it in net[:SAFETY_NET_MAX]:
        print(f"[safety net] added: {it['title'][:120]} ({it['source']})")
    shortlist += net[:SAFETY_NET_MAX]

    # Links sent with /check in the chat
    manual = manual_items()
    if manual:
        print(f"[check] manual checks requested: {len(manual)}")
    shortlist = manual + shortlist
    for it in shortlist:
        print(f"[verify] {'CHECK ' if it.get('manual') else ''}{it['title'][:120]} ({it['source']})")

    sent = 0
    for i in range(0, len(shortlist), VERIFY_BATCH):
        batch = shortlist[i:i + VERIFY_BATCH]
        texts = [article_text(it) for it in batch]
        for it, t in zip(batch, texts):
            it["_fulltext"] = t
        keep = [i for i, it in enumerate(batch) if it.get("manual") or not is_old_article(it)]
        for i, it in enumerate(batch):
            if i not in keep:
                print(f"[verify] dropped: old article from {it['article_date']}: {it['title'][:100]}")
        batch, texts = [batch[i] for i in keep], [texts[i] for i in keep]
        if not batch:
            continue
        today_msk = dt.datetime.now(MSK).date()
        user = (f"TODAY: {today_msk.isoformat()} ({WD_RU[today_msk.weekday()]})\n\n"
                + (f"IGNORED TOPICS (not relevant): {', '.join(IGNORED_TOPIC_TERMS)}\n\n" if IGNORED_TOPIC_TERMS else "")
                + feedback_block() + f"RECENT ALERTS:\n{recent_alerts_block()}\n\n" + "\n\n".join(
            f"ITEM {n}{' (ANALYST CHECK)' if it.get('manual') else ''}\nSource: {it['source']}\nPublished: "
            f"{pub_date_msk(it).isoformat()} ({WD_RU[pub_date_msk(it).weekday()]})\n"
            f"URL: {it['url']}\nTitle: {it['title']}\nText: {texts[n]}"
            for n, it in enumerate(batch)))
        res = ask_json(VERIFY_MODEL, VERIFY_PROMPT, user, max_tokens=3500)

        if res is None:
            # AI unavailable: still alert, clearly marked, so nothing is silently lost
            for it in batch:
                if it.get("manual"):
                    send("❔ Проверить ссылку не удалось: ИИ сейчас недоступен. Пришлите её ещё раз позже.",
                         reply_to=it.get("reply_to"))
                    continue
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

        answered = set()
        for r in res.get("results", []):
            n = r.get("n")
            if not isinstance(n, int) or not 0 <= n < len(batch):
                continue
            it = batch[n]
            answered.add(n)
            if r.get("relevant") is False:
                print(f"[verify] not relevant: {it['title'][:100]} — {r.get('reason_ru', '')}")
                if it.get("manual"):
                    send(f"🔎 <b>Проверка ссылки:</b> не относится к теме мониторинга.\n{e(r.get('reason_ru'))}",
                         reply_to=it.get("reply_to"))
                continue
            clean_vague_date(r)
            if re.fullmatch(r"\s*\d{4}-\d{2}-\d{2}\s*", r.get("date_text") or ""):
                # a made-up date (usually the publication date) - treat the date as unknown
                r["date_text"], r["date_start"], r["date_end"] = "", {"kind": "unknown"}, None
            w = resolve_when(r, it)
            dup = r.get("duplicate_of")
            row = db.execute("SELECT * FROM alerts WHERE id=?", (dup,)).fetchone() if isinstance(dup, int) else None
            if not row and not it.get("manual"):
                why = reject_reason(r, it, w)
                if why:
                    print(f"[verify] dropped by rule ({why}): {it['title'][:100]}")
                    continue
            print(f"[verify] RELEVANT{' (already alerted #' + str(dup) + ')' if row else ''}: {it['title'][:100]}")
            if row:
                handle_update(row, r, it, w)
                if it.get("manual"):
                    send("🔎 <b>Проверка ссылки:</b> это событие уже есть в оповещениях (см. ответ на исходное сообщение).",
                         reply_to=it.get("reply_to"))
                continue
            create_alert(r, it, w)
            sent += 1
        for n, it in enumerate(batch):
            if it.get("manual") and n not in answered:
                send("🔎 <b>Проверка ссылки:</b> ИИ не нашёл здесь анонса визита или встречи с участием "
                     "российских официальных лиц.", reply_to=it.get("reply_to"))
            elif n not in answered:
                print(f"[verify] not relevant: {it['title'][:100]}")

    # Housekeeping
    db.execute("DELETE FROM seen WHERE ts < ?", (time.time() - 14 * 86400,))
    db.commit()
    heartbeat(len(collected), broken)
    weekly_digest()
    meta_set("last_run_ts", str(run_started))
    print(f"Done. New alerts: {sent}. Telegram messages delivered: {DELIVERY['ok']}, failed: {DELIVERY['failed']}")
    if DELIVERY["failed"] and not DELIVERY["ok"]:
        # Make the GitHub run fail: GitHub then emails you, so a broken Telegram link can't go unnoticed
        raise RuntimeError(f"Telegram не принимает сообщения: {DELIVERY['last_error']}. "
                           f"Проверьте TELEGRAM_CHAT_ID и что бот состоит в группе.")


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
