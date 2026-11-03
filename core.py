# -*- coding: utf-8 -*-
"""
Core logic for the shopping-list price comparator.

Pipeline:
  1. download_store_files()  - Stores XML of each chain (transparency law files)
  2. find_nearby_stores()    - geocode branches in the chosen cities, keep the ones in radius
  3. download_price_files()  - PriceFull XML only for the nearby branches
  4. read_list_from_images() - Claude vision turns WhatsApp screenshots into items
  5. compare()               - match items to products and rank branches by basket cost
"""
import asyncio
import base64
import datetime as dt
import glob
import json
import math
import os
import re
import threading
import time
import unicodedata

import requests
from lxml import etree

BASE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(BASE, "data")
DUMPS = os.path.join(DATA, "dumps")
CONFIG_PATH = os.path.join(DATA, "config.json")
GEOCACHE_PATH = os.path.join(DATA, "geocache.json")
NEARBY_PATH = os.path.join(DATA, "nearby.json")
os.makedirs(DUMPS, exist_ok=True)

CLAUDE_MODEL = os.environ.get("CLAUDE_MODEL", "claude-sonnet-5-5")
USER_AGENT = "superzol-local-price-compare/1.0 (personal use)"

# scraper name -> Hebrew display name
CHAINS = {
    "SHUFERSAL": "שופרסל",
    "RAMI_LEVY": "רמי לוי",
    "VICTORY_NEW_SOURCE": "ויקטורי",
    "YOHANANOF": "יוחננוף",
    "OSHER_AD": "אושר עד",
    "HAZI_HINAM": "חצי חינם",
    "TIV_TAAM": "טיב טעם",
    "YAYNO_BITAN_AND_CARREFOUR": "יינות ביתן / קרפור",
    "MAHSANI_ASHUK_NEW_SOURCE": "מחסני השוק",
    "KESHET": "קשת טעמים",
    "SUPER_YUDA": "סופר יודה",
    "FRESH_MARKET_AND_SUPER_DOSH": "פרשמרקט",
    "KING_STORE": "קינג סטור",
    "STOP_MARKET": "סטופ מרקט",
    "ZOL_VEBEGADOL": "זול ובגדול",
    "NETIV_HASED": "נתיב החסד",
    "SHUK_AHIR": "שוק העיר",
    "CITY_MARKET_SHOPS": "סיטי מרקט",
    "DOR_ALON": "דור אלון (AM:PM)",
    "SUPER_SAPIR": "סופר ספיר",
    "POLIZER": "פוליצר",
    "SALACH_DABACH": "סאלח דבאח",
    "MAAYAN_2000": "מעיין 2000",
    "GOOD_PHARM": "גוד פארם",
    "SUPER_PHARM": "סופר פארם",
}
DEFAULT_CHAINS = ["SHUFERSAL", "RAMI_LEVY", "VICTORY_NEW_SOURCE", "YOHANANOF", "OSHER_AD",
                  "HAZI_HINAM", "YAYNO_BITAN_AND_CARREFOUR", "SUPER_YUDA"]

DEFAULT_CONFIG = {
    "address": "אופנהיימר 10, תל אביב",
    "home": None,            # {"lat":..,"lon":..,"label":..}; filled from address on first use
    "cities": "תל אביב, רמת גן, גבעתיים, בני ברק, רמת השרון, הרצליה, חולון, בת ים, "
              "פתח תקווה, גבעת שמואל, קרית אונו, אור יהודה, יהוד, כפר סבא, רעננה, "
              "הוד השרון, ראשון לציון, אזור, נתניה",
    "radius_km": 30,          # search boundary (straight line); drive time decides the recommendation
    "max_drive_min": 25,      # recommend only branches up to this drive time
    "worth_min": 30,          # a branch this far or more ...
    "worth_save": 50,
    "max_per_chain": 4,       # closest branches kept per chain/format
    "favorites": None,        # filled with DEFAULT_FAVORITES on first load         # ... is "not worth it" even if it saves more than this
    "chains": DEFAULT_CHAINS,
    "api_key": "",
    "include_club": False,
    "last_update": None,
}


# ---------------------------------------------------------------- config / io
def load_json(path, default):
    try:
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return default


def save_json(path, obj):
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(obj, f, ensure_ascii=False, indent=1)
    os.replace(tmp, path)


def load_config():
    cfg = dict(DEFAULT_CONFIG)
    cfg.update(load_json(CONFIG_PATH, {}))
    if not cfg.get("api_key"):
        cfg["api_key"] = os.environ.get("ANTHROPIC_API_KEY", "")
    if cfg.get("favorites") is None:
        cfg["favorites"] = [dict(f) for f in DEFAULT_FAVORITES]
    return cfg


def save_config(cfg):
    save_json(CONFIG_PATH, cfg)


# ---------------------------------------------------------------- job / progress
class Job:
    """One background job at a time, with a log the UI polls."""

    def __init__(self):
        self.lock = threading.Lock()
        self.running = False
        self.log = []
        self.error = None
        self.name = ""

    def say(self, msg):
        stamp = time.strftime("%H:%M:%S")
        with self.lock:
            self.log.append(f"{stamp}  {msg}")
            self.log = self.log[-300:]
        print(msg, flush=True)

    def start(self, name, fn):
        with self.lock:
            if self.running:
                return False
            self.running, self.error, self.log, self.name = True, None, [], name

        def run():
            try:
                fn(self)
            except Exception as e:  # report anything to the UI
                self.error = str(e)
                self.say(f"שגיאה: {e}")
            finally:
                self.running = False

        threading.Thread(target=run, daemon=True).start()
        return True

    def state(self):
        with self.lock:
            return {"running": self.running, "log": list(self.log), "error": self.error, "name": self.name}


JOB = Job()


# Central Bureau of Statistics settlement codes, used instead of names in some store lists
CBS_CITIES = {
    5000: "תל אביב", 8600: "רמת גן", 6300: "גבעתיים", 6100: "בני ברק", 2650: "רמת השרון",
    6400: "הרצליה", 6600: "חולון", 6200: "בת ים", 7900: "פתח תקווה", 681: "גבעת שמואל",
    2620: "קרית אונו", 2400: "אור יהודה", 9400: "יהוד", 6900: "כפר סבא", 8700: "רעננה",
    9700: "הוד השרון", 8300: "ראשון לציון", 565: "אזור", 7400: "נתניה", 3000: "ירושלים",
    4000: "חיפה", 70: "אשדוד", 7100: "אשקלון", 9000: "באר שבע", 8400: "רחובות",
    7400: "נתניה", 6500: "חדרה", 1200: "מודיעין", 2610: "בית שמש", 2640: "ראש העין",
    2660: "יבנה", 7200: "נס ציונה", 8500: "רמלה", 7000: "לוד", 1309: "אלעד",
    2630: "קרית גת", 9100: "נהריה", 7600: "עכו", 2800: "קרית שמונה", 6700: "טבריה",
    8000: "צפת", 1139: "כרמיאל", 2100: "טירת כרמל", 2300: "קרית טבעון", 6800: "קרית אתא",
    9500: "קרית ביאליק", 8200: "קרית מוצקין", 9600: "קרית ים", 2710: "אום אל פחם",
    3570: "אריאל", 3780: "ביתר עילית", 3797: "מודיעין עילית", 3616: "מעלה אדומים",
    2600: "אילת", 31: "אופקים", 2200: "דימונה", 1031: "שדרות", 246: "נתיבות",
    1034: "קרית מלאכי", 8800: "שפרעם", 7300: "נצרת", 1061: "נוף הגליל", 874: "מגדל העמק",
    240: "יקנעם עילית", 1015: "מבשרת ציון", 2560: "ערד", 168: "כפר יונה", 9200: "בית שאן",
}


def city_name(raw):
    """City field may be a name or a numeric CBS code."""
    raw = str(raw or "").strip()
    if raw.isdigit():
        return CBS_CITIES.get(int(raw), "")
    return raw


# ---------------------------------------------------------------- text helpers
_NIQQUD = re.compile(r"[֑-ׇ]")
_PUNCT = re.compile(r"[\"'`׳״\-–—_,.;:!?()\[\]{}/\\|*+]+")


def norm(s):
    s = unicodedata.normalize("NFKC", str(s or ""))
    s = _NIQQUD.sub("", s).lower()
    s = s.replace("%", " % ")
    s = _PUNCT.sub(" ", s)
    return re.sub(r"\s+", " ", s).strip()


def tokens(s):
    return [t for t in norm(s).split(" ") if t]


_FINALS = str.maketrans("ךםןףץ", "כמנפצ")


def stem(w):
    """Very small Hebrew stemmer: final letters, plural/feminine endings (בננות/בננה -> בננ)."""
    for suf in ("ים", "ות"):
        if len(w) > len(suf) + 2 and w.endswith(suf):
            w = w[:-len(suf)]
            break
    else:
        if len(w) > 3 and w[-1] in "הת":
            w = w[:-1]
    return w.translate(_FINALS)


def _tok_match(q, name_tokens):
    """1.0 exact, 0.8-0.9 prefix/stem/with Hebrew prefix letter, 0 otherwise."""
    if q in name_tokens:
        return 1.0
    if len(q) >= 4 and not q.isdigit():
        sq = stem(q)
        for t in name_tokens:
            if stem(t) == sq or (len(t) > 3 and t[0] in "הובלמש" and stem(t[1:]) == sq):
                return 0.9
    for t in name_tokens:
        if len(q) >= 2 and (t.startswith(q) or (len(t) >= 3 and q.startswith(t))):
            return 0.8
        # Hebrew prefixes: ה / ו / ב / ל / מ / ש
        if len(t) > 2 and t[0] in "הובלמש" and t[1:] == q:
            return 0.9
        if len(q) > 2 and q[0] in "הובלמש" and q[1:] == t:
            return 0.9
    return 0.0


def haversine_km(a_lat, a_lon, b_lat, b_lon):
    r = 6371.0
    p1, p2 = math.radians(a_lat), math.radians(b_lat)
    dphi = math.radians(b_lat - a_lat)
    dl = math.radians(b_lon - a_lon)
    h = math.sin(dphi / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return 2 * r * math.asin(math.sqrt(h))


# ---------------------------------------------------------------- geocoding (OpenStreetMap Nominatim)
_geo_lock = threading.Lock()
_last_geo = [0.0]


def geocode(query):
    """Returns {"lat","lon","label","city"} or None. Cached; respects 1 req/sec."""
    query = (query or "").strip()
    if not query:
        return None
    cache = load_json(GEOCACHE_PATH, {})
    if query in cache:
        return cache[query]
    with _geo_lock:
        wait = 1.1 - (time.time() - _last_geo[0])
        if wait > 0:
            time.sleep(wait)
        _last_geo[0] = time.time()
        try:
            r = requests.get(
                "https://nominatim.openstreetmap.org/search",
                params={"q": query, "format": "json", "countrycodes": "il", "limit": 1,
                        "addressdetails": 1, "accept-language": "he"},
                headers={"User-Agent": USER_AGENT}, timeout=20)
            r.raise_for_status()
            js = r.json()
        except Exception:
            return None
    res = None
    if js:
        a = js[0].get("address", {})
        res = {"lat": float(js[0]["lat"]), "lon": float(js[0]["lon"]),
               "label": js[0].get("display_name", ""),
               "city": a.get("city") or a.get("town") or a.get("village") or ""}
    cache = load_json(GEOCACHE_PATH, {})
    cache[query] = res
    save_json(GEOCACHE_PATH, cache)
    return res


# ---------------------------------------------------------------- drive time (OpenStreetMap routing, OSRM)
def estimate_drive_min(km):
    # roads ~1.3x straight line; ~25 km/h in town, up to ~55 km/h for longer (highway) trips
    speed = min(55.0, 25.0 + km * 1.5)
    return round(km * 1.3 / speed * 60 + 3)


def add_drive_times(home, stores):
    """Adds drive_min (+ drive_estimated) to each store. Uses the free OSRM server; no traffic data."""
    for i in range(0, len(stores), 80):
        chunk = stores[i:i + 80]
        coords = ";".join([f"{home['lon']},{home['lat']}"] + [f"{s['lon']},{s['lat']}" for s in chunk])
        durs = None
        try:
            r = requests.get(f"https://router.project-osrm.org/table/v1/driving/{coords}",
                             params={"sources": "0", "annotations": "duration"},
                             headers={"User-Agent": USER_AGENT}, timeout=30)
            if r.ok and r.json().get("code") == "Ok":
                durs = r.json()["durations"][0][1:]
        except Exception:
            durs = None
        for k, s in enumerate(chunk):
            d = durs[k] if durs and durs[k] is not None else None
            if d is not None:
                # OSRM has no traffic; add 25% for typical Gush Dan traffic
                s["drive_min"] = round(d / 60 * 1.25 + 1)
                s["drive_estimated"] = False
            else:
                s["drive_min"] = estimate_drive_min(s["distance_km"])
                s["drive_estimated"] = True
        time.sleep(1)


# ---------------------------------------------------------------- XML parsing
_PARSER = etree.XMLParser(recover=True, huge_tree=True, resolve_entities=False)


def _local(tag):
    if not isinstance(tag, str):
        return ""
    return tag.rsplit("}", 1)[-1].rsplit(":", 1)[-1].lower()


def _children(el):
    d = {}
    for c in el:
        k = _local(c.tag)
        if k and k not in d:
            d[k] = (c.text or "").strip()
    return d


def _parse(path):
    with open(path, "rb") as f:
        raw = f.read()
    if raw[:2] == b"\x1f\x8b":
        import gzip
        raw = gzip.decompress(raw)
    if raw[:2] in (b"\xff\xfe", b"\xfe\xff"):
        raw = raw.decode("utf-16").encode("utf-8")
        raw = re.sub(rb"encoding=['\"][^'\"]+['\"]", b'encoding="utf-8"', raw, count=1)
    root = etree.fromstring(raw, _PARSER)
    if root is None:
        raise ValueError("bad xml")
    return root


# Two naming styles exist:
#   PriceFull7290785400000-013-202611030010.xml           chain-store-YYYYMMDDHHMM
#   PriceFull7290058140886-001-024-20261103-001006.xml    chain-subchain-store-YYYYMMDD-HHMMSS
_FNAME = re.compile(r"(?i)(storesfull|stores?|pricefull|price|promofull|promo)(\d{13})?"
                    r"-(\d{1,4})-(?:(\d{1,4})-)?(\d{8})-?(\d{2,6})?")


def file_info(path):
    """(kind, chain_id, store_id, timestamp YYYYMMDDHHMMSS) from a transparency file name."""
    n = os.path.basename(path)
    m = _FNAME.search(n)
    if not m:
        return None
    kind = m.group(1).lower()
    kind = "stores" if kind.startswith("store") else kind
    store = m.group(4) if m.group(4) is not None else m.group(3)
    ts = m.group(5) + (m.group(6) or "").ljust(6, "0")
    return kind, m.group(2) or "", int(store), ts


def parse_stores(path, chain_key):
    root = _parse(path)
    info = file_info(path)
    chain_id_file = info[1] if info else ""
    chain_id_doc = ""
    chain_name_doc = ""
    for el in root.iter():
        k = _local(el.tag)
        if k == "chainid" and not chain_id_doc:
            chain_id_doc = (el.text or "").strip()
        if k == "chainname" and not chain_name_doc:
            chain_name_doc = (el.text or "").strip()
    out = []
    for el in root.iter():
        ch = _children(el)
        if "storeid" not in ch or not ch["storeid"].strip().isdigit():
            continue
        if len(el) < 3:
            continue
        sub = ch.get("subchainname") or ""
        out.append({
            "chain_key": chain_key,
            "chain_id": chain_id_file or ch.get("chainid") or chain_id_doc,
            "chain_name": CHAINS.get(chain_key) or ch.get("chainname") or chain_name_doc,
            "sub_chain": sub,
            "store_id": int(ch["storeid"]),
            "name": ch.get("storename") or ch.get("storenm") or "",
            "address": ch.get("address") or "",
            "city": city_name(ch.get("city")) or (ch.get("city") or ""),
            "zip": ch.get("zipcode") or "",
        })
    return out


def parse_prices(path):
    """Returns {item_code: {...}} for one store file."""
    root = _parse(path)
    items = {}
    for el in root.iter():
        if _local(el.tag) not in ("item", "product", "line"):
            continue
        ch = _children(el)
        code = ch.get("itemcode", "").strip()
        price = ch.get("itemprice", "").strip()
        if not code or not price:
            continue
        try:
            p = float(price)
        except ValueError:
            continue
        if p <= 0:
            continue
        items[code] = {
            "code": code,
            "name": ch.get("itemname") or ch.get("itemnm") or ch.get("manufactureritemdescription") or "",
            "manufacturer": ch.get("manufacturername") or ch.get("manufacturename") or "",
            "price": p,
            "unit_price": _f(ch.get("unitofmeasureprice")),
            "unit": ch.get("unitofmeasure") or "",
            "qty": ch.get("quantity") or "",
            "unit_qty": ch.get("unitqty") or "",
            "weighted": (ch.get("bisweighted") or "0").strip() in ("1", "true", "True"),
            "updated": ch.get("priceupdatedate") or "",
        }
    return items


def _f(v):
    try:
        return float(v)
    except (TypeError, ValueError):
        return None


def scan_files(chain_key, kind):
    """[(chain_id, store_id, ts, path)] for every downloaded file of this kind."""
    out = []
    for p in glob.glob(os.path.join(DUMPS, chain_key, "**", "*"), recursive=True):
        if os.path.isdir(p) or p.endswith((".json", ".txt", ".log")):
            continue
        info = file_info(p)
        if info and info[0] == kind:
            out.append((info[1], info[2], info[3], p))
    return out


def latest_files(chain_key, kind):
    """{(chain_id, store_id): path}, newest file of each. One chain folder can hold
    several chain ids (e.g. Shufersal + Shufersal BE), each with its own stores file."""
    best = {}
    for cid, sid, ts, p in scan_files(chain_key, kind):
        k = (cid, None if kind == "stores" else sid)
        if k not in best or ts > best[k][0]:
            best[k] = (ts, p)
    return {k: v[1] for k, v in best.items()}


def _store_matches(store, files):
    """Files (cid, sid, ts, path) that belong to this store."""
    sid, cid = store["store_id"], str(store.get("chain_id") or "")
    mine = [f for f in files if f[1] == sid]
    exact = [f for f in mine if f[0] == cid]
    if exact or (cid and any(f[0] == cid for f in files)):
        return exact
    # several chains share this folder (e.g. Shufersal + BE): never borrow another chain's files
    if len({k[0] for k in latest_files(store["chain_key"], "stores")}) > 1:
        return []
    return mine  # chain id unknown or files carry a different id: fall back to store id


def store_file(store, kind):
    """Newest file of this kind for the store, or None."""
    m = _store_matches(store, scan_files(store["chain_key"], kind))
    return max(m, key=lambda f: f[2])[3] if m else None


def files_after(store, kind, after_ts=""):
    """All files of one store and kind newer than after_ts, oldest first: [(ts, path)]."""
    out = [(ts, p) for _, _, ts, p in _store_matches(store, scan_files(store["chain_key"], kind))
           if ts > after_ts]
    # one entry per timestamp (the same file may exist as .gz and extracted)
    seen, uniq = set(), []
    for ts, p in sorted(out):
        if ts not in seen:
            seen.add(ts)
            uniq.append((ts, p))
    return uniq


# ---------------------------------------------------------------- promotions
def _dtparse(date_s, hour_s=""):
    d = re.search(r"(\d{4})-?(\d{2})-?(\d{2})", date_s or "")
    if not d:
        return None
    h = re.search(r"(\d{1,2}):(\d{2})", hour_s or "") or re.search(r"[ T](\d{1,2}):(\d{2})", date_s or "")
    hh, mm = (int(h.group(1)), int(h.group(2))) if h else (0, 0)
    try:
        return dt.datetime(int(d.group(1)), int(d.group(2)), int(d.group(3)), min(hh, 23), mm)
    except ValueError:
        return None


def parse_promos(path):
    """{promotion_id: promo} for one promo file."""
    root = _parse(path)
    promos = {}
    for el in root.iter():
        if _local(el.tag) not in ("promotion", "sale"):
            continue
        ch = _children(el)
        pid = ch.get("promotionid") or ""
        if not pid:
            continue
        codes, clubs = [], []
        for d in el.iter():
            k = _local(d.tag)
            if k == "itemcode" and (d.text or "").strip():
                parent = d.getparent()
                gift = _children(parent).get("isgiftitem", "0") if parent is not None else "0"
                if gift.strip() not in ("1", "true"):
                    codes.append(d.text.strip())
            elif k == "clubid" and (d.text or "").strip():
                clubs.append(d.text.strip())
        promos[pid] = {
            "id": pid,
            "desc": ch.get("promotiondescription") or "",
            "start": _dtparse(ch.get("promotionstartdate"), ch.get("promotionstarthour")),
            "end": _dtparse(ch.get("promotionenddate"), ch.get("promotionendhour")),
            "reward": (ch.get("rewardtype") or "").strip(),
            "min_qty": _f(ch.get("minqty")) or 1.0,
            "price": _f(ch.get("discountedprice")),
            "rate": _f(ch.get("discountrate")),
            "coupon": (ch.get("additionaliscoupon") or "0").strip() in ("1", "true"),
            "total": (ch.get("additionalistotal") or "0").strip() in ("1", "true"),
            "min_purchase": _f(ch.get("minpurchaseamnt")) or 0,
            "club": any(c not in ("0", "00", "") for c in clubs),
            "codes": codes,
        }
    return promos


def promo_unit_price(promo, regular, qty):
    """Effective price per unit for this promo, or None if it doesn't apply/can't be trusted."""
    if promo["coupon"] or promo["total"] or promo["min_purchase"] > 0:
        return None
    min_q = max(promo["min_qty"], 1.0) if promo["min_qty"] >= 1 else promo["min_qty"]
    if qty + 1e-9 < min_q:
        return None
    unit = None
    if promo["price"] and promo["price"] > 0:
        p = promo["price"]
        # "2 ב-20" is published as MinQty=2, DiscountedPrice=20 (price of the bundle)
        if min_q > 1 and p > regular * 1.01:
            unit = p / min_q
        elif min_q > 1 and p <= regular and p / min_q < regular * 0.2:
            unit = p
        else:
            unit = p if p < regular else p / min_q
    elif promo["rate"] and promo["rate"] > 0:
        r = promo["rate"]
        r = r / 100 if r > 100 else r
        if 0 < r <= 90:
            unit = regular * (1 - r / 100)
    if unit is None or not (regular * 0.15 <= unit < regular - 0.005):
        return None
    if min_q > 1 and qty > min_q:
        # only full bundles get the deal; the rest at regular price
        bundles = math.floor(qty / min_q + 1e-9)
        rest = qty - bundles * min_q
        unit = (bundles * min_q * unit + rest * regular) / qty
    return unit


# ---------------------------------------------------------------- downloading (il-supermarket-scraper)
def _israel_today():
    return dt.datetime.utcnow() + dt.timedelta(hours=2)


_ERR_LOCAL = threading.local()
_log_ready = [False]


def _err():
    """Library warnings/errors collected in the current thread (one thread per chain)."""
    if not hasattr(_ERR_LOCAL, "errors"):
        _ERR_LOCAL.errors = []
    return _ERR_LOCAL.errors


def _hook_library_log():
    """Keep the scraper library's warnings for the UI, and its full log in data/scraper.log."""
    if _log_ready[0]:
        return
    import logging
    from il_supermarket_scarper.utils import Logger

    class Keep(logging.Handler):
        def emit(self, rec):
            if rec.levelno >= logging.WARNING:
                e = _err()
                e.append(rec.getMessage()[:300])
                del e[:-50]

    Logger.set_logging_level("INFO")
    fh = logging.FileHandler(os.path.join(DATA, "scraper.log"), encoding="utf-8")
    fh.setFormatter(logging.Formatter("%(asctime)s %(levelname)s %(message)s"))
    Logger.logger.addHandler(fh)
    Logger.logger.addHandler(Keep())
    _log_ready[0] = True


async def _scrape_async(chain_key, files_type, store_id=None, when=None):
    from il_supermarket_scarper import ScraperFactory
    from il_supermarket_scarper.utils.files.file_output import DiskFileOutput
    _hook_library_log()

    cls = ScraperFactory[chain_key].value
    out = DiskFileOutput(storage_path=os.path.join(DUMPS, chain_key))
    scraper = cls(file_output=out)
    kw = {"files_types": [files_type]}
    if store_id:
        kw["store_id"] = int(store_id)
    if when is not None:
        kw["when_date"] = when
    n = 0
    async for _ in scraper.scrape(**kw):
        n += 1
    return n


def scrape(chain_key, files_type, store_id=None, when=None):
    """Download matching files; never raises (errors go to _err()) so files already on disk still count."""
    if os.environ.get("SUPERZOL_OFFLINE"):
        return 0
    try:
        return asyncio.run(_scrape_async(chain_key, files_type, store_id, when))
    except Exception as e:
        _err().append(f"{type(e).__name__}: {e}"[:300])
        return 0


STORES_CHECK_PATH = os.path.join(DATA, "stores_checked.json")


def download_store_files(job, chains):
    checked = load_json(STORES_CHECK_PATH, {})
    for ck in chains:
        if latest_files(ck, "stores") and time.time() - checked.get(ck, 0) < 7 * 86400:
            continue
        job.say(f"{CHAINS.get(ck, ck)}: מוריד רשימת סניפים...")
        try:
            # no date filter: some chains publish several store lists (e.g. Shufersal + BE)
            del _err()[:]
            scrape(ck, "STORE_FILE")
            if _err() and not latest_files(ck, "stores"):
                raise RuntimeError(_err()[-1][:150])
            checked[ck] = time.time()
            save_json(STORES_CHECK_PATH, checked)
        except Exception as e:
            job.say(f"{CHAINS.get(ck, ck)}: נכשל ({e})")
        n = len(latest_files(ck, "stores"))
        if not n:
            job.say(f"{CHAINS.get(ck, ck)}: לא נמצא קובץ סניפים")
        elif n > 1:
            job.say(f"{CHAINS.get(ck, ck)}: נמצאו {n} רשימות סניפים (תתי-רשתות)")


def all_stores(chains):
    stores = []
    for ck in chains:
        for p in latest_files(ck, "stores").values():
            try:
                stores += parse_stores(p, ck)
            except Exception as e:
                print("store parse failed", p, e)
    # dedupe
    seen, out = set(), []
    for s in stores:
        k = (s["chain_key"], s["chain_id"], s["store_id"])
        if k not in seen:
            seen.add(k)
            out.append(s)
    return out


def find_nearby_stores(job, cfg):
    home = cfg.get("home")
    if not home and cfg.get("address"):
        loc = geocode(cfg["address"])
        if loc:
            home = cfg["home"] = dict(loc, query=cfg["address"])
            save_config(cfg)
    if not home:
        raise RuntimeError("קודם צריך להגדיר כתובת בית")
    cities = [norm(c) for c in re.split(r"[,\n]", cfg.get("cities") or "") if norm(c)]
    if not cities and home.get("city"):
        cities = [norm(home["city"])]
    radius = float(cfg.get("radius_km") or 5)
    stores = all_stores(cfg["chains"])
    job.say(f"נמצאו {len(stores)} סניפים בכל הרשתות שנבחרו; מסנן לפי ערים: {', '.join(cities) or 'הכל'}")

    def in_cities(s):
        if not cities:
            return True
        blob = norm(f"{s['city']} {s['address']} {s['name']}")
        return any(c in blob for c in cities)

    cand = [s for s in stores if in_cities(s)]
    job.say(f"{len(cand)} סניפים בערים שבחרת. מאתר מיקום (פעם ראשונה לוקח קצת זמן)...")
    nearby = []
    for i, s in enumerate(cand):
        city = s["city"] if not s["city"].isdigit() else ""
        queries = []
        if s["address"]:
            queries.append(f"{s['address']}, {city or s['name']}")
        if city:
            queries.append(f"{s['name']}, {city}")
        loc = None
        for q in queries:
            loc = geocode(q)
            if loc:
                break
        if not loc:
            continue
        d = haversine_km(home["lat"], home["lon"], loc["lat"], loc["lon"])
        if d <= radius:
            s = dict(s, lat=loc["lat"], lon=loc["lon"], distance_km=round(d, 2))
            nearby.append(s)
        if (i + 1) % 10 == 0:
            job.say(f"  ...{i + 1}/{len(cand)}")
    job.say("מחשב זמני נסיעה...")
    add_drive_times(home, nearby)
    nearby.sort(key=lambda s: s["drive_min"])
    # same chain + format usually has the same prices: keep only the closest few of each
    per = int(cfg.get("max_per_chain") or 4)
    favs = {id(s) for s in match_favorites(cfg, nearby).values()}
    count, kept = {}, []
    for s in nearby:
        if id(s) in favs:
            kept.append(s)
            continue
        k = (s["chain_key"], s.get("chain_id"), s.get("sub_chain") or "")
        count[k] = count.get(k, 0) + 1
        if count[k] <= (min(per, SLOW_PER_CHAIN) if s["chain_key"] in SLOW_CHAINS else per):
            kept.append(s)
    if len(kept) < len(nearby):
        job.say(f"נשארו {len(kept)} סניפים: {per} הקרובים מכל רשת ופורמט")
    nearby = kept
    save_json(NEARBY_PATH, nearby)
    job.say(f"{len(nearby)} סניפים ברדיוס {radius:g} ק\"מ")
    return nearby


SCRAPE_TIMEOUT = int(os.environ.get("SUPERZOL_SCRAPE_TIMEOUT", "180"))  # seconds per site request


def scrape_limited(chain_key, files_type, store_id=None, when=None, timeout=None):
    """scrape() with a time limit, so a slow or throttling site can't stall the whole update.
    On timeout the download keeps going in the background and we move on."""
    if timeout is None:
        timeout = SLOW_TIMEOUT if chain_key in SLOW_CHAINS else SCRAPE_TIMEOUT
    box = {}
    errs = _err()

    def run():
        _ERR_LOCAL.errors = errs  # report into the caller's error list
        box["n"] = scrape(chain_key, files_type, store_id, when)

    t = threading.Thread(target=run, daemon=True)
    t.start()
    t.join(timeout)
    if t.is_alive():
        errs.append(f"timeout after {timeout}s")
        return None
    return box.get("n", 0)


CHECKED_PATH = os.path.join(DATA, "checked.json")
# Shufersal's site answers very slowly: once a day full prices + promos only, fewer branches, shorter wait
SLOW_CHAINS = {"SHUFERSAL"}
SLOW_PER_CHAIN = 2
SLOW_TIMEOUT = 90
RECHECK_MIN = int(os.environ.get("SUPERZOL_RECHECK_MIN", "60"))  # skip branches checked this recently


def download_price_files(job, nearby, force=False):
    """Chains run in parallel (one worker per chain), branches of a chain one after another.
    Branches checked successfully in the last RECHECK_MIN minutes are skipped (unless force)."""
    from concurrent.futures import ThreadPoolExecutor

    checked = load_json(CHECKED_PATH, {})
    done = [0]
    total = len(nearby)

    today = _israel_today()
    today_s = today.strftime("%Y%m%d")
    ok = [0]
    lock = threading.Lock()

    def full(s, ftype, kind, st):
        """Make sure there's a recent full file. At most 2 site requests. Returns its timestamp."""
        ck, sid = s["chain_key"], s["store_id"]
        cur = store_file(s, kind)
        if not (cur and file_info(cur)[3][:8] == today_s):
            n = scrape_limited(ck, ftype, store_id=sid, when=today)
            if n is None:
                st["timeout"] = True
            elif store_file(s, kind) == cur:
                # nothing from today: take whatever the site lists for this branch (usually yesterday's)
                st["timeout"] = scrape_limited(ck, ftype, store_id=sid) is None
        cur = store_file(s, kind)
        return file_info(cur)[3] if cur else None

    def updates(s, ftype, kind, base_ts):
        before = len(files_after(s, kind, base_ts or ""))
        scrape_limited(s["chain_key"], ftype, store_id=s["store_id"], when=today)
        return len(files_after(s, kind, base_ts or "")) - before

    def one(s):
        sid = s["store_id"]
        label = f"{s['chain_name']} {s['name']}"
        ck_key = f"{s['chain_key']}|{s.get('chain_id')}|{sid}"
        with lock:
            done[0] += 1
            n_now = done[0]
        age = (time.time() - checked.get(ck_key, 0)) / 60
        slow = s["chain_key"] in SLOW_CHAINS
        have = store_file(s, "pricefull")
        if not force and slow and have and file_info(have)[3][:8] == today_s:
            with lock:
                ok[0] += 1
            job.say(f"[{n_now}/{total}] {label}: מחירי היום כבר קיימים (ברשת הזו מעדכנים פעם ביום)")
            return "skip"
        if not force and age < RECHECK_MIN and have:
            with lock:
                ok[0] += 1
            job.say(f"[{n_now}/{total}] {label}: נבדק לפני {age:.0f} דק', מדלג")
            return "skip"
        job.say(f"[{n_now}/{total}] {label}: בודק מחירים ומבצעים...")
        del _err()[:]
        st = {}
        base = full(s, "PRICE_FULL_FILE", "pricefull", st)
        if not base:
            errs = _err()
            if st.get("timeout"):
                why = "האתר של הרשת איטי מדי כרגע, ננסה שוב בעדכון הבא"
            else:
                why = "האתר לא מפרסם קובץ מחירים לסניף הזה"
                real = [e for e in errs if "No files to download" not in e]
                if real:
                    why += f"; {real[-1][:120]}"
            job.say(f"{label} (סניף {sid}): אין מחירים. {why}")
            return "timeout" if st.get("timeout") else "none"
        with lock:
            ok[0] += 1
        pst = {}
        if slow:
            n_upd = 0
            pbase = full(s, "PROMO_FULL_FILE", "promofull", pst)
        else:
            n_upd = updates(s, "PRICE_FILE", "price", base)
            pbase = full(s, "PROMO_FULL_FILE", "promofull", pst)
            if not pst.get("timeout"):
                updates(s, "PROMO_FILE", "promo", pbase or "")
        with lock:
            checked[ck_key] = time.time()
            save_json(CHECKED_PATH, checked)
        last = files_after(s, "price", base)
        last_ts = last[-1][0] if last else base
        job.say(f"{label}: ✓ מחירים נכונים ל-{last_ts[6:8]}/{last_ts[4:6]} {last_ts[8:10]}:{last_ts[10:12]}"
                f" ({n_upd} עדכונים חדשים){'' if pbase else ' · אין קובץ מבצעים'}")

    def chain_worker(stores):
        slow = 0
        for i, s in enumerate(stores):
            if slow >= 2:
                rest = len(stores) - i
                job.say(f"{s['chain_name']}: האתר לא עונה, מדלג על עוד {rest} סניפים. ננסה בעדכון הבא")
                return
            try:
                slow = slow + 1 if one(s) == "timeout" else 0
            except Exception as e:
                job.say(f"{s['chain_name']} {s['name']}: שגיאה ({e})")

    by_chain = {}
    for s in nearby:
        by_chain.setdefault(s["chain_key"], []).append(s)
    # favourites first inside each chain, so my regular stores are ready soonest
    fav_ids = {id(x) for x in match_favorites(load_config(), nearby).values()}
    for lst in by_chain.values():
        lst.sort(key=lambda x: (id(x) not in fav_ids, x.get("drive_min", 99)))
    with ThreadPoolExecutor(max_workers=max(1, len(by_chain))) as ex:
        list(ex.map(chain_worker, by_chain.values()))
    return ok[0]


NEARBY_META = os.path.join(DATA, "nearby_meta.json")


def _nearby_signature(cfg):
    keys = ("address", "cities", "radius_km", "chains", "favorites", "max_per_chain")
    return json.dumps({k: cfg.get(k) for k in keys}, ensure_ascii=False, sort_keys=True)


def full_update(job):
    cfg = load_config()
    download_store_files(job, cfg["chains"])
    meta = load_json(NEARBY_META, {})
    nearby = load_json(NEARBY_PATH, [])
    if nearby and meta.get("sig") == _nearby_signature(cfg) and time.time() - meta.get("t", 0) < 7 * 86400:
        job.say(f"{len(nearby)} סניפים קרובים (שמורים מהפעם הקודמת)")
    else:
        old = nearby
        nearby = find_nearby_stores(job, cfg)
        if nearby:
            save_json(NEARBY_META, {"sig": _nearby_signature(cfg), "t": time.time()})
        elif old:
            # locating failed (no internet / map service down): keep the previous list
            save_json(NEARBY_PATH, old)
            nearby = old
            job.say(f"איתור הסניפים נכשל, ממשיך עם {len(old)} הסניפים מהפעם הקודמת")
    if not nearby:
        job.say("לא נמצאו סניפים קרובים. נסה להגדיל רדיוס או להוסיף ערים.")
        return
    ok = download_price_files(job, nearby)
    job.say(f"מחירים נמצאו ל-{ok} מתוך {len(nearby)} סניפים")
    cfg = load_config()
    cfg["last_update"] = time.strftime("%Y-%m-%d %H:%M")
    save_config(cfg)
    job.say("העדכון הסתיים ✓")


# ---------------------------------------------------------------- Claude API
def claude(api_key, content, max_tokens=4000, system=None):
    if not api_key:
        raise RuntimeError("חסר מפתח Claude API (בהגדרות)")
    body = {"model": CLAUDE_MODEL, "max_tokens": max_tokens,
            "messages": [{"role": "user", "content": content}]}
    if system:
        body["system"] = system
    r = requests.post("https://api.anthropic.com/v1/messages", json=body, timeout=180,
                      headers={"x-api-key": api_key, "anthropic-version": "2023-06-01",
                               "content-type": "application/json"})
    if r.status_code != 200:
        raise RuntimeError(f"Claude API {r.status_code}: {r.text[:300]}")
    return "".join(b.get("text", "") for b in r.json().get("content", []) if b.get("type") == "text")


def _json_from(text):
    m = re.search(r"\{.*\}|\[.*\]", text, re.S)
    if not m:
        raise ValueError("no json in model answer")
    return json.loads(m.group(0))


def read_list_from_images(api_key, images):
    """images: list of (media_type, base64). Returns [{"name","qty","note"}]."""
    content = [{"type": "image", "source": {"type": "base64", "media_type": mt, "data": b64}}
               for mt, b64 in images]
    content.append({"type": "text", "text": (
        "אלה צילומי מסך מוואטסאפ עם רשימת קניות לסופרמרקט. "
        "חלץ את כל פריטי הקנייה מכל התמונות (בלי כפילויות, בלי שעות/שמות שולחים/טקסט שאינו פריט). "
        "לכל פריט: name = שם המוצר כפי שכתוב, מתוקן מעט אם יש שגיאת כתיב ברורה, כולל מותג/גודל/אחוז שומן אם צוינו; "
        "qty = כמות כמספר שלם, או null אם לא צוינה כמות; unit = \"kg\" אם הכמות צוינה במשקל (ק\"ג, חצי קילו=0.5, גרם/1000), אחרת \"units\"; "
        "note = הערה קצרה אם יש (למשל 'הכי זול', 'ללא גלוטן'), אחרת ריק. "
        'החזר JSON בלבד בפורמט: {"items":[{"name":"","qty":null,"unit":"units","note":""}]}')})
    js = _json_from(claude(api_key, content))
    items = js.get("items", js) if isinstance(js, dict) else js
    out = []
    for it in items:
        name = str(it.get("name", "")).strip()
        if name:
            try:
                q = float(it["qty"]) if it.get("qty") not in (None, "") else None
            except (TypeError, ValueError):
                q = None
            mode = "kg" if str(it.get("unit") or "").lower() == "kg" else "units"
            out.append({"name": name, "qty": q, "mode": mode, "note": str(it.get("note") or "")})
    return normalize_items(out)


# ---------------------------------------------------------------- produce, emojis, preferences, favorites
PREFS_PATH = os.path.join(DATA, "prefs.json")
IMG_DIR = os.path.join(DATA, "img")

# keywords (prefix match on words), emoji, default count, kg per unit, unit label
PRODUCE = [
    (("תפוח אדמה", "תפוחי אדמה", "תפוא"), "🥔", 6, 0.2, "יח'"),
    (("בטטה", "בטטות"), "🍠", 3, 0.3, "יח'"),
    (("עגבניות שרי", "עגבניה שרי", "שרי"), "🍅", 1, 0.25, "קופסה"),
    (("בננה", "בננות"), "🍌", 5, 0.18, "יח'"),
    (("תפוח", "תפוחים", "תפוחי עץ"), "🍎", 5, 0.2, "יח'"),
    (("אגס", "אגסים"), "🍐", 4, 0.18, "יח'"),
    (("מלפפון", "מלפפונים"), "🥒", 6, 0.12, "יח'"),
    (("עגבניה", "עגבניות"), "🍅", 6, 0.15, "יח'"),
    (("בצל", "בצלים"), "🧅", 4, 0.15, "יח'"),
    (("גזר",), "🥕", 6, 0.1, "יח'"),
    (("פלפל", "פלפלים"), "🫑", 3, 0.2, "יח'"),
    (("אבוקדו",), "🥑", 3, 0.2, "יח'"),
    (("לימון", "לימונים"), "🍋", 4, 0.12, "יח'"),
    (("תפוז", "תפוזים"), "🍊", 5, 0.25, "יח'"),
    (("קלמנטינה", "קלמנטינות", "מנדרינה"), "🍊", 8, 0.1, "יח'"),
    (("ענבים", "ענב"), "🍇", 1, 0.5, "אריזה"),
    (("קישוא", "קישואים"), "🥒", 4, 0.2, "יח'"),
    (("חציל", "חצילים"), "🍆", 2, 0.35, "יח'"),
    (("אפרסק", "אפרסקים", "נקטרינה"), "🍑", 5, 0.17, "יח'"),
    (("מנגו",), "🥭", 2, 0.35, "יח'"),
    (("אבטיח",), "🍉", 1, 4.0, "יח'"),
    (("מלון",), "🍈", 1, 1.5, "יח'"),
    (("קיווי",), "🥝", 5, 0.08, "יח'"),
    (("שום",), "🧄", 2, 0.05, "ראש"),
    (("כרובית",), "🥦", 1, 0.8, "יח'"),
    (("ברוקולי",), "🥦", 1, 0.5, "יח'"),
    (("כרוב",), "🥬", 1, 1.0, "יח'"),
    (("חסה",), "🥬", 1, 0.4, "יח'"),
    (("תירס",), "🌽", 1, None, "קופסה"),
    (("תות", "תותים"), "🍓", 1, 0.25, "קופסה"),
]

EMOJI_WORDS = [
    (("חלב",), "🥛"), (("לחם", "לחמניות", "פיתות", "פיתה", "חלה"), "🍞"), (("ביצים", "ביצה"), "🥚"),
    (("קוטג", "גבינה", "גבינת", "בולגרית", "צהובה", "מוצרלה"), "🧀"), (("יוגורט", "מעדן", "דני"), "🥣"),
    (("חמאה",), "🧈"), (("עוף", "חזה", "שניצל", "פרגית", "כרעיים"), "🍗"), (("בשר", "טחון", "אנטריקוט", "סטייק"), "🥩"),
    (("דג", "סלמון", "טונה"), "🐟"), (("אורז",), "🍚"), (("פסטה", "ספגטי", "פתיתים"), "🍝"),
    (("קפה",), "☕"), (("תה",), "🍵"), (("שמן",), "🫒"), (("מים",), "💧"), (("מיץ", "שתיה", "קולה", "סודה"), "🧃"),
    (("יין",), "🍷"), (("בירה",), "🍺"), (("שוקולד",), "🍫"), (("במבה", "ביסלי", "חטיף", "צ'יפס", "צ׳יפס"), "🍿"),
    (("עוגיות", "עוגה", "ופל"), "🍪"), (("גלידה",), "🍦"), (("דבש",), "🍯"), (("קמח",), "🌾"), (("סוכר", "מלח"), "🧂"),
    (("נייר טואלט", "טואלט", "מגבות"), "🧻"), (("סבון", "שמפו", "מרכך", "אבקת כביסה", "נוזל כלים"), "🧼"),
    (("חומוס", "טחינה", "ממרח"), "🥙"), (("קורנפלקס", "דגני"), "🥣"), (("שימורים", "תירס שימורים"), "🥫"),
    (("נקניק", "נקניקיות", "פסטרמה"), "🌭"), (("פיצה",), "🍕"), (("ירקות", "פירות"), "🥗"),
]


def _word_hit(name_n, kws):
    words = name_n.split()
    for kw in kws:
        k = norm(kw)
        if " " in k:
            if k in name_n:
                return True
        elif any(w == k or w.startswith(k) or (len(w) > 2 and w[0] in "הובלמש" and w[1:].startswith(k))
                 for w in words):
            return True
    return False


def produce_info(name):
    n = norm(name)
    for kws, emo, cnt, kg, label in PRODUCE:
        if _word_hit(n, kws):
            return {"emoji": emo, "count": cnt, "unit_kg": kg, "unit_label": label}
    return None


def emoji_for(name):
    p = produce_info(name)
    if p:
        return p["emoji"]
    n = norm(name)
    for kws, emo in EMOJI_WORDS:
        if _word_hit(n, kws):
            return emo
    return "🛒"


def load_prefs():
    return load_json(PREFS_PATH, {})


def pref_key(name):
    return norm(name)


def normalize_items(items):
    """Fill defaults: produce counts, saved preferences (⭐), emoji. qty None = not specified."""
    prefs = load_prefs()
    out = []
    for it in items:
        name = str(it.get("name") or "").strip()
        if not name:
            continue
        p = prefs.get(pref_key(name))
        prod = produce_info(name)
        qty, mode = it.get("qty"), it.get("mode")
        given = qty not in (None, "", 0)
        if p and not given:
            qty, mode = p.get("qty"), p.get("mode")
        if not given and qty in (None, "", 0):
            qty = prod["count"] if prod else 1
        if not mode:
            mode = "units"
        try:
            qty = float(qty)
        except (TypeError, ValueError):
            qty = 1.0
        if mode == "units":
            qty = max(1.0, float(round(qty)))
        out.append({
            "name": name, "qty": qty, "mode": mode, "note": it.get("note") or "",
            "emoji": emoji_for(name), "unit_label": prod["unit_label"] if prod else "יח'",
            "unit_kg": prod["unit_kg"] if prod else None, "produce": bool(prod),
            "starred": bool(p), "hint": (p or {}).get("hint") or (p or {}).get("product_name") or it.get("hint", ""),
            "pref_product": (p or {}).get("product_name", ""),
        })
    return out


def save_pref(pref_name, on=True, **fields):
    prefs = load_prefs()
    k = pref_key(pref_name)
    if not on:
        prefs.pop(k, None)
    else:
        p = prefs.get(k, {"name": pref_name})
        for f, v in fields.items():
            if v is not None:
                p[f] = v
        prefs[k] = p
    save_json(PREFS_PATH, prefs)
    return prefs.get(k)


def read_product_photo(api_key, media_type, b64):
    """Product photo -> short description (brand, product, size) to use as a preference."""
    content = [{"type": "image", "source": {"type": "base64", "media_type": media_type, "data": b64}},
               {"type": "text", "text": "זו תמונה של מוצר מהסופר. כתוב בשורה אחת בעברית: מותג, שם המוצר, וגודל/משקל/אחוז שומן "
                                        "כפי שמופיע על האריזה. אם יש ברקוד קריא, הוסף בסוף: ברקוד=<מספר>. בלי שום טקסט נוסף."}]
    txt = claude(api_key, content, max_tokens=200).strip().splitlines()[0]
    m = re.search(r"ברקוד\s*=\s*(\d{8,14})", txt)
    return re.sub(r"\s*ברקוד\s*=\s*\d+", "", txt).strip(), (m.group(1) if m else None)


# favorites: rules matched against the branch list (chain + any keyword in name/address/city),
# or exact branch ids added from the results screen
DEFAULT_FAVORITES = [
    {"label": "קרפור נווה אביבים", "chain_key": "YAYNO_BITAN_AND_CARREFOUR", "any": ["נווה אביבים", "אופנהיימר"]},
    {"label": "שופרסל טאגור", "chain_key": "SHUFERSAL", "any": ["טאגור", "טגור"]},
    {"label": "קרפור שוסטר", "chain_key": "YAYNO_BITAN_AND_CARREFOUR", "any": ["שוסטר"]},
    {"label": "אושר עד בני ברק", "chain_key": "OSHER_AD", "any": ["בני ברק"]},
    {"label": "רמי לוי בני ברק", "chain_key": "RAMI_LEVY", "any": ["בני ברק"]},
]


def _fav_match(rule, s):
    if rule.get("chain_key") != s["chain_key"]:
        return False
    if rule.get("store_id") is not None:
        return int(rule["store_id"]) == s["store_id"] and str(rule.get("chain_id") or s.get("chain_id")) == str(s.get("chain_id"))
    blob = norm(f"{s.get('name', '')} {s.get('address', '')} {s.get('city', '')}")
    return any(norm(k) in blob for k in rule.get("any", []))


def match_favorites(cfg, stores):
    """{rule index: store} using the closest branch for each rule."""
    favs = cfg.get("favorites") or []
    out = {}
    for i, rule in enumerate(favs):
        hits = [s for s in stores if _fav_match(rule, s)]
        if hits:
            out[i] = min(hits, key=lambda s: s.get("drive_min", s.get("distance_km", 99)))
    return out


def product_image(code):
    """Front image of a product by barcode from Open Food Facts (cached). Returns bytes or None."""
    if not re.fullmatch(r"\d{8,14}", code or ""):
        return None
    os.makedirs(IMG_DIR, exist_ok=True)
    path, miss = os.path.join(IMG_DIR, code + ".jpg"), os.path.join(IMG_DIR, code + ".none")
    if os.path.exists(path):
        return open(path, "rb").read()
    if os.path.exists(miss) and time.time() - os.path.getmtime(miss) < 14 * 86400:
        return None
    data = None
    try:
        r = requests.get(f"https://world.openfoodfacts.org/api/v2/product/{code}",
                         params={"fields": "image_front_small_url,image_small_url"},
                         headers={"User-Agent": USER_AGENT}, timeout=8)
        prod = r.json().get("product") or {} if r.ok else {}
        url = prod.get("image_front_small_url") or prod.get("image_small_url")
        if url:
            ir = requests.get(url, headers={"User-Agent": USER_AGENT}, timeout=8)
            if ir.ok and ir.content:
                data = ir.content
    except Exception:
        data = None
    if data:
        open(path, "wb").write(data)
    else:
        open(miss, "w").close()
    return data


# ---------------------------------------------------------------- comparison
_price_cache = {}


def _cached(key, fn):
    if key not in _price_cache:
        if len(_price_cache) > 200:
            _price_cache.clear()
        _price_cache[key] = fn()
    return _price_cache[key]


def store_prices(s):
    """Full price file + every hourly update published after it. Returns (items, timestamp)."""
    p = store_file(s, "pricefull")
    if not p:
        return None, None
    base_ts = file_info(p)[3]
    ups = files_after(s, "price", base_ts)

    def build():
        items = dict(_cached(("p", p, os.path.getmtime(p)), lambda: parse_prices(p)))
        for _, up in ups:
            try:
                for code, v in _cached(("p", up, os.path.getmtime(up)), lambda: parse_prices(up)).items():
                    if code in items:
                        # update files often carry only code+price; keep the descriptive fields
                        merged = dict(items[code])
                        merged.update({k: val for k, val in v.items() if val not in ("", None)})
                        merged["weighted"] = items[code]["weighted"] or v["weighted"]
                        items[code] = merged
                    else:
                        items[code] = v
            except Exception as e:
                print("update parse failed", up, e)
        return items

    key = ("merged", p, tuple(u for _, u in ups))
    return _cached(key, build), (ups[-1][0] if ups else base_ts)


def store_promos(s):
    """{item_code: [promo,...]} from the full promo file + later promo updates."""
    p = store_file(s, "promofull")
    base_ts = file_info(p)[3] if p else ""
    ups = files_after(s, "promo", base_ts)
    if not p and not ups:
        return {}

    def build():
        by_id = {}
        for f in ([p] if p else []) + [u for _, u in ups]:
            try:
                by_id.update(_cached(("promo", f, os.path.getmtime(f)), lambda: parse_promos(f)))
            except Exception as e:
                print("promo parse failed", f, e)
        by_code = {}
        for pr in by_id.values():
            for c in pr["codes"]:
                by_code.setdefault(c, []).append(pr)
        return by_code

    return _cached(("promos", p, tuple(u for _, u in ups)), build)


def product_key(store, code):
    # real barcodes are shared across chains; short internal codes are chain-specific
    return code if len(code) >= 8 else f"{store['chain_id'] or store['chain_key']}:{code}"


def build_universe(stores_prices):
    uni = {}
    for s, items in stores_prices:
        for code, it in items.items():
            k = product_key(s, code)
            u = uni.get(k)
            if not u:
                u = uni[k] = {"key": k, "name": it["name"], "manufacturer": it["manufacturer"],
                              "qty": it["qty"], "unit": it["unit"], "weighted": it["weighted"],
                              "stores": 0, "min": it["price"], "max": it["price"],
                              "_tok": set(tokens(it["name"]))}
            u["stores"] += 1
            u["min"] = min(u["min"], it["price"])
            u["max"] = max(u["max"], it["price"])
    return uni


def candidates(item_name, uni, n=30):
    q = tokens(item_name)
    if not q:
        return []
    scored = []
    for u in uni.values():
        t = u["_tok"]
        s = sum(_tok_match(x, t) for x in q) / len(q)
        if s >= 0.5:
            # prefer names where the first query word appears early
            first = norm(u["name"]).find(q[0])
            bonus = 0.05 if first == 0 else 0
            scored.append((s + bonus, u["stores"], u))
    scored.sort(key=lambda x: (-x[0], -x[1], len(x[2]["name"])))
    return [(round(sc, 3), u) for sc, _, u in scored[:n]]


def choose_products(api_key, items, cands):
    """Returns list (per item) of accepted product keys, best first."""
    if not api_key:
        out = []
        for c in cands:
            if not c:
                out.append([])
                continue
            top = c[0][0]
            out.append([u["key"] for sc, u in c if sc >= top - 0.01][:12])
        return out
    lines = []
    for i, (it, c) in enumerate(zip(items, cands)):
        lines.append(f"\n### פריט {i}: \"{it['name']}\" (כמות {it['qty']:g}){' — ' + it['note'] if it.get('note') else ''}"
                     f"{' — הקונה קונה בדרך כלל: ' + it['hint'] if it.get('hint') else ''}")
        for sc, u in c:
            size = f"{u['qty']} {u['unit']}".strip()
            lines.append(f"- key={u['key']} | {u['name']} | {u['manufacturer']} | {size} | "
                         f"{'שקיל' if u['weighted'] else ''} | ₪{u['min']:.2f}-{u['max']:.2f} | ב-{u['stores']} סניפים")
        if not c:
            lines.append("- (אין מועמדים)")
    prompt = (
        "אתה עוזר להשוות מחירי סל קניות בסופרמרקטים בישראל. לכל פריט ברשימה יש רשימת מוצרים מועמדים מקבצי המחירים.\n"
        "לכל פריט בחר את המוצרים שקונה סביר היה מקבל כתחליף שווה ערך לפריט שנכתב:\n"
        "- אם צוין מותג, גודל או אחוז שומן, או מה שהקונה קונה בדרך כלל — שים אותו ראשון ורק מוצרים שתואמים.\n"
        "- אם לא צוין — כלול את המוצרים הנפוצים מאותו סוג ובגודל סטנדרטי דומה (למשל חלב 3% 1 ליטר מכל מותג), "
        "בלי גדלים חריגים, מארזי ענק, מוצרים מעובדים אחרים או מוצרים שרק מכילים את המילה.\n"
        "- סדר מהמתאים ביותר. עד 12 מוצרים. אם אין אף מתאים, רשימה ריקה.\n"
        'החזר JSON בלבד: {"results":[{"item":0,"keys":["..."]}]}\n' + "\n".join(lines))
    js = _json_from(claude(api_key, prompt, max_tokens=6000))
    by = {int(r.get("item", -1)): [str(k) for k in r.get("keys", [])] for r in js.get("results", [])}
    valid = [{u["key"] for _, u in c} for c in cands]
    return [[k for k in by.get(i, []) if k in valid[i]] for i in range(len(items))]


MIN_SHARE = 0.75  # compare against the best store only with at least 75% of its items


def _amounts(it, product_weighted):
    """(amount used for pricing, human text). Weighted products are priced per kg."""
    qty, mode = float(it.get("qty") or 1), it.get("mode") or "units"
    if product_weighted:
        if mode == "kg":
            return qty, f"{qty:g} ק\"ג"
        per = it.get("unit_kg") or (produce_info(it["name"]) or {}).get("unit_kg") or 0.2
        kg = round(qty * per, 3)
        return kg, f"{qty:g} {it.get('unit_label') or 'יח'} ≈ {kg:g} ק\"ג"
    if mode == "kg":
        n = max(1.0, float(round(qty)))
        return n, f"{n:g} אריזות"
    return qty, f"{qty:g}"


def compare(items, use_ai=True):
    cfg = load_config()
    items = normalize_items(items)
    if not items:
        raise RuntimeError("הרשימה ריקה")
    prefs = load_prefs()
    nearby = load_json(NEARBY_PATH, [])
    if not nearby:
        raise RuntimeError("אין סניפים קרובים שמורים. לחץ קודם 'עדכן מחירים'.")
    sp, dates = [], {}
    for s in nearby:
        items_map, stamp = store_prices(s)
        if items_map:
            sp.append((s, items_map))
            dates[(s["chain_key"], s.get("chain_id"), s["store_id"])] = stamp
    if not sp:
        raise RuntimeError("אין קובצי מחירים לסניפים הקרובים. לחץ 'עדכן מחירים'.")
    uni = build_universe(sp)
    cands = []
    for it in items:
        c = candidates(it["name"], uni)
        if it.get("hint"):  # a saved/photographed product: search its description too
            seen = {u["key"] for _, u in c}
            c += [(sc, u) for sc, u in candidates(it["hint"], uni, n=15) if u["key"] not in seen]
        cands.append(c)
    ai_error = None
    key = cfg.get("api_key") if use_ai else ""
    try:
        accepted = choose_products(key, items, cands)
    except Exception as e:  # bad key / no internet / quota: fall back to word matching
        ai_error = str(e)[:200]
        key = ""
        accepted = choose_products("", items, cands)
    # saved favourite product (⭐ on a result line): preferred, others only as a substitute
    preferred = []
    for it in items:
        p = prefs.get(pref_key(it["name"])) or {}
        preferred.append([k for k in p.get("keys", []) if k in uni])

    include_club = bool(cfg.get("include_club"))
    now = _israel_today()
    rows = []
    for idx_s, (s, prices) in enumerate(sp):
        lookup = {product_key(s, c): v for c, v in prices.items()}
        promos = store_promos(s)
        total, found, lines, missing, saved = 0.0, 0, [], [], 0.0
        for it, acc, pref in zip(items, accepted, preferred):
            best = None  # (cost, unit_price, product, promo, amount_text, key)
            for group, is_sub in ((pref, False), ([k for k in acc if k not in pref], bool(pref))):
                for k in group:
                    v = lookup.get(k)
                    if not v:
                        continue
                    amount, amount_txt = _amounts(it, v["weighted"])
                    unit, used = v["price"], None
                    for pr in promos.get(v["code"], []):
                        if pr["club"] and not include_club:
                            continue
                        if (pr["start"] and pr["start"] > now) or (pr["end"] and pr["end"] < now):
                            continue
                        u = promo_unit_price(pr, v["price"], amount)
                        if u is not None and u < unit:
                            unit, used = u, pr
                    cost = unit * amount
                    if best is None or cost < best[0]:
                        best = (cost, unit, v, used, amount_txt, k, is_sub)
                if best:
                    break  # found the preferred product here: don't look at substitutes
            if best:
                cost, unit, v, pr, amount_txt, k, is_sub = best
                total += cost
                saved += (v["price"] - unit) * (cost / unit if unit else 0)
                found += 1
                lines.append({"item": it["name"], "emoji": it["emoji"], "product": v["name"],
                              "manufacturer": v["manufacturer"], "code": v["code"], "key": k,
                              "price": round(unit, 2), "regular": v["price"], "qty": it["qty"],
                              "amount": amount_txt, "cost": round(cost, 2), "weighted": v["weighted"],
                              "substitute": is_sub, "is_pref": k in pref,
                              "promo": (pr["desc"] or "מבצע") + (" (מועדון)" if pr["club"] else "") if pr else None})
            else:
                missing.append(it["name"])
                lines.append({"item": it["name"], "emoji": it["emoji"], "product": None})
        st = dates.get((s["chain_key"], s.get("chain_id"), s["store_id"]), "")
        rows.append({
            "id": f"st{idx_s}", "chain_key": s["chain_key"], "chain_id": s.get("chain_id"),
            "store_id": s["store_id"], "chain": s["chain_name"], "sub_chain": s.get("sub_chain", ""),
            "store": s["name"],
            "address": f"{s['address']} {s['city'] if not str(s['city']).isdigit() else ''}".strip(),
            "distance_km": s["distance_km"], "lat": s["lat"], "lon": s["lon"],
            "drive_min": s.get("drive_min", estimate_drive_min(s["distance_km"])),
            "drive_estimated": s.get("drive_estimated", True),
            "total": round(total, 2), "found": found, "n": len(items), "missing": missing, "lines": lines,
            "saved": round(saved, 2), "has_promos": bool(promos),
            "prices_from": f"{st[6:8]}/{st[4:6]} {st[8:10]}:{st[10:12]}" if len(st) >= 12 else st,
        })

    max_drive = float(cfg.get("max_drive_min") or 25)
    worth_min = float(cfg.get("worth_min") or 30)
    worth_save = float(cfg.get("worth_save") or 50)
    for r in rows:
        r["in_range"] = r["drive_min"] <= max_drive
        r["over_by"] = max(0, round(r["drive_min"] - max_drive))
    rows.sort(key=lambda r: (not r["in_range"], -r["found"], r["total"], r["drive_min"]))
    near = [r for r in rows if r["in_range"]]

    def vs(a, b):
        """Compare two stores on the items both have: (n, a_cost, b_cost)."""
        both = [i for i in range(len(items)) if a["lines"][i].get("product") and b["lines"][i].get("product")]
        return len(both), round(sum(a["lines"][i]["cost"] for i in both), 2), round(sum(b["lines"][i]["cost"] for i in both), 2)

    def brief(r):
        return None if not r else {k: r[k] for k in ("id", "chain_key", "chain", "store", "total", "found", "n",
                                                       "missing", "drive_min", "saved")}

    best_complete = near[0] if near else None
    if best_complete:
        best_complete["recommended"] = True
    # a store is comparable to the best only if it has at least 75% of the items the best one has
    need = int(math.ceil(MIN_SHARE * best_complete["found"])) if best_complete else 0

    far = []
    if best_complete:
        for r in rows:
            if r is best_complete:
                continue
            n, here, there = vs(r, best_complete)
            if n:
                r["vs_top"] = {"n": n, "here": here, "top": there}
            if not r["in_range"] and n >= need and there - here > 0:
                save = round(there - here, 2)
                not_worth = save > worth_save and r["drive_min"] >= worth_min
                r["verdict"] = (f"חוסך {save:.0f} ₪ על {n}/{len(items)} מוצרים, אבל ~{r['drive_min']} דק' נסיעה "
                                f"({r['over_by']} דק' מעבר לטווח). "
                                + (f"לפי הכלל שלך ({worth_min:.0f} דק' ומעלה) לא שווה לנסוע" if not_worth
                                   else "מחוץ לטווח הנסיעה שהגדרת"))
                far.append({"id": r["id"], "chain_key": r["chain_key"], "chain": r["chain"], "store": r["store"],
                            "save": save, "n": n, "of": len(items), "drive_min": r["drive_min"],
                            "over_by": r["over_by"], "not_worth": not_worth})
    far.sort(key=lambda x: -x["save"])
    far = far[:2]

    # my regular stores vs the best, on exactly the same items
    fav_rows = []
    for i, st_ in match_favorites(cfg, rows).items():
        st_["favorite"] = (cfg["favorites"][i].get("label") or st_["store"])
        st_["fav_index"] = i
        fav_rows.append(st_)
    fav = []
    for r in fav_rows:
        d = {"n": 0, "ok": False}
        if best_complete and r is not best_complete:
            n, here, there = vs(r, best_complete)
            d = {"n": n, "of": len(items), "here": here, "top": there, "diff": round(here - there, 2),
                 "ok": n >= need}
        fav.append(dict(brief(r), label=r["favorite"], vs_best=d, is_best=r is best_complete))
    fav.sort(key=lambda f: (not f["is_best"], not f["vs_best"].get("ok"), f["vs_best"].get("diff", 0)))
    missing_favs = [f.get("label") for i, f in enumerate(cfg.get("favorites") or [])
                    if i not in {r.get("fav_index") for r in fav_rows}]

    # cards: top 5 in range; far ones and favourites are kept separately so links can jump to them
    top5 = near[:5]
    top_ids = {r["id"] for r in top5}
    far_ids = {f["id"] for f in far}
    more, seen = [], set(top_ids)
    for r in [r for r in rows if r["id"] in far_ids] + fav_rows:
        if r["id"] not in seen:
            seen.add(r["id"])
            more.append(r)

    split = []
    for idx, it in enumerate(items):
        b = None
        for r in (near or rows):
            ln = r["lines"][idx]
            if ln.get("product") and (b is None or ln["cost"] < b[1]["cost"]):
                b = (r, ln)
        if b:
            split.append({"item": it["name"], "store": f"{b[0]['chain']} {b[0]['store']}",
                          "product": b[1]["product"], "cost": b[1]["cost"]})
    matched = []
    for it, acc in zip(items, accepted):
        names = [uni[k]["name"] for k in acc[:4] if k in uni]
        matched.append({"item": it["name"], "matches": names, "n": len(acc)})
    return {"stores": top5, "more": more, "items": items, "max_drive": max_drive,
            "best_complete": brief(best_complete), "need": need, "min_share": MIN_SHARE,
            "favorites": fav, "missing_favorites": missing_favs, "far": far,
            "no_near": not near,
            "split": split, "split_total": round(sum(x["cost"] for x in split), 2),
            "matched": matched, "used_ai": bool(key), "ai_error": ai_error}
