# -*- coding: utf-8 -*-
"""
Builds a compact price file for the phone app (the Claude page).

  python build_data.py --group github   # chains reachable from abroad (runs on GitHub every morning)
  python build_data.py --group mac      # chains that block access from abroad (runs on the Mac)

Output: out/prices_<group>.json  (stores near home, their products, today's prices and simple promos)
"""
import argparse
import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import core  # noqa: E402

# chains whose sites answer from outside Israel (checked weekly by the scraper project)
GROUPS = {
    "github": ["SHUFERSAL", "RAMI_LEVY", "OSHER_AD", "YOHANANOF", "SUPER_YUDA"],
    "mac": ["YAYNO_BITAN_AND_CARREFOUR", "HAZI_HINAM", "VICTORY_NEW_SOURCE"],
}
OUT = os.path.join(core.BASE, "out")


def active_promos(promos, regular, now):
    """Keep only promos the phone can price safely: [desc, min_qty, price, rate, club]."""
    out = []
    for pr in promos:
        if pr["coupon"] or pr["total"] or pr["min_purchase"] > 0:
            continue
        if (pr["start"] and pr["start"] > now) or (pr["end"] and pr["end"] < now):
            continue
        q = max(pr["min_qty"], 1.0) if pr["min_qty"] >= 1 else pr["min_qty"]
        if core.promo_unit_price(pr, regular, max(q, 1.0)) is None:
            continue
        out.append([pr["desc"][:60], round(q, 2), pr["price"], pr["rate"], 1 if pr["club"] else 0])
    # one general + one club promo is enough
    gen = [p for p in out if not p[4]][:1]
    club = [p for p in out if p[4]][:1]
    return gen + club


def export(nearby, chains, path):
    now = core._israel_today()
    stores, plist, pindex, prices = [], [], {}, {}
    for s in nearby:
        if s["chain_key"] not in chains:
            continue
        items, stamp = core.store_prices(s)
        if not items:
            continue
        promos = core.store_promos(s)
        sid = f"{s['chain_key']}:{s.get('chain_id')}:{s['store_id']}"
        rows = []
        for code, v in items.items():
            k = core.product_key(s, code)
            if k not in pindex:
                pindex[k] = len(plist)
                size = f"{v['qty']} {v['unit']}".strip()
                plist.append([k, v["name"][:80], (v["manufacturer"] or "")[:30], size[:20], 1 if v["weighted"] else 0])
            row = [pindex[k], round(v["price"], 2)]
            pr = active_promos(promos.get(code, []), v["price"], now) if promos else []
            if pr:
                row.append(pr)
            rows.append(row)
        prices[sid] = rows
        stores.append({
            "id": sid, "chain_key": s["chain_key"], "chain_id": s.get("chain_id"), "store_id": s["store_id"],
            "chain": s["chain_name"], "sub_chain": s.get("sub_chain", ""), "name": s["name"],
            "address": f"{s['address']} {s['city'] if not str(s['city']).isdigit() else ''}".strip(),
            "lat": s["lat"], "lon": s["lon"], "distance_km": s["distance_km"],
            "drive_min": s.get("drive_min"), "drive_estimated": s.get("drive_estimated", True),
            "prices_from": stamp,
        })
    cfg = core.load_config()
    fav = core.match_favorites(cfg, [x for x in nearby if x["chain_key"] in chains])
    labels = {f"{x['chain_key']}:{x.get('chain_id')}:{x['store_id']}": cfg["favorites"][i].get("label")
              for i, x in fav.items()}
    for st in stores:
        if st["id"] in labels:
            st["favorite"] = labels[st["id"]]
    data = {"generated": time.strftime("%Y-%m-%d %H:%M"), "chains": chains,
            "home": {k: cfg.get("home", {}).get(k) for k in ("lat", "lon", "label")} if cfg.get("home") else None,
            "max_drive_min": cfg.get("max_drive_min", 25), "stores": stores, "products": plist, "prices": prices}
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, separators=(",", ":"))
    return len(stores), len(plist), os.path.getsize(path)


class Printer:
    def say(self, msg):
        print(msg, flush=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--group", choices=GROUPS, required=True)
    ap.add_argument("--no-download", action="store_true", help="only export what is already on disk")
    a = ap.parse_args()
    chains = GROUPS[a.group]
    job = Printer()
    cfg = core.load_config()
    if not a.no_download:
        cfg["chains"] = chains
        core.download_store_files(job, chains)
        nearby = core.find_nearby_stores(job, cfg)
        if not nearby:
            print("no stores found nearby", flush=True)
            sys.exit(1)
        core.download_price_files(job, nearby, force=True)
    else:
        nearby = [s for s in core.load_json(core.NEARBY_PATH, []) if s["chain_key"] in chains]
    n, p, size = export(nearby, chains, os.path.join(OUT, f"prices_{a.group}.json"))
    print(f"exported {n} stores, {p} products, {size / 1e6:.1f} MB", flush=True)


if __name__ == "__main__":
    main()
