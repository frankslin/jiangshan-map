#!/usr/bin/env python3
"""
Align the atlas prefecture polygons (geojson/snapshots) with the CBDB
ADDRESSES table and report where names, positions or parent circuits disagree.

CBDB data is CC BY-NC-SA 4.0 and is NOT bundled here: download the SQLite
release, build ADDRESSES with CBDB's own scripts/create_addresses_table.py
(https://github.com/cbdb-project/cbdb_sqlite), then run:

    pip install opencc-python-reimplemented
    python3 scripts/align_cbdb.py --db latest.db --out cbdb_align/

For each snapshot covering 600–1911 CE (CBDB place coverage starts with
Sui/Tang and its prefecture units end with the Qing), the phase's middle year is used. A CBDB prefecture-level unit is
represented by its seat plus the seats of the counties it governs that year;
those points are tested against each atlas prefecture polygon.

Outputs:
  crosswalk.csv    one row per atlas prefecture feature and snapshot
  unmatched.csv    CBDB prefecture-level units with no atlas polygon of that name
  issues.geojson   CBDB seats behind every non-ok row, for viewing in demo.html
  summary.md       counts per dynasty and the most frequent problems
"""
import argparse
import csv
import json
import math
import os
import re
import sqlite3
import sys
from collections import Counter, defaultdict

try:
    from opencc import OpenCC
except ImportError:
    sys.exit('Needs opencc for traditional -> simplified names: pip install opencc-python-reimplemented')

T2S = OpenCC('t2s').convert
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# CBDB c_admin_type values treated as prefecture level (when not nested under
# another prefecture-level unit) and as circuit/province level.
PREF_TYPES = {
    'Zhou', 'Fu', 'Jun', 'Jun Commandery', 'Zhilizhou', 'Zhiliting', 'Jimizhou',
    'Junminfu', 'Ting', 'Junmin fu', 'Junminzhou',
}
PROVINCE_TYPES = {'Sheng', 'sheng', 'Xingsheng', 'Xingzhongshusheng', 'xingzhongshusheng'}
# Song/Jin 路 are circuits; Yuan 路 sit under a (xing) zhongshu sheng and are prefecture level.
REGION_TYPES = {'Lu', 'Dao', 'Buzhengsi', 'Zhili'} | PROVINCE_TYPES
COUNTY_TYPES = {'Xian', 'xian', 'County'}
SUFFIX = re.compile(r'(行中书省|中书省|行省|直隶州|直隶厅|军民府|都督府|州|府|郡|军|厅|路|道|监)$')
VARIANTS = str.maketrans({'礠': '磁', '颍': '颖', '辩': '辨', '乾': '干', '兖': '兗'})
DIRECTION = re.compile(r'[东西南北]')
FIRST_YEAR, LAST_YEAR = 600, 1911  # CBDB has no prefecture-level units after the Qing
HOMONYM_KM = 250  # a same-named CBDB seat farther than this from the polygon is another place


def norm(name):
    """Compare names in one script: OpenCC t2s plus common variant characters."""
    return T2S(name or '').translate(VARIANTS)


def stem(name):
    while True:
        s = SUFFIX.sub('', name)
        if not s or s == name:
            return name
        name = s


def region_relation(atlas, cbdb):
    """'ok', 'subdivision' (e.g. 江南西道 within CBDB's 江南道, 淮南西路 vs 淮南路) or 'mismatch'."""
    a, c = stem(atlas), stem(cbdb)
    if a == c or a in cbdb or c in atlas:
        return 'ok'
    if DIRECTION.sub('', a) == DIRECTION.sub('', c):
        return 'subdivision'
    return 'mismatch'


# ---------- geometry ----------

def in_ring(x, y, ring):
    inside = False
    j = len(ring) - 1
    for i in range(len(ring)):
        xi, yi = ring[i]
        xj, yj = ring[j]
        if (yi > y) != (yj > y) and x < (xj - xi) * (y - yi) / (yj - yi) + xi:
            inside = not inside
        j = i
    return inside


def in_polygon(x, y, rings):
    return in_ring(x, y, rings[0]) and not any(in_ring(x, y, h) for h in rings[1:])


def contains(feature, x, y):
    b = feature['bbox']
    if x < b[0] or y < b[1] or x > b[2] or y > b[3]:
        return False
    g = feature['geometry']
    if g['type'] == 'Polygon':
        return in_polygon(x, y, g['coordinates'])
    return any(in_polygon(x, y, p) for p in g['coordinates'])


def km(a, b):
    lat = math.radians((a[1] + b[1]) / 2)
    dx = (a[0] - b[0]) * 111.32 * math.cos(lat)
    dy = (a[1] - b[1]) * 110.57
    return round(math.hypot(dx, dy))


# ---------- CBDB ----------

def load_cbdb(db):
    con = sqlite3.connect(db)
    if not con.execute("select 1 from sqlite_master where name='ADDRESSES'").fetchone():
        sys.exit('ADDRESSES table missing: run CBDB scripts/create_addresses_table.py --db <db> first')
    types = dict(con.execute('select c_addr_id, c_admin_type from ADDR_CODES'))
    rows = []
    for r in con.execute(
        '''select c_addr_id, c_name_chn, c_admin_type, c_firstyear, c_lastyear,
                  coalesce(c_belongs_firstyear, c_firstyear), coalesce(c_belongs_lastyear, c_lastyear),
                  x_coord, y_coord,
                  belongs1_ID, belongs1_Name_chn, belongs2_ID, belongs2_Name_chn,
                  belongs3_ID, belongs3_Name_chn
           from ADDRESSES where c_name_chn is not null'''
    ):
        x, y = r[7], r[8]
        rows.append({
            'id': r[0], 'name': norm(r[1]), 'type': r[2], 'first': r[3] or -9999, 'last': r[4] or 9999,
            'bfirst': r[5] or -9999, 'blast': r[6] or 9999,
            'pt': (x, y) if x and y and 70 < x < 140 and 15 < y < 55 else None,
            'parents': [(r[i], norm(r[i + 1])) for i in (9, 11, 13) if r[i]],
        })
    # Every span a unit existed under a given name, to explain renamings.
    spans = defaultdict(list)
    for r in con.execute('select c_addr_id, c_name_chn, c_firstyear, c_lastyear, x_coord, y_coord, c_admin_type from ADDR_CODES'):
        if r[1] and r[4] and r[5]:
            spans[norm(r[1])].append((r[2], r[3], (r[4], r[5]), r[0], r[6]))
    return rows, types, spans


def units_at(rows, types, year):
    """Prefecture-level CBDB units active in `year`, with seat and county points."""
    active = [r for r in rows if r['first'] <= year <= r['last'] and r['bfirst'] <= year <= r['blast']]
    by_id = {}
    for r in active:
        by_id.setdefault(r['id'], r)
    def pref_level(t, parent_t):
        return t in PREF_TYPES or (t == 'Lu' and parent_t in PROVINCE_TYPES)

    def chain(r):
        """[(id, name, type, is_prefecture_level)] from the unit's parent upwards."""
        ps = r['parents']
        out = []
        for i, (pid, n) in enumerate(ps):
            t = types.get(pid)
            up = types.get(ps[i + 1][0]) if i + 1 < len(ps) else None
            out.append((pid, n, t, pref_level(t, up)))
        return out

    prefs = {}
    for r in by_id.values():
        c = chain(r)
        if not pref_level(r['type'], c[0][2] if c else None):
            continue
        if c and c[0][3]:
            continue  # sub-prefecture unit: zhou/ting under a fu, zhou under a Yuan lu
        region = next(
            (n for _, n, t, is_pref in c
             if t in REGION_TYPES and not is_pref and not (t == 'Dao' and year > 907)),  # Tang dao lapse after 907
            '',
        )
        prefs[r['id']] = {**r, 'region': region, 'counties': []}
    for r in by_id.values():
        if r['type'] in COUNTY_TYPES and r['pt']:
            owner = next((pid for pid, *_ in chain(r) if pid in prefs), None)
            if owner:
                prefs[owner]['counties'].append(r['pt'])
    return prefs


# ---------- alignment ----------

def align(snapshot, year, prefs, spans):
    feats = [f for f in snapshot['features'] if f['properties']['layer'] == 'prefecture']
    regions = [f for f in snapshot['features'] if f['properties']['layer'] == 'region']
    if not feats:
        return [], [], []

    def where(pt, pool):
        return next((f for f in pool if contains(f, *pt)), None)

    # Atlas prefecture containing each CBDB seat / county, computed once per unit.
    loc = {}
    for pid, p in prefs.items():
        seat = where(p['pt'], feats) if p['pt'] else None
        counties = Counter(id(f) for f in (where(c, feats) for c in p['counties']) if f)
        loc[pid] = (seat, counties)

    by_name = defaultdict(list)
    by_stem = defaultdict(list)
    for pid, p in prefs.items():
        by_name[p['name']].append(pid)
        by_stem[stem(p['name'])].append(pid)

    rows, issues = [], []
    matched = set()
    for f in feats:
        props = f['properties']
        title = norm(props['title'])
        cands = by_name.get(title) or by_stem.get(stem(title)) or []

        def score(pid):
            seat, counties = loc[pid]
            total = len(prefs[pid]['counties'])
            inside = counties.get(id(f), 0)
            return (seat is f) * 2 + (inside / total if total else 0), inside, total

        row = {'title': props['title'], 'category': props.get('category', '')}
        # Drop homonyms: same name, but a different place far away.
        cands = [pid for pid in cands if not prefs[pid]['pt'] or loc[pid][0] is f or distance_to(f, prefs[pid]['pt']) <= HOMONYM_KM]
        best = max(
            cands,
            key=lambda pid: (score(pid)[0], -(distance_to(f, prefs[pid]['pt']) if prefs[pid]['pt'] else 0)),
            default=None,
        )
        if best is not None:
            p = prefs[best]
            seat, _ = loc[best]
            s, inside, total = score(best)
            matched.add(best)
            row.update(cbdb_id=best, cbdb_name=p['name'], cbdb_type=p['type'], counties_inside=inside, counties_total=total)
            if seat is f or (seat and norm(seat['properties']['title']) == title) or (not p['pt'] and total and inside / total >= 0.5):
                row['status'] = 'ok'
            elif not p['pt'] and not total:
                row['status'] = 'no_coords'  # name matches, but CBDB has no seat or county coordinates
            elif p['pt']:
                row['status'] = 'seat_outside'
                row['note'] = f"治所落在{seat['properties']['title'] if seat else '无州郡多边形处'}，距多边形约 {distance_to(f, p['pt'])} km"
            else:
                row['status'] = 'counties_outside'
                row['note'] = f'属县仅 {inside}/{total} 落在多边形内'
            # Parent circuit / province check.
            if p['pt'] and p['region']:
                reg = where(p['pt'], regions)
                atlas_region = reg['properties']['title'] if reg else ''
                row['region_atlas'], row['region_cbdb'] = atlas_region, p['region']
                if atlas_region:
                    row['region_status'] = region_relation(norm(atlas_region), p['region'])
        else:
            # No CBDB unit of this name this year: which CBDB unit occupies the polygon?
            occupant = max(
                prefs,
                key=lambda pid: (loc[pid][0] is f) * 2 + (loc[pid][1].get(id(f), 0) / max(1, len(prefs[pid]['counties']))),
                default=None,
            )
            occ_ok = occupant is not None and (loc[occupant][0] is f or loc[occupant][1].get(id(f), 0) * 2 >= max(1, len(prefs[occupant]['counties'])) > 0)
            if occ_ok:
                p = prefs[occupant]
                matched.add(occupant)
                row.update(status='ok' if p['name'] == title or stem(p['name']) == stem(title) else 'renamed', cbdb_id=occupant, cbdb_name=p['name'], cbdb_type=p['type'])
                other = [s for s in spans.get(title, []) if not (s[0] or -9999) <= year <= (s[1] or 9999)]
                near = [s for s in other if km(s[2], p['pt'] or s[2]) < 60]
                row['note'] = (
                    f"CBDB {year} 年此地为{p['name']}；“{title}”在 CBDB 中的年份为 "
                    + '、'.join(f'{s[0]}–{s[1]}' for s in near[:3])
                    if near
                    else f"CBDB {year} 年此地为{p['name']}，附近无同名 CBDB 单位"
                )
            else:
                row['status'] = 'no_cbdb'
        rows.append(row)
        if row['status'] != 'ok' or row.get('region_status') == 'mismatch':
            pid = row.get('cbdb_id')
            pt = prefs[pid]['pt'] if pid else None
            issues.append({
                'type': 'Feature',
                'properties': {k: v for k, v in row.items() if k != 'category'},
                'geometry': {'type': 'Point', 'coordinates': list(pt)} if pt else None,
            })
    unmatched = [
        {'cbdb_id': pid, 'cbdb_name': p['name'], 'cbdb_type': p['type'], 'region_cbdb': p['region'],
         'atlas_at_seat': (loc[pid][0]['properties']['title'] if loc[pid][0] else '')}
        for pid, p in prefs.items()
        if pid not in matched and p['pt']
    ]
    return rows, issues, unmatched


def distance_to(feature, pt):
    g = feature['geometry']
    polys = [g['coordinates']] if g['type'] == 'Polygon' else g['coordinates']
    return min(km(pt, v) for poly in polys for v in poly[0])


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--db', required=True, help='CBDB SQLite file with the ADDRESSES table')
    ap.add_argument('--geojson', default=os.path.join(ROOT, 'geojson'))
    ap.add_argument('--out', default='cbdb_align')
    a = ap.parse_args()

    rows_db, types, spans = load_cbdb(a.db)
    index = json.load(open(os.path.join(a.geojson, 'index.json'), encoding='utf-8'))
    os.makedirs(a.out, exist_ok=True)

    cross, issues, unmatched = [], [], []
    for d in index['dynasties']:
        for ph in d['phases']:
            if ph['to'] < FIRST_YEAR or ph['from'] > LAST_YEAR:
                continue
            year = (max(ph['from'], FIRST_YEAR) + min(ph['to'], LAST_YEAR)) // 2
            snap = json.load(open(os.path.join(a.geojson, ph['file']), encoding='utf-8'))
            prefs = units_at(rows_db, types, year)
            r, i, u = align(snap, year, prefs, spans)
            base = {'dynasty': d['key'], 'snapshot': ph['snapshot'], 'from': ph['from'], 'to': ph['to'], 'year': year}
            cross += [{**base, **x} for x in r]
            for x in i:
                x['properties'] = {**base, **x['properties']}
            issues += [x for x in i if x['geometry']]
            unmatched += [{**base, **x} for x in u]
            print(f"{ph['snapshot']:<16} {year:>5}  prefectures {len(r):>4}  CBDB units {len(prefs):>4}", file=sys.stderr)

    cols = ['dynasty', 'snapshot', 'from', 'to', 'year', 'title', 'category', 'status', 'cbdb_id', 'cbdb_name', 'cbdb_type',
            'counties_inside', 'counties_total', 'region_atlas', 'region_cbdb', 'region_status', 'note']
    write_csv(os.path.join(a.out, 'crosswalk.csv'), cols, cross)
    write_csv(os.path.join(a.out, 'unmatched.csv'),
              ['dynasty', 'snapshot', 'from', 'to', 'year', 'cbdb_id', 'cbdb_name', 'cbdb_type', 'region_cbdb', 'atlas_at_seat'], unmatched)
    with open(os.path.join(a.out, 'issues.geojson'), 'w', encoding='utf-8') as fh:
        json.dump({'type': 'FeatureCollection', 'license': 'Derived from CBDB (CC BY-NC-SA 4.0)', 'features': issues}, fh, ensure_ascii=False)
    write_summary(os.path.join(a.out, 'summary.md'), cross, unmatched)
    print(f'Wrote {len(cross)} crosswalk rows, {len(issues)} issue points to {a.out}/', file=sys.stderr)


def write_csv(path, cols, rows):
    with open(path, 'w', newline='', encoding='utf-8-sig') as fh:
        w = csv.DictWriter(fh, cols, extrasaction='ignore')
        w.writeheader()
        w.writerows(rows)


def write_summary(path, cross, unmatched):
    by_dyn = defaultdict(Counter)
    region = defaultdict(Counter)  # ok / subdivision / mismatch
    for r in cross:
        by_dyn[r['dynasty']][r['status']] += 1
        if r.get('region_status'):
            region[r['dynasty']][r['region_status']] += 1
    statuses = ['ok', 'no_coords', 'renamed', 'seat_outside', 'counties_outside', 'no_cbdb']
    lines = ['# Atlas × CBDB ADDRESSES alignment', '',
             'One row per atlas prefecture polygon per snapshot (600–1911 CE; each snapshot evaluated at its middle year).', '',
             '| dynasty | ' + ' | '.join(statuses) + ' | region ok | region subdivision | region mismatch | CBDB units without atlas name |',
             '|' + '---|' * (len(statuses) + 5)]
    miss = Counter(u['dynasty'] for u in unmatched)
    for dyn in dict.fromkeys(r['dynasty'] for r in cross):
        c = by_dyn[dyn]
        lines.append(f'| {dyn} | ' + ' | '.join(str(c[s]) for s in statuses)
                     + f" | {region[dyn]['ok']} | {region[dyn]['subdivision']} | {region[dyn]['mismatch']} | {miss[dyn]} |")
    tot = Counter(r['status'] for r in cross)
    lines += ['', '**Total:** ' + ', '.join(f'{s} {tot[s]}' for s in statuses), '']

    def top(title, rows, key, n=25):
        cnt = Counter(key(r) for r in rows)
        lines.extend([f'## {title}', ''] + [f'- {k} ×{v}' for k, v in cnt.most_common(n)] + [''])

    top('Most frequent renamings (atlas name → CBDB name at that year)',
        [r for r in cross if r['status'] == 'renamed'], lambda r: f"{r['dynasty']}: {r['title']} → {r['cbdb_name']}")
    top('Seats outside the same-named polygon',
        [r for r in cross if r['status'] == 'seat_outside'], lambda r: f"{r['dynasty']}: {r['title']}（{r.get('note', '')}）")
    top('Parent circuit/province mismatches (atlas → CBDB)',
        [r for r in cross if r.get('region_status') == 'mismatch'],
        lambda r: f"{r['dynasty']}: {r['title']} 在 {r['region_atlas']}，CBDB 属 {r['region_cbdb']}")
    with open(path, 'w', encoding='utf-8') as fh:
        fh.write('\n'.join(lines))


if __name__ == '__main__':
    main()
