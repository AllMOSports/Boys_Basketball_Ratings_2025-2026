"""
All MO Sports - travel-limited playoff bracket optimizer (football and boys basketball).

For each class it:
  1. Geocodes every school (U.S. Census batch geocoder; ZIP-center fallback).
  2. Pulls a full drive-time table from OSRM (chunked, so 100+ team classes work).
  3. Seeds teams by Overall Rating + head-to-head jump rule.
  4. Groups teams into districts so that EVERY possible matchup meets the
     travel limits, or, where that's impossible, breaks as few limits as
     possible and reports each one.
  5. Places teams on the bracket: top seeds get byes, the rest play best-vs-worst.

Bracket size
  * 64 lines / 8 districts when a class has <= 64 teams:
      District QF, District SF, District Final, Quarterfinal, Semifinal, Championship
  * 128 lines / 16 districts when a class has 65-128 teams (basketball Classes 1-4):
      District QF, District SF, District Final, Sectional, Quarterfinal, Semifinal, Championship

Travel limits (every possible matchup)
  * any two teams in the same district <= --district-limit (default 3.0 h)
  * any two teams in districts that meet in the first round after districts
    (Quarterfinal for 8 districts, Sectional for 16) <= --next-limit (default 4.0 h)
  * no limit after that

Seeds
  * Sort by ovr_rating. Then, working from the top seed down, a team within 5
    spots below that beat a team head-to-head jumps directly above it. A team
    can jump at most once. --no-jumps turns this off.

Byes
  * statewide: seeds 1..(lines - teams) get first-round byes.
  * district:  each district's top seeds get that district's byes
               (far fewer travel violations).

Sports (--sport)
  football        ratings football_ratings_2026.json
                  games   football_games_2026_all.json
                  addresses football_school_addresses.csv
                  output  playoff_brackets/
  boys_basketball ratings mo-data/output/mshsaa_historical_records/boys_basketball/
                          Boys_Basketball_Ratings_History_2012-2025.json  (season --season, default latest)
                  games   mo-data/output/boys_basketball_schedule_2025-2026.json
                  addresses basketball_school_addresses.csv
                  output  playoff_brackets_boys_basketball/
  (mo-data/ is a checkout of AllMOSports/All_MO_Sports-Data; the workflow does this.)
  --ratings / --games / --addresses / --season override the defaults.

Head-to-head games
  --games-through YYYY-MM-DD ignores later games (use it to leave out postseason results).

Other files
  coord_overrides.json (optional) {"Team": [lat, lon]}
  school_coords.json            geocode cache, shared across sports, keyed by team + address
  drive_times/<prefix>class_N.json  drive-time cache (seconds)

Usage
  python playoff_bracket_optimizer.py --sport football --classes 1,2,3,4,5,6 --bye-rule district
  python playoff_bracket_optimizer.py --sport boys_basketball --classes 1,2,3,4,5,6 --bye-rule district
  --factor scales OSRM drive times before checking limits (e.g. 0.85 if OSRM
  runs slow vs. real-world times). Set OSRM_URL to use your own OSRM server.
"""
import argparse, csv, io, itertools, json, math, os, sys, time

import requests
from ortools.sat.python import cp_model

OSRM_URL = os.environ.get('OSRM_URL', 'https://router.project-osrm.org').rstrip('/')
CENSUS_BATCH = 'https://geocoding.geo.census.gov/geocoder/locations/addressbatch'
OSRM_CHUNK = 50  # teams per side of each OSRM table request (<=100 points per request)

SPORTS = {
    'football': {
        'label': 'Football',
        'ratings': 'football_ratings_2026.json',
        'games': 'football_games_2026_all.json',
        'addresses': 'football_school_addresses.csv',
        'out_dir': 'playoff_brackets',
        'cache_prefix': '',
    },
    'boys_basketball': {
        'label': 'Boys Basketball',
        'ratings': 'mo-data/output/mshsaa_historical_records/boys_basketball/Boys_Basketball_Ratings_History_2012-2025.json',
        'games': 'mo-data/output/boys_basketball_schedule_2025-2026.json',
        'addresses': 'basketball_school_addresses.csv',
        'out_dir': 'playoff_brackets_boys_basketball',
        'cache_prefix': 'boys_basketball_',
    },
}


def log(*a):
    print(*a, flush=True)


# --------------------------------------------------------------------------- data
def load_json(p, default=None):
    if os.path.exists(p):
        with open(p) as f:
            return json.load(f)
    return default


def save_json(p, obj):
    os.makedirs(os.path.dirname(p) or '.', exist_ok=True)
    with open(p, 'w') as f:
        json.dump(obj, f, indent=1)


def load_addresses(path):
    with open(path, newline='') as f:
        return {r['team']: r for r in csv.DictReader(f)}


def load_ratings(path, season=None):
    """Accepts {'teams': [...]} or a history file {'seasons': [{'year':..,'teams':[...]}, ...]}."""
    js = load_json(path)
    if js is None:
        sys.exit(f'Ratings file not found: {path}')
    if 'teams' in js:
        return js['teams'], None
    seasons = js['seasons']
    if season is None:
        s = max(seasons, key=lambda s: s['year'])
    else:
        hits = [s for s in seasons if s['year'] == season]
        if not hits:
            sys.exit(f'Season {season} not in {path}; available: {[s["year"] for s in seasons]}')
        s = hits[0]
    return s['teams'], s['year']


def load_games(path):
    """Returns a list of {date, team1, team2, score1, score2, forfeit}.
    Accepts a flat game list (football) or a per-team schedule {'teams': {team: [games]}} (basketball)."""
    js = load_json(path)
    if js is None:
        log(f'Games file not found ({path}); head-to-head jumps will be skipped')
        return []
    if isinstance(js, list):
        return js
    games, seen = [], set()
    for team, sched in js.get('teams', {}).items():
        for g in sched:
            ts, os_ = g.get('team_score'), g.get('opp_score')
            if ts is None or os_ is None:
                continue
            opp = g.get('opponent')
            key = (g.get('date'), *sorted([team, opp]), *sorted([ts, os_]))
            if key in seen:  # same game listed on both teams' schedules
                continue
            seen.add(key)
            games.append({'date': g.get('date'), 'team1': team, 'team2': opp, 'score1': ts, 'score2': os_,
                          'forfeit': bool(g.get('forfeit'))})
    return games


# --------------------------------------------------------------------------- geocoding
def addr_key(a):
    return f"{a['street']}|{a['city']}|{a['zip']}".upper()


def geocode(teams, addresses, cache_path='school_coords.json'):
    cache = load_json(cache_path, {})
    overrides = load_json('coord_overrides.json', {})
    for t, (lat, lon) in overrides.items():
        cache[t] = {'lat': lat, 'lon': lon, 'source': 'override'}

    def ok(t):  # cached entry exists and was made from this same address
        c = cache.get(t)
        return c is not None and (c.get('source') == 'override' or c.get('addr', addr_key(addresses[t])) == addr_key(addresses[t]))

    need = [t for t in teams if not ok(t)]
    if need:
        log(f'Geocoding {len(need)} schools with the Census batch geocoder...')
        for start in range(0, len(need), 1000):
            batch = need[start:start + 1000]
            buf = io.StringIO()
            w = csv.writer(buf)
            ids = {}
            for i, t in enumerate(batch):
                a = addresses[t]
                ids[str(i)] = t
                w.writerow([i, a['street'], a['city'], a.get('state') or 'MO', a['zip']])
            res_text = ''
            for attempt in range(3):
                try:
                    r = requests.post(CENSUS_BATCH, files={'addressFile': ('addr.csv', buf.getvalue(), 'text/csv')},
                                      data={'benchmark': 'Public_AR_Current'}, timeout=300)
                    r.raise_for_status()
                    res_text = r.text
                    break
                except Exception as e:
                    log(f'  Census geocoder attempt {attempt + 1} failed: {e}')
                    time.sleep(10)
            for row in csv.reader(io.StringIO(res_text)):
                if len(row) >= 6 and row[0] in ids and row[2] == 'Match' and row[5]:
                    t = ids[row[0]]
                    lon, lat = map(float, row[5].split(','))
                    cache[t] = {'lat': lat, 'lon': lon, 'source': 'census', 'matched': row[4], 'addr': addr_key(addresses[t])}
        zip_fallback = 0
        for t in need:
            if not ok(t) or cache[t].get('addr') != addr_key(addresses[t]):
                a = addresses[t]
                cache[t] = {'lat': float(a['zip_lat']), 'lon': float(a['zip_lon']), 'source': 'zip_center',
                            'addr': addr_key(a)}
                zip_fallback += 1
        if zip_fallback:
            log(f'  {zip_fallback} schools had no street match (PO Box or rural route); using ZIP center')
        save_json(cache_path, cache)
    return {t: cache[t] for t in teams}


# --------------------------------------------------------------------------- drive times
def osrm_table(points, src_idx, dst_idx):
    pts = ';'.join(f'{lon:.5f},{lat:.5f}' for lat, lon in points)
    url = (f'{OSRM_URL}/table/v1/driving/{pts}?annotations=duration'
           f'&sources={";".join(map(str, src_idx))}&destinations={";".join(map(str, dst_idx))}')
    for attempt in range(6):
        try:
            r = requests.get(url, timeout=180)
            if r.status_code == 429:
                raise RuntimeError('rate limited (429)')
            r.raise_for_status()
            js = r.json()
            if js.get('code') != 'Ok':
                raise RuntimeError(js.get('message', js.get('code')))
            return js['durations']
        except Exception as e:
            wait = 15 * (attempt + 1)
            log(f'  OSRM attempt {attempt + 1} failed ({e}); retrying in {wait}s')
            time.sleep(wait)
    sys.exit(f'Could not get drive times from {OSRM_URL}')


def drive_matrix(cls, teams, coords, prefix):
    path = f'drive_times/{prefix}class_{cls}.json'
    teams = sorted(teams)  # cache key independent of seed order
    key = [[t, round(coords[t]['lat'], 5), round(coords[t]['lon'], 5)] for t in teams]
    cached = load_json(path)
    if cached and cached.get('key') == key:
        return cached['seconds']
    chunks = [teams[i:i + OSRM_CHUNK] for i in range(0, len(teams), OSRM_CHUNK)]
    log(f'Class {cls}: requesting {len(teams)}x{len(teams)} drive times from OSRM ({len(chunks) ** 2} requests)...')
    sec = {}
    for A in chunks:
        for B in chunks:
            pts_t = A + [t for t in B if t not in A]
            points = [(coords[t]['lat'], coords[t]['lon']) for t in pts_t]
            src = [pts_t.index(t) for t in A]
            dst = [pts_t.index(t) for t in B]
            dur = osrm_table(points, src, dst)
            for i, a in enumerate(A):
                for j, b in enumerate(B):
                    if a == b:
                        continue
                    if dur[i][j] is None:
                        sys.exit(f'OSRM found no route between {a} and {b}; check coordinates')
                    sec[a + '|' + b] = dur[i][j]
            time.sleep(2)  # be polite to the public server
    save_json(path, {'key': key, 'seconds': sec})
    return sec


# --------------------------------------------------------------------------- seeding
def make_seeds(cls, ratings, games, use_jumps=True):
    teams = sorted([t for t in ratings if t['classification'] == cls], key=lambda t: -t['ovr_rating'])
    order = [t['school'] for t in teams]
    wins, h2h = {}, {}
    for g in games:
        if g.get('score1') is None or g.get('score2') is None or g['score1'] == g['score2']:
            continue
        w, l = (g['team1'], g['team2']) if g['score1'] > g['score2'] else (g['team2'], g['team1'])
        wins[(w, l)] = wins.get((w, l), 0) + 1
        h2h.setdefault((w, l), []).append(
            f"{g['date']}: {g['team1']} {g['score1']}, {g['team2']} {g['score2']}" + (' (forfeit)' if g.get('forfeit') else ''))
    beat = lambda a, b: wins.get((a, b), 0) > wins.get((b, a), 0)  # won the season series
    seeds, moved, jumps, p = order[:], set(), [], 0
    while use_jumps and p < len(seeds):
        top = seeds[p]
        cand = [q for q in range(p + 1, min(p + 6, len(seeds))) if seeds[q] not in moved and beat(seeds[q], top)]
        if cand:
            q = cand[0]  # highest-rated eligible team jumps first
            j = seeds.pop(q)
            seeds.insert(p, j)
            moved.add(j)
            jumps.append({'team': j, 'jumped': top, 'from_seed': q + 1, 'to_seed': p + 1,
                          'result': h2h.get((j, top), []) + h2h.get((top, j), [])})
            continue  # the jumped team (now one spot lower) can still be jumped by someone else
        p += 1
    rating = {t['school']: t['ovr_rating'] for t in teams}
    return seeds, order, rating, jumps


# --------------------------------------------------------------------------- bracket
def bracket_order(n):
    o = [1]
    while len(o) < n:
        m = len(o) * 2 + 1
        o = [x for s in o for x in (s, m - s)]
    return o


class Bracket:
    def __init__(self, n_teams):
        if n_teams <= 64:
            self.lines = 64
        elif n_teams <= 128:
            self.lines = 128
        else:
            sys.exit(f'{n_teams} teams is more than a 128-line bracket holds')
        self.D = self.lines // 8
        self.slot = bracket_order(self.lines)  # slot[line] = ideal seed on that line
        self.next_pairs = [(d, d + 1) for d in range(0, self.D, 2)]
        if self.D == 8:
            self.rounds = ['District Quarterfinal', 'District Semifinal', 'District Championship',
                           'Quarterfinal', 'Semifinal', 'Championship']
            self.next_name = 'Quarterfinal'
        else:
            self.rounds = ['District Quarterfinal', 'District Semifinal', 'District Championship',
                           'Sectional', 'Quarterfinal', 'Semifinal', 'Championship']
            self.next_name = 'Sectional'
        self.byes = self.lines - n_teams


def optimize_districts(seeds, tt, time_limit, bye_rule, B, dist_lim, next_lim):
    """Assign teams to B.D districts in two stages:
       Stage 1: fewest travel violations (each over-limit pair that could meet counts once).
       Stage 2: holding that count, keep each team near its ideal seed line."""
    N = len(seeds)
    seed = {t: i + 1 for i, t in enumerate(seeds)}
    wt = {t: 1 + (N - seed[t]) / N for t in seeds}
    D = B.D

    def build():
        m = cp_model.CpModel()
        y = {(t, d): m.NewBoolVar(f'y{i}_{d}') for i, t in enumerate(seeds) for d in range(D)}
        for t in seeds:
            m.AddExactlyOne(y[t, d] for d in range(D))
        m.Add(y[seeds[0], 0] == 1)  # symmetry breaking: #1 seed in District 1
        for d in range(D):
            size = sum(y[t, d] for t in seeds)
            m.Add(size >= 4)
            m.Add(size <= 8)
            if bye_rule == 'statewide':  # a district with s teams holds exactly 8-s statewide bye seeds
                m.Add(sum(y[t, d] for t in seeds if seed[t] <= B.byes) == 8 - size)
        viol = []
        for a, b in itertools.combinations(seeds, 2):
            h = tt(a, b)
            if h > dist_lim:
                v = m.NewBoolVar('')
                for d in range(D):
                    m.Add(y[a, d] + y[b, d] <= 1 + v)
                viol.append((v, a, b, 'District rounds', h))
            if h > next_lim:
                v = m.NewBoolVar('')
                for d1, d2 in B.next_pairs:
                    m.Add(y[a, d1] + y[b, d2] <= 1 + v)
                    m.Add(y[b, d1] + y[a, d2] <= 1 + v)
                viol.append((v, a, b, B.next_name, h))
        proxy = sum(int(round(100 * wt[t])) * min(abs(seed[t] - B.slot[k]) for k in range(8 * d, 8 * d + 8)) * y[t, d]
                    for t in seeds for d in range(D))
        return m, y, viol, proxy

    def run(m, secs):
        s = cp_model.CpSolver()
        s.parameters.max_time_in_seconds = secs
        s.parameters.num_workers = 8
        s.parameters.random_seed = 1
        st = s.Solve(m)
        if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            sys.exit('Solver found no bracket at all (try a longer --time-limit)')
        return s, st

    # Stage 1
    m, y, viol, proxy = build()
    m.Minimize(sum(v for v, *_ in viol))
    s1, st1 = run(m, time_limit * 0.6)
    best = int(round(s1.ObjectiveValue()))
    proven = int(round(s1.BestObjectiveBound())) >= best
    hint = {k: s1.Value(v) for k, v in y.items()}
    # Stage 2
    m, y, viol, proxy = build()
    m.Add(sum(v for v, *_ in viol) <= best)
    for k, v in y.items():
        m.AddHint(v, hint[k])
    m.Minimize(proxy)
    s, st = run(m, time_limit * 0.4)
    districts = {d: sorted([t for t in seeds if s.Value(y[t, d])], key=lambda t: seed[t]) for d in range(D)}
    violations = [{'team_a': a, 'team_b': b, 'round': r, 'hours': round(h, 2)} for v, a, b, r, h in viol if s.Value(v)]
    info = {'solver_status': f'stage1 {s1.StatusName(st1)}, stage2 {s.StatusName(st)}',
            'violations_proven_minimum': proven,
            'solve_seconds': round(s1.WallTime() + s.WallTime(), 1)}
    return districts, violations, info


def place_lines(districts, seed, bye_rule, B):
    """Within each district: bye teams take the best seed lines; remaining teams
    play best-vs-worst in the District Quarterfinal."""
    line = {}
    for d, mem in districts.items():
        pairs = sorted([(k, k + 1) if B.slot[k] < B.slot[k + 1] else (k + 1, k) for k in range(8 * d, 8 * d + 8, 2)],
                       key=lambda p: B.slot[p[0]])
        if bye_rule == 'statewide':
            bye_t = [t for t in mem if seed[t] <= B.byes]
        else:
            bye_t = mem[:8 - len(mem)]
        play = [t for t in mem if t not in bye_t]
        for t, p in zip(bye_t, pairs):
            line[p[0]] = t
        for i, p in enumerate(pairs[len(bye_t):]):
            line[p[0]] = play[i]
            line[p[1]] = play[-1 - i]
    return line


# --------------------------------------------------------------------------- reporting
def fmt_h(h):
    mins = int(round(h * 60))
    return f'{mins // 60}h {mins % 60:02d}m'


def write_outputs(cfg, cls, season, seeds, order, rating, jumps, districts, line, violations, info, tt, args, B):
    seed = {t: i + 1 for i, t in enumerate(seeds)}
    N = len(seeds)
    next_key = B.next_name.lower() + 's'  # 'quarterfinals' or 'sectionals'
    out = {'sport': args.sport, 'season': season, 'class': cls, 'teams': N, 'bracket_lines': B.lines,
           'districts_count': B.D, 'rounds': B.rounds, 'byes': B.byes, 'bye_rule': args.bye_rule,
           'drive_time_factor': args.factor,
           'limits_hours': {'district_rounds': args.district_limit, B.next_name.lower(): args.next_limit},
           **info, 'violations': violations,
           'seeds': [{'seed': seed[t], 'team': t, 'ovr_rating': rating[t], 'rating_rank': order.index(t) + 1} for t in seeds],
           'jumps': jumps, 'districts': [], next_key: [], 'lines': []}
    md = [f"# {cfg['label']} Class {cls} travel-limited bracket", '',
          f'{N} teams on a {B.lines}-line bracket ({B.D} districts), {B.byes} first-round byes ({args.bye_rule} bye rule). '
          f'Drive-time factor {args.factor}. Limits: district rounds {args.district_limit} h, '
          f'{B.next_name.lower()} {args.next_limit} h (every possible matchup).', '',
          f'**Travel-limit violations: {len(violations)}**' +
          (' (proven minimum)' if info['violations_proven_minimum'] else ' (best found in time limit)'), '']
    if jumps:
        md += ['## Head-to-head jumps', '']
        md += [f"- **{j['team']}** jumped {j['jumped']} (seed {j['from_seed']} to {j['to_seed']}): {'; '.join(j['result'])}"
               for j in jumps]
        md += ['']
    for d in range(B.D):
        mem = districts[d]
        mx = max((tt(a, b) for a, b in itertools.combinations(mem, 2)), default=0)
        games, byelist = [], []
        for k in range(8 * d, 8 * d + 8, 2):
            a, b = line.get(k), line.get(k + 1)
            if a and b:
                hi, lo = sorted((a, b), key=lambda t: seed[t])
                games.append({'home': hi, 'away': lo, 'drive_h': round(tt(a, b), 2)})
            elif a or b:
                byelist.append(a or b)
        out['districts'].append({'district': d + 1, 'teams': [{'seed': seed[t], 'team': t} for t in mem],
                                 'byes': byelist, 'dqf_games': games, 'max_drive_h': round(mx, 2)})
        md += [f'## District {d + 1}  (longest possible trip {fmt_h(mx)})', '',
               '| Line | Seed | Team | First round |', '|---|---|---|---|']
        for k in range(8 * d, 8 * d + 8):
            t = line.get(k)
            if not t:
                continue
            opp = line.get(k ^ 1)
            fr = 'Bye' if not opp else f'vs #{seed[opp]} {opp} ({fmt_h(tt(t, opp))})'
            md.append(f'| {k + 1} | {seed[t]} | {t} | {fr} |')
        md.append('')
    md += [f'## {B.next_name} pairings', '']
    for d1, d2 in B.next_pairs:
        mx = max(tt(a, b) for a in districts[d1] for b in districts[d2])
        out[next_key].append({'districts': [d1 + 1, d2 + 1], 'max_drive_h': round(mx, 2)})
        md.append(f'- District {d1 + 1} champion vs District {d2 + 1} champion (longest possible trip {fmt_h(mx)})')
    md += ['- Later rounds: no travel limit', '']
    if violations:
        md += ['## Possible matchups over the limit', '', '| Round | Team | Team | Drive |', '|---|---|---|---|']
        md += [f"| {v['round']} | {v['team_a']} | {v['team_b']} | {fmt_h(v['hours'])} |"
               for v in sorted(violations, key=lambda v: -v['hours'])]
        md.append('')
    md += ['## Seeds', '', '| Seed | Team | OVR | Rating rank |', '|---|---|---|---|']
    md += [f'| {seed[t]} | {t} | {rating[t]} | {order.index(t) + 1} |' for t in seeds]
    out['lines'] = [{'line': k + 1, 'ideal_seed': B.slot[k], 'team': line.get(k),
                     'seed': seed.get(line.get(k))} for k in range(B.lines)]
    save_json(f"{cfg['out_dir']}/class_{cls}.json", out)
    with open(f"{cfg['out_dir']}/class_{cls}.md", 'w') as f:
        f.write('\n'.join(md) + '\n')


# --------------------------------------------------------------------------- main
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--sport', choices=list(SPORTS), default='football')
    ap.add_argument('--classes', default='1,2,3,4,5,6')
    ap.add_argument('--factor', type=float, default=1.0)
    ap.add_argument('--time-limit', type=float, default=60)
    ap.add_argument('--district-limit', type=float, default=3.0, help='hours, any two teams in a district')
    ap.add_argument('--next-limit', type=float, default=4.0,
                    help='hours, first round after districts (Quarterfinal or Sectional)')
    ap.add_argument('--bye-rule', choices=['statewide', 'district'], default='district')
    ap.add_argument('--no-jumps', action='store_true',
                    help='Seed purely by Overall Rating (skip the head-to-head jump rule)')
    ap.add_argument('--ratings')
    ap.add_argument('--games')
    ap.add_argument('--addresses')
    ap.add_argument('--season', type=int, help='season year inside a ratings history file (default latest)')
    ap.add_argument('--games-through', help='only use games on or before this date (YYYY-MM-DD) for head-to-head, '
                                            'e.g. the last regular-season day so playoff games are ignored')
    args = ap.parse_args()

    cfg = dict(SPORTS[args.sport])
    ratings, season = load_ratings(args.ratings or cfg['ratings'], args.season)
    games = load_games(args.games or cfg['games'])
    if args.games_through:
        games = [g for g in games if g.get('date') and str(g['date'])[:10] <= args.games_through]
    addresses = load_addresses(args.addresses or cfg['addresses'])
    classes = [int(c) for c in args.classes.split(',') if c.strip()]
    log(f"{cfg['label']}: {len(ratings)} rated teams" + (f' (season {season})' if season else '') +
        f', {len(games)} games for head-to-head')

    summary = [f"# {cfg['label']} travel-limited playoff brackets", '',
               f'Bye rule: {args.bye_rule}. Drive-time factor {args.factor}. Limits: district rounds '
               f'{args.district_limit} h; first round after districts {args.next_limit} h.', '',
               '| Class | Teams | Bracket | Byes | Violations | Proven minimum? |', '|---|---|---|---|---|---|']
    for cls in classes:
        seeds, order, rating, jumps = make_seeds(cls, ratings, games, use_jumps=not args.no_jumps)
        if not seeds:
            log(f'Class {cls}: no teams, skipping')
            continue
        missing = [t for t in seeds if t not in addresses]
        if missing:
            sys.exit(f'Class {cls}: no address for {missing}; add them to the addresses file')
        B = Bracket(len(seeds))
        coords = geocode(seeds, addresses)
        sec = drive_matrix(cls, seeds, coords, cfg['cache_prefix'])
        tt = lambda a, b: max(sec[a + '|' + b], sec[b + '|' + a]) * args.factor / 3600  # slower direction, hours
        log(f'Class {cls}: optimizing {B.D} districts ({len(seeds)} teams, up to {args.time_limit:.0f}s)...')
        districts, violations, info = optimize_districts(seeds, tt, args.time_limit, args.bye_rule, B,
                                                         args.district_limit, args.next_limit)
        seed = {t: i + 1 for i, t in enumerate(seeds)}
        line = place_lines(districts, seed, args.bye_rule, B)
        write_outputs(cfg, cls, season, seeds, order, rating, jumps, districts, line, violations, info, tt, args, B)
        log(f"Class {cls}: {len(violations)} violations ({info['solver_status']}, {info['solve_seconds']}s)")
        summary.append(f"| {cls} | {len(seeds)} | {B.lines} lines / {B.D} districts | {B.byes} | {len(violations)} | "
                       f"{'Yes' if info['violations_proven_minimum'] else 'No'} |")
    os.makedirs(cfg['out_dir'], exist_ok=True)
    with open(f"{cfg['out_dir']}/README.md", 'w') as f:
        f.write('\n'.join(summary) + '\n')
    log(f"Done. See {cfg['out_dir']}/.")


if __name__ == '__main__':
    main()
