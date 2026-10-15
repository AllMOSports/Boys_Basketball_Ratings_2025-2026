"""
All MO Sports - travel-limited playoff bracket optimizer, v2 (football and boys basketball).
 
What it does for each class
  1. Geocodes every school (U.S. Census batch geocoder; ZIP-center fallback).
  2. Pulls a full drive-time table from OSRM (chunked, so 100+ team classes work).
  3. Seeds teams by Overall Rating (+ optional head-to-head jump rule).
  4. Builds districts in two stages:
       Stage 1 - travel: fewest minutes over the travel limits (every possible
                 matchup counts). A 3h05m trip costs far less than a 5h one.
       Stage 2 - balance: holding travel at that level (plus optional slack),
                 spread the strong teams out and keep districts compact:
                   * one top-tier seed per district (top 8, or top 16 with 16 districts)
                   * penalty for strong teams (top 2x tier) sharing a district
                   * even spread of seed tiers across districts
                   * small penalty on total drive time inside districts
  5. Places districts and teams on the bracket: district pairs (or, with
     --reseed, district champions) follow standard seeding; top seeds get
     byes; first round is best-vs-worst inside each district.
  6. Scores the result AND MSHSAA's actual districts the same way
     (travel + competitive balance via Monte Carlo on the ratings).
 
Bracket size
  64 lines / 8 districts (<= 64 teams):  District QF/SF/Final, Quarterfinal, Semifinal, Championship
  128 lines / 16 districts (65-128):     District QF/SF/Final, Sectional, Quarterfinal, Semifinal, Championship
 
Main options
  --sport football|boys_basketball
  --district-limit H     max hours between any two teams in a district (default 3.0)
  --next-limit H         max hours for the first round after districts (default 4.0)
  --sweep 2.5,3,3.5,4    run several district limits; outputs go to limit_X/ subfolders
  --priority balance|travel|geographic   objective preset (default balance)
  --weights top=5000,pairs=40,tiers=200,travel=1   override preset weights
  --travel-slack-pct P   stage 2 may exceed the best travel score by P% for balance (default 50;
                         classes that reach zero violations stay at zero)
  --travel-slack MIN     extra absolute minutes over the limits stage 2 may add (default 0)
  --reseed               after districts, re-seed champions by seed (no geographic pairing)
  --bye-rule district|statewide
  --no-jumps / --games-through YYYY-MM-DD
  --factor F|auto        scale OSRM times; 'auto' uses --calibration
  --calibration FILE     CSV team_a,team_b,minutes (e.g. Google Maps checks) -> recommended factor
  --sims N               Monte Carlo runs per bracket for the scorecard (default 4000)
  --sigma S              point-margin std dev for win probabilities (default: football 14, basketball 11)
 
Inputs / outputs per sport
  football        football_ratings_2026.json, football_games_2026_all.json,
                  football_school_addresses.csv -> playoff_brackets/
  boys_basketball mo-data/output/mshsaa_historical_records/boys_basketball/Boys_Basketball_Ratings_History_2012-2025.json
                  mo-data/output/boys_basketball_schedule_2025-2026.json,
                  basketball_school_addresses.csv -> playoff_brackets_boys_basketball/
  Shared caches: school_coords.json, drive_times/<prefix>class_N.json
  coord_overrides.json (optional) {"Team": [lat, lon]}
  Set OSRM_URL to use your own OSRM server.
"""
import argparse, csv, io, itertools, json, math, os, random, statistics, sys, time
 
import requests
from ortools.sat.python import cp_model
 
OSRM_URL = os.environ.get('OSRM_URL', 'https://router.project-osrm.org').rstrip('/')
CENSUS_BATCH = 'https://geocoding.geo.census.gov/geocoder/locations/addressbatch'
OSRM_CHUNK = 50
 
SPORTS = {
    'football': {
        'label': 'Football', 'sigma': 14.0,
        'ratings': 'football_ratings_2026.json',
        'games': 'football_games_2026_all.json',
        'addresses': 'football_school_addresses.csv',
        'out_dir': 'playoff_brackets', 'cache_prefix': '',
    },
    'boys_basketball': {
        'label': 'Boys Basketball', 'sigma': 11.0,
        'ratings': 'mo-data/output/mshsaa_historical_records/boys_basketball/Boys_Basketball_Ratings_History_2012-2025.json',
        'games': 'mo-data/output/boys_basketball_schedule_2025-2026.json',
        'addresses': 'basketball_school_addresses.csv',
        'out_dir': 'playoff_brackets_boys_basketball', 'cache_prefix': 'boys_basketball_',
    },
}
 
PRESETS = {  # objective weights for stage 2 (travel term is in minutes)
    'balance':    {'top': 5000, 'pairs': 40, 'tiers': 200, 'travel': 1},
    'travel':     {'top': 500,  'pairs': 5,  'tiers': 50,  'travel': 8},
    'geographic': {'top': 0,    'pairs': 0,  'tiers': 0,   'travel': 10},
}
 
 
def log(*a):
    print(*a, flush=True)
 
 
# =========================================================================== data
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
            if key in seen:
                continue
            seen.add(key)
            games.append({'date': g.get('date'), 'team1': team, 'team2': opp, 'score1': ts, 'score2': os_,
                          'forfeit': bool(g.get('forfeit'))})
    return games
 
 
# =========================================================================== geocoding
def addr_key(a):
    return f"{a['street']}|{a['city']}|{a['zip']}".upper()
 
 
def geocode(teams, addresses, cache_path='school_coords.json'):
    cache = load_json(cache_path, {})
    for t, (lat, lon) in load_json('coord_overrides.json', {}).items():
        cache[t] = {'lat': lat, 'lon': lon, 'source': 'override'}
 
    def ok(t):
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
        fallback = 0
        for t in need:
            if cache.get(t, {}).get('addr') != addr_key(addresses[t]) and cache.get(t, {}).get('source') != 'override':
                a = addresses[t]
                cache[t] = {'lat': float(a['zip_lat']), 'lon': float(a['zip_lon']), 'source': 'zip_center', 'addr': addr_key(a)}
                fallback += 1
        if fallback:
            log(f'  {fallback} schools had no street match (PO Box or rural route); using ZIP center')
        save_json(cache_path, cache)
    return {t: cache[t] for t in teams}
 
 
# =========================================================================== drive times
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
    teams = sorted(teams)
    key = [[t, round(coords[t]['lat'], 5), round(coords[t]['lon'], 5)] for t in teams]
    cached = load_json(path)
    if cached and cached.get('key') == key:
        return cached['seconds']
    chunks = [teams[i:i + OSRM_CHUNK] for i in range(0, len(teams), OSRM_CHUNK)]
    log(f'Class {cls}: requesting {len(teams)}x{len(teams)} drive times from OSRM ({len(chunks) ** 2} requests)...')
    sec = {}
    for A in chunks:
        for Bc in chunks:
            pts_t = A + [t for t in Bc if t not in A]
            points = [(coords[t]['lat'], coords[t]['lon']) for t in pts_t]
            dur = osrm_table(points, [pts_t.index(t) for t in A], [pts_t.index(t) for t in Bc])
            for i, a in enumerate(A):
                for j, b in enumerate(Bc):
                    if a != b:
                        if dur[i][j] is None:
                            sys.exit(f'OSRM found no route between {a} and {b}; check coordinates')
                        sec[a + '|' + b] = dur[i][j]
            time.sleep(2)
    save_json(path, {'key': key, 'seconds': sec})
    return sec
 
 
def calibrate(path, matrices):
    """CSV team_a,team_b,minutes (real-world drive time). Returns median real/OSRM ratio."""
    ratios, rows = [], []
    with open(path, newline='') as f:
        for r in csv.DictReader(f):
            if not (r.get('minutes') or '').strip():
                continue  # blank row in the template
            a, b, m = r['team_a'].strip(), r['team_b'].strip(), float(r['minutes'])
            for sec in matrices.values():
                if a + '|' + b in sec:
                    osrm = max(sec[a + '|' + b], sec[b + '|' + a]) / 60
                    ratios.append(m / osrm)
                    rows.append((a, b, m, round(osrm, 1)))
                    break
            else:
                log(f'  calibration: {a} / {b} not found in the same class, skipped')
    if not ratios:
        sys.exit('Calibration file had no usable pairs')
    f = statistics.median(ratios)
    log(f'Calibration: {len(ratios)} pairs, median real/OSRM = {f:.3f} (range {min(ratios):.2f}-{max(ratios):.2f})')
    return round(f, 3), rows
 
 
# =========================================================================== seeding
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
    beat = lambda a, b: wins.get((a, b), 0) > wins.get((b, a), 0)
    seeds, moved, jumps, p = order[:], set(), [], 0
    while use_jumps and p < len(seeds):
        top = seeds[p]
        cand = [q for q in range(p + 1, min(p + 6, len(seeds))) if seeds[q] not in moved and beat(seeds[q], top)]
        if cand:
            q = cand[0]
            j = seeds.pop(q)
            seeds.insert(p, j)
            moved.add(j)
            jumps.append({'team': j, 'jumped': top, 'from_seed': q + 1, 'to_seed': p + 1,
                          'result': h2h.get((j, top), []) + h2h.get((top, j), [])})
            continue
        p += 1
    rating = {t['school']: t['ovr_rating'] for t in teams}
    mshsaa_district = {t['school']: t.get('district') for t in teams}
    return seeds, order, rating, jumps, mshsaa_district
 
 
# =========================================================================== bracket
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
        self.R = int(math.log2(self.lines))
        self.slot = bracket_order(self.lines)
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
 
 
def optimize_districts(seeds, tt, args, B, limit, next_lim, weights):
    N = len(seeds)
    D = B.D
    seed = {t: i + 1 for i, t in enumerate(seeds)}
    pairs = list(itertools.combinations(seeds, 2))  # (better, worse) by seed
    hrs = {p: tt(*p) for p in pairs}
    top = [t for t in seeds if seed[t] <= D]
    strong = [t for t in seeds if seed[t] <= 2 * D]
    n_tiers = math.ceil(N / D)
 
    def build(full):
        m = cp_model.CpModel()
        y = {(t, d): m.NewBoolVar('') for t in seeds for d in range(D)}
        for t in seeds:
            m.AddExactlyOne(y[t, d] for d in range(D))
        m.Add(y[seeds[0], 0] == 1)  # symmetry breaking
        for d in range(D):
            size = sum(y[t, d] for t in seeds)
            m.Add(size >= 4)
            m.Add(size <= 8)
            if args.bye_rule == 'statewide':
                m.Add(sum(y[t, d] for t in seeds if seed[t] <= B.byes) == 8 - size)
        z, over_terms, viol, nxt = {}, [], [], {}
        for p in pairs:
            a, b = p
            h = hrs[p]
            if full or h > limit:
                v = m.NewBoolVar('')
                for d in range(D):
                    m.Add(y[a, d] + y[b, d] <= 1 + v)
                z[p] = v
                if h > limit:
                    over_terms.append((int(round((h - limit) * 60)) + 30) * v)
                    viol.append((v, a, b, 'District rounds', h))
            if not args.reseed and h > next_lim:
                w = m.NewBoolVar('')
                for d1, d2 in B.next_pairs:
                    m.Add(y[a, d1] + y[b, d2] <= 1 + w)
                    m.Add(y[b, d1] + y[a, d2] <= 1 + w)
                over_terms.append((int(round((h - next_lim) * 60)) + 30) * w)
                viol.append((w, a, b, B.next_name, h))
                nxt[p] = w
        return m, y, z, over_terms, viol, nxt
 
    def run(m, secs, must=True):
        s = cp_model.CpSolver()
        s.parameters.max_time_in_seconds = secs
        s.parameters.num_workers = 8
        s.parameters.random_seed = 1
        st = s.Solve(m)
        if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE) and must:
            sys.exit('Solver found no bracket at all (try a longer --time-limit)')
        return s, st
 
    # ---- Stage 1: travel
    m, y, z, over, viol, nxt = build(full=False)
    m.Minimize(sum(over) if over else 0)
    s1, st1 = run(m, args.time_limit * 0.4)
    best = int(round(s1.ObjectiveValue())) if over else 0
    proven = (int(round(s1.BestObjectiveBound())) >= best) if over else True
    hint = {k: s1.Value(v) for k, v in y.items()}
    dist1 = {t: d for (t, d), v in hint.items() if v}
    stage1_districts = [sorted([t for t in seeds if dist1[t] == d], key=lambda t: seed[t]) for d in range(D)]
    stage1_viol = [{'team_a': a, 'team_b': b, 'round': r, 'hours': round(h, 2)} for v, a, b, r, h in viol if s1.Value(v)]
 
    # ---- Stage 2: balance + compactness, travel held at best (+ slack)
    m, y, z, over, viol, nxt = build(full=True)
    pair_of = {}
    for d1, d2 in B.next_pairs:
        pair_of[d1], pair_of[d2] = d2, d1
    for p, v in z.items():
        m.AddHint(v, int(dist1[p[0]] == dist1[p[1]]))
    for p, v in nxt.items():
        m.AddHint(v, int(pair_of[dist1[p[0]]] == dist1[p[1]]))
    groups = []  # (var, members, district) for 'at most one' style penalties, hinted below
    allowance = best + int(round(best * args.travel_slack_pct / 100)) + int(args.travel_slack)
    if over:
        m.Add(sum(over) <= allowance)
    terms = []
    if weights['top'] and len(top) >= 2:
        for d in range(D):
            e = m.NewIntVar(0, len(top), '')
            m.Add(e >= sum(y[t, d] for t in top) - 1)
            terms.append(weights['top'] * e)
            groups.append((e, top, d))
    if weights['pairs']:
        for p in itertools.combinations(strong, 2):
            wgt = (2 * D + 1 - seed[p[0]]) + (2 * D + 1 - seed[p[1]])
            terms.append(weights['pairs'] * wgt * z[p])
    if weights['tiers']:
        for k in range(n_tiers):
            tier = [t for t in seeds if k * D < seed[t] <= (k + 1) * D]
            if len(tier) < 2:
                continue
            for d in range(D):
                e = m.NewIntVar(0, len(tier), '')
                m.Add(e >= sum(y[t, d] for t in tier) - 1)
                terms.append(weights['tiers'] * e)
                groups.append((e, tier, d))
    if weights['travel']:
        terms.append(weights['travel'] * sum(int(round(hrs[p] * 60)) * z[p] for p in pairs))
    m.Minimize(sum(terms) if terms else 0)
    for k, v in y.items():
        m.AddHint(v, hint[k])
    for e, mem, d in groups:
        m.AddHint(e, max(0, sum(1 for t in mem if dist1[t] == d) - 1))
    s, st = run(m, args.time_limit * 0.6, must=False)
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        districts = [sorted([t for t in seeds if s.Value(y[t, d])], key=lambda t: seed[t]) for d in range(D)]
        violations = [{'team_a': a, 'team_b': b, 'round': r, 'hours': round(h, 2)} for v, a, b, r, h in viol if s.Value(v)]
        st2 = s.StatusName(st)
    else:  # stage 2 found nothing in time: keep the stage 1 (travel-only) bracket
        log('  stage 2 found no improvement in time; using the travel-only bracket (try a longer --time-limit)')
        districts, violations, st2 = stage1_districts, stage1_viol, 'NONE (kept stage 1)'
    info = {'solver_status': f'stage1 {s1.StatusName(st1)}, stage2 {st2}',
            'violations_proven_minimum': proven, 'minutes_over_limit_score': best,
            'travel_allowance_used': allowance,
            'solve_seconds': round(s1.WallTime() + s.WallTime(), 1)}
    return districts, violations, info
 
 
def order_districts(districts, seed, B, reseed):
    """Put district blocks on the bracket so top seeds follow standard seeding.
    Without reseed, solver-chosen district pairs (which share the next-round travel
    limit) stay together; pairs and the two districts within a pair are ordered."""
    best = [min(seed[t] for t in d) if d else 10 ** 6 for d in districts]
    ideal = [B.slot[8 * k] for k in range(B.D)]  # ideal top seed of each district position
    out = [None] * B.D
    if reseed:
        for d, k in zip(sorted(range(B.D), key=lambda d: best[d]), sorted(range(B.D), key=lambda k: ideal[k])):
            out[k] = districts[d]
        return out
    pairs = [(d1, d2) for d1, d2 in B.next_pairs]
    pslots = list(range(B.D // 2))
    pbest = sorted(pairs, key=lambda p: min(best[p[0]], best[p[1]]))
    sbest = sorted(pslots, key=lambda j: min(ideal[2 * j], ideal[2 * j + 1]))
    for (d1, d2), j in zip(pbest, sbest):
        hi, lo = sorted((d1, d2), key=lambda d: best[d])
        k_hi, k_lo = sorted((2 * j, 2 * j + 1), key=lambda k: ideal[k])
        out[k_hi], out[k_lo] = districts[hi], districts[lo]
    return out
 
 
def place_lines(districts, seed, bye_rule, B):
    line = {}
    for d, mem in enumerate(districts):
        pairs = sorted([(k, k + 1) if B.slot[k] < B.slot[k + 1] else (k + 1, k) for k in range(8 * d, 8 * d + 8, 2)],
                       key=lambda p: B.slot[p[0]])
        bye_t = [t for t in mem if seed[t] <= B.byes] if bye_rule == 'statewide' else mem[:8 - len(mem)]
        play = [t for t in mem if t not in bye_t]
        for t, p in zip(bye_t, pairs):
            line[p[0]] = t
        for i, p in enumerate(pairs[len(bye_t):]):
            line[p[0]] = play[i]
            line[p[1]] = play[-1 - i]
    return line
 
 
def mshsaa_districts(seeds, mdist, B):
    """MSHSAA's actual districts (from the ratings file), in district-number order."""
    groups = {}
    for t in seeds:
        if mdist.get(t) is None:
            return None, 'some teams have no district number'
        groups.setdefault(int(mdist[t]), []).append(t)
    if len(groups) != B.D:
        return None, f'{len(groups)} MSHSAA districts vs {B.D} bracket districts'
    if any(len(g) > 8 for g in groups.values()):
        return None, 'an MSHSAA district has more than 8 teams'
    seed = {t: i + 1 for i, t in enumerate(seeds)}
    return [sorted(groups[k], key=lambda t: seed[t]) for k in sorted(groups)], None
 
 
# =========================================================================== scorecard
def scorecard(line, seeds, rating, tt, B, limit, next_lim, sims, sigma, rng):
    seed = {t: i + 1 for i, t in enumerate(seeds)}
    teams = [line.get(k) for k in range(B.lines)]
    D = B.D
    district_of = {t: k // 8 for k, t in enumerate(teams) if t}
    phi = lambda x: 0.5 * (1 + math.erf(x / math.sqrt(2)))
    pw = {}
 
    def p_win(a, b):
        if (a, b) not in pw:
            pw[(a, b)] = phi((rating[a] - rating[b]) / sigma)
        return pw[(a, b)]
 
    # chalk (higher seed always wins)
    chalk_d, chalk_n = [], []
    ent = teams[:]
    for r in range(4):
        nxt = []
        for i in range(0, len(ent), 2):
            a, b = ent[i], ent[i + 1]
            if a and b:
                (chalk_d if r < 3 else chalk_n).append(tt(a, b) * 60)
                nxt.append(a if seed[a] < seed[b] else b)
            else:
                nxt.append(a or b)
        ent = nxt
    # Monte Carlo
    top8 = {t for t in seeds if seed[t] <= 8}
    top4 = {t for t in seeds if seed[t] <= 4}
    s1, s2 = seeds[0], seeds[1] if len(seeds) > 1 else None
    tot_d = n_d = tot_n = n_n = 0
    any_over = e_top8 = e_top4 = meet12 = champ1 = 0
    for _ in range(sims):
        ent = teams[:]
        over = False
        for r in range(B.R):
            if r == B.R - 3:
                e_top8 += sum(1 for t in ent if t in top8)
            if r == B.R - 2:
                e_top4 += sum(1 for t in ent if t in top4)
            if r == B.R - 1:
                meet12 += (s1 in ent and s2 in ent)
            nxt = []
            for i in range(0, len(ent), 2):
                a, b = ent[i], ent[i + 1]
                if a and b:
                    if r < 3:
                        h = tt(a, b)
                        tot_d += h * 60
                        n_d += 1
                        over = over or h > limit
                    elif r == 3:
                        tot_n += tt(a, b) * 60
                        n_n += 1
                    nxt.append(a if rng.random() < p_win(a, b) else b)
                else:
                    nxt.append(a or b)
            ent = nxt
        champ1 += ent[0] == s1
        any_over += over
    top_t = [t for t in seeds if seed[t] <= D]
    strong = [t for t in seeds if seed[t] <= 2 * D]
    dist_best = {}
    for t in teams:
        if t:
            d = district_of[t]
            dist_best[d] = min(dist_best.get(d, 10 ** 6), seed[t])
    best_ratings = [rating[seeds[s - 1]] for s in dist_best.values()]
    return {
        'chalk_district_game_avg_min': round(statistics.mean(chalk_d), 1) if chalk_d else 0,
        'chalk_district_game_max_min': round(max(chalk_d), 1) if chalk_d else 0,
        'chalk_district_games_over_limit': sum(1 for x in chalk_d if x > limit * 60),
        'chalk_next_round_max_min': round(max(chalk_n), 1) if chalk_n else 0,
        'expected_district_game_min': round(tot_d / max(n_d, 1), 1),
        'expected_next_round_game_min': round(tot_n / max(n_n, 1), 1),
        'p_any_district_game_over_limit': round(any_over / sims, 3),
        'top_seed_pairs_same_district': sum(1 for a, b in itertools.combinations(top_t, 2) if district_of[a] == district_of[b]),
        'strong_pairs_same_district': sum(1 for a, b in itertools.combinations(strong, 2) if district_of[a] == district_of[b]),
        'weakest_district_best_seed': max(dist_best.values()),
        'district_best_rating_sd': round(statistics.pstdev(best_ratings), 2),
        'exp_top8_in_quarterfinals': round(e_top8 / sims, 2),
        'exp_top4_in_final_four': round(e_top4 / sims, 2),
        'p_1_vs_2_final': round(meet12 / sims, 3),
        'p_top_seed_champion': round(champ1 / sims, 3),
    }
 
 
SC_LABELS = [
    ('chalk_district_game_avg_min', 'Avg district-round trip, expected matchups (min)', 'low'),
    ('chalk_district_game_max_min', 'Longest district-round trip, expected matchups (min)', 'low'),
    ('expected_district_game_min', 'Avg district-round trip, simulated (min)', 'low'),
    ('p_any_district_game_over_limit', 'Chance any district game is over the limit', 'low'),
    ('chalk_next_round_max_min', 'Longest first post-district trip, expected (min)', 'low'),
    ('top_seed_pairs_same_district', 'Top-tier seed pairs sharing a district', 'low'),
    ('strong_pairs_same_district', 'Strong-team pairs (top 2x tier) sharing a district', 'low'),
    ('weakest_district_best_seed', "Weakest district's best seed", 'low'),
    ('district_best_rating_sd', 'Spread of district top-team ratings (SD)', 'low'),
    ('exp_top8_in_quarterfinals', 'Expected top-8 seeds reaching the quarterfinals', 'high'),
    ('exp_top4_in_final_four', 'Expected top-4 seeds reaching the final four', 'high'),
    ('p_1_vs_2_final', 'Chance #1 and #2 meet in the final', 'high'),
    ('p_top_seed_champion', 'Chance the #1 seed wins', 'info'),
]
 
 
# =========================================================================== reporting
def fmt_h(h):
    mins = int(round(h * 60))
    return f'{mins // 60}h {mins % 60:02d}m'
 
 
def write_outputs(cfg, out_dir, cls, season, seeds, order, rating, jumps, districts, line, violations, info,
                  tt, args, B, limit, next_lim, weights, sc, base_sc, base_line, base_note, factor):
    seed = {t: i + 1 for i, t in enumerate(seeds)}
    N = len(seeds)
    next_key = B.next_name.lower() + 's'
    out = {'sport': args.sport, 'season': season, 'class': cls, 'teams': N, 'bracket_lines': B.lines,
           'districts_count': B.D, 'rounds': B.rounds, 'byes': B.byes, 'bye_rule': args.bye_rule,
           'reseed': args.reseed, 'priority': args.priority, 'weights': weights,
           'drive_time_factor': factor,
           'limits_hours': {'district_rounds': limit, B.next_name.lower(): None if args.reseed else next_lim},
           **info, 'violations': violations, 'scorecard': sc, 'mshsaa_scorecard': base_sc,
           'mshsaa_note': base_note,
           'seeds': [{'seed': seed[t], 'team': t, 'ovr_rating': rating[t], 'rating_rank': order.index(t) + 1} for t in seeds],
           'jumps': jumps, 'districts': [], next_key: [], 'lines': [],
           'mshsaa_lines': [{'line': k + 1, 'team': base_line.get(k)} for k in range(B.lines)] if base_line else None}
    md = [f"# {cfg['label']} Class {cls} travel-limited bracket", '',
          f'{N} teams on a {B.lines}-line bracket ({B.D} districts), {B.byes} first-round byes ({args.bye_rule} bye rule). '
          f'Priority: {args.priority}. Drive-time factor {factor}. District limit {limit} h' +
          ('; district champions re-seeded after districts.' if args.reseed else f'; {B.next_name.lower()} limit {next_lim} h.'),
          '', f'**Travel-limit violations: {len(violations)}**' +
          (' (proven minimum)' if info['violations_proven_minimum'] else ' (best found in time limit)'), '']
    md += ['## Scorecard', '', '| Measure | This bracket | MSHSAA districts |', '|---|---|---|']
    for k, lab, _ in SC_LABELS:
        md.append(f"| {lab} | {sc[k]} | {base_sc[k] if base_sc else '-'} |")
    if base_note:
        md.append(f'\nMSHSAA comparison: {base_note}')
    md.append('')
    if jumps:
        md += ['## Head-to-head jumps', '']
        md += [f"- **{j['team']}** jumped {j['jumped']} (seed {j['from_seed']} to {j['to_seed']}): {'; '.join(j['result'])}"
               for j in jumps]
        md.append('')
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
            if t:
                opp = line.get(k ^ 1)
                fr = 'Bye' if not opp else f'vs #{seed[opp]} {opp} ({fmt_h(tt(t, opp))})'
                md.append(f'| {k + 1} | {seed[t]} | {t} | {fr} |')
        md.append('')
    md += [f'## {B.next_name} pairings', '']
    for d1, d2 in B.next_pairs:
        mx = max(tt(a, b) for a in districts[d1] for b in districts[d2])
        out[next_key].append({'districts': [d1 + 1, d2 + 1], 'max_drive_h': round(mx, 2)})
        md.append(f'- District {d1 + 1} champion vs District {d2 + 1} champion (longest possible trip {fmt_h(mx)})')
    md.append('')
    if violations:
        md += ['## Possible matchups over the limit', '', '| Round | Team | Team | Drive |', '|---|---|---|---|']
        md += [f"| {v['round']} | {v['team_a']} | {v['team_b']} | {fmt_h(v['hours'])} |"
               for v in sorted(violations, key=lambda v: -v['hours'])]
        md.append('')
    md += ['## Seeds', '', '| Seed | Team | OVR | Rating rank |', '|---|---|---|---|']
    md += [f'| {seed[t]} | {t} | {rating[t]} | {order.index(t) + 1} |' for t in seeds]
    out['lines'] = [{'line': k + 1, 'ideal_seed': B.slot[k], 'team': line.get(k), 'seed': seed.get(line.get(k))}
                    for k in range(B.lines)]
    save_json(f'{out_dir}/class_{cls}.json', out)
    with open(f'{out_dir}/class_{cls}.md', 'w') as f:
        f.write('\n'.join(md) + '\n')
 
 
# =========================================================================== main
def parse_weights(args):
    w = dict(PRESETS[args.priority])
    if args.weights:
        for part in args.weights.split(','):
            k, v = part.split('=')
            if k.strip() not in w:
                sys.exit(f'Unknown weight {k}; use top, pairs, tiers, travel')
            w[k.strip()] = int(float(v))
    return w
 
 
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--sport', choices=list(SPORTS), default='football')
    ap.add_argument('--classes', default='1,2,3,4,5,6')
    ap.add_argument('--factor', default='1.0', help="number, or 'auto' with --calibration")
    ap.add_argument('--calibration', help='CSV team_a,team_b,minutes of real-world drive times')
    ap.add_argument('--time-limit', type=float, default=300, help='solver seconds per class (per limit)')
    ap.add_argument('--district-limit', type=float, default=3.0)
    ap.add_argument('--next-limit', type=float, default=4.0)
    ap.add_argument('--sweep', help='comma-separated district limits to compare, e.g. 2.5,3,3.5,4')
    ap.add_argument('--priority', choices=list(PRESETS), default='balance')
    ap.add_argument('--weights', help='override weights, e.g. top=5000,pairs=40,tiers=200,travel=1')
    ap.add_argument('--travel-slack-pct', type=float, default=50,
                    help='stage 2 may exceed the best travel score by this %% to improve balance '
                         '(a class that can reach zero violations stays at zero)')
    ap.add_argument('--travel-slack', type=float, default=0,
                    help='extra absolute minutes-over-limit stage 2 may add (can create new violations)')
    ap.add_argument('--reseed', action='store_true', help='re-seed district champions by seed after districts')
    ap.add_argument('--bye-rule', choices=['statewide', 'district'], default='district')
    ap.add_argument('--no-jumps', action='store_true')
    ap.add_argument('--games-through')
    ap.add_argument('--sims', type=int, default=4000)
    ap.add_argument('--sigma', type=float)
    ap.add_argument('--ratings')
    ap.add_argument('--games')
    ap.add_argument('--addresses')
    ap.add_argument('--season', type=int)
    args = ap.parse_args()
 
    cfg = dict(SPORTS[args.sport])
    sigma = args.sigma or cfg['sigma']
    weights = parse_weights(args)
    ratings, season = load_ratings(args.ratings or cfg['ratings'], args.season)
    games = load_games(args.games or cfg['games'])
    if args.games_through:
        games = [g for g in games if g.get('date') and str(g['date'])[:10] <= args.games_through]
    addresses = load_addresses(args.addresses or cfg['addresses'])
    classes = [int(c) for c in args.classes.split(',') if c.strip()]
    limits = [float(x) for x in args.sweep.split(',')] if args.sweep else [args.district_limit]
    log(f"{cfg['label']}: {len(ratings)} rated teams" + (f' (season {season})' if season else '') +
        f', {len(games)} games for head-to-head; priority {args.priority} {weights}')
 
    # ---- Phase 1: seeds, coordinates, drive times for every class
    prep, matrices = {}, {}
    for cls in classes:
        seeds, order, rating, jumps, mdist = make_seeds(cls, ratings, games, use_jumps=not args.no_jumps)
        if not seeds:
            log(f'Class {cls}: no teams, skipping')
            continue
        missing = [t for t in seeds if t not in addresses]
        if missing:
            sys.exit(f'Class {cls}: no address for {missing}; add them to the addresses file')
        coords = geocode(seeds, addresses)
        matrices[cls] = drive_matrix(cls, seeds, coords, cfg['cache_prefix'])
        prep[cls] = (seeds, order, rating, jumps, mdist)
 
    calib_rows = None
    if args.factor == 'auto':
        if not args.calibration:
            sys.exit("--factor auto needs --calibration FILE")
        factor, calib_rows = calibrate(args.calibration, matrices)
    else:
        factor = float(args.factor)
        if args.calibration:
            rec, calib_rows = calibrate(args.calibration, matrices)
            log(f'  (recommended --factor {rec}; using {factor})')
 
    # ---- Phase 2: optimize + score
    summary = [f"# {cfg['label']} travel-limited playoff brackets", '',
               f'Priority {args.priority} {weights}. Travel slack {args.travel_slack_pct:g}% (+{args.travel_slack:g} min). Bye rule {args.bye_rule}. Reseed after districts: {args.reseed}. '
               f'Drive-time factor {factor}. First round after districts limit: '
               f"{'none (reseeded)' if args.reseed else f'{args.next_limit} h'}.", '',
               '| Class | District limit | Violations | Avg district trip (min) ours / MSHSAA | '
               'Top-seed pairs together ours / MSHSAA | Exp. top-8 in QF ours / MSHSAA | Weakest district best seed ours / MSHSAA |',
               '|---|---|---|---|---|---|---|']
    for cls, (seeds, order, rating, jumps, mdist) in prep.items():
        sec = matrices[cls]
        tt = lambda a, b, sec=sec: max(sec[a + '|' + b], sec[b + '|' + a]) * factor / 3600
        B = Bracket(len(seeds))
        seed = {t: i + 1 for i, t in enumerate(seeds)}
        base, base_note = mshsaa_districts(seeds, mdist, B)
        base_line = place_lines(base, seed, 'district', B) if base else None
        for limit in limits:
            out_dir = cfg['out_dir'] if len(limits) == 1 else f"{cfg['out_dir']}/limit_{limit:g}"
            log(f'Class {cls}: {B.D} districts, {len(seeds)} teams, district limit {limit} h '
                f'(up to {args.time_limit:.0f}s)...')
            districts, violations, info = optimize_districts(seeds, tt, args, B, limit, args.next_limit, weights)
            districts = order_districts(districts, seed, B, args.reseed)
            line = place_lines(districts, seed, args.bye_rule, B)
            rng = random.Random(cls * 1000 + int(limit * 10))
            sc = scorecard(line, seeds, rating, tt, B, limit, args.next_limit, args.sims, sigma, rng)
            base_sc = scorecard(base_line, seeds, rating, tt, B, limit, args.next_limit, args.sims, sigma,
                                random.Random(cls * 1000 + int(limit * 10))) if base_line else None
            write_outputs(cfg, out_dir, cls, season, seeds, order, rating, jumps, districts, line, violations, info,
                          tt, args, B, limit, args.next_limit, weights, sc, base_sc, base_line, base_note, factor)
            log(f"Class {cls} @ {limit} h: {len(violations)} violations, avg district trip {sc['chalk_district_game_avg_min']} min, "
                f"top-seed pairs together {sc['top_seed_pairs_same_district']}"
                + (f" (MSHSAA: {base_sc['chalk_district_game_avg_min']} min, {base_sc['top_seed_pairs_same_district']} pairs)" if base_sc else ''))
            b = base_sc or {}
            summary.append(f"| {cls} | {limit} h | {len(violations)} | {sc['chalk_district_game_avg_min']} / {b.get('chalk_district_game_avg_min', '-')} | "
                           f"{sc['top_seed_pairs_same_district']} / {b.get('top_seed_pairs_same_district', '-')} | "
                           f"{sc['exp_top8_in_quarterfinals']} / {b.get('exp_top8_in_quarterfinals', '-')} | "
                           f"{sc['weakest_district_best_seed']} / {b.get('weakest_district_best_seed', '-')} |")
    if calib_rows:
        summary += ['', '## Calibration pairs', '', '| Team | Team | Real (min) | OSRM (min) |', '|---|---|---|---|']
        summary += [f'| {a} | {b} | {m} | {o} |' for a, b, m, o in calib_rows]
    summary += ['', 'MSHSAA columns use MSHSAA\'s actual districts with the same seeds and the same scoring '
                '(seeding inside each district by rating, district N paired with N+1).']
    os.makedirs(cfg['out_dir'], exist_ok=True)
    with open(f"{cfg['out_dir']}/README.md", 'w') as f:
        f.write('\n'.join(summary) + '\n')
    log(f"Done. See {cfg['out_dir']}/.")
 
 
if __name__ == '__main__':
    main()
