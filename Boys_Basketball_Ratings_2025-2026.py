import requests
from bs4 import BeautifulSoup
import json
import csv
import re
import pandas as pd
from datetime import datetime, date, timedelta
import time
 
# ---------------------------------------------------------------------------
# CONFIGURATION
# ---------------------------------------------------------------------------
 
SEASON_YEAR   = 2025   # NOTE: labeled by the year the season *starts* (Nov 2025),
                        # matching football's convention. Basketball runs Nov->Mar,
                        # so confirm this against whatever year-label your existing
                        # boys basketball repo/classifications.json already uses
                        # before trusting the output filenames.
SEASON_START  = date(2025, 11, 1)   # a couple weeks before games typically tip off,
                                     # to safely catch early jamborees/scrimmage results
SEASON_END    = date(2026, 4, 1)
BASE_URL      = "https://www.mshsaa.org/activities/scoreboard.aspx?alg=5&date={}"
MAX_POINTS    = 150    # basketball scores run higher than football; 150 comfortably
                        # covers OT shootouts without being so loose it lets garbage
                        # scrape values through. Tighten if you see this ever binding.
OUTPUT_PATH   = f"boys_basketball_ratings_{SEASON_YEAR}.json"
CSV_PATH      = f"boys_basketball_scoreboard_{SEASON_YEAR}.csv"
CLASSIFICATIONS_PATH  = "classifications.json"
SCHOOLS_CSV           = "mshsaa_schools.csv"
ITERATIONS            = 1000
LEARNING_RATE         = 0.1
 
# --- v2 rating engine settings (soft weighting + shrinkage, replaces the
#     old hard Phase-2 cutoff) ---
# NOTE: these three were tuned for football's scoring distribution (0-100,
# blowouts often 40-60+ pts). Basketball margins are compressed onto a lower
# scale, so treat these as starting points to recalibrate the same way you
# did alg/class-count/constants for the soccer buildout, not as safe defaults:
COMPETITIVE_THRESHOLD = 30    # half-weight point of the smooth decay curve
REGULARIZATION_K      = 3.0   # pseudo-games added to every team's denominator (shrinkage)
MOV_CAP               = 25    # max points of "error" any single game can contribute
 
# ---------------------------------------------------------------------------
# MANUAL GAMES (not listed on MSHSAA Scoreboard)
# ---------------------------------------------------------------------------
# Add any games missing from the MSHSAA scoreboard here.
# Format: ("YYYY-MM-DD", "Team 1 Name", score1, "Team 2 Name", score2)
# Team names must match exactly the names in classifications.json.
 
MANUAL_GAMES = [
    # Football's Russellville backfill doesn't apply here -- this is a fresh
    # sport with its own scoreboard gaps. Populate after a first full scrape
    # + report_missing_teams() pass identifies what alg=5 is missing.
]
 
# ---------------------------------------------------------------------------
# SCORE CORRECTIONS (from Suspicious_Scores_-_Boys_Basketball.xlsx review)
# ---------------------------------------------------------------------------
# Fixes for games that scraped with a bad score. Matched by date + the two
# team names (order-independent), then each team's score is set explicitly
# -- so this works regardless of which team the scraper put in the home
# slot vs. the away slot.
# Format: ("YYYY-MM-DD", "Team A", correct_score_A, "Team B", correct_score_B)
 
SCORE_CORRECTIONS = [
    # Build from a Boys_Basketball scoreboard review workbook, same pattern
    # as the football one -- don't reuse football's corrections, these are
    # per-game and sport-specific.
]
 
# ---------------------------------------------------------------------------
# EXCLUDED GAMES (from Suspicious_Scores_-_Boys_Basketball.xlsx review)
# ---------------------------------------------------------------------------
# Games to drop entirely -- confirmed bad/unverifiable entries rather than
# fixable score typos. Matched by date + the two team names (order-independent).
# Format: ("YYYY-MM-DD", "Team A", "Team B")
 
EXCLUDED_GAMES = [
    # Football's exclusions are specific to those games -- start empty and
    # add basketball-specific bad/unverifiable entries as you find them.
]
 
HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/120.0.0.0 Safari/537.36"
    ),
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
    "Accept-Language": "en-US,en;q=0.5",
    "Referer": "https://www.mshsaa.org/"
}
 
# ---------------------------------------------------------------------------
# HTTP SESSION (connection reuse + retry on transient failures)
# ---------------------------------------------------------------------------
# Days that timeout right at the 20s ceiling get one retry with a short
# backoff before we give up on them. A shared Session reuses the underlying
# TCP connection instead of opening a fresh one per request, which by
# itself often reduces the frequency of these near-ceiling timeouts.
 
def build_session():
    from requests.adapters import HTTPAdapter
    try:
        from urllib3.util.retry import Retry
    except ImportError:
        from requests.packages.urllib3.util.retry import Retry
 
    session = requests.Session()
    retry = Retry(
        total=1,                      # one retry after the first failure
        connect=1,
        read=1,
        backoff_factor=1.5,           # short pause before the retry
        status_forcelist=[500, 502, 503, 504],
        raise_on_status=False,
    )
    adapter = HTTPAdapter(max_retries=retry, pool_connections=1, pool_maxsize=1)
    session.mount("https://", adapter)
    session.mount("http://", adapter)
    return session
 
# ---------------------------------------------------------------------------
# CLASSIFICATIONS
# ---------------------------------------------------------------------------
 
def load_classifications(path=CLASSIFICATIONS_PATH):
    """Return team_to_class and team_to_district dicts keyed by school name."""
    with open(path) as f:
        data = json.load(f)
    team_to_class    = {}
    team_to_district = {}
    for entry in data["teams"]:
        school = entry["school"]
        team_to_class[school]    = entry["classification"]
        team_to_district[school] = entry["district"]
    return team_to_class, team_to_district
 
 
# ---------------------------------------------------------------------------
# NAME RESOLUTION
# ---------------------------------------------------------------------------
 
def build_id_to_classname(team_to_class, schools_csv=SCHOOLS_CSV):
    """
    Build { school_id_str : classification_name } by exact-matching
    mshsaa_schools.csv names to classifications.json names after stripping
    the ' High School' suffix. No fuzzy matching used.
 
    MANUAL_OVERRIDES covers the 21 schools whose mshsaa_schools.csv name
    does not match their classifications.json name. IDs were looked up
    directly from the MSHSAA scoreboard pages.
    """
    # IMPORTANT: football's MANUAL_OVERRIDES are keyed by school ID, and the
    # IDs themselves are stable across sports (same MSHSAA school record).
    # But the *co-op arrangement* is not guaranteed to match -- a school can
    # co-op for football while fielding its own boys basketball team, or
    # vice versa. Don't assume this list transfers as-is. Regenerate it the
    # same way it was built originally: run this script once with an empty
    # dict, let report_missing_teams() surface every classifications.json
    # school with zero scraped games, then look up each one's real s= ID
    # from the alg=5 scoreboard/schedule page and add it here.
    MANUAL_OVERRIDES = {
    }
 
    df = pd.read_csv(schools_csv)
    known_class_names = set(team_to_class.keys())
 
    id_to_classname = {}
    for _, row in df.iterrows():
        full_name = row["school_name"]
        sid       = str(row["school_id"])
        stripped  = full_name.replace(" High School", "").strip()
 
        if stripped in known_class_names:
            id_to_classname[sid] = stripped
        elif full_name in known_class_names:
            id_to_classname[sid] = full_name
 
    # Apply manual overrides last so they always take priority
    id_to_classname.update(MANUAL_OVERRIDES)
 
    print(f"  [name-resolve] {len(id_to_classname)} schools mapped by ID "
          f"({len(MANUAL_OVERRIDES)} via manual overrides)")
    return id_to_classname
 
 
def resolve_name(cell, id_to_classname, known_teams):
    """
    Resolve a scoreboard table cell to a classification name.
 
    Step 1: Extract s= ID from href → look up in id_to_classname.
            Handles renamed/merged schools (e.g. 'Scott City with Chaffee'
            → 'Scott City') because the ID in the href never changes.
    Step 2: Exact match of display text against known_teams.
            Handles co-op names that exist in classifications as-is.
    Returns None if unresolvable — game will be skipped.
    """
    a = cell.find("a", href=lambda h: h and "/MySchool/Schedule.aspx" in h)
    if not a:
        return None
 
    # Step 1: ID-based lookup
    href  = a.get("href", "")
    match = re.search(r"[?&]s=(\d+)", href, re.IGNORECASE)
    if match:
        sid = match.group(1)
        if sid in id_to_classname:
            return id_to_classname[sid]
 
    # Step 2: Exact display text match
    display_text = a.get_text(strip=True)
    if display_text in known_teams:
        return display_text
 
    return None
 
 
# ---------------------------------------------------------------------------
# SCRAPING
# ---------------------------------------------------------------------------
 
def is_mshsaa_team(cell):
    return cell.find(
        "a", href=lambda h: h and "/MySchool/Schedule.aspx" in h
    ) is not None
 
 
def parse_score(text):
    text = text.strip()
    if not text:
        return None
    try:
        score = int(text)
    except ValueError:
        return None
    return score if 0 <= score <= MAX_POINTS else None
 
 
def is_forfeit(c1, c2):
    return "forfeit" in (c1.get_text() + c2.get_text()).lower()
 
 
def scrape_date(target_date, id_to_classname, known_teams, session):
    url = BASE_URL.format(target_date.strftime("%m%d%Y"))
    try:
        # (connect_timeout, read_timeout) -- 10s to connect, 25s to read.
        # 25s (vs. the old flat 20s) gives borderline-slow responses (the
        # ~20.6-20.9s ones you saw) a real chance to finish instead of
        # being cut off right before they would have succeeded.
        resp = session.get(url, timeout=(10, 25), headers=HEADERS)
        resp.raise_for_status()
    except requests.exceptions.Timeout as e:
        print(f"  TIMEOUT {target_date}: {e}")
        return [], "timeout"
    except requests.RequestException as e:
        print(f"  Failed {target_date}: {e}")
        return [], "error"
 
    soup  = BeautifulSoup(resp.text, "html.parser")
    games = []
 
    for table in soup.find_all("table"):
        rows = table.find_all("tr")
        if len(rows) < 3:
            continue
        if "final" not in rows[-1].get_text().lower():
            continue
 
        t1c = rows[1].find_all("td")
        t2c = rows[2].find_all("td")
        if len(t1c) < 3 or len(t2c) < 3:
            continue
        if not is_mshsaa_team(t1c[1]) or not is_mshsaa_team(t2c[1]):
            continue
        if is_forfeit(t1c[1], t2c[1]):
            continue
 
        name1 = resolve_name(t1c[1], id_to_classname, known_teams)
        name2 = resolve_name(t2c[1], id_to_classname, known_teams)
 
        if name1 is None or name2 is None:
            continue
 
        s1 = parse_score(t1c[2].get_text())
        s2 = parse_score(t2c[2].get_text())
        if s1 is None or s2 is None:
            continue
 
        games.append((
            target_date.strftime("%Y-%m-%d"),
            name1, s1,
            name2, s2
        ))
 
    return games, None
 
 
def scrape_full_season(id_to_classname, known_teams):
    all_games     = []
    current       = SEASON_START
    scrape_t0     = time.perf_counter()
    slow_days     = []   # (date, seconds) for anything taking > 3s
    failed_days   = []   # (date, reason) for anything that never succeeded
    session       = build_session()
 
    while current <= min(SEASON_END, date.today()):
        day_t0 = time.perf_counter()
        print(f"  Scraping {current}...", end=" ", flush=True)
        day_games, fail_reason = scrape_date(current, id_to_classname, known_teams, session)
        all_games.extend(day_games)
        day_elapsed = time.perf_counter() - day_t0
        print(f"{len(day_games)} games ({day_elapsed:.1f}s)")
        if day_elapsed > 3.0:
            slow_days.append((current, day_elapsed))
        if fail_reason is not None:
            failed_days.append((current, fail_reason))
        current += timedelta(days=1)
        time.sleep(0.5)
 
    scrape_elapsed = time.perf_counter() - scrape_t0
    print(f"\n  [TIMING] Scraping took {scrape_elapsed:.1f}s total "
          f"for {len(all_games)} games.")
    if slow_days:
        print(f"  [TIMING] {len(slow_days)} slow day(s) (>3s each):")
        for d, secs in slow_days:
            print(f"    {d}: {secs:.1f}s")
    if failed_days:
        print(f"\n  *** {len(failed_days)} date(s) NEVER returned data, "
              f"even after retry -- these dates may be missing real "
              f"games. Check them manually against MSHSAA and add via "
              f"MANUAL_GAMES if needed: ***")
        for d, reason in failed_days:
            print(f"    {d} ({reason})")
    else:
        print("  All dates returned successfully -- no known data gaps "
              "from scraping failures.")
    return all_games
 
 
def apply_score_corrections(all_games, corrections=SCORE_CORRECTIONS):
    """
    Fix known-bad scores in place. Matches each game by date + the two team
    names (order-independent), then overwrites each named team's score with
    the corrected value -- regardless of which position (t1/t2) that team
    ended up in during scraping.
    """
    lookup = {}
    for date_str, team_a, score_a, team_b, score_b in corrections:
        lookup[(date_str, frozenset([team_a, team_b]))] = {team_a: score_a, team_b: score_b}
 
    corrected = 0
    fixed_games = []
    for date_str, t1, s1, t2, s2 in all_games:
        key = (date_str, frozenset([t1, t2]))
        fix = lookup.get(key)
        if fix is not None:
            new_s1 = fix.get(t1, s1)
            new_s2 = fix.get(t2, s2)
            if (new_s1, new_s2) != (s1, s2):
                corrected += 1
            fixed_games.append((date_str, t1, new_s1, t2, new_s2))
        else:
            fixed_games.append((date_str, t1, s1, t2, s2))
 
    if corrected:
        print(f"  Corrected {corrected} game score(s) via SCORE_CORRECTIONS.")
    else:
        print("  No SCORE_CORRECTIONS matched (nothing changed).")
 
    return fixed_games
 
 
def apply_exclusions(all_games, exclusions=EXCLUDED_GAMES):
    """
    Drop games confirmed bad/unverifiable. Matches by date + the two team
    names (order-independent).
    """
    exclude_keys = {(date_str, frozenset([team_a, team_b]))
                     for date_str, team_a, team_b in exclusions}
 
    filtered_games = [
        g for g in all_games
        if (g[0], frozenset([g[1], g[3]])) not in exclude_keys
    ]
 
    removed = len(all_games) - len(filtered_games)
    if removed:
        print(f"  Removed {removed} excluded game(s) via EXCLUDED_GAMES.")
    else:
        print("  No EXCLUDED_GAMES matched (nothing removed).")
 
    return filtered_games
 
 
def deduplicate_games(all_games):
    """
    Remove duplicate games where the same two teams played on the same date
    with the same scores, regardless of which team is listed as home or away.
 
    A game is considered a duplicate if another game exists with:
      - The same date
      - The same two team names (in either order)
      - The same two scores (in either order)
 
    The key is built from a frozenset of (team, score) pairs so that
    (Date, Team A, 54, Team B, 13) and (Date, Team B, 13, Team A, 54)
    produce the same key and only one is kept.
    """
    seen         = set()
    unique_games = []
    duplicates   = 0
 
    for game in all_games:
        date_str, t1, s1, t2, s2 = game
        # Key is date + frozenset of team names only — order independent.
        # Scores are intentionally excluded so that (Team A home, Team B away)
        # and (Team B home, Team A away) on the same date are always treated
        # as the same game regardless of which score appears first.
        key = (date_str, frozenset([t1, t2]))
        if key in seen:
            duplicates += 1
            continue
        seen.add(key)
        unique_games.append(game)
 
    if duplicates:
        print(f"  Removed {duplicates} duplicate game(s). "
              f"{len(unique_games)} unique games remain.")
    else:
        print(f"  No duplicates found. {len(unique_games)} games.")
 
    return unique_games
 
 
def report_missing_teams(all_games, team_to_class):
    """
    After scraping is complete, compare every team in classifications.json
    against the teams that actually appeared in scraped games.
    Print only the teams that have zero games — these are the ones that
    genuinely need attention (either their ID needs adding or their
    classifications.json name needs correcting).
    """
    teams_with_games = set()
    for _, t1, _, t2, _ in all_games:
        teams_with_games.add(t1)
        teams_with_games.add(t2)
 
    missing = sorted(
        t for t in team_to_class if t not in teams_with_games
    )
 
    if missing:
        print(f"\n  MISSING TEAMS: {len(missing)} classification schools have "
              f"no games in the scraped data.")
        print(f"  These teams need attention — either their MSHSAA page shows")
        print(f"  a different name than classifications.json, or they did not")
        print(f"  play any games this season.")
        print(f"  Missing: {missing}\n")
    else:
        print("\n  All classification schools have at least one game. \n")
 
 
# ---------------------------------------------------------------------------
# CSV OUTPUT
# ---------------------------------------------------------------------------
 
def save_csv(all_games):
    with open(CSV_PATH, "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["Date", "Home Team", "Home Score", "Away Team", "Away Score"])
        for date_str, t1, s1, t2, s2 in all_games:
            writer.writerow([date_str, t1, s1, t2, s2])
    print(f"Saved {len(all_games)} games to {CSV_PATH}")
 
 
# ---------------------------------------------------------------------------
# RATING ENGINE (v2 -- soft competitiveness weighting + shrinkage regularization)
# ---------------------------------------------------------------------------
#
# Replaces the old two-phase (all games, then hard <=40pt cutoff) approach.
# A dominant team no longer has its rating fully decided by 1-2 close games:
#   1. competitiveness_weight() gives every game a smooth weight based on
#      the current rating gap, instead of an all-or-nothing 40-point cutoff.
#   2. REGULARIZATION_K shrinks updates for teams with little competitive
#      signal, instead of letting a tiny sample fully drive their rating.
#   3. MOV_CAP bounds how much error any single game -- even a fully-weighted
#      one -- can contribute, so no one result can swing a rating too hard.
 
def competitiveness_weight(gap, scale=COMPETITIVE_THRESHOLD):
    """
    Smooth weight in (0, 1] based on the current OVR gap between two teams.
    gap=0            -> weight 1.0 (fully counted)
    gap=scale (40)   -> weight 0.5 (half counted)
    gap=2*scale (80) -> weight 0.2 (mostly discounted, never fully zero)
    """
    return 1.0 / (1.0 + (gap / scale) ** 2)
 
 
def run_iterations(games, teams, off_rating, def_rating, league_avg,
                   iterations, phase_label="Fit"):
    for iteration in range(iterations):
        off_error  = {t: 0.0 for t in teams}
        def_error  = {t: 0.0 for t in teams}
        weight_sum = {t: 0.0 for t in teams}
 
        for t1, t2, actual_s1, actual_s2 in games:
            gap = abs((off_rating[t1] + def_rating[t1]) -
                      (off_rating[t2] + def_rating[t2]))
            w = competitiveness_weight(gap)
 
            predicted_s1 = off_rating[t1] - def_rating[t2] + league_avg
            predicted_s2 = off_rating[t2] - def_rating[t1] + league_avg
 
            error_s1 = actual_s1 - predicted_s1
            error_s2 = actual_s2 - predicted_s2
 
            # MOV cap: bound the raw error before it's weighted/accumulated
            error_s1 = max(-MOV_CAP, min(MOV_CAP, error_s1))
            error_s2 = max(-MOV_CAP, min(MOV_CAP, error_s2))
 
            off_error[t1] += w * error_s1
            off_error[t2] += w * error_s2
            def_error[t1] += -w * error_s2
            def_error[t2] += -w * error_s1
 
            weight_sum[t1] += w
            weight_sum[t2] += w
 
        for team in teams:
            # Shrinkage: denominator is (weighted games) + K, not just raw
            # games played. Teams with low competitive weight get smaller,
            # more conservative updates instead of being fully driven by
            # 1-2 games.
            denom = weight_sum[team] + REGULARIZATION_K
            off_rating[team] += (off_error[team] / denom) * LEARNING_RATE
            def_rating[team] += (def_error[team] / denom) * LEARNING_RATE
 
        if (iteration + 1) % 100 == 0:
            print(f"  [{phase_label}] Iteration {iteration + 1}/{iterations} complete")
 
 
def calculate_ratings(all_games, iterations=ITERATIONS):
    games = [(t1, t2, s1, s2) for _, t1, s1, t2, s2 in all_games]
 
    teams = list({t for t1, t2, _, _ in games for t in (t1, t2)})
    if not teams:
        return {}, {}, {}, 0
 
    all_scores = [s for _, _, s1, s2 in games for s in (s1, s2)]
    league_avg = sum(all_scores) / len(all_scores)
    print(f"  League average: {league_avg:.2f} points per game")
 
    off_rating = {t: 0.0 for t in teams}
    def_rating = {t: 0.0 for t in teams}
 
    print(f"\n  Running rating fit ({iterations} iterations, soft-weighted "
          f"by competitiveness [scale={COMPETITIVE_THRESHOLD}], "
          f"shrinkage K={REGULARIZATION_K}, MOV cap={MOV_CAP})...")
    print(f"  [TIMING] {len(teams)} teams, {len(games)} games going into the fit.")
    engine_t0 = time.perf_counter()
    run_iterations(games, teams, off_rating, def_rating, league_avg,
                   iterations=iterations, phase_label="Fit")
    print(f"  [TIMING] Rating fit took {time.perf_counter() - engine_t0:.1f}s.")
 
    ovr_rating = {t: round(off_rating[t] + def_rating[t], 2) for t in teams}
    return off_rating, def_rating, ovr_rating, league_avg
# ---------------------------------------------------------------------------
# JSON OUTPUT
# ---------------------------------------------------------------------------
 
def build_team_entries(off_rating, def_rating, ovr_rating,
                       team_to_class, team_to_district,
                       class_filter=None):
    all_teams = list(ovr_rating.keys())
 
    pool = (
        [t for t in all_teams if team_to_class.get(t) == class_filter]
        if class_filter is not None
        else all_teams
    )
 
    ovr_sorted = sorted(pool, key=lambda t: ovr_rating[t], reverse=True)
    off_sorted = sorted(pool, key=lambda t: off_rating[t], reverse=True)
    def_sorted = sorted(pool, key=lambda t: def_rating[t], reverse=True)
 
    ovr_rank = {t: i + 1 for i, t in enumerate(ovr_sorted)}
    off_rank = {t: i + 1 for i, t in enumerate(off_sorted)}
    def_rank = {t: i + 1 for i, t in enumerate(def_sorted)}
 
    return [
        {
            "ovr_rank":       ovr_rank[t],
            "school":         t,
            "classification": team_to_class.get(t),
            "district":       team_to_district.get(t),
            "ovr_rating":     ovr_rating[t],
            "off_rating":     round(off_rating[t], 2),
            "off_rank":       off_rank[t],
            "def_rating":     round(def_rating[t], 2),
            "def_rank":       def_rank[t],
        }
        for t in ovr_sorted
    ]
 
 
def save_overall_json(off_rating, def_rating, ovr_rating, league_avg,
                      team_to_class, team_to_district):
    entries = build_team_entries(off_rating, def_rating, ovr_rating,
                                 team_to_class, team_to_district)
    output = {
        "last_updated":   datetime.now().strftime("%B %d, %Y at %I:%M %p"),
        "league_average": round(league_avg, 2),
        "teams": entries,
    }
    with open(OUTPUT_PATH, "w") as f:
        json.dump(output, f, indent=2)
 
    print(f"Saved {len(entries)} teams to {OUTPUT_PATH}")
    print("Top 5 overall:")
    for e in entries[:5]:
        print(f"  {e['ovr_rank']}. {e['school']} (Class {e['classification']}) "
              f"| OVR: {e['ovr_rating']:+.2f} "
              f"| OFF: {e['off_rating']:+.2f} "
              f"| DEF: {e['def_rating']:+.2f}")
 
 
def save_class_jsons(off_rating, def_rating, ovr_rating, league_avg,
                     team_to_class, team_to_district):
    for cls in range(1, 7):
        entries = build_team_entries(off_rating, def_rating, ovr_rating,
                                     team_to_class, team_to_district,
                                     class_filter=cls)
        if not entries:
            print(f"  Class {cls}: no teams found — skipping.")
            continue
 
        path = f"boys_basketball_ratings_{SEASON_YEAR}_class{cls}.json"
        output = {
            "last_updated":   datetime.now().strftime("%B %d, %Y at %I:%M %p"),
            "league_average": round(league_avg, 2),
            "classification": cls,
            "teams": entries,
        }
        with open(path, "w") as f:
            json.dump(output, f, indent=2)
 
        print(f"  Class {cls}: {len(entries)} teams → {path}")
        print("    Top 3: " + " | ".join(
            f"{e['ovr_rank']}. {e['school']} ({e['ovr_rating']:+.2f})"
            for e in entries[:3]
        ))
 
 
 
# ---------------------------------------------------------------------------
# CSV RANKINGS OUTPUT
# ---------------------------------------------------------------------------
 
def save_rankings_csv(off_rating, def_rating, ovr_rating,
                      team_to_class, team_to_district,
                      class_filter=None):
    """
    Save a rankings CSV for either all teams (class_filter=None) or a
    specific class.  Rankings (OFF Rank, DEF Rank, OVR Rank) are computed
    within the pool so class CSVs show class-specific ranks.
 
    Columns: School, OFF Rating, DEF Rating, OVR Rating,
             OFF Rank, DEF Rank, OVR Rank
    """
    all_teams = list(ovr_rating.keys())
 
    pool = (
        [t for t in all_teams if team_to_class.get(t) == class_filter]
        if class_filter is not None
        else all_teams
    )
 
    if not pool:
        label = f"Class {class_filter}" if class_filter else "Overall"
        print(f"  {label}: no teams — skipping CSV.")
        return
 
    ovr_sorted = sorted(pool, key=lambda t: ovr_rating[t], reverse=True)
    off_sorted = sorted(pool, key=lambda t: off_rating[t], reverse=True)
    def_sorted = sorted(pool, key=lambda t: def_rating[t], reverse=True)
 
    ovr_rank = {t: i + 1 for i, t in enumerate(ovr_sorted)}
    off_rank = {t: i + 1 for i, t in enumerate(off_sorted)}
    def_rank = {t: i + 1 for i, t in enumerate(def_sorted)}
 
    rows = [
        {
            "School":      t,
            "OFF Rating":  round(off_rating[t], 2),
            "DEF Rating":  round(def_rating[t], 2),
            "OVR Rating":  round(ovr_rating[t], 2),
            "OFF Rank":    off_rank[t],
            "DEF Rank":    def_rank[t],
            "OVR Rank":    ovr_rank[t],
        }
        for t in ovr_sorted
    ]
 
    df = pd.DataFrame(rows, columns=[
        "School", "OFF Rating", "DEF Rating", "OVR Rating",
        "OFF Rank", "DEF Rank", "OVR Rank"
    ])
 
    if class_filter is None:
        path  = f"boys_basketball_rankings_{SEASON_YEAR}_all.csv"
        label = "All teams"
    else:
        path  = f"boys_basketball_rankings_{SEASON_YEAR}_class{class_filter}.csv"
        label = f"Class {class_filter}"
 
    df.to_csv(path, index=False)
    print(f"  {label}: {len(df)} teams — {path}")
 
 
def save_all_rankings_csvs(off_rating, def_rating, ovr_rating,
                           team_to_class, team_to_district):
    """Save overall + one CSV per class (1-6)."""
    save_rankings_csv(off_rating, def_rating, ovr_rating,
                      team_to_class, team_to_district,
                      class_filter=None)
    for cls in range(1, 7):
        save_rankings_csv(off_rating, def_rating, ovr_rating,
                          team_to_class, team_to_district,
                          class_filter=cls)
 
# ---------------------------------------------------------------------------
# MAIN
# ---------------------------------------------------------------------------
 
if __name__ == "__main__":
    print(f"=== MSHSAA Boys Basketball Ratings {SEASON_YEAR} ===")
 
    print("\nLoading classifications...")
    team_to_class, team_to_district = load_classifications()
    known_teams = set(team_to_class.keys())
    print(f"  Loaded {len(team_to_class)} teams from {CLASSIFICATIONS_PATH}")
 
    print("\nBuilding school ID → classification name lookup...")
    id_to_classname = build_id_to_classname(team_to_class, SCHOOLS_CSV)
 
    print("\nScraping season scoreboard...")
    all_games = scrape_full_season(id_to_classname, known_teams)
    print(f"\nTotal valid games (before deduplication): {len(all_games)}")
    if not all_games:
        print("No games found — exiting.")
        exit(1)
 
    if MANUAL_GAMES:
        print(f"\nAdding {len(MANUAL_GAMES)} manual game(s)...")
        all_games.extend(MANUAL_GAMES)
 
    print("\nApplying score corrections...")
    all_games = apply_score_corrections(all_games)
 
    print("\nApplying game exclusions...")
    all_games = apply_exclusions(all_games)
 
    print("\nDeduplicating games...")
    all_games = deduplicate_games(all_games)
 
    print("\nChecking for missing teams...")
    report_missing_teams(all_games, team_to_class)
 
    print("Saving scoreboard CSV...")
    save_csv(all_games)
 
    print(f"\nRunning ratings engine "
          f"({ITERATIONS} Phase 1 + {ITERATIONS} Phase 2 iterations)...")
    off_rating, def_rating, ovr_rating, league_avg = calculate_ratings(all_games)
 
    print("\nSaving overall ratings JSON...")
    save_overall_json(off_rating, def_rating, ovr_rating, league_avg,
                      team_to_class, team_to_district)
 
    print("\nSaving per-class ratings JSONs...")
    save_class_jsons(off_rating, def_rating, ovr_rating, league_avg,
                     team_to_class, team_to_district)
 
    print("\nSaving rankings CSVs...")
    save_all_rankings_csvs(off_rating, def_rating, ovr_rating,
                           team_to_class, team_to_district)
 
    print("\n=== Done ===")
