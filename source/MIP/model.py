from pulp import *
import sys

def optimize(n, gap=0.01):
    # Validate input
    if n % 2 != 0:
        raise ValueError("Number of teams must be even")
    if n < 6:
        raise ValueError("Number of teams must be at least 6")

    W = n - 1   # total weeks
    P = n // 2  # total periods
    M = P * W   # total matches

    # Generate Round Robin schedule using circle method
    # rb[p][w][s] gives the team for period p, week w, slot s
    rb = {}
    for p in range(P):
        rb[p] = {}
        for w in range(W):
            rb[p][w] = {}
            for s in range(2):
                if s == 0:  # Home team
                    if p == 0:
                        rb[p][w][s] = n - 1 if w % 2 == 0 else w
                    else:
                        rb[p][w][s] = (p + w) % (n - 1)
                else:  # Away team
                    if p == 0:
                        rb[p][w][s] = w if w % 2 == 0 else n - 1
                    else:
                        rb[p][w][s] = (n - p + w - 1) % (n - 1)

    # Flatten to list of matches: matches[m][0/1]
    matches = {}
    match_id = 0
    for w in range(W):
        for p in range(P):
            matches[match_id] = {}
            matches[match_id][0] = rb[p][w][0]
            matches[match_id][1] = rb[p][w][1]
            match_id += 1

    # Create the model
    model = LpProblem("RoundRobinScheduling", LpMinimize)

    # Decision Variables
    # matches_one_hot[m, p, w] = 1 if match m is scheduled in period p of week w
    matches_one_hot = LpVariable.dicts("matches_oh",
                              ((m, p, w) for m in range(M) for p in range(P) for w in range(W)),
                              cat='Binary')

    # first_is_home[m] = 1 if in match m the first team is home (0 if second team is home)
    first_is_home = LpVariable.dicts("first_is_home", range(M), cat='Binary')

    # Linearization: y[m,p,w] = matches_one_hot[m,p,w] * first_is_home[m]
    y = LpVariable.dicts("y",
                              ((m, p, w) for m in range(M) for p in range(P) for w in range(W)),
                              cat='Binary')

    # Home and away counts for each team
    home_count = LpVariable.dicts("home", range(n), lowBound=0, upBound=W, cat='Integer')
    away_count = LpVariable.dicts("away", range(n), lowBound=0, upBound=W, cat='Integer')

    # Auxiliary variables for absolute differences
    diff = LpVariable.dicts("diff", range(n), lowBound=0, cat='Integer')

    # Objective variable
    imbalance = LpVariable("imbalance", lowBound=0, cat='Integer')


    # Linearization constraints: y[m,p,w] = matches_one_hot[m,p,w] * first_is_home[m]   (if y[m,p,w]=1 then matches m is played with first team home)
    for m in range(M):
        for p in range(P):
            for w in range(W):
                model += y[m, p, w] <= matches_one_hot[m, p, w], f"lin1_{m}_{p}_{w}"
                model += y[m, p, w] <= first_is_home[m], f"lin2_{m}_{p}_{w}"
                model += y[m, p, w] >= matches_one_hot[m, p, w] + first_is_home[m] - 1, f"lin3_{m}_{p}_{w}"

    # Constraints

    # 1. Each match is played exactly once
    for m in range(M):
        model += lpSum(matches_one_hot[m, p, w] for p in range(P) for w in range(W)) == 1, f"match_{m}_once"

    # 2. Each period-week slot has exactly one match
    for p in range(P):
        for w in range(W):
            model += lpSum(matches_one_hot[m, p, w] for m in range(M)) == 1, f"slot_{p}_{w}_filled"

    # 3. Matches from week w must be scheduled in week w
    for w in range(W):
        week_matches = list(range(w * P, (w + 1) * P))
        for p in range(P):
            model += lpSum(matches_one_hot[m, p, w] for m in week_matches) == 1, f"week_{w}_integrity_{p}"

    # 4. Each team plays at most 2 times in each period across all weeks
    for p in range(P):
        for t in range(n):
            appearances = []
            for w in range(W):
                for m in range(M):
                    team1, team2 = matches[m][0], matches[m][1]
                    if team1 == t or team2 == t:
                        appearances.append(matches_one_hot[m, p, w])

            if appearances:
                model += lpSum(appearances) <= 2, f"team_{t}_period_{p}_limit"

    # 5. Calculate home counts
    for t in range(n):
        home_games = []
        for m in range(M):
            team1, team2 = matches[m][0], matches[m][1]
            for p in range(P):
                for w in range(W):
                    if team1 == t:
                        # Team t is home when first_is_home[m] = 1, so use y[m,p,w]
                        home_games.append(y[m, p, w])
                    elif team2 == t:
                        # Team t is home when first_is_home[m] = 0, so use matches_one_hot[m,p,w] - y[m,p,w]
                        home_games.append(matches_one_hot[m, p, w] - y[m, p, w])

        model += home_count[t] == lpSum(home_games), f"home_count_{t}"

    # 6. Calculate away counts
    for t in range(n):
        away_games = []
        for m in range(M):
            team1, team2 = matches[m][0], matches[m][1]
            for p in range(P):
                for w in range(W):
                    if team1 == t:
                        # Team t is away when first_is_home[m] = 0, so use matches_one_hot[m,p,w] - y[m,p,w]
                        away_games.append(matches_one_hot[m, p, w] - y[m, p, w])
                    elif team2 == t:
                        # Team t is away when first_is_home[m] = 1, so use y[m,p,w]
                        away_games.append(y[m, p, w])

        model += away_count[t] == lpSum(away_games), f"away_count_{t}"

    # 7. Each team plays exactly W games (home + away = W)
    for t in range(n):
        model += home_count[t] + away_count[t] == W, f"team_{t}_total_games"

    # 8. Calculate absolute differences
    for t in range(n):
        model += diff[t] >= home_count[t] - away_count[t], f"diff_{t}_pos"
        model += diff[t] >= away_count[t] - home_count[t], f"diff_{t}_neg"

    # 9. Total imbalance
    model += imbalance == lpSum(diff[t] for t in range(n)), "total_imbalance"

    # 10. Minimum imbalance
    model += imbalance >= n, "min_imbalance"

    # SYMMETRY BREAKING: First match (0) goes to period 0, week 0
    model += matches_one_hot[0, 0, 0] == 1, "symmetry_first_match"

    # SYMMETRY BREAKING: lex order between periods
    for p in range(P - 1):
        model += (lpSum(m * matches_one_hot[m, p, w] for m in range(M) for w in range(W)) <=
                  lpSum(m * matches_one_hot[m, p + 1, w] for m in range(M) for w in range(W)))

    # Objective: Minimize total imbalance
    model += imbalance, "objective"

    # Solve
    solver = PULP_CBC_CMD( msg=False, gapRel=gap, threads=1)
    model.solve(solver)

    # Extract results
    result = {
        'status': LpStatus[model.status],
        'schedule': {},
        'imbalance': None,
        'home_away_counts': {}
    }

    if LpStatus[model.status] == "Optimal" or LpStatus[model.status] == "Not Solved":
        schedule = {}
        for w in range(W):
            schedule[w] = {}
            for p in range(P):
                for m in range(M):
                    if value(matches_one_hot[m, p, w]) and value(matches_one_hot[m, p, w]) > 0.5:
                        team1, team2 = matches[m][0], matches[m][1]
                        h_val = value(first_is_home[m])
                        if h_val and h_val > 0.5:
                            home, away = team1, team2
                        else:
                            home, away = team2, team1
                        schedule[w][p] = (home, away)
        result['schedule'] = schedule

        # Get home/away counts
        home_away_balance = {}
        for t in range(n):
            h_val = value(home_count[t])
            a_val = value(away_count[t])
            d_val = value(diff[t])
            home_away_balance[t] = {
                'home': int(round(h_val)) if h_val else 0,
                'away': int(round(a_val)) if a_val else 0,
                'diff': int(round(d_val)) if d_val else 0
            }
            result['home_away_counts'][t] = (h_val, a_val)

        imb_val = value(imbalance)
        total_imbalance = int(round(imb_val)) if imb_val else 0

        result['imbalance'] = total_imbalance

    return result

def print_schedule(result, n):
    if result['status'] not in ["Optimal", "Not Solved"]:
        print(f"\nOptimization Status: {result['status']}")
        print("Unable to find a solution.\n")
        return

    weeks = range(n - 1)
    periods = range(n // 2)

    print("\n" + "=" * 80)
    print(f"SOLUTION FOUND FOR N = {n}")
    print("=" * 80 + "\n")

    for w in weeks:
        print(f"Week {w + 1}:\n")

        for p in periods:
            home_team, away_team = result['schedule'][w][p]
            print(f"  Period {p + 1}: {home_team} vs {away_team}")

        print()

    print("=" * 80)
    print("HOME/AWAY BALANCE")
    print("=" * 80)

    for t in range(n):
        home_count, away_count = result['home_away_counts'][t]
        diff = abs(home_count - away_count)
        print(
            f"Team {t:2d}: Home={int(home_count):2d}, "
            f"Away={int(away_count):2d}, Difference={int(diff)}"
        )

    print("\n" + "=" * 80)
    print(f"TOTAL IMBALANCE: {result['imbalance']}")
    print("=" * 80 + "\n")


def main():
    if len(sys.argv) != 2:
        print("Usage: python round_robin_scheduler.py <number_of_teams>")
        print("Example: python round_robin_scheduler.py 12")
        sys.exit(1)

    try:
        n = int(sys.argv[1])
    except ValueError:
        print(f"Error: '{sys.argv[1]}' is not a valid integer")
        sys.exit(1)

    # Validate input
    if n < 6:
        print(f"Error: Number of teams must be at least 6 (got {n})")
        sys.exit(1)
    if n % 2 != 0:
        print(f"Error: Number of teams must be even (got {n})")
        sys.exit(1)

    print(f"\nGenerating schedule for {n} teams...")
    print(f"Total weeks: {n - 1}")
    print(f"Matches per week: {n // 2}")
    print(f"Total matches: {(n - 1) * (n // 2)}")
    print("\nOptimizing...\n")

    try:
        # Solve the problem
        result = optimize(n)

        # Print the results
        print_schedule(result, n)

    except ValueError as e:
        print(f"Error: {e}")
        sys.exit(1)
    except Exception as e:
        print(f"Unexpected error: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
