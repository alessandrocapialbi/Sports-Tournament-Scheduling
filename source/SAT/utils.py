from z3 import is_true
import json

def generate_rb_and_flattened(N, W, P, S):
    """
    Generate Round Robin schedule using Circle Method.
    Return W,P,S matrix and flattened W*P, S array
    """
    rb = {}
    for p in P:
        for w in W:
            for s in S:
                if s == 0:  # Home team
                    if p == 0:
                        rb[(p, w, s)] = N - 1 if w % 2 == 0 else w
                    else:
                        rb[(p, w, s)] = (p + w) % (N - 1)
                else:  # Away team
                    if p == 0:
                        rb[(p, w, s)] = w if w % 2 == 0 else N - 1
                    else:
                        rb[(p, w, s)] = (N - p + w - 1) % (N - 1)

    # Flatten to matches array
    matches = {}
    for w in W:
        for p in P:
            for s in S:
                m = w * (N // 2) + p
                matches[m, s] = rb[p, w, s]

    return rb, matches

def calculate_params(N):
    T = range(N)  # Teams
    S = range(2)  # Slots (0=Home, 1=Away)
    W = range(N - 1)  # Weeks
    P = range(N // 2)  # Periods per week
    M = range((N - 1) * (N // 2))  # Total matches
    return T, S, W, P, M


def extract_solution(model, P, W, M, matches_idx_vars, home_is_first_vars=None,
                     home_count_vars=None, away_count_vars=None, diff_vars=None, T=None, N=None):
    """
    Extract solution from Z3 model.

    Args:
        model: Z3 model
        P, W, M: Parameter ranges
        matches_idx_vars: Match index variables
        home_is_first_vars: Optional home orientation variables
        home_count_vars: Optional home count variables
        away_count_vars: Optional away count variables
        diff_vars: Optional difference variables
        T: Optional team range (needed if count vars provided)
        N: Optional number of teams (needed if count vars provided)

    Returns:
        Dictionary with 'solution', 'home_first', 'home_counts', 'away_counts', 'diffs', 'imbalance'
    """
    solution = {}
    home_first = {}

    # Extract match assignments
    for p in P:
        for w in W:
            for m in M:
                if is_true(model.evaluate(matches_idx_vars[p, w][m])):
                    solution[p, w] = m
                    break

    # Extract home/away orientation if provided
    if home_is_first_vars is not None:
        for p in P:
            for w in W:
                home_first[p, w] = is_true(model.evaluate(home_is_first_vars[p, w]))

    # Extract counts and differences if provided
    home_counts = None
    away_counts = None
    diffs = None
    total_imbalance = None

    if home_count_vars is not None and T is not None and N is not None:
        home_counts = {}
        for t in T:
            for k in range(N):
                if is_true(model.evaluate(home_count_vars[t][k])):
                    home_counts[t] = k
                    break

    if away_count_vars is not None and T is not None and N is not None:
        away_counts = {}
        for t in T:
            for k in range(N):
                if is_true(model.evaluate(away_count_vars[t][k])):
                    away_counts[t] = k
                    break

    if diff_vars is not None and T is not None and N is not None:
        diffs = {}
        for t in T:
            for k in range(N):
                if is_true(model.evaluate(diff_vars[t][k])):
                    diffs[t] = k
                    break
        total_imbalance = sum(diffs.values())

    return {
        'solution': solution,
        'home_first': home_first,
        'home_counts': home_counts,
        'away_counts': away_counts,
        'diffs': diffs,
        'imbalance': total_imbalance
    }


def format_json(N, P, W, match_pairs, extracted_solution, runtime, approach_name,
                is_optimal=True, objective_value=None):
    """
    Format solution as JSON according to specification.

    Args:
        N: Number of teams
        P: Period range
        W: Week range
        match_pairs: Dictionary mapping (match_id, slot) -> team_id
        extracted_solution: Dictionary returned by extract_solution()
        runtime: Runtime in seconds (float)
        approach_name: Name of the approach (e.g., "SAT_Basic", "SAT_Optimized")
        is_optimal: Whether the solution is optimal
        objective_value: Objective function value (None for decision problems)

    Returns:
        Dictionary in the required JSON format
    """
    solution = extracted_solution['solution']
    home_first = extracted_solution.get('home_first', {})

    # Build the solution matrix: (n/2) × (n-1) where each entry is [home, away]
    sol_matrix = []

    for p in P:  # Iterate through periods (rows)
        period_row = []
        for w in W:  # Iterate through weeks (columns)
            m = solution[p, w]

            # Determine home/away based on whether home_first is available
            if (p, w) in home_first:
                if home_first[p, w]:
                    home = match_pairs[m, 0]
                    away = match_pairs[m, 1]
                else:
                    home = match_pairs[m, 1]
                    away = match_pairs[m, 0]
            else:
                # Default: first team is home
                home = match_pairs[m, 0]
                away = match_pairs[m, 1]

            # Add 1 to convert from 0-indexed to 1-indexed teams
            period_row.append([home + 1, away + 1])

        sol_matrix.append(period_row)

    # Floor the runtime
    time_floored = int(runtime)

    # If runtime >= 300 or not optimal, set time to 300
    if not is_optimal or runtime >= 300:
        time_floored = 300

    return {
        approach_name: {
            "time": time_floored,
            "optimal": is_optimal,
            "obj": objective_value,
            "sol": sol_matrix
        }
    }


def save_json(json_data, filename):
    """
    Save JSON data to file.

    Args:
        json_data: Dictionary to save
        filename: Output filename
    """
    with open(filename, 'w') as f:
        json.dump(json_data, f, indent=4)
    print(f"\nSolution saved to {filename}")


def print_solution(N, W, P, match_pairs, extracted_solution):
    """
    Print the schedule in a formatted table.

    Args:
        N: Number of teams
        W: Week range
        P: Period range
        match_pairs: Dictionary mapping (match_id, slot) -> team_id
        extracted_solution: Dictionary returned by extract_solution()
    """
    solution = extracted_solution['solution']
    home_first = extracted_solution.get('home_first', {})
    home_counts = extracted_solution.get('home_counts')
    away_counts = extracted_solution.get('away_counts')
    diffs = extracted_solution.get('diffs')
    total_imbalance = extracted_solution.get('imbalance')

    print("\n" + "=" * 60)
    print(f"SOLUTION FOUND for N={N} teams")
    print("=" * 60)

    for w in W:
        print(f"\nWeek {w + 1}:\n")
        print("  ", end="")
        for p in P:
            print(f"Period {p + 1}\t", end="")
        print("\n    ", end="")
        for p in P:
            m = solution[p, w]

            # Determine home/away based on whether home_first is available
            if (p, w) in home_first:
                if home_first[p, w]:
                    home = match_pairs[m, 0]
                    away = match_pairs[m, 1]
                else:
                    home = match_pairs[m, 1]
                    away = match_pairs[m, 0]
            else:
                # Default: first team is home (for backward compatibility)
                home = match_pairs[m, 0]
                away = match_pairs[m, 1]

            print(f"{home} vs {away}\t", end="")
        print("\n")

    # Print balance information if available
    if home_counts is not None and away_counts is not None:
        print("\nHome/Away Balance:")
        T = range(N)
        for t in T:
            diff_str = f", Diff={diffs[t]}" if diffs is not None else ""
            print(f"Team {t}: Home={home_counts[t]}, Away={away_counts[t]}{diff_str}")

        if total_imbalance is not None:
            print(f"\nTotal Imbalance: {total_imbalance}")

    print("=" * 60)
