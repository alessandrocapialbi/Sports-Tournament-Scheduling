from z3 import is_true

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


def print_solution(N, W, P, matches, solution):
    """Print the round robin schedule in a formatted table."""
    # Print solution
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
            home = matches[m, 0]
            away = matches[m, 1]
            print(f"{home} vs {away}\t", end="")
        print("\n")

def compute_imbalance(P, W, T, solution_dict, matches):
    """Compute home-away imbalance from a solution."""
    home_counts = {t: 0 for t in T}
    away_counts = {t: 0 for t in T}

    for p in P:
        for w in W:
            m = solution_dict[p, w]
            home_counts[matches[m, 0]] += 1
            away_counts[matches[m, 1]] += 1

    imbalance = sum(abs(home_counts[t] - away_counts[t]) for t in T)
    return imbalance, home_counts, away_counts

def extract_solution(P, W, M, matches_idx_vars, model):
    """Extract solution from Z3 model."""
    solution = {}
    for p in P:
        for w in W:
            for m in M:
                if is_true(model.evaluate(matches_idx_vars[p, w][m])):
                    solution[p, w] = m
                    break
    return solution
