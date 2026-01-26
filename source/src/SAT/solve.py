from z3 import *

from utils import *
from sat_encodings import *


def add_core_constraints(solver, N, T, S, W, P, M, match_pairs, matches_idx_vars):
    """
    Add core scheduling constraints that are common to both satisfy() and optimization.

    Returns:
        Dictionary with 'matches_idx_vars' and other constraint-related variables
    """
    # Each position has exactly one match assigned (one-hot constraint)
    for p in P:
        for w in W:
            solver.add(exactly_one_he(matches_idx_vars[p, w], f'eo_midx_{p}_{w}'))

    # CONSTRAINT 1: matches_idx[0, 0] = 0 (symmetry breaking)
    solver.add(matches_idx_vars[0, 0][0])

    # CONSTRAINT 2: All different (each match ID used exactly once)
    for m in M:
        indicators = []
        for p in P:
            for w in W:
                indicators.append(matches_idx_vars[p, w][m])
        solver.add(exactly_one_he(indicators, f'alldiff_m_{m}'))

    # CONSTRAINT 3: Range constraint - week w uses matches [w*(N/2), (w+1)*(N/2))
    for w in W:
        for p in P:
            low = w * (N // 2)
            high = (w + 1) * (N // 2)
            for m in M:
                if not (low <= m < high):
                    solver.add(Not(matches_idx_vars[p, w][m]))

    # CONSTRAINT 4: Each team plays at most twice in any period
    for period in P:
        for team in T:
            team_appears = []

            for w in W:
                low = w * (N // 2)
                high = (w + 1) * (N // 2)

                for m in range(low, high):
                    match_has_team = (match_pairs[m, 0] == team or
                                      match_pairs[m, 1] == team)

                    if match_has_team:
                        team_appears.append(matches_idx_vars[period, w][m])

            if len(team_appears) > 2:
                solver.add(at_most_k_seq(team_appears, 2, f'amt2_t{team}_p{period}'))
            elif len(team_appears) == 2:
                solver.add(at_most_one_np(team_appears))


def satisfy(N):
    """Solve the sports scheduling problem for N teams using pure boolean SAT."""
    assert N % 2 == 0, "Number of teams must be even"

    # Parameters
    T, S, W, P, M = calculate_params(N)
    rb, matches = generate_rb_and_flattened(N, W, P, S)

    # Decision variables: matches_idx[p][w] using one-hot encoding
    matches_idx_vars = {}
    for p in P:
        for w in W:
            vars = encode_integer_onehot(f'midx_{p}_{w}', len(M) - 1)
            matches_idx_vars[p, w] = vars

    # Create solver
    solver = Solver()

    # Add core constraints
    add_core_constraints(solver, N, T, S, W, P, M, matches, matches_idx_vars)

    # Solve
    result = solver.check()

    if result == sat:
        model = solver.model()
        solution = extract_solution(model, P, W, M, matches_idx_vars)
        print_solution(N, W, P, matches, solution)
        return solution
    else:
        print("No solution found (UNSAT)")
        return None


def solve_with_optimization(N):
    """
    Solve the sports scheduling problem with home/away balance optimization.

    Args:
        N: Number of teams (must be even)

    Returns:
        Dictionary with solution details or None if UNSAT
    """
    assert N % 2 == 0, "Number of teams must be even"

    T, S, W, P, M = calculate_params(N)
    rb, match_pairs = generate_rb_and_flattened(N, W, P, S)

    # Create solver
    solver = Solver()

    # Decision variables: matches_idx[p][w] using one-hot encoding
    matches_idx_vars = {}
    for p in P:
        for w in W:
            vars = encode_integer_onehot(f'midx_{p}_{w}', len(M) - 1)
            matches_idx_vars[p, w] = vars

    # Decision variables: home_is_first[p][w]
    home_is_first_vars = {}
    for p in P:
        for w in W:
            home_is_first_vars[p, w] = Bool(f'home_first_{p}_{w}')

    # Add core scheduling constraints
    add_core_constraints(solver, N, T, S, W, P, M, match_pairs, matches_idx_vars)

    # HOME/AWAY BALANCE OPTIMIZATION
    # Count variables for each team
    home_count_vars = {}
    away_count_vars = {}

    for t in T:
        home_count_vars[t] = encode_integer_onehot(f'home_count_{t}', N - 1)
        away_count_vars[t] = encode_integer_onehot(f'away_count_{t}', N - 1)

        solver.add(exactly_one_he(home_count_vars[t], f'home_eo_{t}'))
        solver.add(exactly_one_he(away_count_vars[t], f'away_eo_{t}'))

    # Link count variables to actual home/away assignments
    for t in T:
        team_home_indicators = []
        team_away_indicators = []

        for p in P:
            for w in W:
                low = w * (N // 2)
                high = (w + 1) * (N // 2)

                for m in range(low, high):
                    match_assigned = matches_idx_vars[p, w][m]

                    if match_pairs[m, 0] == t:
                        team_home_indicators.append(
                            And(match_assigned, home_is_first_vars[p, w])
                        )
                        team_away_indicators.append(
                            And(match_assigned, Not(home_is_first_vars[p, w]))
                        )
                    elif match_pairs[m, 1] == t:
                        team_home_indicators.append(
                            And(match_assigned, Not(home_is_first_vars[p, w]))
                        )
                        team_away_indicators.append(
                            And(match_assigned, home_is_first_vars[p, w])
                        )

        encode_exact_count(solver, team_home_indicators, home_count_vars[t],
                           N - 1, f'home_t{t}')
        encode_exact_count(solver, team_away_indicators, away_count_vars[t],
                           N - 1, f'away_t{t}')

    # Compute imbalance
    diff_vars = {}
    for t in T:
        diff_vars[t] = encode_integer_onehot(f'diff_{t}', N - 1)
        solver.add(exactly_one_he(diff_vars[t], f'diff_eo_{t}'))

        # diff[t] = |home[t] - away[t]|
        for d in range(N):
            cases = []
            for h in range(N):
                for a in range(N):
                    if abs(h - a) == d:
                        cases.append(And(home_count_vars[t][h], away_count_vars[t][a]))

            if cases:
                solver.add(Implies(diff_vars[t][d], Or(cases)))
                solver.add(Implies(Or(cases), diff_vars[t][d]))
            else:
                solver.add(Not(diff_vars[t][d]))

    # Iteratively minimize
    best_solution = None
    for target in range(N, N * (N - 1) + 1):
        print(f"Trying imbalance = {target}...")
        solver.push()
        constrain_total_imbalance(solver, diff_vars, T, N, target)

        result = solver.check()
        if result == sat:
            print(f"✓ Found solution with imbalance = {target}")
            best_solution = extract_solution(
                solver.model(), P, W, M,
                matches_idx_vars, home_is_first_vars,
                home_count_vars, away_count_vars, diff_vars, T, N
            )
            print_solution(N, W, P, match_pairs, best_solution)
            solver.pop()
            break
        solver.pop()

    return best_solution
