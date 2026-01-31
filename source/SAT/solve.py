import argparse
import time

from sat_encodings import *
from solver_backend import create_solver, ORToolsBackend
from utils import *


def add_core_constraints(solver, N, T, S, W, P, M, match_pairs, matches_idx_vars):
    """
    Add core scheduling constraints.
    """
    # Each position has exactly one match assigned
    for p in P:
        for w in W:
            exactly_one(matches_idx_vars[p, w], solver, f'eo_midx_{p}_{w}')

    # CONSTRAINT 1: matches_idx[0, 0] = 0 (symmetry breaking)
    if isinstance(solver, ORToolsBackend):
        solver.model.Add(matches_idx_vars[0, 0][0] == 1)
    else:
        solver.add_constraint(matches_idx_vars[0, 0][0])

    # CONSTRAINT 2: All different (each match ID used exactly once)
    for m in M:
        indicators = []
        for p in P:
            for w in W:
                indicators.append(matches_idx_vars[p, w][m])
        exactly_one(indicators, solver, f'alldiff_m_{m}')

    # CONSTRAINT 3: Range constraint - week w uses matches [w*(N/2), (w+1)*(N/2))]
    for w in W:
        for p in P:
            low = w * (N // 2)
            high = (w + 1) * (N // 2)
            for m in M:
                if not (low <= m < high):
                    if isinstance(solver, ORToolsBackend):
                        solver.model.Add(matches_idx_vars[p, w][m] == 0)
                    else:
                        solver.add_constraint(Not(matches_idx_vars[p, w][m]))

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

            if len(team_appears) > 0:
                at_most_k(team_appears, 2, solver, f'amt2_t{team}_p{period}')


def satisfy(N, backend='z3'):
    assert N % 2 == 0, "Number of teams must be even"

    # Parameters
    T, S, W, P, M = calculate_params(N)
    rb, matches = generate_rb_and_flattened(N, W, P, S)

    # Create solver with specified backend
    solver = create_solver(backend)

    # Decision variables: matches_idx[p][w] using one-hot encoding
    matches_idx_vars = {}
    for p in P:
        for w in W:
            vars = encode_integer_onehot(solver, f'midx_{p}_{w}', len(M) - 1)
            matches_idx_vars[p, w] = vars

    # Add core constraints
    add_core_constraints(solver, N, T, S, W, P, M, matches, matches_idx_vars)

    # Solve
    start_time = time.time()
    result = solver.check()
    elapsed_time = time.time() - start_time

    if result == 'SAT':
        model = solver.get_model()
        solution = extract_solution(model, P, W, M, matches_idx_vars, backend=backend)
        print_solution(N, W, P, matches, solution)

        if isinstance(solver, ORToolsBackend):
            stats = solver.get_statistics()
            print(f"\nSolver statistics:")
            print(f"  Time: {elapsed_time:.2f}s")
            print(f"  Branches: {stats['branches']}")
            print(f"  Conflicts: {stats['conflicts']}")

        return solution, elapsed_time
    else:
        print("No solution found (UNSAT)")
        return None, elapsed_time


def optimize(N, backend='z3'):
    assert N % 2 == 0, "Number of teams must be even"

    T, S, W, P, M = calculate_params(N)
    rb, match_pairs = generate_rb_and_flattened(N, W, P, S)

    # Create solver
    solver = create_solver(backend)

    # Decision variables: matches_idx[p][w] using one-hot encoding
    matches_idx_vars = {}
    for p in P:
        for w in W:
            vars = encode_integer_onehot(solver, f'midx_{p}_{w}', len(M) - 1)
            matches_idx_vars[p, w] = vars

    # Decision variables: home_is_first[p][w]
    home_is_first_vars = {}
    for p in P:
        for w in W:
            home_is_first_vars[p, w] = solver.create_bool_var(f'home_first_{p}_{w}')

    # Add core scheduling constraints
    add_core_constraints(solver, N, T, S, W, P, M, match_pairs, matches_idx_vars)

    # HOME/AWAY BALANCE OPTIMIZATION
    # Count variables for each team
    home_count_vars = {}
    away_count_vars = {}

    for t in T:
        home_count_vars[t] = encode_integer_onehot(solver, f'home_count_{t}', N - 1)
        away_count_vars[t] = encode_integer_onehot(solver, f'away_count_{t}', N - 1)

        exactly_one(home_count_vars[t], solver, f'home_eo_{t}')
        exactly_one(away_count_vars[t], solver, f'away_eo_{t}')

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
                    # if team t is first in index match:
                    # team t plays home if matches_idx_vars[p, w][m] (match m is a match) and home_is_first_vars[p, w] (match p, w has first team home)
                    # team t plays away if matches_idx_vars[p, w][m] (match m is a match) and not home_is_first_vars[p, w] (match p, w has second team home)
                    if match_pairs[m, 0] == t:
                        # Create auxiliary variables for AND conditions
                        home_ind = solver.create_bool_var(f'home_{t}_{p}_{w}_{m}')
                        away_ind = solver.create_bool_var(f'away_{t}_{p}_{w}_{m}')
                        # ortools
                        if isinstance(solver, ORToolsBackend):
                            solver.model.AddBoolAnd([match_assigned, home_is_first_vars[p, w]]).OnlyEnforceIf(home_ind)
                            solver.model.AddBoolOr(
                                [match_assigned.Not(), home_is_first_vars[p, w].Not()]).OnlyEnforceIf(home_ind.Not())
                            solver.model.AddBoolAnd([match_assigned, home_is_first_vars[p, w].Not()]).OnlyEnforceIf(
                                away_ind)
                            solver.model.AddBoolOr([match_assigned.Not(), home_is_first_vars[p, w]]).OnlyEnforceIf(
                                away_ind.Not())
                        # z3
                        else:
                            solver.add_constraint(home_ind == And(match_assigned, home_is_first_vars[p, w]))
                            solver.add_constraint(away_ind == And(match_assigned, Not(home_is_first_vars[p, w])))

                        team_home_indicators.append(home_ind)
                        team_away_indicators.append(away_ind)
                    # if team t is second in index match:
                    # team t plays home if matches_idx_vars[p, w][m] (match m is a match) and not home_is_first_vars[p, w] (match p, w has second team home)
                    # team t plays away if matches_idx_vars[p, w][m] (match m is a match) and home_is_first_vars[p, w] (match p, w has first team home)
                    elif match_pairs[m, 1] == t:
                        home_ind = solver.create_bool_var(f'home_{t}_{p}_{w}_{m}')
                        away_ind = solver.create_bool_var(f'away_{t}_{p}_{w}_{m}')
                        # ortools
                        if isinstance(solver, ORToolsBackend):
                            solver.model.AddBoolAnd([match_assigned, home_is_first_vars[p, w].Not()]).OnlyEnforceIf(
                                home_ind)
                            solver.model.AddBoolOr([match_assigned.Not(), home_is_first_vars[p, w]]).OnlyEnforceIf(
                                home_ind.Not())
                            solver.model.AddBoolAnd([match_assigned, home_is_first_vars[p, w]]).OnlyEnforceIf(away_ind)
                            solver.model.AddBoolOr(
                                [match_assigned.Not(), home_is_first_vars[p, w].Not()]).OnlyEnforceIf(away_ind.Not())
                        # z3
                        else:
                            solver.add_constraint(home_ind == And(match_assigned, Not(home_is_first_vars[p, w])))
                            solver.add_constraint(away_ind == And(match_assigned, home_is_first_vars[p, w]))

                        team_home_indicators.append(home_ind)
                        team_away_indicators.append(away_ind)
        # channel home and away count
        encode_exact_count(solver, team_home_indicators, home_count_vars[t], N - 1, f'home_t{t}')
        encode_exact_count(solver, team_away_indicators, away_count_vars[t], N - 1, f'away_t{t}')

    # Compute imbalance
    diff_vars = {}

    for t in T:
        diff_vars[t] = encode_integer_onehot(solver, f'diff_{t}', N - 1)
        exactly_one(diff_vars[t], solver, f'diff_eo_{t}')

        if isinstance(solver, ORToolsBackend):
            # OR-Tools: pure boolean case enumeration (same as Z3 branch)
            for d in range(N):
                cases = []
                for h in range(N):
                    for a in range(N):
                        if abs(h - a) == d:
                            cases.append((h, a))
                if cases:
                    # diff_vars[t][d] <=> OR over (home_count[h] AND away_count[a]) for valid (h,a)
                    case_auxes = []
                    for h, a in cases:
                        aux = solver.create_bool_var(f'abs_case_{t}_{d}_{h}_{a}')
                        solver.model.AddBoolAnd([home_count_vars[t][h], away_count_vars[t][a]]).OnlyEnforceIf(aux)
                        solver.model.AddBoolOr([home_count_vars[t][h].Not(), away_count_vars[t][a].Not()]).OnlyEnforceIf(aux.Not())
                        case_auxes.append(aux)
                    # diff_vars[t][d] => at least one case is true
                    solver.model.AddBoolOr(case_auxes).OnlyEnforceIf(diff_vars[t][d])
                    # if any case is true => diff_vars[t][d]
                    for aux in case_auxes:
                        solver.model.AddImplication(aux, diff_vars[t][d])
                else:
                    solver.model.Add(diff_vars[t][d] == 0)
        else:
            # Z3: enumerate cases
            for d in range(N):
                cases = []
                for h in range(N):
                    for a in range(N):
                        if abs(h - a) == d:
                            cases.append(And(home_count_vars[t][h], away_count_vars[t][a]))
                if cases:
                    solver.add_constraint(Implies(diff_vars[t][d], Or(cases)))
                    solver.add_constraint(Implies(Or(cases), diff_vars[t][d]))
                else:
                    solver.add_constraint(Not(diff_vars[t][d]))

    # Minimize total imbalance
    if isinstance(solver, ORToolsBackend):
        # diff_vars[t] is already a correctly-channelled one-hot over [0..N-1]
        # encoding |home_count[t] - away_count[t]|.
        # The total imbalance is simply the sum of each team's diff value.
        # For a one-hot variable, sum(d * diff_vars[t][d]) equals the active index,
        # so summing that over all teams gives the total imbalance directly as a
        # linear expression over booleans — no auxiliary one-hot or channelling needed.
        solver.minimize(sum(d * diff_vars[t][d] for t in T for d in range(N)))

        start_time = time.time()
        result = solver.check()
        elapsed_time = time.time() - start_time

        if result == 'SAT':
            solution = extract_solution(
                solver.get_model(), P, W, M,
                matches_idx_vars,
                home_is_first_vars=home_is_first_vars,
                home_count_vars=home_count_vars,
                away_count_vars=away_count_vars,
                diff_vars=diff_vars,
                T=T,
                N=N,
                backend=backend  # Explicitly named
            )
            print_solution(N, W, P, match_pairs, solution)

            stats = solver.get_statistics()
            print(f"\nSolver statistics:")
            print(f"  Status: {stats['status']}")
            print(f"  Objective: {stats['objective']}")
            print(f"  Time: {elapsed_time:.2f}s")
            print(f"  Branches: {stats['branches']}")
            print(f"  Conflicts: {stats['conflicts']}")

            return solution, elapsed_time
        else:
            print("No solution found")
            return None, elapsed_time
    else:
        # Z3: iterative search
        best_solution = None
        start_time = time.time()

        for target in range(N, N * (N - 1) + 1):
            print(f"Trying imbalance = {target}...")
            solver.push()
            constrain_total_imbalance(solver, diff_vars, T, N, target)

            result = solver.check()
            if result == 'SAT':
                elapsed_time = time.time() - start_time
                print(f"✓ Found solution with imbalance = {target}")
                best_solution = extract_solution(
                    solver.get_model(), P, W, M,
                    matches_idx_vars, home_is_first_vars,
                    home_count_vars, away_count_vars, diff_vars, T, N, backend=backend
                )
                print_solution(N, W, P, match_pairs, best_solution)
                solver.pop()
                return best_solution, elapsed_time
            solver.pop()

        elapsed_time = time.time() - start_time
        return best_solution, elapsed_time


def main():
    parser = argparse.ArgumentParser(
        description="Round-robin scheduling using SAT encodings."
    )

    parser.add_argument(
        "-n", "--n",
        type=int,
        required=True,
        help="Number of teams (must be even)."
    )

    parser.add_argument(
        "-m", "--mode",
        type=str,
        choices=["satisfy", "optimize"],
        required=True,
        help="Execution mode: 'satisfy' for satisfaction, 'optimize' for optimization."
    )

    parser.add_argument(
        "-s", "--solver",
        type=str,
        choices=["z3", "ortools"],
        default="z3",
        help="Solver backend to use: 'z3' or 'ortools' (default: z3)"
    )

    args = parser.parse_args()

    N = args.n
    mode = args.mode
    backend = args.solver

    # Validate input
    if N <= 0:
        print("Error: N must be positive.")
        sys.exit(1)

    if N % 2 != 0:
        print("Error: Number of teams must be even.")
        sys.exit(1)

    print(f"Running with N = {N}, mode = {mode}, backend = {backend}")

    # Run with specified backend
    if mode == "satisfy":
        satisfy(N, backend)
    elif mode == "optimize":
        optimize(N, backend)


if __name__ == "__main__":
    main()