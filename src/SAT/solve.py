from z3 import *

from utils import *
from sat_encodings import *

def satisfy(N, solver):
    """Solve the sports scheduling problem for N teams using pure boolean SAT."""
    assert N % 2 == 0, "Number of teams must be even"

    # Parameters
    T, S, W, P, M = calculate_params(N)

    rb, matches = generate_rb_and_flattened(N, W, P, S)

    # Decision variables: matches_idx[p][w] using one-hot encoding
    # matches_idx_vars[p][w][m] is true iff period p in week w has match m
    matches_idx_vars = {}
    for p in P:
        for w in W:
            vars = encode_integer_onehot(f'midx_{p}_{w}', len(M) - 1)
            matches_idx_vars[p, w] = vars

    # Each position has exactly one match assigned (one-hot constraint)
    for p in P:
        for w in W:
            # Use Heule encoding for exactly-one (most efficient for this)
            solver.add(exactly_one_he(matches_idx_vars[p, w], f'eo_midx_{p}_{w}'))

    # CONSTRAINT 1: matches_idx[0, 0] = 0
    solver.add(matches_idx_vars[0, 0][0])

    # CONSTRAINT 2: All different (each match ID used exactly once across all positions)
    for m in M:
        # Collect all positions that could have match m
        indicators = []
        for p in P:
            for w in W:
                indicators.append(matches_idx_vars[p, w][m])

        # Exactly one position has this match
        # Use Heule encoding for exactly-one
        solver.add(exactly_one_he(indicators, f'alldiff_m_{m}'))

    # CONSTRAINT 3: Range constraint - week w uses matches [w*(N/2), (w+1)*(N/2))
    for w in W:
        for p in P:
            low = w * (N // 2)
            high = (w + 1) * (N // 2)
            # Only matches in [low, high) can be true
            for m in M:
                if not (low <= m < high):
                    solver.add(Not(matches_idx_vars[p, w][m]))

    # CONSTRAINT 4: Each team plays at most twice in any period
    for period in P:
        for team in T:
            # Collect indicators: team appears in matches_idx[period, w]
            team_appears = []

            for w in W:
                # For this week, check which matches are valid (due to range constraint)
                low = w * (N // 2)
                high = (w + 1) * (N // 2)

                for m in range(low, high):
                    # Does match m contain this team?
                    match_has_team = (matches[m, 0] == team or matches[m, 1] == team)

                    if match_has_team:
                        # If matches_idx[period, w] = m, then team appears
                        team_appears.append(matches_idx_vars[period, w][m])

            # At most 2 of these can be true
            # Use sequential encoding for at-most-k (efficient for small k)
            if len(team_appears) > 2:
                solver.add(at_most_k_seq(team_appears, 2, f'amt2_t{team}_p{period}'))
            elif len(team_appears) == 2:
                # Just use pairwise
                solver.add(at_most_one_np(team_appears))

    # Solve
    result = solver.check()

    if result == sat:
        model = solver.model()

        # Extract solution
        solution = {}
        for p in P:
            for w in W:
                for m in M:
                    if is_true(model.evaluate(matches_idx_vars[p, w][m])):
                        solution[p, w] = m
                        break

        # Print solution
        print_solution(N, W, P, matches, solution)

        return solution, matches_idx_vars
    else:
        print("No solution found (UNSAT)")
        return None

def optimize_home_away_balance(N, solver, matches, matches_idx_vars, sat_solution, max_iterations=None):
    """
    Optimize the home-away balance given a SAT solution.

    Parameters:
    - N: Number of teams
    - matches: Dictionary mapping (match_id, slot) -> team_id
    - matches_idx_vars: Dictionary of boolean variables for match assignments
    - solver: Z3 Solver with all base constraints already added
    - max_iterations: Maximum number of optimization iterations (None = until no improvement)

    Returns:
    - best_solution: Dictionary mapping (period, week) -> match_id
    - best_home_counts: Dictionary mapping team -> home count
    - best_away_counts: Dictionary mapping team -> away count
    - best_imbalance: Integer representing the minimum imbalance found
    """

    # Parameters
    T, S, W, P, M = calculate_params(N)

    model = solver.model()
    imbalance, home_counts, away_counts = compute_imbalance(P, W, T, sat_solution, matches)

    best_imbalance = imbalance
    best_solution = sat_solution.copy()
    best_home_counts = home_counts.copy()
    best_away_counts = away_counts.copy()

    print(f"Initial solution found with imbalance = {imbalance}")
    print(f"Home/Away distribution:")
    for t in T:
        print(f"  Team {t}: Home={home_counts[t]}, Away={away_counts[t]}, Diff={abs(home_counts[t] - away_counts[t])}")

    # Optimization loop
    iteration = 0
    while True:
        if max_iterations is not None and iteration >= max_iterations:
            print(f"Reached maximum iterations ({max_iterations})")
            break
        # since N-1 matches are played, then the best imbalance is when every teams has N-1//2 matches either home or away and N-1//2+1 home or away
        if  best_imbalance == N:
            print("Best imabalance reached")
            break

        iteration += 1
        print(f"\nIteration {iteration}: Trying to improve from imbalance = {best_imbalance}")

        # Create constraints to force better imbalance
        solver.push()

        # Add home/away count variables for each team
        home_count_vars = {}
        away_count_vars = {}

        for t in T:
            # Create one-hot encoding for home count
            home_count_vars[t] = [Bool(f"home_count_{t}_{c}_iter_{iteration}") for c in range(N)]
            # Create one-hot encoding for away count
            away_count_vars[t] = [Bool(f"away_count_{t}_{c}_iter_{iteration}") for c in range(N)]

            # Exactly one count value for home
            solver.add(exactly_one_he(home_count_vars[t], f"home_eo_{t}_iter_{iteration}"))
            # Exactly one count value for away
            solver.add(exactly_one_he(away_count_vars[t], f"away_eo_{t}_iter_{iteration}"))

        # Link count variables to actual match assignments
        for t in T:
            for s in S:
                count_vars = home_count_vars[t] if s == 0 else away_count_vars[t]

                # Collect indicators for when team t plays in slot s
                team_in_slot_indicators = []

                for p in P:
                    for w in W:
                        low = w * (N // 2)
                        high = (w + 1) * (N // 2)

                        for m in range(low, high):
                            if matches[m, s] == t:
                                team_in_slot_indicators.append(matches_idx_vars[p, w][m])

                # Encode cardinality: count_vars[k] = True iff exactly k indicators are true
                for k in range(N):
                    if k > len(team_in_slot_indicators):
                        solver.add(Not(count_vars[k]))
                    elif k == 0:
                        # Zero indicators are true
                        solver.add(Implies(count_vars[0],
                                           And([Not(ind) for ind in team_in_slot_indicators])))
                        if len(team_in_slot_indicators) > 0:
                            solver.add(Implies(And([Not(ind) for ind in team_in_slot_indicators]),
                                               count_vars[0]))
                    elif k == len(team_in_slot_indicators):
                        # All indicators are true
                        solver.add(Implies(count_vars[k],
                                           And(team_in_slot_indicators)))
                        solver.add(Implies(And(team_in_slot_indicators),
                                           count_vars[k]))
                    else:
                        # Exactly k indicators are true: at_least_k AND at_most_k
                        at_least_k_indicator = Bool(f"at_least_{k}_t{t}_s{s}_iter_{iteration}")
                        at_most_k_indicator = Bool(f"at_most_{k}_t{t}_s{s}_iter_{iteration}")

                        # at_most_k for the indicators
                        solver.add(Implies(at_most_k_indicator,
                                           at_most_k_seq(team_in_slot_indicators, k,
                                                         f"card_atmost_{k}_t{t}_s{s}_iter_{iteration}")))

                        # at_least_k: at_most (n-k) are false
                        false_indicators = [Not(ind) for ind in team_in_slot_indicators]
                        n_false_allowed = len(team_in_slot_indicators) - k
                        solver.add(Implies(at_least_k_indicator,
                                           at_most_k_seq(false_indicators, n_false_allowed,
                                                         f"card_atleast_{k}_t{t}_s{s}_iter_{iteration}")))

                        # count_vars[k] <=> at_least_k AND at_most_k
                        solver.add(Implies(count_vars[k],
                                           And(at_least_k_indicator, at_most_k_indicator)))
                        solver.add(Implies(And(at_least_k_indicator, at_most_k_indicator),
                                           count_vars[k]))

        # Create difference variables for each team
        diff_vars = {}
        for t in T:
            diff_vars[t] = [Bool(f"diff_{t}_{d}_iter_{iteration}") for d in range(N)]

            # Exactly one difference value
            solver.add(exactly_one_he(diff_vars[t], f"diff_eo_{t}_iter_{iteration}"))

            # Link difference to home/away counts: diff[t][d] = True iff |home[t] - away[t]| = d
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

        # Compute total imbalance and require it to be strictly less than current best
        # Total imbalance = sum of all team differences
        # We need to encode: sum_{t in T} (d * diff_vars[t][d]) < best_imbalance

        # Create binary encoding for total imbalance
        imbalance_bits = []
        max_imbalance = N * (N - 1)
        n_bits = max_imbalance.bit_length()

        for b in range(n_bits):
            imbalance_bits.append(Bool(f"imbalance_bit_{b}_iter_{iteration}"))

        # Add constraints to compute the sum using binary addition
        # This is complex, so we'll use a simpler approach: enumerate feasible total values

        # For each possible total imbalance value less than best_imbalance
        improvement_found = False

        for target in range(best_imbalance):
            solver.push()

            # Force total imbalance = target
            # Find all combinations of team differences that sum to target
            def find_combinations(teams_left, current_sum, current_assignment):
                if teams_left == 0:
                    if current_sum == target:
                        yield current_assignment
                    return

                team_idx = N - teams_left
                for diff in range(min(N, target - current_sum + 1)):
                    yield from find_combinations(teams_left - 1,
                                                 current_sum + diff,
                                                 current_assignment + [diff])

            valid_combinations = list(find_combinations(N, 0, []))

            if not valid_combinations:
                solver.pop()
                continue

            # At least one valid combination must be true
            combination_constraints = []
            for combo in valid_combinations:
                combo_constraint = And([diff_vars[t][combo[t]] for t in T])
                combination_constraints.append(combo_constraint)

            solver.add(Or(combination_constraints))

            # Try to solve
            result = solver.check()

            if result == sat:
                print(f"  Found solution with imbalance = {target}")
                model = solver.model()
                solution = extract_solution(P, W, M, matches, model)
                imbalance, home_counts, away_counts = compute_imbalance(P, W, T, solution, matches)

                # Verify the imbalance
                if imbalance == target and imbalance < best_imbalance:
                    best_imbalance = imbalance
                    best_solution = solution.copy()
                    best_home_counts = home_counts.copy()
                    best_away_counts = away_counts.copy()
                    improvement_found = True

                    print(f"  ✓ Improvement confirmed! New best imbalance = {best_imbalance}")
                    print(f"  Home/Away distribution:")
                    for t in T:
                        print(
                            f"    Team {t}: Home={home_counts[t]}, Away={away_counts[t]}, Diff={abs(home_counts[t] - away_counts[t])}")

                    solver.pop()  # Pop target constraint
                    break

            solver.pop()  # Pop target constraint

        solver.pop()  # Pop iteration constraints

        if not improvement_found:
            print(f"  No improvement found. Stopping optimization.")
            break

    print(f"\n{'=' * 60}")
    print(f"OPTIMIZATION COMPLETE")
    print(f"Best imbalance found: {best_imbalance}")
    print(f"Iterations: {iteration}")
    print(f"{'=' * 60}")

    return best_solution, best_home_counts, best_away_counts, best_imbalance
