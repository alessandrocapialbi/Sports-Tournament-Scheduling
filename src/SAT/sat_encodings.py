from z3 import *
from itertools import combinations

# ============================================================================
# AT MOST ONE ENCODINGS
# ============================================================================

# Naive Pairwise
def at_least_one_np(bool_vars):
    return Or(bool_vars)

def at_most_one_np(bool_vars, name = ""):
    return And([Not(And(pair[0], pair[1])) for pair in combinations(bool_vars, 2)])

def exactly_one_np(bool_vars, name = ""):
    return And(at_least_one_np(bool_vars), at_most_one_np(bool_vars, name))


# Sequential
def at_least_one_seq(bool_vars):
    return at_least_one_np(bool_vars)

def at_most_one_seq(bool_vars, name):
    constraints = []
    n = len(bool_vars)
    s = [Bool(f"s_{name}_{i}") for i in range(n - 1)]
    constraints.append(Or(Not(bool_vars[0]), s[0]))
    constraints.append(Or(Not(bool_vars[n-1]), Not(s[n-2])))
    for i in range(1, n - 1):
        constraints.append(Or(Not(bool_vars[i]), s[i]))
        constraints.append(Or(Not(bool_vars[i]), Not(s[i-1])))
        constraints.append(Or(Not(s[i-1]), s[i]))
    return And(constraints)

def exactly_one_seq(bool_vars, name):
    return And(at_least_one_seq(bool_vars), at_most_one_seq(bool_vars, name))


# Bitwise
def toBinary(num, length=None):
    num_bin = bin(num).split("b")[-1]
    if length:
        return "0" * (length - len(num_bin)) + num_bin
    return num_bin


def at_least_one_bw(bool_vars):
    return at_least_one_np(bool_vars)


def at_most_one_bw(bool_vars, name):
    constraints = []
    n = len(bool_vars)
    m = math.ceil(math.log2(n))
    r = [Bool(f"r_{name}_{i}") for i in range(m)]
    binaries = [toBinary(i, m) for i in range(n)]
    for i in range(n):
        for j in range(m):
            phi = Not(r[j])
            if binaries[i][j] == "1":
                phi = r[j]
            constraints.append(Or(Not(bool_vars[i]), phi))
    return And(constraints)


def exactly_one_bw(bool_vars, name):
    return And(at_least_one_bw(bool_vars), at_most_one_bw(bool_vars, name))


# Heule
def at_least_one_he(bool_vars):
    return at_least_one_np(bool_vars)

def at_most_one_he(bool_vars, name):
    if len(bool_vars) <= 4:
        return And(at_most_one_np(bool_vars))
    y = Bool(f"y_{name}")
    return And(And(at_most_one_np(bool_vars[:3] + [y])), And(at_most_one_he(bool_vars[3:] + [Not(y)], name+"_")))

def exactly_one_he(bool_vars, name):
    return And(at_most_one_he(bool_vars, name), at_least_one_he(bool_vars))


# ============================================================================
# AT MOST K ENCODING (Sequential Counter)
# ============================================================================

def at_most_k_seq(bool_vars, k, name):
    """Sequential counter encoding for at-most-k constraint.
    Based on Sinz's sequential encoding."""
    n = len(bool_vars)
    if n <= k:
        return True
    if k == 0:
        return And([Not(v) for v in bool_vars])

    # s[i][j] means: among the first i+1 variables, at least j+1 are true
    s = [[Bool(f"s_{name}_{i}_{j}") for j in range(k)] for i in range(n - 1)]

    return And(
        Implies(bool_vars[0], s[0][0]),
        Implies(s[n - 2][k - 1], Not(bool_vars[n - 1])),
        And(*[Not(s[0][j]) for j in range(1, k)]),
        And(
            *[
                And(
                    Implies(Or(bool_vars[i], s[i - 1][0]), s[i][0]),
                    And(
                        *[
                            Implies(
                                Or(
                                    And(bool_vars[i], s[i - 1][j - 1]), s[i - 1][j]
                                ),
                                s[i][j],
                            )
                            for j in range(1, k)
                        ]
                    ),
                    Implies(s[i - 1][k - 1], Not(bool_vars[i])),
                )
                for i in range(1, n - 1)
            ]
        ),
    )


# ============================================================================
# HELPER FUNCTIONS
# ============================================================================

def encode_integer_onehot(name, max_val):
    """
    One-hot encoding for integers 0..max_val.
    Returns list of boolean variables where exactly one is true.
    """
    vars = [Bool(f'{name}_val_{i}') for i in range(max_val + 1)]
    return vars

def encode_exact_count(solver, indicators, count_vars, max_count, name):
    """Encode that exactly count_vars[k] is true iff exactly k indicators are true."""
    for k in range(max_count + 1):
        if k > len(indicators):
            solver.add(Not(count_vars[k]))
        elif k == 0:
            # Count is 0 iff all indicators are false
            solver.add(Implies(count_vars[0], And([Not(ind) for ind in indicators])))
            if len(indicators) > 0:
                solver.add(Implies(And([Not(ind) for ind in indicators]), count_vars[0]))
        elif k == len(indicators):
            # Count is len iff all indicators are true
            solver.add(Implies(count_vars[k], And(indicators)))
            solver.add(Implies(And(indicators), count_vars[k]))
        else:
            # Use at-most and at-least encoding
            at_least_k = at_most_k_seq([Not(ind) for ind in indicators],
                                       len(indicators) - k, f'{name}_atleast_{k}')
            at_most_k_cond = at_most_k_seq(indicators, k, f'{name}_atmost_{k}')

            solver.add(Implies(count_vars[k], And(at_least_k, at_most_k_cond)))
            solver.add(Implies(And(at_least_k, at_most_k_cond), count_vars[k]))


def constrain_total_imbalance(solver, diff_vars, T, N, target):
    """Add constraint that sum of all team differences equals target."""

    # Find all valid combinations that sum to target
    def find_combinations(teams_left, current_sum, current_assignment):
        if teams_left == 0:
            if current_sum == target:
                yield current_assignment
            return

        team_idx = N - teams_left
        for diff in range(min(N, target - current_sum + 1)):
            yield from find_combinations(teams_left - 1, current_sum + diff,
                                         current_assignment + [diff])

    valid_combinations = list(find_combinations(N, 0, []))

    if not valid_combinations:
        solver.add(False)  # UNSAT
        return

    combination_constraints = []
    for combo in valid_combinations:
        combo_constraint = And([diff_vars[t][combo[t]] for t in T])
        combination_constraints.append(combo_constraint)

    solver.add(Or(combination_constraints))
