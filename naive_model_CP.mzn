% Naive model, just to start understanding the problem.
% It is very inefficient because it guesses the matches as they are created,
% leading to many failures and restarts. 
% The next approach is to define the possible matches a priori using the circle method,
% computing them only once and then translating the problem into simply assigning periods over weeks,
% while respecting all constraints.


% Include standard global constraints
include "globals.mzn"; 


% Number of teams in the tournament
int: n;
constraint assert(n mod 2 == 0, "Number of teams must be an even number");
% Ensure number of teams is even to allow perfect pairing in each round

% Number of weeks (rounds) in a single round-robin tournament
int: weeks = n - 1;

% Number of period slots per week; n/2 games per round
int: periods = n div 2;

% opponent[t,w] stores the opponent of team t in week w
array[1..n, 1..weeks] of var 1..n: opponent;

% period[t,w] stores the period (time slot) when team t plays in week w
array[1..n, 1..weeks] of var 1..periods: period;

% is_home[t,w] is true if team t plays at home, false if away
array[1..n, 1..weeks] of var bool: is_home;

% No team can play against itself in any week
constraint forall(t in 1..n, w in 1..weeks) (
  opponent[t, w] != t
);

% Each team must play against all other teams exactly once across all weeks
constraint forall(t in 1..n) (
  alldifferent([opponent[t, w] | w in 1..weeks])
);

% Ensure mutual agreement: if team A plays team B, then team B plays team A
constraint forall(w in 1..weeks) (
  symmetric_all_different([opponent[t, w] | t in 1..n])
);

% Both teams in a match share the same period and one must be home while the other is away
constraint forall(t in 1..n, w in 1..weeks) (
    let { var int: opp = opponent[t, w] } in (
        period[t, w] == period[opp, w] /\
        is_home[t, w] != is_home[opp, w]
    )
);

% Each period in a week is assigned exactly to 2 teams (one match per period)
constraint forall(w in 1..weeks)(
    global_cardinality(
        [period[t, w] | t in 1..n],
        [p | p in 1..periods],
        [2 | p in 1..periods]
    )
);

% Each team can play at most twice in the same period across all weeks
constraint forall(t in 1..n, p in 1..periods)(
    count(w in 1..weeks)(period[t, w] == p) <= 2
);

% Break symmetry by fixing team 1's opponents in the first weeks
constraint forall(w in 1..weeks)(
  opponent[1, w] = w + 1
);

% Break symmetry among period values: period 1 appears before 2, 2 before 3, etc.
constraint value_precede_chain(1..periods, [period[t, 1] | t in 1..n]);

% Search strategy: assign opponents first, then periods; restart and relax-and-reconstruct help explore the search space efficiently
solve 
:: restart_luby(250)
:: relax_and_reconstruct([opponent[t,w] | t in 1..n, w in 1..weeks], 60)
:: seq_search([
    int_search([opponent[t,w] | t in 1..n, w in 1..weeks], dom_w_deg, indomain_min, complete),
    int_search([period[t,w] | t in 1..n, w in 1..weeks], first_fail, indomain_min, complete)
]) satisfy;

% Output the schedule week by week, showing period, home team, and away team. Only home teams are printed to avoid duplicate matches
output [
    "SCHEDULE:\n" ++
    concat([
        "\n--- Week " ++ show(w) ++ " ---\n" ++
        concat([
            if fix(is_home[t, w]) then
                "Period " ++ show(period[t,w]) ++ ": " ++ 
                "Team " ++ show(t) ++ " (Home) vs Team " ++ show(opponent[t,w]) ++ " (Away)\n"
            else "" endif
            | p in 1..periods, t in 1..n where fix(period[t, w]) == p
        ])
        | w in 1..weeks
    ])
];
