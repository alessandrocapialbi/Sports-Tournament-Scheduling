% SPORTS SCHEDULING PROBLEM (ROUND ROBIN)
% This model schedules a Round Robin tournament for N teams.
% Key constraints:
% 1. Every team plays every other team exactly once.
% 2. Every team plays exactly once per week.
% 3. No team plays more than twice in the same period (time slot).
% 4. Balanced Home-Away matches among teams (optimized)

include "globals.mzn";

% PARAMETERS AND SETS

int: N;               
% Number of teams. Must be even.
constraint assert(N mod 2 = 0, "Number of teams must be even");

set of int: T = 0..N-1;
% Set of all teams.

set of int: S = 0..1;
% Slots per match (0 = Home, 1 = Away).

set of int: W = 0..N-2;
% Weeks in the season.

set of int: P = 0..N div 2 - 1;
% Periods (time slots) per week.

set of int: M = 0..(N - 1) * (N div 2) - 1;
% Total number of matches to be played.

% DATA GENERATION (CIRCLE METHOD) - Generate unordered pairs

array[P, W, S] of int: rb = array3d(P, W, S,
  [ if s == 0 then
        if p == 0 then 
            if w mod 2 == 0 then N-1 else w endif 
        else (p + w) mod (N-1) endif
    else
        if p == 0 then 
            if w mod 2 == 0 then w else N-1 endif 
        else (N - p + w - 1) mod (N-1) endif
    endif
    | p in P, w in W, s in S
  ]);

% Flatten to list of match pairs (unordered)
array[M, 0..1] of int: match_pairs =
  array2d(M, 0..1, [
    rb[p, w, s]
    | w in W, p in P, s in 0..1
  ]);
  

% DECISION VARIABLES

% The Match ID assigned to period p in week w.
array[P, W] of var M: matches_idx;

% Decision variable: which team from the pair is home (0 = first team, 1 = second team)
array[P, W] of var 0..1: home_is_first;

% Count of how many times team t plays home and away
array[T, 0..1] of var T: Cha;

% define objective var
var int: imbalance;


% CORE CONSTRAINTS
constraint matches_idx[0, 0] = 0;

% 1. VALIDITY
constraint alldifferent(matches_idx);

% 2. constraint solution based on round robin generation
constraint forall(w in W)(
  forall(p in P)(
      w * (N div 2) <= matches_idx[p, w] /\ matches_idx[p, w] < (w + 1) * (N div 2)
  )
);

% 3. Each team plays at most twice in any period
constraint forall(p in P)(
    let {
        array[int] of var M: period_matches = 
            array1d([matches_idx[p, w] | w in W]);
        array[int] of var T: teams = 
            array1d([match_pairs[period_matches[i], s] | i in index_set(period_matches), s in 0..1]);
    } in
    global_cardinality_low_up(
        teams,                          % The array to count
        array1d(T, [t | t in T]),      % The values to count (all teams)
        array1d(T, [0 | t in T]),      % Lower bounds (0 times minimum)
        array1d(T, [2 | t in T])       % Upper bounds (2 times maximum)
    )
);

% 4. Channel home/away counts from the actual solution (matches_idx + home_is_first)
constraint forall(slot in 0..1)(
    let {
        % Collect all TEAMS playing in the given slot (0=home, 1=away)
        array[int] of var T: teams_in_slot = 
            array1d([
                if (slot == 0) == (home_is_first[p, w] == 0) then
                    match_pairs[matches_idx[p, w], 0]
                else
                    match_pairs[matches_idx[p, w], 1]
                endif
                | p in P, w in W
            ]);
        % The counts for each team
        array[T] of var W: counts = 
            array1d(T, [Cha[t, slot] | t in T]);
    } in
    global_cardinality(teams_in_slot, array1d(T, [t | t in T]), counts)
);

% defining obj function as the sum of absolute differences between home and away counts
constraint imbalance = sum(t in T)(abs(Cha[t, 0] - Cha[t, 1]));

constraint imbalance >= N;  % at least N is imbalance

% SYMMETRY BREAKING: Lexicographic ordering between periods
constraint symmetry_breaking_constraint(
    % Break row symmetry: each period's schedule should be lex-ordered
    forall(p in 0..card(P) - 2)(
      lex_less(
          [matches_idx[p, w] | w in W],
          [matches_idx[p+1, w] | w in W]
      )
    )
);

% search strategy
solve
    :: restart_geometric(1.5, 75)
    :: relax_and_reconstruct([matches_idx[p, w] | p in P, w in W], 50)
    :: int_search(
        array1d(matches_idx) ++ array1d(home_is_first),
        dom_w_deg,
        indomain_median,
        complete
    ) minimize imbalance;


% OUTPUT
output [
  concat([
    "Week \(w+1):\n\n",
    "  ",  
    concat([ "Period \(p+1)\t" | p in P ]), 
    "\n    ",  
    concat([
      let {
        int: m = fix(matches_idx[p, w]),
        int: home = if fix(home_is_first[p, w]) == 0 then match_pairs[m, 0] else match_pairs[m, 1] endif,
        int: away = if fix(home_is_first[p, w]) == 0 then match_pairs[m, 1] else match_pairs[m, 0] endif
      } in
      "\(home) vs \(away) \t"
      | p in P
    ]),
    "\n\n"  
  ])
  | w in W
] ++
["\n\nHome/Away Balance:\n"] ++
[
  "Team \(t): Home=\(fix(Cha[t, 0])), Away=\(fix(Cha[t, 1])), Diff=\(abs(fix(Cha[t, 0]) - fix(Cha[t, 1])))\n"
  | t in T
] ++
["\nTotal Imbalance: \(fix(imbalance))\n"];