include "globals.mzn";

% PARAMETERS

% Number of teams. Must be even.
int: N;
constraint assert(N mod 2 = 0, "Number of teams must be even");

% DOMAINS

% Set of all teams.
set of int: T = 0..N-1;

% Slots per match (0 = Home, 1 = Away).
set of int: S = 0..1;

% Weeks in the season.
set of int: W = 0..N-2;

% Periods (time slots) per week.
set of int: P = 0..N div 2 - 1;

% Total number of matches to be played.
set of int: M = 0..(N - 1) * (N div 2) - 1;

% MATCHES GENERATION (CIRCLE METHOD)

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

% Flatten to list of matches
array[M, S] of int: matches =
  array2d(M, S, [
    rb[p, w, s]
    | w in W, p in P, s in S
  ]);

% DECISION VARIABLES

% The Match ID assigned to period p in week w.
array[P, W] of var M: matches_idx;

% CONSTRAINTS

% 1. Validity: no matches repeated
constraint alldifferent(matches_idx);

% 2. Intuition: every p (N / 2) matches generated from round robin method, a week is formed
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
            array1d([matches[period_matches[i], s] | i in index_set(period_matches), s in S]);  % all teams playing in period p
    } in
    % constraint each team to play from 0 to 2 times in each period
    global_cardinality_low_up(
        teams,
        array1d(T, [t | t in T]),
        array1d(T, [0 | t in T]),
        array1d(T, [2 | t in T])
    )
);

% SYMMETRY BREAKING CONSTRAINTS

% First match generated from round robin is the first match
constraint symmetry_breaking_constraint(
    matches_idx[0, 0] = 0
);

% Lexicographic ordering between periods to avoid rows swapping
constraint symmetry_breaking_constraint(
    forall(p in 0..card(P) - 2)(
      lex_less(
          [matches_idx[p, w] | w in W],
          [matches_idx[p+1, w] | w in W]
      )
    )
);

% SEARCH STRATEGY

solve :: int_search(
    array1d(matches_idx),
    first_fail,
    indomain_min,
    complete
) satisfy;

% OUTPUT

output [
  concat([
    "Week \(w+1):\n\n",
    "  ",  
    concat([ "Period \(p+1)\t" | p in P ]), 
    "\n    ",  
    concat([
      "\(matches[matches_idx[p, w], 0]) vs \(matches[matches_idx[p, w], 1]) \t"
      | p in P
    ]),
    "\n\n"  
  ])
  | w in W
];
