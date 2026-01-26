% SPORTS SCHEDULING PROBLEM (ROUND ROBIN) - RESTART LUBY VARIANT
% This model uses restart strategy with Luby sequence

include "globals.mzn";

% PARAMETERS AND SETS

int: N;               
constraint assert(N mod 2 = 0, "Number of teams must be even");

set of int: T = 0..N-1;
set of int: S = 0..1;
set of int: W = 0..N-2;
set of int: P = 0..N div 2 - 1;
set of int: M = 0..(N - 1) * (N div 2) - 1;
set of int: TeamsInSamePeriod = 0..2 * (N - 1) - 1;

% DATA GENERATION (CIRCLE METHOD)

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

array[M, S] of int: matches =
  array2d(M, S, [
    rb[p, w, s]
    | w in W, p in P, s in S
  ]);

% DECISION VARIABLES
array[P, W] of var M: matches_idx;

% CORE CONSTRAINTS
constraint matches_idx[0, 0] = 0;

constraint alldifferent(matches_idx);

constraint forall(w in W)(
  forall(p in P)(
      w * (N div 2) <= matches_idx[p, w] /\ matches_idx[p, w] < (w + 1) * (N div 2)
  )
);

constraint forall(p in P)(
    let {
        array[int] of var M: period_matches = 
            array1d([matches_idx[p, w] | w in W]);
        array[int] of var T: teams = 
            array1d([matches[period_matches[i], s] | i in index_set(period_matches), s in S]);
    } in
    global_cardinality_low_up(
        teams,
        array1d(T, [t | t in T]),
        array1d(T, [0 | t in T]),
        array1d(T, [2 | t in T])
    )
);

constraint symmetry_breaking_constraint(
    forall(p in 0..card(P) - 2)(
      lex_less(
          [matches_idx[p, w] | w in W],
          [matches_idx[p+1, w] | w in W]
      )
    )
);

% SEARCH STRATEGY: RESTART WITH LUBY
solve :: restart_luby(100)
      :: int_search(
          array1d(matches_idx),
          first_fail,
          indomain_min,
          complete
      ) satisfy;

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
