% SPORTS SCHEDULING PROBLEM (ROUND ROBIN)
% This model schedules a Round Robin tournament for N teams.
% Key constraints:
% 1. Every team plays every other team exactly once.
% 2. Every team plays exactly once per week.
% 3. No team plays more than twice in the same period (time slot).

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

set of int: TeamsInSamePeriod = 0..2 * (N - 1) - 1;
% Helper set for the total number of team slots in a specific period across all weeks.

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

% Flatten to list of matches
array[M, S] of int: matches =
  array2d(M, S, [
    rb[p, w, s]
    | w in W, p in P, s in S
  ]);
  

% DECISION VARIABLES

% The Match ID assigned to period p in week w.
array[P, W] of var M: matches_idx;
 

% RE-INSERTED: Count of how many times team t plays in period p.
% We calculate this explicitly to enforce the limit.
array[P, T] of var W: Cp;


% CORE CONSTRAINTS

% 1. constraint solution based on round robin generation
constraint forall(w in W)(
  forall(p in P)(
      w * (N div 2) <= matches_idx[p, w] /\ matches_idx[p, w] < (w + 1) * (N div 2)
  )
);

% 2. VALIDITY
constraint alldifferent(matches_idx);

% 3. Each team plays at most twice a week
constraint forall(p in P)(
    let {
        array[int] of var M: period_matches = 
            array1d([matches_idx[p, w] | w in W]);
        array[int] of var T: teams = 
            array1d([matches[period_matches[i], s] | i in index_set(period_matches), s in S]);
        array[T] of var 0..2*card(W): counts = array1d(T, [Cp[p, t] | t in T]);
    } in
    global_cardinality(teams, array1d(T, [t | t in T]), counts)
);

% search strategy
solve :: int_search(
    array1d(matches_idx),
    first_fail,      % Choose variable with smallest domain
    indomain_min,    % Try smallest value first
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