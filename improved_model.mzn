include "globals.mzn";

int: N;               
% Number of teams. Must be even for a round robin tournament.
constraint assert(N mod 2 = 0, "Number of teams must be even");

set of int: T = 0..N-1;
% Set of all teams indexed from 0 to N-1.

set of int: S = 0..1;
% Each match has two slots (team 0 and team 1).

set of int: W = 0..N-2;
% Weeks of the tournament. A round robin with N teams has N-1 weeks.

set of int: P = 0..N div 2 - 1;
% Periods within a week. Each week has N/2 matches.

set of int: M = 0..(N - 1) * (N div 2) - 1;
% Total match indices. There are (N-1) weeks and N/2 matches per week.

set of int: TeamsInSamePeriod = 0..2 * (N - 1) - 1;
% Teams that play in the same period across all weeks (two per match times N-1 weeks).

% Create round robin tournament using the circle method
array[P, W, S] of int: rb = array3d(P, W, S,
  [ if s == 0 then
        if p == 0 then N-1 else (p + w) mod (N-1) endif
    else
        if p == 0 then w else (N - p + w - 1) mod (N-1) endif
    endif
    | p in P, w in W, s in S
  ]);
% rb[p, w, s] contains the team in period p, week w, slot s.
% Side 0 uses pivot team logic, side 1 pairs remaining teams correctly.

% Flatten the 3D schedule into a list of matches
array[M, S] of int: matches =
  array2d(M, S, [
    rb[p, w, s]
    | w in W, p in P, s in S
  ]);
% matches[i, 0] vs matches[i, 1] gives the two teams of match i.

% Decision variables
array[P, W] of var M: matches_idx; 
% Index of the match assigned to period p in week w

array[P, T] of var W: Cp;  
% Count of how many times team t played in period p

array[W, T] of var P: Cw;  
% Count of how many times team t played in week w

% Each team must play exactly once per week
constraint forall(w in W, t in T)( Cw[w, t] = 1);

% Each team can play at most twice in the same period across all weeks
constraint forall(p in P, t in T) (Cp[p, t] <= 2);

% Lexicographic ordering of periods and weeks. It breaks column/row swapping symmetry.
constraint symmetry_breaking_constraint(
    forall(w in min(W)..max(W)-1)(
        lex_less(
            [matches_idx[p, w] | p in P],      % Week 0 < Week 1 ... < Week (N-2) 
            [matches_idx[p, w+1] | p in P]     
        )
    )
);

% Fixing pivot match in first week to avoid redundant rotations.
constraint matches_idx[0,0] = 0;

% Channeling constraints for Cw
constraint forall(w in W) (
    let {
      array[P] of var int: indexes_of_matches_played_in_week_w = array1d(P, [matches_idx[p, w] | p in P]),
      array[T] of var T: teams_playing_in_week_w  = array1d(T, [matches[i, s] | i in indexes_of_matches_played_in_week_w, s in S])
    } in 
    forall(t in T)(
      Cw[w, t] = count(teams_playing_in_week_w, t)
    )
);
% This ensures Cw[w, t] correctly counts how many times team t plays in week w.

% Channeling constraints for Cp
constraint forall(p in P)(
  let{
    array[W] of var int: indexes_of_matches_played_in_period_p = array1d(W, [matches_idx[p, w] | w in W]),
    array[TeamsInSamePeriod] of var T: teams_playing_in_period_p  = array1d(TeamsInSamePeriod, [matches[i, s] | i in indexes_of_matches_played_in_period_p, s in S])
  } in
  forall(t in T)(
    Cp[p, t] = count(teams_playing_in_period_p, t)
  )
);
% Cp[p, t] counts how many times team t plays in period p across all weeks.

% Solve statement with search strategies
solve 
:: restart_luby(100) 
% Use Luby restart strategy after 100 failures to avoid getting stuck

:: relax_and_reconstruct([matches_idx[p, w] | p in P, w in W], 60)  
% Relax the match indices to allow temporary constraint violations
% The solver will reconstruct feasible solutions after relaxation

:: int_search([matches_idx[p, w] | p in P, w in W], dom_w_deg, indomain_min, complete)  
% Sequential search over matches using weighted degree heuristic and minimum value selection

satisfy;

% Output matches in a readable week-by-week table
output [
  concat([
    "Week \(w+1):\n\n",
    "  ",  
    concat([ "Period \(p+1)\t" | p in P ]),  % Column headers
    "\n    ",  
    concat([
      "\(matches[matches_idx[p, w], 0]) vs \(matches[matches_idx[p, w], 1]) \t"
      | p in P
    ]),
    "\n\n"  
  ])
  | w in W
];
% Each week prints periods as columns, matches side by side, with blank lines between weeks
