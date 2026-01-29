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

% Which team from the pair is home (0 = first team, 1 = second team)
array[P, W] of var 0..1: which_is_home;

% Count of how many times team t plays home and away (s=0 home, s=1 away)
array[T, 0..1] of var T: Cha;

% define objective var
var int: imbalance;

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

% CHANNELING CONSTRAINTS

% Channel home/away counts from the actual solution (matches_idx + which_is_home)
constraint forall(slot in 0..1)(
    let {
        % Collect all teams playing in the given slot (0=home, 1=away)
        array[int] of var T: teams_in_slot =
            array1d([
                if (slot == 0) == (which_is_home[p, w] == 0) then
                    matches[matches_idx[p, w], 0]
                else
                    matches[matches_idx[p, w], 1]
                endif
                | p in P, w in W
            ]);
        % The counts for each team
        array[T] of var W: counts =
            array1d(T, [Cha[t, slot] | t in T]);
    } in
    global_cardinality(teams_in_slot, array1d(T, [t | t in T]), counts)
);

% OBJECTIVE FUNCTION

% Defining obj function as the sum of absolute differences between home and away counts
constraint imbalance = sum(t in T)(abs(Cha[t, 0] - Cha[t, 1]));

% The imbalance is at least N given the constraints of the problem
constraint imbalance >= N;

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
    array1d(matches_idx) ++ array1d(which_is_home),
    first_fail,      % Choose variable with smallest domain
    indomain_min,    % Try smallest value first
    complete
) minimize imbalance;

% OUTPUT

output
[
  concat([
    "Week \(w+1):\n\n",
    concat([
      let {
        int: m = fix(matches_idx[p, w]),
        int: home =
          if fix(which_is_home[p, w]) == 0
          then matches[m, 0]
          else matches[m, 1]
          endif,
        int: away =
          if fix(which_is_home[p, w]) == 0
          then matches[m, 1]
          else matches[m, 0]
          endif
      } in
      "  Period \(p+1): \(home) vs \(away)\n"
      | p in P
    ]),
    "\n"
  ])
  | w in W
]
++
["\nHome/Away Balance:\n"]
++
[
  "Team \(t): Home=\(fix(Cha[t, 0])), Away=\(fix(Cha[t, 1])), Diff=\(abs(fix(Cha[t, 0]) - fix(Cha[t, 1])))\n"
  | t in T
]
++
["\nTotal Imbalance: \(fix(imbalance))\n"];
