include "globals.mzn";

% Total number of teams
int: n;
constraint assert(n mod 2 = 0, "Number of teams must be even");
% n must be even to allow perfect pairing in each round

% Number of weeks (rounds)
int: weeks = n - 1;
% Number of periods (matches per week)
int: periods = n div 2;
% Number of slots per match: slot 1 = first team, slot 2 = second team
int: slots = 2;

% Array of all teams except the pivot team 1
array[1..n-1] of int: teams = [i | i in 2..n];
% Pivot team 1 is fixed; all other teams will rotate around it

% Precompute rotated arrays for each week
% rotated[w, i] gives the i-th team in the rotated circle for week w
array[1..weeks, 1..n-1] of int: rotated =
  array2d(1..weeks, 1..n-1,
    [ teams[(i - w + (n-1)) mod (n-1) + 1] | w in 1..weeks, i in 1..n-1 ]
  );
  
% Explanation of rotation formula:
% i - w + (n-1) : move the index according to the week number
% mod (n-1) : wrap around the (n-1) teams in the circle
% +1 : adjust for MiniZinc 1-based indexing
% This produces clockwise rotation of the teams around the pivot

% Build schedule array
% schedule[p, w, s] gives the team in period p, week w, slot s
array[1..periods, 1..weeks, 1..slots] of int: schedule =
  array3d(1..periods, 1..weeks, 1..slots,
    [ if p == 1 then
          % First period always includes the pivot
          if s == 1 then 1
          else rotated[w, n-1]  % Pivot plays against last team in rotated array
          endif
      else
          % Other periods are paired "outside-in" (first vs last, second vs second-last)
          if s == 1 then rotated[w, p-1]
          else rotated[w, n-p]
          endif
      endif
      | p in 1..periods, w in 1..weeks, s in 1..slots
    ]
  );
  
% Output the schedule in a readable format
output [
  "Week \(w):\n" ++
  concat([
    "Period \(p): " ++ show(schedule[p,w,1]) ++ " vs " ++ show(schedule[p,w,2]) ++ "\n"
    | p in 1..periods
  ])
  | w in 1..weeks
];
