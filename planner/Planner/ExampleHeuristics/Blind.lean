/-
The blind heuristic.

Mirrors pyperplan's `heuristics/blind.py`: zero on goal states and the cheapest
action cost elsewhere.  It is goal-aware and consistent for any non-negative cost
function, and with unit costs it is the constant `1` off the goal — which is what
makes `astar(blind())` in Fast Downward and blind A* here explore the same set of
states up to tie-breaking.
-/
import Planner.ExampleHeuristics.Base

namespace Planner

/-- The smallest cost of any operator, or `1` when the task has no operators. -/
def minActionCost (t : Task) : Nat :=
  t.ops.foldl (init := 1) fun acc op => min acc op.cost

/-- `0` on goal states, the cheapest action cost elsewhere. -/
def blind (t : Task) : Heuristic :=
  let c := minActionCost t
  { name := "blind"
    eval := fun s => if t.isGoal s then 0 else c }

end Planner
