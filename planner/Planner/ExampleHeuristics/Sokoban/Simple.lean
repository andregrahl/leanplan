/-
Sokoban, simple heuristic: the number of boxes not on their goal square.

Every goal atom is `at(box, location)` and only `push` adds one, moving a single
box, so the count falls by at most one per action.  `push` also adds `at-robot`
and `clear` atoms, but those never appear in a goal.
-/
import Planner.ExampleHeuristics.Base

namespace Planner.ExampleHeuristics.Sokoban

/-- The goal-predicate families this heuristic splits the goal into. -/
def families (t : Task) : List (Array Fact) :=
  t.families [["at"]]

/-- The number of `at` goals that do not hold. -/
def simple (t : Task) : Heuristic :=
  maxMissingOf "sokoban-simple" (families t)

/-- The admissibility certificate the planner checks before using `simple`. -/
def certified (t : Task) : Bool :=
  t.familiesSafe (families t)

end Planner.ExampleHeuristics.Sokoban
