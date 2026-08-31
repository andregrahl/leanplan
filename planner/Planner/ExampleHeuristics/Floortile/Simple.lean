/-
Floortile, simple heuristic: the number of tiles still to be painted.

Every goal atom is `painted(tile, colour)`.  Both `paint_up` and `paint_down` paint
exactly one tile, and no other schema adds a `painted` atom, so the count of
unpainted goal tiles falls by at most one per action.
-/
import Planner.ExampleHeuristics.Base

namespace Planner.ExampleHeuristics.Floortile

/-- The goal-predicate families this heuristic splits the goal into. -/
def families (t : Task) : List (Array Fact) :=
  t.families [["painted"]]

/-- The number of `painted` goals that do not hold. -/
def simple (t : Task) : Heuristic :=
  maxMissingOf "floortile-simple" (families t)

/-- The admissibility certificate the planner checks before using `simple`. -/
def certified (t : Task) : Bool :=
  t.familiesSafe (families t)

end Planner.ExampleHeuristics.Floortile
