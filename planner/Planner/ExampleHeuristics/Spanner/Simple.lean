/-
Spanner, simple heuristic: the number of nuts still loose.

Every goal atom is `tightened(n)` and only `tighten_nut` adds one, for a single
nut, so the count falls by at most one per action.
-/
import Planner.ExampleHeuristics.Base

namespace Planner.ExampleHeuristics.Spanner

/-- The goal-predicate families this heuristic splits the goal into. -/
def families (t : Task) : List (Array Fact) :=
  t.families [["tightened"]]

/-- The number of nuts whose `tightened` goal does not hold. -/
def simple (t : Task) : Heuristic :=
  maxMissingOf "spanner-simple" (families t)

/-- The admissibility certificate the planner checks before using `simple`. -/
def certified (t : Task) : Bool :=
  t.familiesSafe (families t)

end Planner.ExampleHeuristics.Spanner
