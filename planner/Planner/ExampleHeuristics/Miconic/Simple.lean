/-
Miconic, simple heuristic: the number of passengers not yet served.

Every goal atom is `served(p)` and only `depart` adds one, for a single passenger,
so the count falls by at most one per action.
-/
import Planner.ExampleHeuristics.Base

namespace Planner.ExampleHeuristics.Miconic

/-- The goal-predicate families this heuristic splits the goal into. -/
def families (t : Task) : List (Array Fact) :=
  t.families [["served"]]

/-- The number of passengers whose `served` goal does not hold. -/
def simple (t : Task) : Heuristic :=
  maxMissingOf "miconic-simple" (families t)

/-- The admissibility certificate the planner checks before using `simple`. -/
def certified (t : Task) : Bool :=
  t.familiesSafe (families t)

end Planner.ExampleHeuristics.Miconic
