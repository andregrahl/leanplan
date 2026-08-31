/-
Ferry, simple heuristic: the number of cars not yet at their destination.

Every goal atom is `at(car, location)`.  The only schema that adds an `at` atom is
`debark`, which lands exactly one car, so the count falls by at most one per
action.
-/
import Planner.ExampleHeuristics.Base

namespace Planner.ExampleHeuristics.Ferry

/-- The goal-predicate families this heuristic splits the goal into. -/
def families (t : Task) : List (Array Fact) :=
  t.families [["at"]]

/-- The number of `at` goals that do not hold. -/
def simple (t : Task) : Heuristic :=
  maxMissingOf "ferry-simple" (families t)

/-- The admissibility certificate the planner checks before using `simple`. -/
def certified (t : Task) : Bool :=
  t.familiesSafe (families t)

end Planner.ExampleHeuristics.Ferry
