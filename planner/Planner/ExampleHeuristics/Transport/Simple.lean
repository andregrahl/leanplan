/-
Transport, simple heuristic: the number of packages not at their destination.

Every goal atom is `at(package, location)`.  `drop` adds one such atom and `drive`
adds an `at` atom for a vehicle, never for a package; no schema adds two `at`
atoms, so the count falls by at most one per action.
-/
import Planner.ExampleHeuristics.Base

namespace Planner.ExampleHeuristics.Transport

/-- The goal-predicate families this heuristic splits the goal into. -/
def families (t : Task) : List (Array Fact) :=
  t.families [["at"]]

/-- The number of `at` goals that do not hold. -/
def simple (t : Task) : Heuristic :=
  maxMissingOf "transport-simple" (families t)

/-- The admissibility certificate the planner checks before using `simple`. -/
def certified (t : Task) : Bool :=
  t.familiesSafe (families t)

end Planner.ExampleHeuristics.Transport
