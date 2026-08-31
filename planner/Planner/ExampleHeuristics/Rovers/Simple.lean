/-
Rovers, simple heuristic: the number of data items not yet communicated.

Goals are `communicated_soil_data`, `communicated_rock_data` and
`communicated_image_data` atoms.  Each `communicate_*` schema adds exactly one of
them and no schema adds two, so all three predicates can share a single family
and the count falls by at most one per action.
-/
import Planner.ExampleHeuristics.Base

namespace Planner.ExampleHeuristics.Rovers

/-- The goal-predicate families this heuristic splits the goal into. -/
def families (t : Task) : List (Array Fact) :=
  t.families [["communicated_soil_data", "communicated_rock_data", "communicated_image_data"]]

/-- The number of `communicated_*` goals that do not hold. -/
def simple (t : Task) : Heuristic :=
  maxMissingOf "rovers-simple" (families t)

/-- The admissibility certificate the planner checks before using `simple`. -/
def certified (t : Task) : Bool :=
  t.familiesSafe (families t)

end Planner.ExampleHeuristics.Rovers
