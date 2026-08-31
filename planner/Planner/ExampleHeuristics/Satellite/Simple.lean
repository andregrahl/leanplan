/-
Satellite, simple heuristic: the number of unmet imaging and pointing goals.

Goals are `have_image` and `pointing` atoms.  `take_image` adds one `have_image`
atom and no `pointing` atom; `turn_to` adds one `pointing` atom and no
`have_image` atom.  No schema adds two goal atoms, so the two predicates share a
single family.
-/
import Planner.ExampleHeuristics.Base

namespace Planner.ExampleHeuristics.Satellite

/-- The goal-predicate families this heuristic splits the goal into. -/
def families (t : Task) : List (Array Fact) :=
  t.families [["have_image", "pointing"]]

/-- The number of `have_image` and `pointing` goals that do not hold. -/
def simple (t : Task) : Heuristic :=
  maxMissingOf "satellite-simple" (families t)

/-- The admissibility certificate the planner checks before using `simple`. -/
def certified (t : Task) : Bool :=
  t.familiesSafe (families t)

end Planner.ExampleHeuristics.Satellite
