/-
Childsnack, simple heuristic: the number of children still to be served.

Every goal atom is `served(c)`, and the only schemas that add one are
`serve_sandwich` and `serve_sandwich_no_gluten`, each of which serves exactly one
child.  So the count of unserved goal children never falls by more than one per
action, and it is zero exactly on goal states.
-/
import Planner.ExampleHeuristics.Base

namespace Planner.ExampleHeuristics.Childsnack

/-- The goal-predicate families this heuristic splits the goal into. -/
def families (t : Task) : List (Array Fact) :=
  t.families [["served"]]

/-- The number of goal children not yet served. -/
def simple (t : Task) : Heuristic :=
  maxMissingOf "childsnack-simple" (families t)

/-- The admissibility certificate the planner checks before using `simple`. -/
def certified (t : Task) : Bool :=
  t.familiesSafe (families t)

end Planner.ExampleHeuristics.Childsnack
