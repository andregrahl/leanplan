/-
Blocks World, simple heuristic: the largest number of unmet goals of one kind.

Goals are `clear`, `on-table` and `on` atoms.  `stack` achieves a `clear` goal and
an `on` goal in the same step and `putdown` achieves a `clear` goal and an
`on-table` goal, so the plain goal count is inadmissible here.  Splitting the
goals into the three predicate families restores it: no schema adds two atoms of
the same predicate, so each family falls by at most one per action, and the
maximum of the three is a lower bound on the remaining plan.
-/
import Planner.ExampleHeuristics.Base

namespace Planner.ExampleHeuristics.Blocksworld

/-- The goal-predicate families this heuristic splits the goal into. -/
def families (t : Task) : List (Array Fact) :=
  t.families [["clear"], ["on-table"], ["on"]]

/-- The maximum of the unmet `clear`, `on-table` and `on` goal counts. -/
def simple (t : Task) : Heuristic :=
  maxMissingOf "blocksworld-simple" (families t)

/-- The admissibility certificate the planner checks before using `simple`. -/
def certified (t : Task) : Bool :=
  t.familiesSafe (families t)

end Planner.ExampleHeuristics.Blocksworld
