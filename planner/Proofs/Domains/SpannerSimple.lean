import Proofs.ExampleHeuristics.Base
import Proofs.ExampleHeuristics.SchemaBase
import Planner.ExampleHeuristics.Spanner.Simple
/-
Spanner, simple heuristic: goal-aware, consistent, admissible.

Only `tighten_nut` adds a `tightened` atom, for a single nut.

That is why `certified` — which checks, against the grounded operators of the
task at hand, that no operator adds two facts of one family — is expected to
hold, and the planner refuses the heuristic if it does not.  Everything below
follows from that one Boolean.
-/

namespace Planner.ExampleHeuristics.Spanner

open Planner

theorem simple_goalAware (t : Task) (hwf : Task.WF t)
    (hcert : certified t = true) : t.GoalAware (simple t).eval :=
  (t.maxMissingOf_admissible hwf "spanner-simple" [["tightened"]] hcert).1

theorem simple_consistent (t : Task) (hwf : Task.WF t)
    (hcert : certified t = true) : t.Consistent (simple t).eval :=
  (t.maxMissingOf_admissible hwf "spanner-simple" [["tightened"]] hcert).2.1

/-- Never overestimates the cost of reaching the goal, on any state the search sees. -/
theorem simple_admissible (t : Task) (hwf : Task.WF t)
    (hcert : certified t = true) : t.Admissible (simple t).eval :=
  (t.maxMissingOf_admissible hwf "spanner-simple" [["tightened"]] hcert).2.2


/-! ### The same, with nothing checked per task

`SchemaFamilySafe` is read off the domain's schemas once: no schema adds two
atoms whose predicates lie in one family.  It holds for every instance, so these
three need no `certified` check.
-/

theorem simple_goalAware_of_schema (t : Task) (hwf : Task.WF t)
    (hgnd : t.goal.toList.Nodup)
    (hsafe : ∀ ps ∈ [["tightened"]], t.SchemaFamilySafe ps) :
    t.GoalAware (simple t).eval :=
  (t.maxMissingOf_admissible_of_schema hwf "spanner-simple"
    [["tightened"]] hgnd hsafe).1

theorem simple_consistent_of_schema (t : Task) (hwf : Task.WF t)
    (hgnd : t.goal.toList.Nodup)
    (hsafe : ∀ ps ∈ [["tightened"]], t.SchemaFamilySafe ps) :
    t.Consistent (simple t).eval :=
  (t.maxMissingOf_admissible_of_schema hwf "spanner-simple"
    [["tightened"]] hgnd hsafe).2.1

/-- Never overestimates, from a fact about the domain's schemas alone. -/
theorem simple_admissible_of_schema (t : Task) (hwf : Task.WF t)
    (hgnd : t.goal.toList.Nodup)
    (hsafe : ∀ ps ∈ [["tightened"]], t.SchemaFamilySafe ps) :
    t.Admissible (simple t).eval :=
  (t.maxMissingOf_admissible_of_schema hwf "spanner-simple"
    [["tightened"]] hgnd hsafe).2.2

end Planner.ExampleHeuristics.Spanner
