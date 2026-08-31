/-
The simple heuristics, stated at the schema level.

All ten *simple* heuristics are the same thing: the maximum, over families of goal
facts, of the count still unmet.  Today each rests on `certified t = true` — a
decidable check run against the grounded operators of the task at hand.  That is a
per-task check, not a statement about the domain.

`SchemaFamilySafe` is the domain-level fact behind it: no schema of the domain
adds two atoms whose predicates both lie in one family.  It is read off the PDDL
once and holds for every instance, and `maxMissingOf_admissible_of_schema` turns
it into admissibility with no check left to run.
-/
import Proofs.ExampleHeuristics.Base

namespace Planner

open Planner.Pddl

/-- No operator adds two facts whose predicates both lie in `ps`. -/
def Task.SchemaFamilySafe (t : Task) (ps : List Name) : Prop :=
  ∀ op ∈ t.ops, ∀ f₁ f₂ : Fact,
    op.add.contains f₁ = true → op.add.contains f₂ = true →
    ps.contains (t.factNames.getD f₁ default).pred = true →
    ps.contains (t.factNames.getD f₂ default).pred = true → f₁ = f₂

theorem mem_goalFactsWith {t : Task} {ps : List Name} {f : Fact}
    (h : f ∈ t.goalFactsWith ps) :
    f ∈ t.goal ∧ ps.contains (t.factNames.getD f default).pred = true := by
  simp only [Task.goalFactsWith, Array.mem_filter] at h
  exact ⟨h.1, by simpa using h.2⟩

/-- The domain-level fact gives the per-task one, for every task of the domain. -/
theorem familySafe_of_schema {t : Task} {ps : List Name}
    (h : t.SchemaFamilySafe ps) : t.FamilySafe (t.goalFactsWith ps) := by
  intro op hop
  by_cases hex : ∃ f ∈ t.goalFactsWith ps, op.add.contains f = true
  · obtain ⟨x, hx, hxadd⟩ := hex
    refine ⟨x, ?_⟩
    intro f hf hne
    by_contra hcon
    have hadd : op.add.contains f = true := by simpa using hcon
    exact hne (h op hop f x hadd hxadd (mem_goalFactsWith hf).2 (mem_goalFactsWith hx).2)
  · refine ⟨0, ?_⟩
    intro f hf _
    by_contra hcon
    exact hex ⟨f, hf, by simpa using hcon⟩

/-- Everything a simple heuristic needs, from a fact about the domain's schemas. -/
theorem Task.maxMissingOf_admissible_of_schema (t : Task) (hwf : Task.WF t) (name : String)
    (preds : List (List Name)) (hgnd : t.goal.toList.Nodup)
    (hsafe : ∀ ps ∈ preds, t.SchemaFamilySafe ps) :
    t.GoalAware (maxMissingOf name (t.families preds)).eval ∧
    t.Consistent (maxMissingOf name (t.families preds)).eval ∧
    t.Admissible (maxMissingOf name (t.families preds)).eval := by
  have hfam : ∀ fam ∈ t.families preds, ∃ ps ∈ preds, fam = t.goalFactsWith ps := by
    intro fam hfam
    simp only [Task.families, List.mem_map] at hfam
    obtain ⟨ps, hps, rfl⟩ := hfam
    exact ⟨ps, hps, rfl⟩
  have hnd : ∀ fam ∈ t.families preds, fam.toList.Nodup := by
    intro fam hf
    obtain ⟨ps, -, rfl⟩ := hfam fam hf
    simp only [Task.goalFactsWith, Array.toList_filter]
    exact hgnd.filter _
  have hsafe' : ∀ fam ∈ t.families preds, t.FamilySafe fam := by
    intro fam hf
    obtain ⟨ps, hps, rfl⟩ := hfam fam hf
    exact familySafe_of_schema (hsafe ps hps)
  have hsub : ∀ fam ∈ t.families preds, ∀ f ∈ fam, f ∈ t.goal := by
    intro fam hf
    obtain ⟨ps, -, rfl⟩ := hfam fam hf
    exact goalFactsWith_subset t ps
  obtain ⟨hga, hcon⟩ := t.maxMissing_properties hwf (t.families preds) hnd hsub hsafe'
  have heq : (maxMissingOf name (t.families preds)).eval = missingMax (t.families preds) :=
    funext fun s => maxMissingOf_eval name (t.families preds) s
  rw [heq]
  exact ⟨hga, hcon, t.admissible _ hga hcon⟩

end Planner
