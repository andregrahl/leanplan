/-
Sokoban's simple heuristic, proved end to end in one file.

The schema-level proof comes first, then the same value closed against the
parsed domain.  The domain vocabulary it reads, including the schemas and the
`Pinned` record, is in `Proofs/Domains/SokobanDomain.lean`.  This file does not
read the improved heuristic's proof, and the improved heuristic's proof does not
read this one.
-/
import Proofs.ExampleHeuristics.Base
import Proofs.ExampleHeuristics.SchemaBase
import Proofs.Domains.SokobanDomain
import Planner.ExampleHeuristics.Sokoban.Simple

/- -------------------------------------------------------------------------- -/
/-
Sokoban, simple heuristic: goal-aware, consistent, admissible.

Only `push` adds an `at` atom, for a single box.

That is why `certified` — which checks, against the grounded operators of the
task at hand, that no operator adds two facts of one family — is expected to
hold, and the planner refuses the heuristic if it does not.  Everything below
follows from that one Boolean.
-/

namespace Planner.ExampleHeuristics.Sokoban

open Planner

theorem simple_goalAware (t : Task) (hwf : Task.WF t)
    (hcert : certified t = true) : t.GoalAware (simple t).eval :=
  (t.maxMissingOf_admissible hwf "sokoban-simple" [["at"]] hcert).1

theorem simple_consistent (t : Task) (hwf : Task.WF t)
    (hcert : certified t = true) : t.Consistent (simple t).eval :=
  (t.maxMissingOf_admissible hwf "sokoban-simple" [["at"]] hcert).2.1

/-- Never overestimates the cost of reaching the goal, on any state the search sees. -/
theorem simple_admissible (t : Task) (hwf : Task.WF t)
    (hcert : certified t = true) : t.Admissible (simple t).eval :=
  (t.maxMissingOf_admissible hwf "sokoban-simple" [["at"]] hcert).2.2


/-! ### The same, with nothing checked per task

`SchemaFamilySafe` is read off the domain's schemas once: no schema adds two
atoms whose predicates lie in one family.  It holds for every instance, so these
three need no `certified` check.
-/

theorem simple_goalAware_of_schema (t : Task) (hwf : Task.WF t)
    (hgnd : t.goal.toList.Nodup)
    (hsafe : ∀ ps ∈ [["at"]], t.SchemaFamilySafe ps) :
    t.GoalAware (simple t).eval :=
  (t.maxMissingOf_admissible_of_schema hwf "sokoban-simple"
    [["at"]] hgnd hsafe).1

theorem simple_consistent_of_schema (t : Task) (hwf : Task.WF t)
    (hgnd : t.goal.toList.Nodup)
    (hsafe : ∀ ps ∈ [["at"]], t.SchemaFamilySafe ps) :
    t.Consistent (simple t).eval :=
  (t.maxMissingOf_admissible_of_schema hwf "sokoban-simple"
    [["at"]] hgnd hsafe).2.1

/-- Never overestimates, from a fact about the domain's schemas alone. -/
theorem simple_admissible_of_schema (t : Task) (hwf : Task.WF t)
    (hgnd : t.goal.toList.Nodup)
    (hsafe : ∀ ps ∈ [["at"]], t.SchemaFamilySafe ps) :
    t.Admissible (simple t).eval :=
  (t.maxMissingOf_admissible_of_schema hwf "sokoban-simple"
    [["at"]] hgnd hsafe).2.2

end Planner.ExampleHeuristics.Sokoban

/- -------------------------------------------------------------------------- -/
/-
Closing the deployed Sokoban heuristic against the parsed domain.

The certified evaluator counts unmet `at(box, location)` goals.  A `move` adds
only `at-robot`; a `push` adds exactly one `at` atom.  Thus no numbered operator
can discharge two members of the goal family in one unit-cost step.
-/

namespace Planner.Lifted.Sokoban

open Planner Planner.Pddl

variable {d : Domain} {p : Problem}

/-- The task's numbered goal contains no duplicate fact. -/
theorem goal_nodup (hp : Pinned d p) (rel : Bool) :
    ((ground d p rel).goal).toList.Nodup := by
  show ((p.goal.toArray.map (fun a =>
    (factIndex (allAtoms (groundedOps d p rel) p.goal.toArray)).1.getD a 0)).toList).Nodup
  rw [Array.toList_map]
  refine List.Nodup.map_on (fun a ha b hb h => ?_) (by simpa using hp.goalNodup)
  have hma : a ∈ allAtoms (groundedOps d p rel) p.goal.toArray := by
    unfold allAtoms
    exact Array.mem_append.mpr (Or.inr (by simpa using ha))
  have hmb : b ∈ allAtoms (groundedOps d p rel) p.goal.toArray := by
    unfold allAtoms
    exact Array.mem_append.mpr (Or.inr (by simpa using hb))
  exact factIndex_injective' _ (factIndex_contains _ hma) (factIndex_contains _ hmb) h

/-- In an atom-level Sokoban operator, two added `at` atoms are the same atom. -/
theorem add_at_unique (hp : Pinned d p) {o : AtomOp} (ho : o ∈ groundedOps d p rel)
    {a₁ a₂ : GroundAtom} (h₁ : a₁ ∈ o.add) (h₂ : a₂ ∈ o.add)
    (hp₁ : a₁.pred = "at") (hp₂ : a₂.pred = "at") : a₁ = a₂ := by
  obtain ⟨hf⟩ := opFacts_ground d p rel ho
  have hi₁ : a₁ ∈ hf.inst.add := hf.subAdd a₁ h₁
  have hi₂ : a₂ ∈ hf.inst.add := hf.subAdd a₂ h₂
  rcases instance_shape hp.domain hf.inst with
      ⟨f, t, dir, hs, ha⟩ | ⟨rl, bl, fl, dir, b, hs, ha⟩
  · obtain ⟨-, hadd, -⟩ := move_atoms hf.inst hs ha
    rw [hadd] at hi₁
    obtain rfl : a₁ = atRobot t := by simpa using hi₁
    simp [atRobot] at hp₁
  · obtain ⟨-, -, -, hadd, -⟩ := push_atoms hf.inst hs ha
    rw [hadd] at hi₁ hi₂
    rcases (by simpa using hi₁ :
        a₁ = atRobot bl ∨ a₁ = atBox b fl ∨ a₁ = clearL bl) with h | h | h
    · subst a₁; simp [atRobot] at hp₁
    · subst a₁
      rcases (by simpa using hi₂ :
          a₂ = atRobot bl ∨ a₂ = atBox b fl ∨ a₂ = clearL bl) with h' | h' | h'
      · subst a₂; simp [atRobot] at hp₂
      · simpa using h'.symm
      · subst a₂; simp [clearL] at hp₂
    · subst a₁; simp [clearL] at hp₁

/-- The numbered grounded task adds at most one box-position fact per action. -/
theorem schemaFamilySafe_at (hp : Pinned d p) (rel : Bool) :
    (ground d p rel).SchemaFamilySafe ["at"] := by
  intro op hop f₁ f₂ hf₁ hf₂ hp₁ hp₂
  have hops : (ground d p rel).ops
      = (groundedOps d p rel).map
        (numberOp (factIndex (allAtoms (groundedOps d p rel) p.goal.toArray)).1) := rfl
  rw [hops, Array.mem_map] at hop
  obtain ⟨o, ho, rfl⟩ := hop
  have hm₁ : f₁ ∈ (numberOp
      (factIndex (allAtoms (groundedOps d p rel) p.goal.toArray)).1 o).add :=
    Array.contains_iff_mem.mp hf₁
  have hm₂ : f₂ ∈ (numberOp
      (factIndex (allAtoms (groundedOps d p rel) p.goal.toArray)).1 o).add :=
    Array.contains_iff_mem.mp hf₂
  obtain ⟨a₁, ha₁, hnum₁⟩ := Array.mem_map.mp hm₁
  obtain ⟨a₂, ha₂, hnum₂⟩ := Array.mem_map.mp hm₂
  have hall₁ : a₁ ∈ allAtoms (groundedOps d p rel) p.goal.toArray :=
    mem_allAtoms_of_op ho (Or.inr (Or.inl ha₁))
  have hall₂ : a₂ ∈ allAtoms (groundedOps d p rel) p.goal.toArray :=
    mem_allAtoms_of_op ho (Or.inr (Or.inl ha₂))
  have hname₁ : (ground d p rel).factNames.getD f₁ default = a₁ := by
    rw [← hnum₁]
    exact factIndex_name _ hall₁
  have hname₂ : (ground d p rel).factNames.getD f₂ default = a₂ := by
    rw [← hnum₂]
    exact factIndex_name _ hall₂
  have hat₁ : a₁.pred = "at" := by simpa [hname₁] using hp₁
  have hat₂ : a₂.pred = "at" := by simpa [hname₂] using hp₂
  have haa : a₁ = a₂ := add_at_unique hp ho ha₁ ha₂ hat₁ hat₂
  rw [← hnum₁, ← hnum₂, haa]

theorem schemaFamiliesSafe (hp : Pinned d p) (rel : Bool) :
    ∀ ps ∈ [["at"]], (ground d p rel).SchemaFamilySafe ps := by
  intro ps hps
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hps
  subst ps
  exact schemaFamilySafe_at hp rel

/-- The simple value is zero at every goal state of a pinned task. -/
theorem simple_goalAware (hp : Pinned d p) (rel : Bool) :
    (ground d p rel).GoalAware
      (Planner.ExampleHeuristics.Sokoban.simple (ground d p rel)).eval :=
  Planner.ExampleHeuristics.Sokoban.simple_goalAware_of_schema _
    (ground_wf d p rel (cost_pos hp rel)) (goal_nodup hp rel)
    (schemaFamiliesSafe hp rel)

/-- The simple value falls by at most the cost of one grounded action. -/
theorem simple_consistent (hp : Pinned d p) (rel : Bool) :
    (ground d p rel).Consistent
      (Planner.ExampleHeuristics.Sokoban.simple (ground d p rel)).eval :=
  Planner.ExampleHeuristics.Sokoban.simple_consistent_of_schema _
    (ground_wf d p rel (cost_pos hp rel)) (goal_nodup hp rel)
    (schemaFamiliesSafe hp rel)

/-- Sokoban's simple heuristic is admissible for every pinned task. -/
theorem simple_admissible_of_pinned (hp : Pinned d p) (rel : Bool) :
    (ground d p rel).Admissible
      (Planner.ExampleHeuristics.Sokoban.simple (ground d p rel)).eval := by
  apply Planner.ExampleHeuristics.Sokoban.simple_admissible_of_schema
  · exact ground_wf d p rel (cost_pos hp rel)
  · exact goal_nodup hp rel
  · exact schemaFamiliesSafe hp rel

end Planner.Lifted.Sokoban

