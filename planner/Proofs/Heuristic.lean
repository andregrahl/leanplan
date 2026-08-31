/-
The public proof contract for a compiled improved heuristic.

Domain proofs supply goal awareness and consistency for the exact runtime value
under the same executable Boolean that the registry checks.  Admissibility is
then derived here once.  Everything below this interface may use grounding,
numbering, reachability, relevance, and compile-faithfulness infrastructure.
A generated domain proof should import this facade and should not reconstruct
those layers itself.
-/
import Proofs.StepView
import Proofs.LiftedHeuristic
import Proofs.FactTables
import Proofs.CompileSupport
import Proofs.SchemaSupport
import Proofs.Certificates
import Proofs.Distance
import Proofs.Validation
import Planner.ExampleHeuristics.Certificate

namespace Planner

/--
The uniform final evidence exported by every improved-heuristic proof.

`check` is the conjunction of the named runtime checks.  The two fields concern
the compiled heuristic the search evaluates, not an abstract surrogate.
-/
structure ImprovedProof (d : Pddl.Domain) (p : Pddl.Problem) (rel : Bool)
    (check : Bool) (h : Heuristic) : Prop where
  goalAware : check = true →
    (ground d p rel).GoalAwareOn (Reachable (ground d p rel)) h.eval
  consistent : check = true →
    (ground d p rel).ConsistentOn (Reachable (ground d p rel)) h.eval

namespace Certificate

/-! Reusable soundness lemmas for the common finite object checks. -/

theorem hasObject_sound {d : Pddl.Domain} {p : Pddl.Problem} {ty : Pddl.Name}
    (h : hasObject d p ty = true) :
    ∃ o ∈ Pddl.allObjects d p, o.type = ty := by
  rw [hasObject, List.any_eq_true] at h
  obtain ⟨o, ho, ht⟩ := h
  exact ⟨o, ho, by simpa using ht⟩

theorem objectNamedWithType_sound {d : Pddl.Domain} {p : Pddl.Problem}
    {name ty : Pddl.Name} (h : objectNamedWithType d p name ty = true) :
    ∃ o ∈ Pddl.allObjects d p, o.name = name ∧ o.type = ty := by
  rw [objectNamedWithType, List.any_eq_true] at h
  obtain ⟨o, ho, hboth⟩ := h
  rw [Bool.and_eq_true] at hboth
  exact ⟨o, ho, by simpa using hboth.1, by simpa using hboth.2⟩

theorem exactType_sound {d : Pddl.Domain} {p : Pddl.Problem} {ty : Pddl.Name}
    (h : exactType d p ty = true) :
    ∀ o ∈ Pddl.allObjects d p,
      d.isSubtype o.type ty = true → o.type = ty := by
  rw [exactType, List.all_eq_true] at h
  intro o ho hs
  have ht := h o ho
  simp only [Bool.or_eq_true] at ht
  rcases ht with hnot | heq
  · have hf : d.isSubtype o.type ty = false := by simpa using hnot
    rw [hf] at hs
    contradiction
  · simpa using heq

theorem disjointTypes_sound {d : Pddl.Domain} {p : Pddl.Problem}
    {left right : Pddl.Name} (h : disjointTypes d p left right = true) :
    ∀ o ∈ Pddl.allObjects d p,
      d.isSubtype o.type left = true → d.isSubtype o.type right = false := by
  rw [disjointTypes, List.all_eq_true] at h
  intro o ho hl
  have hd := h o ho
  simp only [Bool.or_eq_true] at hd
  rcases hd with hleft | hright
  · have hf : d.isSubtype o.type left = false := by simpa using hleft
    rw [hf] at hl
    contradiction
  · simpa using hright

end Certificate

/-- Certificate-conditioned admissibility, derived once from the final contract. -/
theorem ImprovedProof.admissible {d : Pddl.Domain} {p : Pddl.Problem} {rel : Bool}
    {check : Bool} {h : Heuristic} (hp : ImprovedProof d p rel check h)
    (hc : check = true) :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel)) h.eval :=
  (ground d p rel).admissibleOn _ h.eval (reachable_invariant _)
    (hp.goalAware hc) (hp.consistent hc)

end Planner
