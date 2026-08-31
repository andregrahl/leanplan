/-
Correctness of the compiled trigger index.

The generator is only a candidate filter: ordinary operator applicability is
still checked before an ID is returned.  The two public endpoints therefore say
that every returned ID names an applicable operator and every applicable
operator is returned.
-/
import Mathlib.Tactic
import Proofs.Task
import Planner.Search.SuccessorGenerator

namespace Planner

namespace SuccessorGenerator

theorem mem_fallback {t : Task} {i : Nat} :
    i ∈ (compileSuccessorGenerator t).fallback ↔
      i < t.ops.size ∧ operatorTrigger? t i = none := by
  constructor
  · intro h
    obtain ⟨hrange, hnone⟩ := Array.mem_filter.mp h
    exact ⟨by simpa using hrange, by simpa using hnone⟩
  · rintro ⟨hi, hnone⟩
    exact Array.mem_filter.mpr ⟨by simpa using hi, by simp [hnone]⟩

theorem mem_byFact {t : Task} {i f : Nat} (hf : f < t.numFacts) :
    i ∈ (compileSuccessorGenerator t).byFact.getD f #[] ↔
      i < t.ops.size ∧ operatorTrigger? t i = some f := by
  constructor
  · intro h
    have hbucket : (compileSuccessorGenerator t).byFact.getD f #[] =
        (Array.range t.ops.size).filter fun i => operatorTrigger? t i == some f := by
      simp [compileSuccessorGenerator, hf]
    rw [hbucket] at h
    obtain ⟨hrange, heq⟩ := Array.mem_filter.mp h
    exact ⟨by simpa using hrange, eq_of_beq heq⟩
  · rintro ⟨hi, heq⟩
    have hbucket : (compileSuccessorGenerator t).byFact.getD f #[] =
        (Array.range t.ops.size).filter fun i => operatorTrigger? t i == some f := by
      simp [compileSuccessorGenerator, hf]
    rw [hbucket]
    exact Array.mem_filter.mpr ⟨by simpa using hi, by simp [heq]⟩

theorem collect_keeps {g : SuccessorGenerator} {s : State} {i : Nat} :
    ∀ (fuel start : Nat) (ids : Array Nat), i ∈ ids →
      i ∈ collect g s fuel start ids := by
  intro fuel
  induction fuel with
  | zero => exact fun _ _ hi => hi
  | succ fuel ih =>
      intro start ids hi
      rw [collect]
      split
      · split
        · exact ih _ _ (Array.mem_append.mpr (Or.inl hi))
        · exact ih _ _ hi
      · exact hi

theorem collect_adds_bucket {g : SuccessorGenerator} {s : State} {opId f : Nat} :
    ∀ (fuel start : Nat) (ids : Array Nat), start ≤ f → f < start + fuel →
      f < g.numFacts → s.test f = true → opId ∈ g.byFact.getD f #[] →
      opId ∈ collect g s fuel start ids := by
  intro fuel
  induction fuel with
  | zero => intro start ids _ hlt; omega
  | succ fuel ih =>
      intro start ids hstart hend hbound htrue hmem
      rw [collect]
      have hstartBound : start < g.numFacts := by omega
      rw [if_pos hstartBound]
      by_cases heq : start = f
      · subst start
        simp only [htrue, if_true]
        exact collect_keeps _ _ _ (Array.mem_append.mpr (Or.inr hmem))
      · have hnext : start + 1 ≤ f := by omega
        split
        · exact ih _ _ hnext (by omega) hbound htrue hmem
        · exact ih _ _ hnext (by omega) hbound htrue hmem

theorem mem_candidates_of_fallback {g : SuccessorGenerator} {s : State} {i : Nat}
    (hi : i ∈ g.fallback) : i ∈ g.candidates s :=
  collect_keeps _ _ _ hi

theorem mem_candidates_of_bucket {g : SuccessorGenerator} {s : State} {i f : Nat}
    (hf : f < g.numFacts) (htrue : s.test f = true)
    (hi : i ∈ g.byFact.getD f #[]) : i ∈ g.candidates s := by
  exact collect_adds_bucket g.numFacts 0 g.fallback (by omega) (by omega) hf htrue hi

theorem trigger_precondition {t : Task} {i f : Nat} (hi : i < t.ops.size)
    (htrigger : operatorTrigger? t i = some f) :
    f < t.numFacts ∧ f ∈ t.ops[i].pre := by
  have hop : t.ops[i]? = some t.ops[i] := by simp [hi]
  simp only [operatorTrigger?, hop] at htrigger
  split at htrigger
  · rename_i f' hpre
    split at htrigger
    · rename_i hlt
      have hff : f' = f := by simpa using htrigger
      subst f'
      refine ⟨hlt, ?_⟩
      have hlist : t.ops[i].pre.toList[0]? = some f := by simpa using hpre
      simpa using List.mem_of_getElem? hlist
    · simp at htrigger
  · simp at htrigger

theorem applicable_mem_candidates {t : Task} {s : State} {i : Nat}
    (hi : i < t.ops.size) (happ : t.ops[i].applicable s = true) :
    i ∈ (compileSuccessorGenerator t).candidates s := by
  cases htrigger : operatorTrigger? t i with
  | none =>
      exact mem_candidates_of_fallback (mem_fallback.mpr ⟨hi, htrigger⟩)
  | some f =>
      obtain ⟨hf, hpre⟩ := trigger_precondition hi htrigger
      have htrue : s.test f = true := (Op.applicable_iff.mp happ) f hpre
      exact mem_candidates_of_bucket hf htrue
        (mem_byFact hf |>.mpr ⟨hi, htrigger⟩)

theorem collect_valid {t : Task} {s : State} :
    ∀ (fuel start : Nat) (ids : Array Nat),
      (∀ i ∈ ids, i < t.ops.size) →
      start + fuel ≤ t.numFacts →
      ∀ i ∈ collect (compileSuccessorGenerator t) s fuel start ids, i < t.ops.size := by
  intro fuel
  induction fuel with
  | zero => exact fun _ _ hids _ => hids
  | succ fuel ih =>
      intro start ids hids hrange i hi
      rw [collect] at hi
      split at hi
      · rename_i hstart
        split at hi
        · apply ih _ _ _ (by omega) i hi
          intro j hj
          rcases Array.mem_append.mp hj with hj | hj
          · exact hids j hj
          · exact (mem_byFact hstart |>.mp hj).1
        · exact ih _ _ hids (by omega) i hi
      · exact hids i hi

theorem compiled_candidates_valid {t : Task} {s : State} {i : Nat}
    (hi : i ∈ (compileSuccessorGenerator t).candidates s) : i < t.ops.size := by
  apply collect_valid t.numFacts 0 _ _ (by simp) i hi
  intro j hj
  exact (mem_fallback.mp hj).1

/-- Every generated ID is in range and names an applicable operator. -/
theorem applicableIds_sound {t : Task} {s : State} {i : Nat}
    (hi : i ∈ (compileSuccessorGenerator t).applicableIds t s) :
    i < t.ops.size ∧ (t.ops.getD i default).applicable s = true := by
  obtain ⟨hcandidate, happ⟩ := Array.mem_filter.mp hi
  have hlt : i < t.ops.size := compiled_candidates_valid hcandidate
  exact ⟨hlt, happ⟩

/-- Every applicable logical operator is returned by its compiled generator. -/
theorem applicableIds_complete {t : Task} {s : State} {i : Nat}
    (hi : i < t.ops.size) (happ : t.ops[i].applicable s = true) :
    i ∈ (compileSuccessorGenerator t).applicableIds t s := by
  apply Array.mem_filter.mpr
  refine ⟨applicable_mem_candidates hi happ, ?_⟩
  simpa [Array.getD, hi] using happ

end SuccessorGenerator

end Planner
