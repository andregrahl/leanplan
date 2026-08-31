/-
The properties of the shared heuristic machinery in `Planner/ExampleHeuristics/Base.lean`.

Two things are proved here and used by every domain file.

`countMissing_eq` connects the array fold the planner runs to the `List.countP`
that the counting lemmas of `Proofs/Combinators.lean` are stated about.

`maxMissingOver` — the pattern all ten *simple* heuristics are built from — is
goal-aware and consistent under one hypothesis per domain: no operator adds two
facts of the same family.  That hypothesis is a statement about the grounded
operators, and `Proofs/Grounding.lean` derives it from the domain's schemas, so
each domain file supplies only the syntactic reason why its families are safe.
-/
import Proofs.Combinators
import Planner.ExampleHeuristics.Base

namespace Planner

/-! ### The executable count is the count the lemmas talk about -/

private theorem foldl_count (p : Fact → Bool) (l : List Fact) :
    ∀ a : Nat, l.foldl (fun acc g => if p g then acc else acc + 1) a
      = a + l.countP (fun g => !p g) := by
  induction l with
  | nil => intro a; simp
  | cons g rest ih =>
      intro a
      by_cases hg : p g <;>
        simp [List.foldl_cons, hg, ih, Nat.add_assoc, Nat.add_comm]

theorem countMissing_eq (facts : Array Fact) (s : State) :
    countMissing facts s = missing facts.toList s := by
  simp only [countMissing, missing, ← Array.foldl_toList]
  simpa using foldl_count (fun g => s.test g) facts.toList 0

/-! ### The simple heuristic pattern -/

private theorem foldl_max_init (l : List Nat) :
    ∀ b : Nat, l.foldl max b = max b (l.foldl max 0) := by
  induction l with
  | nil => intro b; simp
  | cons a rest ih =>
      intro b
      rw [List.foldl_cons, ih (max b a), List.foldl_cons, ih (max 0 a)]
      simp [Nat.max_assoc]

/-- The maximum, over families, of the unsatisfied-goal count. -/
def missingMax (families : List (Array Fact)) (s : State) : Nat :=
  (families.map fun fam => missing fam.toList s).foldl max 0

@[simp] theorem missingMax_nil (s : State) : missingMax [] s = 0 := rfl

theorem missingMax_cons (fam : Array Fact) (rest : List (Array Fact)) (s : State) :
    missingMax (fam :: rest) s = max (missing fam.toList s) (missingMax rest s) := by
  simp only [missingMax, List.map_cons, List.foldl_cons, Nat.zero_max]
  exact foldl_max_init _ _

/-- The heuristic the planner runs is exactly `missingMax` over its families. -/
theorem maxMissingOf_eval (name : String) (families : List (Array Fact)) (s : State) :
    (maxMissingOf name families).eval s = missingMax families s := by
  simp only [maxMissingOf, missingMax, countMissing_eq, ← Array.foldl_toList]
  simp [List.foldl_map]

/--
A *family* of goal facts is safe when no operator can make two of its members
true at once.  This is the only thing the consistency proof needs, and it is a
syntactic property of the domain's add effects.
-/
def Task.FamilySafe (t : Task) (family : Array Fact) : Prop :=
  ∀ op ∈ t.ops, ∃ x : Fact, ∀ f ∈ family, f ≠ x → op.add.contains f = false

/-- The decidable certificate really does establish family safety. -/
theorem familySafe_of_check {t : Task} {family : Array Fact}
    (h : t.familySafe family = true) : t.FamilySafe family := by
  simp only [Task.familySafe, Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true] at h
  intro op hop
  obtain ⟨-, hall⟩ := h
  obtain ⟨j, hj, hjop⟩ := Array.getElem_of_mem hop
  have hsize := hall j hj
  rw [hjop] at hsize
  -- The facts of the family that this operator adds; there is at most one.
  set sel := family.filter (op.add.contains ·) with hsel
  by_cases hzero : sel.size = 0
  · refine ⟨0, ?_⟩
    intro f hf _
    by_contra hcon
    have : f ∈ sel := by
      simp only [hsel, Array.mem_filter]
      exact ⟨hf, by simpa using hcon⟩
    have : 0 < sel.size := Array.size_pos_of_mem this
    omega
  · have hone : sel.size = 1 := by omega
    have hlt : 0 < sel.size := by omega
    refine ⟨sel[0], ?_⟩
    intro f hf hne
    by_contra hcon
    apply hne
    have hadd : op.add.contains f = true := by simpa using hcon
    have hmem : f ∈ sel := by
      simp only [hsel, Array.mem_filter]
      exact ⟨hf, hadd⟩
    obtain ⟨k, hk, hkf⟩ := Array.getElem_of_mem hmem
    have : k = 0 := by omega
    subst this
    exact hkf.symm

/-- The count of unsatisfied facts in a safe family is consistent. -/
theorem Task.consistent_missing (t : Task) (hwf : Task.WF t) (family : Array Fact)
    (hnd : family.toList.Nodup) (hsafe : t.FamilySafe family) :
    t.Consistent fun s => missing family.toList s := by
  refine t.consistent_of_ops _ ?_
  intro op hop s hs _
  obtain ⟨x, hx⟩ := hsafe op hop
  have hopwf : Op.WF t.numFacts op := hwf.ops op hop
  have key : missing family.toList s ≤ 1 + missing family.toList (op.apply s) := by
    refine missing_le_succ hnd x ?_
    intro f hf hfx hnew
    have hmem : f ∈ family := by simpa using hf
    have hadd : op.add.contains f = false := hx f hmem hfx
    rcases Op.test_apply_le hopwf hs hnew with h | h
    · exact h
    · rw [hadd] at h; exact absurd h (by simp)
  have hcost : 1 ≤ op.cost := hopwf.cost
  omega

/-- A family drawn from the goal is zero exactly when its goals hold. -/
theorem Task.goalAware_missing (t : Task) (family : Array Fact)
    (hsub : ∀ f ∈ family, f ∈ t.goal) :
    t.GoalAware fun s => missing family.toList s := by
  refine t.goalAware_of _ ?_
  intro s _ hgoal
  exact missing_eq_zero fun f hf => hgoal f (hsub f (by simpa using hf))

/--
The maximum over several safe families is goal-aware and consistent, hence
admissible: exactly the shape of every *simple* heuristic.
-/
theorem Task.maxMissing_properties (t : Task) (hwf : Task.WF t)
    (families : List (Array Fact))
    (hnd : ∀ fam ∈ families, fam.toList.Nodup)
    (hsub : ∀ fam ∈ families, ∀ f ∈ fam, f ∈ t.goal)
    (hsafe : ∀ fam ∈ families, t.FamilySafe fam) :
    t.GoalAware (missingMax families) ∧ t.Consistent (missingMax families) := by
  induction families with
  | nil =>
      exact ⟨fun s _ _ => by simp, fun s i s' _ _ => by simp⟩
  | cons fam rest ih =>
      have hrest := ih (fun f hf => hnd f (by simp [hf]))
        (fun f hf => hsub f (by simp [hf])) (fun f hf => hsafe f (by simp [hf]))
      have hga : t.GoalAware fun s => missing fam.toList s :=
        t.goalAware_missing fam (hsub fam (by simp))
      have hcon : t.Consistent fun s => missing fam.toList s :=
        t.consistent_missing hwf fam (hnd fam (by simp)) (hsafe fam (by simp))
      have hEq : missingMax (fam :: rest)
          = fun s => max (missing fam.toList s) (missingMax rest s) :=
        funext fun s => missingMax_cons fam rest s
      rw [hEq]
      exact ⟨goalAware_max hga hrest.1, consistent_max hcon hrest.2⟩

/-! ### The certificate is all a simple heuristic needs -/

theorem nodup_of_check {t : Task} {family : Array Fact}
    (h : t.familySafe family = true) : family.toList.Nodup := by
  simp only [Task.familySafe, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem goalFactsWith_subset (t : Task) (preds : List Pddl.Name) :
    ∀ f ∈ t.goalFactsWith preds, f ∈ t.goal := by
  intro f hf
  simp only [Task.goalFactsWith, Array.mem_filter] at hf
  exact hf.1

/--
Everything the simple heuristics need, from one decidable check: the maximum over
goal-predicate families of the unsatisfied-goal count is goal-aware, consistent
and therefore admissible.
-/
theorem Task.maxMissingOf_admissible (t : Task) (hwf : Task.WF t) (name : String)
    (preds : List (List Pddl.Name))
    (hcert : t.familiesSafe (t.families preds) = true) :
    t.GoalAware (maxMissingOf name (t.families preds)).eval ∧
    t.Consistent (maxMissingOf name (t.families preds)).eval ∧
    t.Admissible (maxMissingOf name (t.families preds)).eval := by
  have hcheck : ∀ fam ∈ t.families preds, t.familySafe fam = true := by
    simpa [Task.familiesSafe, List.all_eq_true] using hcert
  have hnd : ∀ fam ∈ t.families preds, fam.toList.Nodup :=
    fun fam hfam => nodup_of_check (hcheck fam hfam)
  have hsafe : ∀ fam ∈ t.families preds, t.FamilySafe fam :=
    fun fam hfam => familySafe_of_check (hcheck fam hfam)
  have hsub : ∀ fam ∈ t.families preds, ∀ f ∈ fam, f ∈ t.goal := by
    intro fam hfam
    simp only [Task.families, List.mem_map] at hfam
    obtain ⟨ps, -, rfl⟩ := hfam
    exact goalFactsWith_subset t ps
  obtain ⟨hga, hcon⟩ := t.maxMissing_properties hwf (t.families preds) hnd hsub hsafe
  have heq : (maxMissingOf name (t.families preds)).eval = missingMax (t.families preds) :=
    funext fun s => maxMissingOf_eval name (t.families preds) s
  rw [heq]
  exact ⟨hga, hcon, t.admissible _ hga hcon⟩

end Planner
