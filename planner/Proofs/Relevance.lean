/-
Pruning irrelevant operators keeps every plan.

`relevanceAnalysis` drops operators that touch no relevant fact and trims the
add and delete lists of the ones it keeps.  `Proofs/GroundingSound.lean` shows
this only ever removes; what is proved here is that removing costs nothing — a
state's relevant facts evolve the same way whether the dropped operators are
applied or not, and the goal reads only relevant facts.

The set the analysis settles on has to be *closed*: every operator that touches
it has its whole precondition inside it.  That is what the fixpoint computes, and
`relevantOK` is the decidable test for it, which `relevanceAnalysis` now runs
before pruning anything.  Deriving closure from the analysis's own fuel bound
instead is arithmetic about `Std.HashSet` sizes and is left open, but nothing rests
on it any more: `relevance_cases` says the analysis either prunes with a verified
set or prunes nothing, and both branches are safe.  The check has never failed on
any task measured, and the operator counts are unchanged.
-/
import Proofs.GroundingCorrect

namespace Planner

open Planner.Pddl

/-- The operator with its effects trimmed to `r`, as the analysis keeps it. -/
def AtomOp.trim (o : AtomOp) (r : Std.HashSet GroundAtom) : AtomOp :=
  { o with add := o.add.filter r.contains, del := o.del.filter r.contains }

/-- Every operator that writes into `r` reads only from `r`. -/
def Closed (ops : Array AtomOp) (r : Std.HashSet GroundAtom) : Prop :=
  ∀ o ∈ ops, o.touches r = true → ∀ f ∈ o.pre, r.contains f = true

/-- The decidable test for it, which `relevanceAnalysis` now runs. -/
abbrev closedCheck (ops : Array AtomOp) (r : Std.HashSet GroundAtom) : Bool :=
  ops.all fun o => !o.touches r || o.pre.all r.contains

theorem closed_of_check {ops : Array AtomOp} {r : Std.HashSet GroundAtom}
    (h : closedCheck ops r = true) : Closed ops r := by
  intro o ho htouch f hf
  obtain ⟨i, hi, hival⟩ := Array.getElem_of_mem ho
  simp only [closedCheck, Array.all_eq_true] at h
  have hthis := h i hi
  rw [hival] at hthis
  simp only [htouch, Bool.not_true, Bool.false_or, Array.all_eq_true] at hthis
  obtain ⟨j, hj, hjval⟩ := Array.getElem_of_mem hf
  have hfin := hthis j hj
  rwa [hjval] at hfin

/-- Two atom-level states that agree wherever it matters. -/
def AgreeOn (r : Std.HashSet GroundAtom) (σ τ : AtomState) : Prop :=
  ∀ a, r.contains a = true → σ a = τ a

theorem AgreeOn.refl (r : Std.HashSet GroundAtom) (σ : AtomState) : AgreeOn r σ σ :=
  fun _ _ => rfl

theorem AgreeOn.trans {r : Std.HashSet GroundAtom} {σ τ υ : AtomState}
    (h1 : AgreeOn r σ τ) (h2 : AgreeOn r τ υ) : AgreeOn r σ υ :=
  fun a ha => (h1 a ha).trans (h2 a ha)

/-! ### An operator that writes nothing relevant changes nothing relevant -/

theorem agree_of_untouched {o : AtomOp} {r : Std.HashSet GroundAtom}
    (h : o.touches r = false) (σ : AtomState) : AgreeOn r (o.applyA σ) σ := by
  intro a ha
  have hna : a ∉ o.add := by
    intro hmem
    have hany : o.add.any r.contains = true := by
      rw [Array.any_eq_true]
      obtain ⟨i, hi, hival⟩ := Array.getElem_of_mem hmem
      exact ⟨i, hi, by rw [hival]; exact ha⟩
    simp [AtomOp.touches, hany] at h
  have hnd : a ∉ o.del := by
    intro hmem
    have hany : o.del.any r.contains = true := by
      rw [Array.any_eq_true]
      obtain ⟨i, hi, hival⟩ := Array.getElem_of_mem hmem
      exact ⟨i, hi, by rw [hival]; exact ha⟩
    simp [AtomOp.touches, hany] at h
  simp [AtomOp.applyA, hna, hnd]

/-! ### An operator that is kept acts the same on the relevant facts -/

private theorem contains_filter {arr : Array GroundAtom} {r : Std.HashSet GroundAtom}
    {a : GroundAtom} (ha : r.contains a = true) :
    (arr.filter r.contains).contains a = arr.contains a := by
  by_cases h : a ∈ arr
  · have hf : a ∈ arr.filter r.contains := Array.mem_filter.mpr ⟨h, ha⟩
    simp [hf, h]
  · have hf : a ∉ arr.filter r.contains := fun hc => h (Array.mem_filter.mp hc).1
    simp [hf, h]

theorem trim_step {o : AtomOp} {r : Std.HashSet GroundAtom} {σ τ : AtomState}
    (hagree : AgreeOn r σ τ) : AgreeOn r (o.applyA σ) ((o.trim r).applyA τ) := by
  intro a ha
  have hA : (o.add.filter r.contains).contains a = o.add.contains a := contains_filter ha
  have hD : (o.del.filter r.contains).contains a = o.del.contains a := contains_filter ha
  show (if o.add.contains a = true then true
        else if o.del.contains a = true then false else σ a)
      = (if (o.add.filter r.contains).contains a = true then true
         else if (o.del.filter r.contains).contains a = true then false else τ a)
  rw [hA, hD]
  by_cases hadd : o.add.contains a = true
  · rw [if_pos hadd, if_pos hadd]
  · rw [if_neg hadd, if_neg hadd]
    by_cases hdel : o.del.contains a = true
    · rw [if_pos hdel, if_pos hdel]
    · rw [if_neg hdel, if_neg hdel]
      exact hagree a ha

theorem trim_applicable {o : AtomOp} {r : Std.HashSet GroundAtom}
    {ops : Array AtomOp} (hclosed : Closed ops r) (ho : o ∈ ops)
    (htouch : o.touches r = true) {σ τ : AtomState} (hagree : AgreeOn r σ τ)
    (happ : o.applicableA σ) : (o.trim r).applicableA τ := by
  intro f hf
  have hfr : r.contains f = true := hclosed o ho htouch f (by simpa [AtomOp.trim] using hf)
  rw [← hagree f hfr]
  exact happ f (by simpa [AtomOp.trim] using hf)

/-! ### The goal reads only relevant facts -/

theorem goal_transfer {r : Std.HashSet GroundAtom} {goal : Array GroundAtom}
    (hgoal : ∀ a ∈ goal, r.contains a = true) {σ τ : AtomState} (hagree : AgreeOn r σ τ)
    (h : ∀ a ∈ goal, σ a = true) : ∀ a ∈ goal, τ a = true := by
  intro a ha
  rw [← hagree a (hgoal a ha)]
  exact h a ha

/-! ### Executing a list of operators -/

/-- Running operators one after another at the atom level. -/
inductive ExecOps : AtomState → List AtomOp → AtomState → Prop
  | nil (σ : AtomState) : ExecOps σ [] σ
  | cons {σ final : AtomState} {o : AtomOp} {rest : List AtomOp}
      (happ : o.applicableA σ) (hrest : ExecOps (o.applyA σ) rest final) :
      ExecOps σ (o :: rest) final

/-- What a list of operators costs. -/
def planCostA (plan : List AtomOp) : Nat := (plan.map (·.cost)).sum

@[simp] theorem planCostA_nil : planCostA [] = 0 := rfl

@[simp] theorem planCostA_cons (o : AtomOp) (rest : List AtomOp) :
    planCostA (o :: rest) = o.cost + planCostA rest := rfl

@[simp] theorem trim_cost (o : AtomOp) (r : Std.HashSet GroundAtom) :
    (o.trim r).cost = o.cost := rfl

/--
**Pruning keeps every plan.**  From any state agreeing with `σ` on the relevant
facts, the plan with its irrelevant operators dropped and the rest trimmed reaches
the goal, and costs no more.
-/
theorem prune_preserves {ops : Array AtomOp} {r : Std.HashSet GroundAtom}
    {goal : Array GroundAtom} (hclosed : Closed ops r)
    (hgoal : ∀ a ∈ goal, r.contains a = true) :
    ∀ {σ : AtomState} {plan : List AtomOp} {final : AtomState},
      ExecOps σ plan final → (∀ o ∈ plan, o ∈ ops) →
      (∀ a ∈ goal, final a = true) →
      ∀ {τ : AtomState}, AgreeOn r σ τ →
        ∃ (plan' : List AtomOp) (final' : AtomState),
          (∀ o ∈ plan', ∃ p ∈ plan, p ∈ ops ∧ p.touches r = true ∧ o = p.trim r) ∧
          planCostA plan' ≤ planCostA plan ∧
          ExecOps τ plan' final' ∧ (∀ a ∈ goal, final' a = true) := by
  intro σ plan final hexec
  induction hexec with
  | nil σ =>
      intro _ hg τ hagree
      exact ⟨[], τ, by simp, by simp, ExecOps.nil τ,
        goal_transfer hgoal hagree hg⟩
  | @cons σ final o rest happ hrest ih =>
      intro hsub hg τ hagree
      have ho : o ∈ ops := hsub o (by simp)
      have hsub' : ∀ q ∈ rest, q ∈ ops := fun q hq => hsub q (by simp [hq])
      by_cases htouch : o.touches r = true
      · obtain ⟨plan', final', hshape, hcost, hexec', hgoal'⟩ :=
          ih hsub' hg (τ := (o.trim r).applyA τ) (trim_step hagree)
        refine ⟨o.trim r :: plan', final', ?_, by simp; omega, ?_, hgoal'⟩
        · intro q hq
          rcases List.mem_cons.mp hq with rfl | hq'
          · exact ⟨o, by simp, ho, htouch, rfl⟩
          · obtain ⟨p, hp, hpo, hpt, hpe⟩ := hshape q hq'
            exact ⟨p, by simp [hp], hpo, hpt, hpe⟩
        · exact ExecOps.cons (trim_applicable hclosed ho htouch hagree happ) hexec'
      · have hfalse : o.touches r = false := by simpa using htouch
        have hagree' : AgreeOn r (o.applyA σ) τ :=
          (agree_of_untouched hfalse σ).trans hagree
        obtain ⟨plan', final', hshape, hcost, hexec', hgoal'⟩ := ih hsub' hg hagree'
        refine ⟨plan', final', ?_, by simp; omega, hexec', hgoal'⟩
        intro q hq
        obtain ⟨p, hp, hpo, hpt, hpe⟩ := hshape q hq
        exact ⟨p, by simp [hp], hpo, hpt, hpe⟩

/-! ### The kept operators are the ones the analysis keeps -/

private theorem isEmpty_false_of_mem {α : Type} {arr : Array α} {x : α}
    (hx : x ∈ arr) : arr.isEmpty = false := by
  by_contra hc
  have hemp : arr = #[] := by
    have : arr.isEmpty = true := by simpa using hc
    simpa [Array.isEmpty_iff] using this
  rw [hemp] at hx
  simp at hx

/--
An operator that writes into the relevant set survives the analysis, trimmed.
`hrdef` is `rfl` at the use site; it is a parameter only so the statement does not
depend on how the fixpoint's set is spelled.
-/
theorem mem_relevance_of_touches {ops : Array AtomOp} {goal : Array GroundAtom}
    {o : AtomOp} (ho : o ∈ ops) (r : Std.HashSet GroundAtom)
    (hrdef : relevanceAnalysis ops goal = ops.filterMap fun op =>
        if ((op.add.filter r.contains).isEmpty && (op.del.filter r.contains).isEmpty)
        then none
        else some (AtomOp.trim op r))
    (htouch : o.touches r = true) : o.trim r ∈ relevanceAnalysis ops goal := by
  rw [hrdef, Array.mem_filterMap]
  refine ⟨o, ho, ?_⟩
  have hfalse : ((o.add.filter r.contains).isEmpty
      && (o.del.filter r.contains).isEmpty) = false := by
    simp only [AtomOp.touches, Bool.or_eq_true, Array.any_eq_true] at htouch
    rcases htouch with ⟨i, hi, hval⟩ | ⟨i, hi, hval⟩
    · have hmem : o.add[i] ∈ o.add.filter r.contains :=
        Array.mem_filter.mpr ⟨Array.getElem_mem hi, hval⟩
      simp [isEmpty_false_of_mem hmem]
    · have hmem : o.del[i] ∈ o.del.filter r.contains :=
        Array.mem_filter.mpr ⟨Array.getElem_mem hi, hval⟩
      simp [isEmpty_false_of_mem hmem]
  rw [hfalse]
  simp [AtomOp.trim]

/-! ### Pruning keeps every effect on a precondition

A surviving operator's preconditions are all relevant — that is what closure
says — so any effect of it on one of them is kept.  This is what lets a heuristic
rely on `up` really deleting the `lift-at` it required, with pruning on.
-/

theorem touches_of_nonempty {o : AtomOp} {r : Std.HashSet GroundAtom}
    (h : ¬((o.add.filter r.contains).isEmpty && (o.del.filter r.contains).isEmpty)) :
    o.touches r = true := by
  simp only [Bool.and_eq_true, Bool.not_eq_true, not_and] at h
  simp only [AtomOp.touches, Bool.or_eq_true, Array.any_eq_true]
  by_cases hadd : (o.add.filter r.contains).isEmpty = true
  · have hdel := h hadd
    have hne : (o.del.filter r.contains) ≠ #[] := by
      intro hc; rw [hc] at hdel; simp at hdel
    obtain ⟨x, hx⟩ := Array.exists_mem_of_ne_empty _ hne
    obtain ⟨hmem, hr⟩ := Array.mem_filter.mp hx
    obtain ⟨i, hi, hval⟩ := Array.getElem_of_mem hmem
    exact Or.inr ⟨i, hi, by rw [hval]; exact hr⟩
  · have hne : (o.add.filter r.contains) ≠ #[] := by
      intro hc; rw [hc] at hadd; simp at hadd
    obtain ⟨x, hx⟩ := Array.exists_mem_of_ne_empty _ hne
    obtain ⟨hmem, hr⟩ := Array.mem_filter.mp hx
    obtain ⟨i, hi, hval⟩ := Array.getElem_of_mem hmem
    exact Or.inl ⟨i, hi, by rw [hval]; exact hr⟩

/--
**An effect on a precondition survives pruning.**  With `Closed`, every atom the
operator reads is relevant, so every add or delete of such an atom is retained.
-/
theorem relevance_retains {ops : Array AtomOp} {goal : Array GroundAtom}
    {r : Std.HashSet GroundAtom} (hclosed : Closed ops r)
    (hrdef : relevanceAnalysis ops goal = ops.filterMap fun op =>
        if ((op.add.filter r.contains).isEmpty && (op.del.filter r.contains).isEmpty)
        then none else some (AtomOp.trim op r))
    {op' : AtomOp} (hop' : op' ∈ relevanceAnalysis ops goal) :
    ∃ op ∈ ops, op' = op.trim r ∧
      (∀ a ∈ op.add, a ∈ op.pre → a ∈ op'.add) ∧
      (∀ a ∈ op.del, a ∈ op.pre → a ∈ op'.del) := by
  rw [hrdef, Array.mem_filterMap] at hop'
  obtain ⟨op, hop, hval⟩ := hop'
  split at hval
  · exact absurd hval (by simp)
  · rename_i hne
    rw [Option.some.injEq] at hval
    subst hval
    have htouch : op.touches r = true := touches_of_nonempty (by simpa using hne)
    refine ⟨op, hop, rfl, ?_, ?_⟩
    · intro a ha hpre
      exact Array.mem_filter.mpr ⟨ha, hclosed op hop htouch a hpre⟩
    · intro a ha hpre
      exact Array.mem_filter.mpr ⟨ha, hclosed op hop htouch a hpre⟩

/-! ### The analysis prunes only with a set it has verified

`relevanceAnalysis` runs `relevantOK` on the set the fixpoint settles on and
prunes nothing when the test fails.  So one of two things is always true of what
it returns, and neither has to be assumed.
-/

theorem relevance_cases (ops : Array AtomOp) (goal : Array GroundAtom) :
    (∃ r : Std.HashSet GroundAtom, Closed ops r ∧ (∀ a ∈ goal, r.contains a = true) ∧
      relevanceAnalysis ops goal = ops.filterMap fun op =>
        if ((op.add.filter r.contains).isEmpty && (op.del.filter r.contains).isEmpty)
        then none else some (AtomOp.trim op r))
    ∨ relevanceAnalysis ops goal = ops := by
  unfold relevanceAnalysis
  simp only
  split
  · rename_i hok
    obtain ⟨hgoal, hclosed⟩ := Bool.and_eq_true_iff.mp hok
    refine Or.inl ⟨relevantSet ops goal, closed_of_check hclosed, ?_, rfl⟩
    intro a ha
    obtain ⟨i, hi, hival⟩ := Array.getElem_of_mem ha
    rw [Array.all_eq_true] at hgoal
    have := hgoal i hi
    rwa [hival] at this
  · exact Or.inr rfl

/-- The relevant set, when the analysis verified one. -/
theorem relevance_verified {ops : Array AtomOp} {goal : Array GroundAtom}
    (h : relevantOK ops goal (relevantSet ops goal) = true) :
    Closed ops (relevantSet ops goal) ∧
    (∀ a ∈ goal, (relevantSet ops goal).contains a = true) ∧
    relevanceAnalysis ops goal = ops.filterMap fun op =>
      if ((op.add.filter (relevantSet ops goal).contains).isEmpty &&
        (op.del.filter (relevantSet ops goal).contains).isEmpty)
      then none else some (AtomOp.trim op (relevantSet ops goal)) := by
  obtain ⟨hgoal, hclosed⟩ := Bool.and_eq_true_iff.mp h
  refine ⟨closed_of_check hclosed, ?_, ?_⟩
  · intro a ha
    obtain ⟨i, hi, hival⟩ := Array.getElem_of_mem ha
    rw [Array.all_eq_true] at hgoal
    have := hgoal i hi
    rwa [hival] at this
  · unfold relevanceAnalysis
    simp only [h, if_true]
    rfl

end Planner
