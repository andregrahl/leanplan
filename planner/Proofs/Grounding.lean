/-
Grounding: every fact the planner touches is in range.

This is the property the rest of the development rests on.  `Task.WF` says the
initial state has the right number of words, every goal fact is below `numFacts`,
and every operator's precondition, add and delete lists are too.  Every heuristic
proof assumes it, and `astar_optimal` needs it of the initial state, so without it
the chain from "the heuristic is admissible" to "the planner returns an optimal
plan" has a hole in the middle.

What makes it true is the fact numbering.  `factIndex` walks the atoms in order of
first appearance and hands each a fresh number equal to the count of names so far,
so an atom's index is always below the final count — and every atom of every
surviving operator, together with every goal atom, is in that walk by
construction.  `factIndex_lt` is that argument, and `ground_wf` reads it off.

Not proved here: that the grounded task *denotes* the lifted PDDL semantics —
that operators correspond to well-typed schema instances and that the relevance
analysis drops only operators no goal-reaching plan could use.  Those remain
backed by the cross-check against pyperplan's operator sets and by VAL accepting
every plan against the original PDDL.
-/
import Proofs.Task
import Planner.Grounding

namespace Planner

open Planner.Pddl

/-- One step of the numbering fold, named so the proofs can talk about it. -/
private def numberStep (st : Std.HashMap GroundAtom Nat × Array GroundAtom) (a : GroundAtom) :
    Std.HashMap GroundAtom Nat × Array GroundAtom :=
  if st.1.contains a then st else (st.1.insert a st.2.size, st.2.push a)

private theorem factIndex_fold (atoms : Array GroundAtom) :
    factIndex atoms = atoms.toList.foldl numberStep ({}, #[]) := by
  unfold factIndex numberStep
  rw [← Array.foldl_toList]

/-- The invariant the numbering fold maintains: every numbered atom is in range. -/
private def IndexOK (st : Std.HashMap GroundAtom Nat × Array GroundAtom) : Prop :=
  ∀ a, st.1.contains a = true → st.1.getD a 0 < st.2.size

private theorem indexOK_step (st : Std.HashMap GroundAtom Nat × Array GroundAtom)
    (h : IndexOK st) (a : GroundAtom) : IndexOK (numberStep st a) := by
  unfold numberStep
  by_cases hc : st.1.contains a
  · rw [if_pos hc]; exact h
  · rw [if_neg (by simp [hc])]
    intro b hb
    rw [Std.HashMap.contains_insert] at hb
    show (st.1.insert a st.2.size).getD b 0 < (st.2.push a).size
    rw [Std.HashMap.getD_insert, Array.size_push]
    by_cases hab : a == b
    · simp [hab]
    · simp only [hab, if_false]
      simp only [hab, Bool.false_or] at hb
      exact Nat.lt_succ_of_lt (h b hb)

/-- Once an atom is numbered it stays numbered. -/
private theorem numbered_mono (l : List GroundAtom) :
    ∀ (st : Std.HashMap GroundAtom Nat × Array GroundAtom) (b : GroundAtom),
      st.1.contains b = true → (l.foldl numberStep st).1.contains b = true := by
  induction l with
  | nil => intro st b hb; exact hb
  | cons x rest ih =>
      intro st b hb
      refine ih _ b ?_
      unfold numberStep
      by_cases hc : st.1.contains x
      · rw [if_pos hc]; exact hb
      · rw [if_neg (by simp [hc])]
        show (st.1.insert x st.2.size).contains b = true
        rw [Std.HashMap.contains_insert]
        simp [hb]

private theorem fold_ok (l : List GroundAtom) :
    ∀ st : Std.HashMap GroundAtom Nat × Array GroundAtom, IndexOK st →
      IndexOK (l.foldl numberStep st) ∧
        ∀ a ∈ l, (l.foldl numberStep st).1.contains a = true := by
  induction l with
  | nil => intro st h; exact ⟨h, by simp⟩
  | cons x rest ih =>
      intro st h
      obtain ⟨hOK, hall⟩ := ih _ (indexOK_step st h x)
      refine ⟨hOK, ?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha'
      · refine numbered_mono rest _ a ?_
        unfold numberStep
        by_cases hc : st.1.contains a
        · rw [if_pos hc]; exact hc
        · rw [if_neg (by simp [hc])]
          show (st.1.insert a st.2.size).contains a = true
          rw [Std.HashMap.contains_insert]
          simp
      · exact hall a ha'

/-- Every atom of the input is numbered, and below the number of names. -/
theorem factIndex_lt (atoms : Array GroundAtom) :
    ∀ a ∈ atoms, (factIndex atoms).1.getD a 0 < (factIndex atoms).2.size := by
  intro a ha
  rw [factIndex_fold]
  obtain ⟨hOK, hall⟩ := fold_ok atoms.toList ({}, #[]) (by intro b hb; simp at hb)
  exact hOK a (hall a (by simpa using ha))

/-! ### Distinct atoms get distinct numbers

Being in range is only half of what the numbering has to do.  If two different
ground atoms received the same number, the packed bit-set state would conflate
them and the planner would be solving a different problem — one where making one
atom true silently makes another true as well.  Injectivity is what rules that
out, and it holds for the simplest possible reason: each new atom is handed the
current count of names, and every number already handed out is below that count.
-/

/-- The numbering is injective on the atoms it has seen. -/
private def IndexInj (st : Std.HashMap GroundAtom Nat × Array GroundAtom) : Prop :=
  ∀ a b, st.1.contains a = true → st.1.contains b = true →
    st.1.getD a 0 = st.1.getD b 0 → a = b

private theorem indexInj_step (st : Std.HashMap GroundAtom Nat × Array GroundAtom)
    (hOK : IndexOK st) (hInj : IndexInj st) (a : GroundAtom) :
    IndexInj (numberStep st a) := by
  unfold numberStep
  by_cases hc : st.1.contains a
  · rw [if_pos hc]; exact hInj
  · rw [if_neg (by simp [hc])]
    intro x y hx hy hxy
    rw [Std.HashMap.contains_insert] at hx hy
    rw [Std.HashMap.getD_insert, Std.HashMap.getD_insert] at hxy
    by_cases hax : a == x <;> by_cases hay : a == y
    · exact (beq_iff_eq.mp hax).symm.trans (beq_iff_eq.mp hay)
    · -- `x` is the new atom, `y` an old one: their numbers cannot agree
      exfalso
      simp only [hax, hay, if_true, if_false] at hxy
      simp only [hay, Bool.false_or] at hy
      exact absurd hxy.symm (Nat.ne_of_lt (hOK y hy))
    · exfalso
      simp only [hax, hay, if_true, if_false] at hxy
      simp only [hax, Bool.false_or] at hx
      exact absurd hxy (Nat.ne_of_lt (hOK x hx))
    · simp only [hax, hay, if_false] at hxy
      simp only [hax, Bool.false_or] at hx
      simp only [hay, Bool.false_or] at hy
      exact hInj x y hx hy hxy

private theorem fold_inj (l : List GroundAtom) :
    ∀ st : Std.HashMap GroundAtom Nat × Array GroundAtom, IndexOK st → IndexInj st →
      IndexInj (l.foldl numberStep st) := by
  induction l with
  | nil => intro st _ hInj; exact hInj
  | cons x rest ih =>
      intro st hOK hInj
      exact ih _ (indexOK_step st hOK x) (indexInj_step st hOK hInj x)

/-- **Distinct atoms get distinct numbers.** -/
theorem factIndex_injective (atoms : Array GroundAtom) {a b : GroundAtom}
    (ha : a ∈ atoms) (hb : b ∈ atoms)
    (h : (factIndex atoms).1.getD a 0 = (factIndex atoms).1.getD b 0) : a = b := by
  rw [factIndex_fold] at h
  obtain ⟨-, hall⟩ := fold_ok atoms.toList ({}, #[]) (by intro c hc; simp at hc)
  exact fold_inj atoms.toList ({}, #[]) (by intro c hc; simp at hc)
    (by intro c e hc; simp at hc) a b (hall a (by simpa using ha)) (hall b (by simpa using hb)) h

/-! ### The numbering is a bijection

Being in range and injective says the numbering does not conflate atoms.  What
the correspondence with the lifted model needs on top of that is that the names
array really inverts it: fact `f` names the atom that was given number `f`, and
numbering that atom gives `f` back.
-/

/-- Reading a name back gives the number it was numbered with. -/
private def IndexRev (st : Std.HashMap GroundAtom Nat × Array GroundAtom) : Prop :=
  ∀ i, i < st.2.size →
    st.1.contains (st.2.getD i default) = true ∧ st.1.getD (st.2.getD i default) 0 = i

private theorem getD_push_lt' (a : Array GroundAtom) (x : GroundAtom) {j : Nat}
    (h : j < a.size) : (a.push x).getD j default = a.getD j default := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, h, Nat.ne_of_lt h]

private theorem getD_push_eq' (a : Array GroundAtom) (x : GroundAtom) :
    (a.push x).getD a.size default = x := by
  simp [Array.getD_eq_getD_getElem?]

private theorem indexRev_step (st : Std.HashMap GroundAtom Nat × Array GroundAtom)
    (hOK : IndexOK st) (hRev : IndexRev st) (a : GroundAtom) :
    IndexRev (numberStep st a) := by
  unfold numberStep
  by_cases hc : st.1.contains a
  · rw [if_pos hc]; exact hRev
  · rw [if_neg (by simp [hc])]
    intro i hi
    simp only [Array.size_push] at hi
    by_cases hlt : i < st.2.size
    · obtain ⟨hmem, hval⟩ := hRev i hlt
      have hne : (a == st.2.getD i default) = false := by
        by_contra hcon
        simp only [Bool.not_eq_false, beq_iff_eq] at hcon
        rw [hcon] at hc
        exact hc hmem
      refine ⟨?_, ?_⟩
      · show (st.1.insert a st.2.size).contains ((st.2.push a).getD i default) = true
        rw [getD_push_lt' _ _ hlt, Std.HashMap.contains_insert, hmem, Bool.or_true]
      · show (st.1.insert a st.2.size).getD ((st.2.push a).getD i default) 0 = i
        rw [getD_push_lt' _ _ hlt, Std.HashMap.getD_insert,
          if_neg (by simpa [Array.getD_eq_getD_getElem?] using (by simpa using hne :
            ¬ (a = st.2.getD i default)))]
        exact hval
    · have hieq : i = st.2.size := by omega
      subst hieq
      refine ⟨?_, ?_⟩
      · show (st.1.insert a st.2.size).contains ((st.2.push a).getD st.2.size default) = true
        rw [getD_push_eq', Std.HashMap.contains_insert]
        simp
      · show (st.1.insert a st.2.size).getD ((st.2.push a).getD st.2.size default) 0 = st.2.size
        rw [getD_push_eq', Std.HashMap.getD_insert]
        simp

private theorem fold_rev (l : List GroundAtom) :
    ∀ st : Std.HashMap GroundAtom Nat × Array GroundAtom, IndexOK st → IndexRev st →
      IndexRev (l.foldl numberStep st) := by
  induction l with
  | nil => intro st _ hRev; exact hRev
  | cons x rest ih =>
      intro st hOK hRev
      exact ih _ (indexOK_step st hOK x) (indexRev_step st hOK hRev x)

/-- **Numbering a name gives its own number back.** -/
theorem factIndex_rev (atoms : Array GroundAtom) (i : Nat)
    (hi : i < (factIndex atoms).2.size) :
    (factIndex atoms).1.contains ((factIndex atoms).2.getD i default) = true ∧
      (factIndex atoms).1.getD ((factIndex atoms).2.getD i default) 0 = i := by
  rw [factIndex_fold] at hi ⊢
  exact fold_rev atoms.toList ({}, #[]) (by intro c hc; simp at hc)
    (by intro j hj; simp at hj) i hi

/-- Every atom of the input is numbered. -/
theorem factIndex_contains (atoms : Array GroundAtom) {a : GroundAtom} (ha : a ∈ atoms) :
    (factIndex atoms).1.contains a = true := by
  rw [factIndex_fold]
  exact (fold_ok atoms.toList ({}, #[]) (by intro b hb; simp at hb)).2 a (by simpa using ha)

/-- Only atoms of the input are numbered. -/
private theorem fold_mem (l : List GroundAtom) :
    ∀ (st : Std.HashMap GroundAtom Nat × Array GroundAtom) (a : GroundAtom),
      (l.foldl numberStep st).1.contains a = true → st.1.contains a = true ∨ a ∈ l := by
  induction l with
  | nil => intro st a h; exact Or.inl h
  | cons x rest ih =>
      intro st a h
      rcases ih _ a h with h' | h'
      · unfold numberStep at h'
        by_cases hc : st.1.contains x
        · rw [if_pos hc] at h'
          exact Or.inl h'
        · rw [if_neg (by simp [hc])] at h'
          have : (st.1.insert x st.2.size).contains a = true := h'
          rw [Std.HashMap.contains_insert] at this
          rcases Bool.or_eq_true_iff.mp this with hxa | hst
          · exact Or.inr (by simp [(beq_iff_eq.mp hxa).symm])
          · exact Or.inl hst
      · exact Or.inr (by simp [h'])

theorem factIndex_mem (atoms : Array GroundAtom) {a : GroundAtom}
    (h : (factIndex atoms).1.contains a = true) : a ∈ atoms := by
  rw [factIndex_fold] at h
  rcases fold_mem atoms.toList ({}, #[]) a h with h' | h'
  · simp at h'
  · simpa using h'

/-- Injectivity, stated of the atoms the numbering has seen. -/
theorem factIndex_injective' (atoms : Array GroundAtom) {a b : GroundAtom}
    (ha : (factIndex atoms).1.contains a = true) (hb : (factIndex atoms).1.contains b = true)
    (h : (factIndex atoms).1.getD a 0 = (factIndex atoms).1.getD b 0) : a = b := by
  rw [factIndex_fold] at ha hb h
  exact fold_inj atoms.toList ({}, #[]) (by intro c hc; simp at hc)
    (by intro c e hc; simp at hc) a b ha hb h

/-- **Naming a numbered atom gives the atom back.** -/
theorem factIndex_name (atoms : Array GroundAtom) {a : GroundAtom} (ha : a ∈ atoms) :
    (factIndex atoms).2.getD ((factIndex atoms).1.getD a 0) default = a := by
  obtain ⟨hmem, hval⟩ := factIndex_rev atoms _ (factIndex_lt atoms a ha)
  exact factIndex_injective' atoms hmem (factIndex_contains atoms ha) hval


/-! ### Every fact the grounder emits is in range -/

/-- Building a state from a list of facts keeps its word count. -/
theorem State.ofFacts_wf (n : Nat) (facts : Array Fact) :
    State.WF n (State.ofFacts n facts) := by
  have key : ∀ (l : List Fact) (s : State), State.WF n s → State.WF n (l.foldl State.insert s) := by
    intro l
    induction l with
    | nil => intro s hs; exact hs
    | cons x rest ih => intro s hs; exact ih _ (hs.insert x)
  unfold State.ofFacts
  rw [← Array.foldl_toList]
  exact key _ _ ⟨by simp [State.empty]⟩

/-- Every atom of every operator reaches the atom list. -/
private theorem mem_fold_ops (l : List AtomOp) :
    ∀ (acc : Array GroundAtom) (a : GroundAtom),
      (a ∈ acc ∨ ∃ op ∈ l, a ∈ op.pre ∨ a ∈ op.add ∨ a ∈ op.del) →
      a ∈ l.foldl (fun acc op => acc ++ op.pre ++ op.add ++ op.del) acc := by
  induction l with
  | nil =>
      intro acc a h
      rcases h with h | ⟨op, hop, -⟩
      · exact h
      · simp at hop
  | cons x rest ih =>
      intro acc a h
      refine ih _ a ?_
      rcases h with h | ⟨op, hop, hin⟩
      · exact Or.inl (by simp [h])
      · rcases List.mem_cons.mp hop with rfl | hop'
        · refine Or.inl ?_
          rcases hin with h | h | h <;> simp [h]
        · exact Or.inr ⟨op, hop', hin⟩

theorem mem_allAtoms_of_op {ops : Array AtomOp} {goalAtoms : Array GroundAtom}
    {op : AtomOp} (hop : op ∈ ops) {a : GroundAtom}
    (ha : a ∈ op.pre ∨ a ∈ op.add ∨ a ∈ op.del) : a ∈ allAtoms ops goalAtoms := by
  unfold allAtoms
  refine Array.mem_append.mpr (Or.inl ?_)
  rw [← Array.foldl_toList]
  exact mem_fold_ops _ _ a (Or.inr ⟨op, by simpa using hop, ha⟩)

theorem mem_allAtoms_of_goal {ops : Array AtomOp} {goalAtoms : Array GroundAtom}
    {a : GroundAtom} (ha : a ∈ goalAtoms) : a ∈ allAtoms ops goalAtoms :=
  Array.mem_append.mpr (Or.inr ha)

/--
**Every fact the grounder emits is in range.**

The initial state has the right number of words, every goal fact is below
`numFacts`, and so is every fact of every operator.  This is what the heuristic
proofs assume and what `astar_optimal` needs of the initial state.
-/
theorem assemble_wf (ops : Array AtomOp) (goalAtoms : Array GroundAtom)
    (initAtoms : Array GroundAtom) (objects : Array TypedName) (domainName : Name)
    (hcost : ∀ op ∈ ops, 0 < op.cost) :
    Task.WF (assemble ops goalAtoms initAtoms objects domainName) := by
  refine ⟨State.ofFacts_wf _ _, ?_, ?_⟩
  · intro f hf
    obtain ⟨a, ha, rfl⟩ := Array.mem_map.mp hf
    exact factIndex_lt _ a (mem_allAtoms_of_goal ha)
  · intro op hop
    obtain ⟨o, ho, rfl⟩ := Array.mem_map.mp hop
    refine ⟨?_, ?_, ?_, hcost o ho⟩
    · intro f hf
      obtain ⟨a, ha, rfl⟩ := Array.mem_map.mp hf
      exact factIndex_lt _ a (mem_allAtoms_of_op ho (Or.inl ha))
    · intro f hf
      obtain ⟨a, ha, rfl⟩ := Array.mem_map.mp hf
      exact factIndex_lt _ a (mem_allAtoms_of_op ho (Or.inr (Or.inl ha)))
    · intro f hf
      obtain ⟨a, ha, rfl⟩ := Array.mem_map.mp hf
      exact factIndex_lt _ a (mem_allAtoms_of_op ho (Or.inr (Or.inr ha)))

/--
**The grounder produces a well-formed task.**

Every fact of every operator, every goal fact, and the initial state are all in
range, so the invariant that `astar_optimal` and all twenty-one heuristic proofs
assume of the initial state holds of the task the planner actually builds.

The only side condition is that the operators carry a positive cost, which the
parser guarantees — it emits `cost := 1` for every schema in this fragment — and
which is decidable of the grounded operators in any case.
-/
theorem ground_wf (d : Domain) (p : Problem) (relevance : Bool)
    (hcost : ∀ op ∈ groundedOps d p relevance, 0 < op.cost) :
    Task.WF (ground d p relevance) :=
  assemble_wf _ _ _ _ _ hcost

end Planner
