/-
Grounding is faithful: the numbering layer.

`Grounding.assemble` is where ground atoms stop being atoms and become numbers.
Everything the planner does afterwards — the packed states, the operators, the
goal test — reads those numbers, so if the numbering lied, every theorem about
the search would be about a different problem.

This file proves it does not.  `Abstracts t s σ` says the atom-level state `σ`
reads the packed state `s` through the task's names: fact `f` stands for
`factNames[f]`, and an atom that got no number is one of the static atoms, true
in every reachable state.  Under that reading:

  * an operator is applicable exactly when its atom-level preconditions hold;
  * applying it lands on the atom-level successor;
  * the goal test agrees;
  * the initial state reads back as `:init`.

Plans therefore transfer with equal cost, which is `assemble_plan_sound`.

What is *not* proved here is the layer above: that the operators `groundedOps`
produces are exactly the well-typed schema instances of `Proofs/Semantics.lean`,
and that the relevance analysis drops only operators no goal-reaching plan could
use.  That is the remaining item in `PLAN.md`; this file is the half of it that
the fact numbering owns.
-/
import Proofs.Grounding
import Proofs.Semantics

namespace Planner

open Planner.Pddl

/-! ### Reading a built state -/

theorem State.test_empty (n f : Nat) : (State.empty n).test f = false := by
  simp only [State.test, State.empty, Array.getD_eq_getD_getElem?, bne_iff_ne, ne_eq,
    Decidable.not_not]
  by_cases h : f >>> 6 < (Array.replicate (State.wordsFor n) (0 : UInt64)).size
  · rw [Array.getElem?_eq_getElem h]
    simp
  · rw [Array.getElem?_eq_none (by omega)]
    simp

theorem State.test_ofFacts (n : Nat) (facts : Array Fact) (hfacts : ∀ g ∈ facts, g < n)
    (f : Fact) : (State.ofFacts n facts).test f = facts.contains f := by
  have key : ∀ (l : List Fact), (∀ g ∈ l, g < n) → ∀ s : State, State.WF n s →
      (l.foldl (fun s f => s.insert f) s).test f = (l.contains f || s.test f) := by
    intro l
    induction l with
    | nil => intro _ s _; simp
    | cons x rest ih =>
        intro hl s hs
        have hx : x >>> 6 < s.words.size := State.lt_words hs (hl x (by simp))
        rw [List.foldl_cons,
          ih (fun g hg => hl g (by simp [hg])) _ (hs.insert x),
          State.test_insert s f x hx]
        simp [Bool.or_left_comm, Bool.or_assoc]
  unfold State.ofFacts
  rw [← Array.foldl_toList, key facts.toList (by intro g hg; exact hfacts g (by simpa using hg))
    _ ⟨by simp [State.empty, State.wordsFor]⟩, State.test_empty]
  simp [Array.contains_iff_mem, List.contains_iff_mem]

/-! ### The atom-level task

The same operators, before their facts were numbered.  `applyA` deletes and then
adds, exactly as `Op.apply` and the lifted model do.
-/

/-- Applicability, read on atoms. -/
def AtomOp.applicableA (o : AtomOp) (σ : AtomState) : Prop := ∀ a ∈ o.pre, σ a = true

/-- The successor, read on atoms. -/
def AtomOp.applyA (o : AtomOp) (σ : AtomState) : AtomState := fun a =>
  if o.add.contains a then true else if o.del.contains a then false else σ a

/-- The transition system the grounder's operators describe, before numbering. -/
def atomModel (ops : Array AtomOp) (goalAtoms : Array GroundAtom) :
    PlanningModel AtomState Nat where
  transition σ k σ' := ∃ h : k < ops.size, ops[k].applicableA σ ∧ σ' = ops[k].applyA σ
  actionCost k := match ops[k]? with
    | some o => o.cost
    | none => 1
  isGoal σ := ∀ a ∈ goalAtoms, σ a = true

/-- Numbering one operator, exactly as `assemble` does. -/
def numberOp (index : Std.HashMap GroundAtom Nat) (o : AtomOp) : Op :=
  { name := o.name
    pre := o.pre.map fun a => index.getD a 0
    add := o.add.map fun a => index.getD a 0
    del := o.del.map fun a => index.getD a 0
    cost := o.cost }

/-! ### Reading a packed state as a set of atoms -/

/--
`σ` reads the packed state `s` through the task's names: fact `f` stands for
`factNames[f]`, and an atom with no number is one of the static atoms, true in
every reachable state.
-/
structure Abstracts (t : Task) (s : State) (σ : AtomState) : Prop where
  numbered : ∀ f, f < t.numFacts → σ (t.factNames.getD f default) = s.test f
  unnumbered : ∀ a, (∀ f, f < t.numFacts → t.factNames.getD f default ≠ a) →
      σ a = t.staticAtoms.contains a

section Assemble

variable (ops : Array AtomOp) (goalAtoms initAtoms : Array GroundAtom)
  (objects : Array TypedName) (dname : Name)

/-- The atoms the numbering sees. -/
private abbrev atomsOf : Array GroundAtom := allAtoms ops goalAtoms

/-- The number an atom receives. -/
private abbrev ixOf (a : GroundAtom) : Nat :=
  (factIndex (atomsOf ops goalAtoms)).1.getD a 0

theorem assemble_numFacts :
    (assemble ops goalAtoms initAtoms objects dname).numFacts
      = (factIndex (atomsOf ops goalAtoms)).2.size := rfl

theorem assemble_factNames :
    (assemble ops goalAtoms initAtoms objects dname).factNames
      = (factIndex (atomsOf ops goalAtoms)).2 := rfl

theorem assemble_ops :
    (assemble ops goalAtoms initAtoms objects dname).ops
      = ops.map (numberOp (factIndex (atomsOf ops goalAtoms)).1) := rfl

theorem assemble_goal :
    (assemble ops goalAtoms initAtoms objects dname).goal
      = goalAtoms.map (ixOf ops goalAtoms) := rfl

theorem assemble_init_eq :
    (assemble ops goalAtoms initAtoms objects dname).init
      = State.ofFacts (assemble ops goalAtoms initAtoms objects dname).numFacts
          (initAtoms.filterMap (factIndex (atomsOf ops goalAtoms)).1.get?) := rfl

theorem assemble_staticAtoms :
    (assemble ops goalAtoms initAtoms objects dname).staticAtoms
      = initAtoms.filter (!(factIndex (atomsOf ops goalAtoms)).1.contains ·) := rfl

/-! #### The numbering is a bijection between facts and the atoms it saw -/

theorem name_mem (f : Nat)
    (hf : f < (assemble ops goalAtoms initAtoms objects dname).numFacts) :
    (assemble ops goalAtoms initAtoms objects dname).factNames.getD f default
      ∈ atomsOf ops goalAtoms := by
  rw [assemble_factNames]
  exact factIndex_mem _ (factIndex_rev _ f (by rw [← assemble_numFacts]; exact hf)).1

theorem name_ix {a : GroundAtom} (ha : a ∈ atomsOf ops goalAtoms) :
    (assemble ops goalAtoms initAtoms objects dname).factNames.getD
      (ixOf ops goalAtoms a) default = a := by
  rw [assemble_factNames]
  exact factIndex_name _ ha

theorem ix_name (f : Nat)
    (hf : f < (assemble ops goalAtoms initAtoms objects dname).numFacts) :
    ixOf ops goalAtoms
        ((assemble ops goalAtoms initAtoms objects dname).factNames.getD f default) = f := by
  rw [assemble_factNames]
  exact (factIndex_rev _ f (by rw [← assemble_numFacts]; exact hf)).2

theorem ix_lt {a : GroundAtom} (ha : a ∈ atomsOf ops goalAtoms) :
    ixOf ops goalAtoms a < (assemble ops goalAtoms initAtoms objects dname).numFacts :=
  factIndex_lt _ a ha

/-- An atom the numbering never saw is not one of the names. -/
theorem not_mem_of_unnamed {a : GroundAtom}
    (h : ∀ f, f < (assemble ops goalAtoms initAtoms objects dname).numFacts →
      (assemble ops goalAtoms initAtoms objects dname).factNames.getD f default ≠ a) :
    a ∉ atomsOf ops goalAtoms := by
  intro ha
  exact h _ (ix_lt ops goalAtoms initAtoms objects dname ha)
    (name_ix ops goalAtoms initAtoms objects dname ha)

/-- Under the abstraction, an atom's truth is the truth of its fact. -/
theorem abstract_test {s : State} {σ : AtomState}
    (habs : Abstracts (assemble ops goalAtoms initAtoms objects dname) s σ)
    {a : GroundAtom} (ha : a ∈ atomsOf ops goalAtoms) :
    σ a = s.test (ixOf ops goalAtoms a) := by
  have := habs.numbered (ixOf ops goalAtoms a) (ix_lt ops goalAtoms initAtoms objects dname ha)
  rwa [name_ix ops goalAtoms initAtoms objects dname ha] at this

/-- Numbering a list of atoms does not change what it contains. -/
theorem mapped_contains (l : Array GroundAtom) (hl : ∀ b ∈ l, b ∈ atomsOf ops goalAtoms)
    {a : GroundAtom} (ha : a ∈ atomsOf ops goalAtoms) :
    (l.map (ixOf ops goalAtoms)).contains (ixOf ops goalAtoms a) = l.contains a := by
  refine Bool.eq_iff_iff.mpr ?_
  rw [Array.contains_iff_mem, Array.contains_iff_mem]
  simp only [Array.mem_map]
  constructor
  · rintro ⟨b, hb, hbe⟩
    rw [← factIndex_injective _ (hl b hb) ha hbe]
    exact hb
  · intro h
    exact ⟨a, h, rfl⟩

/-! #### One operator

Applicability and the successor agree with what the atoms say, which is the step
every plan-transfer argument repeats.
-/

theorem op_atoms_mem {o : AtomOp} (ho : o ∈ ops) :
    (∀ a ∈ o.pre, a ∈ atomsOf ops goalAtoms) ∧ (∀ a ∈ o.add, a ∈ atomsOf ops goalAtoms) ∧
      (∀ a ∈ o.del, a ∈ atomsOf ops goalAtoms) :=
  ⟨fun a ha => mem_allAtoms_of_op ho (Or.inl ha),
   fun a ha => mem_allAtoms_of_op ho (Or.inr (Or.inl ha)),
   fun a ha => mem_allAtoms_of_op ho (Or.inr (Or.inr ha))⟩

theorem numberOp_wf {o : AtomOp} (ho : o ∈ ops) (hc : 0 < o.cost) :
    Op.WF (assemble ops goalAtoms initAtoms objects dname).numFacts
      (numberOp (factIndex (atomsOf ops goalAtoms)).1 o) := by
  obtain ⟨hpre, hadd, hdel⟩ := op_atoms_mem ops goalAtoms ho
  refine ⟨?_, ?_, ?_, hc⟩ <;> intro f hf <;>
    obtain ⟨a, ha, rfl⟩ := Array.mem_map.mp hf
  · exact ix_lt ops goalAtoms initAtoms objects dname (hpre a ha)
  · exact ix_lt ops goalAtoms initAtoms objects dname (hadd a ha)
  · exact ix_lt ops goalAtoms initAtoms objects dname (hdel a ha)

theorem assemble_applicable {o : AtomOp} (ho : o ∈ ops) {s : State} {σ : AtomState}
    (habs : Abstracts (assemble ops goalAtoms initAtoms objects dname) s σ) :
    (numberOp (factIndex (atomsOf ops goalAtoms)).1 o).applicable s = true ↔ o.applicableA σ := by
  obtain ⟨hpre, -, -⟩ := op_atoms_mem ops goalAtoms ho
  rw [Op.applicable_iff]
  constructor
  · intro h a ha
    rw [abstract_test ops goalAtoms initAtoms objects dname habs (hpre a ha)]
    exact h _ (Array.mem_map.mpr ⟨a, ha, rfl⟩)
  · intro h f hf
    obtain ⟨a, ha, rfl⟩ := Array.mem_map.mp hf
    rw [← abstract_test ops goalAtoms initAtoms objects dname habs (hpre a ha)]
    exact h a ha

theorem assemble_apply {o : AtomOp} (ho : o ∈ ops) (hc : 0 < o.cost) {s : State} {σ : AtomState}
    (hs : State.WF (assemble ops goalAtoms initAtoms objects dname).numFacts s)
    (habs : Abstracts (assemble ops goalAtoms initAtoms objects dname) s σ) :
    Abstracts (assemble ops goalAtoms initAtoms objects dname)
      ((numberOp (factIndex (atomsOf ops goalAtoms)).1 o).apply s) (o.applyA σ) := by
  obtain ⟨hpre, hadd, hdel⟩ := op_atoms_mem ops goalAtoms ho
  have hop := numberOp_wf ops goalAtoms initAtoms objects dname ho hc
  refine ⟨?_, ?_⟩
  · intro f hf
    have hmem := name_mem ops goalAtoms initAtoms objects dname f hf
    have hix := ix_name ops goalAtoms initAtoms objects dname f hf
    set a := (assemble ops goalAtoms initAtoms objects dname).factNames.getD f default with ha
    rw [Op.test_apply hop hs f, ← hix]
    show (if o.add.contains a then true else if o.del.contains a then false else σ a) = _
    rw [show (numberOp (factIndex (atomsOf ops goalAtoms)).1 o).add
        = o.add.map (ixOf ops goalAtoms) from rfl,
      show (numberOp (factIndex (atomsOf ops goalAtoms)).1 o).del
        = o.del.map (ixOf ops goalAtoms) from rfl,
      mapped_contains ops goalAtoms o.add hadd hmem,
      mapped_contains ops goalAtoms o.del hdel hmem,
      abstract_test ops goalAtoms initAtoms objects dname habs hmem]
  · intro a hun
    have hnot := not_mem_of_unnamed ops goalAtoms initAtoms objects dname hun
    have hadd' : o.add.contains a = false := by
      by_contra hcon
      simp only [Bool.not_eq_false] at hcon
      exact hnot (hadd a (Array.contains_iff_mem.mp hcon))
    have hdel' : o.del.contains a = false := by
      by_contra hcon
      simp only [Bool.not_eq_false] at hcon
      exact hnot (hdel a (Array.contains_iff_mem.mp hcon))
    show (if o.add.contains a then true else if o.del.contains a then false else σ a) = _
    rw [hadd', hdel']
    simp only [Bool.false_eq_true, if_false]
    exact habs.unnumbered a hun

/-! #### The goal and the initial state -/

theorem assemble_isGoal {s : State} {σ : AtomState}
    (habs : Abstracts (assemble ops goalAtoms initAtoms objects dname) s σ) :
    (assemble ops goalAtoms initAtoms objects dname).isGoal s = true
      ↔ ∀ a ∈ goalAtoms, σ a = true := by
  rw [Task.isGoal_iff]
  constructor
  · intro h a ha
    rw [abstract_test ops goalAtoms initAtoms objects dname habs (mem_allAtoms_of_goal ha)]
    exact h _ (Array.mem_map.mpr ⟨a, ha, rfl⟩)
  · intro h f hf
    rw [assemble_goal] at hf
    obtain ⟨a, ha, rfl⟩ := Array.mem_map.mp hf
    rw [← abstract_test ops goalAtoms initAtoms objects dname habs (mem_allAtoms_of_goal ha)]
    exact h a ha

theorem assemble_init :
    Abstracts (assemble ops goalAtoms initAtoms objects dname)
      (assemble ops goalAtoms initAtoms objects dname).init (fun a => initAtoms.contains a) := by
  have hfacts : ∀ g ∈ initAtoms.filterMap (factIndex (atomsOf ops goalAtoms)).1.get?,
      g < (assemble ops goalAtoms initAtoms objects dname).numFacts := by
    intro g hg
    obtain ⟨a, ha, hga⟩ := Array.mem_filterMap.mp hg
    have hc : (factIndex (atomsOf ops goalAtoms)).1.contains a = true := by
      rw [Std.HashMap.contains_eq_isSome_getElem?]
      show ((factIndex (atomsOf ops goalAtoms)).1.get? a).isSome = true
      rw [hga]
      rfl
    have hval : ixOf ops goalAtoms a = g := by
      show ((factIndex (atomsOf ops goalAtoms)).1.getD a 0) = g
      rw [Std.HashMap.getD_eq_getD_getElem?]
      show ((factIndex (atomsOf ops goalAtoms)).1.get? a).getD 0 = g
      rw [hga]
      rfl
    rw [← hval]
    exact ix_lt ops goalAtoms initAtoms objects dname (factIndex_mem _ hc)
  refine ⟨?_, ?_⟩
  · intro f hf
    have hmem := name_mem ops goalAtoms initAtoms objects dname f hf
    have hix := ix_name ops goalAtoms initAtoms objects dname f hf
    set a := (assemble ops goalAtoms initAtoms objects dname).factNames.getD f default with ha
    rw [assemble_init_eq, State.test_ofFacts _ _ hfacts f]
    show initAtoms.contains a = _
    refine Bool.eq_iff_iff.mpr ?_
    rw [Array.contains_iff_mem, Array.contains_iff_mem]
    constructor
    · intro hin
      refine Array.mem_filterMap.mpr ⟨a, hin, ?_⟩
      show (factIndex (atomsOf ops goalAtoms)).1.get? a = some f
      have hc : (factIndex (atomsOf ops goalAtoms)).1.contains a = true :=
        factIndex_contains _ hmem
      have hgetD : ((factIndex (atomsOf ops goalAtoms)).1.get? a).getD 0 = f := by
        show ((factIndex (atomsOf ops goalAtoms)).1[a]?).getD 0 = f
        rw [← Std.HashMap.getD_eq_getD_getElem?]
        exact hix
      cases hget : (factIndex (atomsOf ops goalAtoms)).1.get? a with
      | none =>
          rw [Std.HashMap.contains_eq_isSome_getElem?] at hc
          rw [show ((factIndex (atomsOf ops goalAtoms)).1[a]?) = none from hget] at hc
          simp at hc
      | some g =>
          simp only [hget, Option.getD_some] at hgetD
          rw [hgetD]
    · intro hin
      obtain ⟨b, hb, hgb⟩ := Array.mem_filterMap.mp hin
      have hcb : (factIndex (atomsOf ops goalAtoms)).1.contains b = true := by
        rw [Std.HashMap.contains_eq_isSome_getElem?]
        show ((factIndex (atomsOf ops goalAtoms)).1.get? b).isSome = true
        rw [hgb]
        rfl
      have hvalb : ixOf ops goalAtoms b = f := by
        show ((factIndex (atomsOf ops goalAtoms)).1.getD b 0) = f
        rw [Std.HashMap.getD_eq_getD_getElem?]
        show ((factIndex (atomsOf ops goalAtoms)).1.get? b).getD 0 = f
        rw [hgb]
        rfl
      have : b = a := by
        rw [ha, ← hvalb, name_ix ops goalAtoms initAtoms objects dname (factIndex_mem _ hcb)]
      rw [← this]
      exact hb
  · intro a hun
    have hnot := not_mem_of_unnamed ops goalAtoms initAtoms objects dname hun
    rw [assemble_staticAtoms]
    refine Bool.eq_iff_iff.mpr ?_
    rw [Array.contains_iff_mem, Array.contains_iff_mem, Array.mem_filter]
    constructor
    · intro hin
      refine ⟨hin, ?_⟩
      simp only [Bool.not_eq_true']
      by_contra hcon
      simp only [Bool.not_eq_false] at hcon
      exact hnot (factIndex_mem _ hcon)
    · exact fun h => h.1

/-! #### Plans transfer

Every step of a plan of the numbered task is a step of the atom-level task, at
the same cost, so the whole plan transfers.  This is the half of grounding
correctness the fact numbering owns.
-/

theorem assemble_actionCost (k : Nat) :
    (assemble ops goalAtoms initAtoms objects dname).actionCost k
      = (atomModel ops goalAtoms).actionCost k := by
  show (match (assemble ops goalAtoms initAtoms objects dname).ops[k]? with
      | some op => op.cost | none => 1)
    = (match ops[k]? with | some o => o.cost | none => 1)
  rw [assemble_ops, Array.getElem?_map]
  cases ops[k]? <;> rfl

theorem assemble_planCost (plan : List Nat) :
    planCost (assemble ops goalAtoms initAtoms objects dname).model plan
      = planCost (atomModel ops goalAtoms) plan := by
  induction plan with
  | nil => rfl
  | cons k rest ih =>
      show (assemble ops goalAtoms initAtoms objects dname).actionCost k + _
        = (atomModel ops goalAtoms).actionCost k + _
      rw [assemble_actionCost, ih]

/-- **A plan of the numbered task is a plan of the atom-level task.** -/
theorem assemble_plan_sound (hcost : ∀ o ∈ ops, 0 < o.cost) {plan : List Nat} :
    ∀ {s s' : State} {σ : AtomState},
      State.WF (assemble ops goalAtoms initAtoms objects dname).numFacts s →
      Abstracts (assemble ops goalAtoms initAtoms objects dname) s σ →
      Executes (assemble ops goalAtoms initAtoms objects dname).model s plan s' →
      ∃ σ', Abstracts (assemble ops goalAtoms initAtoms objects dname) s' σ' ∧
        Executes (atomModel ops goalAtoms) σ plan σ' := by
  induction plan with
  | nil =>
      intro s s' σ _ habs hexec
      cases hexec
      exact ⟨σ, habs, Executes.nil σ⟩
  | cons k rest ih =>
      intro s s' σ hs habs hexec
      cases hexec with
      | @cons _ mid _ _ _ hstep hrest =>
          obtain ⟨hk, happ, hmid⟩ := hstep
          rw [assemble_ops] at hk
          simp only [Array.size_map] at hk
          have hmem : ops[k] ∈ ops := Array.getElem_mem hk
          have hop : (assemble ops goalAtoms initAtoms objects dname).ops[k]'(by
              rw [assemble_ops]; simpa using hk)
              = numberOp (factIndex (atomsOf ops goalAtoms)).1 ops[k] := by
            simp [assemble_ops]
          rw [hop] at happ hmid
          have happ' : (ops[k]).applicableA σ :=
            (assemble_applicable ops goalAtoms initAtoms objects dname hmem habs).mp happ
          have habs' : Abstracts (assemble ops goalAtoms initAtoms objects dname) mid
              ((ops[k]).applyA σ) := by
            rw [hmid]
            exact assemble_apply ops goalAtoms initAtoms objects dname hmem
              (hcost _ hmem) hs habs
          have hwf : State.WF (assemble ops goalAtoms initAtoms objects dname).numFacts mid := by
            rw [hmid]
            exact Op.wf_apply _ hs
          obtain ⟨σ', habsF, hexecF⟩ := ih hwf habs' hrest
          exact ⟨σ', habsF, Executes.cons ⟨hk, happ', rfl⟩ hexecF⟩

/--
**What the planner finds is a plan of the grounder's operators, atom for atom.**

A plan the search returns for the numbered task executes from `:init`, read as a
set of atoms, to a state satisfying every goal atom, and costs the same.
-/
theorem assemble_sound (hcost : ∀ o ∈ ops, 0 < o.cost) {plan : List Nat} {s' : State}
    (hexec : Executes (assemble ops goalAtoms initAtoms objects dname).model
      (assemble ops goalAtoms initAtoms objects dname).init plan s')
    (hgoal : (assemble ops goalAtoms initAtoms objects dname).isGoal s' = true) :
    ∃ σ', Executes (atomModel ops goalAtoms) (fun a => initAtoms.contains a) plan σ' ∧
      (∀ a ∈ goalAtoms, σ' a = true) ∧
      planCost (atomModel ops goalAtoms) plan
        = planCost (assemble ops goalAtoms initAtoms objects dname).model plan := by
  obtain ⟨σ', habs', hexec'⟩ := assemble_plan_sound ops goalAtoms initAtoms objects dname hcost
    (State.ofFacts_wf _ _) (assemble_init ops goalAtoms initAtoms objects dname) hexec
  exact ⟨σ', hexec',
    (assemble_isGoal ops goalAtoms initAtoms objects dname habs').mp hgoal,
    (assemble_planCost ops goalAtoms initAtoms objects dname plan).symm⟩

end Assemble

/-! ### The grounder as a whole

`ground` is `assemble` applied to the operators `groundedOps` produces, so the
numbering half of grounding correctness holds of it verbatim.  What stands
between this and the lifted model of `Proofs/Semantics.lean` is the operator
half: that `groundedOps` produces exactly the well-typed schema instances that
can occur on a goal-reaching plan.
-/

/-- **Plans of the grounded task are plans of the grounder's operators.** -/
theorem ground_plan_sound (d : Domain) (p : Problem) (relevance : Bool)
    (hcost : ∀ o ∈ groundedOps d p relevance, 0 < o.cost)
    {plan : List Nat} {s' : State}
    (hexec : Executes (ground d p relevance).model (ground d p relevance).init plan s')
    (hgoal : (ground d p relevance).isGoal s' = true) :
    ∃ σ', Executes (atomModel (groundedOps d p relevance) p.goal.toArray)
        (fun a => p.init.toArray.contains a) plan σ' ∧
      (∀ a ∈ p.goal.toArray, σ' a = true) ∧
      planCost (atomModel (groundedOps d p relevance) p.goal.toArray) plan
        = planCost (ground d p relevance).model plan :=
  assemble_sound _ _ _ _ _ hcost hexec hgoal

end Planner
