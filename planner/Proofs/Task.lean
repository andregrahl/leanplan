/-
The semantics of the grounded task in `Planner/Task.lean`.

This file turns the executable `Op.applicable`, `Op.apply` and `Task.isGoal` into
a `PlanningModel`: a transition relation, an action cost, and a goal predicate.
Everything above it — the heuristics, their consistency proofs, and the A*
correctness proof — speaks only about that model, never about bit sets.

The one technical hypothesis is well-formedness: a state has one bit per fact and
every fact an operator mentions is below `numFacts`.  Grounding produces such a
task and `Op.apply` preserves the property, so it never has to be re-established.
-/
import Proofs.State
import Planner.Task

namespace Planner

open Planner.State

/-! ### Well-formedness -/

/-- `s` has exactly the words needed for `n` facts. -/
structure State.WF (n : Nat) (s : State) : Prop where
  size : s.words.size = State.wordsFor n

theorem State.lt_words {n f : Nat} {s : State} (hs : State.WF n s) (hf : f < n) :
    f >>> 6 < s.words.size := by
  rw [hs.size, State.wordsFor, shift_eq]
  omega

theorem State.WF.insert {n : Nat} {s : State} (hs : State.WF n s) (f : Fact) :
    State.WF n (s.insert f) := ⟨by simpa using hs.size⟩

theorem State.WF.erase {n : Nat} {s : State} (hs : State.WF n s) (f : Fact) :
    State.WF n (s.erase f) := ⟨by simpa using hs.size⟩

/-- Every fact an operator mentions is a fact of the task, and its cost is positive. -/
structure Op.WF (n : Nat) (op : Op) : Prop where
  pre : ∀ f ∈ op.pre, f < n
  add : ∀ f ∈ op.add, f < n
  del : ∀ f ∈ op.del, f < n
  cost : 0 < op.cost

/-- A task whose facts are numbered consistently. -/
structure Task.WF (t : Task) : Prop where
  init : State.WF t.numFacts t.init
  goal : ∀ f ∈ t.goal, f < t.numFacts
  ops : ∀ op ∈ t.ops, Op.WF t.numFacts op

/-! ### Reading a fact after an operator -/

private theorem test_foldl_erase {n : Nat} (l : List Fact) :
    ∀ (s : State) (f : Fact), State.WF n s → (∀ g ∈ l, g < n) →
      (l.foldl State.erase s).test f = (!l.contains f && s.test f) := by
  induction l with
  | nil => intro s f _ _; simp
  | cons g rest ih =>
      intro s f hs hl
      have hg : g >>> 6 < s.words.size := State.lt_words hs (hl g (by simp))
      have hrest : ∀ x ∈ rest, x < n := fun x hx => hl x (by simp [hx])
      rw [List.foldl_cons, ih (s.erase g) f (hs.erase g) hrest, State.test_erase s f g hg]
      by_cases h : f = g <;> simp [h]

private theorem test_foldl_insert {n : Nat} (l : List Fact) :
    ∀ (s : State) (f : Fact), State.WF n s → (∀ g ∈ l, g < n) →
      (l.foldl State.insert s).test f = (l.contains f || s.test f) := by
  induction l with
  | nil => intro s f _ _; simp
  | cons g rest ih =>
      intro s f hs hl
      have hg : g >>> 6 < s.words.size := State.lt_words hs (hl g (by simp))
      have hrest : ∀ x ∈ rest, x < n := fun x hx => hl x (by simp [hx])
      rw [List.foldl_cons, ih (s.insert g) f (hs.insert g) hrest, State.test_insert s f g hg]
      by_cases h : f = g <;> simp [h]

private theorem size_foldl (l : List Fact) (g : State → Fact → State)
    (hg : ∀ v f, (g v f).words.size = v.words.size) :
    ∀ s : State, (l.foldl g s).words.size = s.words.size := by
  induction l with
  | nil => intro s; simp
  | cons a rest ih => intro s; simp [List.foldl_cons, ih (g s a), hg]

/-- Applying an operator keeps a state well formed. -/
theorem Op.wf_apply {n : Nat} (op : Op) {s : State} (hs : State.WF n s) :
    State.WF n (op.apply s) := by
  refine ⟨?_⟩
  simp only [Op.apply, ← Array.foldl_toList]
  rw [size_foldl _ _ (fun v f => by simp), size_foldl _ _ (fun v f => by simp)]
  exact hs.size

/-- The successor state of an operator, fact by fact.  Adds win over deletes. -/
theorem Op.test_apply {n : Nat} {op : Op} {s : State} (hop : Op.WF n op)
    (hs : State.WF n s) (f : Fact) :
    (op.apply s).test f =
      if op.add.contains f then true
      else if op.del.contains f then false else s.test f := by
  have hdel : ∀ g ∈ op.del.toList, g < n := fun g hg => hop.del g (by simpa using hg)
  have hadd : ∀ g ∈ op.add.toList, g < n := fun g hg => hop.add g (by simpa using hg)
  have hafterDel : State.WF n (op.del.toList.foldl State.erase s) :=
    ⟨by rw [size_foldl _ _ (fun v f => by simp)]; exact hs.size⟩
  simp only [Op.apply, ← Array.foldl_toList]
  rw [test_foldl_insert _ _ _ hafterDel hadd, test_foldl_erase _ _ _ hs hdel]
  simp only [Array.contains_toList]
  by_cases hA : op.add.contains f <;> by_cases hD : op.del.contains f <;> simp_all

theorem Op.applicable_iff {op : Op} {s : State} :
    op.applicable s = true ↔ ∀ f ∈ op.pre, s.test f = true := by
  simp only [Op.applicable, State.holdsAll, ← Array.all_toList, List.all_eq_true]
  exact ⟨fun h f hf => h f (by simpa using hf), fun h f hf => h f (by simpa using hf)⟩

theorem Task.isGoal_iff {t : Task} {s : State} :
    t.isGoal s = true ↔ ∀ f ∈ t.goal, s.test f = true := by
  simp only [Task.isGoal, State.holdsAll, ← Array.all_toList, List.all_eq_true]
  exact ⟨fun h f hf => h f (by simpa using hf), fun h f hf => h f (by simpa using hf)⟩

/-! ### The planning model -/

/-- A goal-directed transition system with natural action costs. -/
structure PlanningModel (S A : Type) where
  transition : S → A → S → Prop
  actionCost : A → Nat
  isGoal : S → Prop

/-- Executing a sequence of actions. -/
inductive Executes {S A : Type} (m : PlanningModel S A) : S → List A → S → Prop where
  | nil (s : S) : Executes m s [] s
  | cons {s mid final a rest} :
      m.transition s a mid → Executes m mid rest final → Executes m s (a :: rest) final

/-- The total cost of a plan. -/
def planCost {S A : Type} (m : PlanningModel S A) : List A → Nat
  | [] => 0
  | a :: rest => m.actionCost a + planCost m rest

theorem planCost_append {S A : Type} (m : PlanningModel S A) (p q : List A) :
    planCost m (p ++ q) = planCost m p + planCost m q := by
  induction p with
  | nil => simp [planCost]
  | cons a rest ih => simp [planCost, ih, Nat.add_assoc]

/-- Executing a plan and then one more action. -/
theorem executes_append {S A : Type} {m : PlanningModel S A} {s mid final : S}
    {p : List A} {a : A} (hp : Executes m s p mid) (ha : m.transition mid a final) :
    Executes m s (p ++ [a]) final := by
  induction hp with
  | nil s => exact Executes.cons ha (Executes.nil final)
  | @cons s mid' final' b rest hb _ ih => exact Executes.cons hb (ih ha)

/-- Actions of a grounded task are operator indices. -/
def Task.step (t : Task) (s : State) (i : Nat) (s' : State) : Prop :=
  ∃ h : i < t.ops.size, t.ops[i].applicable s = true ∧ s' = t.ops[i].apply s

/-- The cost of an operator index; out-of-range indices are never transitions. -/
def Task.actionCost (t : Task) (i : Nat) : Nat :=
  match t.ops[i]? with
  | some op => op.cost
  | none => 1

/-- The planning model the search explores. -/
def Task.model (t : Task) : PlanningModel State Nat where
  transition := t.step
  actionCost := t.actionCost
  isGoal := fun s => t.isGoal s = true

@[simp] theorem Task.model_transition (t : Task) : t.model.transition = t.step := rfl
@[simp] theorem Task.model_actionCost (t : Task) : t.model.actionCost = t.actionCost := rfl
@[simp] theorem Task.model_isGoal (t : Task) (s : State) :
    t.model.isGoal s ↔ t.isGoal s = true := Iff.rfl

/-- Every state reachable from a well-formed state is well formed. -/
theorem Task.wf_of_executes {t : Task} {s s' : State} {plan : List Nat}
    (hs : State.WF t.numFacts s) (hexec : Executes t.model s plan s') :
    State.WF t.numFacts s' := by
  induction hexec with
  | nil => exact hs
  | @cons s mid final a rest hstep _ ih =>
      obtain ⟨_, _, rfl⟩ := hstep
      exact ih (Op.wf_apply _ hs)

end Planner
