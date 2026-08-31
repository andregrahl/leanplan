/-
What a node array means.

`NodesOK` is the invariant the search maintains: node 0 is the root, every other
node's parent has a smaller index, and every non-root node is one real transition
away from its parent with `g` one action cost larger.  From that alone, `planTo`
is shown to produce a genuine plan from the initial state to the node's state,
whose cost is the node's `g`.  That is the whole content of A*'s soundness; the
search file adds only the goal test.

The induction is strong induction on the node index, following the parent chain
downwards, which is exactly why `planTo` is written to recurse before appending.
-/
import Proofs.Task
import Planner.Search.Node

namespace Planner

/-- Every node of the array is reached from its parent by one real transition. -/
structure NodesOK (t : Task) (nodes : Array Node) : Prop where
  /-- The array is never empty: it starts with the root. -/
  nonempty : 0 < nodes.size
  /-- Node 0 is the initial state at cost zero, with no incoming operator. -/
  root : (nodes.getD 0 default).state = t.init ∧ (nodes.getD 0 default).g = 0 ∧ (nodes.getD 0 default).op = none
  /-- Parents come earlier, so the chain from any node is finite. -/
  parentLt : ∀ i, i < nodes.size → 0 < i → (nodes.getD i default).parent < i
  /-- Every non-root node records the operator that produced it. -/
  step : ∀ i, i < nodes.size → 0 < i →
    ∃ op, (nodes.getD i default).op = some op ∧
      t.step (nodes.getD (nodes.getD i default).parent default).state op (nodes.getD i default).state ∧
      (nodes.getD i default).g = (nodes.getD (nodes.getD i default).parent default).g + t.actionCost op

namespace NodesOK

variable {t : Task} {nodes : Array Node}

/-! ### Cost along a parent chain

Costs strictly increase from a node to its children, provided operators cost
something.  This is what the fuel argument needs: a state repeating on a parent
chain would have to be recorded at a larger cost than it already had, which
`record` forbids, so chains have distinct states and are no longer than the state
space.
-/

/-- A node costs strictly more than its parent. -/
theorem parent_g_lt (ok : NodesOK t nodes) (hcost : ∀ op ∈ t.ops, 0 < op.cost)
    (i : Nat) (hi : i < nodes.size) (hpos : 0 < i) :
    (nodes.getD (nodes.getD i default).parent default).g < (nodes.getD i default).g := by
  obtain ⟨op, -, hstep, hg⟩ := ok.step i hi hpos
  obtain ⟨hlt, -, -⟩ := hstep
  have hpos' : 0 < t.actionCost op := by
    have : t.actionCost op = t.ops[op].cost := by
      simp [Task.actionCost, Array.getElem?_eq_getElem hlt]
    rw [this]
    exact hcost _ (Array.getElem_mem hlt)
  omega

/-- `j` lies on the parent chain leading to `i`. -/
inductive Ancestor (nodes : Array Node) : Nat → Nat → Prop
  | self (i : Nat) : Ancestor nodes i i
  | step {i j : Nat} (hpos : 0 < i)
      (h : Ancestor nodes (nodes.getD i default).parent j) : Ancestor nodes i j

theorem getD_push_lt (a : Array Node) (x : Node) {j : Nat} (h : j < a.size) :
    (a.push x).getD j default = a.getD j default := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem h, Array.getElem?_eq_getElem (by simp; omega),
    Array.getElem_push_lt]

/-- Ancestors sit earlier in the array. -/
theorem ancestor_le (ok : NodesOK t nodes) :
    ∀ (i : Nat), i < nodes.size → ∀ (j : Nat), Ancestor nodes i j → j ≤ i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
      intro hi j ha
      cases ha with
      | self => exact Nat.le_refl _
      | step hpos h =>
          have hp := ok.parentLt i hi hpos
          have := ih _ hp (Nat.lt_trans hp hi) j h
          omega

/-- Costs never rise as the chain is followed downwards. -/
theorem ancestor_g_le (ok : NodesOK t nodes) (hcost : ∀ op ∈ t.ops, 0 < op.cost) :
    ∀ (i : Nat), i < nodes.size → ∀ (j : Nat), Ancestor nodes i j →
      (nodes.getD j default).g ≤ (nodes.getD i default).g := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
      intro hi j ha
      cases ha with
      | self => exact Nat.le_refl _
      | step hpos h =>
          have hp := ok.parentLt i hi hpos
          have hrec := ih _ hp (Nat.lt_trans hp hi) j h
          have := parent_g_lt ok hcost i hi hpos
          omega

/-- Follow the parent link `k` times, stopping at the root. -/
def climb (nodes : Array Node) : Nat → Nat → Nat
  | 0, i => i
  | k + 1, i => if i = 0 then 0 else climb nodes k (nodes.getD i default).parent

theorem climb_ancestor (nodes : Array Node) :
    ∀ (k i : Nat), Ancestor nodes i (climb nodes k i) := by
  intro k
  induction k with
  | zero => intro i; exact Ancestor.self i
  | succ k ih =>
      intro i
      by_cases h0 : i = 0
      · subst h0
        simp only [climb, if_pos rfl]
        exact Ancestor.self 0
      · simp only [climb, if_neg h0]
        exact Ancestor.step (Nat.pos_of_ne_zero h0) (ih _)

theorem climb_lt (ok : NodesOK t nodes) :
    ∀ (k i : Nat), i < nodes.size → climb nodes k i < nodes.size := by
  intro k
  induction k with
  | zero => intro i hi; exact hi
  | succ k ih =>
      intro i hi
      by_cases h0 : i = 0
      · subst h0
        simp only [climb, if_pos rfl]
        exact ok.nonempty
      · simp only [climb, if_neg h0]
        exact ih _ (Nat.lt_trans (ok.parentLt i hi (Nat.pos_of_ne_zero h0)) hi)

/-- Climbing composes. -/
theorem climb_add (nodes : Array Node) :
    ∀ (a b i : Nat), climb nodes (a + b) i = climb nodes b (climb nodes a i) := by
  intro a
  induction a with
  | zero => intro b i; simp [climb]
  | succ a ih =>
      intro b i
      by_cases h0 : i = 0
      · subst h0
        have hz : ∀ k, climb nodes k 0 = 0 := by
          intro k
          induction k with
          | zero => rfl
          | succ k ihk => simp [climb, ihk]
        simp [climb, hz]
      · show climb nodes (a + 1 + b) i = climb nodes b (climb nodes (a + 1) i)
        rw [show a + 1 + b = (a + b) + 1 by omega]
        simp only [climb, if_neg h0]
        exact ih b _

/-- With unit costs, climbing `k` links lowers the cost by exactly `k`. -/
theorem climb_g (ok : NodesOK t nodes) (hunit : ∀ op ∈ t.ops, op.cost = 1) :
    ∀ (k i : Nat), i < nodes.size → k ≤ (nodes.getD i default).g →
      (nodes.getD (climb nodes k i) default).g = (nodes.getD i default).g - k := by
  intro k
  induction k with
  | zero => intro i _ _; simp [climb]
  | succ k ih =>
      intro i hi hk
      have h0 : i ≠ 0 := by
        rintro rfl
        rw [ok.root.2.1] at hk
        omega
      have hpos : 0 < i := Nat.pos_of_ne_zero h0
      obtain ⟨op, -, hstep, hg⟩ := ok.step i hi hpos
      obtain ⟨hlt, -, -⟩ := hstep
      have hcost1 : t.actionCost op = 1 := by
        have : t.actionCost op = t.ops[op].cost := by
          simp [Task.actionCost, Array.getElem?_eq_getElem hlt]
        rw [this]
        exact hunit _ (Array.getElem_mem hlt)
      have hp := ok.parentLt i hi hpos
      have hpi : (nodes.getD i default).parent < nodes.size := Nat.lt_trans hp hi
      have hgp : (nodes.getD (nodes.getD i default).parent default).g
          = (nodes.getD i default).g - 1 := by omega
      simp only [climb, if_neg h0]
      rw [ih _ hpi (by omega), hgp]
      omega

/--
Every node holds a well-formed state.

Node zero is the initial state, and every other is one operator applied to its
parent's, so this follows from the task being well formed.  The pigeonhole step of
the fuel argument needs it: the injection it builds lands in the *well-formed*
states, which are the ones `Proofs/Finite.lean` counts.
-/
theorem states_wf (hwf : Task.WF t) (ok : NodesOK t nodes) :
    ∀ (i : Nat), i < nodes.size → State.WF t.numFacts (nodes.getD i default).state := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
      intro hi
      by_cases hpos : 0 < i
      · obtain ⟨op, -, hstep, -⟩ := ok.step i hi hpos
        obtain ⟨hlt, happ, hval⟩ := hstep
        have hp := ok.parentLt i hi hpos
        have hpar := ih _ hp (Nat.lt_trans hp hi)
        rw [hval]
        exact Op.wf_apply _ hpar
      · have hi0 : i = 0 := by omega
        subst hi0
        rw [ok.root.1]
        exact hwf.init

/-- Appending a node does not change the chains of the nodes already there. -/
theorem ancestor_push (ok : NodesOK t nodes) (x : Node) :
    ∀ (i : Nat), i < nodes.size → ∀ (j : Nat),
      Ancestor (nodes.push x) i j → Ancestor nodes i j := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
      intro hi j ha
      cases ha with
      | self => exact Ancestor.self _
      | step hpos h =>
          rw [getD_push_lt nodes x hi] at h
          have hp := ok.parentLt i hi hpos
          exact Ancestor.step hpos (ih _ hp (Nat.lt_trans hp hi) j h)

theorem getD_push_size (a : Array Node) (x : Node) :
    (a.push x).getD a.size default = x := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_push_size]
  rfl

/--
No state repeats along a parent chain.

This is what bounds the search's costs.  A node is only ever created when its cost
undercuts what `best` holds for its state, and `best` is already at or below the
cost of any node with that state — so a repeat would need the new node to cost
both more than its ancestor and less than it.
-/
def NoRepeat (nodes : Array Node) : Prop :=
  ∀ (i : Nat), i < nodes.size → ∀ (j : Nat), Ancestor nodes i j → j ≠ i →
    (nodes.getD j default).state ≠ (nodes.getD i default).state

/-- Appending a node whose state is new to its parent's chain keeps chains repeat-free. -/
theorem noRepeat_push (ok : NodesOK t nodes) (h : NoRepeat nodes) (x : Node)
    (hparent : x.parent < nodes.size)
    (hfresh : ∀ j, Ancestor nodes x.parent j → (nodes.getD j default).state ≠ x.state) :
    NoRepeat (nodes.push x) := by
  intro i hi j ha hne
  simp only [Array.size_push] at hi
  by_cases hlt : i < nodes.size
  · rw [getD_push_lt nodes x hlt]
    have ha' : Ancestor nodes i j := ancestor_push ok x i hlt j ha
    have hj : j ≤ i := ancestor_le ok i hlt j ha'
    rw [getD_push_lt nodes x (Nat.lt_of_le_of_lt hj hlt)]
    exact h i hlt j ha' hne
  · have hieq : i = nodes.size := by omega
    subst hieq
    rw [getD_push_size]
    cases ha with
    | self => exact absurd rfl hne
    | step hpos hchain =>
        rw [getD_push_size] at hchain
        have hchain' : Ancestor nodes x.parent j := ancestor_push ok x x.parent hparent j hchain
        have hj : j ≤ x.parent := ancestor_le ok x.parent hparent j hchain'
        rw [getD_push_lt nodes x (Nat.lt_of_le_of_lt hj hparent)]
        exact hfresh j hchain'

/--
The plan `planTo` builds really executes from the initial state to the node's
state, and its cost is the node's `g`.  Strong induction on the node index: the
parent is smaller, so its plan is already known to be good, and one transition
extends it.
-/
theorem planTo_valid (ok : NodesOK t nodes) :
    ∀ i, i < nodes.size → ∀ fuel, i < fuel →
      Executes t.model t.init (planTo nodes fuel i).toList (nodes.getD i default).state ∧
      planCost t.model (planTo nodes fuel i).toList = (nodes.getD i default).g := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi fuel hfuel
    match fuel with
    | 0 => omega
    | fuel + 1 =>
      by_cases hzero : i = 0
      · subst hzero
        obtain ⟨hstate, hg, hop⟩ := ok.root
        simp only [Array.getD_eq_getD_getElem?] at hstate hg hop
        simp only [planTo, Array.getD_eq_getD_getElem?, hop]
        refine ⟨?_, ?_⟩
        · simpa [hstate] using Executes.nil (m := t.model) t.init
        · simp [planCost, hg]
      · have hpos : 0 < i := Nat.pos_of_ne_zero hzero
        obtain ⟨op, hop, hstep, hg⟩ := ok.step i hi hpos
        have hparent : (nodes.getD i default).parent < i := ok.parentLt i hi hpos
        have hparentSize : (nodes.getD i default).parent < nodes.size := Nat.lt_trans hparent hi
        obtain ⟨hexec, hcost⟩ := ih _ hparent hparentSize fuel (by omega)
        simp only [Array.getD_eq_getD_getElem?] at hop hstep hg hexec hcost ⊢
        simp only [planTo, Array.getD_eq_getD_getElem?, hop]
        constructor
        · -- Extend the parent's plan by the operator that produced this node.
          rw [Array.toList_push]
          exact executes_append hexec hstep
        · rw [Array.toList_push, planCost_append, hcost]
          simp [planCost, hg]

end NodesOK

end Planner
