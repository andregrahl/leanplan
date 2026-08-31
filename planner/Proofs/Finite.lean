/-
The state space is finite.

A well-formed state is an array of exactly `wordsFor numFacts` machine words, so
it is determined by that many `UInt64`s and no more.  Reading a state as such a
tuple is injective, which makes the well-formed states a `Fintype`.

This is the construction the fuel argument was blocked on.  `loop` recurses on a
`Nat` fuel, and `astar_mono` already shows fuel is only a resource bound — more of
it never changes a finished answer.  With finiteness in hand the rest of the
argument is determined, and it is worth writing down because it needs no
consistency assumption at all:

  * Every node the search creates comes from `record`, which fires only when the
    new `g` is *strictly* below the `g` already recorded for that state.
  * So along any node's parent chain the states are distinct: a state appearing
    twice would have to be recorded at a larger `g` than it already had, which
    `record` forbids.
  * A chain of distinct states is no longer than the cardinality above, so with
    unit costs every recorded `g` is at most that cardinality.
  * For a fixed state the recorded values strictly decrease, so it is recorded at
    most `card + 1` times; over all states, at most `card * (card + 1)` records.
  * Each loop iteration pops one entry, and entries are only ever created by
    `record`, so `card * (card + 1) + 2` iterations suffice.

Both invariants that argument needs are now proved.  `NodeGBounded` in
`Proofs/Search/AStar.lean` is the first — a node's cost is never below what `best`
holds for its state — and `NodesOK.NoRepeat`, established through
`record_fresh`, `expandOne_noRepeat`, `expandFrom_noRepeat` and `expand_noRepeat`,
is the second: no state ever repeats on a parent chain.

What remains is the counting itself: a pigeonhole turning "distinct states in a
finite type" into a numeric bound on chain length, then on costs, then on records,
then on iterations.  It needs unit costs, which this fragment has.  The bound
`2^62` the planner actually passes dwarfs the result for any task that fits in
memory.
-/
import Proofs.Task
import Proofs.Search.Node
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi

namespace Planner

/-- A well-formed state, read as its fixed-length tuple of machine words. -/
def wordsOf (n : Nat) (s : {s : State // State.WF n s}) :
    Fin (State.wordsFor n) → Fin UInt64.size :=
  fun i => (s.val.words.getD i 0).toFin

theorem wordsOf_injective (n : Nat) : Function.Injective (wordsOf n) := by
  rintro ⟨⟨wa⟩, ha⟩ ⟨⟨wb⟩, hb⟩ h
  have hsa : wa.size = State.wordsFor n := ha.size
  have hsb : wb.size = State.wordsFor n := hb.size
  have hw : wa = wb := by
    apply Array.ext
    · rw [hsa, hsb]
    · intro i hia hib
      have hi := congrFun h ⟨i, by rw [← hsa]; exact hia⟩
      simp only [wordsOf] at hi
      have : wa.getD i 0 = wb.getD i 0 := UInt64.toFin_inj.mp hi
      simpa [Array.getD_eq_getD_getElem?, hia, hib] using this
  simp [hw]

/-- **There are only finitely many well-formed states.** -/
noncomputable instance fintypeWF (n : Nat) : Fintype {s : State // State.WF n s} :=
  Fintype.ofInjective (wordsOf n) (wordsOf_injective n)

/-! ### The cost bound

Climbing a node's chain visits distinct states — `NoRepeat` — so mapping each depth
to the state found there is injective into a finite type.  With unit costs the
depth *is* the cost, so a node's cost is below the number of well-formed states.
That is the pigeonhole the fuel argument needs.
-/

theorem g_lt_card (t : Task) (hwf : Task.WF t) {nodes : Array Node} (ok : NodesOK t nodes)
    (hnr : NodesOK.NoRepeat nodes) (hunit : ∀ op ∈ t.ops, op.cost = 1)
    (i : Nat) (hi : i < nodes.size) :
    (nodes.getD i default).g < Fintype.card {s : State // State.WF t.numFacts s} := by
  have hclimb_lt : ∀ k : Nat, NodesOK.climb nodes k i < nodes.size :=
    fun k => NodesOK.climb_lt ok k i hi
  let G := (nodes.getD i default).g
  let f : Fin (G + 1) → {s : State // State.WF t.numFacts s} := fun d =>
    ⟨(nodes.getD (NodesOK.climb nodes d.val i) default).state,
      NodesOK.states_wf hwf ok _ (hclimb_lt d.val)⟩
  have key : ∀ a b : Fin (G + 1), a.val < b.val → f a ≠ f b := by
    intro a b hab heq
    have hsplit : NodesOK.climb nodes b.val i
        = NodesOK.climb nodes (b.val - a.val) (NodesOK.climb nodes a.val i) := by
      rw [← NodesOK.climb_add]
      congr 1
      omega
    have hanc : NodesOK.Ancestor nodes (NodesOK.climb nodes a.val i)
        (NodesOK.climb nodes b.val i) := by
      rw [hsplit]
      exact NodesOK.climb_ancestor nodes _ _
    have hga : (nodes.getD (NodesOK.climb nodes a.val i) default).g = G - a.val :=
      NodesOK.climb_g ok hunit _ _ hi (by have := a.isLt; omega)
    have hgb : (nodes.getD (NodesOK.climb nodes b.val i) default).g = G - b.val :=
      NodesOK.climb_g ok hunit _ _ hi (by have := b.isLt; omega)
    have hidx : NodesOK.climb nodes b.val i ≠ NodesOK.climb nodes a.val i := by
      intro hcon
      rw [hcon, hga] at hgb
      have ha := a.isLt
      have hb := b.isLt
      omega
    exact hnr _ (hclimb_lt a.val) _ hanc hidx (congrArg Subtype.val heq).symm
  have hinj : Function.Injective f := by
    intro a b heq
    by_contra hne
    rcases Nat.lt_or_ge a.val b.val with h | h
    · exact key a b h heq
    · have : b.val < a.val := by
        rcases Nat.lt_or_ge b.val a.val with h' | h'
        · exact h'
        · exact absurd (Fin.ext (Nat.le_antisymm h' h)) hne
      exact key b a this heq.symm
  have hcard := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin] at hcard
  show G < Fintype.card {s : State // State.WF t.numFacts s}
  omega

end Planner
