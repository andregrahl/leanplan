/-
From an operator's add and delete lists to the quantities a heuristic counts.

Every strong heuristic's `Effect` says how one action moves the things it counts,
and the first of those is always the same shape: how many goals of some family are
still unmet.  These lemmas discharge that from facts about the operator that are
*decidable* — which of the family's facts it adds, which it deletes — so a
per-task certificate can establish it rather than a hypothesis assuming it.

The two cases are all a schema can do to a family it touches: achieve exactly one
of its goals, or leave them all alone.  Nothing here is domain-specific.
-/
import Batteries.Data.List.Perm
import Proofs.Combinators
import Proofs.ExampleHeuristics.Base

namespace Planner

/-! ### Counting -/

theorem length_filter_congr {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ x ∈ l, p x = q x) : (l.filter p).length = (l.filter q).length := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
      rw [List.filter_cons, List.filter_cons, h x (by simp)]
      by_cases hq : q x
      · simp [hq, ih (fun y hy => h y (by simp [hy]))]
      · simp [hq, ih (fun y hy => h y (by simp [hy]))]

/-- Dropping exactly one element that the old predicate kept and the new one drops. -/
theorem length_filter_erase_one {α : Type} (l : List α) (p q : α → Bool)
    (x : α) (hx : x ∈ l) (hnd : l.Nodup)
    (hpx : p x = true) (hqx : q x = false)
    (hrest : ∀ y ∈ l, y ≠ x → p y = q y) :
    (l.filter q).length + 1 = (l.filter p).length := by
  induction l with
  | nil => simp at hx
  | cons a rest ih =>
      rw [List.filter_cons, List.filter_cons]
      rcases List.mem_cons.mp hx with rfl | hx'
      · have hnotmem : x ∉ rest := by simpa using hnd.notMem
        have hall : ∀ y ∈ rest, p y = q y := fun y hy =>
          hrest y (by simp [hy]) (by rintro rfl; exact hnotmem hy)
        rw [if_pos hpx, if_neg (by simp [hqx])]
        simp only [List.length_cons]
        rw [length_filter_congr rest p q hall]
      · have hane : a ≠ x := by
          rintro rfl
          exact (by simpa using hnd.notMem : a ∉ rest) hx'
        have heq := hrest a (by simp) hane
        rw [heq]
        have hih := ih hx' hnd.of_cons (fun y hy hyx => hrest y (by simp [hy]) hyx)
        by_cases hq : q a
        · rw [if_pos hq, if_pos hq]
          simp only [List.length_cons]
          omega
        · rw [if_neg (by simp [hq]), if_neg (by simp [hq])]
          exact hih

theorem size_filter_toList {α : Type} (a : Array α) (p : α → Bool) :
    (a.filter p).size = (a.toList.filter p).length := by
  rw [← Array.length_toList, Array.toList_filter]

/-! ### From an operator to the unmet count of a family -/

/--
An operator that achieves none of a family's goals and undoes none leaves the
family's unmet count alone.
-/
theorem unmet_unchanged {α : Type} (items : Array α) (key : α → Fact)
    {n : Nat} {op : Op} {s : State} (hop : Op.WF n op) (hs : State.WF n s)
    (hadd : ∀ y ∈ items, op.add.contains (key y) = false)
    (hdel : ∀ y ∈ items, op.del.contains (key y) = false) :
    (items.filter fun y => !(op.apply s).test (key y)).size
      = (items.filter fun y => !s.test (key y)).size := by
  rw [size_filter_toList, size_filter_toList]
  refine length_filter_congr _ _ _ fun y hy => ?_
  have hy' : y ∈ items := by simpa using hy
  rw [Op.test_apply_same hop hs (hadd y hy') (hdel y hy')]

/--
An operator that achieves exactly one of a family's outstanding goals and undoes
none drops the family's unmet count by exactly one.
-/
theorem unmet_drop_one {α : Type} (items : Array α) (key : α → Fact)
    {n : Nat} {op : Op} {s : State} (hop : Op.WF n op) (hs : State.WF n s)
    (hnd : items.toList.Nodup) (x : α) (hx : x ∈ items)
    (hxadd : op.add.contains (key x) = true) (hxs : s.test (key x) = false)
    (hother : ∀ y ∈ items, y ≠ x → op.add.contains (key y) = false)
    (hdel : ∀ y ∈ items, op.del.contains (key y) = false) :
    (items.filter fun y => !(op.apply s).test (key y)).size + 1
      = (items.filter fun y => !s.test (key y)).size := by
  rw [size_filter_toList, size_filter_toList]
  refine length_filter_erase_one _ _ _ x (by simpa using hx) hnd ?_ ?_ ?_
  · simp [hxs]
  · simp [Op.test_apply_add hop hs hxadd]
  · intro y hy hyx
    have hy' : y ∈ items := by simpa using hy
    rw [Op.test_apply_same hop hs (hother y hy' hyx) (hdel y hy')]

/-! ### Filter counts in general

`unmet_drop_one` and `unmet_unchanged` are the special case where the predicate is
"this goal does not hold".  Several quantities are filters with compound
predicates instead — a spanner that is both usable and carried, a car that is
ashore and located — so the same two shapes are stated once more without fixing
what the predicate is.
-/

/-- Exactly one element stops satisfying the predicate. -/
theorem filter_size_drop_one {α : Type} (items : Array α) (p q : α → Bool) (x : α)
    (hx : x ∈ items) (hnd : items.toList.Nodup)
    (hpx : p x = true) (hqx : q x = false)
    (hrest : ∀ y ∈ items, y ≠ x → p y = q y) :
    (items.filter q).size + 1 = (items.filter p).size := by
  rw [size_filter_toList, size_filter_toList]
  exact length_filter_erase_one _ _ _ x (by simpa using hx) hnd hpx hqx
    (fun y hy hyx => hrest y (by simpa using hy) hyx)

/-- Nothing changes. -/
theorem filter_size_congr {α : Type} (items : Array α) (p q : α → Bool)
    (h : ∀ y ∈ items, p y = q y) : (items.filter p).size = (items.filter q).size := by
  rw [size_filter_toList, size_filter_toList]
  exact length_filter_congr _ _ _ fun y hy => h y (by simpa using hy)

/-! ### Resource pools

The other recurring shape is a pool the heuristic counts as *held* rather than
outstanding — usable spanners in hand, calibrated cameras, empty stores.  Same
argument, read the other way round.
-/

theorem countHolding_eq (facts : Array Fact) (s : State) :
    countHolding facts s = (facts.filter fun f => s.test f).size := by
  rw [size_filter_toList]
  unfold countHolding
  have key : ∀ (l : List Fact) (b : Nat),
      l.foldl (fun acc f => if s.test f then acc + 1 else acc) b
        = b + (l.filter fun f => s.test f).length := by
    intro l
    induction l with
    | nil => intro b; simp
    | cons x rest ih =>
        intro b
        by_cases h : s.test x
        · simp only [List.foldl_cons, List.filter_cons, h, if_true, ih, List.length_cons]
          omega
        · simp only [List.foldl_cons, List.filter_cons, h, ih]
          simp
  rw [← Array.foldl_toList]
  simpa using key facts.toList 0

/-- An operator that produces exactly one of a pool's facts raises the count by one. -/
theorem held_gain_one (facts : Array Fact) {n : Nat} {op : Op} {s : State}
    (hop : Op.WF n op) (hs : State.WF n s) (hnd : facts.toList.Nodup)
    (f : Fact) (hf : f ∈ facts)
    (hadd : op.add.contains f = true) (hfs : s.test f = false)
    (hother : ∀ g ∈ facts, g ≠ f → op.add.contains g = false)
    (hdel : ∀ g ∈ facts, op.del.contains g = false) :
    countHolding facts s + 1 = countHolding facts (op.apply s) := by
  rw [countHolding_eq, countHolding_eq, size_filter_toList, size_filter_toList]
  refine length_filter_erase_one _ _ _ f (by simpa using hf) hnd ?_ ?_ ?_
  · exact Op.test_apply_add hop hs hadd
  · exact hfs
  · intro g hg hgf
    have hg' : g ∈ facts := by simpa using hg
    exact Op.test_apply_same hop hs (hother g hg' hgf) (hdel g hg')

/-- An operator that consumes exactly one of a pool's facts lowers the count by one. -/
theorem held_drop_one (facts : Array Fact) {n : Nat} {op : Op} {s : State}
    (hop : Op.WF n op) (hs : State.WF n s) (hnd : facts.toList.Nodup)
    (f : Fact) (hf : f ∈ facts)
    (hdelf : op.del.contains f = true) (haddf : op.add.contains f = false)
    (hfs : s.test f = true)
    (hother : ∀ g ∈ facts, g ≠ f → op.add.contains g = false)
    (hdel : ∀ g ∈ facts, g ≠ f → op.del.contains g = false) :
    countHolding facts (op.apply s) + 1 = countHolding facts s := by
  rw [countHolding_eq, countHolding_eq, size_filter_toList, size_filter_toList]
  refine length_filter_erase_one _ _ _ f (by simpa using hf) hnd hfs ?_ ?_
  · exact Op.test_apply_del hop hs haddf hdelf
  · intro g hg hgf
    have hg' : g ∈ facts := by simpa using hg
    exact (Op.test_apply_same hop hs (hother g hg' hgf) (hdel g hg' hgf)).symm

/-- An operator touching none of a pool's facts leaves the count alone. -/
theorem held_unchanged (facts : Array Fact) {n : Nat} {op : Op} {s : State}
    (hop : Op.WF n op) (hs : State.WF n s)
    (hadd : ∀ g ∈ facts, op.add.contains g = false)
    (hdel : ∀ g ∈ facts, op.del.contains g = false) :
    countHolding facts (op.apply s) = countHolding facts s := by
  rw [countHolding_eq, countHolding_eq, size_filter_toList, size_filter_toList]
  refine length_filter_congr _ _ _ fun g hg => ?_
  have hg' : g ∈ facts := by simpa using hg
  exact Op.test_apply_same hop hs (hadd g hg') (hdel g hg')

/-! ### Deduplicated sets

Several heuristics count *distinct* things — the floors a lift must still visit,
the locations a vehicle must still reach, the directions a satellite must still
turn to.  Those are `distinct` lists, and what the consistency arguments need of
them is how their length moves: never up when the underlying collection shrinks,
and by at most one when it gains a single element.
-/

theorem mem_distinct {x : Nat} : ∀ l : List Nat, x ∈ distinct l ↔ x ∈ l := by
  intro l
  induction l with
  | nil => simp [distinct]
  | cons a rest ih =>
      simp only [distinct, List.mem_cons, List.mem_filter, ih]
      constructor
      · rintro (rfl | ⟨h1, h2⟩)
        · exact Or.inl rfl
        · exact Or.inr h1
      · rintro (rfl | h)
        · exact Or.inl rfl
        · by_cases hax : x = a
          · exact Or.inl hax
          · exact Or.inr ⟨h, by simpa using hax⟩

theorem distinct_nodup : ∀ l : List Nat, (distinct l).Nodup := by
  intro l
  induction l with
  | nil => simp [distinct]
  | cons a rest ih =>
      simp only [distinct]
      refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · simp [List.mem_filter]
      · exact ih.filter _

/-- Fewer things to visit is never a longer list. -/
theorem length_distinct_mono (l l' : List Nat) (h : ∀ x ∈ l, x ∈ l') :
    (distinct l).length ≤ (distinct l').length := by
  refine (List.subperm_of_subset (distinct_nodup l) ?_).length_le
  intro x hx
  exact (mem_distinct l').mpr (h x ((mem_distinct l).mp hx))

/-- A duplicate-free list is no longer than anything it is contained in. -/
theorem length_le_of_subset (l l' : List Nat) (hnd : l.Nodup) (h : ∀ x ∈ l, x ∈ l') :
    l.length ≤ l'.length :=
  (List.subperm_of_subset hnd h).length_le

/-- Allowing one exception costs one. -/
theorem length_le_succ_of_subset (l l' : List Nat) (a : Nat) (hnd : l.Nodup)
    (h : ∀ x ∈ l, x ∈ l' ∨ x = a) : l.length ≤ l'.length + 1 := by
  have hsub : l ⊆ a :: l' := by
    intro x hx
    rcases h x hx with h' | rfl
    · exact List.mem_cons.mpr (Or.inr h')
    · exact List.mem_cons.mpr (Or.inl rfl)
  have := (List.subperm_of_subset hnd hsub).length_le
  simpa using this

/-- One extra element lengthens the list by at most one. -/
theorem length_distinct_le_succ (l l' : List Nat) (a : Nat)
    (h : ∀ x ∈ l, x ∈ l' ∨ x = a) :
    (distinct l).length ≤ (distinct l').length + 1 := by
  have hsub : ∀ x ∈ l, x ∈ a :: l' := by
    intro x hx
    rcases h x hx with h' | rfl
    · exact List.mem_cons.mpr (Or.inr h')
    · exact List.mem_cons.mpr (Or.inl rfl)
  refine Nat.le_trans (length_distinct_mono l (a :: l') hsub) ?_
  show (distinct (a :: l')).length ≤ (distinct l').length + 1
  simp only [distinct, List.length_cons]
  have : ((distinct l').filter fun y => y != a).length ≤ (distinct l').length :=
    List.length_filter_le _ _
  omega

end Planner
