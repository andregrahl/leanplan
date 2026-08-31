/-
What a distance table has to satisfy, and what follows from it.

The heuristics that measure travel — transport, sokoban, spanner, floortile,
rovers — all need the same two facts about the table `Planner/Distance.lean`
builds: it is zero on the diagonal, and it falls by at most one along any edge.
Those two give both halves of what a heuristic needs: admissibility, because the
table then underestimates the length of every walk, and consistency, because one
step of the graph changes the entry by at most one.

The two facts are *checked* against the table the planner actually built rather
than derived from a proof that breadth-first search is optimal.  That is a
deliberate choice and it is the stronger statement of the two: it rules out a bug
in the search as well as an error in its specification, and it costs one pass
over the graph at load time.  Nothing downstream cares how the numbers were
produced — only that they satisfy these inequalities.
-/
import Proofs.Combinators
import Planner.Distance

namespace Planner

namespace Distances

/-- The two properties a distance table must have for a heuristic to rely on it. -/
structure Sound (g : Graph) (d : Distances) : Prop where
  /-- Nothing to travel when already there. -/
  self : ∀ i, i < g.size → d.get i i = 0
  /-- One edge of the graph changes the distance to any target by at most one. -/
  step : ∀ i i' j, i < g.size → j < g.size → i' ∈ g.adj.getD i #[] →
    d.get i j ≤ 1 + d.get i' j
  /-- Nothing is farther than the cap. -/
  le_bound : ∀ i j, d.get i j ≤ d.bound
  /-- The table has a row per node at most, so a non-node reads as the cap. -/
  tableSize : d.table.size ≤ g.size
  /-- And the cap is at least the node count, so no node index equals it. -/
  boundGe : g.size ≤ d.bound
  /--
  Being within the cap survives stepping back along an edge.

  The triangle inequality alone does not give this: `d i j ≤ 1 + d i' j` can put
  `d i j` at the cap when `d i' j` is one below it.  A value that compares a
  distance against the cap, to ask whether a thing is reachable at all, needs
  this and cannot derive it.
  -/
  reach : ∀ i i' j, i < g.size → j < g.size → i' ∈ g.adj.getD i #[] →
    d.get i' j < d.bound → d.get i j < d.bound
  /-- No row is longer than the node count, so a column past it reads as the cap. -/
  rowSize : ∀ i, (d.table.getD i #[]).size ≤ g.size

theorem sound_of_check {g : Graph} {d : Distances} (h : check g d = true) : Sound g d := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, Array.all_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hself, hstep⟩, hcap⟩, hts⟩, hbg⟩, hreach⟩, hrow⟩ := h
  refine ⟨?_, ?_, ?_, hts, hbg, ?_, ?_⟩
  · intro i hi
    have := hself i (by simpa using hi)
    simpa using this
  · intro i i' j hi hj hmem
    have hi' := hstep i (by simpa using hi)
    obtain ⟨k, hk, hkval⟩ := Array.getElem_of_mem hmem
    have := hi' k hk
    rw [hkval] at this
    have := this j (by simpa using hj)
    simpa using this
  · intro i j
    show ((d.table.getD i #[]).getD j d.bound) ≤ d.bound
    rw [Array.getD_eq_getD_getElem?]
    rcases hx : (d.table.getD i #[])[j]? with _ | x
    · simp
    · simp only [Option.getD_some]
      have hxmem : x ∈ d.table.getD i #[] := Array.mem_of_getElem? hx
      by_cases hi : i < d.table.size
      · have hrow : d.table.getD i #[] ∈ d.table := by
          rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
          simpa using Array.getElem_mem hi
        have h1 := hcap _ (by simpa using hrow) x (by simpa using hxmem)
        simpa using h1
      · rw [Array.getD_eq_getD_getElem?,
          Array.getElem?_eq_none (by omega)] at hxmem
        simp at hxmem

  · intro i i' j hi hj hmem hlt
    have h1 := hreach i (by simpa using hi)
    obtain ⟨k, hk, hkval⟩ := Array.getElem_of_mem hmem
    have h2 := h1 k hk
    rw [hkval] at h2
    have h3 := h2 j (by simpa using hj)
    simp only [decide_eq_true_eq] at h3
    exact h3 hlt

  · intro i
    by_cases hi : i < d.table.size
    · have hmem : d.table.getD i #[] ∈ d.table := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
        simpa using Array.getElem_mem hi
      have := hrow _ (by simpa using hmem)
      simpa using this
    · rw [Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_none (by simpa using Nat.le_of_not_lt hi)]
      simp

/-- The fallback table satisfies the finite soundness check for every graph. -/
theorem check_zero (g : Graph) : check g (zero g) = true := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, Array.all_eq_true,
    decide_eq_true_eq]
  have hget {i j : Nat} (hi : i < g.size) (hj : j < g.size) :
      (zero g).get i j = 0 := by
    simp [zero, Distances.get, Array.getD_eq_getD_getElem?, hi, hj]
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro i hi
    simpa using hget (by simpa using hi) (by simpa using hi)
  · intro i hi i' hi' j hj
    rw [hget (by simpa using hi) (by simpa using hj)]
    omega
  · intro row hrow x hx
    have hrow' : row ∈ List.replicate g.size (Array.replicate g.size 0) := by
      simpa [zero] using hrow
    have hrowEq : row = Array.replicate g.size 0 := by
      exact List.eq_of_mem_replicate hrow'
    subst row
    have hx' : x ∈ List.replicate g.size 0 := by simpa using hx
    have hxEq : x = 0 := List.eq_of_mem_replicate hx'
    subst x
    omega
  · simp [zero]
  · rfl
  · intro i hi i' hi' j hj hlt
    rw [hget (by simpa using hi) (by simpa using hj)]
    exact Nat.zero_lt_of_lt (by simpa using hi)
  · intro row hrow
    have hrow' : row ∈ List.replicate g.size (Array.replicate g.size 0) := by
      simpa [zero] using hrow
    have hrowEq : row = Array.replicate g.size 0 := by
      exact List.eq_of_mem_replicate hrow'
    subst row
    simp

/-- `of` returns either its checked BFS result or the universally safe fallback. -/
theorem check_of (g : Graph) : check g (of g) = true := by
  by_cases h : check g (raw g) = true
  · simp [of, h]
  · have hf : check g (raw g) = false := Bool.eq_false_of_not_eq_true h
    simp [of, hf, check_zero]

/-- Every table produced by the public constructor is sound. -/
theorem sound_of (g : Graph) : Sound g (of g) :=
  sound_of_check (check_of g)

/-- Past the last column, every distance reads as the cap. -/
theorem get_of_col_ge {g : Graph} {d : Distances} (hd : Sound g d) (i : Nat) {j : Nat}
    (hj : g.size ≤ j) : d.get i j = d.bound := by
  show (d.table.getD i #[]).getD j d.bound = d.bound
  rw [Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_none (le_trans (hd.rowSize i) hj)]
  simp

/-- Past the last row, every distance reads as the cap. -/
theorem get_of_ge {g : Graph} {d : Distances} (hd : Sound g d) {i : Nat}
    (hi : g.size ≤ i) (j : Nat) : d.get i j = d.bound := by
  have hrow : d.table.getD i #[] = #[] := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (le_trans hd.tableSize hi)]
    rfl
  show (d.table.getD i #[]).getD j d.bound = d.bound
  rw [hrow]
  simp

/-- A walk of `n` edges in the graph. -/
inductive Walk (g : Graph) : Nat → Nat → Nat → Prop where
  | nil (i : Nat) : Walk g i i 0
  | cons {i i' j n : Nat} (hi : i < g.size) :
      i' ∈ g.adj.getD i #[] → Walk g i' j n → Walk g i j (n + 1)

/--
The table underestimates every walk.  This is the admissibility half: a thing
that has to travel from `i` to `j` takes at least `d.get i j` steps, whatever
route it takes.
-/
theorem le_walk {g : Graph} {d : Distances} (hd : Sound g d) {i j n : Nat}
    (hj : j < g.size) (hw : Walk g i j n) : d.get i j ≤ n := by
  induction hw with
  | nil i => exact Nat.le_of_eq (hd.self i hj)
  | @cons i i' j n hi hmem _ ih =>
      exact Nat.le_trans (hd.step i i' j hi hj hmem) (by omega)

end Distances

/-- `minFrom` never exceeds the cap: it folds `min` from `bound` downwards. -/
theorem Distances.minFrom_le (d : Distances) (sources : Array Nat) (j : Nat) :
    d.minFrom sources j ≤ d.bound := by
  unfold Distances.minFrom
  have key : ∀ (l : List Nat) (b : Nat), b ≤ d.bound →
      l.foldl (fun acc i => min acc (d.get i j)) b ≤ d.bound := by
    intro l
    induction l with
    | nil => intro b hb; exact hb
    | cons x rest ih => intro b hb; exact ih _ (Nat.le_trans (Nat.min_le_left _ _) hb)
  rw [← Array.foldl_toList]
  exact key _ _ (Nat.le_refl _)

/-! ### Moving the sources

The heuristics that use a distance table all bound movement the same way: the
distance from wherever the movers are now to wherever something has to be.  When
a mover takes one edge, that bound changes by at most one — which is the triangle
inequality of `Sound`, lifted to the minimum over several movers.
-/

theorem foldl_min_le_init (f : Nat → Nat) : ∀ (l : List Nat) (b : Nat),
    l.foldl (fun acc i => min acc (f i)) b ≤ b := by
  intro l
  induction l with
  | nil => intro b; exact Nat.le_refl _
  | cons x rest ih => intro b; exact Nat.le_trans (ih _) (Nat.min_le_left _ _)

/-- A minimum below the cap is achieved by one of the sources. -/
theorem minFrom_lt_bound (d : Distances) {src : Array Nat} {l : Nat}
    (h : d.minFrom src l < d.bound) : ∃ u ∈ src, d.get u l < d.bound := by
  show ∃ u ∈ src, _
  rw [Distances.minFrom, ← Array.foldl_toList] at h
  have key : ∀ (xs : List Nat) (b : Nat),
      xs.foldl (fun acc i => min acc (d.get i l)) b < d.bound →
      b < d.bound ∨ ∃ u ∈ xs, d.get u l < d.bound := by
    intro xs
    induction xs with
    | nil => intro b hb; exact Or.inl hb
    | cons x rest ih =>
        intro b hb
        rw [List.foldl_cons] at hb
        rcases ih _ hb with h1 | ⟨u, hu, hlt⟩
        · rcases Nat.lt_or_ge (d.get x l) b with h2 | h2
          · exact Or.inr ⟨x, by simp, by omega⟩
          · exact Or.inl (by omega)
        · exact Or.inr ⟨u, by simp [hu], hlt⟩
  rcases key src.toList d.bound h with h1 | ⟨u, hu, hlt⟩
  · omega
  · exact ⟨u, by simpa using hu, hlt⟩

theorem minFrom_le_of_mem (d : Distances) {src : Array Nat} {u : Nat} (hu : u ∈ src) (l : Nat) :
    d.minFrom src l ≤ d.get u l := by
  unfold Distances.minFrom
  rw [← Array.foldl_toList]
  have key : ∀ (xs : List Nat) (b : Nat) (v : Nat), v ∈ xs →
      xs.foldl (fun acc i => min acc (d.get i l)) b ≤ d.get v l := by
    intro xs
    induction xs with
    | nil => intro b v hv; simp at hv
    | cons x rest ih =>
        intro b v hv
        rcases List.mem_cons.mp hv with rfl | hv'
        · exact Nat.le_trans (foldl_min_le_init _ rest _) (Nat.min_le_right _ _)
        · exact ih _ v hv'
  exact key _ _ u (by simpa using hu)

/-- Moving each source one edge changes the distance to a target by at most one. -/
theorem minFrom_le_succ (d : Distances) (src dst : Array Nat) (l : Nat)
    (h : ∀ w ∈ dst, ∃ u ∈ src, d.get u l ≤ 1 + d.get w l) :
    d.minFrom src l ≤ 1 + d.minFrom dst l := by
  have key : ∀ m : Nat, m ≤ d.bound → (∀ w ∈ dst, m ≤ 1 + d.get w l) →
      m ≤ 1 + d.minFrom dst l := by
    intro m hb hall
    unfold Distances.minFrom
    rw [← Array.foldl_toList]
    have inner : ∀ (xs : List Nat) (b : Nat), m ≤ 1 + b →
        (∀ w ∈ xs, m ≤ 1 + d.get w l) →
        m ≤ 1 + xs.foldl (fun acc i => min acc (d.get i l)) b := by
      intro xs
      induction xs with
      | nil => intro b hbb _; exact hbb
      | cons x rest ih =>
          intro b hbb hallx
          have hx := hallx x (by simp)
          refine ih _ ?_ (fun w hw => hallx w (by simp [hw]))
          show m ≤ 1 + min b (d.get x l)
          omega
    exact inner _ _ (by omega) (fun w hw => hall w (by simpa using hw))
  refine key (d.minFrom src l) (d.minFrom_le src l) ?_
  intro w hw
  obtain ⟨u, hu, hle⟩ := h w hw
  exact Nat.le_trans (minFrom_le_of_mem d hu l) hle

/-- A `max` over a fixed collection moves by at most one when each term does. -/
theorem foldl_max_le_succ {α : Type} (l : List α) (f g : α → Nat)
    (h : ∀ x ∈ l, f x ≤ 1 + g x) :
    ∀ b b' : Nat, b ≤ 1 + b' →
      l.foldl (fun acc x => max acc (f x)) b
        ≤ 1 + l.foldl (fun acc x => max acc (g x)) b' := by
  induction l with
  | nil => intro b b' hb; exact hb
  | cons x rest ih =>
      intro b b' hb
      have hx := h x (by simp)
      refine ih (fun y hy => h y (by simp [hy])) _ _ ?_
      show max b (f x) ≤ 1 + max b' (g x)
      omega

/-- The same when no term rises. -/
theorem foldl_max_mono {α : Type} (l : List α) (f g : α → Nat)
    (h : ∀ x ∈ l, f x ≤ g x) :
    ∀ b b' : Nat, b ≤ b' →
      l.foldl (fun acc x => max acc (f x)) b ≤ l.foldl (fun acc x => max acc (g x)) b' := by
  induction l with
  | nil => intro b b' hb; exact hb
  | cons x rest ih =>
      intro b b' hb
      have hx := h x (by simp)
      refine ih (fun y hy => h y (by simp [hy])) _ _ ?_
      show max b (f x) ≤ max b' (g x)
      omega

/-- A running maximum never falls below where it started. -/
theorem foldl_max_ge_init {α : Type} (l : List α) (f : α → Nat) :
    ∀ b : Nat, b ≤ l.foldl (fun acc x => max acc (f x)) b := by
  induction l with
  | nil => intro b; exact Nat.le_refl _
  | cons x rest ih =>
      intro b
      exact Nat.le_trans (Nat.le_max_left b (f x)) (ih (max b (f x)))

/-- Everything in the collection is below the running maximum. -/
theorem foldl_max_ge_mem {α : Type} (l : List α) (f : α → Nat) {x : α} (hx : x ∈ l) :
    ∀ b : Nat, f x ≤ l.foldl (fun acc y => max acc (f y)) b := by
  induction l with
  | nil => intro b; simp at hx
  | cons a rest ih =>
      intro b
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact Nat.le_trans (Nat.le_max_right b (f x)) (foldl_max_ge_init rest f (max b (f x)))
      · exact ih hx' _

/-- A running minimum moves by at most one when each term does. -/
theorem foldl_min_le_succ {α : Type} (l : List α) (f g : α → Nat)
    (h : ∀ x ∈ l, f x ≤ 1 + g x) :
    ∀ b b' : Nat, b ≤ 1 + b' →
      l.foldl (fun acc x => min acc (f x)) b
        ≤ 1 + l.foldl (fun acc x => min acc (g x)) b' := by
  induction l with
  | nil => intro b b' hb; exact hb
  | cons x rest ih =>
      intro b b' hb
      have hx := h x (by simp)
      refine ih (fun y hy => h y (by simp [hy])) _ _ ?_
      show min b (f x) ≤ 1 + min b' (g x)
      omega

/--
A fold whose step threads the running accumulator moves by at most one when each
step does.  This is what the nested folds need — an inner minimum that starts from
the outer accumulator rather than from a fixed bound.
-/
theorem foldl_step_le_succ {α : Type} (l : List α) (f g : Nat → α → Nat)
    (h : ∀ x ∈ l, ∀ b b' : Nat, b ≤ 1 + b' → f b x ≤ 1 + g b' x) :
    ∀ b b' : Nat, b ≤ 1 + b' → l.foldl f b ≤ 1 + l.foldl g b' := by
  induction l with
  | nil => intro b b' hb; exact hb
  | cons x rest ih =>
      intro b b' hb
      exact ih (fun y hy => h y (by simp [hy])) _ _ (h x (by simp) b b' hb)

/-- A running maximum stays under any bound every term respects. -/
theorem foldl_max_le_bound {α : Type} (l : List α) (f : α → Nat) (M : Nat)
    (h : ∀ x ∈ l, f x ≤ M) : ∀ b, b ≤ M → l.foldl (fun acc x => max acc (f x)) b ≤ M := by
  induction l with
  | nil => intro b hb; exact hb
  | cons x rest ih =>
      intro b hb
      have hxm := h x (by simp)
      refine ih (fun y hy => h y (by simp [hy])) _ ?_
      show max b (f x) ≤ M
      omega


namespace Graph

open Pddl

/-! ### What `ofStatic` builds

The node index and the adjacency lists are two folds.  Reading an edge back out
of the graph is what a consistency proof needs: a schema whose static
precondition names an edge must be able to say that the graph has it.
-/

private theorem index_lt_aux {P : Nat → Prop} :
    ∀ (l : List (Name × Nat)) (m : Std.HashMap Name Nat),
      (∀ (y : Name) (j : Nat), m[y]? = some j → P j) → (∀ e ∈ l, P e.2) →
      ∀ (x : Name) (i : Nat), (l.foldl (fun m e => m.insert e.1 e.2) m)[x]? = some i → P i := by
  intro l
  induction l with
  | nil => intro m hm _ x i h; exact hm x i h
  | cons e l ih =>
      intro m hm hl x i h
      refine ih (m.insert e.1 e.2) ?_ (fun a ha => hl a (List.mem_cons_of_mem _ ha)) x i h
      intro y j hy
      rw [Std.HashMap.getElem?_insert] at hy
      split at hy
      · have : j = e.2 := by simpa using hy.symm
        rw [this]; exact hl e (List.mem_cons_self ..)
      · exact hm y j hy

private theorem index_aux {P : Name → Nat → Prop} :
    ∀ (l : List (Name × Nat)) (m : Std.HashMap Name Nat),
      (∀ (y : Name) (j : Nat), m[y]? = some j → P y j) → (∀ e ∈ l, P e.1 e.2) →
      ∀ (x : Name) (i : Nat), (l.foldl (fun m e => m.insert e.1 e.2) m)[x]? = some i →
        P x i := by
  intro l
  induction l with
  | nil => intro m hm _ x i h; exact hm x i h
  | cons e l ih =>
      intro m hm hl x i h
      refine ih (m.insert e.1 e.2) ?_ (fun a ha => hl a (List.mem_cons_of_mem _ ha)) x i h
      intro y j hy
      rw [Std.HashMap.getElem?_insert] at hy
      split at hy
      · rename_i hkey
        have hj : j = e.2 := by simpa using hy.symm
        have hy2 : y = e.1 := by
          have h3 : (e.1 == y) = true := by simpa using hkey
          exact (by simpa using h3 : e.1 = y).symm
        rw [hj, hy2]; exact hl e (List.mem_cons_self ..)
      · exact hm y j hy

/-- The index a name is given is the position that name sits at. -/
theorem nodeIndex_get {nodes : Array Name} {x : Name} {i : Nat}
    (h : (nodeIndex nodes)[x]? = some i) : nodes.getD i "" = x := by
  unfold nodeIndex at h
  rw [← Array.foldl_toList] at h
  refine index_aux (P := fun y j => nodes.getD j "" = y) _ {} ?_ ?_ x i h
  · intro y j hy; simp at hy
  · intro e he
    rw [Array.toList_zipIdx] at he
    obtain ⟨-, hlt, hget⟩ := List.mem_zipIdx he
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hlt)]
    simpa using hget.symm

theorem nodeIndex_lt {nodes : Array Name} {x : Name} {i : Nat}
    (h : (nodeIndex nodes)[x]? = some i) : i < nodes.size := by
  unfold nodeIndex at h
  rw [← Array.foldl_toList] at h
  refine index_lt_aux (P := fun j => j < nodes.size) _ {} ?_ ?_ x i h
  · intro y j hy; simp at hy
  · intro e he
    rw [Array.toList_zipIdx] at he
    have := List.mem_zipIdx he
    obtain ⟨-, hlt, -⟩ := this
    simpa using hlt

private theorem index_mem_aux :
    ∀ (l : List (Name × Nat)) (m : Std.HashMap Name Nat) (x : Name),
      ((∃ i, (x, i) ∈ l) ∨ (m[x]?).isSome) →
      ((l.foldl (fun m e => m.insert e.1 e.2) m)[x]?).isSome := by
  intro l
  induction l with
  | nil =>
      intro m x h
      rcases h with ⟨i, hi⟩ | h
      · simp at hi
      · exact h
  | cons e l ih =>
      intro m x h
      refine ih (m.insert e.1 e.2) x ?_
      rcases h with ⟨i, hi⟩ | h
      · rcases List.mem_cons.mp hi with heq | hmem
        · refine Or.inr ?_
          rw [Std.HashMap.getElem?_insert]
          have : x = e.1 := by rw [← heq]
          simp [this]
        · exact Or.inl ⟨i, hmem⟩
      · refine Or.inr ?_
        rw [Std.HashMap.getElem?_insert]
        split
        · simp
        · exact h

theorem nodeIndex_isSome {nodes : Array Name} {x : Name} (h : x ∈ nodes) :
    ((nodeIndex nodes)[x]?).isSome := by
  unfold nodeIndex
  rw [← Array.foldl_toList]
  refine index_mem_aux _ {} x (Or.inl ?_)
  obtain ⟨i, hi, hval⟩ := Array.getElem_of_mem h
  refine ⟨i, ?_⟩
  rw [Array.toList_zipIdx, List.mem_zipIdx_iff_getElem?]
  rw [List.getElem?_eq_getElem (by simpa using hi)]
  simp [hval]

/-! ### The edges the graph holds -/

private theorem getD_set_ne {adj : Array (Array Nat)} {u i : Nat} {v : Array Nat}
    (h : i ≠ u) : (adj.setIfInBounds u v).getD i #[] = adj.getD i #[] := by
  unfold Array.setIfInBounds
  split
  · rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
      Array.getElem?_set_ne (h := by assumption) (Ne.symm h)]
  · rfl

private theorem getD_set_self {adj : Array (Array Nat)} {u : Nat} {v : Array Nat}
    (h : u < adj.size) : (adj.setIfInBounds u v).getD u #[] = v := by
  unfold Array.setIfInBounds
  rw [dif_pos h, Array.getD_eq_getD_getElem?, Array.getElem?_set_self (by simpa using h)]
  rfl

private theorem addEdge_size (index : Std.HashMap Name Nat) (adj : Array (Array Nat))
    (a : GroundAtom) : (addEdge index adj a).size = adj.size := by
  unfold addEdge
  split <;> [skip; rfl]
  split <;> [rw [Array.size_setIfInBounds]; rfl]

private theorem addEdge_mono (index : Std.HashMap Name Nat) (adj : Array (Array Nat))
    (a : GroundAtom) {i j : Nat} (h : j ∈ adj.getD i #[]) :
    j ∈ (addEdge index adj a).getD i #[] := by
  unfold addEdge
  split <;> [skip; exact h]
  split <;> [skip; exact h]
  rename_i u _ v _
  by_cases hu : i = u
  · subst hu
    by_cases hlt : i < adj.size
    · rw [getD_set_self hlt]
      exact Array.mem_push.mpr (Or.inl h)
    · rw [Array.setIfInBounds, dif_neg hlt]
      exact h
  · rw [getD_set_ne hu]; exact h

private theorem foldEdges_size (index : Std.HashMap Name Nat) :
    ∀ (l : List GroundAtom) (adj : Array (Array Nat)),
      (l.foldl (addEdge index) adj).size = adj.size := by
  intro l
  induction l with
  | nil => intro adj; rfl
  | cons a l ih => intro adj; rw [List.foldl_cons, ih, addEdge_size]

private theorem foldEdges_mono (index : Std.HashMap Name Nat) :
    ∀ (l : List GroundAtom) (adj : Array (Array Nat)) {i j : Nat},
      j ∈ adj.getD i #[] → j ∈ (l.foldl (addEdge index) adj).getD i #[] := by
  intro l
  induction l with
  | nil => intro adj i j h; exact h
  | cons a l ih => intro adj i j h; exact ih _ (addEdge_mono index adj a h)

private theorem foldEdges_mem (index : Std.HashMap Name Nat) (pred : Name) :
    ∀ (l : List GroundAtom) (adj : Array (Array Nat)) {x y : Name} {i j : Nat},
      ({ pred := pred, args := [x, y] } : GroundAtom) ∈ l →
      index[x]? = some i → index[y]? = some j → i < adj.size →
      j ∈ (l.foldl (addEdge index) adj).getD i #[] := by
  intro l
  induction l with
  | nil => intro adj x y i j hmem _ _ _; simp at hmem
  | cons a l ih =>
      intro adj x y i j hmem hx hy hlt
      rcases List.mem_cons.mp hmem with heq | htail
      · subst heq
        rw [List.foldl_cons]
        refine foldEdges_mono index l _ ?_
        show j ∈ (addEdge index adj { pred := pred, args := [x, y] }).getD i #[]
        unfold addEdge
        simp only [hx, hy]
        rw [getD_set_self hlt]
        exact Array.mem_push.mpr (Or.inr rfl)
      · rw [List.foldl_cons]
        exact ih _ htail hx hy (by rw [addEdge_size]; exact hlt)

/-- One adjacency list per node. -/
theorem adj_size (nodes : Array Name) (edges : Array GroundAtom) :
    (ofEdges nodes edges).adj.size = (ofEdges nodes edges).size := by
  show (edges.foldl (init := Array.replicate nodes.size #[]) (addEdge (nodeIndex nodes))).size
    = nodes.size
  rw [← Array.foldl_toList, foldEdges_size]
  simp

/--
An edge the task's static atoms name is an edge of the graph, as long as both
of its ends are nodes.  This is what lets a schema whose static precondition
names an edge use the distance table's triangle inequality.
-/
theorem mem_adj_of_mem {nodes : Array Name} {edges : Array GroundAtom}
    {pred x y : Name} {i j : Nat}
    (hmem : ({ pred := pred, args := [x, y] } : GroundAtom) ∈ edges)
    (hx : (ofEdges nodes edges).find? x = some i)
    (hy : (ofEdges nodes edges).find? y = some j) :
    j ∈ (ofEdges nodes edges).adj.getD i #[] := by
  have hix : (nodeIndex nodes)[x]? = some i := hx
  have hiy : (nodeIndex nodes)[y]? = some j := hy
  simp only [ofEdges]
  rw [← Array.foldl_toList]
  refine foldEdges_mem (nodeIndex nodes) pred _ _ (by simpa using hmem) hix hiy ?_
  rw [Array.size_replicate]
  exact nodeIndex_lt hix

theorem mem_adj_of_static {t : Task} {pred : Name} {nodes : Array Name}
    {x y : Name} {i j : Nat}
    (hmem : ({ pred := pred, args := [x, y] } : GroundAtom) ∈ t.staticAtoms)
    (hx : (ofStatic t pred nodes).find? x = some i)
    (hy : (ofStatic t pred nodes).find? y = some j) :
    j ∈ (ofStatic t pred nodes).adj.getD i #[] :=
  mem_adj_of_mem (by simp only [Array.mem_filter]; exact ⟨by simpa using hmem, by simp⟩) hx hy

/-- Reading the index back gives the name it was made from. -/
theorem find?_node {nodes : Array Name} {edges : Array GroundAtom} {x : Name} {i : Nat}
    (h : (ofEdges nodes edges).find? x = some i) :
    (ofEdges nodes edges).nodes.getD i "" = x :=
  nodeIndex_get (nodes := nodes) h

/-- Every index the graph hands out is a node. -/
theorem find?_lt' {nodes : Array Name} {edges : Array GroundAtom} {x : Name} {i : Nat}
    (h : (ofEdges nodes edges).find? x = some i) : i < (ofEdges nodes edges).size := by
  have : (nodeIndex nodes)[x]? = some i := h
  exact nodeIndex_lt this

theorem find?_lt {t : Task} {pred : Name} {nodes : Array Name} {x : Name} {i : Nat}
    (h : (ofStatic t pred nodes).find? x = some i) : i < (ofStatic t pred nodes).size :=
  find?_lt' h

/-- And every node has one. -/
theorem find?_isSome' {nodes : Array Name} {edges : Array GroundAtom} {x : Name}
    (h : x ∈ nodes) : ((ofEdges nodes edges).find? x).isSome := nodeIndex_isSome h

theorem find?_isSome {t : Task} {pred : Name} {nodes : Array Name} {x : Name}
    (h : x ∈ nodes) : ((ofStatic t pred nodes).find? x).isSome := nodeIndex_isSome h

end Graph

end Planner
