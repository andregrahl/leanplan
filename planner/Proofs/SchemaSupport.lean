/-
Support for stating heuristics at the schema level.

The per-domain `Schema.lean` files replace an assumption about a heuristic's
counters with an assumption about what the domain's schemas do to the predicates,
and derive the counters.  Two shapes of counter recur and are proved here once:
a sum over a list of objects, and a maximum over one.
-/
import Proofs.Certificates

namespace Planner

/-! ### Sums written as the planner writes them -/

theorem foldl_add_eq_sum {α : Type} (f : α → Nat) :
    ∀ (l : List α) (b : Nat), l.foldl (fun acc x => acc + f x) b = b + (l.map f).sum := by
  intro l
  induction l with
  | nil => intro b; simp
  | cons x rest ih => intro b; simp [ih, Nat.add_assoc]

/-- One element's contribution falls by one, the rest are unchanged. -/
theorem sum_map_drop_one {α : Type} (l : List α) (f g : α → Nat) (x : α)
    (hx : x ∈ l) (hnd : l.Nodup) (hstep : g x + 1 = f x)
    (hrest : ∀ y ∈ l, y ≠ x → f y = g y) :
    (l.map g).sum + 1 = (l.map f).sum := by
  induction l with
  | nil => simp at hx
  | cons a rest ih =>
      rcases List.mem_cons.mp hx with rfl | hx'
      · have hnotMem : x ∉ rest := by simpa using hnd.notMem
        have hall : ∀ y ∈ rest, f y = g y := fun y hy =>
          hrest y (by simp [hy]) (by rintro rfl; exact hnotMem hy)
        have : (rest.map f).sum = (rest.map g).sum := by
          congr 1
          exact List.map_congr_left hall
        simp only [List.map_cons, List.sum_cons, this]
        omega
      · have hane : a ≠ x := by
          rintro rfl
          exact (by simpa using hnd.notMem : a ∉ rest) hx'
        have := ih hx' hnd.of_cons (fun y hy hyx => hrest y (by simp [hy]) hyx)
        simp only [List.map_cons, List.sum_cons, hrest a (by simp) hane]
        omega

/-- Every element's contribution is at most as large. -/
theorem sum_map_mono {α : Type} (l : List α) (f g : α → Nat)
    (h : ∀ y ∈ l, f y ≤ g y) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a rest ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (h a (by simp)) (ih fun y hy => h y (by simp [hy]))

/-- Every element's contribution is at most one larger, except one that may be one worse. -/
theorem sum_map_le_succ {α : Type} (l : List α) (f g : α → Nat) (x : α)
    (hnd : l.Nodup) (hstep : f x ≤ g x + 1)
    (hrest : ∀ y ∈ l, y ≠ x → f y ≤ g y) :
    (l.map f).sum ≤ (l.map g).sum + 1 := by
  induction l with
  | nil => simp
  | cons a rest ih =>
      by_cases hax : a = x
      · subst hax
        have hnotMem : a ∉ rest := by simpa using hnd.notMem
        have hall : ∀ y ∈ rest, f y ≤ g y := fun y hy =>
          hrest y (by simp [hy]) (by rintro rfl; exact hnotMem hy)
        have := sum_map_mono rest f g hall
        simp only [List.map_cons, List.sum_cons]
        omega
      · have := ih hnd.of_cons (fun y hy hyx => hrest y (by simp [hy]) hyx)
        have ha := hrest a (by simp) hax
        simp only [List.map_cons, List.sum_cons]
        omega

/-- One element's contribution is `j` smaller, and no other element's is larger. -/
theorem sum_map_add_le {α : Type} (l : List α) (f g : α → Nat) (x : α) (j : Nat)
    (hx : x ∈ l) (hnd : l.Nodup) (hstep : f x + j ≤ g x)
    (hrest : ∀ y ∈ l, y ≠ x → f y ≤ g y) :
    (l.map f).sum + j ≤ (l.map g).sum := by
  induction l with
  | nil => simp at hx
  | cons a rest ih =>
      by_cases hax : a = x
      · subst hax
        have hnotMem : a ∉ rest := by simpa using hnd.notMem
        have hall : ∀ y ∈ rest, f y ≤ g y := fun y hy =>
          hrest y (by simp [hy]) (by rintro rfl; exact hnotMem hy)
        have := sum_map_mono rest f g hall
        simp only [List.map_cons, List.sum_cons]
        omega
      · have hxr : x ∈ rest := by
          rcases List.mem_cons.mp hx with h | h
          · exact absurd h.symm hax
          · exact h
        have := ih hxr hnd.of_cons (fun y hy hyx => hrest y (by simp [hy]) hyx)
        have ha := hrest a (by simp) hax
        simp only [List.map_cons, List.sum_cons]
        omega

/-- One element's contribution shifts by `k`, the rest are unchanged. -/
theorem sum_map_shift {α : Type} (l : List α) (f g : α → Nat) (x : α) (k : Nat)
    (hx : x ∈ l) (hnd : l.Nodup) (hstep : f x + k = g x)
    (hrest : ∀ y ∈ l, y ≠ x → f y = g y) :
    (l.map f).sum + k = (l.map g).sum := by
  induction l with
  | nil => simp at hx
  | cons a rest ih =>
      by_cases hax : a = x
      · subst hax
        have hnotMem : a ∉ rest := by simpa using hnd.notMem
        have hall : ∀ y ∈ rest, f y = g y := fun y hy =>
          hrest y (by simp [hy]) (by rintro rfl; exact hnotMem hy)
        have : (rest.map f).sum = (rest.map g).sum := by
          congr 1; exact List.map_congr_left hall
        simp only [List.map_cons, List.sum_cons, this]
        omega
      · have hx' : x ∈ rest := by
          rcases List.mem_cons.mp hx with rfl | h
          · exact absurd rfl hax
          · exact h
        have := ih hx' hnd.of_cons (fun y hy hyx => hrest y (by simp [hy]) hyx)
        have ha := hrest a (by simp) hax
        simp only [List.map_cons, List.sum_cons, ha]
        omega

/-- A list with exactly one element satisfying `p` filters to that element. -/
theorem filter_eq_singleton {α : Type} (x : α) (p : α → Bool) (hpx : p x = true) :
    ∀ l : List α, x ∈ l → l.Nodup → (∀ y ∈ l, p y = true → y = x) → l.filter p = [x] := by
  intro l
  induction l with
  | nil => intro hx _ _; simp at hx
  | cons a rest ih =>
      intro hx hnd huniq
      rcases List.mem_cons.mp hx with heq | hx'
      · subst heq
        have hnotMem : x ∉ rest := by simpa using hnd.notMem
        rw [List.filter_cons, if_pos hpx]
        congr 1
        refine List.filter_eq_nil_iff.mpr fun y hy hpy => ?_
        have := huniq y (by simp [hy]) (by simpa using hpy)
        subst this
        exact hnotMem hy
      · have hane : p a = false := by
          by_contra hcon
          have hpa : p a = true := by simpa using hcon
          have heq2 := huniq a (by simp) hpa
          subst heq2
          exact (by simpa using hnd.notMem : a ∉ rest) hx'
        rw [List.filter_cons, if_neg (by simp [hane])]
        exact ih hx' hnd.of_cons (fun y hy hpy => huniq y (by simp [hy]) hpy)

/-! ### Counters that range over a filtered collection

A count over `l.filter p` is a count over `l` in which the elements `p` rejects
contribute nothing.  Written that way, the collection is the same in both states
and the "differs at one object" lemmas apply even when the filter itself moves.
-/

theorem sum_filter_eq_ite {α : Type} (l : List α) (p : α → Bool) (f : α → Nat) :
    ((l.filter p).map f).sum = (l.map fun x => if p x then f x else 0).sum := by
  induction l with
  | nil => simp
  | cons a rest ih =>
      by_cases h : p a <;> simp [List.filter_cons, h, ih]

theorem foldl_max_filter {α : Type} (l : List α) (p : α → Bool) (f : α → Nat) :
    ∀ b : Nat, (l.filter p).foldl (fun acc x => max acc (f x)) b
      = l.foldl (fun acc x => max acc (if p x then f x else 0)) b := by
  induction l with
  | nil => intro b; simp
  | cons a rest ih =>
      intro b
      by_cases h : p a <;> simp [List.filter_cons, h, ih]

/-- Two folds whose steps agree on every element agree. -/
theorem foldl_congr_mem {α : Type} {f g : Nat → α → Nat} :
    ∀ (l : List α), (∀ x ∈ l, ∀ acc, f acc x = g acc x) → ∀ b, l.foldl f b = l.foldl g b := by
  intro l
  induction l with
  | nil => intro _ b; rfl
  | cons x xs ih =>
      intro h b
      rw [List.foldl_cons, List.foldl_cons, h x (by simp) b,
        ih (fun y hy => h y (by simp [hy]))]

/-- The same for a `flatMap`. -/
theorem flatMap_congr_mem {α β : Type} {f g : α → List β} :
    ∀ (l : List α), (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x xs ih =>
      intro h
      rw [List.flatMap_cons, List.flatMap_cons, h x (by simp),
        ih (fun y hy => h y (by simp [hy]))]

/-- Two filters that agree on every element of the array give the same array. -/
theorem array_filter_congr {α : Type} (a : Array α) (p q : α → Bool)
    (h : ∀ x ∈ a, p x = q x) : a.filter p = a.filter q := by
  apply Array.toList_inj.mp
  rw [Array.toList_filter, Array.toList_filter]
  exact List.filter_congr fun x hx => h x (by simpa using hx)

/-! ### Counting the facts of an array that hold -/

/-- One fact becomes true and nothing else changes. -/
theorem countHolding_succ (facts : Array Fact) {s s' : State} (x : Fact) (hx : x ∈ facts)
    (hnd : facts.toList.Nodup) (hxs : s.test x = false) (hxs' : s'.test x = true)
    (hrest : ∀ f ∈ facts, f ≠ x → s'.test f = s.test f) :
    countHolding facts s' = countHolding facts s + 1 := by
  rw [countHolding_eq, countHolding_eq, size_filter_toList, size_filter_toList]
  refine (length_filter_erase_one _ (fun f => s'.test f) (fun f => s.test f) x
    (by simpa using hx) hnd hxs' hxs ?_).symm
  intro y hy hne
  exact hrest y (by simpa using hy) hne

theorem countHolding_congr' (facts : Array Fact) {s s' : State}
    (h : ∀ f ∈ facts, s'.test f = s.test f) :
    countHolding facts s' = countHolding facts s := by
  rw [countHolding_eq, countHolding_eq, size_filter_toList, size_filter_toList]
  exact length_filter_congr _ _ _ fun y hy => h y (by simpa using hy)

/-- One item's goal becomes true; the unmet count falls by one.  Stated over a
pair of predicates, so the lifted proofs use it too. -/
theorem unmet_size_drop' {α β : Type} (items : Array α) (key : α → β)
    {P Q : β → Bool} (x : α)
    (hx : x ∈ items) (hnd : items.toList.Nodup)
    (hxs : P (key x) = false) (hxs' : Q (key x) = true)
    (hrest : ∀ y ∈ items, y ≠ x → Q (key y) = P (key y)) :
    (items.filter fun y => !Q (key y)).size + 1
      = (items.filter fun y => !P (key y)).size := by
  rw [size_filter_toList, size_filter_toList]
  refine length_filter_erase_one _ _ _ x (by simpa using hx) hnd (by simp [hxs])
    (by simp [hxs']) ?_
  intro y hy hne
  rw [hrest y (by simpa using hy) hne]

/-- One item's goal fact becomes true; the unmet count falls by one. -/
theorem unmet_size_drop {α : Type} (items : Array α) (key : α → Fact) {s s' : State} (x : α)
    (hx : x ∈ items) (hnd : items.toList.Nodup)
    (hxs : s.test (key x) = false) (hxs' : s'.test (key x) = true)
    (hrest : ∀ y ∈ items, y ≠ x → s'.test (key y) = s.test (key y)) :
    (items.filter fun y => !s'.test (key y)).size + 1
      = (items.filter fun y => !s.test (key y)).size := by
  rw [size_filter_toList, size_filter_toList]
  refine length_filter_erase_one _ _ _ x (by simpa using hx) hnd (by simp [hxs])
    (by simp [hxs']) ?_
  intro y hy hne
  rw [hrest y (by simpa using hy) hne]

/-- A filter that keeps fewer elements gives a smaller count. -/
theorem filter_size_le {α : Type} (a : Array α) (p q : α → Bool)
    (h : ∀ x ∈ a, p x = true → q x = true) : (a.filter p).size ≤ (a.filter q).size := by
  rw [size_filter_toList, size_filter_toList]
  have key : ∀ l : List α, (∀ x ∈ l, p x = true → q x = true) →
      (l.filter p).length ≤ (l.filter q).length := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons x rest ih =>
        intro hl
        have hr := ih fun y hy => hl y (by simp [hy])
        rw [List.filter_cons, List.filter_cons]
        by_cases hp : p x
        · rw [if_pos hp, if_pos (hl x (by simp) hp)]
          simpa using hr
        · rw [if_neg (by simp [hp])]
          by_cases hq : q x
          · rw [if_pos hq]; simp; omega
          · rw [if_neg (by simp [hq])]; exact hr
  exact key a.toList fun x hx => h x (by simpa using hx)

/-- A running minimum is below every term. -/
theorem foldl_min_le_mem {α : Type} (l : List α) (f : α → Nat) {x : α} (hx : x ∈ l) :
    ∀ b : Nat, l.foldl (fun a y => min a (f y)) b ≤ f x := by
  induction l with
  | nil => simp at hx
  | cons a rest ih =>
      intro b
      rcases List.mem_cons.mp hx with rfl | hx'
      · have key : ∀ (l : List α) (c : Nat), l.foldl (fun a y => min a (f y)) c ≤ c := by
          intro l
          induction l with
          | nil => intro c; exact Nat.le_refl _
          | cons y ys ihy =>
              intro c
              exact Nat.le_trans (ihy _) (Nat.min_le_left _ _)
        exact Nat.le_trans (key rest _) (Nat.min_le_right _ _)
      · exact ih hx' _

/-- A list filter that keeps fewer elements gives a smaller count. -/
theorem filter_size_le' {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ x ∈ l, p x = true → q x = true) : (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons x rest ih =>
      have hr := ih fun y hy => h y (by simp [hy])
      rw [List.filter_cons, List.filter_cons]
      by_cases hp : p x
      · rw [if_pos hp, if_pos (h x (by simp) hp)]
        simpa using hr
      · rw [if_neg (by simp [hp])]
        by_cases hq : q x
        · rw [if_pos hq]; simp; omega
        · rw [if_neg (by simp [hq])]; exact hr

/-! ### Set counts over any type

The lifted heuristics count objects, not fact numbers, so the two shapes of set
bound are needed for an arbitrary type with decidable equality.
-/

theorem length_le_of_subset' {α : Type} [DecidableEq α] (l l' : List α)
    (hnd : l.Nodup) (h : ∀ x ∈ l, x ∈ l') : l.length ≤ l'.length :=
  (List.subperm_of_subset hnd h).length_le

/-- One element leaves a filter, and nothing else changes. -/
theorem length_filter_drop_one {α : Type} (l : List α) (P Q : α → Bool) (a : α)
    (ha : a ∈ l) (hnd : l.Nodup) (hPa : P a = true) (hQa : Q a = false)
    (h : ∀ y ∈ l, y ≠ a → P y = Q y) :
    (l.filter P).length = (l.filter Q).length + 1 := by
  induction l with
  | nil => simp at ha
  | cons z rest ih =>
      by_cases hza : z = a
      · subst hza
        have hnm : z ∉ rest := by simpa using hnd.notMem
        have hall : ∀ y ∈ rest, P y = Q y := fun y hy =>
          h y (by simp [hy]) (by rintro rfl; exact hnm hy)
        rw [List.filter_cons, List.filter_cons, List.filter_congr hall,
          if_pos hPa, if_neg (by simp [hQa])]
        simp
      · have hmem : a ∈ rest := by
          rcases List.mem_cons.mp ha with hc | hc
          · exact absurd hc.symm hza
          · exact hc
        have hrest := ih hmem hnd.of_cons fun y hy hya => h y (by simp [hy]) hya
        rw [List.filter_cons, List.filter_cons, h z (by simp) hza]
        split
        · simp only [List.length_cons]; omega
        · omega

/-! ### Two lists in step

`Forall₂` is how a compiled table is paired with the objects a `Cfg` names.
These four are what every such pairing needs.
-/

theorem forall₂_mem_left {α β : Type} {R : α → β → Prop} {l : List α} {m : List β}
    (h : List.Forall₂ R l m) {a : α} (ha : a ∈ l) : ∃ b ∈ m, R a b := by
  induction h with
  | nil => simp at ha
  | @cons x y rest1 rest2 hxy _ ih =>
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact ⟨y, List.mem_cons_self .., hxy⟩
      · obtain ⟨b, hb, hR⟩ := ih ha'
        exact ⟨b, List.mem_cons_of_mem _ hb, hR⟩

theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} {l : List α} {m : List β}
    (h : List.Forall₂ R l m) {b : β} (hb : b ∈ m) : ∃ a ∈ l, R a b := by
  induction h with
  | nil => simp at hb
  | @cons x y rest1 rest2 hxy _ ih =>
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact ⟨x, List.mem_cons_self .., hxy⟩
      · obtain ⟨a, ha, hR⟩ := ih hb'
        exact ⟨a, List.mem_cons_of_mem _ ha, hR⟩

theorem forall₂_any {α β : Type} {R : α → β → Prop} {P : α → Bool} {Q : β → Bool}
    {l : List α} {m : List β} (h : List.Forall₂ R l m)
    (hpq : ∀ a b, R a b → P a = Q b) : l.any P = m.any Q := by
  induction h with
  | nil => rfl
  | @cons x y rest1 rest2 hxy _ ih => simp only [List.any_cons, hpq x y hxy, ih]

theorem forall₂_map_sum {α β : Type} {R : α → β → Prop} {l : List α} {m : List β}
    (h : List.Forall₂ R l m) (f : α → Nat) (g : β → Nat)
    (hfg : ∀ a b, R a b → f a = g b) : (l.map f).sum = (m.map g).sum := by
  induction h with
  | nil => rfl
  | @cons x y rest1 rest2 hxy _ ih =>
      simp only [List.map_cons, List.sum_cons, hfg x y hxy, ih]

/-- An `any` over a list paired with its indices asks only about the elements. -/
theorem any_zipIdx {α : Type} (P : α → Bool) :
    ∀ (l : List α) (n : Nat), (l.zipIdx n).any (fun x => P x.1) = l.any P := by
  intro l
  induction l with
  | nil => intro n; rfl
  | cons a rest ih => intro n; simp only [List.zipIdx_cons, List.any_cons, ih]

/-- Two `filterMap`s that keep the same entries pair up.  This is how a compiled
table built by `filterMap` is matched against the lifted list built the same way. -/
theorem forall₂_filterMap {α β γ : Type} {R : β → γ → Prop}
    {f : α → Option β} {g : α → Option γ} :
    ∀ (l : List α), (∀ x ∈ l, (∀ b, f x = some b → ∃ c, g x = some c ∧ R b c) ∧
      (f x = none → g x = none)) →
    List.Forall₂ R (l.filterMap f) (l.filterMap g) := by
  intro l
  induction l with
  | nil => intro _; exact List.Forall₂.nil
  | cons x xs ih =>
      intro h
      obtain ⟨hsome, hnone⟩ := h x (by simp)
      have hrest := ih (fun y hy => h y (by simp [hy]))
      rcases hf : f x with _ | b
      · rw [List.filterMap_cons_none hf, List.filterMap_cons_none (hnone hf)]
        exact hrest
      · obtain ⟨c, hg, hR⟩ := hsome b hf
        rw [List.filterMap_cons_some hf, List.filterMap_cons_some hg]
        exact List.Forall₂.cons hR hrest

/-- A `filterMap` that never fails pairs with the list it ran over.  This is how a
compiled table built by looking each object up is matched against that object
list. -/
theorem forall₂_filterMap_total {α β : Type} {R : β → α → Prop} {g : α → Option β} :
    ∀ (l : List α), (∀ x ∈ l, ∃ b, g x = some b ∧ R b x) →
      List.Forall₂ R (l.filterMap g) l := by
  intro l
  induction l with
  | nil => intro _; exact List.Forall₂.nil
  | cons x xs ih =>
      intro h
      obtain ⟨b, hb, hR⟩ := h x (by simp)
      rw [List.filterMap_cons_some hb]
      exact List.Forall₂.cons hR (ih fun y hy => h y (by simp [hy]))

/-- A table built by mapping over a list pairs with that list. -/
theorem forall₂_map_left {α β : Type} {R : β → α → Prop} {f : α → β} :
    ∀ (l : List α), (∀ x ∈ l, R (f x) x) → List.Forall₂ R (l.map f) l := by
  intro l
  induction l with
  | nil => intro _; exact List.Forall₂.nil
  | cons x xs ih =>
      intro h
      exact List.Forall₂.cons (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

/-- The mirror: the lifted side is a map of the compiled one. -/
theorem forall₂_map_right {α β : Type} {R : α → β → Prop} {f : α → β} :
    ∀ (l : List α), (∀ x ∈ l, R x (f x)) → List.Forall₂ R l (l.map f) := by
  intro l
  induction l with
  | nil => intro _; exact List.Forall₂.nil
  | cons x xs ih =>
      intro h
      exact List.Forall₂.cons (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

/-- The same, when the compiled side is indexed by position. -/
theorem forall₂_map_zipIdx {α β : Type} {R : β × Nat → α → Prop} {f : α → β} :
    ∀ (l : List α) (n : Nat),
      (∀ i, (h : i < l.length) → R (f l[i], n + i) l[i]) →
      List.Forall₂ R ((l.map f).zipIdx n) l := by
  intro l
  induction l with
  | nil => intro _ _; exact List.Forall₂.nil
  | cons x xs ih =>
      intro n h
      rw [List.map_cons, List.zipIdx_cons]
      refine List.Forall₂.cons (by simpa using h 0 (by simp)) (ih (n + 1) ?_)
      intro i hi
      have := h (i + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem forall₂_filter {α β : Type} {R : α → β → Prop} {P : α → Bool} {Q : β → Bool}
    {l : List α} {m : List β} (h : List.Forall₂ R l m)
    (hpq : ∀ a b, R a b → P a = Q b) :
    List.Forall₂ R (l.filter P) (m.filter Q) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons x y rest1 rest2 hxy _ ih =>
      rw [List.filter_cons, List.filter_cons, hpq x y hxy]
      by_cases hq : Q y
      · rw [if_pos hq, if_pos hq]; exact List.Forall₂.cons hxy ih
      · rw [if_neg hq, if_neg hq]; exact ih

/-- Two paired lists filtered and mapped by pointwise-equal functions agree. -/
theorem forall₂_filterMap_eq {α β γ : Type} {R : α → β → Prop} {f : α → Option γ}
    {g : β → Option γ} {l : List α} {m : List β} (h : List.Forall₂ R l m)
    (hfg : ∀ a b, R a b → f a = g b) : l.filterMap f = m.filterMap g := by
  induction h with
  | nil => rfl
  | @cons x y rest1 rest2 hxy _ ih =>
      rw [List.filterMap_cons, List.filterMap_cons, hfg x y hxy, ih]

theorem forall₂_map_eq {α β γ : Type} {R : α → β → Prop} {f : α → γ} {g : β → γ}
    {l : List α} {m : List β} (h : List.Forall₂ R l m)
    (hfg : ∀ a b, R a b → f a = g b) : l.map f = m.map g := by
  induction h with
  | nil => rfl
  | @cons x y rest1 rest2 hxy _ ih =>
      rw [List.map_cons, List.map_cons, hfg x y hxy, ih]

/-- Pairing survives numbering the entries. -/
theorem forall₂_zipIdx {α β : Type} {R : α → β → Prop} {l : List α} {m : List β}
    (h : List.Forall₂ R l m) :
    ∀ n : Nat, List.Forall₂ (fun x y => R x.1 y.1 ∧ x.2 = y.2) (l.zipIdx n) (m.zipIdx n) := by
  induction h with
  | nil => intro n; exact List.Forall₂.nil
  | @cons x y rest1 rest2 hxy _ ih =>
      intro n
      rw [List.zipIdx_cons, List.zipIdx_cons]
      exact List.Forall₂.cons ⟨hxy, rfl⟩ (ih (n + 1))

theorem forall₂_getLast? {α β : Type} {R : α → β → Prop} {l : List α} {m : List β}
    (h : List.Forall₂ R l m) :
    (l.getLast? = none ∧ m.getLast? = none) ∨
      ∃ a b, l.getLast? = some a ∧ m.getLast? = some b ∧ R a b := by
  induction h with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | @cons x y rest1 rest2 hxy hrest ih =>
      rw [List.getLast?_cons, List.getLast?_cons]
      rcases ih with ⟨h1, h2⟩ | ⟨a, b, h1, h2, hR⟩
      · exact Or.inr ⟨x, y, by rw [h1]; rfl, by rw [h2]; rfl, hxy⟩
      · exact Or.inr ⟨a, b, by rw [h1]; rfl, by rw [h2]; rfl, hR⟩


/-- A filter that admits less is no longer. -/
theorem length_filter_mono {α : Type} (l : List α) (P Q : α → Bool)
    (h : ∀ y ∈ l, P y = true → Q y = true) :
    (l.filter P).length ≤ (l.filter Q).length := by
  induction l with
  | nil => simp
  | cons z rest ih =>
      have hrest := ih fun y hy => h y (by simp [hy])
      rw [List.filter_cons, List.filter_cons]
      by_cases hp : P z
      · rw [if_pos hp, if_pos (h z (by simp) hp)]; simpa using hrest
      · rw [if_neg (by simpa using hp)]
        split
        · simp; omega
        · exact hrest

/-- Two filters that never both fire count their union. -/
theorem length_filter_add_or {α : Type} (l : List α) (P Q : α → Bool)
    (h : ∀ y ∈ l, P y = true → Q y = false) :
    (l.filter P).length + (l.filter Q).length
      = (l.filter fun y => P y || Q y).length := by
  induction l with
  | nil => simp
  | cons z rest ih =>
      have hrest := ih fun y hy => h y (by simp [hy])
      rw [List.filter_cons, List.filter_cons, List.filter_cons]
      by_cases hp : P z
      · rw [if_pos hp, if_neg (by rw [h z (by simp) hp]; simp), if_pos (by simp [hp])]
        simp only [List.length_cons]
        omega
      · rw [if_neg (by simpa using hp)]
        by_cases hq : Q z
        · rw [if_pos hq, if_pos (by simp [hq])]
          simp only [List.length_cons]
          omega
        · rw [if_neg (by simpa using hq), if_neg (by simp [hp, hq])]
          exact hrest

/-- A sum over a filtered list shrinks when the filter does. -/
theorem sum_filter_mono {α : Type} (l : List α) (P Q : α → Bool) (f : α → Nat)
    (h : ∀ y ∈ l, P y = true → Q y = true) :
    ((l.filter P).map f).sum ≤ ((l.filter Q).map f).sum := by
  induction l with
  | nil => simp
  | cons z rest ih =>
      have hrest := ih fun y hy => h y (by simp [hy])
      rw [List.filter_cons, List.filter_cons]
      by_cases hp : P z
      · rw [if_pos hp, if_pos (h z (by simp) hp)]
        simp only [List.map_cons, List.sum_cons]
        omega
      · rw [if_neg (by simpa using hp)]
        split
        · simp only [List.map_cons, List.sum_cons]
          omega
        · exact hrest

/-- Two filters that differ at one element differ in length by at most one. -/
theorem length_filter_le_succ {α : Type} (l : List α) (P Q : α → Bool) (a : α)
    (hnd : l.Nodup) (h : ∀ y ∈ l, y ≠ a → P y = Q y) :
    (l.filter P).length ≤ (l.filter Q).length + 1 := by
  induction l with
  | nil => simp
  | cons z rest ih =>
      by_cases hza : z = a
      · subst hza
        have hnm : z ∉ rest := by simpa using hnd.notMem
        have hall : ∀ y ∈ rest, P y = Q y := fun y hy =>
          h y (by simp [hy]) (by rintro rfl; exact hnm hy)
        have : (rest.filter P) = (rest.filter Q) := List.filter_congr hall
        rw [List.filter_cons, List.filter_cons, this]
        split <;> split <;> simp <;> omega
      · have hrest := ih hnd.of_cons (fun y hy hya => h y (by simp [hy]) hya)
        rw [List.filter_cons, List.filter_cons, h z (by simp) hza]
        split <;> simp <;> omega

/-- A filter can lose at most one element when, away from that element,
everything selected before is still selected afterwards. -/
theorem length_filter_le_succ_mono {α : Type} (l : List α) (P Q : α → Bool) (a : α)
    (hnd : l.Nodup) (h : ∀ y ∈ l, y ≠ a → P y = true → Q y = true) :
    (l.filter P).length ≤ (l.filter Q).length + 1 := by
  induction l with
  | nil => simp
  | cons z rest ih =>
      by_cases hza : z = a
      · subst hza
        have hnm : z ∉ rest := by simpa using hnd.notMem
        have hrest : (rest.filter P).length ≤ (rest.filter Q).length :=
          length_filter_mono rest P Q fun y hy =>
            h y (by simp [hy]) (by rintro rfl; exact hnm hy)
        rw [List.filter_cons, List.filter_cons]
        split <;> split <;> simp_all <;> omega
      · have hrest := ih hnd.of_cons fun y hy hya => h y (by simp [hy]) hya
        rw [List.filter_cons, List.filter_cons]
        by_cases hp : P z = true
        · rw [if_pos hp, if_pos (h z (by simp) hza hp)]
          simp only [List.length_cons]
          omega
        · rw [if_neg (by simpa using hp)]
          split <;> simp_all <;> omega

/-- Nodup lists whose members correspond under an injective map have equal length. -/
theorem length_eq_of_naming {α β : Type} [DecidableEq α] [DecidableEq β]
    (l : List α) (m : List β) (f : α → β)
    (hl : l.Nodup) (hm : m.Nodup)
    (hinj : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y)
    (hinto : ∀ x ∈ l, f x ∈ m) (honto : ∀ y ∈ m, ∃ x ∈ l, f x = y) :
    l.length = m.length := by
  have hmapnd : (l.map f).Nodup := by
    rw [List.nodup_map_iff_inj_on hl]
    exact hinj
  have h1 : (l.map f).length ≤ m.length :=
    length_le_of_subset' _ _ hmapnd (by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      exact hinto x hx)
  have h2 : m.length ≤ (l.map f).length :=
    length_le_of_subset' _ _ hm (by
      intro y hy
      obtain ⟨x, hx, hfx⟩ := honto y hy
      exact List.mem_map.mpr ⟨x, hx, hfx⟩)
  rw [List.length_map] at h1 h2
  omega

theorem length_le_succ_of_subset' {α : Type} [DecidableEq α] (l l' : List α) (a : α)
    (hnd : l.Nodup) (h : ∀ x ∈ l, x ∈ l' ∨ x = a) : l.length ≤ l'.length + 1 := by
  have hsub : ∀ x ∈ l, x ∈ a :: l' := by
    intro x hx
    rcases h x hx with h1 | rfl
    · exact List.mem_cons_of_mem _ h1
    · exact List.mem_cons_self ..
  have := length_le_of_subset' l (a :: l') hnd hsub
  simpa [Nat.add_comm] using this

/-- Deduplication commutes with a map that is injective on the list. -/
theorem dedup_map_injOn {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β) :
    ∀ (l : List α), (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) →
      (l.map f).dedup = l.dedup.map f := by
  intro l
  induction l with
  | nil => simp
  | cons a rest ih =>
      intro hinj
      have hrest := ih fun x hx y hy => hinj x (by simp [hx]) y (by simp [hy])
      by_cases ha : a ∈ rest
      · have hfa : f a ∈ rest.map f := List.mem_map.mpr ⟨a, ha, rfl⟩
        rw [List.map_cons, List.dedup_cons_of_mem hfa, List.dedup_cons_of_mem ha, hrest]
      · have hfa : f a ∉ rest.map f := by
          intro hmem
          obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hmem
          exact ha (hinj a (by simp) y (by simp [hy]) hfy.symm ▸ hy)
        rw [List.map_cons, List.dedup_cons_of_notMem hfa,
          List.dedup_cons_of_notMem ha, hrest, List.map_cons]

end Planner
