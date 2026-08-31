/-
What the bucket open list guarantees.

Only four facts are needed above this file, and they are exactly the ones A\*'s
optimality argument uses:

  * pushing keeps everything that was there and adds the new entry;
  * popping returns an entry that *was* there;
  * the entry it returns has minimal `f` among everything there — this is the
    one that matters, and the bucket layout makes it structural rather than an
    invariant about a heap;
  * popping keeps every other entry.

`Mem` says where an entry lives: its node index sits in the stack at
`buckets[f][h]`.  `WF` records the one invariant the structure maintains, that
`minF` really is a lower bound on the keys present, which is what lets `pop?`
start its scan there instead of at zero.
-/
import Proofs.Combinators
import Planner.Search.OpenList

namespace Planner

namespace OpenList

/-- `e` is in the open list when its node sits in the stack at `buckets[e.f][e.h]`. -/
def Mem (q : OpenList) (e : Entry) : Prop :=
  e.node ∈ (q.buckets.getD e.f #[]).getD e.h #[]

/--
The one invariant the structure maintains: `minF` really is a lower bound on the
keys present, which is what lets `pop?` start its scan there instead of at zero.
-/
structure WF (q : OpenList) : Prop where
  minF : ∀ e, q.Mem e → q.minF ≤ e.f

/-! ### Reading nested arrays after a write -/

theorem getD_modify_self {α : Type} (a : Array α) (i : Nat) (f : α → α) (d : α)
    (hi : i < a.size) : (a.modify i f).getD i d = f (a.getD i d) := by
  simp [Array.getD_eq_getD_getElem?, hi, Array.size_modify, Array.getElem_modify]

theorem getD_modify_ne {α : Type} (a : Array α) (i j : Nat) (f : α → α) (d : α)
    (hij : i ≠ j) : (a.modify i f).getD j d = a.getD j d := by
  by_cases hj : j < a.size
  · simp [Array.getD_eq_getD_getElem?, hj, Array.size_modify, Array.getElem_modify, hij]
  · simp [Array.getD_eq_getD_getElem?, Array.size_modify, hj]

theorem getD_widen {α : Type} (a : Array α) (i j : Nat) (pad : α) :
    (widen a i pad).getD j pad = a.getD j pad := by
  simp only [widen]
  split
  · rfl
  · rename_i h
    by_cases hj : j < a.size
    · simp [Array.getD_eq_getD_getElem?, hj, Array.getElem?_append]
    · by_cases hj' : j < a.size + (i + 1 - a.size)
      · rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
        rw [Array.getElem?_eq_getElem (by simp; omega)]
        rw [Array.getElem?_eq_none_iff.mpr (by omega)]
        simp [Array.getElem_append, hj]
      · rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
        rw [Array.getElem?_eq_none_iff.mpr (by simp; omega)]
        rw [Array.getElem?_eq_none_iff.mpr (by omega)]

theorem lt_size_widen {α : Type} (a : Array α) (i : Nat) (pad : α) :
    i < (widen a i pad).size := by
  simp only [widen]
  split
  · assumption
  · simp only [Array.size_append, Array.size_replicate]
    omega

/-! ### Pushing -/

theorem push_mem_self (q : OpenList) (e : Entry) : (q.push e).Mem e := by
  have hf : e.f < (widen q.buckets e.f #[]).size := lt_size_widen _ _ _
  have hh : e.h < (widen ((widen q.buckets e.f #[]).getD e.f #[]) e.h #[]).size :=
    lt_size_widen _ _ _
  simp only [Mem, push, getD_modify_self _ _ _ _ hf, getD_modify_self _ _ _ _ hh]
  simp

theorem push_mem (q : OpenList) (e x : Entry) (h : q.Mem x) : (q.push e).Mem x := by
  simp only [Mem, push] at h ⊢
  by_cases hf : e.f = x.f
  · rw [← hf] at h ⊢
    have hfsize : e.f < (widen q.buckets e.f #[]).size := lt_size_widen _ _ _
    rw [getD_modify_self _ _ _ _ hfsize, getD_widen]
    by_cases hh : e.h = x.h
    · rw [← hh] at h ⊢
      have hhsize : e.h < (widen (q.buckets.getD e.f #[]) e.h #[]).size := lt_size_widen _ _ _
      rw [getD_modify_self _ _ _ _ hhsize, getD_widen]
      simpa using Array.mem_push_of_mem _ h
    · rw [getD_modify_ne _ _ _ _ _ hh, getD_widen]
      exact h
  · rw [getD_modify_ne _ _ _ _ _ hf, getD_widen]
    exact h

/-- Everything present after a push was present before, or is the pushed entry. -/
theorem mem_push {q : OpenList} {e x : Entry} (hx : (q.push e).Mem x) :
    q.Mem x ∨ (x.f = e.f ∧ x.h = e.h ∧ x.node = e.node) := by
  simp only [Mem, push] at hx
  simp only [Mem]
  by_cases hf : e.f = x.f
  · rw [← hf] at hx ⊢
    have hfsize : e.f < (widen q.buckets e.f #[]).size := lt_size_widen _ _ _
    rw [getD_modify_self _ _ _ _ hfsize, getD_widen] at hx
    by_cases hh : e.h = x.h
    · rw [← hh] at hx ⊢
      have hhsize : e.h < (widen (q.buckets.getD e.f #[]) e.h #[]).size := lt_size_widen _ _ _
      rw [getD_modify_self _ _ _ _ hhsize, getD_widen] at hx
      rcases Array.mem_push.mp hx with h | h
      · exact Or.inl h
      · exact Or.inr ⟨rfl, rfl, h⟩
    · rw [getD_modify_ne _ _ _ _ _ hh, getD_widen] at hx
      exact Or.inl hx
  · rw [getD_modify_ne _ _ _ _ _ hf, getD_widen] at hx
    exact Or.inl hx

theorem push_wf {q : OpenList} (hq : WF q) (e : Entry) : WF (q.push e) := by
  refine ⟨?_⟩
  intro x hx
  simp only [push]
  rcases mem_push hx with hprev | ⟨hf, -, -⟩
  · have := hq.minF x hprev; omega
  · omega

/-! ### Popping -/

/-- Nothing is on the empty list. -/
theorem not_mem_empty (e : Entry) : ¬ empty.Mem e := by
  simp [Mem, empty]

theorem empty_wf : WF empty := ⟨fun e he => absurd he (not_mem_empty e)⟩

/-- Every stack of bucket `i` is empty. -/
def BucketEmpty (bs : Array (Array (Array Nat))) (i : Nat) : Prop :=
  ∀ h, (bs.getD i #[]).getD h #[] = #[]

theorem getD_eq_getElem {α : Type} (a : Array α) (k : Nat) (d : α) (hk : k < a.size) :
    a.getD k d = a[k] := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk]
  rfl

theorem getD_of_size_le {α : Type} (a : Array α) (k : Nat) (d : α) (hk : a.size ≤ k) :
    a.getD k d = d := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none_iff.mpr hk]
  rfl

theorem bucketEmpty_of_none {bs : Array (Array (Array Nat))} {i : Nat}
    (h : ((bs.getD i #[]).any fun row => !row.isEmpty) = false) : BucketEmpty bs i := by
  intro k
  by_cases hk : k < (bs.getD i #[]).size
  · rw [getD_eq_getElem _ _ _ hk]
    have hval := (Array.any_eq_false.mp h) k hk
    simpa [Array.isEmpty_iff] using hval
  · exact getD_of_size_le _ _ _ (by omega)

theorem bucketEmpty_of_size {bs : Array (Array (Array Nat))} {i : Nat} (h : bs.size ≤ i) :
    BucketEmpty bs i := by
  intro k
  rw [getD_of_size_le _ _ _ h]
  rfl

/-- Everything the scan skipped over really was empty. -/
theorem firstNonEmpty_spec {bs : Array (Array (Array Nat))} :
    ∀ (fuel start f : Nat), firstNonEmpty bs start fuel = some f →
      start ≤ f ∧ ((bs.getD f #[]).any fun row => !row.isEmpty) = true ∧
        ∀ i, start ≤ i → i < f → BucketEmpty bs i := by
  intro fuel
  induction fuel with
  | zero => intro start f h; simp [firstNonEmpty] at h
  | succ fuel ih =>
      intro start f h
      rw [firstNonEmpty] at h
      split at h
      · simp at h
      · split at h
        · rename_i hne
          simp only [Option.some.injEq] at h
          subst h
          exact ⟨Nat.le_refl _, by simpa using hne, fun i hi hlt => absurd hlt (by omega)⟩
        · rename_i hempty
          obtain ⟨hle, hany, hall⟩ := ih (start + 1) f h
          refine ⟨by omega, hany, ?_⟩
          intro i hi hlt
          by_cases hstart : i = start
          · subst hstart
            exact bucketEmpty_of_none (by simpa using hempty)
          · exact hall i (by omega) hlt

/-- If the scan found nothing, nothing was there. -/
theorem firstNonEmpty_none {bs : Array (Array (Array Nat))} :
    ∀ (fuel start : Nat), bs.size ≤ start + fuel →
      firstNonEmpty bs start fuel = none → ∀ i, start ≤ i → BucketEmpty bs i := by
  intro fuel
  induction fuel with
  | zero =>
      intro start hsize _ i hi
      exact bucketEmpty_of_size (by omega)
  | succ fuel ih =>
      intro start hsize h i hi
      rw [firstNonEmpty] at h
      split at h
      · rename_i hge
        exact bucketEmpty_of_size (by omega)
      · rename_i hlt
        split at h
        · simp at h
        · rename_i hempty
          by_cases hstart : i = start
          · subst hstart
            exact bucketEmpty_of_none (by simpa using hempty)
          · exact ih (start + 1) (by omega) h i (by omega)

/-- The row scan lands on a stack that really has something in it. -/
theorem firstNonEmptyRow_spec {row : Array (Array Nat)} :
    ∀ (fuel start h : Nat), firstNonEmptyRow row start fuel = some h →
      (row.getD h #[]) ≠ #[] := by
  intro fuel
  induction fuel with
  | zero => intro start h hh; simp [firstNonEmptyRow] at hh
  | succ fuel ih =>
      intro start h hh
      rw [firstNonEmptyRow] at hh
      split at hh
      · simp at hh
      · split at hh
        · exact ih (start + 1) h hh
        · rename_i hne
          simp only [Option.some.injEq] at hh
          subst hh
          simpa [Array.isEmpty_iff] using hne

/-- If the row scan found nothing, every stack from `start` on is empty. -/
theorem firstNonEmptyRow_none {row : Array (Array Nat)} :
    ∀ (fuel start : Nat), row.size ≤ start + fuel →
      firstNonEmptyRow row start fuel = none → ∀ i, start ≤ i → row.getD i #[] = #[] := by
  intro fuel
  induction fuel with
  | zero =>
      intro start hsize _ i hi
      exact getD_of_size_le _ _ _ (by omega)
  | succ fuel ih =>
      intro start hsize h i hi
      rw [firstNonEmptyRow] at h
      split at h
      · rename_i hge
        exact getD_of_size_le _ _ _ (by omega)
      · split at h
        · rename_i hempty
          by_cases hstart : i = start
          · subst hstart
            simpa [Array.isEmpty_iff] using hempty
          · exact ih (start + 1) (by omega) h i (by omega)
        · simp at h

/-! ### What `pop?` returns -/

/--
The facts A\* needs about a pop: the entry was there, it has minimal `f`, and
everything else is still there.
-/
theorem pop?_spec {q : OpenList} (hq : WF q) {e : Entry} {q' : OpenList}
    (h : q.pop? = some (e, q')) :
    q.Mem e ∧ (∀ x, q.Mem x → e.f ≤ x.f) ∧
      (∀ x, q.Mem x → x.node ≠ e.node → q'.Mem x) ∧ WF q' := by
  simp only [pop?] at h
  split at h
  · simp at h
  · rename_i f hfind
    obtain ⟨hle, -, hskip⟩ := firstNonEmpty_spec _ _ _ hfind
    split at h
    · simp at h
    · rename_i hrow hrowfind
      have hstack : (q.buckets.getD f #[]).getD hrow #[] ≠ #[] :=
        firstNonEmptyRow_spec _ _ _ hrowfind
      -- Both indices are in range, or the stack would be the empty default.
      have hfsize : f < q.buckets.size := by
        by_contra hc
        exact hstack (by rw [getD_of_size_le _ _ _ (Nat.not_lt.mp hc)]; rfl)
      have hhsize : hrow < (q.buckets.getD f #[]).size := by
        by_contra hc
        exact hstack (getD_of_size_le _ _ _ (Nat.not_lt.mp hc))
      split at h
      · simp at h
      · rename_i node hback
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨he, hq'⟩ := h
        subst he
        subst hq'
        -- The popped node is the last element of its stack.
        obtain ⟨rest, hrest⟩ := Array.back?_eq_some_iff.mp hback
        have hlast : ((q.buckets.getD f #[]).getD hrow #[]).toList
            = (((q.buckets.getD f #[]).getD hrow #[]).pop).toList ++ [node] := by
          rw [hrest]; simp
        -- Anything present outside bucket `f` between `minF` and `f` is impossible.
        have hnotbelow : ∀ x, q.Mem x → f ≤ x.f := by
          intro x hx
          by_contra hlt
          have hxf : q.minF ≤ x.f := hq.minF x hx
          have hempty := hskip x.f hxf (by omega) x.h
          simp only [Mem, hempty] at hx
          simp at hx
        refine ⟨?_, ?_, ?_, ?_⟩
        · show node ∈ (q.buckets.getD f #[]).getD hrow #[]
          have : node ∈ ((q.buckets.getD f #[]).getD hrow #[]).toList := by
            rw [hlast]; simp
          simpa using this
        · intro x hx
          show f ≤ x.f
          exact hnotbelow x hx
        · intro x hx hne
          simp only [Mem] at hx ⊢
          by_cases hf : f = x.f
          · subst hf
            rw [getD_modify_self _ _ _ _ hfsize]
            by_cases hh : hrow = x.h
            · subst hh
              rw [getD_modify_self _ _ _ _ hhsize]
              have hin : x.node ∈ ((q.buckets.getD x.f #[]).getD x.h #[]).toList := by
                simpa using hx
              rw [hlast] at hin
              rcases List.mem_append.mp hin with hmem | hmem
              · exact Array.mem_def.mpr hmem
              · simp only [List.mem_singleton] at hmem
                exact absurd hmem hne
            · rw [getD_modify_ne _ _ _ _ _ hh]; exact hx
          · rw [getD_modify_ne _ _ _ _ _ hf]; exact hx
        · refine ⟨?_⟩
          intro x hx
          have hprev : q.Mem x := by
            simp only [Mem] at hx ⊢
            by_cases hf : f = x.f
            · subst hf
              rw [getD_modify_self _ _ _ _ hfsize] at hx
              by_cases hh : hrow = x.h
              · subst hh
                rw [getD_modify_self _ _ _ _ hhsize] at hx
                have h1 := Array.mem_def.mp hx
                have h2 := List.mem_append_left [node] h1
                rw [← hlast] at h2
                exact Array.mem_def.mpr h2
              · rw [getD_modify_ne _ _ _ _ _ hh] at hx; exact hx
            · rw [getD_modify_ne _ _ _ _ _ hf] at hx; exact hx
          exact hnotbelow x hprev

/-- Nothing is in an open list that `pop?` reports as exhausted. -/
private theorem mem_of_mem_pop {α : Type} {a : Array α} {x : α} (h : x ∈ a.pop) : x ∈ a := by
  rcases Array.getElem_of_mem h with ⟨i, hi, hix⟩
  have hi' : i < a.size := by simp [Array.size_pop] at hi; omega
  have hx : a[i] = x := by rw [← hix]; simp [Array.getElem_pop]
  exact hx ▸ Array.getElem_mem hi'

private theorem getD_modify_self_ge {α : Type} (a : Array α) (i : Nat) (f : α → α) (d : α)
    (hi : ¬ i < a.size) : (a.modify i f).getD i d = d := by
  simp [Array.getD_eq_getD_getElem?, Array.size_modify, hi]

/--
Popping only ever removes.  Whatever is still on the list afterwards was on it
before, which is what lets an invariant about every open entry survive a pop.
-/
theorem pop?_mem_mono {q : OpenList} {e : Entry} {q' : OpenList}
    (h : q.pop? = some (e, q')) : ∀ x, q'.Mem x → q.Mem x := by
  simp only [pop?] at h
  split at h
  · simp at h
  · rename_i f hfind
    split at h
    · simp at h
    · rename_i hrow hrowfind
      split at h
      · simp at h
      · rename_i nd hback
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, hq'⟩ := h
        intro x hx
        rw [← hq'] at hx
        simp only [Mem] at hx ⊢
        by_cases hf : f = x.f
        · rw [← hf] at hx ⊢
          by_cases hsize : f < q.buckets.size
          · rw [getD_modify_self _ _ _ _ hsize] at hx
            by_cases hh : hrow = x.h
            · rw [← hh] at hx ⊢
              by_cases hsize' : hrow < (q.buckets.getD f #[]).size
              · rw [getD_modify_self _ _ _ _ hsize'] at hx
                exact mem_of_mem_pop hx
              · rw [getD_modify_self_ge _ _ _ _ hsize'] at hx
                simp at hx
            · rw [getD_modify_ne _ _ _ _ _ hh] at hx
              exact hx
          · rw [getD_modify_self_ge _ _ _ _ hsize] at hx
            simp at hx
        · rw [getD_modify_ne _ _ _ _ _ hf] at hx
          exact hx

theorem pop?_none {q : OpenList} (hq : WF q) (h : q.pop? = none) : ∀ e, ¬ q.Mem e := by
  intro e he
  simp only [pop?] at h
  split at h
  · rename_i hfind
    have hall := firstNonEmpty_none _ q.minF (by omega) hfind e.f (hq.minF e he)
    simp only [Mem, hall e.h] at he
    simp at he
  · rename_i f hfind
    obtain ⟨-, hany, -⟩ := firstNonEmpty_spec _ _ _ hfind
    -- The bucket the scan stopped at holds a non-empty stack, so the row scan
    -- and `back?` below it cannot both come up empty.
    obtain ⟨k, hk, hkne⟩ := Array.any_eq_true.mp hany
    split at h
    · rename_i hrowfind
      have hempty := firstNonEmptyRow_none _ 0 (by omega) hrowfind k (Nat.zero_le _)
      rw [getD_eq_getElem _ _ _ hk] at hempty
      simp only [Array.getD_eq_getD_getElem?] at hempty hkne
      rw [hempty] at hkne
      simp at hkne
    · rename_i hrow hrowfind
      have hstack : (q.buckets.getD f #[]).getD hrow #[] ≠ #[] :=
        firstNonEmptyRow_spec _ _ _ hrowfind
      split at h
      · rename_i hback
        rw [Array.back?_eq_none_iff] at hback
        exact hstack hback
      · simp at h

end OpenList

end Planner
