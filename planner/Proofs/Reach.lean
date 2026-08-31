/-
What the walk over a graph reaches.

Two facts are needed of it, and a value that cuts a subtree needs both.

  * It reaches nothing outside the least set that holds the start squares and is
    closed under the edges it may enter.  That is what says a square it does not
    mark is one no robot can walk to.
  * It is itself closed under those edges.  That is what says the region only
    ever shrinks as squares stop being enterable.
-/
import Proofs.Certificates

namespace Planner.Reach

variable {adj : Array (Array Nat)} {enterable : Nat → Bool}

theorem getD_setIfInBounds_true {s : Array Bool} {q p : Nat}
    (h : (s.setIfInBounds q true).getD p false = true) : p = q ∨ s.getD p false = true := by
  by_cases hpq : p = q
  · exact Or.inl hpq
  refine Or.inr ?_
  by_cases hp : p < s.size
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hp]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hp)] at h
    simp only [Option.getD_some] at h ⊢
    rw [Array.getElem_setIfInBounds] at h
    rcases (by simpa using h : q = p ∨ s[p] = true) with hc | hc
    · exact absurd hc.symm hpq
    · exact hc
  · exfalso
    rw [Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none (by simpa using Nat.le_of_not_lt hp)] at h
    simp at h

theorem getD_setIfInBounds_self {s : Array Bool} {q : Nat} (h : q < s.size) :
    (s.setIfInBounds q true).getD q false = true := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using h)]
  simp

theorem getD_setIfInBounds_mono {s : Array Bool} {q p : Nat}
    (h : s.getD p false = true) : (s.setIfInBounds q true).getD p false = true := by
  have hp0 : p < s.size := by
    rcases Nat.lt_or_ge p s.size with hlt | hge
    · exact hlt
    · exfalso
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simpa using hge)] at h
      simp at h
  by_cases hpq : p = q
  · rw [hpq]
    exact getD_setIfInBounds_self (by rw [← hpq]; exact hp0)
  · have hp : p < s.size := hp0
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hp)]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hp] at h
    simp only [Option.getD_some] at h ⊢
    rw [Array.getElem_setIfInBounds, if_neg (fun hc : q = p => hpq hc.symm)]
    exact h

/-! ### The walk stays inside any closed set -/

/-- Everything the walk has marked or queued satisfies `Q`. -/
structure Holds (Q : Nat → Prop) (n : Nat) (seen : Array Bool) (queue : Array Nat) : Prop where
  size : seen.size = n
  marked : ∀ p, seen.getD p false = true → Q p
  queued : ∀ v ∈ queue, Q v

theorem push_holds {Q : Nat → Prop} {n : Nat} {seen : Array Bool} {queue : Array Nat}
    {v : Nat} (h : Holds Q n seen queue) (hv : enterable v = true → v < n → Q v) :
    Holds Q n (reachPush enterable (seen, queue) v).1
      (reachPush enterable (seen, queue) v).2 := by
  unfold reachPush
  by_cases hc : (!seen.getD v false && enterable v && v < seen.size) = true
  · have hcond : enterable v = true ∧ v < seen.size := by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact ⟨hc.1.2, hc.2⟩
    have hQv : Q v := hv hcond.1 (by rw [← h.size]; exact hcond.2)
    simp only [hc, if_pos]
    refine ⟨by simpa using h.size, ?_, ?_⟩
    · intro p hp
      rcases getD_setIfInBounds_true hp with hpv | hs
      · rw [hpv]; exact hQv
      · exact h.marked p hs
    · intro w hw
      rcases Array.mem_push.mp hw with hq | hwv
      · exact h.queued w hq
      · rw [hwv]; exact hQv
  · simp only [hc, if_neg, Bool.not_eq_true]
    exact h

theorem fold_holds {Q : Nat → Prop} {n : Nat} :
    ∀ (l : List Nat) {seen : Array Bool} {queue : Array Nat},
      Holds Q n seen queue → (∀ v ∈ l, enterable v = true → v < n → Q v) →
      Holds Q n (l.foldl (reachPush enterable) (seen, queue)).1
        (l.foldl (reachPush enterable) (seen, queue)).2 := by
  intro l
  induction l with
  | nil => intro seen queue h _; exact h
  | cons v rest ih =>
      intro seen queue h hall
      exact ih (seen := (reachPush enterable (seen, queue) v).1)
        (queue := (reachPush enterable (seen, queue) v).2)
        (push_holds h (hall v (by simp)))
        (fun w hw => hall w (by simp [hw]))

theorem loop_marked {Q : Nat → Prop} {n : Nat}
    (hclosed : ∀ u v, Q u → v ∈ adj.getD u #[] → enterable v = true → v < n → Q v) :
    ∀ (fuel : Nat) (seen : Array Bool) (queue : Array Nat) (head : Nat),
      Holds Q n seen queue →
      ∀ p, (reachLoop adj enterable fuel seen queue head).getD p false = true → Q p := by
  intro fuel
  induction fuel with
  | zero => intro seen queue head h p hp; exact h.marked p hp
  | succ k ih =>
      intro seen queue head h p hp
      unfold reachLoop at hp
      by_cases hb : head ≥ queue.size
      · rw [if_pos hb] at hp; exact h.marked p hp
      · rw [if_neg hb] at hp
        refine ih _ _ (head + 1) ?_ p hp
        have hu : queue.getD head 0 ∈ queue := by
          rw [Array.getD_eq_getD_getElem?,
            Array.getElem?_eq_getElem (Nat.lt_of_not_le hb)]
          simpa using Array.getElem_mem (Nat.lt_of_not_le hb)
        have hQu : Q (queue.getD head 0) := h.queued _ hu
        have := fold_holds (Q := Q) (n := n) (adj.getD (queue.getD head 0) #[]).toList h
          (fun v hv => hclosed _ v hQu (by simpa using hv))
        rw [Array.foldl_toList] at this
        exact this

/-- **The walk marks nothing outside a closed set that holds the start squares.** -/
theorem reachFrom_least (adj : Array (Array Nat)) (start : Array Nat)
    (enterable : Nat → Bool) (Q : Nat → Prop) (hstart : ∀ p ∈ start, Q p)
    (hclosed : ∀ u v, Q u → v ∈ adj.getD u #[] → enterable v = true → v < adj.size → Q v) :
    ∀ p, (reachFrom adj start enterable).getD p false = true → Q p := by
  refine loop_marked hclosed _ _ _ _ ?_
  rw [← Array.foldl_toList]
  refine fold_holds start.toList ⟨by simp, ?_, by intro v hv; simp at hv⟩
    (fun v hv _ _ => hstart v (by simpa using hv))
  intro z hz
  exfalso
  rw [Array.getD_eq_getD_getElem?] at hz
  rcases Nat.lt_or_ge z adj.size with hlt | hge
  · rw [Array.getElem?_eq_getElem (by simpa using hlt)] at hz; simp at hz
  · rw [Array.getElem?_eq_none (by simpa using hge)] at hz; simp at hz

/-- Nothing is reached but the start squares and the ones the caller admits. -/
theorem reachFrom_guarded (adj : Array (Array Nat)) (start : Array Nat)
    (enterable : Nat → Bool) :
    ∀ p, (reachFrom adj start enterable).getD p false = true →
      start.contains p = true ∨ enterable p = true :=
  reachFrom_least adj start enterable _
    (fun p hp => Or.inl (by simpa using hp))
    (fun _ v _ _ hen _ => Or.inr hen)

/-! ### The walk is closed under the edges it may enter -/

theorem push_mono {st : Array Bool × Array Nat} {v p : Nat}
    (h : st.1.getD p false = true) :
    (reachPush enterable st v).1.getD p false = true := by
  unfold reachPush
  by_cases hc : (!st.1.getD v false && enterable v && v < st.1.size) = true
  · simp only [hc, if_pos]
    exact getD_setIfInBounds_mono h
  · simp only [hc, if_neg, Bool.not_eq_true]
    exact h

theorem fold_mono : ∀ (l : List Nat) (st : Array Bool × Array Nat) (p : Nat),
    st.1.getD p false = true →
    (l.foldl (reachPush enterable) st).1.getD p false = true := by
  intro l
  induction l with
  | nil => intro st p h; exact h
  | cons v rest ih => intro st p h; exact ih _ p (push_mono h)

theorem push_size (st : Array Bool × Array Nat) (v : Nat) :
    (reachPush enterable st v).1.size = st.1.size := by
  unfold reachPush
  by_cases hc : (!st.1.getD v false && enterable v && v < st.1.size) = true
  · simp only [hc, if_pos]; simp
  · simp only [hc, if_neg, Bool.not_eq_true]

theorem fold_size : ∀ (l : List Nat) (st : Array Bool × Array Nat),
    (l.foldl (reachPush enterable) st).1.size = st.1.size := by
  intro l
  induction l with
  | nil => intro st; rfl
  | cons v rest ih => intro st; rw [List.foldl_cons, ih, push_size]

theorem push_marks {st : Array Bool × Array Nat} {v : Nat} (hen : enterable v = true)
    (hlt : v < st.1.size) : (reachPush enterable st v).1.getD v false = true := by
  unfold reachPush
  by_cases hc : (!st.1.getD v false && enterable v && v < st.1.size) = true
  · simp only [hc, if_pos]
    exact getD_setIfInBounds_self hlt
  · have hmark : st.1.getD v false = true := by
      rcases hv : st.1.getD v false with _ | _
      · exact absurd (show (!st.1.getD v false && enterable v && decide (v < st.1.size)) = true
          from by simp [hv, hen, hlt]) hc
      · rfl
    simp only [hc, if_neg, Bool.not_eq_true]
    exact hmark

theorem fold_marks : ∀ (l : List Nat) (st : Array Bool × Array Nat),
    ∀ v ∈ l, enterable v = true → v < st.1.size →
      (l.foldl (reachPush enterable) st).1.getD v false = true := by
  intro l
  induction l with
  | nil => intro st v hv; simp at hv
  | cons w rest ih =>
      intro st v hv hen hlt
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hv with hvw | hvr
      · subst hvw
        exact fold_mono rest _ v (push_marks hen hlt)
      · exact ih _ v hvr hen (by rw [push_size]; exact hlt)

/-- What the walk knows while it runs. -/
structure Walk (n : Nat) (seen : Array Bool) (queue : Array Nat) : Prop where
  size : seen.size = n
  markedQueued : ∀ p, seen.getD p false = true → p ∈ queue
  queuedMarked : ∀ v ∈ queue, seen.getD v false = true
  nodup : queue.toList.Nodup
  range : ∀ v ∈ queue, v < n

theorem push_walk {n : Nat} {seen : Array Bool} {queue : Array Nat} {v : Nat}
    (h : Walk n seen queue) :
    Walk n (reachPush enterable (seen, queue) v).1 (reachPush enterable (seen, queue) v).2 := by
  unfold reachPush
  by_cases hc : (!seen.getD v false && enterable v && v < seen.size) = true
  · have hcond : seen.getD v false = false ∧ v < seen.size := by
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
      exact ⟨hc.1.1, hc.2⟩
    have hnotq : v ∉ queue := by
      intro hq
      rw [h.queuedMarked v hq] at hcond
      exact Bool.noConfusion hcond.1
    simp only [hc, if_pos]
    refine ⟨by simpa using h.size, ?_, ?_, ?_, ?_⟩
    · intro p hp
      rcases getD_setIfInBounds_true hp with hpv | hs
      · rw [hpv]; exact Array.mem_push.mpr (Or.inr rfl)
      · exact Array.mem_push.mpr (Or.inl (h.markedQueued p hs))
    · intro w hw
      rcases Array.mem_push.mp hw with hq | hwv
      · exact getD_setIfInBounds_mono (h.queuedMarked w hq)
      · rw [hwv]; exact getD_setIfInBounds_self hcond.2
    · rw [Array.toList_push]
      refine List.nodup_append.mpr ⟨h.nodup, List.nodup_singleton v, ?_⟩
      intro a ha b hb hab
      have hbv : b = v := by simpa using hb
      exact hnotq (by rw [← hbv, ← hab]; simpa using ha)
    · intro w hw
      rcases Array.mem_push.mp hw with hq | hwv
      · exact h.range w hq
      · rw [hwv, ← h.size]; exact hcond.2
  · simp only [hc, if_neg, Bool.not_eq_true]
    exact h

theorem fold_walk {n : Nat} : ∀ (l : List Nat) {seen : Array Bool} {queue : Array Nat},
    Walk n seen queue →
    Walk n (l.foldl (reachPush enterable) (seen, queue)).1
      (l.foldl (reachPush enterable) (seen, queue)).2 := by
  intro l
  induction l with
  | nil => intro seen queue h; exact h
  | cons v rest ih =>
      intro seen queue h
      exact ih (push_walk h)


/-! ### And it stops only when every marked square has been looked at -/

theorem push_prefix {st : Array Bool × Array Nat} {v i : Nat} (hi : i < st.2.size) :
    (reachPush enterable st v).2.getD i 0 = st.2.getD i 0 := by
  unfold reachPush
  by_cases hc : (!st.1.getD v false && enterable v && v < st.1.size) = true
  · simp only [hc, if_pos]
    show (st.2.push v).getD i 0 = st.2.getD i 0
    rw [Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (show i < (st.2.push v).size from by simp; omega),
      Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
    simp only [Option.getD_some]
    exact Array.getElem_push_lt hi
  · simp only [hc, if_neg, Bool.not_eq_true]

theorem push_grows (st : Array Bool × Array Nat) (v : Nat) :
    st.2.size ≤ (reachPush enterable st v).2.size := by
  unfold reachPush
  by_cases hc : (!st.1.getD v false && enterable v && v < st.1.size) = true
  · simp only [hc, if_pos]
    show st.2.size ≤ (st.2.push v).size
    simp
  · simp only [hc, if_neg, Bool.not_eq_true]
    exact Nat.le_refl _

theorem fold_prefix : ∀ (l : List Nat) (st : Array Bool × Array Nat) (i : Nat),
    i < st.2.size → (l.foldl (reachPush enterable) st).2.getD i 0 = st.2.getD i 0 := by
  intro l
  induction l with
  | nil => intro st i _; rfl
  | cons v rest ih =>
      intro st i hi
      rw [List.foldl_cons, ih _ i (Nat.lt_of_lt_of_le hi (push_grows st v)), push_prefix hi]

/-- Every square the walk has taken off the queue has its neighbours marked. -/
def Done (n : Nat) (adj : Array (Array Nat)) (enterable : Nat → Bool)
    (seen : Array Bool) (queue : Array Nat) (head : Nat) : Prop :=
  ∀ i, i < head → ∀ v ∈ adj.getD (queue.getD i 0) #[], enterable v = true → v < n →
    seen.getD v false = true

theorem queue_size_le {n : Nat} {seen : Array Bool} {queue : Array Nat}
    (h : Walk n seen queue) : queue.size ≤ n := by
  have := length_le_of_subset queue.toList (List.range n) h.nodup (fun x hx => by
    rw [List.mem_range]
    exact h.range x (by simpa using hx))
  simpa using this

theorem closed_of_done {n : Nat} {seen : Array Bool} {queue : Array Nat} {head : Nat}
    (hw : Walk n seen queue) (hd : Done n adj enterable seen queue head)
    (hq : queue.size ≤ head) :
    ∀ u v, seen.getD u false = true → v ∈ adj.getD u #[] → enterable v = true → v < n →
      seen.getD v false = true := by
  intro u v hu hv hen hlt
  obtain ⟨i, hi, hival⟩ := Array.getElem_of_mem (hw.markedQueued u hu)
  refine hd i (Nat.lt_of_lt_of_le hi hq) v ?_ hen hlt
  rw [show queue.getD i 0 = u from by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, hival]; rfl]
  exact hv

theorem loop_closed {n : Nat} :
    ∀ (fuel : Nat) (seen : Array Bool) (queue : Array Nat) (head : Nat),
      Walk n seen queue → Done n adj enterable seen queue head → n ≤ head + fuel →
      ∀ u v, (reachLoop adj enterable fuel seen queue head).getD u false = true →
        v ∈ adj.getD u #[] → enterable v = true → v < n →
        (reachLoop adj enterable fuel seen queue head).getD v false = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro seen queue head hw hd hle
      exact closed_of_done hw hd (Nat.le_trans (queue_size_le hw) (by omega))
  | succ k ih =>
      intro seen queue head hw hd hle u v hu hv hen hlt
      unfold reachLoop at hu ⊢
      by_cases hb : head ≥ queue.size
      · rw [if_pos hb] at hu ⊢
        exact closed_of_done hw hd hb u v hu hv hen hlt
      · rw [if_neg hb] at hu ⊢
        have hhead : head < queue.size := Nat.lt_of_not_le hb
        set l := (adj.getD (queue.getD head 0) #[]).toList with hl
        set st := (l.foldl (reachPush enterable) (seen, queue)) with hst
        have hfold : (adj.getD (queue.getD head 0) #[]).foldl (init := (seen, queue))
            (reachPush enterable) = st := by rw [hst, hl, Array.foldl_toList]
        rw [hfold] at hu ⊢
        refine ih st.1 st.2 (head + 1) (by rw [hst]; exact fold_walk l hw) ?_ (by omega)
          u v hu hv hen hlt
        intro i hi w hw2 hen2 hlt2
        rcases Nat.lt_or_ge i head with hih | hih
        · have hprefix : st.2.getD i 0 = queue.getD i 0 := by
            rw [hst]
            exact fold_prefix l (seen, queue) i (show i < queue.size from by omega)
          rw [hprefix] at hw2
          exact fold_mono l (seen, queue) w (hd i hih w hw2 hen2 hlt2)
        · have hieq : i = head := by omega
          rw [hieq] at hw2
          have hprefix : st.2.getD head 0 = queue.getD head 0 := by
            rw [hst]
            exact fold_prefix l (seen, queue) head (show head < queue.size from hhead)
          rw [hprefix] at hw2
          rw [hst]
          exact fold_marks l (seen, queue) w (by simpa [hl] using hw2) hen2
            (by rw [show (seen, queue).1.size = n from hw.size]; exact hlt2)

/-- **The walk is closed: an edge out of a marked square into one it may enter
lands on a marked square.** -/
theorem reachFrom_closed (adj : Array (Array Nat)) (start : Array Nat)
    (enterable : Nat → Bool) :
    ∀ u v, (reachFrom adj start enterable).getD u false = true →
      v ∈ adj.getD u #[] → enterable v = true → v < adj.size →
      (reachFrom adj start enterable).getD v false = true := by
  refine loop_closed adj.size _ _ 0 ?_ (by intro i hi; omega) (by omega)
  rw [← Array.foldl_toList]
  refine fold_walk start.toList ⟨by simp, ?_, by intro v hv; simp at hv, by simp, ?_⟩
  · intro z hz
    exfalso
    rw [Array.getD_eq_getD_getElem?] at hz
    rcases Nat.lt_or_ge z adj.size with hlt | hge
    · rw [Array.getElem?_eq_getElem (by simpa using hlt)] at hz; simp at hz
    · rw [Array.getElem?_eq_none (by simpa using hge)] at hz; simp at hz
  · intro v hv; simp at hv

theorem loop_mono :
    ∀ (fuel : Nat) (seen : Array Bool) (queue : Array Nat) (head p : Nat),
      seen.getD p false = true →
      (reachLoop adj enterable fuel seen queue head).getD p false = true := by
  intro fuel
  induction fuel with
  | zero => intro seen queue head p h; exact h
  | succ k ih =>
      intro seen queue head p h
      unfold reachLoop
      by_cases hb : head ≥ queue.size
      · rw [if_pos hb]; exact h
      · rw [if_neg hb]
        refine ih _ _ (head + 1) p ?_
        rw [← Array.foldl_toList]
        exact fold_mono _ (seen, queue) p h

/-- **A start square the walk may enter is marked.** -/
theorem reachFrom_start (adj : Array (Array Nat)) (start : Array Nat)
    (enterable : Nat → Bool) {p : Nat} (hp : p ∈ start) (hen : enterable p = true)
    (hlt : p < adj.size) : (reachFrom adj start enterable).getD p false = true := by
  refine loop_mono adj.size _ _ 0 p ?_
  rw [← Array.foldl_toList]
  exact fold_marks start.toList _ p (by simpa using hp) hen (by simpa using hlt)


end Planner.Reach
