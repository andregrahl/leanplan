/-
Blocksworld's improved heuristic, proved end to end in one file.

The order below is the order the argument is built in.  The schema-level proof
comes first: the improved value over the domain's own data, and what each schema
does to the counters.  The rest lifts that value to the parsed domain and
compiles it against the numbered task.

The runtime heuristic and its data stay under `Planner/`.  The simple heuristic
of this domain is proved in `Proofs/Domains/BlocksworldSimple.lean`.
-/
import Planner.ExampleHeuristics.Blocksworld.Certificate
import Proofs.Heuristic
import Planner.GeneratedDomains.Blocksworld
import Proofs.Combinators
import Proofs.Certificates
import Proofs.ExampleHeuristics.Base
import Proofs.SchemaSupport
import Proofs.FactTables
import Proofs.StepView
import Proofs.LiftedHeuristic
import Proofs.CompileSupport
import Proofs.Validation
import Mathlib.Data.Finset.Card
import Planner.ExampleHeuristics.Blocksworld.Improved

/- -------------------------------------------------------------------------- -/
/-
The must-move fixpoint.

This is the piece the plan flagged as the outlier, and the statement is the
substance of it.  A blocksworld action does exactly one of two things to the
vocabulary the analysis reads — the block under each block, which block is in the
hand, and whose goal support is unmet:

  * a **grab** (`pickup`, `unstack`) takes `a` into the empty hand: `a` comes off
    whatever it was on, nothing else moves, and `a`'s goal support can only become
    *less* satisfied;
  * a **place** (`putdown`, `stack`) puts the held `a` down: `a` acquires a
    support, nothing else moves, and `a`'s goal support can only become *more*
    satisfied.

Everything else the analysis uses — which block the goal wants under which, which
blocks the goal wants clear — is static.  So the whole domain reduces to those two
shapes, and the theorem is that neither drops `moveBound` by more than one.

Two facts about the state are needed and are not free.  A block sits on at most
one block, and towers are finite: climbing down from any block falls off the
bottom within `blocks.size` steps.  Both are physical, both are preserved by every
schema, and without them the "fixpoint" of a cyclic tower is not a fixpoint at
all.
-/

namespace Planner.ExampleHeuristics.Blocksworld

open Planner

/-! ### Towers -/

/-- The block `j` steps below `b`, if there is one. -/
def climb (d : Data) (s : State) : Nat → Nat → Option Nat
  | 0, b => some b
  | j + 1, b => (climb d s j b).bind (supportOf d s)

theorem climb_zero (d : Data) (s : State) (b : Nat) : climb d s 0 b = some b := rfl

theorem climb_succ (d : Data) (s : State) (j b : Nat) :
    climb d s (j + 1) b = (climb d s j b).bind (supportOf d s) := rfl

/-- Climbing from `b` is climbing one less from the block under `b`. -/
theorem climb_succ_left (d : Data) (s : State) :
    ∀ (j b : Nat), climb d s (j + 1) b = (supportOf d s b).bind (climb d s j) := by
  intro j
  induction j with
  | zero =>
      intro b
      simp only [climb, Option.bind]
      cases supportOf d s b <;> rfl
  | succ j ih =>
      intro b
      rw [climb_succ, ih b]
      cases hs : supportOf d s b with
      | none => simp
      | some c => simp [climb_succ]

/-- Once a tower runs out it stays out. -/
theorem climb_none_mono (d : Data) (s : State) (b : Nat) :
    ∀ (j k : Nat), j ≤ k → climb d s j b = none → climb d s k b = none := by
  intro j k hjk hj
  induction k with
  | zero =>
      have hj0 : j = 0 := by omega
      subst hj0
      exact hj
  | succ k ih =>
      by_cases h : j ≤ k
      · rw [climb_succ, ih h]
        rfl
      · have : j = k + 1 := by omega
        rw [← this]
        exact hj

/-! ### The fixpoint, read as a chain -/

/-- `mustMoveAux` is exactly "a seed sits at or below `b`, within `k` steps". -/
theorem mustMoveAux_iff (d : Data) (s : State) :
    ∀ (k b : Nat), mustMoveAux d s k b = true ↔
      ∃ j, j < k ∧ ∃ y, climb d s j b = some y ∧ seed d s y = true := by
  intro k
  induction k with
  | zero =>
      intro b
      simp only [mustMoveAux, Bool.false_eq_true, false_iff]
      rintro ⟨j, hj, -⟩
      omega
  | succ k ih =>
      intro b
      rw [mustMoveAux]
      constructor
      · intro h
        rcases Bool.or_eq_true_iff.mp h with hseed | hrest
        · exact ⟨0, by omega, b, rfl, hseed⟩
        · cases hsup : supportOf d s b with
          | none => rw [hsup] at hrest; simp at hrest
          | some c =>
              rw [hsup] at hrest
              obtain ⟨j, hj, y, hy, hseed⟩ := (ih c).mp hrest
              refine ⟨j + 1, by omega, y, ?_, hseed⟩
              rw [climb_succ_left, hsup]
              exact hy
      · rintro ⟨j, hj, y, hy, hseed⟩
        cases j with
        | zero =>
            rw [climb_zero] at hy
            simp only [Option.some.injEq] at hy
            subst hy
            simp [hseed]
        | succ j =>
            rw [climb_succ_left] at hy
            cases hsup : supportOf d s b with
            | none => rw [hsup] at hy; simp at hy
            | some c =>
                rw [hsup] at hy
                simp only [Option.bind_some] at hy
                have : mustMoveAux d s k c = true :=
                  (ih c).mpr ⟨j, by omega, y, hy, hseed⟩
                simp [this]

/-! ### What a physical state guarantees

A block sits on at most one block, and towers are finite: climbing `blocks.size`
steps down from anywhere falls off the bottom.  Both hold of every state a
blocksworld plan can reach, and both are needed — the first for the detour
argument, the second to make the bounded unfolding a genuine fixpoint rather than
a truncation.
-/

structure Physical (d : Data) (s : State) : Prop where
  /-- At most one block rests directly on any block. -/
  unique : ∀ x y c, supportOf d s x = some c → supportOf d s y = some c → x = y
  /-- Towers are no taller than the number of blocks. -/
  grounded : ∀ b, climb d s d.blocks.size b = none
  /-- A block whose goal support holds really does stand on that block.  This is
  the same fact as `unique` read through the compiled data: the goal's `on` fact
  for a block is one of that block's `on` facts, and at most one of those holds. -/
  placed : ∀ b f c, (d.blocks.getD b default).goalOn = some (f, c) →
    supportUnmet d s b = false → supportOf d s b = some c

/-- Nothing stands on itself: a tower would then never end. -/
theorem Physical.no_self {d : Data} {s : State} (hp : Physical d s) (b : Nat) :
    supportOf d s b ≠ some b := by
  intro hb
  have hall : ∀ j, climb d s j b = some b := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [climb_succ, ih]; exact hb
  have := hp.grounded b
  rw [hall d.blocks.size] at this
  simp at this

theorem mustMoveAux_mono (d : Data) (s : State) {k k' b : Nat} (h : k ≤ k')
    (hk : mustMoveAux d s k b = true) : mustMoveAux d s k' b = true := by
  obtain ⟨j, hj, y, hy, hseed⟩ := (mustMoveAux_iff d s k b).mp hk
  exact (mustMoveAux_iff d s k' b).mpr ⟨j, by omega, y, hy, hseed⟩

/-- Past the number of blocks the unfolding has converged. -/
theorem mustMoveAux_saturates (d : Data) (s : State) (hp : Physical d s) {k : Nat}
    (hk : d.blocks.size ≤ k) (b : Nat) :
    mustMoveAux d s k b = mustMoveAux d s d.blocks.size b := by
  refine Bool.eq_iff_iff.mpr ⟨fun h => ?_, fun h => mustMoveAux_mono d s hk h⟩
  obtain ⟨j, hj, y, hy, hseed⟩ := (mustMoveAux_iff d s k b).mp h
  have hjlt : j < d.blocks.size := by
    by_contra hc
    have hnone : climb d s j b = none :=
      climb_none_mono d s b _ _ (Nat.not_lt.mp hc) (hp.grounded b)
    rw [hnone] at hy
    simp at hy
  exact (mustMoveAux_iff d s _ b).mpr ⟨j, hjlt, y, hy, hseed⟩

theorem mustMove_eq_aux (d : Data) (s : State) (hp : Physical d s) {k : Nat}
    (hk : d.blocks.size ≤ k) (b : Nat) : mustMoveAux d s k b = mustMove d s b := by
  rw [mustMove, mustMoveAux_saturates d s hp hk b,
    mustMoveAux_saturates d s hp (Nat.le_succ _) b]

/-- The fixpoint equation: a block moves when it is a seed or stands on a mover. -/
theorem mustMove_unfold (d : Data) (s : State) (hp : Physical d s) (b : Nat) :
    mustMove d s b =
      (seed d s b ||
        match supportOf d s b with
        | some c => mustMove d s c
        | none => false) := by
  rw [mustMove, mustMoveAux]
  cases hsup : supportOf d s b with
  | none => simp
  | some c =>
      show (seed d s b || mustMoveAux d s d.blocks.size c)
        = (seed d s b || mustMove d s c)
      rw [mustMove_eq_aux d s hp (Nat.le_refl _) c]

/-- `b` must move exactly when a seed sits at or below it. -/
theorem mustMove_iff (d : Data) (s : State) (hp : Physical d s) (b : Nat) :
    mustMove d s b = true ↔
      ∃ j, ∃ y, climb d s j b = some y ∧ seed d s y = true := by
  rw [mustMove, mustMoveAux_iff]
  constructor
  · rintro ⟨j, -, y, hy, hseed⟩
    exact ⟨j, y, hy, hseed⟩
  · rintro ⟨j, y, hy, hseed⟩
    have hjlt : j < d.blocks.size := by
      by_contra hc
      have hnone : climb d s j b = none :=
        climb_none_mono d s b _ _ (Nat.not_lt.mp hc) (hp.grounded b)
      rw [hnone] at hy
      simp at hy
    exact ⟨j, by omega, y, hy, hseed⟩

/-! ### A block's goal tower

The detour argument needs the goal read as a chain, the way the state is: the
block the goal wants under `b`, then the one under that.
-/

/-- The block the goal wants directly under `b`. -/
def goalSup (d : Data) (b : Nat) : Option Nat :=
  ((d.blocks.getD b default).goalOn).map (·.2)

/-- The block the goal wants `i` levels below `b`. -/
def goalClimb (d : Data) : Nat → Nat → Option Nat
  | 0, b => some b
  | i + 1, b => (goalClimb d i b).bind (goalSup d)

theorem goalSup_eq_some {d : Data} {b z : Nat} (h : goalSup d b = some z) :
    ∃ f, (d.blocks.getD b default).goalOn = some (f, z) := by
  unfold goalSup at h
  cases hg : (d.blocks.getD b default).goalOn with
  | none => rw [hg] at h; simp at h
  | some ft =>
      rw [hg] at h
      simp only [Option.map_some, Option.some.injEq] at h
      refine ⟨ft.1, ?_⟩
      congr 1
      rw [← h]

theorem goalClimb_succ_left (d : Data) :
    ∀ (i b : Nat), goalClimb d (i + 1) b = (goalSup d b).bind (goalClimb d i) := by
  intro i
  induction i with
  | zero =>
      intro b
      simp only [goalClimb, Option.bind]
      cases goalSup d b <;> rfl
  | succ i ih =>
      intro b
      rw [goalClimb, ih b]
      cases hs : goalSup d b with
      | none => simp
      | some c => simp [goalClimb]

/-- `inGoalChain` is exactly "the goal wants `target` somewhere below `b`". -/
theorem inGoalChainAux_iff (d : Data) :
    ∀ (k b target : Nat), inGoalChainAux d k b target = true ↔
      ∃ i, 1 ≤ i ∧ i ≤ k ∧ goalClimb d i b = some target := by
  intro k
  induction k with
  | zero =>
      intro b target
      simp only [inGoalChainAux, Bool.false_eq_true, false_iff]
      rintro ⟨i, hi, hik, -⟩
      omega
  | succ k ih =>
      intro b target
      rw [inGoalChainAux]
      cases hg : (d.blocks.getD b default).goalOn with
      | none =>
          simp only [Bool.false_eq_true, false_iff]
          rintro ⟨i, hi, hik, hclimb⟩
          have hsup : goalSup d b = none := by rw [goalSup, hg]; rfl
          cases i with
          | zero => omega
          | succ i =>
              rw [goalClimb_succ_left, hsup] at hclimb
              simp at hclimb
      | some fc =>
          have hsup : goalSup d b = some fc.2 := by rw [goalSup, hg]; rfl
          simp only [Bool.or_eq_true, beq_iff_eq, ih]
          constructor
          · rintro (rfl | ⟨i, hi, hik, hclimb⟩)
            · exact ⟨1, by omega, by omega, by
                rw [goalClimb_succ_left, hsup]; rfl⟩
            · exact ⟨i + 1, by omega, by omega, by
                rw [goalClimb_succ_left, hsup]; exact hclimb⟩
          · rintro ⟨i, hi, hik, hclimb⟩
            cases i with
            | zero => omega
            | succ i =>
                rw [goalClimb_succ_left, hsup] at hclimb
                simp only [Option.bind_some] at hclimb
                cases i with
                | zero =>
                    left
                    simpa [goalClimb] using hclimb
                | succ i => exact Or.inr ⟨i + 1, by omega, by omega, hclimb⟩

/-! ### The two shapes an action takes

Everything the analysis reads about a state is here: which block is under which,
which block is in the hand, and whose goal support is unmet.  A `Grab` is
`pickup` or `unstack`, a `Place` is `putdown` or `stack`, and the fields are what
the schemas do to that vocabulary.
-/

/-- `pickup` and `unstack`: the empty hand takes `a` off whatever it was on. -/
structure Grab (d : Data) (s s' : State) (a : Nat) : Prop where
  /-- The hand was empty. -/
  noneHeld : ∀ x, isHeld d s x = false
  /-- It now holds `a`, and nothing else. -/
  heldA : isHeld d s' a = true
  heldOther : ∀ x, x ≠ a → isHeld d s' x = false
  /-- `a` was clear. -/
  nothingOn : ∀ x, supportOf d s x ≠ some a
  /-- `a` is off its support; nothing else moved. -/
  supportA : supportOf d s' a = none
  supportOther : ∀ x, x ≠ a → supportOf d s' x = supportOf d s x
  /-- Taking `a` can only unmake its own goal support. -/
  unmetA : supportUnmet d s a = true → supportUnmet d s' a = true
  unmetOther : ∀ x, x ≠ a → supportUnmet d s' x = supportUnmet d s x
  /-- `a` is one of the task's blocks. -/
  aLt : a < d.blocks.size

/-- `putdown` and `stack`: the held `a` is put down somewhere. -/
structure Place (d : Data) (s s' : State) (a : Nat) : Prop where
  /-- The hand held `a`, and nothing else. -/
  heldA : isHeld d s a = true
  heldOther : ∀ x, x ≠ a → isHeld d s x = false
  /-- The hand is empty afterwards. -/
  noneHeld : ∀ x, isHeld d s' x = false
  /-- Nothing rests on `a`, before or after. -/
  nothingOn : ∀ x, supportOf d s x ≠ some a
  nothingOn' : ∀ x, supportOf d s' x ≠ some a
  /-- `a` was in the hand, so it was on nothing; nothing else moved. -/
  supportA : supportOf d s a = none
  supportOther : ∀ x, x ≠ a → supportOf d s' x = supportOf d s x
  /-- Putting `a` down can only make its own goal support hold. -/
  unmetA : supportUnmet d s' a = true → supportUnmet d s a = true
  unmetOther : ∀ x, x ≠ a → supportUnmet d s' x = supportUnmet d s x
  /-- `a` is one of the task's blocks. -/
  aLt : a < d.blocks.size

/-! ### Chains that avoid the block being moved -/

/-- Nothing rests on `a`, so no tower below any other block passes through it. -/
theorem climb_ne (d : Data) (s : State) {a : Nat} (hno : ∀ x, supportOf d s x ≠ some a) :
    ∀ (j x y : Nat), x ≠ a → climb d s j x = some y → y ≠ a := by
  intro j
  induction j with
  | zero =>
      intro x y hx hy
      rw [climb_zero] at hy
      simp only [Option.some.injEq] at hy
      exact hy ▸ hx
  | succ j ih =>
      intro x y hx hy
      rw [climb_succ] at hy
      cases hc : climb d s j x with
      | none => rw [hc] at hy; simp at hy
      | some z =>
          rw [hc] at hy
          simp only [Option.bind_some] at hy
          intro hya
          exact hno z (by rw [hy, hya])

/-- Off the block being moved, the towers are the same in both states. -/
theorem climb_congr (d : Data) (s s' : State) {a : Nat}
    (hsup : ∀ x, x ≠ a → supportOf d s' x = supportOf d s x)
    (hno : ∀ x, supportOf d s x ≠ some a) :
    ∀ (j x : Nat), x ≠ a → climb d s' j x = climb d s j x := by
  intro j
  induction j with
  | zero => intro x _; rfl
  | succ j ih =>
      intro x hx
      rw [climb_succ, climb_succ, ih x hx]
      cases hc : climb d s j x with
      | none => simp
      | some z =>
          simp only [Option.bind_some]
          exact hsup z (climb_ne d s hno j x z hx hc)

/-! ### How the must-move set moves

Off the block being moved nothing changes at all: the towers are the same and so
are the reasons a block has to move.  The whole difference between the two states
is concentrated in `a`.
-/

/-- A block's seed status is read off its support, its goal support and the hand. -/
theorem seed_congr (d : Data) (s s' : State) (x : Nat)
    (hun : supportUnmet d s' x = supportUnmet d s x)
    (hsup : supportOf d s' x = supportOf d s x)
    (hheld : isHeld d s' x = isHeld d s x) : seed d s' x = seed d s x := by
  unfold seed blocking
  rw [hun, hsup, hheld]

theorem mustMove_congr_off (d : Data) (s s' : State) (a : Nat)
    (hp : Physical d s) (hp' : Physical d s')
    (hsup : ∀ x, x ≠ a → supportOf d s' x = supportOf d s x)
    (hno : ∀ x, supportOf d s x ≠ some a)
    (hseed : ∀ x, x ≠ a → seed d s' x = seed d s x)
    (x : Nat) (hx : x ≠ a) : mustMove d s' x = mustMove d s x := by
  refine Bool.eq_iff_iff.mpr ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨j, y, hy, hs⟩ := (mustMove_iff d s' hp' x).mp h
    rw [climb_congr d s s' hsup hno j x hx] at hy
    exact (mustMove_iff d s hp x).mpr
      ⟨j, y, hy, by rwa [hseed y (climb_ne d s hno j x y hx hy)] at hs⟩
  · obtain ⟨j, y, hy, hs⟩ := (mustMove_iff d s hp x).mp h
    refine (mustMove_iff d s' hp' x).mpr ⟨j, y, ?_, ?_⟩
    · rw [climb_congr d s s' hsup hno j x hx]; exact hy
    · rw [hseed y (climb_ne d s hno j x y hx hy)]; exact hs

/-! #### A grab -/

theorem Grab.seed_off {d : Data} {s s' : State} {a : Nat} (hg : Grab d s s' a)
    (x : Nat) (hx : x ≠ a) : seed d s' x = seed d s x :=
  seed_congr d s s' x (hg.unmetOther x hx) (hg.supportOther x hx)
    (by rw [hg.heldOther x hx, hg.noneHeld x])

theorem Grab.seed_a {d : Data} {s s' : State} {a : Nat} (hg : Grab d s s' a) :
    seed d s' a = true := by
  unfold seed
  rw [hg.heldA]
  simp

theorem Grab.mustMove_off {d : Data} {s s' : State} {a : Nat} (hg : Grab d s s' a)
    (hp : Physical d s) (hp' : Physical d s') (x : Nat) (hx : x ≠ a) :
    mustMove d s' x = mustMove d s x :=
  mustMove_congr_off d s s' a hp hp' hg.supportOther hg.nothingOn hg.seed_off x hx

/-- The block in the hand must move. -/
theorem Grab.mustMove_a {d : Data} {s s' : State} {a : Nat} (hg : Grab d s s' a)
    (hp' : Physical d s') : mustMove d s' a = true :=
  (mustMove_iff d s' hp' a).mpr ⟨0, a, rfl, hg.seed_a⟩

/-! #### A place -/

theorem Place.seed_off {d : Data} {s s' : State} {a : Nat} (hpl : Place d s s' a)
    (x : Nat) (hx : x ≠ a) : seed d s' x = seed d s x :=
  seed_congr d s s' x (hpl.unmetOther x hx) (hpl.supportOther x hx)
    (by rw [hpl.noneHeld x, hpl.heldOther x hx])

theorem Place.mustMove_off {d : Data} {s s' : State} {a : Nat} (hpl : Place d s s' a)
    (hp : Physical d s) (hp' : Physical d s') (x : Nat) (hx : x ≠ a) :
    mustMove d s' x = mustMove d s x :=
  mustMove_congr_off d s s' a hp hp' hpl.supportOther hpl.nothingOn hpl.seed_off x hx

/-- The block in the hand must move. -/
theorem Place.mustMove_a {d : Data} {s s' : State} {a : Nat} (hpl : Place d s s' a)
    (hp : Physical d s) : mustMove d s a = true := by
  refine (mustMove_iff d s hp a).mpr ⟨0, a, rfl, ?_⟩
  unfold seed
  rw [hpl.heldA]
  simp

/-! ### Counting blocks

The four quantities the bound adds up are counts over the block list, so what the
arithmetic needs of them is how a count moves when the predicate weakens, and how
much a single block can be worth.
-/

theorem countP_le_of_imp {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ x ∈ l, p x = true → q x = true) : l.countP p ≤ l.countP q := by
  induction l with
  | nil => simp
  | cons x rest ih =>
      have hrest := ih fun y hy => h y (by simp [hy])
      rw [List.countP_cons, List.countP_cons]
      by_cases hp : p x
      · rw [if_pos hp, if_pos (h x (by simp) hp)]
        omega
      · rw [if_neg hp]
        by_cases hq : q x
        · rw [if_pos hq]; omega
        · rw [if_neg hq]; omega

/-- Allowing one block to escape the implication costs one. -/
theorem countP_le_succ_of_imp {α : Type} [DecidableEq α] (l : List α) (p q : α → Bool) (a : α)
    (hnd : l.Nodup) (h : ∀ x ∈ l, x ≠ a → p x = true → q x = true) :
    l.countP p ≤ l.countP q + 1 := by
  induction l with
  | nil => simp
  | cons x rest ih =>
      have hrest := ih (List.nodup_cons.mp hnd).2 fun y hy => h y (by simp [hy])
      rw [List.countP_cons, List.countP_cons]
      by_cases hxa : x = a
      · subst hxa
        have hoff : ∀ y ∈ rest, p y = true → q y = true := by
          intro y hy hp
          exact h y (by simp [hy]) (by rintro rfl; exact (List.nodup_cons.mp hnd).1 hy) hp
        have := countP_le_of_imp rest p q hoff
        by_cases hp : p x <;> by_cases hq : q x <;> simp_all <;> omega
      · by_cases hp : p x
        · rw [if_pos hp, if_pos (h x (by simp) hxa hp)]
          omega
        · rw [if_neg hp]
          by_cases hq : q x
          · rw [if_pos hq]; omega
          · rw [if_neg hq]; omega

/-- A block the count gains outright. -/
theorem countP_succ_le_of_witness {α : Type} [DecidableEq α] (l : List α) (p q : α → Bool)
    (a : α) (ha : a ∈ l) (hnd : l.Nodup) (hpa : p a = false) (hqa : q a = true)
    (h : ∀ x ∈ l, p x = true → q x = true) : l.countP p + 1 ≤ l.countP q := by
  induction l with
  | nil => simp at ha
  | cons x rest ih =>
      rw [List.countP_cons, List.countP_cons]
      rcases List.mem_cons.mp ha with rfl | ha'
      · have hle := countP_le_of_imp rest p q fun y hy => h y (by simp [hy])
        rw [if_neg (by simp [hpa]), if_pos hqa]
        omega
      · have hx : x ≠ a := by
          rintro rfl
          exact (List.nodup_cons.mp hnd).1 ha'
        have hrest := ih ha' (List.nodup_cons.mp hnd).2 fun y hy => h y (by simp [hy])
        by_cases hp : p x
        · rw [if_pos hp, if_pos (h x (by simp) hp)]
          omega
        · rw [if_neg hp]
          by_cases hq : q x
          · rw [if_pos hq]; omega
          · rw [if_neg hq]; omega

/-- Splitting the movers into the two halves the bound treats differently. -/
theorem countP_split {α : Type} (l : List α) (p r : α → Bool) :
    l.countP (fun x => p x && r x) + l.countP (fun x => p x && !r x) = l.countP p := by
  induction l with
  | nil => simp
  | cons x rest ih =>
      rw [List.countP_cons, List.countP_cons, List.countP_cons]
      by_cases hp : p x
      · by_cases hr : r x <;> simp [hp, hr] <;> omega
      · simp [hp]
        omega

/-- Two counts that differ at one block only. -/
theorem countP_off_eq {α : Type} [DecidableEq α] (l : List α) (p q : α → Bool) (a : α)
    (hnd : l.Nodup) (ha : a ∈ l) (h : ∀ x ∈ l, x ≠ a → p x = q x) :
    l.countP p + (if q a then 1 else 0) = l.countP q + (if p a then 1 else 0) := by
  induction l with
  | nil => simp at ha
  | cons x rest ih =>
      rw [List.countP_cons, List.countP_cons]
      rcases List.mem_cons.mp ha with rfl | ha'
      · have hoff : ∀ y ∈ rest, p y = q y := by
          intro y hy
          exact h y (by simp [hy]) (by rintro rfl; exact (List.nodup_cons.mp hnd).1 hy)
        have hcount : rest.countP p = rest.countP q :=
          Nat.le_antisymm (countP_le_of_imp rest p q fun y hy hpy => by rw [← hoff y hy]; exact hpy)
            (countP_le_of_imp rest q p fun y hy hqy => by rw [hoff y hy]; exact hqy)
        by_cases hp : p a <;> by_cases hq : q a <;> simp [hp, hq, hcount] <;> omega
      · have hx : x ≠ a := by
          rintro rfl
          exact (List.nodup_cons.mp hnd).1 ha'
        have hrest := ih (List.nodup_cons.mp hnd).2 ha' fun y hy => h y (by simp [hy])
        have hxe := h x (by simp) hx
        by_cases hp : p x
        · rw [if_pos hp, if_pos (show q x = true by rw [← hxe]; exact hp)]
          omega
        · rw [if_neg hp, if_neg (show ¬ (q x = true) by rw [← hxe]; exact hp)]
          omega

theorem countP_pos_of_mem {α : Type} (l : List α) (p : α → Bool) (a : α) (ha : a ∈ l)
    (hpa : p a = true) : 0 < l.countP p := by
  rw [List.countP_pos_iff]
  exact ⟨a, ha, hpa⟩

/-! ### The bound in one line

`moveBound` is a grab and a place for every block that must move, less the one
already in the hand, less the one that may stay there, plus two per detour.  In
that form the two step theorems are arithmetic over five counts.
-/

/-- How many blocks must move. -/
def movers (d : Data) (s : State) : Nat := (blockList d).countP fun b => mustMove d s b

/-- Whether any mover only has to get out of the way. -/
def clearingFlag (d : Data) (s : State) : Nat := if needClearing d s > 0 then 1 else 0

theorem blockList_nodup (d : Data) : (blockList d).Nodup := List.nodup_range

theorem mem_blockList {d : Data} {b : Nat} : b ∈ blockList d ↔ b < d.blocks.size :=
  List.mem_range

theorem needPlace_add_needClearing (d : Data) (s : State) :
    needPlace d s + needClearing d s = movers d s :=
  countP_split _ _ _

theorem heldNeedsPlace_le_movers (d : Data) (s : State) :
    heldNeedsPlace d s ≤ movers d s := by
  unfold heldNeedsPlace
  split
  · rename_i hany
    obtain ⟨b, hb, hbp⟩ := List.any_eq_true.mp hany
    exact countP_pos_of_mem _ _ b hb (by simpa using (Bool.and_eq_true_iff.mp hbp).1)
  · exact Nat.zero_le _

theorem clearingFlag_le_movers (d : Data) (s : State) :
    clearingFlag d s ≤ movers d s := by
  unfold clearingFlag
  split
  · rename_i hpos
    obtain ⟨b, hb, hbp⟩ := List.countP_pos_iff.mp hpos
    exact countP_pos_of_mem _ _ b hb (Bool.and_eq_true_iff.mp hbp).1
  · exact Nat.zero_le _

/-- The bound, with the two subtractions moved to the other side. -/
theorem moveBound_eq (d : Data) (s : State) :
    moveBound d s + heldNeedsPlace d s + clearingFlag d s
      = 2 * movers d s + 2 * detours d s := by
  have hm := needPlace_add_needClearing d s
  have hh := heldNeedsPlace_le_movers d s
  have hc := clearingFlag_le_movers d s
  show (needPlace d s + needClearing d s - heldNeedsPlace d s + detours d s)
      + (needPlace d s + needClearing d s
          - (if needClearing d s > 0 then 1 else 0) + detours d s)
      + heldNeedsPlace d s + clearingFlag d s
    = 2 * movers d s + 2 * detours d s
  unfold clearingFlag at hc ⊢
  omega

/-! ### A grab moves nothing down

Taking a block into an empty hand only ever adds to the must-move set — `a` joins
it if it was not there already — and only ever adds detours.  What it does take
away is the grab that block no longer needs, which is the one unit of slack the
theorem allows.
-/

theorem Grab.mustMove_imp {d : Data} {s s' : State} {a : Nat} (hg : Grab d s s' a)
    (hp : Physical d s) (hp' : Physical d s') (x : Nat) (hx : mustMove d s x = true) :
    mustMove d s' x = true := by
  by_cases hxa : x = a
  · subst hxa
    exact hg.mustMove_a hp'
  · rw [hg.mustMove_off hp hp' x hxa]
    exact hx

theorem Grab.movers_le {d : Data} {s s' : State} {a : Nat} (hg : Grab d s s' a)
    (hp : Physical d s) (hp' : Physical d s') : movers d s ≤ movers d s' :=
  countP_le_of_imp _ _ _ fun x _ hx => hg.mustMove_imp hp hp' x hx

theorem Grab.held_zero {d : Data} {s s' : State} {a : Nat} (hg : Grab d s s' a) :
    heldNeedsPlace d s = 0 := by
  unfold heldNeedsPlace
  rw [if_neg]
  intro hany
  obtain ⟨b, -, hbp⟩ := List.any_eq_true.mp hany
  rw [hg.noneHeld b] at hbp
  simp at hbp

theorem Grab.held_one {d : Data} {s s' : State} {a : Nat} (hg : Grab d s s' a)
    (hp' : Physical d s') : heldNeedsPlace d s' = 1 := by
  unfold heldNeedsPlace
  rw [if_pos]
  exact List.any_eq_true.mpr ⟨a, mem_blockList.mpr hg.aLt, by
    rw [hg.mustMove_a hp', hg.heldA]; rfl⟩

theorem Grab.detours_le {d : Data} {s s' : State} {a : Nat} (hg : Grab d s s' a)
    (hp : Physical d s) (hp' : Physical d s') : detours d s ≤ detours d s' := by
  refine countP_le_of_imp _ _ _ fun b _ hb => ?_
  obtain ⟨hmm, hdet⟩ := Bool.and_eq_true_iff.mp hb
  refine Bool.and_eq_true_iff.mpr ⟨hg.mustMove_imp hp hp' b hmm, ?_⟩
  unfold detour at hdet ⊢
  cases hgo : (d.blocks.getD b default).goalOn with
  | none => rw [hgo] at hdet; simp at hdet
  | some ft =>
      rw [hgo] at hdet
      obtain ⟨htarget, hway⟩ := Bool.and_eq_true_iff.mp hdet
      refine Bool.and_eq_true_iff.mpr ⟨hg.mustMove_imp hp hp' _ htarget, ?_⟩
      by_cases hba : b = a
      · subst hba
        rw [hg.heldA]
        simp
      · rw [hg.heldOther b hba, hg.supportOther b hba]
        rw [hg.noneHeld b] at hway
        exact hway

/-- If the grab creates the first block that only needs clearing away, it also
adds a block to the must-move set. -/
theorem Grab.movers_lt {d : Data} {s s' : State} {a : Nat} (hg : Grab d s s' a)
    (hp : Physical d s) (hp' : Physical d s')
    (hcf : needClearing d s = 0) (hcf' : 0 < needClearing d s') :
    movers d s + 1 ≤ movers d s' := by
  obtain ⟨x, hx, hxp⟩ := List.countP_pos_iff.mp hcf'
  obtain ⟨hmm', hun'⟩ := Bool.and_eq_true_iff.mp hxp
  have hxa : x = a := by
    by_contra hxa
    have hmm : mustMove d s x = true := by rwa [hg.mustMove_off hp hp' x hxa] at hmm'
    have hun : supportUnmet d s x = false := by
      have := hg.unmetOther x hxa
      simp only [Bool.not_eq_true'] at hun'
      rw [this] at hun'
      exact hun'
    have : 0 < needClearing d s :=
      countP_pos_of_mem _ _ x hx (by rw [hmm, hun]; rfl)
    omega
  rw [hxa] at hmm' hun' hx
  have hunA : supportUnmet d s a = false := by
    by_contra hc
    simp only [Bool.not_eq_false] at hc
    have := hg.unmetA hc
    rw [this] at hun'
    simp at hun'
  have hnot : mustMove d s a = false := by
    by_contra hc
    simp only [Bool.not_eq_false] at hc
    have : 0 < needClearing d s :=
      countP_pos_of_mem _ _ a (mem_blockList.mpr hg.aLt) (by rw [hc, hunA]; rfl)
    omega
  exact countP_succ_le_of_witness _ _ _ a (mem_blockList.mpr hg.aLt) (blockList_nodup d)
    hnot hmm' fun x _ hx => hg.mustMove_imp hp hp' x hx

/-- **A grab never drops the bound by more than one.** -/
theorem grab_step {d : Data} {s s' : State} {a : Nat} (hg : Grab d s s' a)
    (hp : Physical d s) (hp' : Physical d s') :
    moveBound d s ≤ moveBound d s' + 1 := by
  have he := moveBound_eq d s
  have he' := moveBound_eq d s'
  have hm := hg.movers_le hp hp'
  have hd := hg.detours_le hp hp'
  have hh := hg.held_zero
  have hh' := hg.held_one hp'
  have hcf : clearingFlag d s ≤ 1 := by unfold clearingFlag; split <;> omega
  have hcf' : clearingFlag d s' ≤ 1 := by unfold clearingFlag; split <;> omega
  by_cases hjump : clearingFlag d s = 0 ∧ clearingFlag d s' = 1
  · obtain ⟨h0, h1⟩ := hjump
    have hlt : movers d s + 1 ≤ movers d s' := by
      refine hg.movers_lt hp hp' ?_ ?_
      · unfold clearingFlag at h0
        split at h0 <;> omega
      · unfold clearingFlag at h1
        split at h1
        · assumption
        · omega
    omega
  · have : clearingFlag d s' ≤ clearingFlag d s := by
      by_cases h0 : clearingFlag d s = 0
      · have : clearingFlag d s' ≠ 1 := fun hc => hjump ⟨h0, hc⟩
        omega
      · omega
    omega

/-! ### A place

Putting the held block down is the direction that can take things away, and it is
where the analysis has to be read carefully.  The block may leave the must-move
set, taking its grab and its place with it; what the theorem needs is that
nothing else leaves with it, and in particular that no *other* block was counting
on it as a detour.  That is the goal-tower argument below: if `a` ends up where
the goal wants it and nothing under it has to move, then everything under it is
already in place, so a block that would have to detour around `a` would have to
be standing where one of those blocks stands.
-/

theorem mustMove_false_parts (d : Data) (s : State) (hp : Physical d s) (b : Nat)
    (h : mustMove d s b = false) :
    seed d s b = false ∧ ∀ c, supportOf d s b = some c → mustMove d s c = false := by
  rw [mustMove_unfold d s hp b] at h
  rw [Bool.or_eq_false_iff] at h
  refine ⟨h.1, fun c hc => ?_⟩
  have := h.2
  rw [hc] at this
  exact this

theorem seed_false_unmet {d : Data} {s : State} {b : Nat} (h : seed d s b = false) :
    supportUnmet d s b = false := by
  unfold seed at h
  simp only [Bool.or_eq_false_iff] at h
  exact h.1.1

theorem Place.held_one {d : Data} {s s' : State} {a : Nat} (hpl : Place d s s' a)
    (hp : Physical d s) : heldNeedsPlace d s = 1 := by
  unfold heldNeedsPlace
  rw [if_pos]
  exact List.any_eq_true.mpr ⟨a, mem_blockList.mpr hpl.aLt, by
    rw [hpl.mustMove_a hp, hpl.heldA]; rfl⟩

theorem Place.held_zero {d : Data} {s s' : State} {a : Nat} (hpl : Place d s s' a) :
    heldNeedsPlace d s' = 0 := by
  unfold heldNeedsPlace
  rw [if_neg]
  intro hany
  obtain ⟨b, -, hbp⟩ := List.any_eq_true.mp hany
  rw [hpl.noneHeld b] at hbp
  simp at hbp

theorem Place.movers_eq {d : Data} {s s' : State} {a : Nat} (hpl : Place d s s' a)
    (hp : Physical d s) (hp' : Physical d s') :
    movers d s' + 1 = movers d s + (if mustMove d s' a then 1 else 0) := by
  have hoff : ∀ x ∈ blockList d, x ≠ a → mustMove d s x = mustMove d s' x :=
    fun x _ hx => (hpl.mustMove_off hp hp' x hx).symm
  have := countP_off_eq (blockList d) (fun b => mustMove d s b) (fun b => mustMove d s' b)
    a (blockList_nodup d) (mem_blockList.mpr hpl.aLt) hoff
  simp only [hpl.mustMove_a hp, if_pos] at this
  show movers d s' + 1 = movers d s + _
  unfold movers
  omega

/-- Every block in `a`'s goal tower is settled, once `a` itself is. -/
theorem Place.goal_tower {d : Data} {s s' : State} {a : Nat} (hpl : Place d s s' a)
    (hp' : Physical d s') (hB : mustMove d s' a = false) :
    ∀ (i z : Nat), goalClimb d i a = some z →
      mustMove d s' z = false ∧
        ∀ f c, (d.blocks.getD z default).goalOn = some (f, c) → supportOf d s' z = some c := by
  intro i
  induction i with
  | zero =>
      intro z hz
      simp only [goalClimb, Option.some.injEq] at hz
      subst hz
      refine ⟨hB, fun f c hgo => ?_⟩
      exact hp'.placed a f c hgo (seed_false_unmet (mustMove_false_parts d s' hp' a hB).1)
  | succ i ih =>
      intro z hz
      rw [goalClimb] at hz
      cases hw : goalClimb d i a with
      | none => rw [hw] at hz; simp at hz
      | some w =>
          rw [hw] at hz
          simp only [Option.bind_some] at hz
          obtain ⟨hwmm, hwplaced⟩ := ih w hw
          -- `w`'s goal support is `z`, and `w` stands on it.
          obtain ⟨f, hgo⟩ := goalSup_eq_some hz
          have hsupw : supportOf d s' w = some z := hwplaced f z hgo
          have hzmm : mustMove d s' z = false :=
            (mustMove_false_parts d s' hp' w hwmm).2 z hsupw
          exact ⟨hzmm, fun f c hgoz =>
            hp'.placed z f c hgoz (seed_false_unmet (mustMove_false_parts d s' hp' z hzmm).1)⟩

/-- No other block was detouring around `a`, once `a` is settled. -/
theorem Place.target_ne {d : Data} {s s' : State} {a : Nat} (hpl : Place d s s' a)
    (hp : Physical d s) (hp' : Physical d s') (hB : mustMove d s' a = false)
    (b : Nat) (hb : b ≠ a) (hmm : mustMove d s b = true) (f : Fact)
    (hgo : (d.blocks.getD b default).goalOn = some (f, a))
    (hway : (isHeld d s b ||
      match supportOf d s b with
      | some sup => inGoalChain d b sup
      | none => false) = true) : False := by
  rw [hpl.heldOther b hb] at hway
  simp only [Bool.false_or] at hway
  cases hsup : supportOf d s b with
  | none => rw [hsup] at hway; simp at hway
  | some y =>
      rw [hsup] at hway
      unfold inGoalChain at hway
      obtain ⟨i, hi1, hin, hclimb⟩ := (inGoalChainAux_iff d _ b y).mp hway
      have hgs : goalSup d b = some a := by unfold goalSup; rw [hgo]; rfl
      cases i with
      | zero => omega
      | succ i =>
          rw [goalClimb_succ_left, hgs] at hclimb
          simp only [Option.bind_some] at hclimb
          cases i with
          | zero =>
              simp only [goalClimb, Option.some.injEq] at hclimb
              exact hpl.nothingOn b (by rw [hsup, hclimb])
          | succ j =>
              rw [goalClimb] at hclimb
              cases hw : goalClimb d j a with
              | none => rw [hw] at hclimb; simp at hclimb
              | some w =>
                  rw [hw] at hclimb
                  simp only [Option.bind_some] at hclimb
                  obtain ⟨fw, hgow⟩ := goalSup_eq_some hclimb
                  obtain ⟨hwmm, hwplaced⟩ := hpl.goal_tower hp' hB j w hw
                  have hsupw : supportOf d s' w = some y := hwplaced fw y hgow
                  have hsupb : supportOf d s' b = some y := by
                    rw [hpl.supportOther b hb, hsup]
                  have hbw : b = w := hp'.unique b w y hsupb hsupw
                  have hb' : mustMove d s' b = true := by
                    rw [hpl.mustMove_off hp hp' b hb]; exact hmm
                  rw [hbw, hwmm] at hb'
                  simp at hb'

/-- A block other than `a` keeps its detour, provided `a` keeps its place in the
must-move set for as long as that block needs it. -/
theorem Place.detour_transfer {d : Data} {s s' : State} {a : Nat} (hpl : Place d s s' a)
    (hp : Physical d s) (hp' : Physical d s') (b : Nat) (hb : b ≠ a)
    (hdet : detour d s b = true)
    (hcase : ∀ f c, (d.blocks.getD b default).goalOn = some (f, c) →
      mustMove d s c = true → mustMove d s' c = true) :
    detour d s' b = true := by
  unfold detour at hdet ⊢
  cases hgo : (d.blocks.getD b default).goalOn with
  | none => rw [hgo] at hdet; simp at hdet
  | some ft =>
      rw [hgo] at hdet
      obtain ⟨htarget, hway⟩ := Bool.and_eq_true_iff.mp hdet
      refine Bool.and_eq_true_iff.mpr ⟨hcase ft.1 ft.2 (by rw [hgo]) htarget, ?_⟩
      rw [hpl.noneHeld b, hpl.supportOther b hb]
      rw [hpl.heldOther b hb] at hway
      exact hway

/-- Settled, `a` needs no detour of its own. -/
theorem Place.detour_a_false {d : Data} {s s' : State} {a : Nat} (hpl : Place d s s' a)
    (hp : Physical d s) (hp' : Physical d s') (hB : mustMove d s' a = false) :
    detour d s a = false := by
  unfold detour
  cases hgo : (d.blocks.getD a default).goalOn with
  | none => rfl
  | some ft =>
      obtain ⟨f, tg⟩ := ft
      have hun' : supportUnmet d s' a = false :=
        seed_false_unmet (mustMove_false_parts d s' hp' a hB).1
      have hsup' : supportOf d s' a = some tg := hp'.placed a f tg (by rw [hgo]) hun'
      have hne : tg ≠ a := by
        intro hEq
        exact hp'.no_self a (by rw [hsup', hEq])
      have htf : mustMove d s' tg = false :=
        (mustMove_false_parts d s' hp' a hB).2 tg hsup'
      have hmf : mustMove d s tg = false := by
        rw [← hpl.mustMove_off hp hp' tg hne]; exact htf
      show (mustMove d s tg &&
        (isHeld d s a ||
          match supportOf d s a with
          | some sup => inGoalChain d a sup
          | none => false)) = false
      rw [hmf]
      simp

/-- If `a` ends up where the goal wants it, its own detour survives. -/
theorem Place.detour_a_placed {d : Data} {s s' : State} {a : Nat} (hpl : Place d s s' a)
    (hp : Physical d s) (hp' : Physical d s') (hun' : supportUnmet d s' a = false)
    (hdet : detour d s a = true) : detour d s' a = true := by
  unfold detour at hdet ⊢
  cases hgo : (d.blocks.getD a default).goalOn with
  | none => rw [hgo] at hdet; simp at hdet
  | some ft =>
      obtain ⟨f, tg⟩ := ft
      rw [hgo] at hdet
      obtain ⟨htarget, -⟩ := Bool.and_eq_true_iff.mp hdet
      have hsup' : supportOf d s' a = some tg := hp'.placed a f tg (by rw [hgo]) hun'
      have hne : tg ≠ a := by
        intro hEq
        exact hp'.no_self a (by rw [hsup', hEq])
      refine Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩
      · rw [← hpl.mustMove_off hp hp' tg hne] at htarget
        exact htarget
      · rw [hsup']
        have h1 : (1 : Nat) ≤ d.blocks.size := by have := hpl.aLt; omega
        have hchain : inGoalChain d a tg = true := by
          unfold inGoalChain
          refine (inGoalChainAux_iff d _ a tg).mpr ⟨1, Nat.le_refl _, h1, ?_⟩
          rw [goalClimb_succ_left]
          unfold goalSup
          rw [hgo]
          rfl
        show (isHeld d s' a || inGoalChain d a tg) = true
        rw [hchain]
        simp

theorem detour_parts {d : Data} {s : State} {b : Nat} (h : detour d s b = true) :
    ∃ f c, (d.blocks.getD b default).goalOn = some (f, c) ∧ mustMove d s c = true ∧
      (isHeld d s b ||
        match supportOf d s b with
        | some sup => inGoalChain d b sup
        | none => false) = true := by
  unfold detour at h
  cases hgo : (d.blocks.getD b default).goalOn with
  | none => rw [hgo] at h; simp at h
  | some ft =>
      obtain ⟨f, tg⟩ := ft
      rw [hgo] at h
      obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
      exact ⟨f, tg, rfl, h1, h2⟩

theorem Place.detours_le_succ {d : Data} {s s' : State} {a : Nat} (hpl : Place d s s' a)
    (hp : Physical d s) (hp' : Physical d s') (hA : mustMove d s' a = true) :
    detours d s ≤ detours d s' + 1 := by
  refine countP_le_succ_of_imp _ _ _ a (blockList_nodup d) fun b _ hb hbp => ?_
  obtain ⟨hmm, hdet⟩ := Bool.and_eq_true_iff.mp hbp
  refine Bool.and_eq_true_iff.mpr ⟨by rw [hpl.mustMove_off hp hp' b hb]; exact hmm, ?_⟩
  refine hpl.detour_transfer hp hp' b hb hdet fun f c hgo hc => ?_
  by_cases hca : c = a
  · rw [hca]; exact hA
  · rw [hpl.mustMove_off hp hp' c hca]; exact hc

theorem Place.detours_le_caseB {d : Data} {s s' : State} {a : Nat} (hpl : Place d s s' a)
    (hp : Physical d s) (hp' : Physical d s') (hB : mustMove d s' a = false) :
    detours d s ≤ detours d s' := by
  refine countP_le_of_imp _ _ _ fun b _ hbp => ?_
  obtain ⟨hmm, hdet⟩ := Bool.and_eq_true_iff.mp hbp
  by_cases hb : b = a
  · exfalso
    rw [hb] at hdet
    rw [hpl.detour_a_false hp hp' hB] at hdet
    simp at hdet
  · refine Bool.and_eq_true_iff.mpr ⟨by rw [hpl.mustMove_off hp hp' b hb]; exact hmm, ?_⟩
    refine hpl.detour_transfer hp hp' b hb hdet fun f c hgo hc => ?_
    by_cases hca : c = a
    · exfalso
      obtain ⟨f', c', hgo', -, hway⟩ := detour_parts hdet
      rw [hgo] at hgo'
      simp only [Option.some.injEq, Prod.mk.injEq] at hgo'
      exact hpl.target_ne hp hp' hB b hb hmm f (by rw [hgo, hca]) hway
    · rw [hpl.mustMove_off hp hp' c hca]; exact hc

theorem Place.detours_le_placed {d : Data} {s s' : State} {a : Nat} (hpl : Place d s s' a)
    (hp : Physical d s) (hp' : Physical d s') (hA : mustMove d s' a = true)
    (hun' : supportUnmet d s' a = false) : detours d s ≤ detours d s' := by
  refine countP_le_of_imp _ _ _ fun b _ hbp => ?_
  obtain ⟨hmm, hdet⟩ := Bool.and_eq_true_iff.mp hbp
  by_cases hb : b = a
  · rw [hb] at hdet ⊢
    exact Bool.and_eq_true_iff.mpr ⟨hA, hpl.detour_a_placed hp hp' hun' hdet⟩
  · refine Bool.and_eq_true_iff.mpr ⟨by rw [hpl.mustMove_off hp hp' b hb]; exact hmm, ?_⟩
    refine hpl.detour_transfer hp hp' b hb hdet fun f c hgo hc => ?_
    by_cases hca : c = a
    · rw [hca]; exact hA
    · rw [hpl.mustMove_off hp hp' c hca]; exact hc

/-- The only block that can become the first one merely in the way is `a` itself. -/
theorem Place.clearing_jump {d : Data} {s s' : State} {a : Nat} (hpl : Place d s s' a)
    (hp : Physical d s) (hp' : Physical d s') (hcf : needClearing d s = 0)
    (hcf' : 0 < needClearing d s') :
    mustMove d s' a = true ∧ supportUnmet d s' a = false := by
  obtain ⟨x, hx, hxp⟩ := List.countP_pos_iff.mp hcf'
  obtain ⟨hmm', hun'⟩ := Bool.and_eq_true_iff.mp hxp
  simp only [Bool.not_eq_true'] at hun'
  have hxa : x = a := by
    by_contra hxa
    have hmm : mustMove d s x = true := by rwa [hpl.mustMove_off hp hp' x hxa] at hmm'
    have hun : supportUnmet d s x = false := by
      rw [← hpl.unmetOther x hxa]; exact hun'
    have : 0 < needClearing d s := countP_pos_of_mem _ _ x hx (by rw [hmm, hun]; rfl)
    omega
  rw [hxa] at hmm' hun'
  exact ⟨hmm', hun'⟩

theorem Place.clearing_le_caseB {d : Data} {s s' : State} {a : Nat} (hpl : Place d s s' a)
    (hp : Physical d s) (hp' : Physical d s') (hB : mustMove d s' a = false) :
    needClearing d s' ≤ needClearing d s := by
  refine countP_le_of_imp _ _ _ fun b _ hbp => ?_
  obtain ⟨hmm', hun'⟩ := Bool.and_eq_true_iff.mp hbp
  by_cases hb : b = a
  · rw [hb, hB] at hmm'
    simp at hmm'
  · rw [← hpl.mustMove_off hp hp' b hb, ← hpl.unmetOther b hb]
    exact Bool.and_eq_true_iff.mpr ⟨hmm', hun'⟩

/-- **A place never drops the bound by more than one.** -/
theorem place_step {d : Data} {s s' : State} {a : Nat} (hpl : Place d s s' a)
    (hp : Physical d s) (hp' : Physical d s') :
    moveBound d s ≤ moveBound d s' + 1 := by
  have he := moveBound_eq d s
  have he' := moveBound_eq d s'
  have hh := hpl.held_one hp
  have hh' := hpl.held_zero
  have hmv := hpl.movers_eq hp hp'
  have hcfle : clearingFlag d s ≤ 1 := by unfold clearingFlag; split <;> omega
  have hcfle' : clearingFlag d s' ≤ 1 := by unfold clearingFlag; split <;> omega
  cases hA : mustMove d s' a with
  | true =>
      have hm : movers d s' = movers d s := by rw [hA] at hmv; simp at hmv; omega
      by_cases hjump : needClearing d s = 0 ∧ 0 < needClearing d s'
      · obtain ⟨h0, h1⟩ := hjump
        obtain ⟨-, hun'⟩ := hpl.clearing_jump hp hp' h0 h1
        have hd := hpl.detours_le_placed hp hp' hA hun'
        have hcf0 : clearingFlag d s = 0 := by unfold clearingFlag; rw [h0]; rfl
        omega
      · have hcfmono : clearingFlag d s' ≤ clearingFlag d s := by
          unfold clearingFlag
          split
          · rename_i h1
            rw [if_pos]
            by_contra hc
            exact hjump ⟨by omega, h1⟩
          · omega
        have hd := hpl.detours_le_succ hp hp' hA
        omega
  | false =>
      have hm : movers d s' + 1 = movers d s := by rw [hA] at hmv; simpa using hmv
      have hd := hpl.detours_le_caseB hp hp' hA
      have hc := hpl.clearing_le_caseB hp hp' hA
      have hcfmono : clearingFlag d s' ≤ clearingFlag d s := by
        unfold clearingFlag
        split
        · rw [if_pos (by omega)]
        · omega
      omega

/-! ### The bound vanishes at a goal

A goal state satisfies every goal fact, so no block's goal support is unmet, and
no block stands on one the goal wants clear or wants something else on.  The only
seed left is a block in the hand — and the analysis charges nothing for it,
because the grab it would need is already done and the place it would need is the
one that may be left undone.  So the bound is zero, which is what admissibility
needs and what the plan recorded as blocksworld's second assumption.
-/

/-- What a goal state looks like to the analysis. -/
structure GoalPosition (d : Data) (s : State) : Prop where
  /-- Every goal support holds. -/
  supportsMet : ∀ b, supportUnmet d s b = false
  /-- Nothing stands on a block the goal wants clear or wants another block on. -/
  notBlocking : ∀ b, blocking d s b = false
  /-- The hand holds at most one block. -/
  heldUnique : ∀ x y, isHeld d s x = true → isHeld d s y = true → x = y
  /-- Nothing rests on a block in the hand. -/
  nothingOnHeld : ∀ x y, isHeld d s y = true → supportOf d s x ≠ some y
  /-- The goal never asks for a block to stand on itself. -/
  noSelfGoal : ∀ b f, (d.blocks.getD b default).goalOn ≠ some (f, b)

theorem countP_le_one {α : Type} (l : List α) (p : α → Bool)
    (h : ∀ x ∈ l, ∀ y ∈ l, p x = true → p y = true → x = y) (hnd : l.Nodup) :
    l.countP p ≤ 1 := by
  induction l with
  | nil => simp
  | cons x rest ih =>
      rw [List.countP_cons]
      by_cases hp : p x
      · have hzero : rest.countP p = 0 := by
          rw [List.countP_eq_zero]
          intro y hy hpy
          exact (List.nodup_cons.mp hnd).1
            (by rw [h x (by simp) y (by simp [hy]) hp hpy]; exact hy)
        rw [hzero, if_pos hp]
      · rw [if_neg hp, Nat.add_zero]
        exact ih (fun a ha b hb => h a (by simp [ha]) b (by simp [hb]))
          (List.nodup_cons.mp hnd).2

/-- At a goal position the only block that must move is the one in the hand. -/
theorem GoalPosition.mustMove_iff_held {d : Data} {s : State} (hg : GoalPosition d s)
    (hp : Physical d s) (b : Nat) : mustMove d s b = isHeld d s b := by
  have hseed : ∀ x, seed d s x = isHeld d s x := by
    intro x
    unfold seed
    rw [hg.supportsMet x, hg.notBlocking x]
    simp
  refine Bool.eq_iff_iff.mpr ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨j, y, hy, hs⟩ := (mustMove_iff d s hp b).mp h
    rw [hseed y] at hs
    -- the seed is `b` itself: nothing rests on a held block
    cases j with
    | zero =>
        rw [climb_zero] at hy
        simp only [Option.some.injEq] at hy
        rw [hy]
        exact hs
    | succ j =>
        exfalso
        rw [climb_succ] at hy
        cases hc : climb d s j b with
        | none => rw [hc] at hy; simp at hy
        | some z =>
            rw [hc] at hy
            simp only [Option.bind_some] at hy
            exact hg.nothingOnHeld z y hs hy
  · exact (mustMove_iff d s hp b).mpr ⟨0, b, rfl, by rw [hseed b]; exact h⟩

theorem GoalPosition.moveBound_zero {d : Data} {s : State} (hg : GoalPosition d s)
    (hp : Physical d s) : moveBound d s = 0 := by
  have hmm := hg.mustMove_iff_held hp
  -- no block needs placing, and no detour is forced
  have hplace : needPlace d s = 0 := by
    unfold needPlace
    rw [List.countP_eq_zero]
    intro b _ hb
    rw [hg.supportsMet b] at hb
    simp at hb
  have hdet : detours d s = 0 := by
    unfold detours
    rw [List.countP_eq_zero]
    intro b _ hb
    obtain ⟨hmb, hdb⟩ := Bool.and_eq_true_iff.mp hb
    obtain ⟨f, c, hgo, hc, -⟩ := detour_parts hdb
    have hbheld : isHeld d s b = true := by rw [← hmm b]; exact hmb
    have hcheld : isHeld d s c = true := by rw [← hmm c]; exact hc
    exact hg.noSelfGoal b f (by rw [hgo, hg.heldUnique c b hcheld hbheld])
  have hone : movers d s ≤ 1 :=
    countP_le_one _ _ (fun x _ y _ hx hy =>
      hg.heldUnique x y (by rw [← hmm x]; exact hx) (by rw [← hmm y]; exact hy))
      (blockList_nodup d)
  have hsplit := needPlace_add_needClearing d s
  have heq := moveBound_eq d s
  have hheld : heldNeedsPlace d s = clearingFlag d s := by
    unfold heldNeedsPlace clearingFlag
    by_cases hc : 0 < needClearing d s
    · rw [if_pos hc, if_pos]
      obtain ⟨b, hb, hbp⟩ := List.countP_pos_iff.mp hc
      exact List.any_eq_true.mpr ⟨b, hb, by
        rw [(Bool.and_eq_true_iff.mp hbp).1, ← hmm b, (Bool.and_eq_true_iff.mp hbp).1]; rfl⟩
    · rw [if_neg hc, if_neg]
      intro hany
      obtain ⟨b, hb, hbp⟩ := List.any_eq_true.mp hany
      obtain ⟨hmb, -⟩ := Bool.and_eq_true_iff.mp hbp
      have : 0 < needClearing d s :=
        countP_pos_of_mem _ _ b hb (by rw [hmb, hg.supportsMet b]; rfl)
      omega
  have hcfle : clearingFlag d s ≤ movers d s := clearingFlag_le_movers d s
  rcases Nat.eq_zero_or_pos (needClearing d s) with h0 | hpos
  · have hcf0 : clearingFlag d s = 0 := by
      unfold clearingFlag
      rw [if_neg (by omega)]
    omega
  · have hcf1 : clearingFlag d s = 1 := by
      unfold clearingFlag
      rw [if_pos hpos]
    omega

end Planner.ExampleHeuristics.Blocksworld

/- -------------------------------------------------------------------------- -/
/-
Blocksworld, improved heuristic: goal-aware, consistent, admissible.

Two bounds on the same actions, combined with `max`: the unmet `clear` goals, and
the must-move analysis.  `Effect` says how one action may move the pair — every
schema is a grab or a place, and each moves either bound by at most one.

This is the domain the plan flagged as the outlier, and the must-move half is no
longer a hypothesis.  `Proofs/Domains/Blocksworld/MustMove.lean` proves it:

  * `grab_step` — `pickup` and `unstack` take a block into the empty hand, which
    only ever adds to the must-move set and only ever adds detours, and the one
    unit it takes away is the grab that block no longer needs;
  * `place_step` — `putdown` and `stack` put the held block down, which is the
    direction that can take things away.  The block may leave the must-move set
    with its grab and its place, but nothing else leaves with it: if it ends up
    where the goal wants it with nothing under it to move, then everything under
    it is already in place, so no other block could have been detouring around
    it without standing where one of those blocks stands;
  * `GoalPosition.moveBound_zero` — at a goal the only seed left is a block in
    the hand, and the analysis charges nothing for it, since its grab is already
    done and its place is the one that may be left undone.

What remains a hypothesis is the same thing every other domain assumes: that each
grounded operator really is one of the domain's schemas — here, that it induces a
`Grab` or a `Place` — together with the physical invariant of the states it runs
on: a block rests on at most one block, towers are finite, and a block whose goal
support holds really stands on that block.  Every schema preserves all three, and
the planner can check them of the initial state.
-/

namespace Planner.ExampleHeuristics.Blocksworld

open Planner

/-! ### The two quantities -/

/-- Unmet `clear` goals. -/
abbrev Cc (d : Data) (s : State) : Nat := clearBound d s
/-- The must-move bound. -/
abbrev Mc (d : Data) (s : State) : Nat := moveBound d s

/--
How an action may move the two quantities: a grab, or a place.  Both carry the
shape of the action in the analysis's own vocabulary, and the physical invariant
of the states either side, which is all the must-move theorems need.
-/
inductive Effect (d : Data) (s s' : State) : Prop
  | grab (a : Nat) (hshape : Grab d s s' a) (hp : Physical d s) (hp' : Physical d s')
      (hC : Cc d s ≤ Cc d s' + 1)
  | place (a : Nat) (hshape : Place d s s' a) (hp : Physical d s) (hp' : Physical d s')
      (hC : Cc d s ≤ Cc d s' + 1)

/-! ### Discharging the clear-goal component

A single action clears at most one block, so the count of unmet `clear` goals
falls by at most one.  That follows from the operator's add list alone, which is
decidable.
-/

theorem clearBound_le_succ (d : Data) {n : Nat} {op : Op} {s : State}
    (hnd : d.clearGoals.toList.Nodup) (x : Fact)
    (hnew : ∀ f ∈ d.clearGoals.toList, f ≠ x → (op.apply s).test f = true → s.test f = true) :
    Cc d s ≤ Cc d (op.apply s) + 1 := by
  show countMissing d.clearGoals s ≤ countMissing d.clearGoals (op.apply s) + 1
  rw [countMissing_eq, countMissing_eq]
  have := missing_le_succ hnd x hnew
  omega

/-! ### The step -/

private theorem step_arith (C M C' M' cost : Nat) (hcost : 1 ≤ cost)
    (hC : C ≤ C' + 1) (hM : M ≤ M' + 1) :
    max C M ≤ cost + max C' M' := by omega

/-- **One action moves the bound by at most one.** -/
theorem value_step (d : Data) (s s' : State) (he : Effect d s s')
    (cost : Nat) (hcost : 1 ≤ cost) : value d s ≤ cost + value d s' := by
  show max (Cc d s) (Mc d s) ≤ cost + max (Cc d s') (Mc d s')
  cases he with
  | grab a hshape hp hp' hC =>
      exact step_arith _ _ _ _ cost hcost hC (grab_step hshape hp hp')
  | place a hshape hp hp' hC =>
      exact step_arith _ _ _ _ cost hcost hC (place_step hshape hp hp')

/-! ### Assembly -/

/-- The `clear` branch of the value vanishes at a goal state, with no invariant needed. -/
theorem clearBound_eq_zero_of_goal (d : Data) (s : State)
    (hall : ∀ f ∈ d.clearGoals, s.test f = true) : clearBound d s = 0 := by
  unfold clearBound
  rw [countMissing_eq]
  exact missing_eq_zero fun f hf => hall f (by simpa using hf)

/--
Goal awareness.  The `clear` half is immediate; the must-move half is
`GoalPosition.moveBound_zero`, so what is assumed is only that a goal state is a
goal *position* — every goal support met, nothing standing on a block the goal
wants clear — and that it is physical.
-/
theorem improved_goalAware (t : Task)
    (hclear : ∀ f ∈ (compile t).clearGoals, f ∈ t.goal)
    (hgoal : ∀ s, (∀ f ∈ t.goal, s.test f = true) →
      GoalPosition (compile t) s ∧ Physical (compile t) s) :
    t.GoalAware (improved t).eval := by
  refine t.goalAware_of _ fun s _ hg => ?_
  obtain ⟨hgp, hp⟩ := hgoal s hg
  show max (clearBound (compile t) s) (moveBound (compile t) s) = 0
  rw [clearBound_eq_zero_of_goal _ s fun f hf => hg _ (hclear f hf),
    hgp.moveBound_zero hp]
  rfl

theorem improved_consistent (t : Task)
    (heff : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      Effect (compile t) s (op.apply s))
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost) :
    t.Consistent (improved t).eval :=
  t.consistent_of_ops _ fun op hop s hs happ =>
    value_step _ s _ (heff op hop s hs happ) op.cost (hcost op hop)

/-- Never overestimates the cost of reaching the goal. -/
theorem improved_admissible (t : Task)
    (hclear : ∀ f ∈ (compile t).clearGoals, f ∈ t.goal)
    (hgoal : ∀ s, (∀ f ∈ t.goal, s.test f = true) →
      GoalPosition (compile t) s ∧ Physical (compile t) s)
    (heff : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      Effect (compile t) s (op.apply s))
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost) :
    t.Admissible (improved t).eval :=
  t.admissible _ (improved_goalAware t hclear hgoal) (improved_consistent t heff hcost)

/-! ### Relative to an invariant

`Physical` and `GoalPosition` are not properties of every well-formed state: a
state that sets both `on(a, b)` and `on(b, a)` is well formed, and is neither.
So the hypotheses above can only be met on the states the search reaches, and
the versions below say so: they take an invariant `Q`, and ask for `Physical`
and the effect shape only where `Q` holds.  `Q` is what the planner checks of
the initial state and what every operator preserves.
-/

/-- Zero at every goal state the invariant admits. -/
theorem improved_goalAwareOn (t : Task) (Q : State → Prop)
    (hclear : ∀ f ∈ (compile t).clearGoals, f ∈ t.goal)
    (hgoal : ∀ s, Q s → (∀ f ∈ t.goal, s.test f = true) →
      GoalPosition (compile t) s ∧ Physical (compile t) s) :
    t.GoalAwareOn Q (improved t).eval := by
  refine t.goalAwareOn_of _ _ fun s _ hq hg => ?_
  obtain ⟨hgp, hp⟩ := hgoal s hq hg
  show max (clearBound (compile t) s) (moveBound (compile t) s) = 0
  rw [clearBound_eq_zero_of_goal _ s fun f hf => hg _ (hclear f hf),
    hgp.moveBound_zero hp]
  rfl

/-- Never falls by more than one action costs, along the transitions the
invariant admits. -/
theorem improved_consistentOn (t : Task) (Q : State → Prop)
    (heff : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → Q s → op.applicable s = true →
      Effect (compile t) s (op.apply s))
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost) :
    t.ConsistentOn Q (improved t).eval :=
  t.consistentOn_of_ops _ _ fun op hop s hs hq happ =>
    value_step _ s _ (heff op hop s hs hq happ) op.cost (hcost op hop)

/-- Never overestimates, on the states the invariant admits. -/
theorem improved_admissibleOn (t : Task) (Q : State → Prop)
    (hQ : ∀ s i s', State.WF t.numFacts s → Q s → t.step s i s' → Q s')
    (hclear : ∀ f ∈ (compile t).clearGoals, f ∈ t.goal)
    (hgoal : ∀ s, Q s → (∀ f ∈ t.goal, s.test f = true) →
      GoalPosition (compile t) s ∧ Physical (compile t) s)
    (heff : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → Q s → op.applicable s = true →
      Effect (compile t) s (op.apply s))
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost) :
    t.AdmissibleOn Q (improved t).eval :=
  t.admissibleOn _ _ hQ (improved_goalAwareOn t Q hclear hgoal)
    (improved_consistentOn t Q heff hcost)

end Planner.ExampleHeuristics.Blocksworld

/- -------------------------------------------------------------------------- -/
/-
Blocksworld, stated at the schema level.

`Effect` in `Improved.lean` already carries the schema shapes — `Grab` and
`Place` say what `pickup`/`unstack` and `putdown`/`stack` do to the vocabulary the
must-move analysis reads.  What it still assumes is the *clear*-goal half,
`Cc d s ≤ Cc d s' + 1`, a statement about the heuristic's own counter.

That half is replaced here by the syntactic fact behind it: an action makes at
most one `clear` goal newly true.  Every schema of the domain adds at most one
`clear` atom, so it holds for every instance.
-/

namespace Planner.ExampleHeuristics.Blocksworld

open Planner

/-- At most one `clear` goal becomes newly true. -/
def ClearsOne (d : Data) (s s' : State) : Prop :=
  ∃ x : Fact, ∀ f ∈ d.clearGoals, f ≠ x → s'.test f = true → s.test f = true

theorem clearBound_le_of_clearsOne {d : Data} {s s' : State}
    (hnd : d.clearGoals.toList.Nodup) (h : ClearsOne d s s') :
    Cc d s ≤ Cc d s' + 1 := by
  obtain ⟨x, hx⟩ := h
  show countMissing d.clearGoals s ≤ countMissing d.clearGoals s' + 1
  rw [countMissing_eq, countMissing_eq]
  have := missing_le_succ hnd x fun f hf hfx => hx f (by simpa using hf) hfx
  omega

/-- One action of the domain: a grab or a place, and at most one `clear` goal gained. -/
inductive SchemaStep (d : Data) (s s' : State) : Prop
  | grab (a : Nat) (hshape : Grab d s s' a) (hp : Physical d s) (hp' : Physical d s')
      (hclear : ClearsOne d s s')
  | place (a : Nat) (hshape : Place d s s' a) (hp : Physical d s) (hp' : Physical d s')
      (hclear : ClearsOne d s s')

theorem value_step_of_schema (d : Data) (s s' : State)
    (hnd : d.clearGoals.toList.Nodup) (he : SchemaStep d s s')
    (cost : Nat) (hcost : 1 ≤ cost) : value d s ≤ cost + value d s' := by
  refine value_step d s s' ?_ cost hcost
  cases he with
  | grab a hshape hp hp' hclear =>
      exact .grab a hshape hp hp' (clearBound_le_of_clearsOne hnd hclear)
  | place a hshape hp hp' hclear =>
      exact .place a hshape hp hp' (clearBound_le_of_clearsOne hnd hclear)

/-- Zero at every goal state, assuming only what the schemas do. -/
theorem improved_goalAware_of_schema (t : Task)
    (hclear : ∀ f ∈ (compile t).clearGoals, f ∈ t.goal)
    (hgoal : ∀ s, (∀ f ∈ t.goal, s.test f = true) →
      GoalPosition (compile t) s ∧ Physical (compile t) s) :
    t.GoalAware (improved t).eval := improved_goalAware t hclear hgoal

/-- And never falls by more than one action costs. -/
theorem improved_consistent_of_schema (t : Task)
    (hnd : (compile t).clearGoals.toList.Nodup)
    (hstep : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      SchemaStep (compile t) s (op.apply s))
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost) :
    t.Consistent (improved t).eval :=
  t.consistent_of_ops _ fun op hop s hs happ =>
    value_step_of_schema _ s _ hnd (hstep op hop s hs happ) op.cost (hcost op hop)

/-- Never overestimates, with the clear-goal count derived rather than assumed. -/
theorem improved_admissible_of_schema (t : Task)
    (hclear : ∀ f ∈ (compile t).clearGoals, f ∈ t.goal)
    (hnd : (compile t).clearGoals.toList.Nodup)
    (hgoal : ∀ s, (∀ f ∈ t.goal, s.test f = true) →
      GoalPosition (compile t) s ∧ Physical (compile t) s)
    (hstep : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      SchemaStep (compile t) s (op.apply s))
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost) :
    t.Admissible (improved t).eval :=
  t.admissible _ (improved_goalAware_of_schema t hclear hgoal)
    (improved_consistent_of_schema t hnd hstep hcost)

/-! ### Relative to an invariant

`SchemaStep` carries `Physical` on both sides, and `Physical` is not a property
of every well-formed state.  So the schema obligation is discharged only where
the invariant holds, and the results say so.
-/

theorem improved_goalAwareOn_of_schema (t : Task) (Q : State → Prop)
    (hclear : ∀ f ∈ (compile t).clearGoals, f ∈ t.goal)
    (hgoal : ∀ s, Q s → (∀ f ∈ t.goal, s.test f = true) →
      GoalPosition (compile t) s ∧ Physical (compile t) s) :
    t.GoalAwareOn Q (improved t).eval := improved_goalAwareOn t Q hclear hgoal

theorem improved_consistentOn_of_schema (t : Task) (Q : State → Prop)
    (hnd : (compile t).clearGoals.toList.Nodup)
    (hstep : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → Q s → op.applicable s = true →
      SchemaStep (compile t) s (op.apply s))
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost) :
    t.ConsistentOn Q (improved t).eval :=
  t.consistentOn_of_ops _ _ fun op hop s hs hq happ =>
    value_step_of_schema _ s _ hnd (hstep op hop s hs hq happ) op.cost (hcost op hop)

/-- **Blocks World's improved heuristic never overestimates**, on the states the
invariant admits, with every obligation reduced to what one schema does. -/
theorem improved_admissibleOn_of_schema (t : Task) (Q : State → Prop)
    (hQ : ∀ s i s', State.WF t.numFacts s → Q s → t.step s i s' → Q s')
    (hclear : ∀ f ∈ (compile t).clearGoals, f ∈ t.goal)
    (hnd : (compile t).clearGoals.toList.Nodup)
    (hgoal : ∀ s, Q s → (∀ f ∈ t.goal, s.test f = true) →
      GoalPosition (compile t) s ∧ Physical (compile t) s)
    (hstep : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → Q s → op.applicable s = true →
      SchemaStep (compile t) s (op.apply s))
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost) :
    t.AdmissibleOn Q (improved t).eval :=
  t.admissibleOn _ _ hQ (improved_goalAwareOn_of_schema t Q hclear hgoal)
    (improved_consistentOn_of_schema t Q hnd hstep hcost)

end Planner.ExampleHeuristics.Blocksworld

/- -------------------------------------------------------------------------- -/
/-
Blocks World's improved heuristic, closed on the task the grounder builds.

This discharges the four hypotheses of
`Proofs/Domains/Blocksworld/Schema.lean`:

  * every entry of `clearGoals` is a goal fact — `mem_goalFactsWith`;
  * they are distinct, because the goal facts of one predicate are;
  * a goal state is a `GoalPosition` and `Physical` — both are read off the
    state by `decide`-style case analysis on what a goal state guarantees;
  * every grounded operator is one of the four schemas and moves the analysis
    as a grab or a place.

The last is where this file earns its keep: an operator of a grounded blocksworld
task, read through `OpFacts`, has exactly the atoms its schema instance names,
and those name at most two blocks.  Case on which schema it is; each gives one
of the four step structures.
-/

namespace Planner.ExampleHeuristics.Blocksworld

open Planner Planner.Pddl

/-! ### The clear goals -/

/-- Every fact the compiled table lists as a `clear` goal is a goal fact. -/
theorem clearGoals_sub_goal (t : Task) :
    ∀ f ∈ (compile t).clearGoals, f ∈ t.goal := fun f hf =>
  (mem_goalFactsWith (preds := ["clear"]) hf).1

/-- The goal facts of one predicate are distinct, so `clearGoals` has no
repeats: it is a filter of the goal array, and the goal array lists each fact
once (a task's goal never names the same fact twice). -/
theorem clearGoals_nodup (t : Task) (hnd : t.goal.toList.Nodup) :
    ((compile t).clearGoals).toList.Nodup := by
  simp only [compile, Task.goalFactsWith, Array.toList_filter]
  exact List.Nodup.filter _ hnd

end Planner.ExampleHeuristics.Blocksworld

/- -------------------------------------------------------------------------- -/
/-
Blocks World: every grounded operator is one of the four schemas, and moves the
must-move analysis as the schema says.

The bridge reads one transition through `stepView`: the operator's atoms are its
schema instance's atoms under two object names.  Case on which schema; each of
the four gives a `Grab` or a `Place` over the compiled data, because every
quantity the analysis reads — support, hand, unmet goal support — is a test of
one fact whose atom the instance names.
-/

namespace Planner.ExampleHeuristics.Blocksworld

open Planner Planner.Pddl

variable {d : Domain} {p : Problem} {relevance : Bool}

/-! ### Reading the compiled data off atoms

Each entry of the per-block tables pairs a fact with the atom it names.  So a
state tests "block `b` is held" exactly when the abstracted state holds
`holding b` — provided the table has that entry.  The lemmas below read the
three dynamic families this way.
-/

/-- If the task numbers the atom, testing the fact whose name it is decides the
atom-level state. -/
theorem test_of_atom {t : Task} {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) {f : Fact} (hf : f < t.numFacts) :
    s.test f = σ (t.factNames.getD f default) :=
  (habs.numbered f hf).symm

/-- A fact whose atom does not move keeps its truth value. -/
theorem test_frame {t : Task} {s s' : State} {σ τ : AtomState}
    (habs : Abstracts t s σ) (habs' : Abstracts t s' τ)
    (hn : t.numFacts = t.factNames.size) {f : Fact} (hf : f < t.factNames.size)
    (h : τ (t.factNames.getD f default) = σ (t.factNames.getD f default)) :
    s'.test f = s.test f := by
  rw [test_of_atom habs' (by rw [hn]; exact hf),
    test_of_atom habs (by rw [hn]; exact hf)]
  exact h

/-- A fact whose atom is false afterwards is false afterwards. -/
theorem test_false {t : Task} {s' : State} {τ : AtomState}
    (habs' : Abstracts t s' τ) (hn : t.numFacts = t.factNames.size)
    {f : Fact} (hf : f < t.factNames.size)
    (h : τ (t.factNames.getD f default) = false) : s'.test f = false := by
  rw [test_of_atom habs' (by rw [hn]; exact hf)]; exact h

/-! ### The hand and the supports, read off the compiled tables

Each entry of a per-block table pairs a fact with the atom naming it.  The
lemmmas below say what those atoms are.
-/

/-- The atom `holding(b)`. -/
def holdAtom (b : Name) : GroundAtom := { pred := "holding", args := [b] }
/-- The atom `clear(b)`. -/
def clearAtom (b : Name) : GroundAtom := { pred := "clear", args := [b] }
/-- The atom `on-table(b)`. -/
def tableAtom (b : Name) : GroundAtom := { pred := "on-table", args := [b] }
/-- The atom `arm-empty`. -/
def emptyAtom : GroundAtom := { pred := "arm-empty", args := [] }
/-- The atom `on(b, u)`. -/
def onAtom (b u : Name) : GroundAtom := { pred := "on", args := [b, u] }

/-- Reading a mapped array in range is reading the function of the read. -/
theorem getD_map_lt {α β : Type} (f : α → β) (xs : Array α) (i : Nat)
    (db : β) (d : α) (hlt : i < xs.size) :
    (xs.map f).getD i db = f (xs.getD i d) := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (by simp only [Array.size_map]; exact hlt),
      Array.getElem?_eq_getElem hlt, Option.getD_some, Option.getD_some,
      Array.getElem_map]

/-- `compile` maps over the object list, so reading its table past the end gives
the default entry, whose optional slots are all empty.  A block index whose
entry names a fact is therefore an index into the object list. -/
theorem lt_objectNames_of_getD {t : Task} {i : Nat} {α : Type}
    (g : BlockInfo → Option α) (hg : g default = none)
    (hi : g ((compile t).blocks.getD i default) ≠ none) :
    i < t.objectNames.size := by
  by_contra hc
  refine hi ?_
  unfold compile
  rw [Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none_iff.2 (by simpa using hc), Option.getD_none]
  exact hg

/-- If the compiled table holds a fact at some block's `holdingFact`, that
fact names the atom `holding` of the block whose entry it is. -/
theorem holdingFact_names {t : Task} {f : Fact} {bname : Name} {i : Nat}
    (hi : ((compile t).blocks.getD i default).holdingFact = some f)
    (hb : t.objectNames.getD i default = bname) :
    t.factNames.getD f default = holdAtom bname := by
  have hlt := lt_objectNames_of_getD BlockInfo.holdingFact rfl (by rw [hi]; simp)
  unfold compile blockInfoOf supportFactOf at hi
  rw [getD_map_lt _ _ i _ default hlt, hb] at hi
  exact factsWith_find_args_map hi

/-- Any fact appearing in a block's `holdingFact` slot is a numbered fact. -/
theorem factLt_of_holding {t : Task} {f : Fact} {bname : Name} {i : Nat}
    (hi : ((compile t).blocks.getD i default).holdingFact = some f)
    (hb : t.objectNames.getD i default = bname)
    (hn : t.numFacts = t.factNames.size) :
    f < t.numFacts := by
  have hlt := lt_objectNames_of_getD BlockInfo.holdingFact rfl (by rw [hi]; simp)
  unfold compile blockInfoOf supportFactOf at hi
  rw [getD_map_lt _ _ i _ default hlt, hb] at hi
  rcases hx : ((t.factsWith "holding").find? fun (_, a) => a.args == [bname]) with _ | x
  · rw [hx] at hi; simp at hi
  · have hx' := Array.mem_of_find?_eq_some hx
    obtain ⟨hlt', hname, -⟩ := mem_factsWith hx'
    rw [hx] at hi
    simp only [Option.map_some, Option.some.injEq] at hi
    obtain ⟨rfl, rfl⟩ := hi
    rw [hn]; exact hlt'

/-- Reading the hand off the compiled table decides the atom-level state:
`isHeld` tests exactly the fact whose name is `holding(bname)`. -/
theorem isHeld_eq {t : Task} {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size)
    {bname : Name} (bi : Nat) (hb : t.objectNames.getD bi default = bname)
    (f : Fact)
    (hf : ((compile t).blocks.getD bi default).holdingFact = some f) :
    isHeld (compile t) s bi = σ (holdAtom bname) := by
  unfold isHeld
  simp only [hf]
  have hname : t.factNames.getD f default = holdAtom bname :=
    holdingFact_names hf hb
  rw [← hname]
  exact test_of_atom habs (factLt_of_holding hf hb hn)

/-- A found support entry in the compiled table reads back as the support. -/
theorem supportOf_found {t : Task} {s : State}
    (bi ui : Nat) (f : Fact)
    (hf : ((compile t).blocks.getD bi default).onFacts.find?
      (fun p => s.test p.1) = some (f, ui)) :
    supportOf (compile t) s bi = some ui :=
  congrArg _ hf

/-- No true on-fact of a block means it has no support. -/
theorem supportOf_none {t : Task} {s : State}
    (bi : Nat)
    (hf : ((compile t).blocks.getD bi default).onFacts.find?
      (fun p => s.test p.1) = none) :
    supportOf (compile t) s bi = none := congrArg _ hf

theorem onTableFact_names {t : Task} {f : Fact} {bname : Name} {i : Nat}
    (hi : ((compile t).blocks.getD i default).onTableFact = some f)
    (hb : t.objectNames.getD i default = bname) :
    t.factNames.getD f default = tableAtom bname := by
  have hlt := lt_objectNames_of_getD BlockInfo.onTableFact rfl (by rw [hi]; simp)
  unfold compile blockInfoOf supportFactOf at hi
  rw [getD_map_lt _ _ i _ default hlt, hb] at hi
  exact factsWith_find_args_map hi

/-- A block whose table has no `holding` fact is never held. -/
theorem isHeld_of_none {t : Task} {s : State} {bi : Nat}
    (hf : ((compile t).blocks.getD bi default).holdingFact = none) :
    isHeld (compile t) s bi = false := by unfold isHeld; rw [hf]

/-- **The hand reader, over atoms.**  A held block is held in the abstracted
state too. -/
theorem isHeld_holds {t : Task} {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) {bi : Nat}
    (h : isHeld (compile t) s bi = true) :
    σ (holdAtom (t.objectNames.getD bi default)) = true := by
  rcases hf : ((compile t).blocks.getD bi default).holdingFact with _ | f
  · rw [isHeld_of_none hf] at h; exact absurd h (by simp)
  · rw [← isHeld_eq habs hn bi rfl f hf]; exact h

/-- Only a block can be held. -/
theorem isHeld_lt {t : Task} {s : State} {bi : Nat}
    (h : isHeld (compile t) s bi = true) : bi < t.objectNames.size := by
  rcases hf : ((compile t).blocks.getD bi default).holdingFact with _ | f
  · rw [isHeld_of_none hf] at h; exact absurd h (by simp)
  · exact lt_objectNames_of_getD BlockInfo.holdingFact rfl (by rw [hf]; simp)

/-- `supportUnmet` spelled out: it is the two stored goal facts, each failing. -/
theorem supportUnmet_eq (d : Data) (s : State) (b : Nat) :
    supportUnmet d s b =
      ((d.blocks.getD b default).goalOn.elim false (fun q => !s.test q.1) ||
        (d.blocks.getD b default).goalOnTable.elim false (fun f => !s.test f)) := by
  dsimp only [supportUnmet]
  cases (d.blocks.getD b default).goalOn <;>
    cases (d.blocks.getD b default).goalOnTable <;> rfl

/-- A block's goal support is met when both goal facts its table stores are
true.  `supportUnmet` reads no other fact. -/
theorem supportUnmet_eq_false {d : Data} {s : State} {b : Nat}
    (h1 : ∀ f c, (d.blocks.getD b default).goalOn = some (f, c) → s.test f = true)
    (h2 : ∀ f, (d.blocks.getD b default).goalOnTable = some f → s.test f = true) :
    supportUnmet d s b = false := by
  simp only [supportUnmet]
  rcases hgo : (d.blocks.getD b default).goalOn with _ | ⟨f, c⟩ <;>
    rcases hgt : (d.blocks.getD b default).goalOnTable with _ | g
  · simp
  · simp [h2 _ hgt]
  · simp [h1 _ _ hgo]
  · simp [h1 _ _ hgo, h2 _ hgt]

/-- `supportUnmet` reads only the two goal facts the block's table stores, so
two states that agree on both agree on it. -/
theorem supportUnmet_congr {d : Data} {s s' : State} {b : Nat}
    (h1 : ∀ f c, (d.blocks.getD b default).goalOn = some (f, c) →
      s'.test f = s.test f)
    (h2 : ∀ f, (d.blocks.getD b default).goalOnTable = some f →
      s'.test f = s.test f) :
    supportUnmet d s' b = supportUnmet d s b := by
  simp only [supportUnmet]
  rcases hgo : (d.blocks.getD b default).goalOn with _ | ⟨f, c⟩ <;>
    rcases hgt : (d.blocks.getD b default).goalOnTable with _ | g
  · simp
  · simp [h2 _ hgt]
  · simp [h1 _ _ hgo]
  · simp [h1 _ _ hgo, h2 _ hgt]

/--
And an unmet goal support stays unmet, as long as no goal fact the block stores
*gains* truth.  Read with the two states swapped this is the `Place` direction:
there it is the earlier state whose facts must not be truer.
-/
theorem supportUnmet_mono {d : Data} {s s' : State} {b : Nat}
    (h1 : ∀ f c, (d.blocks.getD b default).goalOn = some (f, c) →
      s'.test f = true → s.test f = true)
    (h2 : ∀ f, (d.blocks.getD b default).goalOnTable = some f →
      s'.test f = true → s.test f = true)
    (h : supportUnmet d s b = true) : supportUnmet d s' b = true := by
  rw [supportUnmet_eq] at h ⊢
  revert h
  rcases hgo : (d.blocks.getD b default).goalOn with _ | ⟨f, c⟩ <;>
    rcases hgt : (d.blocks.getD b default).goalOnTable with _ | g <;>
    simp only [Option.elim] <;> intro h
  · exact h
  · rcases hg : s'.test g with _ | _
    · simp [hg]
    · rw [h2 g hgt hg] at h; simp at h
  · rcases hf : s'.test f with _ | _
    · simp [hf]
    · rw [h1 f c hgo hf] at h; simp at h
  · rcases hf : s'.test f with _ | _
    · simp [hf]
    · rcases hg : s'.test g with _ | _
      · simp [hg]
      · rw [h1 f c hgo hf, h2 g hgt hg] at h; simp at h

/-- Past the last block the compiled table is the default entry. -/
theorem blocks_getD_out {t : Task} {x : Nat} (hx : t.objectNames.size ≤ x) :
    (compile t).blocks.getD x default = default := by
  unfold compile
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none_iff.2 (by simpa using hx),
    Option.getD_none]

/-! ### The `on` table of one block

`onEntriesOf` keeps the `on` facts whose first argument is the block, and pairs
each with the index of the block underneath.  So every entry is a numbered fact
naming `on(b, c)`, with `c` the object that index picks out.  That is all the
support reader needs: `supportOf` is a `find?` over this table, and the two
`find?` lemmas of `Proofs/FactTables.lean` turn it into a question about atoms.
-/

/-- The object an index found by `findIdx?` picks out is the one searched for. -/
theorem objectName_of_findIdx {t : Task} {c : Name} {ci : Nat}
    (h : t.objectNames.findIdx? (· == c) = some ci) :
    t.objectNames.getD ci default = c := by
  obtain ⟨hlt, hp, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp h
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt, Option.getD_some]
  exact eq_of_beq hp

/-- Every entry of a block's `on` table is a numbered fact naming `on(b, c)`. -/
theorem mem_onEntriesOf {t : Task} {b : Name} {f : Fact} {ci : Nat}
    (h : (f, ci) ∈ onEntriesOf (fun c => t.objectNames.findIdx? (· == c)) b
      (t.factsWith "on")) :
    f < t.factNames.size ∧
      t.factNames.getD f default = onAtom b (t.objectNames.getD ci default) ∧
      ci < t.objectNames.size := by
  obtain ⟨⟨g, a⟩, hy, hval⟩ := Array.mem_filterMap.mp h
  obtain ⟨hlt, hname, hpred⟩ := mem_factsWith hy
  dsimp only at hval
  rcases hargs : a.args with _ | ⟨x, rest⟩
  · rw [hargs] at hval; simp at hval
  rcases rest with _ | ⟨c, rest⟩
  · rw [hargs] at hval; simp at hval
  rcases rest with _ | ⟨w, rest⟩
  case cons.cons.cons => rw [hargs] at hval; simp at hval
  rw [hargs] at hval
  dsimp only at hval
  by_cases hx : x == b
  · rw [if_pos hx] at hval
    rcases hidx : t.objectNames.findIdx? (· == c) with _ | j
    · rw [hidx] at hval; simp at hval
    · rw [hidx] at hval
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hval
      obtain ⟨rfl, rfl⟩ := hval
      refine ⟨hlt, ?_, (Array.findIdx?_eq_some_iff_getElem.mp hidx).1⟩
      rw [hname, objectName_of_findIdx hidx]
      show a = { pred := "on", args := [b, c] }
      rw [← hpred, ← eq_of_beq hx, ← hargs]
  · rw [if_neg hx] at hval; simp at hval

/-- The entries of a block's `on` table are numbered facts, which is the range
condition the two `find?` lemmas ask for. -/
theorem onFacts_ok {t : Task} (bi : Nat) :
    ∀ y ∈ ((compile t).blocks.getD bi default).onFacts, y.1 < t.factNames.size := by
  intro y hy
  by_cases hlt : bi < t.objectNames.size
  · unfold compile blockInfoOf at hy
    rw [getD_map_lt _ _ bi _ default hlt] at hy
    exact (mem_onEntriesOf (by simpa using hy)).1
  · exfalso
    unfold compile at hy
    rw [Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_none_iff.2 (by simpa using hlt), Option.getD_none] at hy
    exact absurd hy (by simp [show (default : BlockInfo).onFacts = #[] from rfl])

/-- The atom a found support entry names. -/
theorem onFacts_names {t : Task} {bi ci : Nat} {f : Fact} {bname : Name}
    (hb : t.objectNames.getD bi default = bname)
    (hy : (f, ci) ∈ ((compile t).blocks.getD bi default).onFacts) :
    t.factNames.getD f default = onAtom bname (t.objectNames.getD ci default) := by
  have hlt : bi < t.objectNames.size := by
    by_contra hc
    unfold compile at hy
    rw [Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_none_iff.2 (by simpa using hc), Option.getD_none] at hy
    exact absurd hy (by simp [show (default : BlockInfo).onFacts = #[] from rfl])
  unfold compile blockInfoOf at hy
  rw [getD_map_lt _ _ bi _ default hlt, hb] at hy
  exact (mem_onEntriesOf (by simpa using hy)).2.1

/-- **The support reader, over atoms.**  If the compiled table finds a true
`on` fact for `b`, the abstracted state holds `on(b, c)` for the block `c` the
entry names. -/
theorem supportOf_holds {t : Task} {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size)
    {bi ci : Nat} {bname : Name} (hb : t.objectNames.getD bi default = bname)
    (h : supportOf (compile t) s bi = some ci) :
    ∃ f, (f, ci) ∈ ((compile t).blocks.getD bi default).onFacts ∧
      σ (onAtom bname (t.objectNames.getD ci default)) = true := by
  unfold supportOf at h
  rcases hx : ((compile t).blocks.getD bi default).onFacts.find?
      (fun p => s.test p.1) with _ | x
  · rw [hx] at h; simp at h
  · rw [hx] at h
    simp only [Option.map_some, Option.some.injEq] at h
    obtain ⟨hmem, hσ⟩ := find?_holds habs hn (onFacts_ok bi) hx
    subst h
    refine ⟨x.1, by simpa using hmem, ?_⟩
    rw [← onFacts_names hb (by simpa using hmem)]
    exact hσ

/-- **And the other way.**  If the table finds nothing, the abstracted state
holds no `on(b, c)` the table lists. -/
theorem supportOf_none_holds {t : Task} {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size)
    {bi : Nat} {bname : Name} (hb : t.objectNames.getD bi default = bname)
    (h : supportOf (compile t) s bi = none) :
    ∀ y ∈ ((compile t).blocks.getD bi default).onFacts,
      σ (onAtom bname (t.objectNames.getD y.2 default)) = false := by
  intro y hy
  have hx : ((compile t).blocks.getD bi default).onFacts.find?
      (fun p => s.test p.1) = none := by
    unfold supportOf at h
    exact Option.map_eq_none_iff.mp h
  rw [← onFacts_names (ci := y.2) hb (by simpa using hy)]
  exact find?_none_holds habs hn (onFacts_ok bi) hx y hy

/-- **The other direction.**  A numbered `on(b, c)` fact whose second block is an
object is an entry of `b`'s table.  `factsWith` lists every numbered atom of its
predicate, and `onEntriesOf` drops only the ones with another block on top or an
unknown block underneath. -/
theorem mem_onEntriesOf_of {t : Task} {b c : Name} {f : Fact} {ci : Nat}
    (hf : f < t.factNames.size) (hname : t.factNames.getD f default = onAtom b c)
    (hidx : t.objectNames.findIdx? (· == c) = some ci) :
    (f, ci) ∈ onEntriesOf (fun c => t.objectNames.findIdx? (· == c)) b
      (t.factsWith "on") := by
  refine Array.mem_filterMap.mpr ⟨(f, onAtom b c),
    mem_factsWith_of_named hf hname rfl, ?_⟩
  show (match (onAtom b c).args with
    | [x, c] => if x == b then (t.objectNames.findIdx? (· == c)).map ((f, ·)) else none
    | _ => none) = some (f, ci)
  simp only [onAtom, beq_self_eq_true, if_pos, hidx, Option.map_some]

/-- The same, read through the compiled table at a block's index. -/
theorem mem_onFacts_of {t : Task} {b c : Name} {f : Fact} {bi ci : Nat}
    (hbi : bi < t.objectNames.size) (hb : t.objectNames.getD bi default = b)
    (hf : f < t.factNames.size) (hname : t.factNames.getD f default = onAtom b c)
    (hidx : t.objectNames.findIdx? (· == c) = some ci) :
    (f, ci) ∈ ((compile t).blocks.getD bi default).onFacts := by
  unfold compile blockInfoOf
  rw [getD_map_lt _ _ bi _ default hbi, hb]
  exact mem_onEntriesOf_of hf hname hidx

/-! ### The tables have the entries the atoms call for

The readers above say what a table entry means.  For the step proof the other
direction is needed as well: if the task numbers the atom, the table has the
entry.  `supportFactOf` searches by arguments, so a numbered atom of the right
predicate and argument makes the search succeed.
-/

/-- **A numbered one-argument atom is found by `supportFactOf`.** -/
theorem supportFactOf_some {t : Task} {pred b : Name} {f : Fact}
    (hf : f < t.factNames.size)
    (hname : t.factNames.getD f default = { pred := pred, args := [b] }) :
    ∃ g, supportFactOf (t.factsWith pred) b = some g ∧
      t.factNames.getD g default = { pred := pred, args := [b] } := by
  have hmem := mem_factsWith_of_named hf hname rfl
  rcases hx : (t.factsWith pred).find? (fun y => y.2.args == [b]) with _ | x
  · exact absurd (Array.find?_eq_none.mp hx (f, { pred := pred, args := [b] }) hmem)
      (by simp)
  · exact ⟨x.1, by unfold supportFactOf; rw [hx]; rfl, factsWith_find_args hx⟩

/-- The compiled table has a `holding` entry for every block whose `holding`
atom the task numbers. -/
theorem holdingFact_some {t : Task} {b : Name} {bi : Nat} {f : Fact}
    (hbi : bi < t.objectNames.size) (hb : t.objectNames.getD bi default = b)
    (hf : f < t.factNames.size) (hname : t.factNames.getD f default = holdAtom b) :
    ∃ g, ((compile t).blocks.getD bi default).holdingFact = some g ∧
      t.factNames.getD g default = holdAtom b := by
  obtain ⟨g, hg, hgn⟩ := supportFactOf_some (pred := "holding") hf hname
  refine ⟨g, ?_, hgn⟩
  unfold compile blockInfoOf
  rw [getD_map_lt _ _ bi _ default hbi, hb]
  exact hg

/-- The same for `on-table`. -/
theorem onTableFact_some {t : Task} {b : Name} {bi : Nat} {f : Fact}
    (hbi : bi < t.objectNames.size) (hb : t.objectNames.getD bi default = b)
    (hf : f < t.factNames.size) (hname : t.factNames.getD f default = tableAtom b) :
    ∃ g, ((compile t).blocks.getD bi default).onTableFact = some g ∧
      t.factNames.getD g default = tableAtom b := by
  obtain ⟨g, hg, hgn⟩ := supportFactOf_some (pred := "on-table") hf hname
  refine ⟨g, ?_, hgn⟩
  unfold compile blockInfoOf
  rw [getD_map_lt _ _ bi _ default hbi, hb]
  exact hg

/-! ### Reading the hand both ways, and a framed step

The step proof needs `isHeld` in both directions, and it needs to know that a
step which touches no `on` atom leaves every support where it was.
-/

/-- A block the abstracted state does not hold is not held. -/
theorem isHeld_false_of {t : Task} {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) {bi : Nat}
    (h : σ (holdAtom (t.objectNames.getD bi default)) = false) :
    isHeld (compile t) s bi = false := by
  rcases hf : ((compile t).blocks.getD bi default).holdingFact with _ | f
  · exact isHeld_of_none hf
  · rw [isHeld_eq habs hn bi rfl f hf]; exact h

/-- And one it does hold is held, once the table has the entry. -/
theorem isHeld_true_of {t : Task} {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) {bi : Nat} {f : Fact}
    (hf : ((compile t).blocks.getD bi default).holdingFact = some f)
    (h : σ (holdAtom (t.objectNames.getD bi default)) = true) :
    isHeld (compile t) s bi = true := by
  rw [isHeld_eq habs hn bi rfl f hf]; exact h

/-- **A step that touches no `on` atom leaves every support alone.** -/
theorem supportOf_congr {t : Task} {s s' : State} {σ τ : AtomState}
    (habs : Abstracts t s σ) (habs' : Abstracts t s' τ)
    (hn : t.numFacts = t.factNames.size) (bi : Nat)
    (hframe : ∀ c, τ (onAtom (t.objectNames.getD bi default) c)
      = σ (onAtom (t.objectNames.getD bi default) c)) :
    supportOf (compile t) s' bi = supportOf (compile t) s bi := by
  unfold supportOf
  refine congrArg _ (array_find?_congr _ _ _ fun y hy => ?_)
  obtain ⟨f, ci⟩ := y
  show s'.test f = s.test f
  have hlt : f < t.numFacts := by rw [hn]; exact onFacts_ok bi (f, ci) hy
  rw [test_of_atom habs' hlt, test_of_atom habs hlt,
    onFacts_names (ci := ci) rfl hy, hframe]

/-- **No true `on` atom means no support.** -/
theorem supportOf_none_of {t : Task} {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) {bi : Nat}
    (h : ∀ c, σ (onAtom (t.objectNames.getD bi default) c) = false) :
    supportOf (compile t) s bi = none := by
  rcases hs : supportOf (compile t) s bi with _ | ci
  · rfl
  · obtain ⟨-, -, hσ⟩ := supportOf_holds habs hn rfl hs
    rw [h] at hσ
    exact absurd hσ (by simp)

/-! ### Supports are block indices

The index a support entry carries comes from `findIdx?` over the object list, so
it is an index into that list — which is what `Physical` needs to count towers
against the number of blocks.
-/

/-- The number of compiled blocks is the number of objects. -/
theorem blocks_size (t : Task) : (compile t).blocks.size = t.objectNames.size := by
  unfold compile; simp

/-- The index in a support entry is a block index. -/
theorem onFacts_snd_lt {t : Task} {bi : Nat} {y : Fact × Nat}
    (hy : y ∈ ((compile t).blocks.getD bi default).onFacts) :
    y.2 < (compile t).blocks.size := by
  have hlt : bi < t.objectNames.size := by
    by_contra hc
    unfold compile at hy
    rw [Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_none_iff.2 (by simpa using hc), Option.getD_none] at hy
    exact absurd hy (by simp [show (default : BlockInfo).onFacts = #[] from rfl])
  unfold compile blockInfoOf at hy
  rw [getD_map_lt _ _ bi _ default hlt] at hy
  rw [blocks_size]
  exact (mem_onEntriesOf (by simpa using hy)).2.2

/-- **A block's support is a block.** -/
theorem supportOf_lt {t : Task} {s : State} {x c : Nat}
    (h : supportOf (compile t) s x = some c) : c < (compile t).blocks.size := by
  unfold supportOf at h
  rcases hx : ((compile t).blocks.getD x default).onFacts.find?
      (fun p => s.test p.1) with _ | y
  · rw [hx] at h; simp at h
  · rw [hx] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    exact onFacts_snd_lt (Array.mem_of_find?_eq_some hx)

end Planner.ExampleHeuristics.Blocksworld

/- -------------------------------------------------------------------------- -/
/-
Towers end.

`Physical.grounded` says a chain of `blocks.size` supports runs out.  That is not
a local condition on the state — a state holding `on(a, b)` and `on(b, a)` breaks
it while satisfying every other field — so it has to come from acyclicity: no
block stands above itself.

The bridge is pigeonhole.  A chain of `n` steps out of a block visits `n + 1`
blocks, and there are only `n` of them, so two positions of the chain hold the
same block.  The stretch between those two positions is a chain from that block
back to itself, which acyclicity forbids.
-/

namespace Planner.ExampleHeuristics.Blocksworld

open Planner

/-- Climbing `i + k` steps is climbing `i`, then `k` more. -/
theorem climb_add (d : Data) (s : State) (b i : Nat) :
    ∀ k, climb d s (i + k) b = (climb d s i b).bind (climb d s k) := by
  intro k
  induction k with
  | zero => cases h : climb d s i b <;> simp [climb]
  | succ k ih =>
      rw [show i + (k + 1) = (i + k) + 1 from rfl, climb_succ, ih, Option.bind_assoc]
      cases h : climb d s i b with
      | none => simp
      | some z => simp [climb_succ]

/-- No block stands above itself, read as block indices. -/
def AcyclicIdx (d : Data) (s : State) : Prop :=
  ∀ b j, 0 < j → climb d s j b ≠ some b

/--
**Towers end.**  If no block stands above itself, every support is a block, and
nothing that is not a block has a support, then a chain of `blocks.size` steps
runs out.

The last two hypotheses are what `compile` gives: the index in a support entry
comes from `findIdx?` over the object list, and a table read past its end is the
empty one.
-/
theorem grounded_of_acyclic (d : Data) (s : State) (hpos : 0 < d.blocks.size)
    (hsup : ∀ x c, supportOf d s x = some c → c < d.blocks.size)
    (hout : ∀ x, d.blocks.size ≤ x → supportOf d s x = none)
    (hac : AcyclicIdx d s) (b : Nat) :
    climb d s d.blocks.size b = none := by
  by_contra hne
  have hall : ∀ i, i ≤ d.blocks.size → climb d s i b ≠ none := fun i hi hcon =>
    hne (climb_none_mono d s b i d.blocks.size hi hcon)
  -- The chain starts at a block: otherwise it stops after one step.
  have hb : b < d.blocks.size := by
    by_contra hbc
    refine hall 1 hpos ?_
    rw [climb_succ_left, hout b (by omega)]
    rfl
  -- Every position of the chain holds a block.
  have hval : ∀ i, i ≤ d.blocks.size → (climb d s i b).getD 0 < d.blocks.size := by
    intro i hi
    rcases i with _ | i
    · rw [climb_zero]; exact hb
    · rcases hc : climb d s (i + 1) b with _ | z
      · exact absurd hc (hall _ hi)
      · rw [climb_succ] at hc
        rcases hc2 : climb d s i b with _ | w
        · rw [hc2] at hc; simp at hc
        · rw [hc2, Option.bind_some] at hc
          simpa using hsup w z hc
  -- Two positions hold the same block, and the stretch between them is a cycle.
  have key : ∀ i j, i < j → j ≤ d.blocks.size →
      (climb d s i b).getD 0 = (climb d s j b).getD 0 → False := by
    intro i j hij hjn heq
    rcases hci : climb d s i b with _ | z
    · exact hall i (by omega) hci
    rcases hcj : climb d s j b with _ | w
    · exact hall j hjn hcj
    rw [hci, hcj] at heq
    simp only [Option.getD_some] at heq
    subst heq
    obtain ⟨k, rfl⟩ : ∃ k, j = i + k := ⟨j - i, by omega⟩
    have hsplit : climb d s (i + k) b = climb d s k z := by
      rw [climb_add, hci, Option.bind_some]
    rw [hcj] at hsplit
    exact hac z k (by omega) hsplit.symm
  obtain ⟨i, hi, j, hj, hne', heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := Finset.range (d.blocks.size + 1)) (t := Finset.range d.blocks.size)
      (f := fun i => (climb d s i b).getD 0)
      (by simp)
      (fun i hi => Finset.mem_range.mpr (hval i (by
        have := Finset.mem_range.mp hi; omega)))
  simp only [Finset.mem_range] at hi hj
  rcases Nat.lt_or_ge i j with h | h
  · exact key i j h (by omega) heq
  · exact key j i (by omega) (by omega) heq.symm

/-! ### For a compiled task

The two range hypotheses are properties of `compile`: a support index comes from
`findIdx?` over the object list, and a table read past its end is the empty one.
-/

/-- Past the last block the compiled table is empty, so there is no support. -/
theorem supportOf_out {t : Task} {s : State} {x : Nat}
    (hx : (compile t).blocks.size ≤ x) : supportOf (compile t) s x = none := by
  unfold supportOf
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none_iff.2 hx, Option.getD_none]
  simp [show (default : BlockInfo).onFacts = #[] from rfl]

/-- Only a block has a support. -/
theorem supportOf_fst_lt {t : Task} {s : State} {x c : Nat}
    (h : supportOf (compile t) s x = some c) : x < (compile t).blocks.size := by
  by_contra hc
  rw [supportOf_out (by omega)] at h
  exact absurd h (by simp)

/-- **`Physical.grounded` for a compiled task**, from acyclicity alone. -/
theorem grounded_compile (t : Task) (s : State) (hpos : 0 < (compile t).blocks.size)
    (hac : AcyclicIdx (compile t) s) (b : Nat) :
    climb (compile t) s (compile t).blocks.size b = none :=
  grounded_of_acyclic _ s hpos (fun _ _ => supportOf_lt) (fun _ => supportOf_out) hac b

end Planner.ExampleHeuristics.Blocksworld

/- -------------------------------------------------------------------------- -/
/-
Which domain a Blocks World task came from.

The equation on `actions` fixes the four schemas exactly as the parser produces
them.  The remaining lemmas expose their instantiated atoms, which lets the
heuristic proof reason about one lifted transition without mentioning grounding
or fact numbers.
-/

namespace Planner.Lifted.Blocksworld

open Planner Planner.Pddl

/-! ### The domain's atoms -/

abbrev holding (x : Name) : GroundAtom := { pred := "holding", args := [x] }
abbrev clearA (x : Name) : GroundAtom := { pred := "clear", args := [x] }
abbrev onTable (x : Name) : GroundAtom := { pred := "on-table", args := [x] }
abbrev armEmpty : GroundAtom := { pred := "arm-empty", args := [] }
abbrev on (x c : Name) : GroundAtom := { pred := "on", args := [x, c] }

/-! ### The schemas, as the parser produces them -/

abbrev objP (n : Name) : TypedName := { name := n, type := "object" }

abbrev holdingV (x : Name) : Atom := { pred := "holding", args := [.var x] }
abbrev clearV (x : Name) : Atom := { pred := "clear", args := [.var x] }
abbrev onTableV (x : Name) : Atom := { pred := "on-table", args := [.var x] }
abbrev armEmptyV : Atom := { pred := "arm-empty", args := [] }
abbrev onV (x c : Name) : Atom := { pred := "on", args := [.var x, .var c] }

abbrev pickupA : Action := Planner.GeneratedDomains.Blocksworld.action0
abbrev putdownA : Action := Planner.GeneratedDomains.Blocksworld.action1
abbrev stackA : Action := Planner.GeneratedDomains.Blocksworld.action2
abbrev unstackA : Action := Planner.GeneratedDomains.Blocksworld.action3

abbrev BlocksworldDomain (d : Domain) : Prop :=
  d.actions = Planner.GeneratedDomains.Blocksworld.actions

/-! ### Every predicate the value reads is dynamic -/

theorem holding_dynamic {d : Domain} (hd : BlocksworldDomain d) :
    (staticPredicates d).contains "holding" = false :=
  not_static_of_mem_add (a := pickupA) (by rw [hd]; simp)
    (y := holdingV "?ob") (by simp [pickupA])

theorem clear_dynamic {d : Domain} (hd : BlocksworldDomain d) :
    (staticPredicates d).contains "clear" = false :=
  not_static_of_mem_del (a := stackA) (by rw [hd]; simp)
    (y := clearV "?underob") (by simp [stackA])

theorem onTable_dynamic {d : Domain} (hd : BlocksworldDomain d) :
    (staticPredicates d).contains "on-table" = false :=
  not_static_of_mem_add (a := putdownA) (by rw [hd]; simp)
    (y := onTableV "?ob") (by simp [putdownA])

theorem armEmpty_dynamic {d : Domain} (hd : BlocksworldDomain d) :
    (staticPredicates d).contains "arm-empty" = false :=
  not_static_of_mem_add (a := putdownA) (by rw [hd]; simp)
    (y := armEmptyV) (by simp [putdownA])

theorem on_dynamic {d : Domain} (hd : BlocksworldDomain d) :
    (staticPredicates d).contains "on" = false :=
  not_static_of_mem_add (a := stackA) (by rw [hd]; simp)
    (y := onV "?ob" "?underob") (by simp [stackA])

/-! ### Instances -/

theorem instance_shape {d : Domain} {objects : List TypedName}
    (hd : BlocksworldDomain d) (i : Instance d objects) :
    (∃ b, i.schema = pickupA ∧ i.args = [b]) ∨
    (∃ b, i.schema = putdownA ∧ i.args = [b]) ∨
    (∃ b u, i.schema = stackA ∧ i.args = [b, u]) ∨
    (∃ b u, i.schema = unstackA ∧ i.args = [b, u]) := by
  have hmem : i.schema ∈ [pickupA, putdownA, stackA, unstackA] := by
    have hm : i.schema ∈ d.actions := i.mem
    rw [hd] at hm
    exact hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with hs | hs | hs | hs
  · obtain ⟨b, ha, -⟩ := i.args_one (by rw [hs])
    exact Or.inl ⟨b, hs, ha⟩
  · obtain ⟨b, ha, -⟩ := i.args_one (by rw [hs])
    exact Or.inr (Or.inl ⟨b, hs, ha⟩)
  · obtain ⟨b, u, ha, -, -⟩ := i.args_two (by rw [hs])
    exact Or.inr (Or.inr (Or.inl ⟨b, u, hs, ha⟩))
  · obtain ⟨b, u, ha, -, -⟩ := i.args_two (by rw [hs])
    exact Or.inr (Or.inr (Or.inr ⟨b, u, hs, ha⟩))

/-- What a `pickup` instance reads, adds and deletes. -/
theorem pickup_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {b : Name} (hs : i.schema = pickupA) (ha : i.args = [b]) :
    clearA b ∈ i.pre ∧ onTable b ∈ i.pre ∧ armEmpty ∈ i.pre ∧
    i.add = [holding b] ∧ i.del = [clearA b, onTable b, armEmpty] := by
  have hp : i.pre = [clearA b, onTable b, armEmpty] := by
    rw [i.pre_eq, hs, ha]; rfl
  have hadd : i.add = [holding b] := by rw [i.add_eq, hs, ha]; rfl
  have hdel : i.del = [clearA b, onTable b, armEmpty] := by
    rw [i.del_eq, hs, ha]; rfl
  simp [hp, hadd, hdel]

/-- What a `putdown` instance reads, adds and deletes. -/
theorem putdown_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {b : Name} (hs : i.schema = putdownA) (ha : i.args = [b]) :
    i.pre = [holding b] ∧
    i.add = [clearA b, armEmpty, onTable b] ∧ i.del = [holding b] := by
  have hp : i.pre = [holding b] := by rw [i.pre_eq, hs, ha]; rfl
  have hadd : i.add = [clearA b, armEmpty, onTable b] := by
    rw [i.add_eq, hs, ha]; rfl
  have hdel : i.del = [holding b] := by rw [i.del_eq, hs, ha]; rfl
  exact ⟨hp, hadd, hdel⟩

/-- What a `stack` instance reads, adds and deletes. -/
theorem stack_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {b u : Name} (hs : i.schema = stackA) (ha : i.args = [b, u]) :
    clearA u ∈ i.pre ∧ holding b ∈ i.pre ∧
    i.add = [armEmpty, clearA b, on b u] ∧ i.del = [clearA u, holding b] := by
  have hp : i.pre = [clearA u, holding b] := by
    rw [i.pre_eq, hs, ha]; rfl
  have hadd : i.add = [armEmpty, clearA b, on b u] := by
    rw [i.add_eq, hs, ha]; rfl
  have hdel : i.del = [clearA u, holding b] := by
    rw [i.del_eq, hs, ha]; rfl
  simp [hp, hadd, hdel]

/-- What an `unstack` instance reads, adds and deletes. -/
theorem unstack_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {b u : Name} (hs : i.schema = unstackA) (ha : i.args = [b, u]) :
    on b u ∈ i.pre ∧ clearA b ∈ i.pre ∧ armEmpty ∈ i.pre ∧
    i.add = [holding b, clearA u] ∧
    i.del = [on b u, clearA b, armEmpty] := by
  have hp : i.pre = [on b u, clearA b, armEmpty] := by
    rw [i.pre_eq, hs, ha]; rfl
  have hadd : i.add = [holding b, clearA u] := by
    rw [i.add_eq, hs, ha]; rfl
  have hdel : i.del = [on b u, clearA b, armEmpty] := by
    rw [i.del_eq, hs, ha]; rfl
  simp [hp, hadd, hdel]

end Planner.Lifted.Blocksworld

/- -------------------------------------------------------------------------- -/
/-
Blocks World's improved heuristic, at the lifted level.

The value is the compiled one read over atoms: the unmet `clear` goals, and the
must-move analysis — which blocks have to move, which of those need placing
where the goal wants them, which have to detour, and the hand.  Every quantity
here is written exactly as its compiled counterpart in
`Planner/ExampleHeuristics/Blocksworld/Improved.lean`, with the block index
replaced by the block's name, so the bridge between the two is congruence
rather than translation.

Nothing in this file mentions a `Fact`, a `State`, or the grounder.
-/

namespace Planner.Lifted.Blocksworld

open Planner Planner.Pddl

/-! ### What the problem fixes -/

/-- What a blocksworld problem pins down for the heuristic: the objects, which
block the goal wants under which, whether it wants a block on the table or
clear, and which block it wants standing on which. -/
structure Cfg where
  blocks : List Name
  /-- The goal's `on(b, c)` supports. -/
  goalOn : Name → Option Name
  /-- Whether the goal wants `b` on the table. -/
  goalTable : Name → Bool
  /-- Whether the goal wants `b` clear. -/
  goalClear : Name → Bool
  /-- The block the goal wants standing on `b`. -/
  goalCarries : Name → Option Name

/-! ### Reading the state -/

/-- Is `b` in the hand? -/
def held (σ : AtomState) (b : Name) : Bool := σ (holding b)

/-- Is `b` on the table? -/
def onTableHolds (σ : AtomState) (b : Name) : Bool := σ (onTable b)

/-- The block `b` stands on, if any. -/
def support (cfg : Cfg) (σ : AtomState) (b : Name) : Option Name :=
  cfg.blocks.find? fun u => σ (on b u)

/-- Does the goal fix a support for `b` that does not hold? -/
def supportUnmet (cfg : Cfg) (σ : AtomState) (b : Name) : Bool :=
  (match cfg.goalOn b with
   | some g => !(σ (on b g))
   | none => false) ||
  (cfg.goalTable b && !σ (onTable b))

/-- Does `b` sit on a block the goal wants clear, or wants another block on? -/
def blocking (cfg : Cfg) (σ : AtomState) (b : Name) : Bool :=
  match support cfg σ b with
  | some u =>
      cfg.goalClear u ||
        (match cfg.goalCarries u with
         | some w => w != b
         | none => false)
  | none => false

/-- A block has to move for a reason of its own. -/
def seed (cfg : Cfg) (σ : AtomState) (b : Name) : Bool :=
  supportUnmet cfg σ b || blocking cfg σ b || held σ b

/-- The fixpoint, unfolded `k` levels down `b`'s tower. -/
def mustMoveAux (cfg : Cfg) (σ : AtomState) : Nat → Name → Bool
  | 0, _ => false
  | k + 1, b =>
      seed cfg σ b ||
        match support cfg σ b with
        | some u => mustMoveAux cfg σ k u
        | none => false

/-- `b` has to move: it is a seed, or it stands on a block that has to move. -/
def mustMove (cfg : Cfg) (σ : AtomState) (b : Name) : Bool :=
  mustMoveAux cfg σ (cfg.blocks.length + 1) b

/-- Does the goal want `target` below `b`, following `b`'s goal tower down
`k` levels? -/
def inGoalChainAux (cfg : Cfg) : Nat → Name → Name → Bool
  | 0, _, _ => false
  | k + 1, b, target =>
      match cfg.goalOn b with
      | some next => next == target || inGoalChainAux cfg k next target
      | none => false

/-- Does the goal want `target` somewhere below `b`? -/
def inGoalChain (cfg : Cfg) (b target : Name) : Bool :=
  inGoalChainAux cfg cfg.blocks.length b target

/-- `b` must be parked somewhere temporary: its destination is not ready and it
is in the way of getting it ready. -/
def detour (cfg : Cfg) (σ : AtomState) (b : Name) : Bool :=
  match cfg.goalOn b with
  | some target =>
      mustMove cfg σ target &&
        (held σ b ||
          (match support cfg σ b with
           | some sup => inGoalChain cfg b sup
           | none => false))
  | none => false

/-- Blocks that must move and need placing where the goal wants them. -/
def needPlace (cfg : Cfg) (σ : AtomState) : Nat :=
  cfg.blocks.countP fun b => mustMove cfg σ b && supportUnmet cfg σ b

/-- Blocks that must move but only have to get out of the way. -/
def needClearing (cfg : Cfg) (σ : AtomState) : Nat :=
  cfg.blocks.countP fun b => mustMove cfg σ b && !supportUnmet cfg σ b

/-- One grab is already done when the arm holds a block that must move. -/
def heldNeedsPlace (cfg : Cfg) (σ : AtomState) : Nat :=
  if cfg.blocks.any fun b => mustMove cfg σ b && held σ b then 1 else 0

/-- Blocks that must be moved twice. -/
def detours (cfg : Cfg) (σ : AtomState) : Nat :=
  cfg.blocks.countP fun b => mustMove cfg σ b && detour cfg σ b

/-- The must-move bound: a grab and a place per mover, less the grab already
done and the place that may stay undone, plus two per detour. -/
def moveBound (cfg : Cfg) (σ : AtomState) : Nat :=
  let m := needPlace cfg σ + needClearing cfg σ
  let grabs := m - heldNeedsPlace cfg σ + detours cfg σ
  let places := m - (if needClearing cfg σ > 0 then 1 else 0) + detours cfg σ
  grabs + places

/-! ### The clear-goal bound -/

/-- The goal's `clear` atoms, as names. -/
abbrev clearGoalsOf (p : Problem) : List Name :=
  p.goal.filterMap fun a => match a.pred with
    | "clear" => a.args.getD 0 ""
    | _ => ""

/-- Unmet `clear` goals. -/
def clearBound (p : Problem) (σ : AtomState) : Nat :=
  (clearGoalsOf p).countP fun x => !σ (clearA x)

/-- The larger of the two bounds. -/
def value (p : Problem) (cfg : Cfg) (σ : AtomState) : Nat :=
  max (clearBound p σ) (moveBound cfg σ)

/-! ### Goal awareness -/

/-- A support is always one of the task's blocks. -/
theorem support_mem {cfg : Cfg} {σ : AtomState} {b u : Name}
    (h : support cfg σ b = some u) : u ∈ cfg.blocks := by
  unfold support at h
  exact List.mem_of_find?_eq_some h

/-- No block of the list is a seed, so no block of the list has to move:
the tower below any block stays inside the list. -/
theorem mustMove_eq_false (cfg : Cfg) (σ : AtomState)
    (hseed : ∀ b ∈ cfg.blocks, seed cfg σ b = false) :
    ∀ b ∈ cfg.blocks, mustMoveAux cfg σ (cfg.blocks.length + 1) b = false := by
  have key : ∀ (k : Nat) (b : Name), b ∈ cfg.blocks →
      ∀ j, k + j ≤ cfg.blocks.length + 1 → mustMoveAux cfg σ k b = false := by
    intro k
    induction k with
    | zero => intro b _ _ _; rfl
    | succ k ih =>
        intro b hb j hj
        show (seed cfg σ b ||
          match support cfg σ b with
          | some u => mustMoveAux cfg σ k u
          | none => false) = false
        have hs : seed cfg σ b = false := hseed b hb
        cases hsup : support cfg σ b with
        | none =>
            show (seed cfg σ b || false) = false
            rw [show seed cfg σ b = false from hs]
            rfl
        | some u =>
            simp only [Bool.false_or, hs]
            exact ih u (support_mem hsup) j (by omega)
  intro b hb
  exact key _ b hb 0 (by omega)

/-- Zero once every goal support holds and nothing stands in the way: no block
is a seed, so no block has to move, and every count in the bound vanishes. -/
theorem moveBound_eq_zero (cfg : Cfg) (σ : AtomState)
    (hseed : ∀ b ∈ cfg.blocks, seed cfg σ b = false) :
    moveBound cfg σ = 0 := by
  have hmm : ∀ b ∈ cfg.blocks, mustMove cfg σ b = false :=
    mustMove_eq_false cfg σ hseed
  have hnp : needPlace cfg σ = 0 := by
    unfold needPlace
    rw [List.countP_eq_zero]
    intro b hb hb'
    rw [hmm b hb] at hb'
    simp at hb'
  have hnc : needClearing cfg σ = 0 := by
    unfold needClearing
    rw [List.countP_eq_zero]
    intro b hb hb'
    rw [hmm b hb] at hb'
    simp at hb'
  have hdet : detours cfg σ = 0 := by
    unfold detours
    rw [List.countP_eq_zero]
    intro b hb hb'
    rw [hmm b hb] at hb'
    simp at hb'
  show needPlace cfg σ + needClearing cfg σ - heldNeedsPlace cfg σ + detours cfg σ +
    (needPlace cfg σ + needClearing cfg σ -
      (if needClearing cfg σ > 0 then 1 else 0) + detours cfg σ) = 0
  rw [hnp, hnc, hdet]
  simp

end Planner.Lifted.Blocksworld

/- -------------------------------------------------------------------------- -/
/-
Blocks World's invariant and its schemas, at the lifted level.

`Inv` says what every reachable blocksworld state looks like physically:

  * at most one block rests directly on any block, and no block rests on more
    than one; the hand holds at most one;
  * a supported block is neither on the table nor under anything the table holds;
  * a clear block has nothing standing on it;
  * `arm-empty` holds exactly when nothing is held;
  * a held block stands on nothing, is on no table, has nothing on it,
    and is not clear;
  * nothing rests on the table's underside.

Every one of the four schemas keeps it.  The proofs read each instance through
its shape: an atom outside add ∪ del is framed, an atom only del can touch never
becomes true.
-/

namespace Planner.Lifted.Blocksworld

open Planner Planner.Pddl

variable {d : Domain} {objects : List TypedName}

/-! ### Atoms of different predicates are different -/

@[simp] theorem holding_ne_clearA (x y : Name) : holding x ≠ clearA y := by
  simp [holding, clearA]
@[simp] theorem holding_ne_onTable (x y : Name) : holding x ≠ onTable y := by
  simp [holding, onTable]
@[simp] theorem holding_ne_armEmpty (x : Name) : holding x ≠ armEmpty := by
  simp [holding, armEmpty]
@[simp] theorem holding_ne_on (x y c : Name) : holding x ≠ on y c := by
  simp [holding, on]
@[simp] theorem clearA_ne_onTable (x y : Name) : clearA x ≠ onTable y := by
  simp [clearA, onTable]
@[simp] theorem clearA_ne_armEmpty (x : Name) : clearA x ≠ armEmpty := by
  simp [clearA, armEmpty]
@[simp] theorem clearA_ne_on (x y c : Name) : clearA x ≠ on y c := by
  simp [clearA, on]
@[simp] theorem onTableX_ne_armEmpty (x : Name) : onTable x ≠ armEmpty := by
  simp [onTable, armEmpty]
@[simp] theorem on_ne_holding (y c x : Name) : on y c ≠ holding x := by
  simp [on, holding]
@[simp] theorem on_ne_clear (y c x : Name) : on y c ≠ clearA x := by
  simp [on, clearA]
@[simp] theorem on_ne_table (y c x : Name) : on y c ≠ onTable x := by
  simp [on, onTable]
@[simp] theorem on_ne_empty (y c : Name) : on y c ≠ armEmpty := by
  simp [on, armEmpty]

@[simp] theorem onTable_ne_on (x y c : Name) : onTable x ≠ on y c := by
  simp [onTable, on]
@[simp] theorem armEmpty_ne_on (y c : Name) : armEmpty ≠ on y c := by
  simp [armEmpty, on]
@[simp] theorem clearA_ne_holding (x y : Name) : clearA x ≠ holding y := by
  simp [clearA, holding]
@[simp] theorem onTable_ne_holding (x y : Name) : onTable x ≠ holding y := by
  simp [onTable, holding]
@[simp] theorem armEmpty_ne_holding (x : Name) : armEmpty ≠ holding x := by
  simp [armEmpty, holding]
@[simp] theorem onTable_ne_clearA (x y : Name) : onTable x ≠ clearA y := by
  simp [onTable, clearA]
@[simp] theorem armEmpty_ne_clearA (x : Name) : armEmpty ≠ clearA x := by
  simp [armEmpty, clearA]
@[simp] theorem armEmpty_ne_onTable (x : Name) : armEmpty ≠ onTable x := by
  simp [armEmpty, onTable]

/-- Two `holding` atoms are equal exactly when their blocks are. -/
@[simp] theorem holding_inj {x y : Name} : (holding x = holding y) = (x = y) := by
  simp [holding]

/-- The same, for `clear`. -/
@[simp] theorem clearA_inj {x y : Name} : (clearA x = clearA y) = (x = y) := by
  simp [clearA]

/-- The same, for `on-table`. -/
@[simp] theorem onTable_inj {x y : Name} : (onTable x = onTable y) = (x = y) := by
  simp [onTable]

/-- The same, for `on`. -/
@[simp] theorem on_inj {x1 c1 x2 c2 : Name} :
    (on x1 c1 = on x2 c2) = (x1 = x2 ∧ c1 = c2) := by
  simp [on]

/-! ### Frames -/

/-- An atom outside the four a `pickup`/`putdown` touches does not move. -/
private theorem framed4 {o : AtomOp} {i : Instance d objects} {a x y z w : GroundAtom}
    (hadd : ∀ b ∈ o.add, b ∈ i.add) (hdel : ∀ b ∈ o.del, b ∈ i.del)
    (hia : i.add = [x]) (hid : i.del = [y, z, w])
    (hax : a ≠ x) (hay : a ≠ y) (haz : a ≠ z) (haw : a ≠ w) (σ : AtomState) :
    o.applyA σ a = σ a := by
  refine applyA_frame σ ?_ ?_
  · intro hmem
    have h := hadd a hmem; rw [hia] at h; exact hax (by simpa using h)
  · intro hmem
    have h := hdel a hmem; rw [hid] at h
    rcases (by simpa using h : a = y ∨ a = z ∨ a = w) with h1 | h1 | h1
    · exact hay h1
    · exact haz h1
    · exact haw h1

/-- An atom outside the union of a `stack`/`unstack` instance's add and delete
lists does not move. -/
private theorem framedSU {o : AtomOp} {i : Instance d objects}
    {a hb hu hc hae hon : GroundAtom}
    (hadd : ∀ g ∈ o.add, g ∈ i.add) (hdel : ∀ g ∈ o.del, g ∈ i.del)
    (hia : i.add = [hae, hc, hon]) (hid : i.del = [hu, hb, hae])
    (han : a ≠ hae) (hac : a ≠ hc) (hon' : a ≠ hon)
    (ahu : a ≠ hu) (ahb : a ≠ hb) (σ : AtomState) :
    o.applyA σ a = σ a := by
  refine applyA_frame σ ?_ ?_
  · intro hmem
    have h := hadd a hmem; rw [hia] at h
    rcases (by simpa using h : a = hae ∨ a = hc ∨ a = hon) with h1 | h1 | h1
    · exact han h1
    · exact hac h1
    · exact hon' h1
  · intro hmem
    have h := hdel a hmem; rw [hid] at h
    rcases (by simpa using h : a = hu ∨ a = hb ∨ a = hae) with h1 | h1 | h1
    · exact ahu h1
    · exact ahb h1
    · exact han h1

/-! ### The invariant -/

/-- What every reachable blocksworld state looks like physically. -/
structure Inv (σ : AtomState) : Prop where
  /-- At most one block rests directly on any block. -/
  oneOn : ∀ x c u, σ (on x c) = true → σ (on u c) = true → x = u
  /-- A block rests on at most one block: its `on` facts name one place. -/
  oneSupport : ∀ x c d, σ (on x c) = true → σ (on x d) = true → c = d
  /-- The hand holds at most one block. -/
  oneHeld : ∀ x y, σ (holding x) = true → σ (holding y) = true → x = y
  /-- A block standing on something is not on the table. -/
  onNotTable : ∀ x c, σ (on x c) = true → σ (onTable x) = false
  /-- `arm-empty` holds exactly when nothing is held. -/
  emptyIff : σ armEmpty = true ↔ ∀ x, σ (holding x) = false
  /-- A held block is neither on anything nor on the table nor supporting anything. -/
  heldFree : ∀ x, σ (holding x) = true →
    (∀ c, σ (on x c) = false) ∧ σ (onTable x) = false ∧ ∀ z, σ (on z x) = false
  /-- A held block is never clear.  Without this field the degenerate
  self-stack `stack(b, b)` could fire off a held-and-clear block, and its
  successor would break `clearAbove`. -/
  heldNotClear : ∀ x, σ (holding x) = true → σ (clearA x) = false
  /-- Nothing rests on the table's underside: if `x` stands on `c` and `y` is
  on the table then `x ≠ y`. -/
  tableDistinct : ∀ x c y, σ (on x c) = true → σ (onTable y) = true → x ≠ y
  /-- A clear block supports nothing.  Deleting `clear` keeps this trivially,
  which is why `pickup` preserves it. -/
  clearAbove : ∀ y z, σ (clearA y) = true → σ (on z y) = false

/-! ### What each schema does, as a transition shape -/

variable {o : AtomOp}

/-- A `pickup b` step: the hand takes `b` off the table. -/
structure PickupStep (σ τ : AtomState) (b : Name) : Prop where
  preClear : σ (clearA b) = true
  preTable : σ (onTable b) = true
  preEmpty : σ armEmpty = true
  addHolding : τ (holding b) = true
  delClear : τ (clearA b) = false
  delTable : τ (onTable b) = false
  delEmpty : τ armEmpty = false
  frame : ∀ a, a ≠ holding b → a ≠ clearA b → a ≠ onTable b → a ≠ armEmpty →
    τ a = σ a

/-- A `putdown b` step: the held `b` goes back on the table. -/
structure PutdownStep (σ τ : AtomState) (b : Name) : Prop where
  preHeld : σ (holding b) = true
  addClear : τ (clearA b) = true
  addEmpty : τ armEmpty = true
  addTable : τ (onTable b) = true
  delHeld : τ (holding b) = false
  frame : ∀ a, a ≠ holding b → a ≠ clearA b → a ≠ onTable b → a ≠ armEmpty →
    τ a = σ a

/-- A `stack b u` step: the held `b` goes onto `u`. -/
structure StackStep (σ τ : AtomState) (b u : Name) : Prop where
  preClearU : σ (clearA u) = true
  preHeld : σ (holding b) = true
  addEmpty : τ armEmpty = true
  addClearB : τ (clearA b) = true
  addOn : τ (on b u) = true
  delClearU : τ (clearA u) = false
  delHeld : τ (holding b) = false
  frame : ∀ a, a ≠ holding b → a ≠ clearA b → a ≠ armEmpty →
    a ≠ clearA u → a ≠ on b u → τ a = σ a

/-- An `unstack b u` step: the hand takes `b` off `u`.  Note `on-table` appears
in neither add nor delete of the schema, so the frame does not mention it. -/
structure UnstackStep (σ τ : AtomState) (b u : Name) : Prop where
  preOn : σ (on b u) = true
  preClearB : σ (clearA b) = true
  preEmpty : σ armEmpty = true
  addHeld : τ (holding b) = true
  addClearU : τ (clearA u) = true
  delOn : τ (on b u) = false
  delClearB : τ (clearA b) = false
  delEmpty : τ armEmpty = false
  frame : ∀ a, a ≠ holding b → a ≠ clearA b → a ≠ armEmpty →
    a ≠ clearA u → a ≠ on b u → τ a = σ a

/-! ### Acyclicity

`Inv` says nothing about towers ending.  A state holding both `on(a, b)` and
`on(b, a)` meets every field of it, and yet the must-move analysis climbs towers
and has to reach the bottom of one.  So acyclicity is carried as a second
invariant, next to `Inv` rather than inside it.

Only `stack` adds an `on` fact, so only `stack` can close a cycle — and it
cannot.  The block it stacks is held, and `Inv.heldFree` says a held block has
nothing under it and nothing on it, so before the step that block has no edge at
all.  The new edge therefore leaves it with no way back.
-/

/-- `x` stands somewhere above `y`: a chain of `on` facts leads down from `x`
to `y`. -/
abbrev Above (σ : AtomState) : Name → Name → Prop :=
  Relation.TransGen fun a b => σ (on a b) = true

/-- No block stands above itself. -/
def Acyclic (σ : AtomState) : Prop := ∀ x, ¬ Above σ x x

/-- A step that adds no `on` fact keeps acyclicity. -/
theorem acyclic_of_sub {σ τ : AtomState}
    (h : ∀ x c, τ (on x c) = true → σ (on x c) = true) (ha : Acyclic σ) :
    Acyclic τ := fun x hx => ha x (hx.mono fun a b hab => h a b hab)

/-- Nothing reaches a block that has nothing standing on it. -/
theorem not_above_of_nothingOn {σ : AtomState} {b : Name}
    (hb : ∀ z, σ (on z b) = false) (z : Name) : ¬ Above σ z b := by
  intro h
  obtain ⟨w, -, hw⟩ := Relation.TransGen.tail'_iff.mp h
  rw [hb w] at hw
  exact Bool.false_ne_true hw

/-- **A step that adds one edge out of an isolated block keeps acyclicity.**
Every `τ` edge is a `σ` edge or the new `(b, u)`; `b` has no `σ` edge into it,
and `u ≠ b`. -/
theorem acyclic_of_add_edge {σ τ : AtomState} {b u : Name}
    (hedge : ∀ x c, τ (on x c) = true → σ (on x c) = true ∨ (x = b ∧ c = u))
    (hinto : ∀ z, σ (on z b) = false) (hub : u ≠ b) (ha : Acyclic σ) :
    Acyclic τ := by
  -- Every `τ` chain is a `σ` chain, or starts at `b` and continues from `u`.
  have key : ∀ x y, Above τ x y → Above σ x y ∨ (x = b ∧ (y = u ∨ Above σ u y)) := by
    intro x y h
    induction h using Relation.TransGen.head_induction_on with
    | single hxy =>
        rcases hedge _ _ hxy with hs | ⟨rfl, rfl⟩
        · exact Or.inl (Relation.TransGen.single hs)
        · exact Or.inr ⟨rfl, Or.inl rfl⟩
    | head hxw _ ihw =>
        rename_i x w _
        rcases hedge _ _ hxw with hs | ⟨rfl, rfl⟩
        · rcases ihw with hw | ⟨rfl, -⟩
          · exact Or.inl (hw.head hs)
          · rw [hinto x] at hs; exact absurd hs Bool.false_ne_true
        · rcases ihw with hw | ⟨heq, -⟩
          · exact Or.inr ⟨rfl, Or.inr hw⟩
          · exact absurd heq hub
  intro x hx
  rcases key x x hx with hs | ⟨rfl, hy⟩
  · exact ha x hs
  · rcases hy with rfl | hs
    · exact hub rfl
    · exact not_above_of_nothingOn hinto u hs

/-! ### Acyclicity, schema by schema

`pickup` and `putdown` touch no `on` fact at all, and `unstack` only deletes
one, so all three keep acyclicity by `acyclic_of_sub`.  `stack` is the one case
with something to prove.
-/

theorem PickupStep.on_frame {σ τ : AtomState} {b : Name} (h : PickupStep σ τ b)
    (x c : Name) : τ (on x c) = σ (on x c) :=
  h.frame _ (by simp) (by simp) (by simp) (by simp)

theorem PickupStep.acyclic_preserved {σ τ : AtomState} {b : Name}
    (h : PickupStep σ τ b) (ha : Acyclic σ) : Acyclic τ :=
  acyclic_of_sub (fun x c hx => by rw [← h.on_frame x c]; exact hx) ha

theorem PutdownStep.on_frame {σ τ : AtomState} {b : Name} (h : PutdownStep σ τ b)
    (x c : Name) : τ (on x c) = σ (on x c) :=
  h.frame _ (by simp) (by simp) (by simp) (by simp)

theorem PutdownStep.acyclic_preserved {σ τ : AtomState} {b : Name}
    (h : PutdownStep σ τ b) (ha : Acyclic σ) : Acyclic τ :=
  acyclic_of_sub (fun x c hx => by rw [← h.on_frame x c]; exact hx) ha

theorem UnstackStep.acyclic_preserved {σ τ : AtomState} {b u : Name}
    (h : UnstackStep σ τ b u) (ha : Acyclic σ) : Acyclic τ := by
  refine acyclic_of_sub (fun x c hx => ?_) ha
  by_cases hbu : on x c = on b u
  · rw [hbu, h.delOn] at hx; exact absurd hx Bool.false_ne_true
  · rw [h.frame _ (by simp) (by simp) (by simp) (by simp) hbu] at hx; exact hx

/-- **`stack` cannot close a cycle.**  The block it stacks is held, so before
the step nothing stands on it and it stands on nothing.  The block it is stacked
onto is clear, and a held block is never clear, so the two are different. -/
theorem StackStep.acyclic_preserved {σ τ : AtomState} {b u : Name}
    (h : StackStep σ τ b u) (hinv : Inv σ) (ha : Acyclic σ) : Acyclic τ := by
  obtain ⟨-, -, hinto⟩ := hinv.heldFree b h.preHeld
  have hub : u ≠ b := by
    intro hu
    have hc := h.preClearU
    rw [hu, hinv.heldNotClear b h.preHeld] at hc
    exact Bool.false_ne_true hc
  refine acyclic_of_add_edge (fun x c hx => ?_) hinto hub ha
  by_cases hbu : on x c = on b u
  · exact Or.inr (by simpa using hbu)
  · exact Or.inl (by
      rw [← h.frame _ (by simp) (by simp) (by simp) (by simp) hbu]; exact hx)

/-! ### Preservation: pickup -/

theorem PickupStep.inv_preserved {σ τ : AtomState} {b : Name}
    (hstep : PickupStep σ τ b) (hinv : Inv σ) : Inv τ := by
  obtain ⟨pc, pt, pe, ah, dc, dt, de, hfr⟩ := hstep
  have frHeld : ∀ x : Name, x ≠ b → τ (holding x) = σ (holding x) := by
    intro x hx
    refine hfr _ ?_ (by simp) (by simp) (by simp)
    intro hc
    rw [holding_inj] at hc
    exact hx hc
  have frClear : ∀ y : Name, y ≠ b → τ (clearA y) = σ (clearA y) := by
    intro y hy
    refine hfr _ (fun hc => (Ne.symm (holding_ne_clearA b y)).elim hc)
      (fun hc => by rw [clearA_inj] at hc; exact hy hc)
      (fun hc => (clearA_ne_onTable y b).elim hc)
      (fun hc => (clearA_ne_armEmpty y).elim hc)
  have frTable : ∀ y : Name, y ≠ b → τ (onTable y) = σ (onTable y) := by
    intro y hy
    refine hfr _ (fun hc => (Ne.symm (holding_ne_onTable b y)).elim hc)
      (fun hc => (Ne.symm (clearA_ne_onTable b y)).elim hc)
      (fun hc => by rw [onTable_inj] at hc; exact hy hc)
      (fun hc => (onTableX_ne_armEmpty y).elim hc)
  have frOn : ∀ y c : Name, τ (on y c) = σ (on y c) :=
    fun y c => hfr _ (on_ne_holding y c b)
      (on_ne_clear y c b) (on_ne_table y c b) (on_ne_empty y c)
  -- the hand holds `b` and nothing else
  have hheld : ∀ x, τ (holding x) = true ↔ x = b := by
    intro x
    constructor
    · intro hx
      by_cases hxb : x = b
      · exact hxb
      · have h2 := hinv.emptyIff.mp pe x
        rw [← frHeld x hxb, hx] at h2
        exact absurd h2 (by simp)
    · intro hx; rw [hx]; exact ah
  refine
    { oneOn := ?_, oneSupport := ?_, oneHeld := ?_, onNotTable := ?_, emptyIff := ?_,
      heldFree := ?_, heldNotClear := ?_, tableDistinct := ?_, clearAbove := ?_ }
  · intro x c u hx hu
    rw [frOn x c] at hx
    rw [frOn u c] at hu
    exact hinv.oneOn x c u hx hu
  · intro x c d hx hd
    rw [frOn x c] at hx
    rw [frOn x d] at hd
    exact hinv.oneSupport x c d hx hd
  · intro x y hx hy
    rw [(hheld x).mp hx, (hheld y).mp hy]
  · intro x c hx
    by_cases hxb : x = b
    · exfalso
      rw [hxb] at hx
      rw [frOn b c] at hx
      exact (hinv.tableDistinct b c b hx pt rfl).elim
    · rw [frOn x c] at hx
      rw [frTable x hxb]
      exact hinv.onNotTable x c hx
  · have emp1 : τ armEmpty = true → ∀ x, τ (holding x) = false := by
      intro hem x
      by_cases hxb : x = b
      · subst hxb
        exfalso
        rw [de] at hem
        exact absurd hem (by simp)
      · rw [frHeld x hxb]
        exact hinv.emptyIff.mp pe x
    have emp2 : (∀ x, τ (holding x) = false) → τ armEmpty = true := by
      intro hall
      have hb : τ (holding b) = false := hall b
      rw [hb] at ah
      exact absurd ah (by simp)
    exact ⟨emp1, emp2⟩
  · intro x hx
    have hxb' : x = b := (hheld x).mp hx
    subst hxb'
    have h1 : ∀ c, τ (on x c) = false := by
      intro c
      rw [frOn x c]
      by_cases hc : σ (on x c) = true
      · have h3 := hinv.onNotTable x c hc
        rw [pt] at h3
        exact absurd h3 (by simp)
      · simpa using hc
    refine ⟨h1, dt, fun z => (frOn z x).trans (hinv.clearAbove x z pc)⟩
  · intro x hx
    rw [(hheld x).mp hx]
    exact dc
  · intro x c y hx hy
    by_cases hyb : y = b
    · exfalso
      rw [hyb] at hy
      rw [dt] at hy
      exact absurd hy (by simp)
    · rw [frOn x c] at hx
      rw [frTable y hyb] at hy
      exact hinv.tableDistinct x c y hx hy
  · intro y z hy
    by_cases hyb : y = b
    · subst hyb
      rw [frOn z y]
      exact hinv.clearAbove y z pc
    · rw [frOn z y]
      rw [frClear y hyb] at hy
      exact hinv.clearAbove y z hy

/-! ### Preservation: putdown -/

theorem PutdownStep.inv_preserved {σ τ : AtomState} {b : Name}
    (hstep : PutdownStep σ τ b) (hinv : Inv σ) : Inv τ := by
  obtain ⟨ph, ac, ae, atab, dh, hfr⟩ := hstep
  have frHeld : ∀ x : Name, x ≠ b → τ (holding x) = σ (holding x) := by
    intro x hx
    refine hfr _ (fun hc => hx (by rw [holding_inj] at hc; exact hc))
      (fun hc => (holding_ne_clearA x b).elim hc)
      (fun hc => (holding_ne_onTable x b).elim hc)
      (fun hc => (holding_ne_armEmpty x).elim hc)
  have frClear : ∀ y : Name, y ≠ b → τ (clearA y) = σ (clearA y) := by
    intro y hy
    refine hfr _ (fun hc => (Ne.symm (holding_ne_clearA b y)).elim hc)
      (fun hc => by rw [clearA_inj] at hc; exact hy hc)
      (fun hc => (clearA_ne_onTable y b).elim hc)
      (fun hc => (clearA_ne_armEmpty y).elim hc)
  have frTable : ∀ y : Name, y ≠ b → τ (onTable y) = σ (onTable y) := by
    intro y hy
    refine hfr _ (fun hc => (Ne.symm (holding_ne_onTable b y)).elim hc)
      (fun hc => (Ne.symm (clearA_ne_onTable b y)).elim hc)
      (fun hc => by rw [onTable_inj] at hc; exact hy hc)
      (fun hc => (onTableX_ne_armEmpty y).elim hc)
  have frOn : ∀ y c : Name, τ (on y c) = σ (on y c) :=
    fun y c => hfr _ (fun hc => (on_ne_holding y c b).elim hc)
      (fun hc => (on_ne_clear y c b).elim hc)
      (fun hc => (on_ne_table y c b).elim hc)
      (fun hc => (on_ne_empty y c).elim hc)
  -- before: only `b` is held; after the putdown nothing is held at all
  have hnone : ∀ x, τ (holding x) = false := by
    intro x
    by_cases hxb : x = b
    · rw [hxb, dh]
    · rw [frHeld x hxb]
      by_cases hc : σ (holding x) = true
      · exact absurd (hinv.oneHeld x b hc ph) hxb
      · simpa using hc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x c u hx hu
    rw [frOn x c] at hx
    rw [frOn u c] at hu
    exact hinv.oneOn x c u hx hu
  · intro x c d hx hd
    rw [frOn x c] at hx
    rw [frOn x d] at hd
    exact hinv.oneSupport x c d hx hd
  · -- nothing is held afterwards
    intro x y hx hy
    rw [hnone x] at hx
    exact absurd hx (by simp)
  · intro x c hx
    by_cases hxb : x = b
    · subst hxb
      exfalso
      have hfr' := frOn x c
      rw [hx] at hfr'
      have hcon : σ (on x c) = false := hinv.heldFree x ph |>.1 c
      rw [hcon] at hfr'
      exact absurd hfr' (by simp)
    · -- `x` ≠ `b`, so both atoms are framed: the invariant carries over directly.
      rw [frOn x c] at hx
      rw [frTable x hxb]
      exact hinv.onNotTable x c hx
  · refine ⟨fun hem x => hnone x, fun _ => ae⟩
  · intro x hx
    exact absurd hx (by rw [hnone x]; simp)
  · intro x hx
    exact absurd hx (by rw [hnone x]; simp)
  · intro x c y hx hy hxy
    rw [hxy] at hx
    have hx' : σ (on y c) = true := by rw [← frOn y c]; exact hx
    by_cases hb : y = b
    · have hh : σ (holding y) = true := by rw [hb]; exact ph
      have hfalse := (hinv.heldFree y hh).1 c
      rw [hfalse] at hx'
      exact absurd hx' (by simp)
    · have ht : σ (onTable y) = false := hinv.onNotTable y c hx'
      rw [frTable y hb] at hy
      rw [ht] at hy
      exact absurd hy (by simp)
  · intro y z hy
    by_cases hb : y = b
    · have hh : σ (holding y) = true := by rw [hb]; exact ph
      rw [frOn z y]
      exact (hinv.heldFree y hh).2.2 z
    · have hc' : σ (clearA y) = true := by
        rw [← frClear y hb]
        exact hy
      rw [frOn z y]
      exact hinv.clearAbove y z hc'

/-! ### Preservation: stack -/

theorem StackStep.inv_preserved {σ τ : AtomState} {b u : Name}
    (hstep : StackStep σ τ b u) (hinv : Inv σ) : Inv τ := by
  obtain ⟨pcu, ph, ae, acb, aon, dcu, dh, fr⟩ := hstep
  -- self-stacking is impossible: a held block is never clear
  by_cases hub : u = b
  · exfalso
    rw [hub] at pcu
    rw [hinv.heldNotClear b ph] at pcu
    exact absurd pcu (by simp)
  have frHeld : ∀ x : Name, x ≠ b → τ (holding x) = σ (holding x) := by
    intro x hx
    refine fr _ ?_ ?_ ?_ ?_ ?_
    · intro hc; rw [holding_inj] at hc; exact hx hc
    · exact holding_ne_clearA x b
    · exact holding_ne_armEmpty x
    · exact holding_ne_clearA x u
    · exact fun hc => ((Ne.symm (on_ne_holding b u x)).elim hc)
  have frClear : ∀ y : Name, y ≠ b → y ≠ u → τ (clearA y) = σ (clearA y) := by
    intro y hyb hyu
    refine fr _ ?_ ?_ ?_ ?_ ?_
    · exact fun hc => ((Ne.symm (holding_ne_clearA b y)).elim hc)
    · intro hc; rw [clearA_inj] at hc; exact hyb hc
    · exact clearA_ne_armEmpty y
    · intro hc; rw [clearA_inj] at hc; exact hyu hc
    · exact fun hc => ((clearA_ne_on y b u).elim hc)
  have frTable : ∀ x : Name, τ (onTable x) = σ (onTable x) := by
    intro x
    refine fr _ ?_ ?_ ?_ ?_ ?_
    · exact fun hc => ((Ne.symm (holding_ne_onTable b x)).elim hc)
    · exact fun hc => ((Ne.symm (clearA_ne_onTable b x)).elim hc)
    · exact onTableX_ne_armEmpty x
    · exact fun hc => ((Ne.symm (clearA_ne_onTable u x)).elim hc)
    · exact fun hc => ((Ne.symm (on_ne_table b u x)).elim hc)
  have frOn : ∀ z c : Name, (z ≠ b ∨ c ≠ u) → τ (on z c) = σ (on z c) := by
    intro z c hne
    refine fr _ ?_ ?_ ?_ ?_ ?_
    · exact on_ne_holding z c b
    · exact on_ne_clear z c b
    · exact on_ne_empty z c
    · exact on_ne_clear z c u
    · intro hc
      rw [on_inj] at hc
      rcases hne with h1 | h2
      · exact absurd hc.1 h1
      · exact absurd hc.2 h2
  -- A true `on` atom is either framed — so it held before — or it is the one
  -- the schema added.
  have key : ∀ z c : Name, τ (on z c) = true → σ (on z c) = true ∨ (z = b ∧ c = u) := by
    intro z c h
    by_cases h1 : z = b
    · by_cases h2 : c = u
      · exact Or.inr ⟨h1, h2⟩
      · exact Or.inl (by rw [← frOn z c (Or.inr h2)]; exact h)
    · exact Or.inl (by rw [← frOn z c (Or.inl h1)]; exact h)
  have hnone : ∀ x : Name, τ (holding x) = false := by
    intro x
    by_cases hxb : x = b
    · rw [hxb, dh]
    · rw [frHeld x hxb]
      by_cases hh : σ (holding x) = true
      · have := hinv.oneHeld x b hh ph
        rw [this] at hxb; exact absurd hxb (by simp)
      · simpa using hh
  refine
    { oneOn := ?_, oneSupport := ?_, oneHeld := ?_, onNotTable := ?_, emptyIff := ?_,
      heldFree := ?_, heldNotClear := ?_, tableDistinct := ?_, clearAbove := ?_ }
  · intro x c w hx hw
    rcases key x c hx with hsx | hxe
    · rcases key w c hw with hsw | hwe
      · exact hinv.oneOn x c w hsx hsw
      · -- `w` is `b` and `c` is `u`: but `u` was clear before, so nothing stood on it
        exfalso
        have hcu : c = u := hwe.2
        rw [hcu] at hsx
        rw [hinv.clearAbove u x pcu] at hsx
        exact absurd hsx (by simp)
    · -- `x` is `b`, `c` is `u`
      have hcu : c = u := hxe.2
      rw [hcu] at hw
      rcases key w u hw with hsw | hwe
      · exfalso
        rw [hinv.clearAbove u w pcu] at hsw
        exact absurd hsw (by simp)
      · exact hxe.1.trans hwe.1.symm
  · intro x c d hx hd
    rcases key x c hx with hs | he
    · rcases key x d hd with hs2 | he2
      · exact hinv.oneSupport x c d hs hs2
      · exfalso
        rw [he2.1] at hs
        rw [(hinv.heldFree b ph).1 c] at hs
        exact absurd hs (by simp)
    · rcases key x d hd with hs2 | he2
      · exfalso
        rw [he.1] at hs2
        rw [(hinv.heldFree b ph).1 d] at hs2
        exact absurd hs2 (by simp)
      · exact he.2.trans he2.2.symm
  · intro x y hx hy
    rw [hnone x] at hx
    exact absurd hx (by simp)
  · intro z c hx
    rcases key z c hx with hs | he
    · rw [frTable z]
      exact hinv.onNotTable z c hs
    · rw [he.1, frTable b]
      exact (hinv.heldFree b ph).2.1
  · exact ⟨fun hem x => hnone x, fun _ => ae⟩
  · intro x hx
    rw [hnone x] at hx
    exact absurd hx (by simp)
  · intro x hx
    rw [hnone x] at hx
    exact absurd hx (by simp)
  · intro z c y hx hy hxy
    rw [hxy] at hx
    have hy' : σ (onTable y) = true := by
      rw [← frTable y]
      exact hy
    rcases key y c hx with hs | he
    · rw [hinv.onNotTable y c hs] at hy'
      exact absurd hy' (by simp)
    · -- `y` is `b`: a held block is not on the table
      rw [he.1] at hy'
      rw [(hinv.heldFree b ph).2.1] at hy'
      exact absurd hy' (by simp)
  · intro y z hy
    by_cases hyb : y = b
    · rw [hyb, frOn z b (Or.inr (Ne.symm hub))]
      exact (hinv.heldFree b ph).2.2 z
    · by_cases hyu : y = u
      · rw [hyu] at hy
        rw [dcu] at hy
        exact absurd hy (by simp)
      · rw [frClear y hyb hyu] at hy
        rw [frOn z y (Or.inr hyu)]
        exact hinv.clearAbove y z hy

/-! ### Preservation: unstack -/

theorem UnstackStep.inv_preserved {σ τ : AtomState} {b u : Name}
    (hstep : UnstackStep σ τ b u) (hinv : Inv σ) : Inv τ := by
  obtain ⟨pon, pcb, pe, ah, acu, don, dcb, de, fr⟩ := hstep
  -- self-unstacking is impossible: `clear(b)` means nothing rests on `b`
  by_cases hub : u = b
  · exfalso
    rw [hub] at pon
    rw [hinv.clearAbove b b pcb] at pon
    exact absurd pon (by simp)
  have frHeld : ∀ x : Name, x ≠ b → τ (holding x) = σ (holding x) := by
    intro x hx
    refine fr _ ?_ ?_ ?_ ?_ ?_
    · intro hc; rw [holding_inj] at hc; exact hx hc
    · exact holding_ne_clearA x b
    · exact holding_ne_armEmpty x
    · exact holding_ne_clearA x u
    · exact fun hc => ((Ne.symm (on_ne_holding b u x)).elim hc)
  have frClear : ∀ y : Name, y ≠ b → y ≠ u → τ (clearA y) = σ (clearA y) := by
    intro y hyb hyu
    refine fr _ ?_ ?_ ?_ ?_ ?_
    · exact fun hc => ((Ne.symm (holding_ne_clearA b y)).elim hc)
    · intro hc; rw [clearA_inj] at hc; exact hyb hc
    · exact clearA_ne_armEmpty y
    · intro hc; rw [clearA_inj] at hc; exact hyu hc
    · exact fun hc => ((clearA_ne_on y b u).elim hc)
  have frTable : ∀ x : Name, τ (onTable x) = σ (onTable x) := by
    intro x
    refine fr _ ?_ ?_ ?_ ?_ ?_
    · exact fun hc => ((Ne.symm (holding_ne_onTable b x)).elim hc)
    · exact fun hc => ((Ne.symm (clearA_ne_onTable b x)).elim hc)
    · exact onTableX_ne_armEmpty x
    · exact fun hc => ((Ne.symm (clearA_ne_onTable u x)).elim hc)
    · exact fun hc => ((Ne.symm (on_ne_table b u x)).elim hc)
  -- The schema deletes its `on` atom, so any `on` atom true after an unstack
  -- was true before.
  have frOnAll : ∀ z c : Name, τ (on z c) = true → τ (on z c) = σ (on z c) := by
    intro z c h
    refine fr _ ?_ ?_ ?_ ?_ ?_
    · exact on_ne_holding z c b
    · exact on_ne_clear z c b
    · exact on_ne_empty z c
    · exact on_ne_clear z c u
    · intro hc
      rw [on_inj] at hc
      have hz : z = b := hc.1
      have hcu : c = u := hc.2
      rw [hz, hcu, don] at h
      exact absurd h (by simp)
  -- after an unstack exactly one block is held: the one taken off
  have hb : ∀ x : Name, τ (holding x) = true → x = b := by
    intro x hx
    by_cases hxb : x = b
    · exact hxb
    · rw [frHeld x hxb] at hx
      have h0 := hinv.emptyIff.mp pe x
      rw [h0] at hx
      exact absurd hx (by simp)
  refine
    { oneOn := ?_, oneSupport := ?_, oneHeld := ?_, onNotTable := ?_, emptyIff := ?_,
      heldFree := ?_, heldNotClear := ?_, tableDistinct := ?_, clearAbove := ?_ }
  · intro x c w hx hw
    rw [frOnAll x c hx] at hx
    rw [frOnAll w c hw] at hw
    exact hinv.oneOn x c w hx hw
  · intro x c d hx hd
    rw [frOnAll x c hx] at hx
    rw [frOnAll x d hd] at hd
    exact hinv.oneSupport x c d hx hd
  · intro x y hx hy
    rw [hb x hx, hb y hy]
  · intro x c hx
    by_cases hxc : x = b
    · exfalso
      by_cases hcu : c = u
      · rw [hxc, hcu, don] at hx; exact absurd hx (by simp)
      · rw [hxc] at hx
        rw [frOnAll b c hx] at hx
        exact absurd (hinv.oneSupport b c u hx pon) hcu
    · rw [frOnAll x c hx] at hx
      rw [frTable x]
      exact hinv.onNotTable x c hx
  · refine ⟨?_, ?_⟩
    · intro hem
      rw [de] at hem
      exact absurd hem (by simp)
    · intro hall
      have := hall b
      rw [ah] at this
      exact absurd this (by simp)
  · intro x hx
    have hxb : x = b := hb x hx
    rw [hxb] at hx ⊢
    refine ⟨?_, ?_, ?_⟩
    · intro c
      by_cases hc : τ (on b c) = true
      · by_cases hcu : c = u
        · rw [hcu, don] at hc; exact absurd hc (by simp)
        · rw [frOnAll b c hc] at hc
          exact absurd (hinv.oneSupport b c u hc pon) hcu
      · simpa using hc
    · have ht : σ (onTable b) = false := by
        by_cases ht : σ (onTable b) = true
        · exact absurd (hinv.tableDistinct b u b pon ht) (by simp)
        · simpa using ht
      rw [frTable b]
      exact ht
    · intro w
      by_cases hc : τ (on w b) = true
      · rw [frOnAll w b hc] at hc
        exact absurd hc (by rw [hinv.clearAbove b w pcb]; simp)
      · simpa using hc
  · intro x hx
    rw [hb x hx]
    exact dcb
  · intro x c y hx hy hxy
    rw [hxy] at hx
    have hy' : σ (onTable y) = true := by
      rw [← frTable y]
      exact hy
    by_cases hyb : y = b
    · rw [hyb] at hy'
      exact absurd (hinv.tableDistinct b u b pon hy') (by simp)
    · rw [frOnAll y c hx] at hx
      rw [hinv.onNotTable y c hx] at hy'
      exact absurd hy' (by simp)
  · intro y z hy
    by_cases hyb : y = b
    · rw [hyb] at hy
      rw [dcb] at hy
      exact absurd hy (by simp)
    · by_cases hyu : y = u
      · have hgoal : τ (on z u) = false := by
          by_cases hc : τ (on z u) = true
          · by_cases hz : z = b
            · rw [hz, don] at hc; exact absurd hc (by simp)
            · rw [frOnAll z u hc] at hc
              exact absurd (hinv.oneOn z u b hc pon) hz
          · simpa using hc
        rw [hyu]
        exact hgoal
      · rw [frClear y hyb hyu] at hy
        by_cases hc : τ (on z y) = true
        · rw [frOnAll z y hc] at hc
          rw [hinv.clearAbove y z hy] at hc
          exact absurd hc (by simp)
        · simpa using hc

end Planner.Lifted.Blocksworld

/- -------------------------------------------------------------------------- -/
/-
Reading Blocks World's compiled goal tables on a grounded task.

`goalFactOf` looks an atom up among the task's goal atoms and reads the fact out
of `t.goal` at that atom's own position.  Nothing in `Task.WF` ties those two
arrays together, so what the fact names is a property of the *grounded* task, and
that is what this file supplies: a goal fact the tables store is numbered, names
the atom it was looked up by, and is a goal of the problem.

Every goal quantity the must-move analysis reads — `goalOn`, `goalOnTable` —
is built by `goalFactOf`, so all three facts are needed for each of them.
-/

namespace Planner.Lifted.Blocksworld

open Planner Planner.Pddl Planner.ExampleHeuristics.Blocksworld

variable {d : Domain} {p : Problem} {rel : Bool}

/-- **What a goal fact of the compiled tables names.**  It is numbered, it names
the atom it was looked up by, and that atom is a goal of the problem. -/
theorem goalFactOf_spec {a : GroundAtom} {f : Fact}
    (h : goalFactOf (ground d p rel) a = some f) :
    f < (ground d p rel).factNames.size ∧
      (ground d p rel).factNames.getD f default = a ∧ a ∈ p.goal ∧
      f ∈ (ground d p rel).goal := by
  unfold goalFactOf at h
  rcases hx : (ground d p rel).goalAtoms.zipIdx.find? (fun q => q.1 == a) with _ | x
  · rw [hx] at h; simp at h
  · rw [hx] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hmem : x ∈ (ground d p rel).goalAtoms.zipIdx := Array.mem_of_find?_eq_some hx
    have hb : x.1 = a := by
      have := Array.find?_some hx
      simpa using this
    obtain ⟨-, hlt, hget⟩ := Array.mem_zipIdx hmem
    simp only [Nat.zero_add, Nat.sub_zero] at hlt hget
    obtain ⟨hname, hf⟩ := goal_name_eq d p rel (i := x.2) hlt
    subst h
    have hgs : (ground d p rel).goal.size = (ground d p rel).goalAtoms.size := by
      show (p.goal.toArray.map (fun a =>
        (factIndex (allAtoms (groundedOps d p rel) p.goal.toArray)).1.getD a 0)).size
        = (ground d p rel).goalAtoms.size
      rw [Array.size_map, taskOf_goalAtoms]
    have hlt' : x.2 < (ground d p rel).goal.size := by rw [hgs]; exact hlt
    refine ⟨hf, hname.trans (hget.symm.trans hb), ?_, ?_⟩
    · have hmem2 : a ∈ (ground d p rel).goalAtoms := by
        rw [← hb, hget]; exact Array.getElem_mem hlt
      simpa [taskOf_goalAtoms] using hmem2
    · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt', Option.getD_some]
      exact Array.getElem_mem hlt'

/-- The goal fact stored for a block's goal support is numbered and names the
atom `on(b, c)` it was looked up by. -/
theorem goalOnOf_spec {idx : Name → Option Nat} {b : Name}
    {goalOnAtoms : Array GroundAtom} {f : Fact} {ci : Nat}
    (hgoal : ∀ a ∈ goalOnAtoms, ∃ x c, a = { pred := "on", args := [x, c] })
    (h : goalOnOf (ground d p rel) idx b goalOnAtoms = some (f, ci)) :
    ∃ c, idx c = some ci ∧
      f < (ground d p rel).factNames.size ∧
      (ground d p rel).factNames.getD f default = onAtom b c ∧
      onAtom b c ∈ p.goal ∧ f ∈ (ground d p rel).goal := by
  unfold goalOnOf at h
  obtain ⟨a, hx, h⟩ := Option.bind_eq_some_iff.mp h
  have hmem : a ∈ goalOnAtoms := Array.mem_of_find?_eq_some hx
  have hfirst : (match a.args with | [x, _] => x == b | _ => false) = true := by
    simpa using Array.find?_some hx
  obtain ⟨x, c, rfl⟩ := hgoal a hmem
  dsimp only at h hfirst
  obtain ⟨g, hgf, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨j, hci, h⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hlt, hname, hmemg, hgoalf⟩ := goalFactOf_spec hgf
  have hxb : x = b := eq_of_beq hfirst
  subst hxb
  exact ⟨c, hci, hlt, hname, hmemg, hgoalf⟩

/-- The goal fact stored for a block's `on-table` goal is a goal fact of the
task. -/
theorem goalOnTableOf_spec {b : Name} {goalTableAtoms : Array GroundAtom} {g : Fact}
    (hsub : ∀ a ∈ goalTableAtoms, a.pred = "on-table")
    (h : ((goalTableAtoms.find? fun a => a.args == [b]).bind
      (goalFactOf (ground d p rel))) = some g) :
    g < (ground d p rel).factNames.size ∧
      (ground d p rel).factNames.getD g default = tableAtom b ∧
      g ∈ (ground d p rel).goal := by
  obtain ⟨a, hx, hg⟩ := Option.bind_eq_some_iff.mp h
  have hargs : a.args = [b] := by simpa using Array.find?_some hx
  have hpred := hsub a (Array.mem_of_find?_eq_some hx)
  obtain ⟨hlt, hname, -, hmem⟩ := goalFactOf_spec hg
  refine ⟨hlt, ?_, hmem⟩
  rw [hname]
  show a = { pred := "on-table", args := [b] }
  rw [← hpred, ← hargs]

/-- If a block's table says the goal wants it clear, `clear` of that block is a
goal atom. -/
theorem goalClear_spec {b : Name} {goalClearAtoms : Array GroundAtom}
    (hsub : ∀ a ∈ goalClearAtoms, a ∈ p.goal ∧ a.pred = "clear")
    (h : goalClearAtoms.any (fun a => a.args == [b]) = true) :
    ({ pred := "clear", args := [b] } : GroundAtom) ∈ p.goal := by
  simp only [Array.any_eq_true] at h
  obtain ⟨i, hi, hargs⟩ := h
  obtain ⟨hg, hpred⟩ := hsub goalClearAtoms[i] (Array.getElem_mem hi)
  rwa [show ({ pred := "clear", args := [b] } : GroundAtom) = goalClearAtoms[i] from by
    rw [← hpred, ← (by simpa using hargs : goalClearAtoms[i].args = [b])]]

/-- The block a table says the goal wants carried is named by a goal atom. -/
theorem goalCarriesOf_spec {idx : Name → Option Nat} {b : Name}
    {goalOnAtoms : Array GroundAtom} {x : Nat}
    (hgoal : ∀ a ∈ goalOnAtoms,
      (∃ y c, a = { pred := "on", args := [y, c] }) ∧ a ∈ p.goal)
    (h : goalCarriesOf idx b goalOnAtoms = some x) :
    ∃ y, idx y = some x ∧
      ({ pred := "on", args := [y, b] } : GroundAtom) ∈ p.goal := by
  unfold goalCarriesOf at h
  obtain ⟨a, hx, h⟩ := Option.bind_eq_some_iff.mp h
  have hmem := Array.mem_of_find?_eq_some hx
  have hlast : (match a.args with | [_, c] => c == b | _ => false) = true := by
    simpa using Array.find?_some hx
  obtain ⟨⟨y, c, rfl⟩, hg⟩ := hgoal a hmem
  dsimp only at h hlast
  refine ⟨y, h, ?_⟩
  rw [← eq_of_beq hlast]
  exact hg

/-- A goal atom of one predicate is a goal of the problem. -/
theorem goalAtomsWith_mem {pred : Name} {a : GroundAtom}
    (h : a ∈ (ground d p rel).goalAtomsWith pred) : a ∈ p.goal ∧ a.pred = pred := by
  obtain ⟨hg, hp⟩ := mem_goalAtomsWith h
  refine ⟨?_, hp⟩
  rw [taskOf_goalAtoms] at hg
  simpa using hg

/-! ### The compiled goal tables, read directly

The two lemmas above work on the raw table builders.  These read the compiled
entry at a block index instead, which is the form every later proof wants.
-/

open Planner.ExampleHeuristics.Blocksworld
  (compile blockInfoOf getD_map_lt onAtom tableAtom lt_objectNames_of_getD
    objectName_of_findIdx BlockInfo)

/-- **The goal-support fact a compiled table stores** names `on(b, c)` for the
two blocks its indices pick out, and is a goal fact. -/
theorem compile_goalOn_spec {bi : Nat} {f : Fact} {c : Nat}
    (harity : ∀ a ∈ (ground d p rel).goalAtomsWith "on",
      ∃ x y, a = { pred := "on", args := [x, y] })
    (h : ((compile (ground d p rel)).blocks.getD bi default).goalOn = some (f, c)) :
    f < (ground d p rel).factNames.size ∧
      (ground d p rel).factNames.getD f default
        = onAtom ((ground d p rel).objectNames.getD bi default)
            ((ground d p rel).objectNames.getD c default) ∧
      f ∈ (ground d p rel).goal := by
  have hbi := lt_objectNames_of_getD BlockInfo.goalOn rfl (by rw [h]; simp)
  have h' : goalOnOf (ground d p rel)
      (fun x => (ground d p rel).objectNames.findIdx? (· == x))
      ((ground d p rel).objectNames.getD bi default)
      ((ground d p rel).goalAtomsWith "on") = some (f, c) := by
    unfold compile blockInfoOf at h
    rwa [getD_map_lt _ _ bi _ default hbi] at h
  obtain ⟨cname, hidx, hf, hname, -, hgoal⟩ := goalOnOf_spec harity h'
  exact ⟨hf, by rw [hname, objectName_of_findIdx hidx], hgoal⟩

/-- **The `on-table` goal fact a compiled table stores** names `on-table(b)`,
and is a goal fact. -/
theorem compile_goalOnTable_spec {bi : Nat} {g : Fact}
    (h : ((compile (ground d p rel)).blocks.getD bi default).goalOnTable = some g) :
    g < (ground d p rel).factNames.size ∧
      (ground d p rel).factNames.getD g default
        = tableAtom ((ground d p rel).objectNames.getD bi default) ∧
      g ∈ (ground d p rel).goal := by
  have hbi := lt_objectNames_of_getD BlockInfo.goalOnTable rfl (by rw [h]; simp)
  have h' : ((((ground d p rel).goalAtomsWith "on-table").find?
      fun a => a.args == [(ground d p rel).objectNames.getD bi default]).bind
      (goalFactOf (ground d p rel))) = some g := by
    unfold compile blockInfoOf at h
    rwa [getD_map_lt _ _ bi _ default hbi] at h
  exact goalOnTableOf_spec (fun a ha => (goalAtomsWith_mem ha).2) h'

/-! ### A goal state holds every goal atom

The tables store facts for the goal supports, but not for the `clear` goals or
for the block the goal wants carried — those are read as atoms.  This turns any
goal atom into a fact the goal state makes true.
-/

/-- **Every goal atom holds in a goal state.** -/
theorem goalAtom_holds {s : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (hgoal : ∀ f ∈ (ground d p rel).goal, s.test f = true)
    {a : GroundAtom} (ha : a ∈ p.goal) : σ a = true := by
  have ha' : a ∈ (ground d p rel).goalAtoms := by rw [taskOf_goalAtoms]; simpa using ha
  obtain ⟨i, hi, hget⟩ := Array.getElem_of_mem ha'
  obtain ⟨hname, hf⟩ := goal_name_eq d p rel hi
  rw [hget] at hname
  have hgs : (ground d p rel).goal.size = (ground d p rel).goalAtoms.size := by
    show (p.goal.toArray.map (fun a =>
      (factIndex (allAtoms (groundedOps d p rel) p.goal.toArray)).1.getD a 0)).size
      = (ground d p rel).goalAtoms.size
    rw [Array.size_map, taskOf_goalAtoms]
  have hmem : (ground d p rel).goal.getD i 0 ∈ (ground d p rel).goal := by
    have hlt' : i < (ground d p rel).goal.size := by rw [hgs]; exact hi
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt', Option.getD_some]
    exact Array.getElem_mem hlt'
  rw [← hname, habs.numbered _ (by rw [taskOf_numFacts]; exact hf)]
  exact hgoal _ hmem

end Planner.Lifted.Blocksworld

/- -------------------------------------------------------------------------- -/
/-
Every grounded blocksworld operator is one of the four schemas.

`Proofs/Lifted/BlocksworldInv.lean` says what each schema does to an atom-level
state, and proves the two invariants are kept.  Nothing there builds those shapes
from an actual operator, which is what this file does.

The one subtlety is the add lists.  Grounding may drop an add whose atom the
operator already reads, because it is true anyway.  `add_holds` covers both
cases at once, so the schema proofs never have to look.
-/

namespace Planner.Lifted.Blocksworld

open Planner Planner.Pddl

variable {d : Domain} {p : Problem}

/-- **An atom the schema adds holds after the step.**  Either the operator kept
the add, or the atom was already a precondition — and then it was true before
and the step does not delete it. -/
theorem add_holds {o : AtomOp} (hfa : OpFactsAdd d p o) {y : Atom}
    (hy : y ∈ hfa.inst.schema.add)
    (hdel : instAtom hfa.inst.schema.params hfa.inst.args y ∉ hfa.inst.del)
    {σ : AtomState} (happ : o.applicableA σ) :
    o.applyA σ (instAtom hfa.inst.schema.params hfa.inst.args y) = true := by
  by_cases hpre : instAtom hfa.inst.schema.params hfa.inst.args y ∈ o.pre
  · have hnd : instAtom hfa.inst.schema.params hfa.inst.args y ∉ o.del :=
      fun hc => hdel (hfa.subDel _ hc)
    by_cases hadd : instAtom hfa.inst.schema.params hfa.inst.args y ∈ o.add
    · exact applyA_add σ hadd
    · rw [applyA_frame σ hadd hnd]; exact happ _ hpre
  · exact asserted_of_lists hfa hy hpre σ

/-- An atom outside the instance's add and delete lists does not move. -/
theorem framedList {objects : List TypedName} {o : AtomOp} {i : Instance d objects}
    {a : GroundAtom} (hadd : ∀ g ∈ o.add, g ∈ i.add) (hdel : ∀ g ∈ o.del, g ∈ i.del)
    (h1 : a ∉ i.add) (h2 : a ∉ i.del) (σ : AtomState) :
    o.applyA σ a = σ a :=
  applyA_frame σ (fun hc => h1 (hadd a hc)) (fun hc => h2 (hdel a hc))

/-! ### `pickup` -/

theorem pickup_step (hd : BlocksworldDomain d) {o : AtomOp} (hfa : OpFactsAdd d p o)
    {b : Name} (hs : hfa.inst.schema = pickupA) (ha : hfa.inst.args = [b])
    {σ : AtomState} (happ : o.applicableA σ) :
    PickupStep σ (o.applyA σ) b := by
  obtain ⟨hpc, hpt, hpe, hadd, hdel⟩ := pickup_atoms hfa.inst hs ha
  have hinst : instAtom hfa.inst.schema.params hfa.inst.args (holdingV "?ob")
      = holding b := by rw [hs, ha]; rfl
  refine
    { preClear := pre_holds hfa.toOpFacts hpc (clear_dynamic hd) happ
      preTable := pre_holds hfa.toOpFacts hpt (onTable_dynamic hd) happ
      preEmpty := pre_holds hfa.toOpFacts hpe (armEmpty_dynamic hd) happ
      addHolding := ?_
      delClear := falsified_of_lists hfa.toOpFacts hadd hdel (by simp) (by simp) hpc
        (clear_dynamic hd) σ
      delTable := falsified_of_lists hfa.toOpFacts hadd hdel (by simp) (by simp) hpt
        (onTable_dynamic hd) σ
      delEmpty := falsified_of_lists hfa.toOpFacts hadd hdel (by simp) (by simp) hpe
        (armEmpty_dynamic hd) σ
      frame := fun a h1 h2 h3 h4 =>
        framedList hfa.subAdd hfa.subDel (by rw [hadd]; simp [h1])
          (by rw [hdel]; simp [h2, h3, h4]) σ }
  · have := add_holds hfa (y := holdingV "?ob") (by rw [hs]; simp [pickupA])
      (by rw [hinst, hdel]; simp) happ
    rwa [hinst] at this

/-! ### `putdown` -/

theorem putdown_step (hd : BlocksworldDomain d) {o : AtomOp} (hfa : OpFactsAdd d p o)
    {b : Name} (hs : hfa.inst.schema = putdownA) (ha : hfa.inst.args = [b])
    {σ : AtomState} (happ : o.applicableA σ) :
    PutdownStep σ (o.applyA σ) b := by
  obtain ⟨hpre, hadd, hdel⟩ := putdown_atoms hfa.inst hs ha
  have hph : holding b ∈ hfa.inst.pre := by rw [hpre]; simp
  have hc : instAtom hfa.inst.schema.params hfa.inst.args (clearV "?ob")
      = clearA b := by rw [hs, ha]; rfl
  have he : instAtom hfa.inst.schema.params hfa.inst.args armEmptyV
      = armEmpty := by rw [hs, ha]; rfl
  have ht : instAtom hfa.inst.schema.params hfa.inst.args (onTableV "?ob")
      = onTable b := by rw [hs, ha]; rfl
  refine
    { addClear := ?_
      addEmpty := ?_
      addTable := ?_
      preHeld := pre_holds hfa.toOpFacts hph (holding_dynamic hd) happ
      delHeld := falsified_of_lists hfa.toOpFacts hadd hdel (by simp) (by simp) hph
        (holding_dynamic hd) σ
      frame := fun a h1 h2 h3 h4 =>
        framedList hfa.subAdd hfa.subDel (by rw [hadd]; simp [h2, h4, h3])
          (by rw [hdel]; simp [h1]) σ }
  · have := add_holds hfa (y := clearV "?ob") (by rw [hs]; simp [putdownA])
      (by rw [hc, hdel]; simp) happ
    rwa [hc] at this
  · have := add_holds hfa (y := armEmptyV) (by rw [hs]; simp [putdownA])
      (by rw [he, hdel]; simp) happ
    rwa [he] at this
  · have := add_holds hfa (y := onTableV "?ob") (by rw [hs]; simp [putdownA])
      (by rw [ht, hdel]; simp) happ
    rwa [ht] at this

/-! ### `stack`

`stack(b, b)` would add and delete `clear b` at once, so its shape would be
wrong.  It never fires: its preconditions ask for `b` held and `b` clear, and
`Inv.heldNotClear` says a held block is not clear.
-/

theorem stack_step (hd : BlocksworldDomain d) {o : AtomOp} (hfa : OpFactsAdd d p o)
    {b u : Name} (hs : hfa.inst.schema = stackA) (ha : hfa.inst.args = [b, u])
    {σ : AtomState} (hinv : Inv σ) (happ : o.applicableA σ) :
    StackStep σ (o.applyA σ) b u := by
  obtain ⟨hpu, hph, hadd, hdel⟩ := stack_atoms hfa.inst hs ha
  have hcu : σ (clearA u) = true := pre_holds hfa.toOpFacts hpu (clear_dynamic hd) happ
  have hhb : σ (holding b) = true := pre_holds hfa.toOpFacts hph (holding_dynamic hd) happ
  have hub : u ≠ b := by
    intro h
    rw [h, hinv.heldNotClear b hhb] at hcu
    exact Bool.false_ne_true hcu
  have he : instAtom hfa.inst.schema.params hfa.inst.args armEmptyV
      = armEmpty := by rw [hs, ha]; rfl
  have hcb : instAtom hfa.inst.schema.params hfa.inst.args (clearV "?ob")
      = clearA b := by rw [hs, ha]; rfl
  have hon : instAtom hfa.inst.schema.params hfa.inst.args (onV "?ob" "?underob")
      = on b u := by rw [hs, ha]; rfl
  refine
    { preClearU := hcu
      preHeld := hhb
      addEmpty := ?_
      addClearB := ?_
      addOn := ?_
      delClearU := falsified_of_lists hfa.toOpFacts hadd hdel (by simp [hub])
        (by simp) hpu (clear_dynamic hd) σ
      delHeld := falsified_of_lists hfa.toOpFacts hadd hdel (by simp) (by simp) hph
        (holding_dynamic hd) σ
      frame := fun a h1 h2 h3 h4 h5 =>
        framedList hfa.subAdd hfa.subDel (by rw [hadd]; simp [h3, h2, h5])
          (by rw [hdel]; simp [h4, h1]) σ }
  · have := add_holds hfa (y := armEmptyV) (by rw [hs]; simp [stackA])
      (by rw [he, hdel]; simp) happ
    rwa [he] at this
  · have := add_holds hfa (y := clearV "?ob") (by rw [hs]; simp [stackA])
      (by rw [hcb, hdel]; simp [Ne.symm hub]) happ
    rwa [hcb] at this
  · have := add_holds hfa (y := onV "?ob" "?underob") (by rw [hs]; simp [stackA])
      (by rw [hon, hdel]; simp) happ
    rwa [hon] at this

/-! ### `unstack`

`unstack(b, b)` is ruled out the same way: it asks for `on(b, b)`, and no block
stands above itself.
-/

theorem unstack_step (hd : BlocksworldDomain d) {o : AtomOp} (hfa : OpFactsAdd d p o)
    {b u : Name} (hs : hfa.inst.schema = unstackA) (ha : hfa.inst.args = [b, u])
    {σ : AtomState} (hac : Acyclic σ) (happ : o.applicableA σ) :
    UnstackStep σ (o.applyA σ) b u := by
  obtain ⟨hpon, hpc, hpe, hadd, hdel⟩ := unstack_atoms hfa.inst hs ha
  have hon' : σ (on b u) = true := pre_holds hfa.toOpFacts hpon (on_dynamic hd) happ
  have hbu : b ≠ u := by
    intro h
    rw [h] at hon'
    exact hac u (Relation.TransGen.single hon')
  have hh : instAtom hfa.inst.schema.params hfa.inst.args (holdingV "?ob")
      = holding b := by rw [hs, ha]; rfl
  have hcu : instAtom hfa.inst.schema.params hfa.inst.args (clearV "?underob")
      = clearA u := by rw [hs, ha]; rfl
  refine
    { preOn := hon'
      preClearB := pre_holds hfa.toOpFacts hpc (clear_dynamic hd) happ
      preEmpty := pre_holds hfa.toOpFacts hpe (armEmpty_dynamic hd) happ
      addHeld := ?_
      addClearU := ?_
      delOn := falsified_of_lists hfa.toOpFacts hadd hdel (by simp) (by simp) hpon
        (on_dynamic hd) σ
      delClearB := falsified_of_lists hfa.toOpFacts hadd hdel (by simp [hbu])
        (by simp) hpc (clear_dynamic hd) σ
      delEmpty := falsified_of_lists hfa.toOpFacts hadd hdel (by simp) (by simp) hpe
        (armEmpty_dynamic hd) σ
      frame := fun a h1 h2 h3 h4 h5 =>
        framedList hfa.subAdd hfa.subDel (by rw [hadd]; simp [h1, h4])
          (by rw [hdel]; simp [h5, h2, h3]) σ }
  · have := add_holds hfa (y := holdingV "?ob") (by rw [hs]; simp [unstackA])
      (by rw [hh, hdel]; simp) happ
    rwa [hh] at this
  · have := add_holds hfa (y := clearV "?underob") (by rw [hs]; simp [unstackA])
      (by rw [hcu, hdel]; simp [Ne.symm hbu]) happ
    rwa [hcu] at this

/-! ### Assembling the shape

Every operator is one of the four, and both invariants survive it.

The operators come with `OpFactsAdd`, which is what says a kept add really
holds.  That is available on the unpruned task; with the relevance analysis on,
grounding may drop an add whose fact it judged irrelevant, and then the shape
above is not the right statement to make.
-/

/-- One action of the domain, as one of the four shapes. -/
inductive SchemaShape (σ τ : AtomState) : Prop
  | pickup (b : Name) (h : PickupStep σ τ b)
  | putdown (b : Name) (h : PutdownStep σ τ b)
  | stack (b u : Name) (h : StackStep σ τ b u)
  | unstack (b u : Name) (h : UnstackStep σ τ b u)

/-- **Every operator has one of the four shapes.** -/
theorem schemaShape_of_op (hd : BlocksworldDomain d) {o : AtomOp}
    (hfa : OpFactsAdd d p o) {σ : AtomState} (hinv : Inv σ) (hac : Acyclic σ)
    (happ : o.applicableA σ) : SchemaShape σ (o.applyA σ) := by
  rcases instance_shape hd hfa.inst with
    ⟨b, hs, ha⟩ | ⟨b, hs, ha⟩ | ⟨b, u, hs, ha⟩ | ⟨b, u, hs, ha⟩
  · exact .pickup b (pickup_step hd hfa hs ha happ)
  · exact .putdown b (putdown_step hd hfa hs ha happ)
  · exact .stack b u (stack_step hd hfa hs ha hinv happ)
  · exact .unstack b u (unstack_step hd hfa hs ha hac happ)

/-- **Both invariants are kept by every operator.** -/
theorem inv_preserved_of_op (hd : BlocksworldDomain d) {o : AtomOp}
    (hfa : OpFactsAdd d p o) {σ : AtomState} (hinv : Inv σ) (hac : Acyclic σ)
    (happ : o.applicableA σ) : Inv (o.applyA σ) ∧ Acyclic (o.applyA σ) := by
  cases schemaShape_of_op hd hfa hinv hac happ with
  | pickup b h => exact ⟨h.inv_preserved hinv, h.acyclic_preserved hac⟩
  | putdown b h => exact ⟨h.inv_preserved hinv, h.acyclic_preserved hac⟩
  | stack b u h => exact ⟨h.inv_preserved hinv, h.acyclic_preserved hinv hac⟩
  | unstack b u h => exact ⟨h.inv_preserved hinv, h.acyclic_preserved hac⟩

/-- The unpruned task's operators carry the add facts the shapes need. -/
theorem opFactsAdd_ground_false (d : Domain) (p : Problem) {o : AtomOp}
    (ho : o ∈ groundedOps d p false) : Nonempty (OpFactsAdd d p o) :=
  opFacts_raw_add d p (by rwa [← groundedOps_false])

/-- **Both invariants are transition invariants of the unpruned task.** -/
theorem inv_closed (hd : BlocksworldDomain d) :
    ∀ o ∈ groundedOps d p false, ∀ σ, Inv σ → Acyclic σ → o.applicableA σ →
      Inv (o.applyA σ) ∧ Acyclic (o.applyA σ) := by
  intro o ho σ hinv hac happ
  obtain ⟨hfa⟩ := opFactsAdd_ground_false d p ho
  exact inv_preserved_of_op hd hfa hinv hac happ

end Planner.Lifted.Blocksworld

/- -------------------------------------------------------------------------- -/
/-
From the lifted acyclicity invariant to `Physical.grounded`.

`Proofs/Lifted/BlocksworldInv.lean` proves `Acyclic` — no block stands above
itself — is kept by all four schemas.  `Proofs/Domains/Blocksworld/Grounded.lean`
proves that acyclicity over block *indices* makes towers end.  This file joins
the two: a step of the compiled `climb` is an `on` atom of the abstracted state,
so a compiled cycle is a lifted one.
-/

namespace Planner.Lifted.Blocksworld

open Planner Planner.Pddl

variable {d : Domain} {p : Problem} {rel : Bool}
open Planner.ExampleHeuristics.Blocksworld
  (climb climb_zero climb_succ_left compile supportOf AcyclicIdx onAtom
    supportOf_holds grounded_compile supportOf_fst_lt blocks_size onFacts_ok
    onFacts_names onFacts_snd_lt test_of_atom mem_onFacts_of
    lt_objectNames_of_getD goalOnOf blockInfoOf getD_map_lt Physical
    isHeld isHeld_holds isHeld_lt holdAtom GoalPosition
    supportUnmet_eq_false goalFactOf goalCarriesOf supportOf_lt
    objectName_of_findIdx)

/-- The two spellings of the `on` atom agree. -/
theorem onAtom_eq (a b : Name) : onAtom a b = on a b := rfl

/-- **A compiled climb is a lifted chain.**  Each step reads a true `on` fact,
which the abstracted state holds as an `on` atom. -/
theorem above_of_climb {t : Task} {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    ∀ j x y, 0 < j → climb (compile t) s j x = some y →
      Above σ (t.objectNames.getD x default) (t.objectNames.getD y default) := by
  intro j
  induction j with
  | zero => intro x y h; omega
  | succ j ih =>
      intro x y _ hc
      rw [climb_succ_left] at hc
      rcases hs : supportOf (compile t) s x with _ | c
      · rw [hs] at hc; simp at hc
      · rw [hs, Option.bind_some] at hc
        obtain ⟨f, -, hedge⟩ := supportOf_holds habs hn rfl hs
        rw [onAtom_eq] at hedge
        rcases j with _ | j
        · rw [climb_zero] at hc
          simp only [Option.some.injEq] at hc
          subst hc
          exact Relation.TransGen.single hedge
        · exact (ih c y (by omega) hc).head hedge

/-- **Acyclicity transfers to block indices.** -/
theorem acyclicIdx_of_acyclic {t : Task} {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size)
    (hac : Acyclic σ) : AcyclicIdx (compile t) s := fun b j hj hcon =>
  hac _ (above_of_climb habs hn j b b hj hcon)

/-- **`Physical.grounded` from the lifted invariant.**  Towers of a compiled
blocksworld task end, because no block stands above itself. -/
theorem grounded_of_inv {t : Task} {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size)
    (hpos : 0 < (compile t).blocks.size) (hac : Acyclic σ) (b : Nat) :
    climb (compile t) s (compile t).blocks.size b = none :=
  grounded_compile t s hpos (acyclicIdx_of_acyclic habs hn hac) b

/-! ### At most one block on any block

`Inv.oneOn` says it over names.  Turning it into a statement about indices needs
the object list to name each block once, which is what `hinj` asks for.
-/

/-- **`Physical.unique` from the lifted invariant.** -/
theorem unique_of_inv {t : Task} {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size)
    (hinj : ∀ x y, x < t.objectNames.size → y < t.objectNames.size →
      t.objectNames.getD x default = t.objectNames.getD y default → x = y)
    (hinv : Inv σ) :
    ∀ x y c, supportOf (compile t) s x = some c →
      supportOf (compile t) s y = some c → x = y := by
  intro x y c hx hy
  obtain ⟨-, -, hex⟩ := supportOf_holds habs hn rfl hx
  obtain ⟨-, -, hey⟩ := supportOf_holds habs hn rfl hy
  rw [onAtom_eq] at hex hey
  refine hinj x y ?_ ?_ (hinv.oneOn _ _ _ hex hey)
  · rw [← blocks_size t]; exact supportOf_fst_lt hx
  · rw [← blocks_size t]; exact supportOf_fst_lt hy

/-! ### A met goal support really holds

`Physical.placed` is `Inv.oneSupport` read through the tables: the goal fact of
a block's goal support is one of that block's `on` facts, and at most one of
those is true.
-/

/-- A true entry of a block's table is *the* support: any other true entry names
the same block, and the object list names each block once. -/
theorem supportOf_eq_of_mem {t : Task} {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size)
    (hinj : ∀ x y, x < t.objectNames.size → y < t.objectNames.size →
      t.objectNames.getD x default = t.objectNames.getD y default → x = y)
    (hinv : Inv σ) {bi ci : Nat} {f : Fact}
    (hmem : (f, ci) ∈ ((compile t).blocks.getD bi default).onFacts)
    (htrue : s.test f = true) :
    supportOf (compile t) s bi = some ci := by
  unfold supportOf
  rcases hx : ((compile t).blocks.getD bi default).onFacts.find?
      (fun p => s.test p.1) with _ | y
  · exact absurd (Array.find?_eq_none.mp hx (f, ci) hmem) (by simp [htrue])
  · rw [hx, Option.map_some]
    obtain ⟨hy, hσy⟩ := find?_holds habs hn (onFacts_ok bi) hx
    have hey : σ (onAtom (t.objectNames.getD bi default)
        (t.objectNames.getD y.2 default)) = true := by
      rw [← onFacts_names (ci := y.2) rfl (by simpa using hy)]; exact hσy
    have hef : σ (onAtom (t.objectNames.getD bi default)
        (t.objectNames.getD ci default)) = true := by
      rw [← onFacts_names (ci := ci) rfl hmem,
        ← test_of_atom habs (by rw [hn]; exact onFacts_ok bi (f, ci) hmem)]
      exact htrue
    rw [onAtom_eq] at hey hef
    rw [hinj y.2 ci (by rw [← blocks_size t]; exact onFacts_snd_lt hy)
      (by rw [← blocks_size t]; exact onFacts_snd_lt hmem)
      (hinv.oneSupport _ _ _ hey hef)]

/-- **`Physical.placed` from the lifted invariant.** -/
theorem placed_of_inv {t : Task} {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size)
    (hinj : ∀ x y, x < t.objectNames.size → y < t.objectNames.size →
      t.objectNames.getD x default = t.objectNames.getD y default → x = y)
    (hinv : Inv σ)
    (harity : ∀ a ∈ (ground d p rel).goalAtomsWith "on",
      ∃ x c, a = { pred := "on", args := [x, c] })
    (ht : t = ground d p rel) :
    ∀ b f c, ((compile t).blocks.getD b default).goalOn = some (f, c) →
      ExampleHeuristics.Blocksworld.supportUnmet (compile t) s b = false →
        supportOf (compile t) s b = some c := by
  subst ht
  intro b f c hgo hun
  have hbi : b < (ground d p rel).objectNames.size :=
    lt_objectNames_of_getD ExampleHeuristics.Blocksworld.BlockInfo.goalOn rfl (by rw [hgo]; simp)
  -- The goal fact of the block's goal support is true.
  have htrue : s.test f = true := by
    unfold ExampleHeuristics.Blocksworld.supportUnmet at hun
    simp only [hgo, Bool.or_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_false] at hun
    exact hun.1
  -- And it is one of the block's `on` facts.
  have hgo' : goalOnOf (ground d p rel)
      (fun c => (ground d p rel).objectNames.findIdx? (· == c))
      ((ground d p rel).objectNames.getD b default)
      ((ground d p rel).goalAtomsWith "on") = some (f, c) := by
    unfold compile blockInfoOf at hgo
    rwa [getD_map_lt _ _ b _ default hbi] at hgo
  obtain ⟨cname, hidx, hf, hname, -, -⟩ := goalOnOf_spec harity hgo'
  exact supportOf_eq_of_mem habs hn hinj hinv
    (mem_onFacts_of hbi rfl hf hname hidx) htrue

/-! ### `Physical`, assembled

All three fields now come from the lifted invariant, which
`Proofs/Lifted/BlocksworldInv.lean` proves every schema keeps.  What is left of
the task is `hinj` — the object list names each block once — and `hpos`, that
the task has a block at all.  `Physical.grounded` is false without `hpos`: a
chain of zero steps out of a block is that block.
-/

/-- **`Physical` from the lifted invariant.** -/
theorem physical_of_inv {s : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (hinj : ∀ x y, x < (ground d p rel).objectNames.size →
      y < (ground d p rel).objectNames.size →
      (ground d p rel).objectNames.getD x default
        = (ground d p rel).objectNames.getD y default → x = y)
    (hpos : 0 < (compile (ground d p rel)).blocks.size)
    (harity : ∀ a ∈ (ground d p rel).goalAtomsWith "on",
      ∃ x c, a = { pred := "on", args := [x, c] })
    (hinv : Inv σ) (hac : Acyclic σ) :
    Physical (compile (ground d p rel)) s where
  unique := unique_of_inv habs hn hinj hinv
  grounded := grounded_of_inv habs hn hpos hac
  placed := placed_of_inv habs hn hinj hinv harity rfl

/-! ### The hand, at a goal position

Two of `GoalPosition`'s fields are about the hand, and both come from `Inv`
directly: the hand holds one block, and nothing rests on what it holds.
-/

/-- The two spellings of the `holding` atom agree. -/
theorem holdAtom_eq (a : Name) : holdAtom a = holding a := rfl

/-- **`GoalPosition.heldUnique` from the lifted invariant.** -/
theorem heldUnique_of_inv {t : Task} {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size)
    (hinj : ∀ x y, x < t.objectNames.size → y < t.objectNames.size →
      t.objectNames.getD x default = t.objectNames.getD y default → x = y)
    (hinv : Inv σ) :
    ∀ x y, isHeld (compile t) s x = true → isHeld (compile t) s y = true → x = y := by
  intro x y hx hy
  have hex := isHeld_holds habs hn hx
  have hey := isHeld_holds habs hn hy
  rw [holdAtom_eq] at hex hey
  exact hinj x y (isHeld_lt hx) (isHeld_lt hy) (hinv.oneHeld _ _ hex hey)

/-- **`GoalPosition.nothingOnHeld` from the lifted invariant.** -/
theorem nothingOnHeld_of_inv {t : Task} {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) (hinv : Inv σ) :
    ∀ x y, isHeld (compile t) s y = true → supportOf (compile t) s x ≠ some y := by
  intro x y hy hx
  have hey := isHeld_holds habs hn hy
  rw [holdAtom_eq] at hey
  obtain ⟨-, -, hno⟩ := hinv.heldFree _ hey
  obtain ⟨-, -, hex⟩ := supportOf_holds habs hn rfl hx
  rw [onAtom_eq, hno] at hex
  exact Bool.false_ne_true hex

/-! ### Every goal support is met at a goal state

`supportUnmet` reads only the two goal facts a block's table stores, and both are
goal facts of the task, so a goal state makes both true.
-/

/-- **`GoalPosition.supportsMet` at a goal state.** -/
theorem supportsMet_of_goal {s : State}
    (harity : ∀ a ∈ (ground d p rel).goalAtomsWith "on",
      ∃ x c, a = { pred := "on", args := [x, c] })
    (hgoal : ∀ f ∈ (ground d p rel).goal, s.test f = true) :
    ∀ b, ExampleHeuristics.Blocksworld.supportUnmet
      (compile (ground d p rel)) s b = false := by
  intro b
  refine supportUnmet_eq_false (fun f c hgo => ?_) (fun g hgt => ?_)
  · have hbi := lt_objectNames_of_getD
      ExampleHeuristics.Blocksworld.BlockInfo.goalOn rfl (by rw [hgo]; simp)
    have hgo' : goalOnOf (ground d p rel)
        (fun c => (ground d p rel).objectNames.findIdx? (· == c))
        ((ground d p rel).objectNames.getD b default)
        ((ground d p rel).goalAtomsWith "on") = some (f, c) := by
      unfold compile blockInfoOf at hgo
      rwa [getD_map_lt _ _ b _ default hbi] at hgo
    obtain ⟨-, -, -, -, -, hf⟩ := goalOnOf_spec harity hgo'
    exact hgoal f hf
  · have hbi := lt_objectNames_of_getD
      ExampleHeuristics.Blocksworld.BlockInfo.goalOnTable rfl (by rw [hgt]; simp)
    have hgt' : ((((ground d p rel).goalAtomsWith "on-table").find?
        fun a => a.args == [(ground d p rel).objectNames.getD b default]).bind
        (goalFactOf (ground d p rel))) = some g := by
      unfold compile blockInfoOf at hgt
      rwa [getD_map_lt _ _ b _ default hbi] at hgt
    exact hgoal g (goalOnTableOf_spec
      (fun a ha => (goalAtomsWith_mem ha).2) hgt').2.2

/-! ### Nothing stands where the goal wants space

`blocking` asks two things of the block underneath: does the goal want it clear,
and does the goal want a *different* block on it.  `Inv.clearAbove` answers the
first and `Inv.oneOn` the second.
-/

/-- **`GoalPosition.notBlocking` at a goal state.** -/
theorem notBlocking_of_goal {s : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (hinj : ∀ x y, x < (ground d p rel).objectNames.size →
      y < (ground d p rel).objectNames.size →
      (ground d p rel).objectNames.getD x default
        = (ground d p rel).objectNames.getD y default → x = y)
    (hinv : Inv σ)
    (harity : ∀ a ∈ (ground d p rel).goalAtomsWith "on",
      ∃ y c, a = { pred := "on", args := [y, c] })
    (hgoal : ∀ f ∈ (ground d p rel).goal, s.test f = true) :
    ∀ b, ExampleHeuristics.Blocksworld.blocking
      (compile (ground d p rel)) s b = false := by
  intro b
  simp only [ExampleHeuristics.Blocksworld.blocking]
  rcases hs : supportOf (compile (ground d p rel)) s b with _ | c
  · rfl
  · obtain ⟨-, -, hbc⟩ := supportOf_holds habs hn rfl hs
    rw [onAtom_eq] at hbc
    have hci : c < (ground d p rel).objectNames.size := by
      rw [← blocks_size]; exact supportOf_lt hs
    have hbi : b < (ground d p rel).objectNames.size := by
      rw [← blocks_size]; exact supportOf_fst_lt hs
    have hgclear : ((compile (ground d p rel)).blocks.getD c default).goalClear
        = ((ground d p rel).goalAtomsWith "clear").any
            (fun a => a.args == [(ground d p rel).objectNames.getD c default]) := by
      unfold compile blockInfoOf
      rw [getD_map_lt _ _ c _ default hci]
    have hgcar : ((compile (ground d p rel)).blocks.getD c default).goalCarries
        = goalCarriesOf (fun x => (ground d p rel).objectNames.findIdx? (· == x))
            ((ground d p rel).objectNames.getD c default)
            ((ground d p rel).goalAtomsWith "on") := by
      unfold compile blockInfoOf
      rw [getD_map_lt _ _ c _ default hci]
    simp only [Bool.or_eq_false_iff]
    refine ⟨?_, ?_⟩
    · -- The goal does not want `c` clear: `b` stands on it.
      by_contra hgc
      simp only [Bool.not_eq_false] at hgc
      rw [hgclear] at hgc
      have hclear := goalClear_spec (fun a ha => goalAtomsWith_mem ha) hgc
      have hσ : σ (clearA ((ground d p rel).objectNames.getD c default)) = true :=
        goalAtom_holds habs hgoal hclear
      rw [hinv.clearAbove _ _ hσ] at hbc
      exact Bool.false_ne_true hbc
    · -- Nor a different block on it: `Inv.oneOn` names the same one.
      rcases hgc : ((compile (ground d p rel)).blocks.getD c default).goalCarries with _ | x
      · rfl
      · rw [hgcar] at hgc
        obtain ⟨y, hidx, hmem⟩ :=
          goalCarriesOf_spec (fun a ha => ⟨harity a ha, (goalAtomsWith_mem ha).1⟩) hgc
        have hσ : σ (on y ((ground d p rel).objectNames.getD c default)) = true :=
          goalAtom_holds habs hgoal hmem
        have hyb : y = (ground d p rel).objectNames.getD b default :=
          hinv.oneOn _ _ _ hσ hbc
        have hx : (ground d p rel).objectNames.getD x default = y :=
          objectName_of_findIdx hidx
        have : x = b := hinj x b
          (Array.findIdx?_eq_some_iff_getElem.mp hidx).1 hbi (by rw [hx, hyb])
        simp [this]

/-- **`GoalPosition.noSelfGoal` at a goal state.**  A goal that asked a block to
stand on itself would make that block stand above itself. -/
theorem noSelfGoal_of_goal {s : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (hac : Acyclic σ)
    (harity : ∀ a ∈ (ground d p rel).goalAtomsWith "on",
      ∃ y c, a = { pred := "on", args := [y, c] })
    (hgoal : ∀ f ∈ (ground d p rel).goal, s.test f = true) :
    ∀ b f, ((compile (ground d p rel)).blocks.getD b default).goalOn ≠ some (f, b) := by
  intro b f hgo
  have hbi := lt_objectNames_of_getD
    ExampleHeuristics.Blocksworld.BlockInfo.goalOn rfl (by rw [hgo]; simp)
  have hgo' : goalOnOf (ground d p rel)
      (fun c => (ground d p rel).objectNames.findIdx? (· == c))
      ((ground d p rel).objectNames.getD b default)
      ((ground d p rel).goalAtomsWith "on") = some (f, b) := by
    unfold compile blockInfoOf at hgo
    rwa [getD_map_lt _ _ b _ default hbi] at hgo
  obtain ⟨cname, hidx, -, -, hmem, -⟩ := goalOnOf_spec harity hgo'
  have hc : (ground d p rel).objectNames.getD b default = cname :=
    objectName_of_findIdx hidx
  have hσ : σ (on ((ground d p rel).objectNames.getD b default) cname) = true :=
    goalAtom_holds habs hgoal hmem
  rw [hc] at hσ
  exact hac cname (Relation.TransGen.single hσ)

/-! ### The goal shape, assembled

This is the `hgoal` hypothesis of `improved_admissibleOn_of_schema`: at a goal
state the analysis sees a goal *position*, and the state is physical.  Both now
follow from the two lifted invariants, which every schema keeps.
-/

/-- **`GoalPosition` from the lifted invariants.** -/
theorem goalPosition_of_inv {s : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (hinj : ∀ x y, x < (ground d p rel).objectNames.size →
      y < (ground d p rel).objectNames.size →
      (ground d p rel).objectNames.getD x default
        = (ground d p rel).objectNames.getD y default → x = y)
    (hinv : Inv σ) (hac : Acyclic σ)
    (harity : ∀ a ∈ (ground d p rel).goalAtomsWith "on",
      ∃ y c, a = { pred := "on", args := [y, c] })
    (hgoal : ∀ f ∈ (ground d p rel).goal, s.test f = true) :
    GoalPosition (compile (ground d p rel)) s where
  supportsMet := supportsMet_of_goal harity hgoal
  notBlocking := notBlocking_of_goal habs hn hinj hinv harity hgoal
  heldUnique := heldUnique_of_inv habs hn hinj hinv
  nothingOnHeld := nothingOnHeld_of_inv habs hn hinv
  noSelfGoal := noSelfGoal_of_goal habs hac harity hgoal

/--
**The `hgoal` obligation, discharged.**

`improved_admissibleOn_of_schema` asks that a goal state be a goal position and
be physical.  Both now come from `Inv` and `Acyclic`, which
`Proofs/Lifted/BlocksworldInv.lean` proves every schema keeps.
-/
theorem goalShape_of_inv {s : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (hinj : ∀ x y, x < (ground d p rel).objectNames.size →
      y < (ground d p rel).objectNames.size →
      (ground d p rel).objectNames.getD x default
        = (ground d p rel).objectNames.getD y default → x = y)
    (hpos : 0 < (compile (ground d p rel)).blocks.size)
    (hinv : Inv σ) (hac : Acyclic σ)
    (harity : ∀ a ∈ (ground d p rel).goalAtomsWith "on",
      ∃ y c, a = { pred := "on", args := [y, c] })
    (hgoal : ∀ f ∈ (ground d p rel).goal, s.test f = true) :
    GoalPosition (compile (ground d p rel)) s ∧
      Physical (compile (ground d p rel)) s :=
  ⟨goalPosition_of_inv habs hn hinj hinv hac harity hgoal,
    physical_of_inv habs hn hinj hpos harity hinv hac⟩

end Planner.Lifted.Blocksworld

/- -------------------------------------------------------------------------- -/
/-
From the atom-level shapes to the compiled analysis.

`Proofs/Lifted/BlocksworldStep.lean` turns every operator into one of the four
schema shapes, stated over ground atoms.  The must-move analysis is stated over
the compiled tables and block indices.  This file crosses between them: each
shape becomes a `Grab` or a `Place`.

Every field is one of the readers of `Proofs/Domains/Blocksworld/Step.lean`
applied to one line of the shape.  The two invariants do the rest: `Inv.emptyIff`
says the hand is empty when `arm-empty` holds, `Inv.clearAbove` that nothing
stands on a clear block, `Inv.onNotTable` that a block on the table stands on
nothing.
-/

namespace Planner.Lifted.Blocksworld

open Planner Planner.Pddl
open Planner.ExampleHeuristics.Blocksworld
  (compile Grab Place isHeld supportOf supportUnmet onAtom holdAtom tableAtom
    isHeld_of_none isHeld_false_of isHeld_true_of supportOf_holds supportOf_none_of
    supportOf_congr supportUnmet_congr supportUnmet_mono test_frame test_false
    blocks_getD_out blocks_size BlockInfo lt_objectNames_of_getD
    supportOf_out test_of_atom ClearsOne SchemaStep holdingFact_some Physical
    improved improved_admissibleOn_of_schema clearGoals_sub_goal clearGoals_nodup)

variable {d : Domain} {p : Problem} {rel : Bool}

/-- The two spellings of the `on-table` atom agree. -/
theorem tableAtom_eq (x : Name) : tableAtom x = onTable x := rfl

/-- Out of range the table holds no `holding` fact, so nothing is held there. -/
theorem isHeld_out {t : Task} {s : State} {x : Nat} (hx : t.objectNames.size ≤ x) :
    isHeld (compile t) s x = false :=
  isHeld_of_none (by rw [blocks_getD_out hx]; rfl)

/--
**A `pickup` is a `Grab`.**

The hand was empty, so nothing was held; `b` was clear, so nothing stood on it;
`b` was on the table, so it stood on nothing, and it still stands on nothing
because no `on` atom moves.  The only goal fact that moves is `on-table(b)`,
which falls — so `b`'s own goal support can only become unmet, and no other
block's changes.
-/
theorem grab_of_pickup
    {s s' : State} {σ τ : AtomState}
    (habs : Abstracts (ground d p rel) s σ) (habs' : Abstracts (ground d p rel) s' τ)
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (hinj : ∀ x y, x < (ground d p rel).objectNames.size →
      y < (ground d p rel).objectNames.size →
      (ground d p rel).objectNames.getD x default
        = (ground d p rel).objectNames.getD y default → x = y)
    (harity : ∀ a ∈ (ground d p rel).goalAtomsWith "on",
      ∃ x y, a = { pred := "on", args := [x, y] })
    (hinv : Inv σ) {b : Name} {a : Nat} {fh : Fact}
    (hba : (ground d p rel).objectNames.getD a default = b)
    (haLt : a < (ground d p rel).objectNames.size)
    (hhf : ((compile (ground d p rel)).blocks.getD a default).holdingFact = some fh)
    (hstep : PickupStep σ τ b) :
    Grab (compile (ground d p rel)) s s' a := by
  -- No `on` atom moves.
  have honframe : ∀ x c, τ (onAtom x c) = σ (onAtom x c) := fun x c => by
    rw [onAtom_eq]
    exact hstep.frame _ (by simp) (by simp) (by simp) (by simp)
  -- The hand was empty.
  have hnoheld : ∀ y, σ (holding y) = false := hinv.emptyIff.mp hstep.preEmpty
  -- `b` was on the table, so it stood on nothing, and still does.
  have hbon : ∀ c, τ (onAtom b c) = false := by
    intro c
    rw [honframe, onAtom_eq]
    by_contra hc
    simp only [Bool.not_eq_false] at hc
    have hpt := hstep.preTable
    rw [hinv.onNotTable b c hc] at hpt
    exact Bool.false_ne_true hpt
  refine
    { noneHeld := fun x => isHeld_false_of habs hn (by rw [holdAtom_eq]; exact hnoheld _)
      heldA := isHeld_true_of habs' hn hhf
        (by rw [holdAtom_eq, hba]; exact hstep.addHolding)
      heldOther := ?_
      nothingOn := ?_
      supportA := ?_
      supportOther := fun x _ => supportOf_congr habs habs' hn x (honframe _)
      unmetA := ?_
      unmetOther := ?_
      aLt := by rw [blocks_size]; exact haLt }
  · -- Only `b` is held afterwards, and every other block's `holding` is framed.
    intro x hx
    by_cases hxlt : x < (ground d p rel).objectNames.size
    · have hne : (ground d p rel).objectNames.getD x default ≠ b := fun h =>
        hx (hinj x a hxlt haLt (by rw [h, hba]))
      refine isHeld_false_of habs' hn ?_
      rw [holdAtom_eq, hstep.frame _ (by simpa using hne) (by simp) (by simp) (by simp)]
      exact hnoheld _
    · exact isHeld_out (by omega)
  · -- `b` was clear, so nothing stood on it.
    intro x hxs
    obtain ⟨-, -, hσ⟩ := supportOf_holds habs hn rfl hxs
    rw [onAtom_eq, hba, hinv.clearAbove b _ hstep.preClear] at hσ
    exact Bool.false_ne_true hσ
  · exact supportOf_none_of habs' hn (by rw [hba]; exact hbon)
  · -- `b`'s `on-table` goal fact falls; its `on` goal fact does not move.
    refine supportUnmet_mono (fun f c hgo => ?_) (fun g hgt => ?_)
    · obtain ⟨hf, hname, -⟩ := compile_goalOn_spec harity hgo
      intro ht
      rwa [test_frame habs habs' hn hf (by rw [hname]; exact honframe _ _)] at ht
    · obtain ⟨hg, hgname, -⟩ := compile_goalOnTable_spec hgt
      intro ht
      rw [test_false habs' hn hg (by rw [hgname, hba, tableAtom_eq]; exact hstep.delTable)]
        at ht
      exact absurd ht (by simp)
  · -- No other block's goal facts move.
    intro x hx
    refine supportUnmet_congr (fun f c hgo => ?_) (fun g hgt => ?_)
    · obtain ⟨hf, hname, -⟩ := compile_goalOn_spec harity hgo
      exact test_frame habs habs' hn hf (by rw [hname]; exact honframe _ _)
    · obtain ⟨hg, hgname, -⟩ := compile_goalOnTable_spec hgt
      have hxlt := lt_objectNames_of_getD BlockInfo.goalOnTable rfl (by rw [hgt]; simp)
      have hne : (ground d p rel).objectNames.getD x default ≠ b := fun h =>
        hx (hinj x a hxlt haLt (by rw [h, hba]))
      refine test_frame habs habs' hn hg ?_
      rw [hgname, tableAtom_eq]
      exact hstep.frame _ (by simp) (by simp) (by simpa using hne) (by simp)

/--
**An `unstack` is a `Grab`.**

The only `on` atom that moves is the one taken apart, so every other support is
where it was.  `b` stood on `u`, so by `Inv.oneSupport` it stood on nothing else,
and by `Inv.onNotTable` it was not on the table — which is why its own goal
support can only stay unmet.
-/
theorem grab_of_unstack
    {s s' : State} {σ τ : AtomState}
    (habs : Abstracts (ground d p rel) s σ) (habs' : Abstracts (ground d p rel) s' τ)
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (hinj : ∀ x y, x < (ground d p rel).objectNames.size →
      y < (ground d p rel).objectNames.size →
      (ground d p rel).objectNames.getD x default
        = (ground d p rel).objectNames.getD y default → x = y)
    (harity : ∀ a ∈ (ground d p rel).goalAtomsWith "on",
      ∃ x y, a = { pred := "on", args := [x, y] })
    (hinv : Inv σ) {b u : Name} {a : Nat} {fh : Fact}
    (hba : (ground d p rel).objectNames.getD a default = b)
    (haLt : a < (ground d p rel).objectNames.size)
    (hhf : ((compile (ground d p rel)).blocks.getD a default).holdingFact = some fh)
    (hstep : UnstackStep σ τ b u) :
    Grab (compile (ground d p rel)) s s' a := by
  -- Every `on` atom but the one taken apart is framed.
  have honframe : ∀ x c, ¬(x = b ∧ c = u) → τ (onAtom x c) = σ (onAtom x c) := by
    intro x c hne
    rw [onAtom_eq]
    exact hstep.frame _ (by simp) (by simp) (by simp) (by simp)
      (by simpa using fun h1 h2 => hne ⟨h1, h2⟩)
  have hnoheld : ∀ y, σ (holding y) = false := hinv.emptyIff.mp hstep.preEmpty
  -- `b` stood on `u` and on nothing else, and now stands on nothing.
  have hbon : ∀ c, τ (onAtom b c) = false := by
    intro c
    by_cases hcu : c = u
    · rw [onAtom_eq, hcu]; exact hstep.delOn
    · rw [honframe b c (fun h => hcu h.2), onAtom_eq]
      by_contra hc
      simp only [Bool.not_eq_false] at hc
      exact hcu (hinv.oneSupport b c u hc hstep.preOn)
  -- And it was not on the table.
  have hbtable : σ (onTable b) = false := hinv.onNotTable b u hstep.preOn
  refine
    { noneHeld := fun x => isHeld_false_of habs hn (by rw [holdAtom_eq]; exact hnoheld _)
      heldA := isHeld_true_of habs' hn hhf
        (by rw [holdAtom_eq, hba]; exact hstep.addHeld)
      heldOther := ?_
      nothingOn := ?_
      supportA := supportOf_none_of habs' hn (by rw [hba]; exact hbon)
      supportOther := ?_
      unmetA := ?_
      unmetOther := ?_
      aLt := by rw [blocks_size]; exact haLt }
  · intro x hx
    by_cases hxlt : x < (ground d p rel).objectNames.size
    · have hne : (ground d p rel).objectNames.getD x default ≠ b := fun h =>
        hx (hinj x a hxlt haLt (by rw [h, hba]))
      refine isHeld_false_of habs' hn ?_
      rw [holdAtom_eq, hstep.frame _ (by simpa using hne) (by simp) (by simp)
        (by simp) (by simp)]
      exact hnoheld _
    · exact isHeld_out (by omega)
  · intro x hxs
    obtain ⟨-, -, hσ⟩ := supportOf_holds habs hn rfl hxs
    rw [onAtom_eq, hba, hinv.clearAbove b _ hstep.preClearB] at hσ
    exact Bool.false_ne_true hσ
  · intro x hx
    by_cases hxlt : x < (ground d p rel).objectNames.size
    · have hne : (ground d p rel).objectNames.getD x default ≠ b := fun h =>
        hx (hinj x a hxlt haLt (by rw [h, hba]))
      exact supportOf_congr habs habs' hn x fun c => honframe _ c fun h => hne h.1
    · rw [supportOf_out (by rw [blocks_size]; omega),
        supportOf_out (by rw [blocks_size]; omega)]
  · refine supportUnmet_mono (fun f c hgo ht => ?_) (fun g hgt ht => ?_)
    · obtain ⟨hf, hname, -⟩ := compile_goalOn_spec harity hgo
      rw [hba] at hname
      by_cases hcu : (ground d p rel).objectNames.getD c default = u
      · rw [test_false habs' hn hf
          (by rw [hname, onAtom_eq, hcu]; exact hstep.delOn)] at ht
        exact absurd ht (by simp)
      · rwa [test_frame habs habs' hn hf
          (by rw [hname]; exact honframe _ _ (fun h => hcu h.2))] at ht
    · obtain ⟨hg, hgname, -⟩ := compile_goalOnTable_spec hgt
      rw [hba] at hgname
      have hfr : τ ((ground d p rel).factNames.getD g default)
          = σ ((ground d p rel).factNames.getD g default) := by
        rw [hgname, tableAtom_eq]
        exact hstep.frame _ (by simp) (by simp) (by simp) (by simp) (by simp)
      rw [test_frame habs habs' hn hg hfr, test_of_atom habs (by rw [hn]; exact hg),
        hgname, tableAtom_eq, hbtable] at ht
      exact absurd ht (by simp)
  · intro x hx
    refine supportUnmet_congr (fun f c hgo => ?_) (fun g hgt => ?_)
    · obtain ⟨hf, hname, -⟩ := compile_goalOn_spec harity hgo
      have hxlt := lt_objectNames_of_getD BlockInfo.goalOn rfl (by rw [hgo]; simp)
      have hne : (ground d p rel).objectNames.getD x default ≠ b := fun h =>
        hx (hinj x a hxlt haLt (by rw [h, hba]))
      exact test_frame habs habs' hn hf
        (by rw [hname]; exact honframe _ _ (fun h => hne h.1))
    · obtain ⟨hg, hgname, -⟩ := compile_goalOnTable_spec hgt
      have hfr : τ ((ground d p rel).factNames.getD g default)
          = σ ((ground d p rel).factNames.getD g default) := by
        rw [hgname, tableAtom_eq]
        exact hstep.frame _ (by simp) (by simp) (by simp) (by simp) (by simp)
      exact test_frame habs habs' hn hg hfr

/--
**A `putdown` is a `Place`.**

`b` was held, so by `Inv.heldFree` it stood on nothing, nothing stood on it, and
it was not on the table.  No `on` atom moves, so every support stays; the one
goal fact that moves is `on-table(b)`, which becomes true.
-/
theorem place_of_putdown
    {s s' : State} {σ τ : AtomState}
    (habs : Abstracts (ground d p rel) s σ) (habs' : Abstracts (ground d p rel) s' τ)
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (hinj : ∀ x y, x < (ground d p rel).objectNames.size →
      y < (ground d p rel).objectNames.size →
      (ground d p rel).objectNames.getD x default
        = (ground d p rel).objectNames.getD y default → x = y)
    (harity : ∀ a ∈ (ground d p rel).goalAtomsWith "on",
      ∃ x y, a = { pred := "on", args := [x, y] })
    (hinv : Inv σ) {b : Name} {a : Nat} {fh : Fact}
    (hba : (ground d p rel).objectNames.getD a default = b)
    (haLt : a < (ground d p rel).objectNames.size)
    (hhf : ((compile (ground d p rel)).blocks.getD a default).holdingFact = some fh)
    (hstep : PutdownStep σ τ b) :
    Place (compile (ground d p rel)) s s' a := by
  have honframe : ∀ x c, τ (onAtom x c) = σ (onAtom x c) := fun x c => by
    rw [onAtom_eq]
    exact hstep.frame _ (by simp) (by simp) (by simp) (by simp)
  obtain ⟨hbon, -, hbup⟩ := hinv.heldFree b hstep.preHeld
  have honly : ∀ y, σ (holding y) = true → y = b := fun y hy =>
    hinv.oneHeld y b hy hstep.preHeld
  have hnoheld' : ∀ y, τ (holding y) = false := by
    intro y
    by_cases hyb : y = b
    · rw [hyb]; exact hstep.delHeld
    · rw [hstep.frame _ (by simpa using hyb) (by simp) (by simp) (by simp)]
      by_contra hc
      simp only [Bool.not_eq_false] at hc
      exact hyb (honly y hc)
  refine
    { heldA := isHeld_true_of habs hn hhf (by rw [holdAtom_eq, hba]; exact hstep.preHeld)
      heldOther := ?_
      noneHeld := fun x =>
        isHeld_false_of habs' hn (by rw [holdAtom_eq]; exact hnoheld' _)
      nothingOn := ?_
      nothingOn' := ?_
      supportA := supportOf_none_of habs hn (by rw [hba]; intro c; rw [onAtom_eq]; exact hbon c)
      supportOther := fun x _ => supportOf_congr habs habs' hn x (honframe _)
      unmetA := ?_
      unmetOther := ?_
      aLt := by rw [blocks_size]; exact haLt }
  · intro x hx
    by_cases hxlt : x < (ground d p rel).objectNames.size
    · have hne : (ground d p rel).objectNames.getD x default ≠ b := fun h =>
        hx (hinj x a hxlt haLt (by rw [h, hba]))
      refine isHeld_false_of habs hn ?_
      rw [holdAtom_eq]
      by_contra hc
      simp only [Bool.not_eq_false] at hc
      exact hne (honly _ hc)
    · exact isHeld_out (by omega)
  · intro x hxs
    obtain ⟨-, -, hσ⟩ := supportOf_holds habs hn rfl hxs
    rw [onAtom_eq, hba, hbup] at hσ
    exact Bool.false_ne_true hσ
  · intro x hxs
    obtain ⟨-, -, hσ⟩ := supportOf_holds habs' hn rfl hxs
    rw [hba, honframe, onAtom_eq, hbup] at hσ
    exact Bool.false_ne_true hσ
  · refine supportUnmet_mono (fun f c hgo ht => ?_) (fun g hgt ht => ?_)
    · obtain ⟨hf, hname, -⟩ := compile_goalOn_spec harity hgo
      rwa [test_frame habs habs' hn hf (by rw [hname]; exact honframe _ _)]
    · obtain ⟨hg, hgname, -⟩ := compile_goalOnTable_spec hgt
      rw [hba] at hgname
      rw [test_of_atom habs' (by rw [hn]; exact hg), hgname, tableAtom_eq]
      exact hstep.addTable
  · intro x hx
    refine supportUnmet_congr (fun f c hgo => ?_) (fun g hgt => ?_)
    · obtain ⟨hf, hname, -⟩ := compile_goalOn_spec harity hgo
      exact test_frame habs habs' hn hf (by rw [hname]; exact honframe _ _)
    · obtain ⟨hg, hgname, -⟩ := compile_goalOnTable_spec hgt
      have hxlt := lt_objectNames_of_getD BlockInfo.goalOnTable rfl (by rw [hgt]; simp)
      have hne : (ground d p rel).objectNames.getD x default ≠ b := fun h =>
        hx (hinj x a hxlt haLt (by rw [h, hba]))
      have hfr : τ ((ground d p rel).factNames.getD g default)
          = σ ((ground d p rel).factNames.getD g default) := by
        rw [hgname, tableAtom_eq]
        exact hstep.frame _ (by simp) (by simp) (by simpa using hne) (by simp)
      exact test_frame habs habs' hn hg hfr

/--
**A `stack` is a `Place`.**

Same as `putdown`, with one `on` atom added.  It is added *out of* `b`, and `b`
was held, so nothing stood on `b` before and nothing does after.  `stack(b, b)`
would break that, and `Inv.heldNotClear` rules it out.
-/
theorem place_of_stack
    {s s' : State} {σ τ : AtomState}
    (habs : Abstracts (ground d p rel) s σ) (habs' : Abstracts (ground d p rel) s' τ)
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (hinj : ∀ x y, x < (ground d p rel).objectNames.size →
      y < (ground d p rel).objectNames.size →
      (ground d p rel).objectNames.getD x default
        = (ground d p rel).objectNames.getD y default → x = y)
    (harity : ∀ a ∈ (ground d p rel).goalAtomsWith "on",
      ∃ x y, a = { pred := "on", args := [x, y] })
    (hinv : Inv σ) {b u : Name} {a : Nat} {fh : Fact}
    (hba : (ground d p rel).objectNames.getD a default = b)
    (haLt : a < (ground d p rel).objectNames.size)
    (hhf : ((compile (ground d p rel)).blocks.getD a default).holdingFact = some fh)
    (hstep : StackStep σ τ b u) :
    Place (compile (ground d p rel)) s s' a := by
  obtain ⟨hbon, hbtable, hbup⟩ := hinv.heldFree b hstep.preHeld
  have hub : u ≠ b := by
    intro h
    have hc := hstep.preClearU
    rw [h, hinv.heldNotClear b hstep.preHeld] at hc
    exact Bool.false_ne_true hc
  have honframe : ∀ x c, ¬(x = b ∧ c = u) → τ (onAtom x c) = σ (onAtom x c) := by
    intro x c hne
    rw [onAtom_eq]
    exact hstep.frame _ (by simp) (by simp) (by simp) (by simp)
      (by simpa using fun h1 h2 => hne ⟨h1, h2⟩)
  have honly : ∀ y, σ (holding y) = true → y = b := fun y hy =>
    hinv.oneHeld y b hy hstep.preHeld
  have hnoheld' : ∀ y, τ (holding y) = false := by
    intro y
    by_cases hyb : y = b
    · rw [hyb]; exact hstep.delHeld
    · rw [hstep.frame _ (by simpa using hyb) (by simp) (by simp) (by simp) (by simp)]
      by_contra hc
      simp only [Bool.not_eq_false] at hc
      exact hyb (honly y hc)
  refine
    { heldA := isHeld_true_of habs hn hhf (by rw [holdAtom_eq, hba]; exact hstep.preHeld)
      heldOther := ?_
      noneHeld := fun x =>
        isHeld_false_of habs' hn (by rw [holdAtom_eq]; exact hnoheld' _)
      nothingOn := ?_
      nothingOn' := ?_
      supportA := supportOf_none_of habs hn (by rw [hba]; intro c; rw [onAtom_eq]; exact hbon c)
      supportOther := ?_
      unmetA := ?_
      unmetOther := ?_
      aLt := by rw [blocks_size]; exact haLt }
  · intro x hx
    by_cases hxlt : x < (ground d p rel).objectNames.size
    · have hne : (ground d p rel).objectNames.getD x default ≠ b := fun h =>
        hx (hinj x a hxlt haLt (by rw [h, hba]))
      refine isHeld_false_of habs hn ?_
      rw [holdAtom_eq]
      by_contra hc
      simp only [Bool.not_eq_false] at hc
      exact hne (honly _ hc)
    · exact isHeld_out (by omega)
  · intro x hxs
    obtain ⟨-, -, hσ⟩ := supportOf_holds habs hn rfl hxs
    rw [onAtom_eq, hba, hbup] at hσ
    exact Bool.false_ne_true hσ
  · intro x hxs
    obtain ⟨-, -, hσ⟩ := supportOf_holds habs' hn rfl hxs
    rw [hba, honframe _ _ (fun h => hub h.2.symm), onAtom_eq, hbup] at hσ
    exact Bool.false_ne_true hσ
  · intro x hx
    by_cases hxlt : x < (ground d p rel).objectNames.size
    · have hne : (ground d p rel).objectNames.getD x default ≠ b := fun h =>
        hx (hinj x a hxlt haLt (by rw [h, hba]))
      exact supportOf_congr habs habs' hn x fun c => honframe _ c fun h => hne h.1
    · rw [supportOf_out (by rw [blocks_size]; omega),
        supportOf_out (by rw [blocks_size]; omega)]
  · refine supportUnmet_mono (fun f c hgo ht => ?_) (fun g hgt ht => ?_)
    · obtain ⟨hf, hname, -⟩ := compile_goalOn_spec harity hgo
      rw [hba] at hname
      rw [test_of_atom habs (by rw [hn]; exact hf), hname, onAtom_eq, hbon] at ht
      exact absurd ht (by simp)
    · obtain ⟨hg, hgname, -⟩ := compile_goalOnTable_spec hgt
      rw [hba] at hgname
      rw [test_of_atom habs (by rw [hn]; exact hg), hgname, tableAtom_eq, hbtable] at ht
      exact absurd ht (by simp)
  · intro x hx
    refine supportUnmet_congr (fun f c hgo => ?_) (fun g hgt => ?_)
    · obtain ⟨hf, hname, -⟩ := compile_goalOn_spec harity hgo
      have hxlt := lt_objectNames_of_getD BlockInfo.goalOn rfl (by rw [hgo]; simp)
      have hne : (ground d p rel).objectNames.getD x default ≠ b := fun h =>
        hx (hinj x a hxlt haLt (by rw [h, hba]))
      exact test_frame habs habs' hn hf
        (by rw [hname]; exact honframe _ _ (fun h => hne h.1))
    · obtain ⟨hg, hgname, -⟩ := compile_goalOnTable_spec hgt
      have hfr : τ ((ground d p rel).factNames.getD g default)
          = σ ((ground d p rel).factNames.getD g default) := by
        rw [hgname, tableAtom_eq]
        exact hstep.frame _ (by simp) (by simp) (by simp) (by simp) (by simp)
      exact test_frame habs habs' hn hg hfr

/-! ### What the proof asks of the task

`Pinned` is the check the planner makes when it loads a blocksworld task.  It is
what turns the general lemmas above into statements about one problem.
-/

/-- What a blocksworld task must satisfy for the proof to apply. -/
structure Pinned (d : Domain) (p : Problem) : Prop where
  /-- The four schemas are the ones the parser produces. -/
  domain : BlocksworldDomain d
  /-- The object type is declared, so the grounder walks it. -/
  objectType : "object" ∈ d.typeNames
  /-- The pair passed the planner's own validators.  `namesNodup` below is read
  off it rather than assumed: validation checks the objects for duplicates, the
  constants for duplicates, and rejects an object that shadows a constant. -/
  validated : Validated d p
  /-- The goal's `on` atoms name two blocks. -/
  goalOnPair : ∀ a ∈ p.goal, a.pred = "on" →
    ∃ x y, a = { pred := "on", args := [x, y] }
  /-- The task has a block.  Without one, `Physical.grounded` is false: a chain
  of no steps out of a block is that block. -/
  hasBlock : allObjects d p ≠ []
  /-- The goal names each atom once. -/
  goalNodup : p.goal.Nodup
  /-- The initial state is physical: one block on any block, one block held,
  no tower that loops. -/
  initInv : Inv (fun a => p.init.toArray.contains a) ∧
    Acyclic (fun a => p.init.toArray.contains a)

/-- The object names are distinct — decided by validation, not assumed. -/
theorem Pinned.namesNodup {d : Domain} {p : Problem} (hp : Pinned d p) :
    ((allObjects d p).map (·.name)).Nodup := hp.validated.namesNodup

/-- **The object list names each block once.** -/
theorem objectNames_inj (hp : Pinned d p) (rel : Bool) :
    ∀ x y, x < (ground d p rel).objectNames.size →
      y < (ground d p rel).objectNames.size →
      (ground d p rel).objectNames.getD x default
        = (ground d p rel).objectNames.getD y default → x = y := by
  have hnd : (ground d p rel).objectNames.toList.Nodup := by
    show (((allObjects d p).toArray.map (·.name)).toList).Nodup
    simpa using hp.namesNodup
  intro x y hx hy h
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hx, Option.getD_some,
    Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hy, Option.getD_some] at h
  exact (List.Nodup.getElem_inj_iff hnd
    (hi := by simpa using hx) (hj := by simpa using hy)).mp (by simpa using h)

/-- **The task has a block.** -/
theorem blocks_pos (hp : Pinned d p) (rel : Bool) :
    0 < (compile (ground d p rel)).blocks.size := by
  rw [blocks_size]
  show 0 < ((allObjects d p).toArray.map (·.name)).size
  simp only [Array.size_map, List.size_toArray]
  exact List.length_pos_iff.mpr hp.hasBlock

/-- **The goal's `on` atoms are binary.** -/
theorem goalOn_pair (hp : Pinned d p) (rel : Bool) :
    ∀ a ∈ (ground d p rel).goalAtomsWith "on",
      ∃ x y, a = { pred := "on", args := [x, y] } := fun a ha =>
  let h := goalAtomsWith_mem ha
  hp.goalOnPair a h.1 h.2

/-! ### The atoms a schema names are numbered

`ground_names_instance` numbers every atom a schema instance adds, given that
the parameter types are declared and that the static preconditions were checked.
Blocks World has no static predicate, so the second is vacuous.
-/

/-- Every precondition of every blocksworld schema is dynamic. -/
theorem pre_dynamic (hp : Pinned d p) {objects : List TypedName}
    (i : Instance d objects) {y : Atom} (hy : y ∈ i.schema.pre) :
    (staticPredicates d).contains y.pred = false := by
  rcases instance_shape hp.domain i with
    ⟨b, hs, -⟩ | ⟨b, hs, -⟩ | ⟨b, u, hs, -⟩ | ⟨b, u, hs, -⟩ <;> rw [hs] at hy
  · rcases (by simpa [pickupA] using hy :
      y = clearV "?ob" ∨ y = onTableV "?ob" ∨ y = armEmptyV) with rfl | rfl | rfl
    · exact clear_dynamic hp.domain
    · exact onTable_dynamic hp.domain
    · exact armEmpty_dynamic hp.domain
  · rcases (by simpa [putdownA] using hy : y = holdingV "?ob") with rfl
    exact holding_dynamic hp.domain
  · rcases (by simpa [stackA] using hy :
      y = clearV "?underob" ∨ y = holdingV "?ob") with rfl | rfl
    · exact clear_dynamic hp.domain
    · exact holding_dynamic hp.domain
  · rcases (by simpa [unstackA] using hy :
      y = onV "?ob" "?underob" ∨ y = clearV "?ob" ∨ y = armEmptyV) with rfl | rfl | rfl
    · exact on_dynamic hp.domain
    · exact clear_dynamic hp.domain
    · exact armEmpty_dynamic hp.domain

/-- Every parameter of every blocksworld schema has the declared object type. -/
theorem params_typed (hp : Pinned d p) {objects : List TypedName}
    (i : Instance d objects) : ∀ pm ∈ i.schema.params, pm.type ∈ d.typeNames := by
  intro pm hpm
  have hty : pm.type = "object" := by
    rcases instance_shape hp.domain i with
      ⟨b, hs, -⟩ | ⟨b, hs, -⟩ | ⟨b, u, hs, -⟩ | ⟨b, u, hs, -⟩ <;> rw [hs] at hpm
    · rcases (by simpa [pickupA] using hpm : pm = objP "?ob") with rfl; rfl
    · rcases (by simpa [putdownA] using hpm : pm = objP "?ob") with rfl; rfl
    · rcases (by simpa [stackA] using hpm :
        pm = objP "?ob" ∨ pm = objP "?underob") with rfl | rfl <;> rfl
    · rcases (by simpa [unstackA] using hpm :
        pm = objP "?ob" ∨ pm = objP "?underob") with rfl | rfl <;> rfl
  rw [hty]; exact hp.objectType

/-! ### The adds relevance pruning keeps

Every Blocks World action has an inverse with the same parameters.  The adds of
one are the preconditions of the other:

* `pickup` / `putdown` exchange `holding` with `clear`, `on-table` and
  `arm-empty`;
* `stack` / `unstack` exchange `holding` and the destination's `clear` with
  `on`, the moved block's `clear` and `arm-empty`.

A pruned operator is kept only when it touches the relevant set, and closure
then puts all of its preconditions in that set.  Its inverse consequently
touches those relevant preconditions and puts every one of the original
operator's adds in the set.  This is the domain-specific argument that turns
the generic `OpFacts` for a pruned operator back into `OpFactsAdd`.
-/

/-- A well-typed instance of one of the four schemas occurs in the raw ground
operator list.  Blocks World has no static preconditions. -/
private theorem raw_of_instance (hp : Pinned d p) (i : Instance d (allObjects d p)) :
    mkOp i.schema (i.schema.pre.filter fun x =>
        !(staticPredicates d).contains x.pred) i.args.toArray ∈ rawOps d p := by
  rw [← groundedOps_false]
  refine groundedOps_complete d p i.mem i.args.toArray ?_ (params_typed hp i) ?_ ?_
  · simpa using i.args_length
  · simpa using i.typed
  · intro y hy hstatic
    rw [pre_dynamic hp i hy] at hstatic
    exact absurd hstatic (by simp)

/-- All Blocks World preconditions survive the grounder's static-predicate
filter. -/
private theorem mem_filtered_pre (hp : Pinned d p) (i : Instance d (allObjects d p))
    {y : Atom} (hy : y ∈ i.schema.pre) :
    y ∈ i.schema.pre.filter (fun x => !(staticPredicates d).contains x.pred) := by
  refine List.mem_filter.mpr ⟨hy, ?_⟩
  rw [pre_dynamic hp i hy]
  rfl

private theorem touches_of_add {o : AtomOp} {r : Std.HashSet GroundAtom}
    {x : GroundAtom} (hx : x ∈ o.add) (hr : r.contains x = true) :
    o.touches r = true := by
  simp only [AtomOp.touches, Bool.or_eq_true, Array.any_eq_true]
  obtain ⟨i, hi, hval⟩ := Array.getElem_of_mem hx
  exact Or.inl ⟨i, hi, by rw [hval]; exact hr⟩

/-- The extra fact carried by `OpFactsAdd` is available with relevance pruning
on or off. -/
def AddsKept (d : Domain) (p : Problem) (rel : Bool) : Prop :=
  ∀ o ∈ groundedOps d p rel, Nonempty (OpFactsAdd d p o)

/-- With pruning off, grounding keeps every non-precondition add. -/
theorem addsKept_false : AddsKept d p false := by
  intro o ho
  exact opFacts_raw_add d p (by rwa [groundedOps_false] at ho)

/-- With pruning on, inverse actions force every add of a retained operator to
remain relevant and hence to survive trimming. -/
theorem addsKept_true (hp : Pinned d p) : AddsKept d p true := by
  intro o ho
  rcases relevance_cases (rawOps d p) p.goal.toArray with
    ⟨r, hclosed, -, hrdef⟩ | hall
  · obtain ⟨hf, hpre, hkept⟩ := opFacts_pruned_add d p ho hclosed hrdef
    refine ⟨{ toOpFacts := hf, addComplete := ?_ }⟩
    intro y hy hnotpre
    apply hkept y hy hnotpre
    rcases instance_shape hp.domain hf.inst with
      ⟨b, hs, ha⟩ | ⟨b, hs, ha⟩ | ⟨b, u, hs, ha⟩ | ⟨b, u, hs, ha⟩
    · -- `pickup`: `putdown` reads `holding b` and adds the relevant `clear b`.
      obtain ⟨hclear, -, -, -, -⟩ := pickup_atoms hf.inst hs ha
      have hclearRel : r.contains (clearA b) = true :=
        hpre _ (pre_mem_op hf hclear (clear_dynamic hp.domain))
      let inv : Instance d (allObjects d p) :=
        { schema := putdownA
          mem := by rw [hp.domain]; simp
          args := [b]
          typed := by
            have h := hf.inst.typed
            rw [hs, ha] at h
            exact h }
      let q := mkOp inv.schema (inv.schema.pre.filter fun x =>
        !(staticPredicates d).contains x.pred) inv.args.toArray
      have hraw : q ∈ rawOps d p := raw_of_instance hp inv
      have hadd : clearA b ∈ q.add := by
        dsimp [q, inv]
        have heq : instAtom putdownA.params ([b] : List Name) (clearV "?ob")
            = clearA b := rfl
        rw [← heq]
        refine mem_mkOp_add putdownA _ #[b] (by simp [putdownA]) ?_
        intro z hz
        have hz' : z = holdingV "?ob" := by
          simpa [putdownA] using (List.mem_filter.mp hz).1
        subst z
        simp [instAtom, holdingV, clearV]
      have htouch : q.touches r = true := touches_of_add hadd hclearRel
      have hy' : y = holdingV "?ob" := by
        rw [hs] at hy
        simpa [pickupA] using hy
      subst y
      have hmem : holding b ∈ q.pre := by
        have hfiltered : holdingV "?ob" ∈ inv.schema.pre.filter (fun x =>
            !(staticPredicates d).contains x.pred) :=
          mem_filtered_pre hp inv (by simp [inv, putdownA])
        dsimp [q, inv] at hfiltered ⊢
        exact mem_mkOp_pre putdownA _ #[b] hfiltered
      simpa [hs, ha] using hclosed q hraw htouch _ hmem
    · -- `putdown`: `pickup` reads its three adds and adds relevant `holding b`.
      obtain ⟨hholding, -, -⟩ := putdown_atoms hf.inst hs ha
      have hholdingMem : holding b ∈ hf.inst.pre := by rw [hholding]; simp
      have hholdingRel : r.contains (holding b) = true :=
        hpre _ (pre_mem_op hf hholdingMem (holding_dynamic hp.domain))
      let inv : Instance d (allObjects d p) :=
        { schema := pickupA
          mem := by rw [hp.domain]; simp
          args := [b]
          typed := by
            have h := hf.inst.typed
            rw [hs, ha] at h
            exact h }
      let q := mkOp inv.schema (inv.schema.pre.filter fun x =>
        !(staticPredicates d).contains x.pred) inv.args.toArray
      have hraw : q ∈ rawOps d p := raw_of_instance hp inv
      have hadd : holding b ∈ q.add := by
        dsimp [q, inv]
        have heq : instAtom pickupA.params ([b] : List Name) (holdingV "?ob")
            = holding b := rfl
        rw [← heq]
        refine mem_mkOp_add pickupA _ #[b] (by simp [pickupA]) ?_
        intro z hz
        have hz' : z = clearV "?ob" ∨ z = onTableV "?ob" ∨ z = armEmptyV := by
          simpa [pickupA] using (List.mem_filter.mp hz).1
        rcases hz' with rfl | rfl | rfl <;>
          simp [instAtom, clearV, onTableV, armEmptyV, holdingV]
      have htouch : q.touches r = true := touches_of_add hadd hholdingRel
      have hy' : y = clearV "?ob" ∨ y = armEmptyV ∨ y = onTableV "?ob" := by
        rw [hs] at hy
        simpa [putdownA] using hy
      rcases hy' with rfl | rfl | rfl
      · have hmem : clearA b ∈ q.pre := by
          have hfiltered : clearV "?ob" ∈ inv.schema.pre.filter (fun x =>
              !(staticPredicates d).contains x.pred) :=
            mem_filtered_pre hp inv (by simp [inv, pickupA])
          dsimp [q, inv] at hfiltered ⊢
          exact mem_mkOp_pre pickupA _ #[b] hfiltered
        simpa [hs, ha] using hclosed q hraw htouch _ hmem
      · have hmem : armEmpty ∈ q.pre := by
          have hfiltered : armEmptyV ∈ inv.schema.pre.filter (fun x =>
              !(staticPredicates d).contains x.pred) :=
            mem_filtered_pre hp inv (by simp [inv, pickupA])
          dsimp [q, inv] at hfiltered ⊢
          exact mem_mkOp_pre pickupA _ #[b] hfiltered
        simpa [hs, ha] using hclosed q hraw htouch _ hmem
      · have hmem : onTable b ∈ q.pre := by
          have hfiltered : onTableV "?ob" ∈ inv.schema.pre.filter (fun x =>
              !(staticPredicates d).contains x.pred) :=
            mem_filtered_pre hp inv (by simp [inv, pickupA])
          dsimp [q, inv] at hfiltered ⊢
          exact mem_mkOp_pre pickupA _ #[b] hfiltered
        simpa [hs, ha] using hclosed q hraw htouch _ hmem
    · -- `stack`: `unstack` reads its three adds and adds relevant `holding b`.
      obtain ⟨-, hholding, -, -⟩ := stack_atoms hf.inst hs ha
      have hholdingRel : r.contains (holding b) = true :=
        hpre _ (pre_mem_op hf hholding (holding_dynamic hp.domain))
      let inv : Instance d (allObjects d p) :=
        { schema := unstackA
          mem := by rw [hp.domain]; simp
          args := [b, u]
          typed := by
            have h := hf.inst.typed
            rw [hs, ha] at h
            exact h }
      let q := mkOp inv.schema (inv.schema.pre.filter fun x =>
        !(staticPredicates d).contains x.pred) inv.args.toArray
      have hraw : q ∈ rawOps d p := raw_of_instance hp inv
      have hadd : holding b ∈ q.add := by
        dsimp [q, inv]
        have heq : instAtom unstackA.params ([b, u] : List Name) (holdingV "?ob")
            = holding b := rfl
        rw [← heq]
        refine mem_mkOp_add unstackA _ #[b, u] (by simp [unstackA]) ?_
        intro z hz
        have hz' : z = onV "?ob" "?underob" ∨ z = clearV "?ob" ∨ z = armEmptyV := by
          simpa [unstackA] using (List.mem_filter.mp hz).1
        rcases hz' with rfl | rfl | rfl <;>
          simp [instAtom, onV, clearV, armEmptyV, holdingV]
      have htouch : q.touches r = true := touches_of_add hadd hholdingRel
      have hy' : y = armEmptyV ∨ y = clearV "?ob" ∨ y = onV "?ob" "?underob" := by
        rw [hs] at hy
        simpa [stackA] using hy
      rcases hy' with rfl | rfl | rfl
      · have hmem : armEmpty ∈ q.pre := by
          have hfiltered : armEmptyV ∈ inv.schema.pre.filter (fun x =>
              !(staticPredicates d).contains x.pred) :=
            mem_filtered_pre hp inv (by simp [inv, unstackA])
          dsimp [q, inv] at hfiltered ⊢
          exact mem_mkOp_pre unstackA _ #[b, u] hfiltered
        simpa [hs, ha] using hclosed q hraw htouch _ hmem
      · have hmem : clearA b ∈ q.pre := by
          have hfiltered : clearV "?ob" ∈ inv.schema.pre.filter (fun x =>
              !(staticPredicates d).contains x.pred) :=
            mem_filtered_pre hp inv (by simp [inv, unstackA])
          dsimp [q, inv] at hfiltered ⊢
          exact mem_mkOp_pre unstackA _ #[b, u] hfiltered
        simpa [hs, ha] using hclosed q hraw htouch _ hmem
      · have hmem : on b u ∈ q.pre := by
          have hfiltered : onV "?ob" "?underob" ∈ inv.schema.pre.filter (fun x =>
              !(staticPredicates d).contains x.pred) :=
            mem_filtered_pre hp inv (by simp [inv, unstackA])
          dsimp [q, inv] at hfiltered ⊢
          exact mem_mkOp_pre unstackA _ #[b, u] hfiltered
        simpa [hs, ha] using hclosed q hraw htouch _ hmem
    · -- `unstack`: `stack` reads its two adds and adds relevant `arm-empty`.
      obtain ⟨-, -, harm, -, -⟩ := unstack_atoms hf.inst hs ha
      have harmRel : r.contains armEmpty = true :=
        hpre _ (pre_mem_op hf harm (armEmpty_dynamic hp.domain))
      let inv : Instance d (allObjects d p) :=
        { schema := stackA
          mem := by rw [hp.domain]; simp
          args := [b, u]
          typed := by
            have h := hf.inst.typed
            rw [hs, ha] at h
            exact h }
      let q := mkOp inv.schema (inv.schema.pre.filter fun x =>
        !(staticPredicates d).contains x.pred) inv.args.toArray
      have hraw : q ∈ rawOps d p := raw_of_instance hp inv
      have hadd : armEmpty ∈ q.add := by
        dsimp [q, inv]
        have heq : instAtom stackA.params ([b, u] : List Name) armEmptyV = armEmpty := rfl
        rw [← heq]
        refine mem_mkOp_add stackA _ #[b, u] (by simp [stackA]) ?_
        intro z hz
        have hz' : z = clearV "?underob" ∨ z = holdingV "?ob" := by
          simpa [stackA] using (List.mem_filter.mp hz).1
        rcases hz' with rfl | rfl <;>
          simp [instAtom, clearV, holdingV, armEmptyV]
      have htouch : q.touches r = true := touches_of_add hadd harmRel
      have hy' : y = holdingV "?ob" ∨ y = clearV "?underob" := by
        rw [hs] at hy
        simpa [unstackA] using hy
      rcases hy' with rfl | rfl
      · have hmem : holding b ∈ q.pre := by
          have hfiltered : holdingV "?ob" ∈ inv.schema.pre.filter (fun x =>
              !(staticPredicates d).contains x.pred) :=
            mem_filtered_pre hp inv (by simp [inv, stackA])
          dsimp [q, inv] at hfiltered ⊢
          exact mem_mkOp_pre stackA _ #[b, u] hfiltered
        simpa [hs, ha] using hclosed q hraw htouch _ hmem
      · have hmem : clearA u ∈ q.pre := by
          have hfiltered : clearV "?underob" ∈ inv.schema.pre.filter (fun x =>
              !(staticPredicates d).contains x.pred) :=
            mem_filtered_pre hp inv (by simp [inv, stackA])
          dsimp [q, inv] at hfiltered ⊢
          exact mem_mkOp_pre stackA _ #[b, u] hfiltered
        simpa [hs, ha] using hclosed q hraw htouch _ hmem
  · rw [groundedOps_true, hall] at ho
    exact opFacts_raw_add d p ho

/-- The add-completeness fact is available in either relevance mode. -/
theorem addsKept (hp : Pinned d p) (rel : Bool) : AddsKept d p rel := by
  cases rel with
  | false => exact addsKept_false
  | true => exact addsKept_true hp

/-- **An atom a blocksworld schema adds or deletes is numbered.** -/
theorem names_atom (hp : Pinned d p) (i : Instance d (allObjects d p)) {y : Atom}
    (hy : y ∈ i.schema.add ∨ y ∈ i.schema.del) :
    ∃ f, f < (ground d p false).numFacts ∧
      (ground d p false).factNames.getD f default
        = instAtom i.schema.params i.args y :=
  ground_names_instance d p i (params_typed hp i)
    (fun z hz hstat => absurd hstat (by rw [pre_dynamic hp i hz]; simp)) (Or.inr hy)

/-- **An atom mentioned by a retained operator is numbered**, with relevance
pruning on or off. -/
theorem names_op_atom (rel : Bool) {o : AtomOp} (ho : o ∈ groundedOps d p rel)
    {a : GroundAtom} (ha : a ∈ o.pre ∨ a ∈ o.add ∨ a ∈ o.del) :
    ∃ f, f < (ground d p rel).numFacts ∧
      (ground d p rel).factNames.getD f default = a := by
  obtain ⟨f, hf, hname⟩ := numbered_of_op d p rel ho ha
  exact ⟨f, by simpa using hf, hname⟩

/-- Every schema add is mentioned by an operator carrying `OpFactsAdd`: it is
either already a precondition or survives in the add list. -/
theorem names_added_atom (rel : Bool) {o : AtomOp} (ho : o ∈ groundedOps d p rel)
    (hfa : OpFactsAdd d p o) {y : Atom} (hy : y ∈ hfa.inst.schema.add) :
    ∃ f, f < (ground d p rel).numFacts ∧
      (ground d p rel).factNames.getD f default =
        instAtom hfa.inst.schema.params hfa.inst.args y := by
  by_cases hpre : instAtom hfa.inst.schema.params hfa.inst.args y ∈ o.pre
  · exact names_op_atom rel ho (Or.inl hpre)
  · exact names_op_atom rel ho (Or.inr (Or.inl (hfa.addComplete y hy hpre)))

/-- **An argument of an instance is a block of the task.** -/
theorem mem_objectNames (hp : Pinned d p) (rel : Bool) {b : Name}
    (hw : WellTyped d (allObjects d p) "object" b) :
    ∃ a, a < (ground d p rel).objectNames.size ∧
      (ground d p rel).objectNames.getD a default = b := by
  obtain ⟨ob, hob, hname, -⟩ := hw
  have hmem : b ∈ (ground d p rel).objectNames := by
    show b ∈ (allObjects d p).toArray.map (·.name)
    exact Array.mem_map.mpr ⟨ob, by simpa using hob, hname⟩
  obtain ⟨a, ha, hget⟩ := Array.getElem_of_mem hmem
  exact ⟨a, ha, by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ha, Option.getD_some]
    exact hget⟩

/-! ### At most one `clear` goal becomes true

`ClearsOne` is the last thing `SchemaStep` asks for.  It is about *facts*, and
what the schemas give is about *atoms*, so it needs the numbering to be
injective — otherwise two `clear` goals could name the same atom and both become
true at once.
-/

/-- **Distinct facts name distinct atoms.**  `factIndex` numbers each atom once,
so reading a name back gives the index it was read from. -/
theorem factNames_inj {f g : Fact}
    (hf : f < (ground d p rel).factNames.size)
    (hg : g < (ground d p rel).factNames.size)
    (h : (ground d p rel).factNames.getD f default
      = (ground d p rel).factNames.getD g default) : f = g := by
  have hfn : (ground d p rel).factNames
      = (factIndex (allAtoms (groundedOps d p rel) p.goal.toArray)).2 := rfl
  rw [hfn] at hf hg h
  obtain ⟨-, hf'⟩ := factIndex_rev _ f hf
  obtain ⟨-, hg'⟩ := factIndex_rev _ g hg
  rw [← hf', h, hg']

/--
**One action makes at most one `clear` goal newly true.**

`x` names the `clear` atom the schema adds, when it adds one.  Every other
`clear` goal names an atom the operator cannot add, so it was already true.
-/
theorem clearsOne_of_add {o : AtomOp} (hfo : OpFacts d p o)
    {s s' : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (habs' : Abstracts (ground d p rel) s' (o.applyA σ))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (hwf : Task.WF (ground d p rel)) (x : Fact)
    (hclear : ∀ a ∈ hfo.inst.add, a.pred = "clear" →
      x < (ground d p rel).factNames.size ∧
        (ground d p rel).factNames.getD x default = a) :
    ClearsOne (compile (ground d p rel)) s s' := by
  refine ⟨x, fun f hf hfx ht => ?_⟩
  have hmem : f ∈ (ground d p rel).goalFactsWith ["clear"] := by
    simpa [compile] using hf
  obtain ⟨hgoal, hpred⟩ := mem_goalFactsWith hmem
  have hflt : f < (ground d p rel).numFacts := hwf.goal f hgoal
  have hflt' : f < (ground d p rel).factNames.size := by rw [← hn]; exact hflt
  by_cases hain : (ground d p rel).factNames.getD f default ∈ hfo.inst.add
  · obtain ⟨hxlt, hxname⟩ := hclear _ hain (by simpa using hpred)
    exact absurd (factNames_inj hflt' hxlt hxname.symm) hfx
  · rw [test_of_atom habs' hflt] at ht
    rw [test_of_atom habs hflt]
    exact falls_of_lists hfo rfl hain ht

/-! ### The step, assembled

`SchemaStep` is a `Grab` or a `Place`, `Physical` on both sides, and `ClearsOne`.
Each of the four schemas supplies the first and the last; the two invariants
supply `Physical`.
-/

/--
**Every operator of a blocksworld task moves the analysis as a grab or a
place**, with relevance pruning on or off.

This is the `hstep` obligation of `improved_admissibleOn_of_schema`.
-/
theorem schemaStep_of_op (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (ho : o ∈ groundedOps d p rel) (hfa : OpFactsAdd d p o)
    {s s' : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (habs' : Abstracts (ground d p rel) s' (o.applyA σ))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (hwf : Task.WF (ground d p rel))
    (hinv : Inv σ) (hac : Acyclic σ) (happ : o.applicableA σ) :
    SchemaStep (compile (ground d p rel)) s s' := by
  obtain ⟨hinv', hac'⟩ := inv_preserved_of_op hp.domain hfa hinv hac happ
  have hinj := objectNames_inj hp rel
  have hpos := blocks_pos hp rel
  have harity := goalOn_pair hp rel
  have hphys : Physical (compile (ground d p rel)) s :=
    physical_of_inv habs hn hinj hpos harity hinv hac
  have hphys' : Physical (compile (ground d p rel)) s' :=
    physical_of_inv habs' hn hinj hpos harity hinv' hac'
  rcases instance_shape hp.domain hfa.inst with
    ⟨b, hs, hargs⟩ | ⟨b, hs, hargs⟩ | ⟨b, u, hs, hargs⟩ | ⟨b, u, hs, hargs⟩
  · -- pickup: adds `holding b`, and no `clear` atom at all
    obtain ⟨o1, ho1, hw⟩ := Pddl.Instance.args_one hfa.inst (by rw [hs])
    rw [hargs] at ho1
    obtain rfl : b = o1 := by simpa using ho1
    obtain ⟨a, haLt, hba⟩ := mem_objectNames hp rel hw
    obtain ⟨fh, hfhlt, hfhname⟩ :=
      names_added_atom rel ho hfa (y := holdingV "?ob") (by rw [hs]; simp [pickupA])
    rw [show instAtom hfa.inst.schema.params hfa.inst.args (holdingV "?ob")
      = holding b from by rw [hs, hargs]; rfl] at hfhname
    obtain ⟨g, hg, -⟩ := holdingFact_some haLt hba (by rw [hn] at hfhlt; exact hfhlt)
      (by rw [holdAtom_eq]; exact hfhname)
    obtain ⟨-, -, -, hadd, -⟩ := pickup_atoms hfa.inst hs hargs
    exact .grab a
      (grab_of_pickup habs habs' hn hinj harity hinv hba haLt hg
        (pickup_step hp.domain hfa hs hargs happ))
      hphys hphys'
      (clearsOne_of_add hfa.toOpFacts habs habs' hn hwf 0 (fun x hx hxp => by
        rw [hadd] at hx
        obtain rfl : x = holding b := by simpa using hx
        exact absurd hxp (by simp [holding])))
  · -- putdown: adds `clear b`
    obtain ⟨o1, ho1, hw⟩ := Pddl.Instance.args_one hfa.inst (by rw [hs])
    rw [hargs] at ho1
    obtain rfl : b = o1 := by simpa using ho1
    obtain ⟨a, haLt, hba⟩ := mem_objectNames hp rel hw
    obtain ⟨fh, hfhlt, hfhname⟩ :=
      names_op_atom rel ho (a := holding b) (Or.inl
        (pre_mem_op hfa.toOpFacts (by
          obtain ⟨hpre, -, -⟩ := putdown_atoms hfa.inst hs hargs
          rw [hpre]; simp) (holding_dynamic hp.domain)))
    obtain ⟨g, hg, -⟩ := holdingFact_some haLt hba (by rw [hn] at hfhlt; exact hfhlt)
      (by rw [holdAtom_eq]; exact hfhname)
    obtain ⟨fc, hfclt, hfcname⟩ :=
      names_added_atom rel ho hfa (y := clearV "?ob") (by rw [hs]; simp [putdownA])
    rw [show instAtom hfa.inst.schema.params hfa.inst.args (clearV "?ob")
      = clearA b from by rw [hs, hargs]; rfl] at hfcname
    obtain ⟨-, hadd, -⟩ := putdown_atoms hfa.inst hs hargs
    exact .place a
      (place_of_putdown habs habs' hn hinj harity hinv hba haLt hg
        (putdown_step hp.domain hfa hs hargs happ))
      hphys hphys'
      (clearsOne_of_add hfa.toOpFacts habs habs' hn hwf fc (fun x hx hxp => by
        rw [hadd] at hx
        rcases (by simpa using hx : x = clearA b ∨ x = armEmpty ∨ x = onTable b)
          with rfl | rfl | rfl
        · exact ⟨by rw [← hn]; exact hfclt, hfcname⟩
        · exact absurd hxp (by simp [armEmpty])
        · exact absurd hxp (by simp [onTable])))
  · -- stack: adds `clear b`
    obtain ⟨o1, o2, ho1, hw1, hw2⟩ := Pddl.Instance.args_two hfa.inst (by rw [hs])
    rw [hargs] at ho1
    obtain ⟨rfl, rfl⟩ : b = o1 ∧ u = o2 := by simpa using ho1
    obtain ⟨a, haLt, hba⟩ := mem_objectNames hp rel hw1
    obtain ⟨fh, hfhlt, hfhname⟩ :=
      names_op_atom rel ho (a := holding b) (Or.inl
        (pre_mem_op hfa.toOpFacts (by
          obtain ⟨-, hpre, -, -⟩ := stack_atoms hfa.inst hs hargs
          exact hpre) (holding_dynamic hp.domain)))
    obtain ⟨g, hg, -⟩ := holdingFact_some haLt hba (by rw [hn] at hfhlt; exact hfhlt)
      (by rw [holdAtom_eq]; exact hfhname)
    obtain ⟨fc, hfclt, hfcname⟩ :=
      names_added_atom rel ho hfa (y := clearV "?ob") (by rw [hs]; simp [stackA])
    rw [show instAtom hfa.inst.schema.params hfa.inst.args (clearV "?ob")
      = clearA b from by rw [hs, hargs]; rfl] at hfcname
    obtain ⟨-, -, hadd, -⟩ := stack_atoms hfa.inst hs hargs
    exact .place a
      (place_of_stack habs habs' hn hinj harity hinv hba haLt hg
        (stack_step hp.domain hfa hs hargs hinv happ))
      hphys hphys'
      (clearsOne_of_add hfa.toOpFacts habs habs' hn hwf fc (fun x hx hxp => by
        rw [hadd] at hx
        rcases (by simpa using hx : x = armEmpty ∨ x = clearA b ∨ x = on b u)
          with rfl | rfl | rfl
        · exact absurd hxp (by simp [armEmpty])
        · exact ⟨by rw [← hn]; exact hfclt, hfcname⟩
        · exact absurd hxp (by simp [on])))
  · -- unstack: adds `clear u`
    obtain ⟨o1, o2, ho1, hw1, hw2⟩ := Pddl.Instance.args_two hfa.inst (by rw [hs])
    rw [hargs] at ho1
    obtain ⟨rfl, rfl⟩ : b = o1 ∧ u = o2 := by simpa using ho1
    obtain ⟨a, haLt, hba⟩ := mem_objectNames hp rel hw1
    obtain ⟨fh, hfhlt, hfhname⟩ :=
      names_added_atom rel ho hfa (y := holdingV "?ob") (by rw [hs]; simp [unstackA])
    rw [show instAtom hfa.inst.schema.params hfa.inst.args (holdingV "?ob")
      = holding b from by rw [hs, hargs]; rfl] at hfhname
    obtain ⟨g, hg, -⟩ := holdingFact_some haLt hba (by rw [hn] at hfhlt; exact hfhlt)
      (by rw [holdAtom_eq]; exact hfhname)
    obtain ⟨fc, hfclt, hfcname⟩ :=
      names_added_atom rel ho hfa (y := clearV "?underob") (by rw [hs]; simp [unstackA])
    rw [show instAtom hfa.inst.schema.params hfa.inst.args (clearV "?underob")
      = clearA u from by rw [hs, hargs]; rfl] at hfcname
    obtain ⟨-, -, -, hadd, -⟩ := unstack_atoms hfa.inst hs hargs
    exact .grab a
      (grab_of_unstack habs habs' hn hinj harity hinv hba haLt hg
        (unstack_step hp.domain hfa hs hargs hac happ))
      hphys hphys'
      (clearsOne_of_add hfa.toOpFacts habs habs' hn hwf fc (fun x hx hxp => by
        rw [hadd] at hx
        rcases (by simpa using hx : x = holding b ∨ x = clearA u) with rfl | rfl
        · exact absurd hxp (by simp [holding])
        · exact ⟨by rw [← hn]; exact hfclt, hfcname⟩))

/-! ### The task the grounder builds

Everything above is assembled here into the one statement a caller wants: the
improved heuristic never overestimates on the task the grounder builds from a
blocksworld domain and problem.
-/

/-- Every operator costs one. -/
theorem cost_one (hp : Pinned d p) (rel : Bool) :
    ∀ o ∈ groundedOps d p rel, 1 ≤ o.cost := by
  intro o ho
  obtain ⟨hf⟩ := opFacts_ground d p rel ho
  rw [hf.cost]
  show 1 ≤ hf.inst.schema.cost
  rcases instance_shape hp.domain hf.inst with
    ⟨b, hs, -⟩ | ⟨b, hs, -⟩ | ⟨b, u, hs, -⟩ | ⟨b, u, hs, -⟩ <;> rw [hs] <;> exact Nat.le_refl 1

/-- And so does every operator of the numbered task. -/
theorem ops_cost (hp : Pinned d p) (rel : Bool) :
    ∀ op ∈ (ground d p rel).ops, 1 ≤ op.cost := by
  intro op hop
  have hops : (ground d p rel).ops
      = (groundedOps d p rel).map
        (numberOp (factIndex (allAtoms (groundedOps d p rel) p.goal.toArray)).1) := rfl
  rw [hops, Array.mem_map] at hop
  obtain ⟨o, ho, rfl⟩ := hop
  exact cost_one hp rel o ho

/-- **Both invariants hold at every reachable state**, with relevance pruning
on or off. -/
theorem reach_inv (hp : Pinned d p) (rel : Bool) (hwf : Task.WF (ground d p rel))
    {s : State} (hreach : Reachable (ground d p rel) s) :
    ∃ σ, Abstracts (ground d p rel) s σ ∧ Inv σ ∧ Acyclic σ := by
  obtain ⟨σ, habs, hi, ha⟩ := reachable_abstracts_inv d p rel hwf
    (fun o ho => Nat.lt_of_lt_of_le Nat.zero_lt_one (cost_one hp rel o ho))
    (fun σ => Inv σ ∧ Acyclic σ) hp.initInv
    (fun o ho σ hσ happ => by
      obtain ⟨hfa⟩ := addsKept hp rel o ho
      exact inv_preserved_of_op hp.domain hfa hσ.1 hσ.2 happ) hreach
  exact ⟨σ, habs, hi, ha⟩

/-- **Every operator applicable at a reachable state is a grab or a place.** -/
theorem schemaStep_of_reach (hp : Pinned d p) (rel : Bool)
    (hwf : Task.WF (ground d p rel))
    {s : State} (hreach : Reachable (ground d p rel) s)
    {op : Op} (hop : op ∈ (ground d p rel).ops) (happ : op.applicable s = true) :
    SchemaStep (compile (ground d p rel)) s (op.apply s) := by
  obtain ⟨σ, habs, hinv, hac⟩ := reach_inv hp rel hwf hreach
  have hcost : ∀ o ∈ groundedOps d p rel, 0 < o.cost :=
    fun o ho => Nat.lt_of_lt_of_le Nat.zero_lt_one (cost_one hp rel o ho)
  have hops : (ground d p rel).ops
      = (groundedOps d p rel).map
        (numberOp (factIndex (allAtoms (groundedOps d p rel) p.goal.toArray)).1) := rfl
  rw [hops, Array.mem_map] at hop
  obtain ⟨o, ho, hnum⟩ := hop
  have happA : o.applicableA σ :=
    (assemble_applicable (groundedOps d p rel) p.goal.toArray p.init.toArray
      (allObjects d p).toArray d.name ho habs).mp (by rw [hnum]; exact happ)
  have habs' : Abstracts (ground d p rel) (op.apply s) (o.applyA σ) := by
    rw [← hnum]
    exact assemble_apply (groundedOps d p rel) p.goal.toArray p.init.toArray
      (allObjects d p).toArray d.name ho (hcost o ho) (hreach.wf hwf) habs
  obtain ⟨hfa⟩ := addsKept hp rel o ho
  exact schemaStep_of_op hp rel ho hfa habs habs' rfl hwf hinv hac happA

/-- The task's goal names each fact once. -/
theorem goal_nodup (hp : Pinned d p) (rel : Bool) :
    ((ground d p rel).goal).toList.Nodup := by
  show ((p.goal.toArray.map (fun a =>
    (factIndex (allAtoms (groundedOps d p rel) p.goal.toArray)).1.getD a 0)).toList).Nodup
  rw [Array.toList_map]
  refine List.Nodup.map_on (fun a ha b hb h => ?_) (by simpa using hp.goalNodup)
  have hma : a ∈ allAtoms (groundedOps d p rel) p.goal.toArray := by
    unfold allAtoms
    exact Array.mem_append.mpr (Or.inr (by simpa using ha))
  have hmb : b ∈ allAtoms (groundedOps d p rel) p.goal.toArray := by
    unfold allAtoms
    exact Array.mem_append.mpr (Or.inr (by simpa using hb))
  exact factIndex_injective' _ (factIndex_contains _ hma) (factIndex_contains _ hmb) h

/--
**Blocks World's improved heuristic never overestimates** on the task the
grounder builds, at every state the search can reach, with relevance pruning on
or off.
-/
theorem improved_admissible_of_pinned (hp : Pinned d p) (rel : Bool) :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel))
      (improved (ground d p rel)).eval := by
  have hwf : Task.WF (ground d p rel) :=
    ground_wf d p rel fun o ho =>
      Nat.lt_of_lt_of_le Nat.zero_lt_one (cost_one hp rel o ho)
  refine improved_admissibleOn_of_schema _ _ ?_ (clearGoals_sub_goal _)
    (clearGoals_nodup _ (goal_nodup hp rel)) ?_ ?_ (ops_cost hp rel)
  · exact fun s i s' _ hr hstep => Reachable.step hr i hstep
  · intro s hr hg
    obtain ⟨σ, habs, hinv, hac⟩ := reach_inv hp rel hwf hr
    exact goalShape_of_inv habs rfl (objectNames_inj hp rel) (blocks_pos hp rel)
      hinv hac (goalOn_pair hp rel) hg
  · exact fun op hop s _ hr happ => schemaStep_of_reach hp rel hwf hr hop happ

/-- Backwards-compatible spelling for the unpruned theorem. -/
theorem improved_admissible (hp : Pinned d p) (_hwf : Task.WF (ground d p false)) :
    (ground d p false).AdmissibleOn (Reachable (ground d p false))
      (improved (ground d p false)).eval :=
  improved_admissible_of_pinned hp false

/-- **Blocks World's improved heuristic is zero at every reachable goal.** -/
theorem improved_goalAware_of_pinned (hp : Pinned d p) (rel : Bool) :
    (ground d p rel).GoalAwareOn (Reachable (ground d p rel))
      (improved (ground d p rel)).eval := by
  have hwf : Task.WF (ground d p rel) :=
    ground_wf d p rel fun o ho =>
      Nat.lt_of_lt_of_le Nat.zero_lt_one (cost_one hp rel o ho)
  refine ExampleHeuristics.Blocksworld.improved_goalAwareOn_of_schema _ _ (clearGoals_sub_goal _) ?_
  intro s hr hg
  obtain ⟨σ, habs, hinv, hac⟩ := reach_inv hp rel hwf hr
  exact goalShape_of_inv habs rfl (objectNames_inj hp rel) (blocks_pos hp rel)
    hinv hac (goalOn_pair hp rel) hg

/-- **And is consistent on the states the search can reach.** -/
theorem improved_consistent_of_pinned (hp : Pinned d p) (rel : Bool) :
    (ground d p rel).ConsistentOn (Reachable (ground d p rel))
      (improved (ground d p rel)).eval := by
  have hwf : Task.WF (ground d p rel) :=
    ground_wf d p rel fun o ho =>
      Nat.lt_of_lt_of_le Nat.zero_lt_one (cost_one hp rel o ho)
  exact ExampleHeuristics.Blocksworld.improved_consistentOn_of_schema _ _
    (clearGoals_nodup _ (goal_nodup hp rel))
    (fun op hop s _ hr happ => schemaStep_of_reach hp rel hwf hr hop happ)
    (ops_cost hp rel)

/-! ### The executable certificate -/

open ExampleHeuristics.Blocksworld.Certificate in
/-- The physical invariant, decoded from the certificate's Boolean. -/
theorem inv_of_check {p : Problem}
    (h : ExampleHeuristics.Blocksworld.Certificate.initInvCheck p = true) :
    Inv (fun a => p.init.toArray.contains a) := by
  simp only [ExampleHeuristics.Blocksworld.Certificate.initInvCheck, Bool.and_eq_true,
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  have hpairs : Planner.Certificate.initPairs p "on" = initPairs p "on" := rfl
  have honesT : Planner.Certificate.initOnes p "on-table" = initOnes p "on-table" := rfl
  have honesH : Planner.Certificate.initOnes p "holding" = initOnes p "holding" := rfl
  have honesC : Planner.Certificate.initOnes p "clear" = initOnes p "clear" := rfl
  have monP : ∀ {x c : Name}, (p.init.toArray.contains (on x c)) = true →
      (x, c) ∈ Planner.Certificate.initPairs p "on" := by
    intro x c hx
    rw [hpairs]
    exact mem_initPairs.mpr (by simpa using hx)
  have monT : ∀ {x : Name}, (p.init.toArray.contains (onTable x)) = true →
      x ∈ Planner.Certificate.initOnes p "on-table" := by
    intro x hx
    rw [honesT]
    exact mem_initOnes.mpr (by simpa using hx)
  have monH : ∀ {x : Name}, (p.init.toArray.contains (holding x)) = true →
      x ∈ Planner.Certificate.initOnes p "holding" := by
    intro x hx
    rw [honesH]
    exact mem_initOnes.mpr (by simpa using hx)
  have monC : ∀ {x : Name}, (p.init.toArray.contains (clearA x)) = true →
      x ∈ Planner.Certificate.initOnes p "clear" := by
    intro x hx
    rw [honesC]
    exact mem_initOnes.mpr (by simpa using hx)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x c u hx hu
    have := h1 (x, c) (monP hx) (u, c) (monP hu)
    simpa using this
  · intro x c e hc he
    have := h2 (x, c) (monP hc) (x, e) (monP he)
    simpa using this
  · intro x y hx hy
    have := h3 x (monH hx) y (monH hy)
    simpa using this
  · intro x c hx
    have := h4 (x, c) (monP hx)
    simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at this
    by_contra hcon
    simp only [Bool.not_eq_false] at hcon
    exact this (monT hcon)
  · constructor
    · intro hae x
      by_contra hcon
      simp only [Bool.not_eq_false] at hcon
      have hne : ¬ (Planner.Certificate.initOnes p "holding").isEmpty = true := by
        intro hemp
        have := monH hcon
        rw [List.isEmpty_iff] at hemp
        rw [hemp] at this
        simp at this
      simp only [beq_iff_eq] at h5
      rw [← h5] at hne
      exact hne (by simpa using hae)
    · intro hno
      have hemp : (Planner.Certificate.initOnes p "holding") = [] := by
        rcases hlist : Planner.Certificate.initOnes p "holding" with _ | ⟨x, rest⟩
        · rfl
        · exfalso
          have hx : x ∈ Planner.Certificate.initOnes p "holding" := by
            rw [hlist]; exact List.mem_cons_self ..
          rw [honesH] at hx
          have := mem_initOnes.mp hx
          have hcon := hno x
          have hmem : (holding x) ∈ p.init := this
          have : (p.init.toArray.contains (holding x)) = true := by simpa using hmem
          rw [this] at hcon
          exact Bool.noConfusion hcon
      simp only [beq_iff_eq] at h5
      have : (Planner.Certificate.initOnes p "holding").isEmpty = true := by
        rw [hemp]; rfl
      rw [← h5] at this
      simpa using this
  · intro x hx
    have hb := h6 x (monH hx)
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
      List.contains_eq_mem, decide_eq_false_iff_not] at hb
    obtain ⟨⟨hons, htab⟩, hcl⟩ := hb
    refine ⟨?_, ?_, ?_⟩
    · intro c
      by_contra hcon
      simp only [Bool.not_eq_false] at hcon
      have := hons (x, c) (monP hcon)
      simp at this
    · by_contra hcon
      simp only [Bool.not_eq_false] at hcon
      exact htab (monT hcon)
    · intro z
      by_contra hcon
      simp only [Bool.not_eq_false] at hcon
      have := hons (z, x) (monP hcon)
      simp at this
  · intro x hx
    have hb := h6 x (monH hx)
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at hb
    by_contra hcon
    simp only [Bool.not_eq_false] at hcon
    exact hb.2 (monC hcon)
  · intro x c y hx hy
    have := h7 (x, c) (monP hx) y (monT hy)
    simpa using this
  · intro y z hy
    by_contra hcon
    simp only [Bool.not_eq_false] at hcon
    have := h8 y (monC hy) (z, y) (monP hcon)
    simp at this

open ExampleHeuristics.Blocksworld.Certificate in
/-- With one support per block, the recorded support is the one `:init` names. -/
theorem support_of_on {p : Problem}
    (hinv : Inv (fun a => p.init.toArray.contains a)) {x c : Name}
    (h : (p.init.toArray.contains (on x c)) = true) : ExampleHeuristics.Blocksworld.Certificate.supportOf p x = some c := by
  have hmem : (x, c) ∈ Planner.Certificate.initPairs p "on" := by
    show (x, c) ∈ initPairs p "on"
    exact mem_initPairs.mpr (by simpa using h)
  rw [ExampleHeuristics.Blocksworld.Certificate.supportOf]
  rcases hf : (Planner.Certificate.initPairs p "on").find? (fun y => y.1 == x) with _ | e
  · exfalso
    have := List.find?_eq_none.mp hf (x, c) hmem
    simp at this
  · have he : e ∈ Planner.Certificate.initPairs p "on" := List.mem_of_find?_eq_some hf
    have hfst : e.1 = x := by
      have := List.find?_some hf
      simpa using this
    have hon : (p.init.toArray.contains (on e.1 e.2)) = true := by
      have : ({ pred := "on", args := [e.1, e.2] } : GroundAtom) ∈ p.init := by
        refine mem_initPairs.mp ?_
        show (e.1, e.2) ∈ initPairs p "on"
        simpa using he
      simpa [on] using this
    rw [hfst] at hon
    have hce : c = e.2 := hinv.oneSupport x c e.2 h hon
    subst hce
    rw [hf]
    rfl

open ExampleHeuristics.Blocksworld.Certificate in
theorem climb_add (p : Problem) (a b : Nat) (x : Name) :
    climb p (a + b) x = (climb p a x).bind (climb p b) := by
  induction a generalizing x with
  | zero => simp [climb]
  | succ k ih =>
      have h1 : k + 1 + b = (k + b) + 1 := by omega
      rw [h1]
      show (ExampleHeuristics.Blocksworld.Certificate.supportOf p x).bind (climb p (k + b)) = _
      rw [show climb p (k + 1) x = (ExampleHeuristics.Blocksworld.Certificate.supportOf p x).bind (climb p k) from rfl,
        Option.bind_assoc]
      congr 1
      funext y
      exact ih y

open ExampleHeuristics.Blocksworld.Certificate in
/-- A tower read upwards is a climb of the same length. -/
theorem climb_of_above {p : Problem}
    (hinv : Inv (fun a => p.init.toArray.contains a)) {x y : Name}
    (h : Above (fun a => p.init.toArray.contains a) x y) :
    ∃ m, 1 ≤ m ∧ climb p m x = some y := by
  induction h with
  | single hxy =>
      refine ⟨1, Nat.le_refl _, ?_⟩
      rw [show climb p 1 x = (ExampleHeuristics.Blocksworld.Certificate.supportOf p x).bind (climb p 0) from rfl,
        support_of_on hinv hxy]
      rfl
  | tail _ hbc ih =>
      obtain ⟨m, hm, hcm⟩ := ih
      refine ⟨m + 1, by omega, ?_⟩
      rw [climb_add, hcm]
      show climb p 1 _ = _
      rw [show ∀ z, climb p 1 z = (ExampleHeuristics.Blocksworld.Certificate.supportOf p z).bind (climb p 0) from fun _ => rfl,
        support_of_on hinv hbc]
      rfl

open ExampleHeuristics.Blocksworld.Certificate in
/-- A climb that returns to its start repeats for ever. -/
theorem climb_mul {p : Problem} {x : Name} {m : Nat} (h : climb p m x = some x) :
    ∀ q, climb p (q * m) x = some x := by
  intro q
  induction q with
  | zero => simp [climb]
  | succ k ih =>
      have hq : (k + 1) * m = k * m + m := by ring
      rw [hq, climb_add, ih]
      exact h

open ExampleHeuristics.Blocksworld.Certificate in
/-- **No block stands above itself**, once every climb falls off. -/
theorem acyclic_of_check {p : Problem}
    (hinv : Inv (fun a => p.init.toArray.contains a))
    (h : ExampleHeuristics.Blocksworld.Certificate.acyclicCheck p = true) :
    Acyclic (fun a => p.init.toArray.contains a) := by
  intro x hx
  obtain ⟨y, hxy, -⟩ := Relation.TransGen.head'_iff.mp hx
  obtain ⟨m, hm1, hmx⟩ := climb_of_above hinv hx
  have hmem : (x, y) ∈ Planner.Certificate.initPairs p "on" := by
    show (x, y) ∈ initPairs p "on"
    exact mem_initPairs.mpr (by simpa using hxy)
  rw [ExampleHeuristics.Blocksworld.Certificate.acyclicCheck, List.all_eq_true] at h
  have hnone : climb p ((Planner.Certificate.initPairs p "on").length + 1) x = none := by
    have hb := h (x, y) hmem
    simpa using hb
  have hq := climb_mul hmx ((Planner.Certificate.initPairs p "on").length + 1)
  have hge : (Planner.Certificate.initPairs p "on").length + 1
      ≤ ((Planner.Certificate.initPairs p "on").length + 1) * m :=
    Nat.le_mul_of_pos_right _ (by omega)
  obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hge
  rw [hs, climb_add, hnone] at hq
  simp at hq

theorem certificate_sound {d : Domain} {p : Problem}
    (hv : Validated d p)
    (h : ExampleHeuristics.Blocksworld.Certificate.certified d p = true) :
    Pinned d p := by
  simp only [ExampleHeuristics.Blocksworld.Certificate.certified, ExampleHeuristics.Blocksworld.Certificate.conditions, Certificate.passes,
    List.all_cons, List.all_nil, Bool.and_eq_true] at h
  rcases h with ⟨hactions, hobject, hgoalOn, hblock, hgoalNodup, hinit, hacyclic, -⟩
  refine
    { domain := by simpa using hactions
      objectType := by simpa using hobject
      validated := hv
      goalOnPair := ?_
      hasBlock := ?_
      goalNodup := of_decide_eq_true hgoalNodup
      initInv := ⟨inv_of_check hinit, acyclic_of_check (inv_of_check hinit) hacyclic⟩ }
  · rw [List.all_eq_true] at hgoalOn
    intro a ha hpred
    have hb := hgoalOn a ha
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hb
    rcases hb with hne | hlen
    · exact absurd hpred hne
    · refine ⟨a.args.getD 0 "", a.args.getD 1 "", ?_⟩
      obtain ⟨pred, args⟩ := a
      simp only at hpred hlen ⊢
      subst hpred
      have hargs : args = [args.getD 0 "", args.getD 1 ""] := list_eq_two hlen
      rw [← hargs]
  · intro hnil
    rw [hnil] at hblock
    simp at hblock

theorem improved_goalAware_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool)
    (h : ExampleHeuristics.Blocksworld.Certificate.certified d p = true) :
    (ground d p rel).GoalAwareOn (Reachable (ground d p rel))
      (improved (ground d p rel)).eval :=
  improved_goalAware_of_pinned (certificate_sound hv h) rel

theorem improved_consistent_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool)
    (h : ExampleHeuristics.Blocksworld.Certificate.certified d p = true) :
    (ground d p rel).ConsistentOn (Reachable (ground d p rel))
      (improved (ground d p rel)).eval :=
  improved_consistent_of_pinned (certificate_sound hv h) rel

theorem improved_proof_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool) :
    ImprovedProof d p rel
      (ExampleHeuristics.Blocksworld.Certificate.certified d p)
      (improved (ground d p rel)) :=
  { goalAware := improved_goalAware_of_certificate hv rel
    consistent := improved_consistent_of_certificate hv rel }

theorem improved_admissible_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool)
    (h : ExampleHeuristics.Blocksworld.Certificate.certified d p = true) :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel))
      (improved (ground d p rel)).eval :=
  (improved_proof_of_certificate hv rel).admissible h

end Planner.Lifted.Blocksworld
