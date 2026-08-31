/-
Miconic's improved heuristic, proved end to end in one file.

The order below is the order the argument is built in.  The first two sections
are the schema-level proof: the improved value over the domain's own data, and
what each schema does to the counters.  The rest lifts that value to the parsed
domain, compiles it against the numbered task, and ends with the four
certificate theorems the registry depends on.

The runtime heuristic, its data, and its certificate stay under `Planner/`.  The
simple heuristic of this domain is proved in `Proofs/Domains/MiconicSimple.lean`.
-/
import Proofs.Combinators
import Proofs.Certificates
import Proofs.SchemaSupport
import Proofs.LiftedHeuristic
import Proofs.FactTables
import Proofs.CompileSupport
import Proofs.Heuristic
import Planner.ExampleHeuristics.Miconic.Improved
import Planner.ExampleHeuristics.Miconic.Domain
import Planner.ExampleHeuristics.Miconic.Certificate

/- -------------------------------------------------------------------------- -/
/-
Miconic, improved heuristic: goal-aware, consistent, admissible.

The heuristic counts three things: the passengers still waiting, those aboard and
unserved, and the distinct floors still to visit other than the one the lift is
on.  The value is `2W + A + N`, and `Effect` below says how one action may move
those three — one constructor per schema family.

  * `board` moves a passenger from waiting to riding, so `2W + A` falls by exactly
    one.  It must not also lower `N`, and it does not: `board` requires the lift to
    be at the passenger's origin, so that floor is the one the lift is on and `N`
    never counted it.
  * `depart` removes a rider, so `2W + A` falls by one, and the same argument
    applies to the destination floor.
  * `up` and `down` leave `W` and `A` alone and change which floor is excluded
    from `N`, so `N` moves by at most one.  This is where `up`/`down` reaching any
    floor in a single step is used: no distance table would say more.

There are no dead ends in this domain — every state can still be served — so the
value is the numeric part alone.

What is assumed rather than checked: that each grounded operator induces one of
the four effects.  For `board` and `depart` that assumption carries the fact that
the lift is at the floor in question, which is where a certificate would have to
look at the operator's precondition.
-/

namespace Planner.ExampleHeuristics.Miconic

open Planner

/-! ### The three quantities -/

/-- Passengers still waiting. -/
abbrev Wc (d : Data) (s : State) : Nat := (waiting d s).size
/-- Passengers aboard and unserved. -/
abbrev Ac (d : Data) (s : State) : Nat := (riding d s).size
/-- Distinct floors still needed, other than the current one. -/
abbrev Nc (d : Data) (s : State) : Nat := (neededFloors d s).length

/-- How an action may move the three quantities: one constructor per schema family. -/
inductive Effect (d : Data) (s s' : State) : Prop
  | board (hW : Wc d s' + 1 = Wc d s) (hA : Ac d s + 1 = Ac d s') (hN : Nc d s ≤ Nc d s')
  | depart (hW : Wc d s' = Wc d s) (hA : Ac d s' + 1 = Ac d s) (hN : Nc d s ≤ Nc d s')
  | move (hW : Wc d s' = Wc d s) (hA : Ac d s' = Ac d s) (hN : Nc d s ≤ Nc d s' + 1)
  | other (hW : Wc d s' = Wc d s) (hA : Ac d s' = Ac d s) (hN : Nc d s ≤ Nc d s')

/-! ### The step -/

private theorem step_arith (W A N W' A' N' cost : Nat) (hcost : 1 ≤ cost)
    (h : (W' + 1 = W ∧ A + 1 = A' ∧ N ≤ N') ∨
         (W' = W ∧ A' + 1 = A ∧ N ≤ N') ∨
         (W' = W ∧ A' = A ∧ N ≤ N' + 1) ∨
         (W' = W ∧ A' = A ∧ N ≤ N')) :
    2 * W + A + N ≤ cost + (2 * W' + A' + N') := by
  rcases h with ⟨h1,h2,h3⟩|⟨h1,h2,h3⟩|⟨h1,h2,h3⟩|⟨h1,h2,h3⟩ <;> omega

theorem value_step (d : Data) (s s' : State) (he : Effect d s s')
    (cost : Nat) (hcost : 1 ≤ cost) : value d s ≤ cost + value d s' := by
  show 2 * Wc d s + Ac d s + Nc d s ≤ cost + (2 * Wc d s' + Ac d s' + Nc d s')
  refine step_arith _ _ _ _ _ _ cost hcost ?_
  cases he with
  | board hW hA hN => exact Or.inl ⟨hW, hA, hN⟩
  | depart hW hA hN => exact Or.inr (Or.inl ⟨hW, hA, hN⟩)
  | move hW hA hN => exact Or.inr (Or.inr (Or.inl ⟨hW, hA, hN⟩))
  | other hW hA hN => exact Or.inr (Or.inr (Or.inr ⟨hW, hA, hN⟩))

/-! ### Assembly -/

theorem unserved_empty (d : Data) (s : State)
    (hall : ∀ p ∈ d.passengers, s.test p.goalFact = true) : unserved d s = #[] := by
  unfold unserved
  rw [Array.filter_eq_empty_iff]
  intro x hx
  simp [hall x hx]

theorem value_eq_zero_of_goal (d : Data) (s : State)
    (hall : ∀ p ∈ d.passengers, s.test p.goalFact = true) : value d s = 0 := by
  unfold value waiting riding neededFloors
  rw [unserved_empty d s hall]
  rfl

theorem improved_goalAware (t : Task)
    (hcompiled : ∀ p ∈ (compile t).passengers, p.goalFact ∈ t.goal) :
    t.GoalAware (improved t).eval := by
  refine t.goalAware_of _ fun s _ hgoal => ?_
  exact value_eq_zero_of_goal _ s fun p hp => hgoal _ (hcompiled p hp)

theorem improved_consistent (t : Task)
    (heff : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      Effect (compile t) s (op.apply s))
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost) :
    t.Consistent (improved t).eval :=
  t.consistent_of_ops _ fun op hop s hs happ =>
    value_step _ s _ (heff op hop s hs happ) op.cost (hcost op hop)

/-- Never overestimates the cost of reaching the goal. -/
theorem improved_admissible (t : Task)
    (hcompiled : ∀ p ∈ (compile t).passengers, p.goalFact ∈ t.goal)
    (heff : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      Effect (compile t) s (op.apply s))
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost) :
    t.Admissible (improved t).eval :=
  t.admissible _ (improved_goalAware t hcompiled) (improved_consistent t heff hcost)


/-! ### Discharging the goal-count component from the operator

`Effect`'s hypotheses are statements about states, but the goal count follows from
facts about the operator alone — which of the family's goals it adds, which it
deletes — and those are decidable.  These two lemmas make that step, so a
certificate can establish it rather than a hypothesis assuming it.
-/

/-- `depart` achieves exactly one outstanding goal, so one fewer remains. -/
theorem goalCount_drop_one (d : Data) {n : Nat} {op : Op} {s : State}
    (hop : Op.WF n op) (hs : State.WF n s) (hnd : (d.passengers).toList.Nodup)
    (x : _) (hx : x ∈ d.passengers)
    (hxadd : op.add.contains ((·.goalFact) x) = true) (hxs : s.test ((·.goalFact) x) = false)
    (hother : ∀ y ∈ d.passengers, y ≠ x → op.add.contains ((·.goalFact) y) = false)
    (hdel : ∀ y ∈ d.passengers, op.del.contains ((·.goalFact) y) = false) :
    ((d.passengers).filter fun y => !(op.apply s).test ((·.goalFact) y)).size + 1
      = ((d.passengers).filter fun y => !s.test ((·.goalFact) y)).size :=
  unmet_drop_one d.passengers (·.goalFact) hop hs hnd x hx hxadd hxs hother hdel

/-- Any operator touching none of the passengers still unserved leaves the count alone. -/
theorem goalCount_unchanged (d : Data) {n : Nat} {op : Op} {s : State}
    (hop : Op.WF n op) (hs : State.WF n s)
    (hadd : ∀ y ∈ d.passengers, op.add.contains ((·.goalFact) y) = false)
    (hdel : ∀ y ∈ d.passengers, op.del.contains ((·.goalFact) y) = false) :
    ((d.passengers).filter fun y => !(op.apply s).test ((·.goalFact) y)).size
      = ((d.passengers).filter fun y => !s.test ((·.goalFact) y)).size :=
  unmet_unchanged d.passengers (·.goalFact) hop hs hadd hdel


/-! ### Discharging the floors the lift must still visit

`board` and `depart` only ever discharge a floor the lift is already on, which the count excludes, so the set never shrinks; `up` and `down` change which floor is excluded, so it gains at most one.  Both follow from how the length of a deduplicated list moves, so the
obligation reduces to a membership statement about the underlying collection.
-/

theorem set_mono (d : Data) (s s' : State) {l l' : List Nat}
    (hl : neededFloors d s = distinct l) (hl' : neededFloors d s' = distinct l')
    (h : ∀ x ∈ l, x ∈ l') : Nc d s ≤ Nc d s' := by
  show (neededFloors d s).length ≤ (neededFloors d s').length
  rw [hl, hl']
  exact length_distinct_mono l l' h

theorem set_le_succ (d : Data) (s s' : State) {l l' : List Nat} (a : Nat)
    (hl : neededFloors d s = distinct l) (hl' : neededFloors d s' = distinct l')
    (h : ∀ x ∈ l, x ∈ l' ∨ x = a) : Nc d s ≤ Nc d s' + 1 := by
  show (neededFloors d s).length ≤ (neededFloors d s').length + 1
  rw [hl, hl']
  exact length_distinct_le_succ l l' a h

end Planner.ExampleHeuristics.Miconic

/- -------------------------------------------------------------------------- -/
/-
Miconic, stated at the schema level.

`Proofs/Domains/Miconic/Improved.lean` assumes `Effect`: a statement about the
heuristic's own counters, one constructor per schema family, taken on trust.  This
file replaces it with `SchemaStep`, which says only what the *domain's schemas* do
to the predicates the heuristic reads — where the lift is, who is aboard, who is
served, where a passenger waits — and then *proves* the movement of the counters.

Two differences are the point of the exercise.

  * Nothing here mentions `waiting`, `riding` or `neededFloors`.  The shapes are
    syntactic, so a grounding argument can discharge them; the counters are
    derived.
  * There is no `other` constructor.  Miconic has four schemas and `up` and `down`
    have the same shape, so three cases cover the domain.  `Effect`'s fourth
    constructor exists only because that assumption ranged over arbitrary
    operators.
-/

namespace Planner.ExampleHeuristics.Miconic

open Planner

/-! ### The state, read in the domain's vocabulary -/

/-- The floor a passenger is still recorded as waiting on. -/
def originFloor (p : PassengerInfo) (s : State) : Option Nat :=
  (p.originFacts.find? fun x => s.test x.1).map (·.2)

theorem floorsNeeded_eq (d : Data) (s : State) (p : PassengerInfo) :
    floorsNeeded d s p =
      (if aboard p s then [] else (originFloor p s).toList) ++ p.destFloor.toList := by
  unfold floorsNeeded originFloor
  by_cases h : aboard p s <;>
    cases hf : p.originFacts.find? (fun x => s.test x.1) <;>
    cases hd : p.destFloor <;>
    simp [h, hf]

/-- Waiting: unserved and not aboard. -/
def predW (s : State) (p : PassengerInfo) : Bool := !aboard p s && !s.test p.goalFact

/-- Riding: unserved and aboard. -/
def predA (s : State) (p : PassengerInfo) : Bool := aboard p s && !s.test p.goalFact

theorem Wc_eq (d : Data) (s : State) :
    Wc d s = (d.passengers.toList.filter (predW s)).length := by
  show (waiting d s).size = _
  unfold waiting unserved predW
  rw [← Array.length_toList, Array.toList_filter, Array.toList_filter, List.filter_filter]

theorem Ac_eq (d : Data) (s : State) :
    Ac d s = (d.passengers.toList.filter (predA s)).length := by
  show (riding d s).size = _
  unfold riding unserved predA
  rw [← Array.length_toList, Array.toList_filter, Array.toList_filter, List.filter_filter]

/-! ### What each schema does

Every field is a statement about the predicates of the domain.  No field mentions
a quantity the heuristic computes.
-/

/-- `board ?f ?p`: the lift stands at `f`, `p` waits there, and `p` gets aboard. -/
structure BoardStep (d : Data) (s s' : State) (f : Nat) (q : PassengerInfo) : Prop where
  memQ : q ∈ d.passengers
  liftAt : currentFloor d s = some f
  liftSame : currentFloor d s' = currentFloor d s
  originQ : originFloor q s = some f
  aboardQ : aboard q s = false
  aboardQ' : aboard q s' = true
  unservedQ : s.test q.goalFact = false
  frameServed : ∀ p ∈ d.passengers, s'.test p.goalFact = s.test p.goalFact
  frameAboard : ∀ p ∈ d.passengers, p ≠ q → aboard p s' = aboard p s
  frameOrigin : ∀ p ∈ d.passengers, p ≠ q → originFloor p s' = originFloor p s

/-- `depart ?f ?p`: the lift stands at `p`'s destination and `p` alights. -/
structure DepartStep (d : Data) (s s' : State) (f : Nat) (q : PassengerInfo) : Prop where
  memQ : q ∈ d.passengers
  liftAt : currentFloor d s = some f
  liftSame : currentFloor d s' = currentFloor d s
  destQ : q.destFloor = some f
  aboardQ : aboard q s = true
  unservedQ : s.test q.goalFact = false
  servedQ' : s'.test q.goalFact = true
  frameServed : ∀ p ∈ d.passengers, p ≠ q → s'.test p.goalFact = s.test p.goalFact
  frameAboard : ∀ p ∈ d.passengers, p ≠ q → aboard p s' = aboard p s
  frameOrigin : ∀ p ∈ d.passengers, p ≠ q → originFloor p s' = originFloor p s

/-- `up ?f1 ?f2` and `down ?f1 ?f2`: only the lift moves. -/
structure MoveStep (d : Data) (s s' : State) (g : Nat) : Prop where
  liftAt' : currentFloor d s' = some g
  frameServed : ∀ p ∈ d.passengers, s'.test p.goalFact = s.test p.goalFact
  frameAboard : ∀ p ∈ d.passengers, aboard p s' = aboard p s
  frameOrigin : ∀ p ∈ d.passengers, originFloor p s' = originFloor p s

/-- One action of the domain, in the schema's own terms. -/
inductive SchemaStep (d : Data) (s s' : State) : Prop
  | board (f : Nat) (q : PassengerInfo) (h : BoardStep d s s' f q)
  | depart (f : Nat) (q : PassengerInfo) (h : DepartStep d s s' f q)
  | move (g : Nat) (h : MoveStep d s s' g)

/-! ### The counters, derived from the shapes

Everything below is what `Effect` currently assumes.
-/

theorem mem_unserved {d : Data} {s : State} {p : PassengerInfo} :
    p ∈ (unserved d s).toList ↔ p ∈ d.passengers ∧ s.test p.goalFact = false := by
  simp [unserved]

/-! #### `board` -/

theorem BoardStep.Wc_drop {d : Data} {s s' : State} {f : Nat} {q : PassengerInfo}
    (h : BoardStep d s s' f q) (hnd : d.passengers.toList.Nodup) :
    Wc d s' + 1 = Wc d s := by
  rw [Wc_eq, Wc_eq]
  refine length_filter_erase_one _ (predW s) (predW s') q (by simpa using h.memQ) hnd
    (by simp [predW, h.aboardQ, h.unservedQ]) (by simp [predW, h.aboardQ']) ?_
  intro y hy hne
  have hm : y ∈ d.passengers := by simpa using hy
  simp [predW, h.frameServed y hm, h.frameAboard y hm hne]

theorem BoardStep.Ac_gain {d : Data} {s s' : State} {f : Nat} {q : PassengerInfo}
    (h : BoardStep d s s' f q) (hnd : d.passengers.toList.Nodup) :
    Ac d s + 1 = Ac d s' := by
  rw [Ac_eq, Ac_eq]
  have hq : s'.test q.goalFact = false := by
    rw [h.frameServed q h.memQ]; exact h.unservedQ
  refine length_filter_erase_one _ (predA s') (predA s) q (by simpa using h.memQ) hnd
    (by simp [predA, h.aboardQ', hq]) (by simp [predA, h.aboardQ]) ?_
  intro y hy hne
  have hm : y ∈ d.passengers := by simpa using hy
  simp [predA, h.frameServed y hm, h.frameAboard y hm hne]

theorem BoardStep.Nc_mono {d : Data} {s s' : State} {f : Nat} {q : PassengerInfo}
    (h : BoardStep d s s' f q) : Nc d s ≤ Nc d s' := by
  refine set_mono d s s' rfl rfl ?_
  intro x hx
  rw [List.mem_filter] at hx
  obtain ⟨hxm, hxf⟩ := hx
  rw [List.mem_flatMap] at hxm
  obtain ⟨p, hp, hxp⟩ := hxm
  rw [mem_unserved] at hp
  have hxne : currentFloor d s ≠ some x := by simpa using hxf
  rw [List.mem_filter, List.mem_flatMap]
  refine ⟨⟨p, ?_, ?_⟩, ?_⟩
  · rw [mem_unserved]
    exact ⟨hp.1, by rw [h.frameServed p hp.1]; exact hp.2⟩
  · by_cases hpq : p = q
    · subst hpq
      rw [floorsNeeded_eq] at hxp ⊢
      simp only [h.aboardQ, h.originQ, Bool.false_eq_true, if_false, Option.toList,
        List.singleton_append, List.mem_cons] at hxp
      simp only [h.aboardQ', if_true, List.nil_append]
      rcases hxp with rfl | hxp
      · exact absurd h.liftAt hxne
      · exact hxp
    · rw [floorsNeeded_eq] at hxp ⊢
      rw [h.frameAboard p hp.1 hpq, h.frameOrigin p hp.1 hpq]
      exact hxp
  · simpa [h.liftSame] using hxne

/-! #### `depart` -/

theorem DepartStep.Wc_same {d : Data} {s s' : State} {f : Nat} {q : PassengerInfo}
    (h : DepartStep d s s' f q) : Wc d s' = Wc d s := by
  rw [Wc_eq, Wc_eq]
  refine length_filter_congr _ (predW s') (predW s) ?_
  intro y hy
  have hm : y ∈ d.passengers := by simpa using hy
  by_cases hne : y = q
  · subst hne
    simp [predW, h.servedQ', h.aboardQ]
  · simp [predW, h.frameServed y hm hne, h.frameAboard y hm hne]

theorem DepartStep.Ac_drop {d : Data} {s s' : State} {f : Nat} {q : PassengerInfo}
    (h : DepartStep d s s' f q) (hnd : d.passengers.toList.Nodup) :
    Ac d s' + 1 = Ac d s := by
  rw [Ac_eq, Ac_eq]
  refine length_filter_erase_one _ (predA s) (predA s') q (by simpa using h.memQ) hnd
    (by simp [predA, h.aboardQ, h.unservedQ]) (by simp [predA, h.servedQ']) ?_
  intro y hy hne
  have hm : y ∈ d.passengers := by simpa using hy
  simp [predA, h.frameServed y hm hne, h.frameAboard y hm hne]

theorem DepartStep.Nc_mono {d : Data} {s s' : State} {f : Nat} {q : PassengerInfo}
    (h : DepartStep d s s' f q) : Nc d s ≤ Nc d s' := by
  refine set_mono d s s' rfl rfl ?_
  intro x hx
  rw [List.mem_filter] at hx
  obtain ⟨hxm, hxf⟩ := hx
  rw [List.mem_flatMap] at hxm
  obtain ⟨p, hp, hxp⟩ := hxm
  rw [mem_unserved] at hp
  have hxne : currentFloor d s ≠ some x := by simpa using hxf
  have hpq : p ≠ q := by
    rintro rfl
    rw [floorsNeeded_eq] at hxp
    simp only [h.aboardQ, if_true, List.nil_append, h.destQ, Option.toList,
      List.mem_singleton] at hxp
    exact hxne (by rw [hxp]; exact h.liftAt)
  rw [List.mem_filter, List.mem_flatMap]
  refine ⟨⟨p, ?_, ?_⟩, ?_⟩
  · rw [mem_unserved]
    exact ⟨hp.1, by rw [h.frameServed p hp.1 hpq]; exact hp.2⟩
  · rw [floorsNeeded_eq] at hxp ⊢
    rw [h.frameAboard p hp.1 hpq, h.frameOrigin p hp.1 hpq]
    exact hxp
  · simpa [h.liftSame] using hxne

/-! #### `up` and `down` -/

theorem MoveStep.Wc_same {d : Data} {s s' : State} {g : Nat} (h : MoveStep d s s' g) :
    Wc d s' = Wc d s := by
  rw [Wc_eq, Wc_eq]
  refine length_filter_congr _ (predW s') (predW s) ?_
  intro y hy
  have hm : y ∈ d.passengers := by simpa using hy
  simp [predW, h.frameServed y hm, h.frameAboard y hm]

theorem MoveStep.Ac_same {d : Data} {s s' : State} {g : Nat} (h : MoveStep d s s' g) :
    Ac d s' = Ac d s := by
  rw [Ac_eq, Ac_eq]
  refine length_filter_congr _ (predA s') (predA s) ?_
  intro y hy
  have hm : y ∈ d.passengers := by simpa using hy
  simp [predA, h.frameServed y hm, h.frameAboard y hm]

theorem MoveStep.Nc_le_succ {d : Data} {s s' : State} {g : Nat} (h : MoveStep d s s' g) :
    Nc d s ≤ Nc d s' + 1 := by
  refine set_le_succ d s s' g rfl rfl ?_
  intro x hx
  rw [List.mem_filter] at hx
  obtain ⟨hxm, hxf⟩ := hx
  rw [List.mem_flatMap] at hxm
  obtain ⟨p, hp, hxp⟩ := hxm
  rw [mem_unserved] at hp
  by_cases hxg : x = g
  · exact Or.inr hxg
  · refine Or.inl ?_
    rw [List.mem_filter, List.mem_flatMap]
    refine ⟨⟨p, ?_, ?_⟩, ?_⟩
    · rw [mem_unserved]
      exact ⟨hp.1, by rw [h.frameServed p hp.1]; exact hp.2⟩
    · rw [floorsNeeded_eq] at hxp ⊢
      rw [h.frameAboard p hp.1, h.frameOrigin p hp.1]
      exact hxp
    · simp [h.liftAt', Ne.symm hxg]

/-! ### The consistency step, with nothing about the counters assumed -/

theorem value_step_of_schema (d : Data) (s s' : State)
    (hnd : d.passengers.toList.Nodup) (he : SchemaStep d s s')
    (cost : Nat) (hcost : 1 ≤ cost) : value d s ≤ cost + value d s' := by
  refine value_step d s s' ?_ cost hcost
  cases he with
  | board f q h => exact .board (h.Wc_drop hnd) (h.Ac_gain hnd) h.Nc_mono
  | depart f q h => exact .depart h.Wc_same (h.Ac_drop hnd) h.Nc_mono
  | move g h => exact .move h.Wc_same h.Ac_same h.Nc_le_succ

/-! ### Admissibility, with the shapes as the only assumption about the operators -/

theorem improved_consistent_of_schema (t : Task)
    (hnd : (compile t).passengers.toList.Nodup)
    (hstep : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      SchemaStep (compile t) s (op.apply s))
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost) :
    t.Consistent (improved t).eval :=
  t.consistent_of_ops _ fun op hop s hs happ =>
    value_step_of_schema _ s _ hnd (hstep op hop s hs happ) op.cost (hcost op hop)

/-- Zero at every goal state, assuming only what the schemas do. -/
theorem improved_goalAware_of_schema (t : Task)
    (hcompiled : ∀ p ∈ (compile t).passengers, p.goalFact ∈ t.goal) :
    t.GoalAware (improved t).eval := improved_goalAware t hcompiled

theorem improved_admissible_of_schema (t : Task)
    (hcompiled : ∀ p ∈ (compile t).passengers, p.goalFact ∈ t.goal)
    (hnd : (compile t).passengers.toList.Nodup)
    (hstep : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      SchemaStep (compile t) s (op.apply s))
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost) :
    t.Admissible (improved t).eval :=
  t.admissible _ (improved_goalAware_of_schema t hcompiled)
    (improved_consistent_of_schema t hnd hstep hcost)

end Planner.ExampleHeuristics.Miconic

/- -------------------------------------------------------------------------- -/
/-
Miconic's heuristic, defined and proved at the lifted level.

Nothing here mentions a `Fact`, a `State`, or `compile`.  The heuristic is a
function of the atoms — who is served, who is aboard, where each passenger waits,
where the lift is — and of the objects the problem declares.  What connects it to
the planner is `admissibleOn_of_lifted`, which is proved once for every domain.

The value is the one the compiled heuristic computes: two actions for each
passenger still waiting, one for each aboard, and one move for each floor still
needed other than the one the lift is on.
-/

namespace Planner.Lifted.Miconic

open Planner Planner.Pddl

/-! ### The domain's atoms -/

def served (p : Name) : GroundAtom := { pred := "served", args := [p] }
def boarded (p : Name) : GroundAtom := { pred := "boarded", args := [p] }
def origin (p f : Name) : GroundAtom := { pred := "origin", args := [p, f] }
def liftAt (f : Name) : GroundAtom := { pred := "lift-at", args := [f] }
def destin (p f : Name) : GroundAtom := { pred := "destin", args := [p, f] }

/-- What the problem fixes: the passengers to serve, the floors, and where each
passenger is bound.  `destin` never changes, so it is read once. -/
structure Cfg where
  passengers : List Name
  floors : List Name
  dest : Name → Option Name

/-! ### The three counts -/

/-- Still to serve and not yet aboard. -/
def waiting (c : Cfg) (σ : AtomState) : List Name :=
  c.passengers.filter fun p => !σ (served p) && !σ (boarded p)

/-- Still to serve and aboard. -/
def riding (c : Cfg) (σ : AtomState) : List Name :=
  c.passengers.filter fun p => !σ (served p) && σ (boarded p)

/-- The floor the lift is standing on. -/
def currentFloor (c : Cfg) (σ : AtomState) : Option Name :=
  c.floors.find? fun f => σ (liftAt f)

/-- Where a passenger is still waiting, if they are. -/
def originFloor (c : Cfg) (σ : AtomState) (p : Name) : Option Name :=
  c.floors.find? fun f => σ (origin p f)

/-- The floors one passenger still forces the lift to visit. -/
def floorsNeeded (c : Cfg) (σ : AtomState) (p : Name) : List Name :=
  (if σ (boarded p) then [] else (originFloor c σ p).toList) ++ (c.dest p).toList

/-- The distinct floors still to visit, other than the one the lift is on. -/
def neededFloors (c : Cfg) (σ : AtomState) : List Name :=
  ((c.passengers.filter fun p => !σ (served p)).flatMap (floorsNeeded c σ)).dedup.filter
    fun f => currentFloor c σ != some f

/-- Two actions per waiting passenger, one per rider, one move per floor needed. -/
def value (c : Cfg) (σ : AtomState) : Nat :=
  2 * (waiting c σ).length + (riding c σ).length + (neededFloors c σ).length

/--
The boarding and departing still owed, as one sum over the passengers: two for a
passenger still waiting, one for a rider, none for one already served.  It is the
same number as `2·waiting + riding`, and it is the form the consistency argument
uses, because one action moves exactly one passenger's term.
-/
def load (c : Cfg) (σ : AtomState) : Nat :=
  (c.passengers.map fun p =>
    if σ (served p) then 0 else if σ (boarded p) then 1 else 2).sum

theorem load_eq (c : Cfg) (σ : AtomState) :
    2 * (waiting c σ).length + (riding c σ).length = load c σ := by
  unfold waiting riding load
  induction c.passengers with
  | nil => rfl
  | cons p rest ih =>
      by_cases hs : σ (served p)
      · simp [List.filter_cons, hs, ih]
      · by_cases hb : σ (boarded p)
        · simp only [List.filter_cons, hs, hb, List.map_cons, List.sum_cons,
            Bool.false_eq_true, if_false, if_true, Bool.not_false, Bool.not_true,
            Bool.and_true, Bool.and_false, List.length_cons]
          omega
        · simp only [List.filter_cons, hs, hb, List.map_cons, List.sum_cons,
            Bool.false_eq_true, if_false, if_true, Bool.not_false, Bool.not_true,
            Bool.and_true, Bool.and_false, List.length_cons]
          omega

theorem value_eq_load (c : Cfg) (σ : AtomState) :
    value c σ = load c σ + (neededFloors c σ).length := by
  unfold value
  rw [← load_eq]

/-! ### The floors still to visit, as a set -/

theorem neededFloors_nodup (c : Cfg) (σ : AtomState) : (neededFloors c σ).Nodup := by
  unfold neededFloors
  exact (List.nodup_dedup _).filter _

theorem mem_neededFloors {c : Cfg} {σ : AtomState} {x : Name} :
    x ∈ neededFloors c σ ↔
      (∃ p ∈ c.passengers, σ (served p) = false ∧ x ∈ floorsNeeded c σ p) ∧
      currentFloor c σ ≠ some x := by
  unfold neededFloors
  rw [List.mem_filter, List.mem_dedup, List.mem_flatMap]
  constructor
  · rintro ⟨⟨p, hp, hx⟩, hf⟩
    rw [List.mem_filter] at hp
    exact ⟨⟨p, hp.1, by simpa using hp.2, hx⟩, by simpa using hf⟩
  · rintro ⟨⟨p, hp, hs, hx⟩, hf⟩
    exact ⟨⟨p, by rw [List.mem_filter]; exact ⟨hp, by simp [hs]⟩, hx⟩, by simpa using hf⟩

theorem neededFloors_mono {c : Cfg} {σ τ : AtomState}
    (h : ∀ x ∈ neededFloors c σ, x ∈ neededFloors c τ) :
    (neededFloors c σ).length ≤ (neededFloors c τ).length :=
  length_le_of_subset' _ _ (neededFloors_nodup c σ) h

theorem neededFloors_le_succ {c : Cfg} {σ τ : AtomState} (a : Name)
    (h : ∀ x ∈ neededFloors c σ, x ∈ neededFloors c τ ∨ x = a) :
    (neededFloors c σ).length ≤ (neededFloors c τ).length + 1 :=
  length_le_succ_of_subset' _ _ a (neededFloors_nodup c σ) h

/-! ### Goal awareness -/

theorem value_eq_zero (c : Cfg) (σ : AtomState)
    (h : ∀ p ∈ c.passengers, σ (served p) = true) : value c σ = 0 := by
  have hunserved : (c.passengers.filter fun p => !σ (served p)) = [] := by
    refine List.filter_eq_nil_iff.mpr ?_
    intro p hp
    simp [h p hp]
  have hw : waiting c σ = [] := by
    refine List.filter_eq_nil_iff.mpr ?_
    intro p hp
    simp [h p hp]
  have hr : riding c σ = [] := by
    refine List.filter_eq_nil_iff.mpr ?_
    intro p hp
    simp [h p hp]
  have hn : neededFloors c σ = [] := by
    unfold neededFloors
    rw [hunserved]
    simp
  simp [value, hw, hr, hn]

/-- The heuristic is goal-aware for a problem whose goal is exactly these
passengers' `served` atoms. -/
theorem liftedGoalAware (c : Cfg) (p : Problem)
    (hsub : ∀ q ∈ c.passengers, served q ∈ p.goal) :
    LiftedGoalAware p (value c) := by
  intro σ hgoal
  refine value_eq_zero c σ fun q hq => ?_
  exact hgoal (served q) (by simpa using hsub q hq)

end Planner.Lifted.Miconic

/- -------------------------------------------------------------------------- -/
/-
Which domain a task came from.

A domain-dependent heuristic has to know its domain's schemas; that is true at
every level of representation.  `MiconicDomain` is that knowledge as one equation
on the parsed domain, decidable and checked once when the task is loaded.

`instance_cases` is what it buys: any well-typed instance of the domain is one of
the four actions, with its arguments named and its atoms computed.  From there a
heuristic proof is a four-way case split and no grounding is in sight.
-/

namespace Planner.Lifted.Miconic

open Planner Planner.Pddl

/-- The task's domain is miconic: its schema list, and the one predicate the
heuristic reads that no schema touches.  Both decidable, checked at load time. -/
structure MiconicPinned (d : Domain) : Prop where
  actions : d.actions = [boardA, departA, upA, downA]
  destinStatic : (staticPredicates d).contains "destin" = true

/-! ### Which predicates the schemas touch -/

theorem liftAt_dynamic {d : Domain} (hd : MiconicDomain d) :
    (staticPredicates d).contains "lift-at" = false :=
  not_static_of_mem_del (a := upA) (by rw [hd]; simp) (y := liftAtV "?f1") (by simp [upA])

theorem origin_dynamic {d : Domain} (hd : MiconicDomain d) :
    (staticPredicates d).contains "origin" = false :=
  not_static_of_mem_del (a := boardA) (by rw [hd]; simp) (y := originV "?p" "?f")
    (by simp [boardA])

theorem boarded_dynamic {d : Domain} (hd : MiconicDomain d) :
    (staticPredicates d).contains "boarded" = false :=
  not_static_of_mem_del (a := departA) (by rw [hd]; simp) (y := boardedV "?p")
    (by simp [departA])

theorem served_dynamic {d : Domain} (hd : MiconicDomain d) :
    (staticPredicates d).contains "served" = false :=
  not_static_of_mem_add (a := departA) (by rw [hd]; simp) (y := servedV "?p")
    (by simp [departA])

/-! ### What an instance of it looks like -/

/-- Every instance is one of the four actions, with its arguments named. -/
theorem instance_shape {d : Domain} {objects : List TypedName} (hd : MiconicDomain d)
    (i : Instance d objects) :
    (∃ f q, i.schema = boardA ∧ i.args = [f, q] ∧ WellTyped d objects "floor" f) ∨
    (∃ f q, i.schema = departA ∧ i.args = [f, q] ∧ WellTyped d objects "floor" f) ∨
    (∃ f1 f2, (i.schema = upA ∨ i.schema = downA) ∧ i.args = [f1, f2] ∧
      WellTyped d objects "floor" f1 ∧ WellTyped d objects "floor" f2) := by
  have hmem : i.schema ∈ [boardA, departA, upA, downA] := hd ▸ i.mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h
  · obtain ⟨f, q, hargs, h1, -⟩ := i.args_two (by rw [h])
    exact Or.inl ⟨f, q, h, hargs, by simpa [floorP] using h1⟩
  · obtain ⟨f, q, hargs, h1, -⟩ := i.args_two (by rw [h])
    exact Or.inr (Or.inl ⟨f, q, h, hargs, by simpa [floorP] using h1⟩)
  · obtain ⟨f1, f2, hargs, h1, h2⟩ := i.args_two (by rw [h])
    exact Or.inr (Or.inr ⟨f1, f2, Or.inl h, hargs, by simpa [f1P] using h1,
      by simpa [f2P] using h2⟩)
  · obtain ⟨f1, f2, hargs, h1, h2⟩ := i.args_two (by rw [h])
    exact Or.inr (Or.inr ⟨f1, f2, Or.inr h, hargs, by simpa [f1P] using h1,
      by simpa [f2P] using h2⟩)

theorem board_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {f q : Pddl.Name} (hs : i.schema = boardA) (ha : i.args = [f, q]) :
    liftAtV "?f" ∈ i.schema.pre ∧
    instAtom i.schema.params i.args (liftAtV "?f") = liftAt f ∧
    originV "?p" "?f" ∈ i.schema.pre ∧
    instAtom i.schema.params i.args (originV "?p" "?f") = origin q f ∧
    i.add = [boarded q] ∧ i.del = [origin q f] := by
  refine ⟨by rw [hs]; simp [boardA], by rw [hs, ha]; rfl,
    by rw [hs]; simp [boardA], by rw [hs, ha]; rfl, ?_, ?_⟩
  · rw [Pddl.Instance.add_eq, hs, ha]; rfl
  · rw [Pddl.Instance.del_eq, hs, ha]; rfl

theorem depart_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {f q : Pddl.Name} (hs : i.schema = departA) (ha : i.args = [f, q]) :
    boardedV "?p" ∈ i.schema.pre ∧
    instAtom i.schema.params i.args (boardedV "?p") = boarded q ∧
    destinV "?p" "?f" ∈ i.schema.pre ∧
    instAtom i.schema.params i.args (destinV "?p" "?f") = destin q f ∧
    liftAtV "?f" ∈ i.schema.pre ∧
    instAtom i.schema.params i.args (liftAtV "?f") = liftAt f ∧
    i.add = [served q] ∧ i.del = [boarded q] := by
  refine ⟨by rw [hs]; simp [departA], by rw [hs, ha]; rfl,
    by rw [hs]; simp [departA], by rw [hs, ha]; rfl,
    by rw [hs]; simp [departA], by rw [hs, ha]; rfl, ?_, ?_⟩
  · rw [Pddl.Instance.add_eq, hs, ha]; rfl
  · rw [Pddl.Instance.del_eq, hs, ha]; rfl

theorem move_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {f1 f2 : Pddl.Name} (hs : i.schema = upA ∨ i.schema = downA)
    (ha : i.args = [f1, f2]) :
    liftAtV "?f1" ∈ i.schema.pre ∧ liftAtV "?f1" ∈ i.schema.del ∧
    instAtom i.schema.params i.args (liftAtV "?f1") = liftAt f1 ∧
    i.add = [liftAt f2] ∧ i.del = [liftAt f1] := by
  rcases hs with h | h <;>
    exact ⟨by rw [h]; simp [upA, downA], by rw [h]; simp [upA, downA],
      by rw [h, ha]; rfl,
      by rw [Pddl.Instance.add_eq, h, ha]; rfl,
      by rw [Pddl.Instance.del_eq, h, ha]; rfl⟩

/-- Every instance is one of the four actions, with its atoms computed. -/
theorem instance_cases {d : Domain} {objects : List TypedName} (hd : MiconicDomain d)
    (i : Instance d objects) :
    (∃ f p, i.add = [boarded p] ∧ i.del = [origin p f]) ∨
    (∃ p, i.add = [served p] ∧ i.del = [boarded p]) ∨
    (∃ f1 f2, i.add = [liftAt f2] ∧ i.del = [liftAt f1]) := by
  have hmem : i.schema ∈ [boardA, departA, upA, downA] := hd ▸ i.mem
  have hadd := i.add_eq
  have hdel := i.del_eq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h
  · obtain ⟨f, p, hargs, -, -⟩ := i.args_two (by rw [h])
    exact Or.inl ⟨f, p, by rw [hadd, h, hargs]; rfl, by rw [hdel, h, hargs]; rfl⟩
  · obtain ⟨f, p, hargs, -, -⟩ := i.args_two (by rw [h])
    exact Or.inr (Or.inl ⟨p, by rw [hadd, h, hargs]; rfl,
      by rw [hdel, h, hargs]; rfl⟩)
  · obtain ⟨f1, f2, hargs, -, -⟩ := i.args_two (by rw [h])
    exact Or.inr (Or.inr ⟨f1, f2, by rw [hadd, h, hargs]; rfl,
      by rw [hdel, h, hargs]; rfl⟩)
  · obtain ⟨f1, f2, hargs, -, -⟩ := i.args_two (by rw [h])
    exact Or.inr (Or.inr ⟨f1, f2, by rw [hadd, h, hargs]; rfl,
      by rw [hdel, h, hargs]; rfl⟩)

end Planner.Lifted.Miconic

/- -------------------------------------------------------------------------- -/
/-
Miconic's improved heuristic: the state invariant it needs, and its preservation.

The floor count is only right when the lift is on one floor and each passenger
waits at one place.  Both are true of `:init` and survive every action, which is
what `Inv` and `inv_preserved` say.  Nothing here mentions a `Fact` or a `State`.
-/

namespace Planner.Lifted.Miconic

open Planner Planner.Pddl

/-- The lift is on one floor, and each passenger waits at one place. -/
structure Inv (σ : AtomState) : Prop where
  oneFloor : ∀ f g, σ (liftAt f) = true → σ (liftAt g) = true → f = g
  oneOrigin : ∀ p f g, σ (origin p f) = true → σ (origin p g) = true → f = g

/-! ### Atoms of different predicates are different -/

@[simp] theorem liftAt_ne_boarded (f p : Name) : liftAt f ≠ boarded p := by
  simp [liftAt, boarded]
@[simp] theorem liftAt_ne_origin (f p g : Name) : liftAt f ≠ origin p g := by
  simp [liftAt, origin]
@[simp] theorem liftAt_ne_served (f p : Name) : liftAt f ≠ served p := by
  simp [liftAt, served]
@[simp] theorem origin_ne_boarded (p f q : Name) : origin p f ≠ boarded q := by
  simp [origin, boarded]
@[simp] theorem origin_ne_served (p f q : Name) : origin p f ≠ served q := by
  simp [origin, served]
@[simp] theorem origin_ne_liftAt (p f g : Name) : origin p f ≠ liftAt g := by
  simp [origin, liftAt]
@[simp] theorem served_ne_boarded (p q : Name) : served p ≠ boarded q := by
  simp [served, boarded]
@[simp] theorem served_ne_origin (p q f : Name) : served p ≠ origin q f := by
  simp [served, origin]
@[simp] theorem served_ne_liftAt (p f : Name) : served p ≠ liftAt f := by
  simp [served, liftAt]
@[simp] theorem boarded_ne_origin (p q f : Name) : boarded p ≠ origin q f := by
  simp [boarded, origin]
@[simp] theorem boarded_ne_served (p q : Name) : boarded p ≠ served q := by
  simp [boarded, served]
@[simp] theorem boarded_ne_liftAt (p f : Name) : boarded p ≠ liftAt f := by
  simp [boarded, liftAt]

/-- An atom outside the operator's single-atom add and delete lists is untouched. -/
private theorem framed {o : AtomOp} {i : Instance d objects} {a x y : GroundAtom}
    (hadd : ∀ b ∈ o.add, b ∈ i.add) (hdel : ∀ b ∈ o.del, b ∈ i.del)
    (hia : i.add = [x]) (hid : i.del = [y]) (hax : a ≠ x) (hay : a ≠ y)
    (σ : AtomState) : o.applyA σ a = σ a := by
  refine applyA_frame σ (fun hmem => ?_) (fun hmem => ?_)
  · have := hadd a hmem
    rw [hia] at this
    exact hax (by simpa using this)
  · have := hdel a hmem
    rw [hid] at this
    exact hay (by simpa using this)

/-- An atom only the delete list can touch never becomes true. -/
private theorem only_falls {o : AtomOp} {i : Instance d objects} {a x : GroundAtom}
    (hadd : ∀ b ∈ o.add, b ∈ i.add) (hia : i.add = [x]) (hax : a ≠ x)
    {σ : AtomState} (h : o.applyA σ a = true) : σ a = true := by
  by_cases hd : a ∈ o.del
  · rw [applyA_del σ hd (fun hmem => hax (by
      have := hadd a hmem; rw [hia] at this; simpa using this))] at h
    exact absurd h (by simp)
  · rwa [applyA_frame σ (fun hmem => hax (by
      have := hadd a hmem; rw [hia] at this; simpa using this)) hd] at h

/-- After a move, `f2` is the only floor that can hold. -/
theorem move_only_f2 {d : Domain} {p : Problem} (hd : MiconicPinned d)
    {o : AtomOp} (hf : OpFacts d p o) {f1 f2 : Name}
    (hs : hf.inst.schema = upA ∨ hf.inst.schema = downA) (ha : hf.inst.args = [f1, f2])
    {σ : AtomState} (hinv : Inv σ) (happ : o.applicableA σ) :
    ∀ x, (o.applyA σ) (liftAt x) = true → x = f2 := by
  obtain ⟨hpreS, hdelS, hinst, hia, hid⟩ := move_atoms hf.inst hs ha
  have hf1 : σ (liftAt f1) = true := by
    have := hf.preComplete (liftAtV "?f1") hpreS (liftAt_dynamic hd.actions)
    rw [hinst] at this
    exact happ _ this
  intro x hx
  by_cases hxf2 : x = f2
  · exact hxf2
  · exfalso
    have hxadd : liftAt x ∉ o.add := by
      intro hmem
      have := hf.subAdd _ hmem
      rw [hia] at this
      exact hxf2 (by simpa [liftAt] using this)
    by_cases hxf1 : x = f1
    · subst hxf1
      have hdelmem : liftAt x ∈ o.del := by
        have hraw := hf.delComplete (liftAtV "?f1") hdelS ?_ ?_
        · rwa [hinst] at hraw
        · rw [hinst, hia]
          intro hmem
          exact hxf2 (by
            have hx2 : liftAt x = liftAt f2 := by simpa using hmem
            simpa [liftAt] using hx2)
        · rw [hinst]
          have := hf.preComplete (liftAtV "?f1") hpreS (liftAt_dynamic hd.actions)
          rwa [hinst] at this
      rw [applyA_del σ hdelmem hxadd] at hx
      exact absurd hx (by simp)
    · have hxdel : liftAt x ∉ o.del := by
        intro hmem
        have := hf.subDel _ hmem
        rw [hid] at this
        exact hxf1 (by simpa [liftAt] using this)
      rw [applyA_frame σ hxadd hxdel] at hx
      exact hxf1 (hinv.oneFloor x f1 hx hf1)

/-! ### The invariant survives every action -/

theorem inv_preserved {d : Domain} {p : Problem} (hd : MiconicPinned d)
    {o : AtomOp} (hf : OpFacts d p o) {σ : AtomState} (hinv : Inv σ)
    (happ : o.applicableA σ) : Inv (o.applyA σ) := by
  rcases instance_shape hd.actions hf.inst with
    ⟨f, q, hs, ha, -⟩ | ⟨f, q, hs, ha, -⟩ | ⟨f1, f2, hs, ha, -, -⟩
  · -- board: adds `boarded q`, deletes `origin q f`
    obtain ⟨-, -, -, -, hia, hid⟩ := board_atoms hf.inst hs ha
    refine ⟨fun g h hg hh => ?_, fun r g h hg hh => ?_⟩
    · rw [framed hf.subAdd hf.subDel hia hid (by simp) (by simp) σ] at hg hh
      exact hinv.oneFloor g h hg hh
    · exact hinv.oneOrigin r g h (only_falls hf.subAdd hia (by simp) hg)
        (only_falls hf.subAdd hia (by simp) hh)
  · -- depart: adds `served q`, deletes `boarded q`
    obtain ⟨-, -, -, -, -, -, hia, hid⟩ := depart_atoms hf.inst hs ha
    refine ⟨fun g h hg hh => ?_, fun r g h hg hh => ?_⟩
    · rw [framed hf.subAdd hf.subDel hia hid (by simp) (by simp) σ] at hg hh
      exact hinv.oneFloor g h hg hh
    · rw [framed hf.subAdd hf.subDel hia hid (by simp) (by simp) σ] at hg hh
      exact hinv.oneOrigin r g h hg hh
  · -- up or down: adds `liftAt f2`, deletes `liftAt f1`
    obtain ⟨hpreS, hdelS, hinst, hia, hid⟩ := move_atoms hf.inst hs ha
    have hf1 : σ (liftAt f1) = true := by
      have := hf.preComplete (liftAtV "?f1") hpreS (liftAt_dynamic hd.actions)
      rw [hinst] at this
      exact happ _ this
    refine ⟨fun g h hg hh => ?_, fun r g h hg hh => ?_⟩
    · -- the only floor that can hold afterwards is `f2`
      have key : ∀ x, (o.applyA σ) (liftAt x) = true → x = f2 := by
        intro x hx
        by_cases hxf2 : x = f2
        · exact hxf2
        · exfalso
          have hxadd : liftAt x ∉ o.add := by
            intro hmem
            have := hf.subAdd _ hmem
            rw [hia] at this
            exact hxf2 (by simpa [liftAt] using this)
          by_cases hxf1 : x = f1
          · subst hxf1
            have hdelmem : liftAt x ∈ o.del := by
              have hraw := hf.delComplete (liftAtV "?f1") hdelS ?_ ?_
              · rwa [hinst] at hraw
              · rw [hinst, hia]
                intro hmem
                exact hxf2 (by
                  have hx2 : liftAt x = liftAt f2 := by simpa using hmem
                  simpa [liftAt] using hx2)
              · rw [hinst]
                have := hf.preComplete (liftAtV "?f1") hpreS (liftAt_dynamic hd.actions)
                rwa [hinst] at this
            rw [applyA_del σ hdelmem hxadd] at hx
            exact absurd hx (by simp)
          · have hxdel : liftAt x ∉ o.del := by
              intro hmem
              have := hf.subDel _ hmem
              rw [hid] at this
              exact hxf1 (by simpa [liftAt] using this)
            rw [applyA_frame σ hxadd hxdel] at hx
            exact hxf1 (hinv.oneFloor x f1 hx hf1)
      rw [key g hg, key h hh]
    · rw [framed hf.subAdd hf.subDel hia hid (by simp) (by simp) σ] at hg hh
      exact hinv.oneOrigin r g h hg hh

/-! ### One action moves one passenger's term

`load` is a sum over the passengers, so an action that changes only one
passenger's `served` or `boarded` moves it by exactly that passenger's amount.
-/

/-- The passengers' terms, off one passenger, are untouched. -/
private theorem load_shift {c : Cfg} {σ τ : AtomState} {q : Name} (k : Nat)
    (hnd : c.passengers.Nodup) (hq : q ∈ c.passengers)
    (hstep : (if τ (served q) then 0 else if τ (boarded q) then 1 else 2) + k
      = (if σ (served q) then 0 else if σ (boarded q) then 1 else 2))
    (hrest : ∀ r ∈ c.passengers, r ≠ q →
      σ (served r) = τ (served r) ∧ σ (boarded r) = τ (boarded r)) :
    load c τ + k = load c σ := by
  unfold load
  refine sum_map_shift _ _ _ q k hq hnd hstep ?_
  intro r hr hne
  obtain ⟨h1, h2⟩ := hrest r hr hne
  simp [h1, h2]

/-- And when a passenger's own term can only fall by one, so can the sum. -/
private theorem load_le {c : Cfg} {σ τ : AtomState} {q : Name}
    (hnd : c.passengers.Nodup)
    (hstep : (if σ (served q) then 0 else if σ (boarded q) then 1 else 2)
      ≤ (if τ (served q) then 0 else if τ (boarded q) then 1 else 2) + 1)
    (hrest : ∀ r ∈ c.passengers, r ≠ q →
      σ (served r) = τ (served r) ∧ σ (boarded r) = τ (boarded r)) :
    load c σ ≤ load c τ + 1 := by
  unfold load
  refine sum_map_le_succ _ _ _ q hnd hstep ?_
  intro r hr hne
  obtain ⟨h1, h2⟩ := hrest r hr hne
  simp [h1, h2]

/-! ### What the configuration owes the problem

`Cfg` is read off the problem once.  These are the three facts a proof needs of
that reading, and they are what `Computes` will have to establish anyway.
-/

structure CfgOK (d : Domain) (p : Problem) (c : Cfg) : Prop where
  floors : ∀ g, WellTyped d (allObjects d p) "floor" g → g ∈ c.floors
  dest : ∀ q f, (Std.HashSet.ofList p.init).contains (destin q f) = true →
    c.dest q = some f
  nodup : c.passengers.Nodup

/-! ### Reading a position, when nothing that position depends on moved -/

theorem currentFloor_congr {c : Cfg} {σ τ : AtomState}
    (h : ∀ g, τ (liftAt g) = σ (liftAt g)) : currentFloor c τ = currentFloor c σ :=
  find?_congr _ _ _ fun x _ => h x

theorem originFloor_congr {c : Cfg} {σ τ : AtomState} (r : Name)
    (h : ∀ g, τ (origin r g) = σ (origin r g)) :
    originFloor c τ r = originFloor c σ r :=
  find?_congr _ _ _ fun x _ => h x

/-- With one lift-at holding, the lift is on that floor. -/
theorem currentFloor_eq {c : Cfg} {σ : AtomState} (hinv : Inv σ) {f : Name}
    (hf : f ∈ c.floors) (hs : σ (liftAt f) = true) : currentFloor c σ = some f := by
  unfold currentFloor
  rcases hfind : c.floors.find? (fun g => σ (liftAt g)) with _ | g
  · rw [List.find?_eq_none] at hfind
    exact absurd hs (by simpa using hfind f hf)
  · have hg := List.find?_some hfind
    rw [hinv.oneFloor g f (by simpa using hg) hs]

/-- And with one origin holding, that is where the passenger waits. -/
theorem originFloor_eq {c : Cfg} {σ : AtomState} (hinv : Inv σ) {r f : Name}
    (hf : f ∈ c.floors) (hs : σ (origin r f) = true) :
    originFloor c σ r = some f := by
  unfold originFloor
  rcases hfind : c.floors.find? (fun g => σ (origin r g)) with _ | g
  · rw [List.find?_eq_none] at hfind
    exact absurd hs (by simpa using hfind f hf)
  · have hg := List.find?_some hfind
    rw [hinv.oneOrigin r g f (by simpa using hg) hs]

/-! ### What each action does to the passengers' terms -/

/-- `board`: at most one passenger's term falls, and only from waiting to riding. -/
theorem board_load {d : Domain} {p : Problem} {c : Cfg} (hd : MiconicPinned d)
    {o : AtomOp} (hf : OpFacts d p o) {f q : Name}
    (hs : hf.inst.schema = boardA) (ha : hf.inst.args = [f, q])
    (hnd : c.passengers.Nodup) (σ : AtomState) :
    load c σ ≤ load c (o.applyA σ) + 1 := by
  obtain ⟨-, -, -, -, hia, hid⟩ := board_atoms hf.inst hs ha
  refine load_le (q := q) hnd ?_ ?_
  · -- `q`'s own term falls by at most one: `boarded` can only turn on
    have hserved : (o.applyA σ) (served q) = σ (served q) :=
      framed hf.subAdd hf.subDel hia hid (by simp) (by simp) σ
    rw [hserved]
    by_cases hsq : σ (served q)
    · simp [hsq]
    · by_cases hbq : σ (boarded q)
      · have : (o.applyA σ) (boarded q) = true := by
          by_cases hmem : boarded q ∈ o.add
          · exact applyA_add σ hmem
          · rw [applyA_frame σ hmem (fun hd' => by
              have := hf.subDel _ hd'; rw [hid] at this; simp at this)]
            exact hbq
        simp [hsq, hbq, this]
      · simp [hsq, hbq]
        split <;> omega
  · intro r hr hne
    have h1 : (o.applyA σ) (served r) = σ (served r) :=
      framed hf.subAdd hf.subDel hia hid (by simp) (by simp) σ
    have h2 : (o.applyA σ) (boarded r) = σ (boarded r) := by
      refine framed hf.subAdd hf.subDel hia hid ?_ (by simp) σ
      simp only [boarded, ne_eq, GroundAtom.mk.injEq, true_and, List.cons.injEq,
        and_true]
      exact fun hc => hne hc
    exact ⟨h1.symm, h2.symm⟩

/-- `depart`: at most one passenger's term falls, and only from riding to served. -/
theorem depart_load {d : Domain} {p : Problem} {c : Cfg} (hd : MiconicPinned d)
    {o : AtomOp} (hf : OpFacts d p o) {f q : Name}
    (hs : hf.inst.schema = departA) (ha : hf.inst.args = [f, q])
    (hnd : c.passengers.Nodup) (σ : AtomState) (happ : o.applicableA σ) :
    load c σ ≤ load c (o.applyA σ) + 1 := by
  obtain ⟨hbS, hbI, -, -, -, -, hia, hid⟩ := depart_atoms hf.inst hs ha
  have hbq : σ (boarded q) = true := by
    have := hf.preComplete (boardedV "?p") hbS (boarded_dynamic hd.actions)
    rw [hbI] at this
    exact happ _ this
  refine load_le (q := q) hnd ?_ ?_
  · by_cases hsq : σ (served q)
    · simp [hsq]
    · simp only [hsq, hbq, Bool.false_eq_true, if_false, if_true]
      split <;> omega
  · intro r hr hne
    have h1 : (o.applyA σ) (served r) = σ (served r) := by
      refine framed hf.subAdd hf.subDel hia hid ?_ (by simp) σ
      simp only [served, ne_eq, GroundAtom.mk.injEq, true_and, List.cons.injEq,
        and_true]
      exact fun hc => hne hc
    have h2 : (o.applyA σ) (boarded r) = σ (boarded r) := by
      refine framed hf.subAdd hf.subDel hia hid (by simp) ?_ σ
      simp only [boarded, ne_eq, GroundAtom.mk.injEq, true_and, List.cons.injEq,
        and_true]
      exact fun hc => hne hc
    exact ⟨h1.symm, h2.symm⟩

/-- A move touches no passenger, so the sum is unchanged. -/
theorem move_load {d : Domain} {p : Problem} {c : Cfg} (hd : MiconicPinned d)
    {o : AtomOp} (hf : OpFacts d p o) {f1 f2 : Name}
    (hs : hf.inst.schema = upA ∨ hf.inst.schema = downA) (ha : hf.inst.args = [f1, f2])
    (σ : AtomState) : load c (o.applyA σ) = load c σ := by
  obtain ⟨-, -, -, hia, hid⟩ := move_atoms hf.inst hs ha
  unfold load
  refine congrArg List.sum (List.map_congr_left ?_)
  intro r _
  have h1 : (o.applyA σ) (served r) = σ (served r) :=
    framed hf.subAdd hf.subDel hia hid (by simp) (by simp) σ
  have h2 : (o.applyA σ) (boarded r) = σ (boarded r) :=
    framed hf.subAdd hf.subDel hia hid (by simp) (by simp) σ
  simp [h1, h2]

/-! ### The floors still to visit

In every case the argument is the same: the lift is standing on the floor the
action happens at, and that floor is the only one the action can take out of the
list — so it was filtered out anyway.
-/

/-- `board` and `depart` do not shorten the list. -/
theorem discharge_floors {c : Cfg} {σ τ : AtomState} {f : Name}
    (hcur : currentFloor c σ = some f) (hcur' : currentFloor c τ = some f)
    (hserved : ∀ r, τ (served r) = σ (served r))
    (hkeep : ∀ r, σ (served r) = false → ∀ x ∈ floorsNeeded c σ r, x ≠ f →
      x ∈ floorsNeeded c τ r) :
    (neededFloors c σ).length ≤ (neededFloors c τ).length := by
  refine neededFloors_mono ?_
  intro x hx
  rw [mem_neededFloors] at hx ⊢
  obtain ⟨⟨r, hr, hs, hxf⟩, hne⟩ := hx
  have hxne : x ≠ f := by rintro rfl; exact hne hcur
  exact ⟨⟨r, hr, by rw [hserved r]; exact hs, hkeep r hs x hxf hxne⟩,
    by rw [hcur']; simpa using fun h => hxne h.symm⟩

/-- A move lengthens it by at most one. -/
theorem move_floors {c : Cfg} {σ τ : AtomState} {f2 : Name}
    (hcur' : ∀ x, currentFloor c τ = some x → x = f2)
    (hserved : ∀ r, τ (served r) = σ (served r))
    (hsame : ∀ r, floorsNeeded c τ r = floorsNeeded c σ r) :
    (neededFloors c σ).length ≤ (neededFloors c τ).length + 1 := by
  refine neededFloors_le_succ f2 ?_
  intro x hx
  rw [mem_neededFloors] at hx
  obtain ⟨⟨r, hr, hs, hxf⟩, -⟩ := hx
  by_cases hx2 : x = f2
  · exact Or.inr hx2
  · refine Or.inl ?_
    rw [mem_neededFloors]
    exact ⟨⟨r, hr, by rw [hserved r]; exact hs, by rw [hsame r]; exact hxf⟩,
      fun h => hx2 (hcur' x h)⟩

/-! ### One action, against the whole value -/

theorem board_value {d : Domain} {p : Problem} {c : Cfg} (hd : MiconicPinned d)
    (hc : CfgOK d p c) {o : AtomOp} (hf : OpFacts d p o) {f q : Name}
    (hs : hf.inst.schema = boardA) (ha : hf.inst.args = [f, q])
    (hft : WellTyped d (allObjects d p) "floor" f)
    {σ : AtomState} (hinv : Inv σ) (happ : o.applicableA σ) :
    value c σ ≤ 1 + value c (o.applyA σ) := by
  obtain ⟨hlS, hlI, hoS, hoI, hia, hid⟩ := board_atoms hf.inst hs ha
  have hfl : f ∈ c.floors := hc.floors f hft
  have hlift : σ (liftAt f) = true := by
    have := hf.preComplete (liftAtV "?f") hlS (liftAt_dynamic hd.actions)
    rw [hlI] at this; exact happ _ this
  have horig : σ (origin q f) = true := by
    have := hf.preComplete (originV "?p" "?f") hoS (origin_dynamic hd.actions)
    rw [hoI] at this; exact happ _ this
  have hliftSame : ∀ g, (o.applyA σ) (liftAt g) = σ (liftAt g) := fun g =>
    framed hf.subAdd hf.subDel hia hid (by simp) (by simp) σ
  have hservedSame : ∀ r, (o.applyA σ) (served r) = σ (served r) := fun r =>
    framed hf.subAdd hf.subDel hia hid (by simp) (by simp) σ
  have hcur : currentFloor c σ = some f := currentFloor_eq hinv hfl hlift
  have hcur' : currentFloor c (o.applyA σ) = some f := by
    rw [currentFloor_congr hliftSame]; exact hcur
  have hfloors := discharge_floors hcur hcur' hservedSame ?_
  · have hload := board_load hd hf hs ha hc.nodup σ
    rw [value_eq_load, value_eq_load]
    omega
  · intro r _ x hx hxf
    unfold floorsNeeded at hx ⊢
    rcases List.mem_append.mp hx with hx1 | hx2
    · by_cases hb : σ (boarded r)
      · rw [if_pos hb] at hx1; simp at hx1
      · rw [if_neg (by simpa using hb)] at hx1
        have hxo : originFloor c σ r = some x := by
          rcases hopt : originFloor c σ r with _ | g
          · rw [hopt] at hx1; simp at hx1
          · rw [hopt] at hx1
            simp only [Option.toList, List.mem_singleton] at hx1
            rw [hx1]
        by_cases hrq : r = q
        · subst hrq
          rw [originFloor_eq hinv hfl horig] at hxo
          exact absurd (Option.some.inj hxo) fun h => hxf h.symm
        · have hob : (o.applyA σ) (boarded r) = σ (boarded r) :=
            framed hf.subAdd hf.subDel hia hid
              (by simp only [boarded, ne_eq, GroundAtom.mk.injEq, true_and,
                List.cons.injEq, and_true]
                  exact fun hcon => hrq hcon) (by simp) σ
          have hoo : originFloor c (o.applyA σ) r = originFloor c σ r :=
            originFloor_congr r fun g =>
              framed hf.subAdd hf.subDel hia hid (by simp)
                (by simp only [origin, ne_eq, GroundAtom.mk.injEq, true_and,
                  List.cons.injEq, and_true]
                    exact fun hcon => hrq hcon.1) σ
          refine List.mem_append_left _ ?_
          rw [if_neg (by rw [hob]; simpa using hb), hoo, hxo]
          simp
    · exact List.mem_append_right _ hx2

theorem depart_value {d : Domain} {p : Problem} {c : Cfg} (hd : MiconicPinned d)
    (hc : CfgOK d p c) {o : AtomOp} (hf : OpFacts d p o) {f q : Name}
    (hs : hf.inst.schema = departA) (ha : hf.inst.args = [f, q])
    (hft : WellTyped d (allObjects d p) "floor" f)
    {σ : AtomState} (hinv : Inv σ) (happ : o.applicableA σ) :
    value c σ ≤ 1 + value c (o.applyA σ) := by
  obtain ⟨hbS, hbI, hdS, hdI, hlS, hlI, hia, hid⟩ := depart_atoms hf.inst hs ha
  have hfl : f ∈ c.floors := hc.floors f hft
  have hlift : σ (liftAt f) = true := by
    have := hf.preComplete (liftAtV "?f") hlS (liftAt_dynamic hd.actions)
    rw [hlI] at this; exact happ _ this
  have hbq : σ (boarded q) = true := by
    have := hf.preComplete (boardedV "?p") hbS (boarded_dynamic hd.actions)
    rw [hbI] at this; exact happ _ this
  have hdq : c.dest q = some f := by
    refine hc.dest q f ?_
    have := hf.staticHeld (destinV "?p" "?f") hdS hd.destinStatic
    rwa [hdI] at this
  have hliftSame : ∀ g, (o.applyA σ) (liftAt g) = σ (liftAt g) := fun g =>
    framed hf.subAdd hf.subDel hia hid (by simp) (by simp) σ
  have hcur : currentFloor c σ = some f := currentFloor_eq hinv hfl hlift
  have hcur' : currentFloor c (o.applyA σ) = some f := by
    rw [currentFloor_congr hliftSame]; exact hcur
  have hservedSame : ∀ r, r ≠ q → (o.applyA σ) (served r) = σ (served r) := fun r hr =>
    framed hf.subAdd hf.subDel hia hid
      (by simp only [served, ne_eq, GroundAtom.mk.injEq, true_and, List.cons.injEq,
        and_true]
          exact fun hcon => hr hcon) (by simp) σ
  have hserved : ∀ r, (o.applyA σ) (served r) = σ (served r) ∨ r = q := by
    intro r
    by_cases hr : r = q
    · exact Or.inr hr
    · exact Or.inl (hservedSame r hr)
  have hfloors : (neededFloors c σ).length ≤ (neededFloors c (o.applyA σ)).length := by
    refine neededFloors_mono ?_
    intro x hx
    rw [mem_neededFloors] at hx ⊢
    obtain ⟨⟨r, hr, hsr, hxf⟩, hne⟩ := hx
    have hxne : x ≠ f := by rintro rfl; exact hne hcur
    have hrq : r ≠ q := by
      rintro rfl
      unfold floorsNeeded at hxf
      rw [if_pos hbq, hdq] at hxf
      simp at hxf
      exact hxne hxf
    refine ⟨⟨r, hr, by rw [hservedSame r hrq]; exact hsr, ?_⟩, ?_⟩
    · have hob : (o.applyA σ) (boarded r) = σ (boarded r) :=
        framed hf.subAdd hf.subDel hia hid (by simp)
          (by simp only [boarded, ne_eq, GroundAtom.mk.injEq, true_and,
            List.cons.injEq, and_true]
              exact fun hcon => hrq hcon) σ
      have hoo : originFloor c (o.applyA σ) r = originFloor c σ r :=
        originFloor_congr r fun g =>
          framed hf.subAdd hf.subDel hia hid (by simp) (by simp) σ
      unfold floorsNeeded at hxf ⊢
      rwa [hob, hoo]
    · rw [hcur']; simpa using fun h => hxne h.symm
  have hload := depart_load hd hf hs ha hc.nodup σ happ
  rw [value_eq_load, value_eq_load]
  omega

theorem move_value {d : Domain} {p : Problem} {c : Cfg} (hd : MiconicPinned d)
    (hc : CfgOK d p c) {o : AtomOp} (hf : OpFacts d p o) {f1 f2 : Name}
    (hs : hf.inst.schema = upA ∨ hf.inst.schema = downA) (ha : hf.inst.args = [f1, f2])
    {σ : AtomState} (hinv : Inv σ) (happ : o.applicableA σ) :
    value c σ ≤ 1 + value c (o.applyA σ) := by
  obtain ⟨-, -, -, hia, hid⟩ := move_atoms hf.inst hs ha
  have hservedSame : ∀ r, (o.applyA σ) (served r) = σ (served r) := fun r =>
    framed hf.subAdd hf.subDel hia hid (by simp) (by simp) σ
  have hsame : ∀ r, floorsNeeded c (o.applyA σ) r = floorsNeeded c σ r := by
    intro r
    have hob : (o.applyA σ) (boarded r) = σ (boarded r) :=
      framed hf.subAdd hf.subDel hia hid (by simp) (by simp) σ
    have hoo : originFloor c (o.applyA σ) r = originFloor c σ r :=
      originFloor_congr r fun g =>
        framed hf.subAdd hf.subDel hia hid (by simp) (by simp) σ
    unfold floorsNeeded
    rw [hob, hoo]
  have hcur' : ∀ x, currentFloor c (o.applyA σ) = some x → x = f2 := by
    intro x hx
    refine move_only_f2 hd hf hs ha hinv happ x ?_
    have := List.find?_some hx
    simpa using this
  have hfloors := move_floors hcur' hservedSame hsame
  have hload := move_load hd hf hs ha (c := c) σ
  rw [value_eq_load, value_eq_load]
  omega

/-! ### Consistency, and admissibility of whatever computes this heuristic -/

theorem liftedConsistent {d : Domain} {p : Problem} {c : Cfg} (hd : MiconicPinned d)
    (hc : CfgOK d p c) (relevance : Bool)
    (hfacts : ∀ o ∈ groundedOps d p relevance, Nonempty (OpFacts d p o))
    (hcost : ∀ o ∈ groundedOps d p relevance, 0 < o.cost) :
    LiftedConsistentOn d p relevance Inv (value c) := by
  intro o ho σ hinv happ
  obtain ⟨hf⟩ := hfacts o ho
  have hc1 := hcost o ho
  rcases instance_shape hd.actions hf.inst with
    ⟨f, q, hs, ha, hft⟩ | ⟨f, q, hs, ha, hft⟩ | ⟨f1, f2, hs, ha, -, -⟩
  · have := board_value hd hc hf hs ha hft hinv happ; omega
  · have := depart_value hd hc hf hs ha hft hinv happ; omega
  · have := move_value hd hc hf hs ha hinv happ; omega

theorem invPreserved {d : Domain} {p : Problem} (hd : MiconicPinned d)
    (relevance : Bool)
    (hfacts : ∀ o ∈ groundedOps d p relevance, Nonempty (OpFacts d p o)) :
    ∀ o ∈ groundedOps d p relevance, ∀ σ, Inv σ → o.applicableA σ → Inv (o.applyA σ) :=
  fun o ho σ hinv happ => inv_preserved hd (hfacts o ho).some hinv happ

/--
**Miconic's improved heuristic is goal-aware.**
-/
theorem improved_goalAwareOn (d : Domain) (p : Problem) (relevance : Bool)
    (c : Cfg) (hd : MiconicPinned d) (hc : CfgOK d p c)
    (hwf : Task.WF (ground d p relevance))
    (hcost : ∀ o ∈ groundedOps d p relevance, 0 < o.cost)
    (hfacts : ∀ o ∈ groundedOps d p relevance, Nonempty (OpFacts d p o))
    (hsub : ∀ q ∈ c.passengers, served q ∈ p.goal)
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hv : State → Nat) (hcomp : ComputesOn (ground d p relevance) Inv hv (value c)) :
    (ground d p relevance).GoalAwareOn (Reachable (ground d p relevance)) hv :=
  goalAwareOn_of_lifted d p relevance hwf hcost hv (value c) Inv hcomp hinit
    (invPreserved hd relevance hfacts) (liftedGoalAware c p hsub)

/-- **Miconic's improved heuristic is consistent.** -/
theorem improved_consistentOn (d : Domain) (p : Problem) (relevance : Bool)
    (c : Cfg) (hd : MiconicPinned d) (hc : CfgOK d p c)
    (hwf : Task.WF (ground d p relevance))
    (hcost : ∀ o ∈ groundedOps d p relevance, 0 < o.cost)
    (hfacts : ∀ o ∈ groundedOps d p relevance, Nonempty (OpFacts d p o))
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hv : State → Nat) (hcomp : ComputesOn (ground d p relevance) Inv hv (value c)) :
    (ground d p relevance).ConsistentOn (Reachable (ground d p relevance)) hv :=
  consistentOn_of_lifted d p relevance hwf hcost hv (value c) Inv hcomp hinit
    (invPreserved hd relevance hfacts) (liftedConsistent hd hc relevance hfacts hcost)

/--
**Miconic's improved heuristic is admissible.**  Anything that computes the lifted
value is admissible on every state the search can reach — which, with
`Computes`, is the compiled heuristic the planner runs.
-/
theorem improved_admissibleOn (d : Domain) (p : Problem) (relevance : Bool)
    (c : Cfg) (hd : MiconicPinned d) (hc : CfgOK d p c)
    (hwf : Task.WF (ground d p relevance))
    (hcost : ∀ o ∈ groundedOps d p relevance, 0 < o.cost)
    (hfacts : ∀ o ∈ groundedOps d p relevance, Nonempty (OpFacts d p o))
    (hsub : ∀ q ∈ c.passengers, served q ∈ p.goal)
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hv : State → Nat) (hcomp : ComputesOn (ground d p relevance) Inv hv (value c)) :
    (ground d p relevance).AdmissibleOn (Reachable (ground d p relevance)) hv :=
  admissibleOn_of_lifted d p relevance hwf hcost hv (value c) Inv hcomp hinit
    (invPreserved hd relevance hfacts) (liftedGoalAware c p hsub)
    (liftedConsistent hd hc relevance hfacts hcost)

end Planner.Lifted.Miconic

/- -------------------------------------------------------------------------- -/
/-
What the compiled miconic heuristic must match.

`Computes` is the last obligation: the number `improved t` returns on a packed
state is the number the lifted heuristic returns on the atoms that state stands
for.  `DataMatches` says what the compiled tables have to be for that, entry by
entry, and it is stated without adding anything to the running code — the atom a
stored fact names is recoverable from the task.

Establishing `DataMatches` from `compile` itself is reasoning about the loop that
builds the record, which is the one part of this domain's proof that is about the
heuristic's own data structure rather than about planning.
-/

namespace Planner.Lifted.Miconic

open Planner Planner.Pddl

/-- The compiled heuristic's per-task record. -/
abbrev CData := ExampleHeuristics.Miconic.Data

/-- The floor a compiled index stands for. -/
def nameOf (c : Cfg) (i : Nat) : Pddl.Name := c.floors.getD i ""

theorem nameOf_mem {c : Cfg} {i : Nat} (h : i < c.floors.length) :
    nameOf c i ∈ c.floors := by
  unfold nameOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

theorem nameOf_inj {c : Cfg} (hnd : c.floors.Nodup) {i j : Nat}
    (hi : i < c.floors.length) (hj : j < c.floors.length)
    (h : nameOf c i = nameOf c j) : i = j := by
  unfold nameOf at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] at h
  exact (List.getElem_inj hnd).mp (by simpa using h)

/-- What one compiled entry must say about one passenger. -/
structure EntryMatches (t : Task) (c : Cfg)
    (pi : ExampleHeuristics.Miconic.PassengerInfo) (q : Pddl.Name) : Prop where
  goalName : t.factNames.getD pi.goalFact default = served q
  goalRange : pi.goalFact < t.factNames.size
  boardedSome : ∀ f, pi.boardedFact = some f →
    t.factNames.getD f default = boarded q ∧ f < t.factNames.size
  boardedNone : pi.boardedFact = none → ∀ σ : AtomState, σ (boarded q) = false
  /-- Each `origin` entry names that floor's atom, and its index is a real floor. -/
  originNames : ∀ x ∈ pi.originFacts,
    t.factNames.getD x.1 default = origin q (nameOf c x.2) ∧ x.1 < t.factNames.size ∧
    x.2 < c.floors.length
  /-- And every floor has an entry. -/
  originOnto : ∀ g ∈ c.floors, ∃ x ∈ pi.originFacts, nameOf c x.2 = g
  /-- The destination agrees. -/
  destSome : ∀ i, pi.destFloor = some i →
    c.dest q = some (nameOf c i) ∧ i < c.floors.length
  destNone : pi.destFloor = none → c.dest q = none

/-- The compiled tables read the same passengers as the `Cfg`, entry for entry. -/
def DataMatches (t : Task) (c : Cfg) (dd : CData) : Prop :=
  List.Forall₂ (EntryMatches t c) dd.passengers.toList c.passengers

/-- What the compiled floor tables must say. -/
structure FloorMatch (t : Task) (c : Cfg) (dd : CData) : Prop where
  nodup : c.floors.Nodup
  /-- Each `lift-at` entry names that floor's atom, and its index is a real floor. -/
  liftNames : ∀ x ∈ dd.liftAt,
    t.factNames.getD x.1 default = liftAt (nameOf c x.2) ∧ x.1 < t.factNames.size ∧
    x.2 < c.floors.length
  /-- And every floor has an entry. -/
  liftOnto : ∀ g ∈ c.floors, ∃ x ∈ dd.liftAt, nameOf c x.2 = g

/-- Where the lift is, read compiled or lifted, is the same floor. -/
theorem currentFloor_matches {t : Task} {c : Cfg} {dd : CData} (hm : FloorMatch t c dd)
    {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) (hinv : Inv σ) :
    (ExampleHeuristics.Miconic.currentFloor dd s).map (nameOf c) = currentFloor c σ := by
  unfold ExampleHeuristics.Miconic.currentFloor
  rcases hfind : dd.liftAt.find? (fun x => s.test x.1) with _ | x
  · -- nothing holds, and every floor has an entry, so nothing holds there either
    rw [hfind]
    simp only [Option.map_none]
    symm
    unfold currentFloor
    rw [List.find?_eq_none]
    intro g hg
    obtain ⟨y, hy, hyg⟩ := hm.liftOnto g hg
    obtain ⟨hname, hrange, -⟩ := hm.liftNames y hy
    have hfalse : s.test y.1 = false := by
      have := Array.find?_eq_none.mp hfind y hy
      simpa using this
    have : σ (liftAt (nameOf c y.2)) = false := by
      rw [← hname, habs.numbered y.1 (by rw [hn]; exact hrange)]
      exact hfalse
    rw [hyg] at this
    simp [this]
  · rw [hfind]
    have hmem : x ∈ dd.liftAt := Array.mem_of_find?_eq_some hfind
    obtain ⟨hname, hrange, hidx⟩ := hm.liftNames x hmem
    have htrue : σ (liftAt (nameOf c x.2)) = true := by
      rw [← hname, habs.numbered x.1 (by rw [hn]; exact hrange)]
      simpa using Array.find?_some hfind
    simp only [Option.map_some]
    exact (currentFloor_eq hinv (nameOf_mem hidx) htrue).symm

/-! ### The compiled per-passenger sum -/

theorem waiting_toList (dd : CData) (s : State) :
    (ExampleHeuristics.Miconic.waiting dd s).size
      = (dd.passengers.toList.filter fun p =>
          !ExampleHeuristics.Miconic.aboard p s && !s.test p.goalFact).length := by
  show ((ExampleHeuristics.Miconic.unserved dd s).filter _).size = _
  unfold ExampleHeuristics.Miconic.unserved
  rw [← Array.length_toList, Array.toList_filter, Array.toList_filter,
    List.filter_filter]

theorem riding_toList (dd : CData) (s : State) :
    (ExampleHeuristics.Miconic.riding dd s).size
      = (dd.passengers.toList.filter fun p =>
          ExampleHeuristics.Miconic.aboard p s && !s.test p.goalFact).length := by
  show ((ExampleHeuristics.Miconic.unserved dd s).filter _).size = _
  unfold ExampleHeuristics.Miconic.unserved
  rw [← Array.length_toList, Array.toList_filter, Array.toList_filter,
    List.filter_filter]

/-- The compiled `2·waiting + riding`, as one sum, exactly as `load` is. -/
theorem compiled_load (dd : CData) (s : State) :
    2 * (ExampleHeuristics.Miconic.waiting dd s).size
      + (ExampleHeuristics.Miconic.riding dd s).size
      = (dd.passengers.toList.map fun pi =>
          if s.test pi.goalFact then 0
          else if ExampleHeuristics.Miconic.aboard pi s then 1 else 2).sum := by
  rw [waiting_toList, riding_toList]
  induction dd.passengers.toList with
  | nil => rfl
  | cons pi rest ih =>
      by_cases hg : s.test pi.goalFact
      · simp [List.filter_cons, hg, ih]
      · by_cases hb : ExampleHeuristics.Miconic.aboard pi s
        · simp only [List.filter_cons, hg, hb, List.map_cons, List.sum_cons,
            Bool.false_eq_true, if_false, if_true, Bool.not_false, Bool.not_true,
            Bool.and_true, Bool.and_false, List.length_cons]
          omega
        · simp only [List.filter_cons, hg, hb, List.map_cons, List.sum_cons,
            Bool.false_eq_true, if_false, if_true, Bool.not_false, Bool.not_true,
            Bool.and_true, Bool.and_false, List.length_cons]
          omega

/-- Entry for entry, the compiled sum is the lifted one. -/
theorem load_lists {t : Task} {c : Cfg} {l : List ExampleHeuristics.Miconic.PassengerInfo}
    {ps : List Pddl.Name} (hm : List.Forall₂ (EntryMatches t c) l ps)
    {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) :
    (l.map fun pi => if s.test pi.goalFact then 0
      else if ExampleHeuristics.Miconic.aboard pi s then 1 else 2).sum
      = (ps.map fun q => if σ (served q) then 0
          else if σ (boarded q) then 1 else 2).sum := by
  induction hm with
  | nil => rfl
  | @cons pi q rest1 rest2 hentry _ ih =>
      obtain ⟨hgoal, hgrange, hboard, hnone, -, -, -, -⟩ := hentry
      have hg : s.test pi.goalFact = σ (served q) := by
        rw [← hgoal]
        exact (habs.numbered _ (by rw [hn]; exact hgrange)).symm
      have hb : ExampleHeuristics.Miconic.aboard pi s = σ (boarded q) := by
        unfold ExampleHeuristics.Miconic.aboard
        rcases hbf : pi.boardedFact with _ | f
        · rw [hnone hbf σ]
        · obtain ⟨hname, hrange⟩ := hboard f hbf
          rw [← hname]
          exact (habs.numbered f (by rw [hn]; exact hrange)).symm
      simp only [List.map_cons, List.sum_cons, hg, hb, ih]

theorem load_matches {t : Task} {c : Cfg} {dd : CData} (hm : DataMatches t c dd)
    {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) :
    2 * (ExampleHeuristics.Miconic.waiting dd s).size
      + (ExampleHeuristics.Miconic.riding dd s).size = load c σ := by
  rw [compiled_load]
  exact load_lists hm habs hn

/-! ### The floors still to visit -/

/-- Where a passenger waits, read compiled or lifted, is the same floor. -/
theorem originFloor_matches {t : Task} {c : Cfg}
    {pi : ExampleHeuristics.Miconic.PassengerInfo} {q : Pddl.Name}
    (he : EntryMatches t c pi q) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) (hinv : Inv σ) :
    ((pi.originFacts.find? fun x => s.test x.1).map (·.2)).map (nameOf c)
      = originFloor c σ q := by
  rcases hfind : pi.originFacts.find? (fun x => s.test x.1) with _ | x
  · rw [hfind]
    simp only [Option.map_none]
    symm
    unfold originFloor
    rw [List.find?_eq_none]
    intro g hg
    obtain ⟨y, hy, hyg⟩ := he.originOnto g hg
    obtain ⟨hname, hrange, -⟩ := he.originNames y hy
    have hfalse : s.test y.1 = false := by
      have := Array.find?_eq_none.mp hfind y hy
      simpa using this
    have hσ : σ (origin q (nameOf c y.2)) = false := by
      rw [← hname, habs.numbered y.1 (by rw [hn]; exact hrange)]
      exact hfalse
    rw [hyg] at hσ
    simp [hσ]
  · rw [hfind]
    have hmem : x ∈ pi.originFacts := Array.mem_of_find?_eq_some hfind
    obtain ⟨hname, hrange, hidx⟩ := he.originNames x hmem
    have htrue : σ (origin q (nameOf c x.2)) = true := by
      rw [← hname, habs.numbered x.1 (by rw [hn]; exact hrange)]
      simpa using Array.find?_some hfind
    simp only [Option.map_some]
    exact (originFloor_eq hinv (nameOf_mem hidx) htrue).symm

/-- And so the floors one passenger forces the lift to visit are the same. -/
theorem floorsNeeded_matches {t : Task} {c : Cfg} {dd : CData}
    {pi : ExampleHeuristics.Miconic.PassengerInfo} {q : Pddl.Name}
    (he : EntryMatches t c pi q) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) (hinv : Inv σ) :
    (ExampleHeuristics.Miconic.floorsNeeded dd s pi).map (nameOf c)
      = floorsNeeded c σ q := by
  have hb : ExampleHeuristics.Miconic.aboard pi s = σ (boarded q) := by
    unfold ExampleHeuristics.Miconic.aboard
    rcases hbf : pi.boardedFact with _ | f
    · rw [he.boardedNone hbf σ]
    · obtain ⟨hname, hrange⟩ := he.boardedSome f hbf
      rw [← hname]
      exact (habs.numbered f (by rw [hn]; exact hrange)).symm
  have horig := originFloor_matches he habs hn hinv
  have hdest : (pi.destFloor.map (nameOf c)) = c.dest q := by
    rcases hd : pi.destFloor with _ | i
    · rw [he.destNone hd]; rfl
    · obtain ⟨hc, -⟩ := he.destSome i hd
      rw [hc]; rfl
  unfold ExampleHeuristics.Miconic.floorsNeeded floorsNeeded
  rw [List.map_append]
  congr 1
  · rw [hb]
    by_cases hbq : σ (boarded q)
    · simp [hbq]
    · simp only [hbq, Bool.false_eq_true, if_false]
      rw [← horig]
      rcases hf : pi.originFacts.find? (fun x => s.test x.1) with _ | x <;> simp [hf]
  · rw [← hdest]
    rcases hd : pi.destFloor with _ | i <;> simp [hd]

/-! ### Two set counts, related by an injective naming -/

/-- Testing an entry's goal fact is asking whether that passenger is served. -/
theorem served_matches {t : Task} {c : Cfg}
    {pi : ExampleHeuristics.Miconic.PassengerInfo} {q : Pddl.Name}
    (he : EntryMatches t c pi q) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    s.test pi.goalFact = σ (served q) := by
  rw [← he.goalName]
  exact (habs.numbered _ (by rw [hn]; exact he.goalRange)).symm

/-- The unserved entries pair off with the unserved passengers. -/
theorem unserved_pairs {t : Task} {c : Cfg}
    {l : List ExampleHeuristics.Miconic.PassengerInfo} {ps : List Pddl.Name}
    (hm : List.Forall₂ (EntryMatches t c) l ps) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    List.Forall₂ (EntryMatches t c) (l.filter fun pi => !s.test pi.goalFact)
      (ps.filter fun q => !σ (served q)) := by
  induction hm with
  | nil => exact List.Forall₂.nil
  | @cons pi q rest1 rest2 he _ ih =>
      have hs := served_matches he habs hn
      by_cases hq : σ (served q)
      · rw [List.filter_cons, List.filter_cons]
        simp only [hs, hq, Bool.not_true, Bool.false_eq_true, if_false]
        exact ih
      · rw [List.filter_cons, List.filter_cons]
        simp only [hs, hq, Bool.not_false, if_true]
        exact List.Forall₂.cons he ih

/-! ### The floor count matches -/

/-- Membership in the compiled list of floors still to visit. -/
theorem mem_compiled_needed {dd : CData} {s : State} {i : Nat} :
    i ∈ ExampleHeuristics.Miconic.neededFloors dd s ↔
      (∃ pi ∈ ExampleHeuristics.Miconic.unserved dd s,
        i ∈ ExampleHeuristics.Miconic.floorsNeeded dd s pi) ∧
      ExampleHeuristics.Miconic.currentFloor dd s ≠ some i := by
  unfold ExampleHeuristics.Miconic.neededFloors
  rw [mem_distinct, List.mem_filter, List.mem_flatMap]
  constructor
  · rintro ⟨⟨pi, hpi, hx⟩, hf⟩
    exact ⟨⟨pi, by simpa using hpi, hx⟩, by simpa using hf⟩
  · rintro ⟨⟨pi, hpi, hx⟩, hf⟩
    exact ⟨⟨pi, by simpa using hpi, hx⟩, by simpa using hf⟩

theorem compiled_needed_nodup (dd : CData) (s : State) :
    (ExampleHeuristics.Miconic.neededFloors dd s).Nodup :=
  distinct_nodup _

/-- The whole raw list of floors, compiled, names the lifted one. -/
theorem rawFloors_matches {t : Task} {c : Cfg} {dd : CData}
    {l : List ExampleHeuristics.Miconic.PassengerInfo} {ps : List Pddl.Name}
    (hm : List.Forall₂ (EntryMatches t c) l ps) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) (hinv : Inv σ) :
    (l.flatMap (ExampleHeuristics.Miconic.floorsNeeded dd s)).map (nameOf c)
      = ps.flatMap (floorsNeeded c σ) := by
  induction hm with
  | nil => rfl
  | @cons pi q rest1 rest2 he _ ih =>
      rw [List.flatMap_cons, List.flatMap_cons, List.map_append,
        floorsNeeded_matches (dd := dd) he habs hn hinv, ih]

/-- Every index the compiled list mentions is a real floor. -/
theorem rawFloors_range {t : Task} {c : Cfg} {dd : CData}
    {l : List ExampleHeuristics.Miconic.PassengerInfo} {ps : List Pddl.Name}
    (hm : List.Forall₂ (EntryMatches t c) l ps) {s : State} :
    ∀ i ∈ l.flatMap (ExampleHeuristics.Miconic.floorsNeeded dd s), i < c.floors.length := by
  induction hm with
  | nil => intro i hi; simp at hi
  | @cons pi q rest1 rest2 he _ ih =>
      intro i hi
      rw [List.flatMap_cons, List.mem_append] at hi
      rcases hi with hi | hi
      · unfold ExampleHeuristics.Miconic.floorsNeeded at hi
        rcases List.mem_append.mp hi with h1 | h2
        · rcases hb : ExampleHeuristics.Miconic.aboard pi s with _ | _
          · rw [if_neg (by simp [hb])] at h1
            rcases hfind : pi.originFacts.find? (fun x => s.test x.1) with _ | x
            · rw [hfind] at h1; simp at h1
            · rw [hfind] at h1
              simp only [List.mem_singleton] at h1
              obtain ⟨-, -, hidx⟩ := he.originNames x (Array.mem_of_find?_eq_some hfind)
              rw [← h1] at hidx; exact hidx
          · rw [if_pos (by simp [hb])] at h1; simp at h1
        · rcases hd : pi.destFloor with _ | j
          · rw [hd] at h2; simp at h2
          · rw [hd] at h2
            simp only [List.mem_singleton] at h2
            obtain ⟨-, hidx⟩ := he.destSome j hd
            rw [← h2] at hidx; exact hidx
      · exact ih i hi

theorem currentFloor_range {t : Task} {c : Cfg} {dd : CData} (hfm : FloorMatch t c dd)
    {s : State} {k : Nat} (h : ExampleHeuristics.Miconic.currentFloor dd s = some k) :
    k < c.floors.length := by
  unfold ExampleHeuristics.Miconic.currentFloor at h
  rcases hfind : dd.liftAt.find? (fun x => s.test x.1) with _ | x
  · rw [hfind] at h; simp at h
  · rw [hfind] at h
    simp only [Option.map_some, Option.some.injEq] at h
    obtain ⟨-, -, hidx⟩ := hfm.liftNames x (Array.mem_of_find?_eq_some hfind)
    rw [← h]; exact hidx

/-- **The floor counts agree.** -/
theorem neededFloors_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) (hfm : FloorMatch t c dd)
    {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) (hinv : Inv σ) :
    (ExampleHeuristics.Miconic.neededFloors dd s).length
      = (neededFloors c σ).length := by
  have hpairs := unserved_pairs hm habs hn (s := s)
  have hraw := rawFloors_matches (dd := dd) hpairs habs hn hinv
  have hrange := rawFloors_range (dd := dd) (s := s) hpairs
  have hcur := currentFloor_matches hfm habs hn hinv
  have hun : ∀ pi, pi ∈ ExampleHeuristics.Miconic.unserved dd s ↔
      pi ∈ dd.passengers.toList.filter fun p => !s.test p.goalFact := by
    intro pi
    unfold ExampleHeuristics.Miconic.unserved
    rw [← Array.toList_filter]
    simp
  -- the raw membership on each side
  have hmemC : ∀ i, (∃ pi ∈ ExampleHeuristics.Miconic.unserved dd s,
        i ∈ ExampleHeuristics.Miconic.floorsNeeded dd s pi) ↔
      i ∈ (dd.passengers.toList.filter fun p => !s.test p.goalFact).flatMap
        (ExampleHeuristics.Miconic.floorsNeeded dd s) := by
    intro i
    rw [List.mem_flatMap]
    exact ⟨fun ⟨pi, h1, h2⟩ => ⟨pi, (hun pi).mp h1, h2⟩,
      fun ⟨pi, h1, h2⟩ => ⟨pi, (hun pi).mpr h1, h2⟩⟩
  have hcurIff : ∀ i, i < c.floors.length →
      (ExampleHeuristics.Miconic.currentFloor dd s = some i ↔
        currentFloor c σ = some (nameOf c i)) := by
    intro i hi
    constructor
    · intro h; rw [← hcur, h]; rfl
    · intro h
      rw [← hcur] at h
      rcases hc : ExampleHeuristics.Miconic.currentFloor dd s with _ | k
      · rw [hc] at h; simp at h
      · rw [hc] at h
        simp only [Option.map_some, Option.some.injEq] at h
        exact congrArg some (nameOf_inj hfm.nodup (currentFloor_range hfm hc) hi h)
  refine length_eq_of_naming _ _ (nameOf c) (compiled_needed_nodup dd s)
    (neededFloors_nodup c σ) ?_ ?_ ?_
  · intro i hi j hj hij
    rw [mem_compiled_needed] at hi hj
    exact nameOf_inj hfm.nodup (hrange i ((hmemC i).mp hi.1))
      (hrange j ((hmemC j).mp hj.1)) hij
  · intro i hi
    rw [mem_compiled_needed] at hi
    obtain ⟨hraw1, hne⟩ := hi
    have hmemraw := (hmemC i).mp hraw1
    have hir := hrange i hmemraw
    have hlift : nameOf c i ∈ (c.passengers.filter fun q => !σ (served q)).flatMap
        (floorsNeeded c σ) := by
      rw [← hraw]; exact List.mem_map.mpr ⟨i, hmemraw, rfl⟩
    obtain ⟨q, hq, hxq⟩ := List.mem_flatMap.mp hlift
    rw [List.mem_filter] at hq
    rw [mem_neededFloors]
    exact ⟨⟨q, hq.1, by simpa using hq.2, hxq⟩,
      fun hcon => hne ((hcurIff i hir).mpr hcon)⟩
  · intro g hg
    rw [mem_neededFloors] at hg
    obtain ⟨⟨q, hq, hs, hxq⟩, hne⟩ := hg
    have hlift : g ∈ (c.passengers.filter fun r => !σ (served r)).flatMap
        (floorsNeeded c σ) :=
      List.mem_flatMap.mpr ⟨q, by rw [List.mem_filter]; exact ⟨hq, by simp [hs]⟩, hxq⟩
    rw [← hraw] at hlift
    obtain ⟨i, hi, hig⟩ := List.mem_map.mp hlift
    have hir := hrange i hi
    refine ⟨i, ?_, hig⟩
    rw [mem_compiled_needed]
    refine ⟨(hmemC i).mpr hi, fun hcon => hne ?_⟩
    rw [← hig]
    exact (hcurIff i hir).mp hcon

/-! ### `Computes`, for miconic -/

/--
**The compiled miconic heuristic computes the lifted one.**  Both halves: the
passengers still to board and alight, and the floors still to visit.
-/
theorem computes {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) (hfm : FloorMatch t c dd)
    (hn : t.numFacts = t.factNames.size) :
    ComputesOn t Inv (ExampleHeuristics.Miconic.value dd) (value c) := by
  intro s σ habs hinv
  show 2 * (ExampleHeuristics.Miconic.waiting dd s).size
    + (ExampleHeuristics.Miconic.riding dd s).size
    + (ExampleHeuristics.Miconic.neededFloors dd s).length = _
  rw [value_eq_load, load_matches hm habs hn, neededFloors_matches hm hfm habs hn hinv]

end Planner.Lifted.Miconic

/- -------------------------------------------------------------------------- -/
/-
What `compile` produces for a miconic task.

The same bridge as ferry's, with one difference: miconic reads a *static*
predicate.  `destin` is checked against `:init` at grounding time and dropped, so
it is never numbered, and the heuristic reads it out of `staticAtoms` instead.
`mem_goal_of_static` is what says the reading is complete — a numbered static atom
could only have come from the goal, and a miconic goal is all `served`.
-/

namespace Planner.Lifted.Miconic

open Planner Planner.Pddl

/-! ### What one decidable pass over the problem establishes -/

/-- The passengers the goal asks to serve. -/
def goalPass (p : Problem) : List Name :=
  p.goal.filterMap fun a =>
    match a.pred == "served", a.args with
    | true, [q] => some q
    | _, _ => none

/-- The `lift-at` places of `:init`. -/
def liftPlaces (p : Problem) : List Name :=
  p.init.filterMap fun a =>
    match a.pred == "lift-at", a.args with
    | true, [f] => some f
    | _, _ => none

/-- The `origin` atoms of `:init`, as (passenger, floor) pairs. -/
def originPairs (p : Problem) : List (Name × Name) :=
  p.init.filterMap fun a =>
    match a.pred == "origin", a.args with
    | true, [q, f] => some (q, f)
    | _, _ => none

/-- The lift stands on one floor and each passenger waits at one. -/
def initInvCheck (p : Problem) : Bool :=
  (liftPlaces p).all (fun f => (liftPlaces p).all fun g => f == g) &&
  (originPairs p).all fun x => (originPairs p).all fun y => !(x.1 == y.1) || x.2 == y.2

structure MiconicProblem (d : Domain) (p : Problem) : Prop where
  /-- The domain is miconic, and `destin` is static in it. -/
  domain : MiconicPinned d
  floorType : "floor" ∈ d.typeNames
  passType : "passenger" ∈ d.typeNames
  /-- Parser validation supplies shared facts such as object-name uniqueness. -/
  validated : Validated d p
  someFloor : ∃ o ∈ allObjects d p, o.type = "floor"
  somePass : ∃ o ∈ allObjects d p, o.type = "passenger"
  /-- Every goal atom asks for a passenger to be served. -/
  goalServed : ∀ a ∈ p.goal, ∃ q ∈ goalPass p, a = served q
  /-- And names a passenger.  `validateProblem` checks it. -/
  goalTyped : ∀ q ∈ goalPass p, ∃ o ∈ allObjects d p, o.name = q ∧ o.type = "passenger"
  goalNodup : (goalPass p).Nodup
  floorExact : ∀ o ∈ allObjects d p, d.isSubtype o.type "floor" = true → o.type = "floor"
  /-- `:init` gives each passenger one destination, at a declared floor. -/
  destinUnique : ∀ a ∈ p.init, ∀ b ∈ p.init, a.pred = "destin" → b.pred = "destin" →
    a.args.head? = b.args.head? → a = b
  destinTyped : ∀ a ∈ p.init, a.pred = "destin" →
    ∃ o ∈ allObjects d p, a.args = [a.args.headD "", o.name] ∧ o.type = "floor"
  /-- Some passenger has to be served, and each has a destination in `:init`. -/
  someGoal : (goalPass p) ≠ []
  destinExists : ∀ k ∈ goalPass p, ∃ a ∈ p.init, a.pred = "destin" ∧ a.args.headD "" = k
  /-- `:init` satisfies the invariant the value reads positions under. -/
  initCheck : initInvCheck p = true

/-! ### The invariant on `:init`, decided -/

theorem mem_liftPlaces {p : Problem} {f : Name} :
    f ∈ liftPlaces p ↔ liftAt f ∈ p.init := by
  constructor
  · intro h
    rw [liftPlaces, List.mem_filterMap] at h
    obtain ⟨a, ha, hval⟩ := h
    by_cases hpred : (a.pred == "lift-at") = true
    · rcases hargs : a.args with _ | ⟨f', rest⟩
      · simp [hpred, hargs] at hval
      · cases rest with
        | cons _ _ => simp [hpred, hargs] at hval
        | nil =>
            simp only [hpred, hargs, Option.some.injEq] at hval
            have : a = liftAt f := by
              show a = { pred := "lift-at", args := [f] }
              rw [← hval, ← hargs, ← (by simpa using hpred : a.pred = "lift-at")]
            rwa [← this]
    · simp only [Bool.not_eq_true] at hpred
      simp [hpred] at hval
  · intro h
    exact List.mem_filterMap.mpr ⟨liftAt f, h, by simp [liftAt]⟩

theorem mem_originPairs {p : Problem} {q f : Name} :
    (q, f) ∈ originPairs p ↔ origin q f ∈ p.init := by
  constructor
  · intro h
    rw [originPairs, List.mem_filterMap] at h
    obtain ⟨a, ha, hval⟩ := h
    by_cases hpred : (a.pred == "origin") = true
    · rcases hargs : a.args with _ | ⟨q', rest⟩
      · simp [hpred, hargs] at hval
      · cases rest with
        | nil => simp [hpred, hargs] at hval
        | cons f' rest' =>
            cases rest' with
            | cons _ _ => simp [hpred, hargs] at hval
            | nil =>
                simp only [hpred, hargs, Option.some.injEq, Prod.mk.injEq] at hval
                obtain ⟨e1, e2⟩ := hval
                have : a = origin q f := by
                  show a = { pred := "origin", args := [q, f] }
                  rw [← e1, ← e2, ← hargs, ← (by simpa using hpred : a.pred = "origin")]
                rwa [← this]
    · simp only [Bool.not_eq_true] at hpred
      simp [hpred] at hval
  · intro h
    exact List.mem_filterMap.mpr ⟨origin q f, h, by simp [origin]⟩

theorem initInv_of_check {p : Problem} (h : initInvCheck p = true) :
    Inv (fun a => p.init.toArray.contains a) := by
  simp only [initInvCheck, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · intro f g hf hg
    have := h1 f (mem_liftPlaces.mpr (by simpa using hf))
    simpa using this g (mem_liftPlaces.mpr (by simpa using hg))
  · intro q f g hf hg
    have := h2 (q, f) (mem_originPairs.mpr (by simpa using hf))
    simpa using this (q, g) (mem_originPairs.mpr (by simpa using hg))

/-! ### The `Cfg` the task describes -/

/-- The passenger a goal entry names, if it names one. -/
def passEntry (t : Task) (x : GroundAtom × Nat) : Option Name :=
  match x.1.pred == "served", x.1.args with
  | true, [q] => some q
  | _, _ => none

/-- Where the task says a passenger is going. -/
def destOf (t : Task) (q : Name) : Option Name :=
  ((t.staticWith "destin").find? fun b =>
      match b.args with
      | [y, _] => y == q
      | _ => false).bind fun b =>
    match b.args with
    | [_, f] => if ((objsOf t "floor").findIdx? (· == f)).isSome then some f else none
    | _ => none

def cfgOf (t : Task) : Cfg where
  passengers := t.goalAtoms.zipIdx.toList.filterMap (passEntry t)
  floors := (objsOf t "floor").toList
  dest := destOf t

theorem cfgOf_floors (t : Task) : (cfgOf t).floors = (objsOf t "floor").toList := rfl

theorem nameOf_cfgOf (t : Task) (i : Nat) :
    nameOf (cfgOf t) i = (objsOf t "floor").getD i "" := by
  unfold nameOf
  rw [cfgOf_floors, List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?]
  simp

theorem floorIndex_sound {t : Task} {f : Name} {i : Nat}
    (h : (objsOf t "floor").findIdx? (· == f) = some i) :
    i < (objsOf t "floor").size ∧ nameOf (cfgOf t) i = f := by
  obtain ⟨hlt, hval⟩ := findIdx_sound h
  exact ⟨hlt, by rw [nameOf_cfgOf]; exact hval⟩

theorem cfgOf_passengers (d : Domain) (p : Problem) :
    (cfgOf (taskOf d p rel)).passengers = goalPass p := by
  show (taskOf d p rel).goalAtoms.zipIdx.toList.filterMap (passEntry (taskOf d p rel)) = _
  rw [show (taskOf d p rel).goalAtoms.zipIdx.toList = p.goal.zipIdx 0 from by
    simp [taskOf_goalAtoms]]
  exact filterMap_zipIdx (fun a => passEntry (taskOf d p rel) (a, 0)) p.goal 0

/-- What the tables need of the task: every atom the heuristic looks up has a
fact.  With pruning off it follows from grounding completeness; with pruning on it
follows from the relevance analysis's own closure. -/
structure MiconicNumbered (d : Domain) (p : Problem) (rel : Bool) : Prop where
  liftAtF : ∀ f, WellTyped d (allObjects d p) "floor" f →
    ∃ n, n < (taskOf d p rel).numFacts ∧
      (taskOf d p rel).factNames.getD n default = liftAt f
  originF : ∀ q f, q ∈ goalPass p → WellTyped d (allObjects d p) "floor" f →
    ∃ n, n < (taskOf d p rel).numFacts ∧
      (taskOf d p rel).factNames.getD n default = origin q f
  boardedF : ∀ q, q ∈ goalPass p →
    ∃ n, n < (taskOf d p rel).numFacts ∧
      (taskOf d p rel).factNames.getD n default = boarded q

/-! ### One `board`, and the three atoms it numbers

Every atom the heuristic reads off the state — `lift-at`, `origin`, `boarded` —
appears in one `board`, whose two preconditions are both dynamic.  So a single
instance carries all three, and no static precondition has to be checked.
-/

def boardInst {d : Domain} {p : Problem} (hd : MiconicDomain d) {f q : Name}
    (h1 : WellTyped d (allObjects d p) "floor" f)
    (h2 : WellTyped d (allObjects d p) "passenger" q) : Instance d (allObjects d p) where
  schema := boardA
  mem := by rw [hd]; simp
  args := [f, q]
  typed := List.Forall₂.cons h1 (List.Forall₂.cons h2 List.Forall₂.nil)

theorem board_named {d : Domain} {p : Problem} (hd : MiconicDomain d)
    (hfl : "floor" ∈ d.typeNames) (hpa : "passenger" ∈ d.typeNames) {f q : Name}
    (h1 : WellTyped d (allObjects d p) "floor" f)
    (h2 : WellTyped d (allObjects d p) "passenger" q) {y : Atom}
    (hy : y ∈ boardA.pre ∨ y ∈ boardA.add ∨ y ∈ boardA.del) :
    ∃ n, n < (taskOf d p false).numFacts ∧
      (taskOf d p false).factNames.getD n default = instAtom boardA.params [f, q] y := by
  refine ground_names_instance d p (boardInst (p := p) hd h1 h2) ?_ ?_ ?_
  · intro pm hpm
    have : pm = floorP ∨ pm = passP := by simpa [boardInst, boardA] using hpm
    rcases this with rfl | rfl
    · exact hfl
    · exact hpa
  · intro z hz hc
    have hz' : z = liftAtV "?f" ∨ z = originV "?p" "?f" := by
      simpa [boardInst, boardA] using hz
    rcases hz' with rfl | rfl
    · have h' : (staticPredicates d).contains "lift-at" = true := hc
      rw [liftAt_dynamic hd] at h'; exact absurd h' (by simp)
    · have h' : (staticPredicates d).contains "origin" = true := hc
      rw [origin_dynamic hd] at h'; exact absurd h' (by simp)
  · rcases hy with h | h | h
    · refine Or.inl ⟨by simpa [boardInst] using h, ?_⟩
      have hz' : y = liftAtV "?f" ∨ y = originV "?p" "?f" := by simpa [boardA] using h
      rcases hz' with rfl | rfl
      · exact liftAt_dynamic hd
      · exact origin_dynamic hd
    · exact Or.inr (Or.inl (by simpa [boardInst] using h))
    · exact Or.inr (Or.inr (by simpa [boardInst] using h))

theorem liftAt_named {d : Domain} {p : Problem} (hd : MiconicDomain d)
    (hfl : "floor" ∈ d.typeNames) (hpa : "passenger" ∈ d.typeNames) {f q : Name}
    (h1 : WellTyped d (allObjects d p) "floor" f)
    (h2 : WellTyped d (allObjects d p) "passenger" q) :
    ∃ n, n < (taskOf d p false).numFacts ∧
      (taskOf d p false).factNames.getD n default = liftAt f := by
  have h := board_named hd hfl hpa h1 h2 (y := liftAtV "?f") (Or.inl (by simp [boardA]))
  simpa [instAtom, boardA, floorP, passP, liftAtV, liftAt] using h

theorem origin_named {d : Domain} {p : Problem} (hd : MiconicDomain d)
    (hfl : "floor" ∈ d.typeNames) (hpa : "passenger" ∈ d.typeNames) {f q : Name}
    (h1 : WellTyped d (allObjects d p) "floor" f)
    (h2 : WellTyped d (allObjects d p) "passenger" q) :
    ∃ n, n < (taskOf d p false).numFacts ∧
      (taskOf d p false).factNames.getD n default = origin q f := by
  have h := board_named hd hfl hpa h1 h2 (y := originV "?p" "?f") (Or.inl (by simp [boardA]))
  simpa [instAtom, boardA, floorP, passP, originV, origin] using h

theorem boarded_named {d : Domain} {p : Problem} (hd : MiconicDomain d)
    (hfl : "floor" ∈ d.typeNames) (hpa : "passenger" ∈ d.typeNames) {f q : Name}
    (h1 : WellTyped d (allObjects d p) "floor" f)
    (h2 : WellTyped d (allObjects d p) "passenger" q) :
    ∃ n, n < (taskOf d p false).numFacts ∧
      (taskOf d p false).factNames.getD n default = boarded q := by
  have h := board_named hd hfl hpa h1 h2 (y := boardedV "?p")
    (Or.inr (Or.inl (by simp [boardA])))
  simpa [instAtom, boardA, floorP, passP, boardedV, boarded] using h

/-! ### What `compile` returns, named -/

theorem compile_liftAt (t : Task) :
    (ExampleHeuristics.Miconic.compile t).liftAt
      = (t.factsWith "lift-at").filterMap (fun y =>
          match y.2.args with
          | [x] => ((objsOf t "floor").findIdx? (· == x)).map ((y.1, ·))
          | _ => none) := rfl

theorem compile_passengers (t : Task) :
    (ExampleHeuristics.Miconic.compile t).passengers
      = t.goalAtoms.zipIdx.filterMap
          (ExampleHeuristics.Miconic.passengerEntry t (t.factsWith "origin")
            (t.factsWith "boarded") (t.staticWith "destin")
            (fun f => (objsOf t "floor").findIdx? (· == f))) := rfl

theorem destOf_of_find {t : Task} {q : Name} {b : GroundAtom}
    (hfind : (t.staticWith "destin").find? (fun b =>
      match b.args with
      | [z, _] => z == q
      | _ => false) = some b) :
    destOf t q = (match b.args with
      | [_, f] => if ((objsOf t "floor").findIdx? (· == f)).isSome then some f else none
      | _ => none) := by
  rw [destOf, hfind]; rfl

/-! ### The tables -/

section Match

variable {d : Domain} {p : Problem} {rel : Bool} (hp : MiconicProblem d p)
  (hn : MiconicNumbered d p rel)

include hp

theorem some_floor_pass : ∃ f q, WellTyped d (allObjects d p) "floor" f ∧
    WellTyped d (allObjects d p) "passenger" q := by
  obtain ⟨of, hof, htf⟩ := hp.someFloor
  obtain ⟨oq, hoq, htq⟩ := hp.somePass
  exact ⟨of.name, oq.name, wellTyped_of_type hof htf, wellTyped_of_type hoq htq⟩

theorem pass_typed {q : Name} (hq : q ∈ goalPass p) :
    WellTyped d (allObjects d p) "passenger" q := by
  obtain ⟨o, ho, hn, ht⟩ := hp.goalTyped q hq
  exact hn ▸ wellTyped_of_type ho ht

theorem goal_of_goalPass {q : Name} (hq : q ∈ goalPass p) : served q ∈ p.goal := by
  rw [goalPass, List.mem_filterMap] at hq
  obtain ⟨a, ha, hval⟩ := hq
  by_cases hpred : (a.pred == "served") = true
  · rcases hargs : a.args with _ | ⟨q', rest⟩
    · simp [hpred, hargs] at hval
    · cases rest with
      | cons _ _ => simp [hpred, hargs] at hval
      | nil =>
          simp only [hpred, hargs, Option.some.injEq] at hval
          have : a = served q := by
            show a = { pred := "served", args := [q] }
            rw [← hval, ← hargs, ← (by simpa using hpred : a.pred = "served")]
          rwa [← this]
  · simp only [Bool.not_eq_true] at hpred
    simp [hpred] at hval

include hn in
theorem floorMatch :
    FloorMatch (taskOf d p rel) (cfgOf (taskOf d p rel))
      (ExampleHeuristics.Miconic.compile (taskOf d p rel)) := by
  refine ⟨by rw [cfgOf_floors]; exact objsOf_nodup hp.validated.namesNodup, ?_, ?_⟩
  · intro x hx
    rw [compile_liftAt, Array.mem_filterMap] at hx
    obtain ⟨y, hy, hval⟩ := hx
    obtain ⟨hrange, hname, hpred⟩ := mem_factsWith hy
    rcases hargs : y.2.args with _ | ⟨f, rest⟩
    · rw [hargs] at hval; simp at hval
    · cases rest with
      | cons _ _ => rw [hargs] at hval; simp at hval
      | nil =>
          rw [hargs] at hval
          dsimp only at hval
          rcases hi : (objsOf (taskOf d p rel) "floor").findIdx? (· == f) with _ | i
          · rw [hi] at hval; simp at hval
          · rw [hi] at hval
            simp only [Option.map_some, Option.some.injEq] at hval
            subst hval
            obtain ⟨hlt, hnm⟩ := floorIndex_sound hi
            refine ⟨?_, hrange, ?_⟩
            · rw [hname, hnm]
              show y.2 = liftAt f
              unfold liftAt
              rw [← hpred, ← hargs]
            · rw [cfgOf_floors]; simpa using hlt
  · intro g hg
    rw [cfgOf_floors] at hg
    have hgm : g ∈ objsOf (taskOf d p rel) "floor" := by simpa using hg
    obtain ⟨-, q, -, hq⟩ := some_floor_pass hp
    obtain ⟨n, hlt, hname⟩ :=
      hn.liftAtF g (objsOf_wellTyped hgm)
    obtain ⟨i, hi⟩ := findIdx_total hgm
    refine ⟨(n, i), ?_, (floorIndex_sound hi).2⟩
    rw [compile_liftAt, Array.mem_filterMap]
    refine ⟨(n, liftAt g), mem_factsWith_of_named (by rwa [← taskOf_numFacts]) hname rfl, ?_⟩
    simp [liftAt, hi]

/-- With pruning off, grounding completeness numbers all three atom families. -/
theorem miconicNumbered_false : MiconicNumbered d p false := by
  obtain ⟨f0, q0, hf0, hq0⟩ := some_floor_pass hp
  exact ⟨fun f hf => liftAt_named hp.domain.actions hp.floorType hp.passType hf hq0,
    fun q f hqm hf => origin_named hp.domain.actions hp.floorType hp.passType hf
      (pass_typed hp hqm),
    fun q hqm => boarded_named hp.domain.actions hp.floorType hp.passType hf0
      (pass_typed hp hqm)⟩

include hn in
/-- One compiled passenger entry says the right things. -/
theorem entryMatch {x : GroundAtom × Nat} {q : Name}
    (hx : x ∈ (taskOf d p rel).goalAtoms.zipIdx)
    (hpred : x.1.pred = "served") (hargs : x.1.args = [q]) :
    EntryMatches (taskOf d p rel) (cfgOf (taskOf d p rel))
      { goalFact := (taskOf d p rel).goal.getD x.2 0
        boardedFact := (((taskOf d p rel).factsWith "boarded").find?
          fun y => y.2.args == [q]).map (·.1)
        originFacts := ((taskOf d p rel).factsWith "origin").filterMap fun y =>
          match y.2.args with
          | [z, f] =>
              if z == q then
                ((objsOf (taskOf d p rel) "floor").findIdx? (· == f)).map ((y.1, ·))
              else none
          | _ => none
        destFloor := (((taskOf d p rel).staticWith "destin").find? fun b =>
          match b.args with
          | [z, _] => z == q
          | _ => false).bind fun b =>
            match b.args with
            | [_, f] => (objsOf (taskOf d p rel) "floor").findIdx? (· == f)
            | _ => none }
      q := by
  obtain ⟨f0, -, hf0, -⟩ := some_floor_pass hp
  have hqm : q ∈ goalPass p := by
    rw [← cfgOf_passengers d p]
    show q ∈ (taskOf d p rel).goalAtoms.zipIdx.toList.filterMap (passEntry (taskOf d p rel))
    exact List.mem_filterMap.mpr ⟨x, Array.mem_def.mp hx, by simp [passEntry, hpred, hargs]⟩
  have hqT : WellTyped d (allObjects d p) "passenger" q := pass_typed hp hqm
  -- the goal atom this entry came from
  have hget : (taskOf d p rel).goalAtoms[x.2]? = some x.1 := Array.mem_zipIdx_iff_getElem?.mp hx
  have hlt : x.2 < (taskOf d p rel).goalAtoms.size := by
    by_contra hc
    rw [Array.getElem?_eq_none (by omega)] at hget
    simp at hget
  have hatom : (taskOf d p rel).goalAtoms[x.2]'hlt = served q := by
    rw [Array.getElem?_eq_getElem hlt] at hget
    have hs : x.1 = served q := by
      show x.1 = { pred := "served", args := [q] }
      rw [← hpred, ← hargs]
    rw [← hs]
    simpa using hget
  obtain ⟨hname, hrange⟩ := goal_name_eq d p rel hlt
  refine ⟨by rw [hname, hatom], hrange, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    refine ⟨?_, ?_⟩
    · have := factsWith_find_args_map hn
      rw [this]; rfl
    · rcases hfind : (((taskOf d p rel).factsWith "boarded").find?
          fun y => y.2.args == [q]) with _ | z
      · rw [hfind] at hn; simp at hn
      · rw [hfind] at hn
        simp only [Option.map_some, Option.some.injEq] at hn
        subst hn
        exact (mem_factsWith (Array.mem_of_find?_eq_some hfind)).1
  · intro hnone
    obtain ⟨n, hnlt, hnname⟩ :=
      hn.boardedF q hqm
    have hmem : (n, boarded q) ∈ (taskOf d p rel).factsWith "boarded" :=
      mem_factsWith_of_named (by rwa [← taskOf_numFacts]) hnname rfl
    rcases hfind : (((taskOf d p rel).factsWith "boarded").find?
        fun y => y.2.args == [q]) with _ | z
    · rw [Array.find?_eq_none] at hfind
      exact absurd (hfind _ hmem) (by simp [boarded])
    · rw [hfind] at hnone; simp at hnone
  · intro y hy
    rw [Array.mem_filterMap] at hy
    obtain ⟨z, hz, hval⟩ := hy
    obtain ⟨hzr, hzn, hzp⟩ := mem_factsWith hz
    rcases hza : z.2.args with _ | ⟨c1, rest⟩
    · rw [hza] at hval; simp at hval
    · cases rest with
      | nil => rw [hza] at hval; simp at hval
      | cons fl rest' =>
          cases rest' with
          | cons _ _ => rw [hza] at hval; simp at hval
          | nil =>
              rw [hza] at hval
              dsimp only at hval
              by_cases hc1 : (c1 == q) = true
              · rw [if_pos hc1] at hval
                rcases hj : (objsOf (taskOf d p rel) "floor").findIdx? (· == fl) with _ | j
                · rw [hj] at hval; simp at hval
                · rw [hj] at hval
                  simp only [Option.map_some, Option.some.injEq] at hval
                  subst hval
                  obtain ⟨hjl, hjn⟩ := floorIndex_sound hj
                  refine ⟨?_, hzr, ?_⟩
                  · rw [hzn, hjn]
                    show z.2 = { pred := "origin", args := [q, fl] }
                    rw [(by simpa using hc1 : c1 = q)] at hza
                    rw [← hzp, ← hza]
                  · rw [cfgOf_floors]; simpa using hjl
              · rw [if_neg hc1] at hval; simp at hval
  · intro g hg
    rw [cfgOf_floors] at hg
    have hgm : g ∈ objsOf (taskOf d p rel) "floor" := by simpa using hg
    obtain ⟨n, hnlt, hnname⟩ :=
      hn.originF q g hqm (objsOf_wellTyped hgm)
    obtain ⟨j, hj⟩ := findIdx_total hgm
    refine ⟨(n, j), ?_, (floorIndex_sound hj).2⟩
    rw [Array.mem_filterMap]
    refine ⟨(n, origin q g),
      mem_factsWith_of_named (by rwa [← taskOf_numFacts]) hnname rfl, ?_⟩
    simp [origin, hj]
  · intro i hi
    rcases hfind : (((taskOf d p rel).staticWith "destin").find? fun b =>
        match b.args with
        | [z, _] => z == q
        | _ => false) with _ | b
    · rw [hfind] at hi; simp at hi
    · rw [hfind] at hi
      simp only [Option.bind_some] at hi
      show destOf (taskOf d p rel) q = some (nameOf (cfgOf (taskOf d p rel)) i) ∧ _
      rw [destOf_of_find hfind]
      revert hi
      rcases hba : b.args with _ | ⟨z, rest⟩
      · intro hi; simp at hi
      · cases rest with
        | nil => intro hi; simp at hi
        | cons fl rest' =>
            cases rest' with
            | cons _ _ => intro hi; simp at hi
            | nil =>
                intro hi
                dsimp only at hi ⊢
                obtain ⟨hjl, hjn⟩ := floorIndex_sound hi
                exact ⟨by rw [if_pos (by rw [hi]; simp), hjn],
                  by rw [cfgOf_floors]; simpa using hjl⟩
  · intro hnone
    rcases hfind : (((taskOf d p rel).staticWith "destin").find? fun b =>
        match b.args with
        | [z, _] => z == q
        | _ => false) with _ | b
    · show destOf (taskOf d p rel) q = none
      rw [destOf, hfind]; rfl
    · rw [hfind] at hnone
      simp only [Option.bind_some] at hnone
      show destOf (taskOf d p rel) q = none
      rw [destOf_of_find hfind]
      revert hnone
      rcases hba : b.args with _ | ⟨z, rest⟩
      · intro _; rfl
      · cases rest with
        | nil => intro _; rfl
        | cons fl rest' =>
            cases rest' with
            | cons _ _ => intro _; rfl
            | nil =>
                intro hnone
                dsimp only at hnone ⊢
                rw [hnone]
                rfl

include hn in
theorem dataMatches :
    DataMatches (taskOf d p rel) (cfgOf (taskOf d p rel))
      (ExampleHeuristics.Miconic.compile (taskOf d p rel)) := by
  show List.Forall₂ (EntryMatches (taskOf d p rel) (cfgOf (taskOf d p rel)))
    (ExampleHeuristics.Miconic.compile (taskOf d p rel)).passengers.toList
    (cfgOf (taskOf d p rel)).passengers
  rw [compile_passengers, Array.toList_filterMap]
  show List.Forall₂ _ _ ((taskOf d p rel).goalAtoms.zipIdx.toList.filterMap
    (passEntry (taskOf d p rel)))
  refine forall₂_filterMap _ ?_
  intro x hx
  by_cases hpred : (x.1.pred == "served") = true
  · rcases hargs : x.1.args with _ | ⟨q, rest⟩
    · exact ⟨fun pi hpi => by
        simp [ExampleHeuristics.Miconic.passengerEntry, hpred, hargs] at hpi,
      fun _ => by simp [passEntry, hpred, hargs]⟩
    · cases rest with
      | cons _ _ =>
          exact ⟨fun pi hpi => by
            simp [ExampleHeuristics.Miconic.passengerEntry, hpred, hargs] at hpi,
          fun _ => by simp [passEntry, hpred, hargs]⟩
      | nil =>
          refine ⟨fun pi hpi => ⟨q, by simp [passEntry, hpred, hargs], ?_⟩, fun hn => ?_⟩
          · simp only [ExampleHeuristics.Miconic.passengerEntry, hpred, hargs,
              Option.some.injEq] at hpi
            rw [← hpi]
            exact entryMatch hp hn (Array.mem_def.mpr (by simpa using hx))
              (by simpa using hpred) hargs
          · simp [ExampleHeuristics.Miconic.passengerEntry, hpred, hargs] at hn
  · simp only [Bool.not_eq_true] at hpred
    exact ⟨fun pi hpi => by
      simp [ExampleHeuristics.Miconic.passengerEntry, hpred] at hpi,
    fun _ => by simp [passEntry, hpred]⟩

/-! ### The configuration is the one the lifted proof asks for -/

theorem destin_static_mem {q f : Name} (hinit : destin q f ∈ p.init) :
    destin q f ∈ (taskOf d p rel).staticWith "destin" := by
  refine mem_staticWith d p rel hinit ?_ rfl
  intro hmem
  have hgoal := mem_goal_of_static d p rel hmem (by simpa [destin] using hp.domain.destinStatic)
  obtain ⟨q', -, hq'⟩ := hp.goalServed _ hgoal
  simp [destin, served] at hq'

theorem cfgOK : CfgOK d p (cfgOf (taskOf d p rel)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨o, ho, hname, hsub⟩ := hg
    rw [cfgOf_floors]
    simpa using (mem_objsOf ho hname (hp.floorExact o ho hsub) :
      g ∈ objsOf (taskOf d p rel) "floor")
  · intro q f hcon
    have hinit : destin q f ∈ p.init := by simpa using hcon
    have hst := destin_static_mem (rel := rel) hp hinit
    -- the destination is a declared floor, so its index exists
    obtain ⟨o, ho, hargs, hty⟩ := hp.destinTyped _ hinit rfl
    have hof : f = o.name := by simpa [destin] using hargs
    have hfm : f ∈ objsOf (taskOf d p rel) "floor" := mem_objsOf ho hof.symm hty
    obtain ⟨j, hj⟩ := findIdx_total hfm
    rcases hfind : (((taskOf d p rel).staticWith "destin").find? fun b =>
        match b.args with
        | [z, _] => z == q
        | _ => false) with _ | b
    · rw [Array.find?_eq_none] at hfind
      exact absurd (hfind _ hst) (by simp [destin])
    · have hbmem := Array.mem_of_find?_eq_some hfind
      have hbp := Array.find?_some hfind
      obtain ⟨hbinit, hbpred⟩ := staticWith_sub d p rel hbmem
      have hbq : b.args.head? = some q := by
        rcases hba : b.args with _ | ⟨z, rest⟩
        · rw [hba] at hbp; simp at hbp
        · cases rest with
          | nil => rw [hba] at hbp; simp at hbp
          | cons _ rest' =>
              cases rest' with
              | cons _ _ => rw [hba] at hbp; simp at hbp
              | nil =>
                  rw [hba] at hbp
                  simp only [List.head?_cons, Option.some.injEq]
                  simpa using hbp
      have hbeq : b = destin q f :=
        hp.destinUnique b hbinit _ hinit hbpred rfl (by rw [hbq]; simp [destin])
      show destOf (taskOf d p rel) q = some f
      rw [destOf_of_find hfind, hbeq]
      show (if ((objsOf (taskOf d p rel) "floor").findIdx? (· == f)).isSome then some f
        else none) = some f
      rw [if_pos (by rw [hj]; simp)]
  · rw [cfgOf_passengers]; exact hp.goalNodup

theorem served_sub : ∀ q ∈ (cfgOf (taskOf d p rel)).passengers, served q ∈ p.goal := by
  intro q hq
  rw [cfgOf_passengers] at hq
  exact goal_of_goalPass hp hq

/-! ### Miconic, end to end -/

theorem opFacts_all : ∀ o ∈ groundedOps d p rel, Nonempty (OpFacts d p o) :=
  fun o ho => opFacts_ground d p rel ho

theorem cost_pos : ∀ o ∈ groundedOps d p rel, 0 < o.cost := by
  intro o ho
  obtain ⟨f⟩ := opFacts_all hp o ho
  rw [f.cost]
  show 0 < f.inst.schema.cost
  have hmem : f.inst.schema ∈ [boardA, departA, upA, downA] := hp.domain.actions ▸ f.inst.mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h <;> rw [h] <;> simp [boardA, departA, upA, downA]

include hn in
/-- **Miconic's improved heuristic is goal-aware on the task the planner searches.** -/
theorem improved_goalAware :
    (ground d p rel).GoalAwareOn (Reachable (ground d p rel))
      (ExampleHeuristics.Miconic.improved (ground d p rel)).eval :=
  improved_goalAwareOn d p rel (cfgOf (taskOf d p rel)) hp.domain (cfgOK hp)
    (ground_wf d p rel (cost_pos hp)) (cost_pos hp) (opFacts_all hp)
    (served_sub hp) (initInv_of_check hp.initCheck) _
    (computes (dataMatches hp hn) (floorMatch hp hn) rfl)

include hn in
/-- **Miconic's improved heuristic is consistent on the task the planner searches.** -/
theorem improved_consistent :
    (ground d p rel).ConsistentOn (Reachable (ground d p rel))
      (ExampleHeuristics.Miconic.improved (ground d p rel)).eval :=
  improved_consistentOn d p rel (cfgOf (taskOf d p rel)) hp.domain (cfgOK hp)
    (ground_wf d p rel (cost_pos hp)) (cost_pos hp) (opFacts_all hp)
    (initInv_of_check hp.initCheck) _
    (computes (dataMatches hp hn) (floorMatch hp hn) rfl)

include hn in
/--
**Miconic's improved heuristic is admissible on the task the planner searches.**
Nothing about the heuristic is assumed; the only hypothesis is `MiconicProblem`,
one decidable pass over the parsed domain and problem.
-/
theorem improved_admissible :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel))
      (ExampleHeuristics.Miconic.improved (ground d p rel)).eval :=
  improved_admissibleOn d p rel (cfgOf (taskOf d p rel)) hp.domain (cfgOK hp)
    (ground_wf d p rel (cost_pos hp)) (cost_pos hp) (opFacts_all hp)
    (served_sub hp) (initInv_of_check hp.initCheck) _
    (computes (dataMatches hp hn) (floorMatch hp hn) rfl)

end Match

/-! ### With the relevance analysis on

Miconic's chain is two steps.  A passenger's `served` goal is relevant, and the
`depart` that would meet it adds that goal atom, so it survives and closure puts
its dynamic preconditions in the set, which is where `boarded` comes from.  Every
`board` for that passenger then adds a relevant `boarded`, so every `lift-at` and
every `origin` follows.  `destin` is static and is never numbered at all.
-/

section Pruned

variable {d : Domain} {p : Problem} (hp : MiconicProblem d p)

private abbrev rset : Std.HashSet GroundAtom := relevantSet (rawOps d p) p.goal.toArray

private theorem touches_of_add {o : AtomOp} {r : Std.HashSet GroundAtom} {x : GroundAtom}
    (hx : x ∈ o.add) (hr : r.contains x = true) : o.touches r = true := by
  simp only [AtomOp.touches, Bool.or_eq_true, Array.any_eq_true]
  obtain ⟨i, hi, hval⟩ := Array.getElem_of_mem hx
  exact Or.inl ⟨i, hi, by rw [hval]; exact hr⟩

include hp

private theorem dynBoard :
    boardA.pre.filter (fun x => !(staticPredicates d).contains x.pred) = boardA.pre := by
  refine List.filter_eq_self.mpr ?_
  intro y hy
  have hy' : y = liftAtV "?f" ∨ y = originV "?p" "?f" := by simpa [boardA] using hy
  rcases hy' with rfl | rfl
  · simpa using liftAt_dynamic hp.domain.actions
  · simpa using origin_dynamic hp.domain.actions

private theorem dynDepart :
    departA.pre.filter (fun x => !(staticPredicates d).contains x.pred)
      = [liftAtV "?f", boardedV "?p"] := by
  have h1 : (liftAtV "?f").pred ∉ staticPredicates d := by
    have := liftAt_dynamic hp.domain.actions
    simpa [liftAtV] using this
  have h2 : (destinV "?p" "?f").pred ∈ staticPredicates d := by
    have := hp.domain.destinStatic
    simpa [destinV] using this
  have h3 : (boardedV "?p").pred ∉ staticPredicates d := by
    have := boarded_dynamic hp.domain.actions
    simpa [boardedV] using this
  simp [departA, List.filter_cons, h1, h2, h3]

/-- One `board` and one `depart`, as the grounder emits them. -/
private def boardRaw (f q : Name) : AtomOp :=
  mkOp boardA (boardA.pre.filter fun x => !(staticPredicates d).contains x.pred) #[f, q]

private def departRaw (f q : Name) : AtomOp :=
  mkOp departA (departA.pre.filter fun x => !(staticPredicates d).contains x.pred) #[f, q]

private theorem inst_hty' (i : Instance d (allObjects d p)) :
    ∀ pm ∈ i.schema.params, pm.type ∈ d.typeNames := by
  intro pm hpm
  have hmem : i.schema ∈ [boardA, departA, upA, downA] := hp.domain.actions ▸ i.mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  have hpm' : pm.type = "floor" ∨ pm.type = "passenger" := by
    rcases hmem with h | h | h | h <;> rw [h] at hpm <;>
      simp only [boardA, departA, upA, downA, floorP, passP, f1P, f2P, List.mem_cons,
        List.not_mem_nil, or_false] at hpm <;>
      rcases hpm with rfl | rfl <;> simp
  rcases hpm' with hh | hh <;> rw [hh]
  · exact hp.floorType
  · exact hp.passType

/-- The instance of `board` and of `depart` for a passenger and a floor. -/
private def departInst {f q : Name} (h1 : WellTyped d (allObjects d p) "floor" f)
    (h2 : WellTyped d (allObjects d p) "passenger" q) : Instance d (allObjects d p) where
  schema := departA
  mem := by rw [hp.domain.actions]; simp
  args := [f, q]
  typed := List.Forall₂.cons h1 (List.Forall₂.cons h2 List.Forall₂.nil)

private theorem board_hstat {f q : Name} :
    ∀ y ∈ boardA.pre, (staticPredicates d).contains y.pred = true →
      instAtom boardA.params [f, q] y ∈ p.init := by
  intro y hy hc
  have hy' : y = liftAtV "?f" ∨ y = originV "?p" "?f" := by simpa [boardA] using hy
  rcases hy' with rfl | rfl
  · have h' : (staticPredicates d).contains "lift-at" = true := hc
    rw [liftAt_dynamic hp.domain.actions] at h'; exact absurd h' (by simp)
  · have h' : (staticPredicates d).contains "origin" = true := hc
    rw [origin_dynamic hp.domain.actions] at h'; exact absurd h' (by simp)

private theorem boardRaw_mem {f q : Name} (h1 : WellTyped d (allObjects d p) "floor" f)
    (h2 : WellTyped d (allObjects d p) "passenger" q) :
    boardRaw (d := d) f q ∈ rawOps d p := by
  rw [← groundedOps_false]
  refine groundedOps_complete d p (a := boardA) (by rw [hp.domain.actions]; simp) #[f, q]
    rfl (inst_hty' hp (boardInst (p := p) hp.domain.actions h1 h2)) ?_ ?_
  · exact List.Forall₂.cons h1 (List.Forall₂.cons h2 List.Forall₂.nil)
  · exact board_hstat hp

private theorem departRaw_mem {f q : Name} (h1 : WellTyped d (allObjects d p) "floor" f)
    (h2 : WellTyped d (allObjects d p) "passenger" q) (hd : destin q f ∈ p.init) :
    departRaw (d := d) f q ∈ rawOps d p := by
  rw [← groundedOps_false]
  refine groundedOps_complete d p (a := departA) (by rw [hp.domain.actions]; simp) #[f, q]
    rfl (inst_hty' hp (departInst hp h1 h2)) ?_ ?_
  · exact List.Forall₂.cons h1 (List.Forall₂.cons h2 List.Forall₂.nil)
  · intro y hy hc
    have hy' : y = liftAtV "?f" ∨ y = destinV "?p" "?f" ∨ y = boardedV "?p" := by
      simpa [departA] using hy
    rcases hy' with rfl | rfl | rfl
    · have h' : (staticPredicates d).contains "lift-at" = true := hc
      rw [liftAt_dynamic hp.domain.actions] at h'; exact absurd h' (by simp)
    · simpa [instAtom, departA, floorP, passP, destinV, destin] using hd
    · have h' : (staticPredicates d).contains "boarded" = true := hc
      rw [boarded_dynamic hp.domain.actions] at h'; exact absurd h' (by simp)

/-- The static precondition of a `depart` really holds, so the instance is real. -/
private theorem depart_hstat {f q : Name} (hd : destin q f ∈ p.init) :
    ∀ y ∈ departA.pre, (staticPredicates d).contains y.pred = true →
      instAtom departA.params [f, q] y ∈ p.init := by
  intro y hy hc
  have hy' : y = liftAtV "?f" ∨ y = destinV "?p" "?f" ∨ y = boardedV "?p" := by
    simpa [departA] using hy
  rcases hy' with rfl | rfl | rfl
  · have h' : (staticPredicates d).contains "lift-at" = true := hc
    rw [liftAt_dynamic hp.domain.actions] at h'; exact absurd h' (by simp)
  · simpa [instAtom, departA, floorP, passP, destinV, destin] using hd
  · have h' : (staticPredicates d).contains "boarded" = true := hc
    rw [boarded_dynamic hp.domain.actions] at h'; exact absurd h' (by simp)


variable (hok : relevantOK (rawOps d p) p.goal.toArray (rset (d := d) (p := p)) = true)

include hok

/-- A goal passenger's `boarded` and their destination floor's `lift-at` are
relevant, because the `depart` that would serve them adds the goal atom. -/
private theorem depart_rel {k f : Name} (hk : k ∈ goalPass p) (hd : destin k f ∈ p.init)
    (hf : WellTyped d (allObjects d p) "floor" f)
    (hkT : WellTyped d (allObjects d p) "passenger" k) :
    (rset (d := d) (p := p)).contains (boarded k) = true := by
  have hgoal : served k ∈ p.goal := goal_of_goalPass hp hk
  have hr : (rset (d := d) (p := p)).contains (served k) = true :=
    (relevance_verified hok).2.1 _ (by simpa using hgoal)
  have hadd : served k ∈ (departRaw (d := d) f k).add := by
    have h := mem_mkOp_add departA (departA.pre.filter fun y =>
      !(staticPredicates d).contains y.pred) #[f, k] (y := servedV "?p")
      (by simp [departA]) ?_
    · simpa [departRaw, instAtom, departA, floorP, passP, servedV, served] using h
    · intro z hz
      rw [dynDepart hp] at hz
      have hz' : z = liftAtV "?f" ∨ z = boardedV "?p" := by simpa using hz
      rcases hz' with rfl | rfl <;>
        simp [instAtom, departA, floorP, passP, liftAtV, boardedV, servedV,
          liftAt, boarded, served]
  have hpre := (relevance_verified hok).1 _ (departRaw_mem hp hf hkT hd)
    (touches_of_add hadd hr)
  have hin : instAtom departA.params [f, k] (boardedV "?p")
      ∈ (departRaw (d := d) f k).pre := by
    have := mem_mkOp_pre departA (departA.pre.filter fun z =>
      !(staticPredicates d).contains z.pred) #[f, k] (y := boardedV "?p")
      (by rw [dynDepart hp]; simp)
    simpa [departRaw] using this
  have := hpre _ hin
  simpa [instAtom, departA, floorP, passP, boardedV, boarded] using this

/-- And then every `lift-at` and every `origin` for that passenger is. -/
private theorem board_rel {k f : Name} (hb : (rset (d := d) (p := p)).contains (boarded k) = true)
    (hf : WellTyped d (allObjects d p) "floor" f)
    (hkT : WellTyped d (allObjects d p) "passenger" k) :
    (boardRaw (d := d) f k).touches (rset (d := d) (p := p)) = true ∧
    (rset (d := d) (p := p)).contains (liftAt f) = true ∧
    (rset (d := d) (p := p)).contains (origin k f) = true := by
  have hadd : boarded k ∈ (boardRaw (d := d) f k).add := by
    have h := mem_mkOp_add boardA (boardA.pre.filter fun y =>
      !(staticPredicates d).contains y.pred) #[f, k] (y := boardedV "?p")
      (by simp [boardA]) ?_
    · simpa [boardRaw, instAtom, boardA, floorP, passP, boardedV, boarded] using h
    · intro z hz
      rw [dynBoard hp] at hz
      have hz' : z = liftAtV "?f" ∨ z = originV "?p" "?f" := by simpa [boardA] using hz
      rcases hz' with rfl | rfl <;>
        simp [instAtom, boardA, floorP, passP, liftAtV, originV, boardedV,
          liftAt, origin, boarded]
  have htouch := touches_of_add hadd hb
  have hpre := (relevance_verified hok).1 _ (boardRaw_mem hp hf hkT) htouch
  have hin : ∀ y ∈ boardA.pre, instAtom boardA.params [f, k] y
      ∈ (boardRaw (d := d) f k).pre := by
    intro y hy
    have := mem_mkOp_pre boardA (boardA.pre.filter fun z =>
      !(staticPredicates d).contains z.pred) #[f, k] (y := y) (by rw [dynBoard hp]; exact hy)
    simpa [boardRaw] using this
  refine ⟨htouch, ?_, ?_⟩
  · have := hpre _ (hin (liftAtV "?f") (by simp [boardA]))
    simpa [instAtom, boardA, floorP, passP, liftAtV, liftAt] using this
  · have := hpre _ (hin (originV "?p" "?f") (by simp [boardA]))
    simpa [instAtom, boardA, floorP, passP, originV, origin] using this

omit hok in
private theorem goal_destin {k : Name} (hk : k ∈ goalPass p) :
    ∃ f, destin k f ∈ p.init ∧ WellTyped d (allObjects d p) "floor" f := by
  obtain ⟨a, ha, hpred, hhead⟩ := hp.destinExists k hk
  obtain ⟨o, ho, hargs, hty⟩ := hp.destinTyped a ha hpred
  rw [hhead] at hargs
  refine ⟨o.name, ?_, wellTyped_of_type ho hty⟩
  have heq : a = destin k o.name := by
    show a = { pred := "destin", args := [k, o.name] }
    rw [← hpred, ← hargs]
  rwa [← heq]

/-- **The three families are numbered with pruning on, too.** -/
theorem miconicNumbered_verified : MiconicNumbered d p true := by
  have hrdef := (relevance_verified hok).2.2
  have hboarded : ∀ k ∈ goalPass p, (rset (d := d) (p := p)).contains (boarded k) = true := by
    intro k hk
    obtain ⟨f, hd, hf⟩ := goal_destin hp hk
    exact depart_rel hp hok hk hd hf (pass_typed hp hk)
  have hname : ∀ {f k : Name}, WellTyped d (allObjects d p) "floor" f →
      WellTyped d (allObjects d p) "passenger" k →
      (rset (d := d) (p := p)).contains (boarded k) = true →
      ∀ y : Atom, (y ∈ boardA.pre ∧ (staticPredicates d).contains y.pred = false) ∨
        ((y ∈ boardA.add ∨ y ∈ boardA.del) ∧
          (rset (d := d) (p := p)).contains (instAtom boardA.params [f, k] y) = true) →
      ∃ n, n < (taskOf d p true).numFacts ∧
        (taskOf d p true).factNames.getD n default = instAtom boardA.params [f, k] y := by
    intro f k hf hk hb y hy
    exact ground_names_instance_pruned d p (boardInst (p := p) hp.domain.actions hf hk)
      (inst_hty' hp _) (board_hstat hp) _ hrdef (board_rel hp hok hb hf hk).1 hy
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    obtain ⟨k0, hk0⟩ := List.exists_mem_of_ne_nil _ hp.someGoal
    have h := hname hf (pass_typed hp hk0) (hboarded k0 hk0) (liftAtV "?f")
      (Or.inl ⟨by simp [boardA], liftAt_dynamic hp.domain.actions⟩)
    simpa [instAtom, boardA, floorP, passP, liftAtV, liftAt] using h
  · intro q f hqm hf
    have h := hname hf (pass_typed hp hqm) (hboarded q hqm) (originV "?p" "?f")
      (Or.inl ⟨by simp [boardA], origin_dynamic hp.domain.actions⟩)
    simpa [instAtom, boardA, floorP, passP, originV, origin] using h
  · intro q hqm
    obtain ⟨f, hd, hf⟩ := goal_destin hp hqm
    have hr : (rset (d := d) (p := p)).contains
        (instAtom boardA.params [f, q] (boardedV "?p")) = true := by
      simpa [instAtom, boardA, floorP, passP, boardedV, boarded] using hboarded q hqm
    have h := hname hf (pass_typed hp hqm) (hboarded q hqm) (boardedV "?p")
      (Or.inr ⟨Or.inl (by simp [boardA]), hr⟩)
    simpa [instAtom, boardA, floorP, passP, boardedV, boarded] using h

end Pruned

section Numbered

variable {d : Domain} {p : Problem} (hp : MiconicProblem d p)

include hp

/-- **The tables are complete on the task the planner grounds, pruning or not.** -/
theorem miconicNumbered (rel : Bool) : MiconicNumbered d p rel := by
  cases rel with
  | false => exact miconicNumbered_false hp
  | true =>
      by_cases hok : relevantOK (rawOps d p) p.goal.toArray
          (relevantSet (rawOps d p) p.goal.toArray) = true
      · exact miconicNumbered_verified hp hok
      · have heq : taskOf d p true = taskOf d p false :=
          taskOf_eq_of_unverified d p (by simpa using hok)
        obtain ⟨f1, f2, f3⟩ := miconicNumbered_false hp
        refine ⟨fun f hf => ?_, fun q f hqm hf => ?_, fun q hqm => ?_⟩
        · rw [heq]; exact f1 f hf
        · rw [heq]; exact f2 q f hqm hf
        · rw [heq]; exact f3 q hqm

/--
**Miconic's improved heuristic is admissible on the task the planner searches**,
with the relevance analysis on or off.
-/
theorem improved_admissible_of_pinned (rel : Bool) :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel))
      (ExampleHeuristics.Miconic.improved (ground d p rel)).eval :=
  improved_admissible hp (miconicNumbered hp rel)

/-- And goal-aware, and consistent. -/
theorem improved_goalAware_of_pinned (rel : Bool) :
    (ground d p rel).GoalAwareOn (Reachable (ground d p rel))
      (ExampleHeuristics.Miconic.improved (ground d p rel)).eval :=
  improved_goalAware hp (miconicNumbered hp rel)

theorem improved_consistent_of_pinned (rel : Bool) :
    (ground d p rel).ConsistentOn (Reachable (ground d p rel))
      (ExampleHeuristics.Miconic.improved (ground d p rel)).eval :=
  improved_consistent hp (miconicNumbered hp rel)

end Numbered

end Planner.Lifted.Miconic

/- -------------------------------------------------------------------------- -/
/-
A miconic domain and problem that satisfy `MiconicProblem`.

Every field is discharged by `decide`, so the hypothesis of
`Proofs/Lifted/MiconicCompile.lean` is one the parser can check and not one
nothing satisfies.
-/

namespace Planner.Lifted.Miconic

open Planner Planner.Pddl

def exDomain : Domain where
  name := "miconic"
  requirements := [":strips", ":typing"]
  types := [{ name := "passenger", parent := "object" },
            { name := "floor", parent := "object" }]
  constants := []
  predicates :=
    [ { name := "origin", params := [passP, floorP] },
      { name := "destin", params := [passP, floorP] },
      { name := "above", params := [f1P, f2P] },
      { name := "boarded", params := [passP] },
      { name := "served", params := [passP] },
      { name := "lift-at", params := [floorP] } ]
  actions := [boardA, departA, upA, downA]

def exProblem : Problem where
  name := "miconic-1"
  domainName := "miconic"
  objects :=
    [ { name := "p1", type := "passenger" },
      { name := "f1", type := "floor" },
      { name := "f2", type := "floor" } ]
  init := [origin "p1" "f1", destin "p1" "f2", { pred := "above", args := ["f1", "f2"] }, liftAt "f1"]
  goal := [served "p1"]

theorem exPinned : MiconicProblem exDomain exProblem := by
  refine ⟨⟨rfl, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    try decide
  exact { domainOK := by decide, problemOK := by decide }

/-- And so the heuristic the planner runs is admissible on that task, with the
relevance analysis on, which is how the planner runs by default. -/
theorem ex_admissible :
    (ground exDomain exProblem true).AdmissibleOn
      (Reachable (ground exDomain exProblem true))
      (ExampleHeuristics.Miconic.improved (ground exDomain exProblem true)).eval :=
  improved_admissible_of_pinned exPinned true

end Planner.Lifted.Miconic

/- -------------------------------------------------------------------------- -/
/-
Soundness of the executable certificate for the improved Miconic heuristic.
-/

namespace Planner.Lifted.Miconic

open Planner Planner.Pddl

theorem certificate_sound {d : Domain} {p : Problem}
    (hv : Validated d p)
    (h : ExampleHeuristics.Miconic.Certificate.certified d p = true) :
    MiconicProblem d p := by
  simp only [ExampleHeuristics.Miconic.Certificate.certified,
    ExampleHeuristics.Miconic.Certificate.conditions, Certificate.passes,
    List.all_cons, List.all_nil, Bool.and_eq_true] at h
  rcases h with
    ⟨hactions, hstatic, hfloorType, hpassType, hsomeFloor, hsomePass,
      hgoalShape, hgoalTyped, hgoalNodup, hfloorExact, hdestUnique,
      hdestTyped, hsomeGoal, hdestComplete, hinit⟩
  refine
    { domain := ⟨by simpa using hactions, by simpa using hstatic⟩
      floorType := by simpa using hfloorType
      passType := by simpa using hpassType
      validated := hv
      someFloor := ?_
      somePass := ?_
      goalServed := ?_
      goalTyped := ?_
      goalNodup := of_decide_eq_true hgoalNodup
      floorExact := ?_
      destinUnique := ?_
      destinTyped := ?_
      someGoal := ?_
      destinExists := ?_
      initCheck := ?_ }
  · rw [Certificate.hasObject, List.any_eq_true] at hsomeFloor
    obtain ⟨o, ho, ht⟩ := hsomeFloor
    exact ⟨o, ho, by simpa using ht⟩
  · rw [Certificate.hasObject, List.any_eq_true] at hsomePass
    obtain ⟨o, ho, ht⟩ := hsomePass
    exact ⟨o, ho, by simpa using ht⟩
  · intro a ha
    rw [ExampleHeuristics.Miconic.Certificate.goalShape, List.all_eq_true] at hgoalShape
    have hs := hgoalShape a ha
    by_cases hpred : (a.pred == "served") = true
    · rcases hargs : a.args with _ | ⟨q, rest⟩
      · simp [hpred, hargs] at hs
      · cases rest with
        | cons _ _ => simp [hpred, hargs] at hs
        | nil =>
            refine ⟨q, ?_, ?_⟩
            · exact List.mem_filterMap.mpr ⟨a, ha, by simp [hpred, hargs]⟩
            · show a = { pred := "served", args := [q] }
              cases a
              simp_all
    · simp [hpred] at hs
  · intro q hq
    rw [ExampleHeuristics.Miconic.Certificate.goalsTyped, List.all_eq_true] at hgoalTyped
    have ht := hgoalTyped q
      (by simpa [ExampleHeuristics.Miconic.Certificate.goalPass, goalPass] using hq)
    rw [Certificate.objectNamedWithType, List.any_eq_true] at ht
    obtain ⟨o, ho, hboth⟩ := ht
    rw [Bool.and_eq_true] at hboth
    exact ⟨o, ho, by simpa using hboth.1, by simpa using hboth.2⟩
  · intro o ho hs
    rw [Certificate.exactType, List.all_eq_true] at hfloorExact
    have ht := hfloorExact o ho
    simp only [Bool.or_eq_true] at ht
    rcases ht with hnot | heq
    · have hf : d.isSubtype o.type "floor" = false := by simpa using hnot
      rw [hf] at hs
      contradiction
    · simpa using heq
  · intro a ha b hb hpa hpb hhead
    rw [ExampleHeuristics.Miconic.Certificate.destinationsUnique,
      List.all_eq_true] at hdestUnique
    have hab := hdestUnique a ha
    rw [List.all_eq_true] at hab
    have heq := hab b hb
    simp [hpa, hpb, hhead] at heq
    exact heq
  · intro a ha hpred
    rw [ExampleHeuristics.Miconic.Certificate.destinationsTyped,
      List.all_eq_true] at hdestTyped
    have ht := hdestTyped a ha
    rcases hargs : a.args with _ | ⟨q, rest⟩
    · simp [hpred, hargs] at ht
    · cases rest with
      | nil => simp [hpred, hargs] at ht
      | cons f rest' =>
          cases rest' with
          | cons _ _ => simp [hpred, hargs] at ht
          | nil =>
              simp [hpred, hargs] at ht
              rw [Certificate.objectNamedWithType, List.any_eq_true] at ht
              obtain ⟨o, ho, hboth⟩ := ht
              rw [Bool.and_eq_true] at hboth
              refine ⟨o, ho, ?_, by simpa using hboth.2⟩
              have hn : o.name = f := by simpa using hboth.1
              simp [hargs, hn]
  · intro hempty
    have hempty' : ExampleHeuristics.Miconic.Certificate.goalPass p = [] := by
      simpa [ExampleHeuristics.Miconic.Certificate.goalPass, goalPass] using hempty
    rw [hempty'] at hsomeGoal
    simp at hsomeGoal
  · intro k hk
    rw [ExampleHeuristics.Miconic.Certificate.destinationsComplete,
      List.all_eq_true] at hdestComplete
    have hd := hdestComplete k
      (by simpa [ExampleHeuristics.Miconic.Certificate.goalPass, goalPass] using hk)
    rw [List.any_eq_true] at hd
    obtain ⟨a, ha, hboth⟩ := hd
    rw [Bool.and_eq_true] at hboth
    exact ⟨a, ha, by simpa using hboth.1, by simpa using hboth.2⟩
  · simpa [ExampleHeuristics.Miconic.Certificate.initInvCheck,
      ExampleHeuristics.Miconic.Certificate.liftPlaces,
      ExampleHeuristics.Miconic.Certificate.originPairs,
      initInvCheck, liftPlaces, originPairs] using hinit.1

theorem improved_goalAware_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool)
    (h : ExampleHeuristics.Miconic.Certificate.certified d p = true) :
    (ground d p rel).GoalAwareOn (Reachable (ground d p rel))
      (ExampleHeuristics.Miconic.improved (ground d p rel)).eval :=
  improved_goalAware_of_pinned (certificate_sound hv h) rel

theorem improved_consistent_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool)
    (h : ExampleHeuristics.Miconic.Certificate.certified d p = true) :
    (ground d p rel).ConsistentOn (Reachable (ground d p rel))
      (ExampleHeuristics.Miconic.improved (ground d p rel)).eval :=
  improved_consistent_of_pinned (certificate_sound hv h) rel

theorem improved_proof_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool) :
    ImprovedProof d p rel
      (ExampleHeuristics.Miconic.Certificate.certified d p)
      (ExampleHeuristics.Miconic.improved (ground d p rel)) :=
  { goalAware := improved_goalAware_of_certificate hv rel
    consistent := improved_consistent_of_certificate hv rel }

theorem improved_admissible_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool)
    (h : ExampleHeuristics.Miconic.Certificate.certified d p = true) :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel))
      (ExampleHeuristics.Miconic.improved (ground d p rel)).eval :=
  (improved_proof_of_certificate hv rel).admissible h

end Planner.Lifted.Miconic
