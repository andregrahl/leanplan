/-
Ferry's improved heuristic, proved end to end in one file.

The order below is the order the argument is built in.  The first two sections
are the schema-level proof: the improved value over the domain's own data, and
what each schema does to the counters.  The rest lifts that value to the parsed
domain, compiles it against the numbered task, and ends with the four
certificate theorems the registry depends on.

The runtime heuristic, its data, and its certificate stay under `Planner/`.  The
simple heuristic of this domain is proved in `Proofs/Domains/FerrySimple.lean`.
-/
import Proofs.Combinators
import Proofs.Certificates
import Proofs.SchemaSupport
import Proofs.LiftedHeuristic
import Proofs.StepView
import Proofs.FactTables
import Proofs.CompileSupport
import Proofs.Heuristic
import Planner.ExampleHeuristics.Ferry.Improved
import Planner.ExampleHeuristics.Ferry.Domain
import Planner.ExampleHeuristics.Ferry.Certificate

/- -------------------------------------------------------------------------- -/
/-
Ferry, improved heuristic: goal awareness and the pieces the schema-level proof
builds on.

The consistency half lives in `Schema.lean`, which states what the domain's four
schemas do to the predicates and derives the per-car count and the sailing bound
from that.  What stays here is goal awareness and the two empty-sail set lemmas.
-/

namespace Planner.ExampleHeuristics.Ferry

open Planner

/-! ### The two quantities -/

/-- Boarding, sailing and debarking still owed, per car. -/
abbrev Sc (d : Data) (s : State) : Nat := ashore d s + aboard d s
/-- The sailing bound. -/
abbrev Rc (d : Data) (s : State) : Nat := max (repositioning d s) (emptySails d s)

/-! ### Assembly -/

theorem unmetCars_empty (d : Data) (s : State)
    (hall : ∀ c ∈ d.cars, s.test c.goalFact = true) : unmetCars d s = #[] := by
  unfold unmetCars
  rw [Array.filter_eq_empty_iff]
  intro x hx
  simp [hall x hx]

theorem value_eq_zero_of_goal (d : Data) (s : State)
    (hall : ∀ c ∈ d.cars, s.test c.goalFact = true) : value d s = 0 := by
  unfold value ashore aboard repositioning emptySails waitingLocs destinations
    ashoreCars aboardCars carriedGoal waitingHere
  rw [unmetCars_empty d s hall]
  rfl

theorem improved_goalAware (t : Task)
    (hcompiled : ∀ c ∈ (compile t).cars, c.goalFact ∈ t.goal) :
    t.GoalAware (improved t).eval := by
  refine t.goalAware_of _ fun s _ hgoal => ?_
  exact value_eq_zero_of_goal _ s fun c hc => hgoal _ (hcompiled c hc)

/-! ### Discharging the empty-sail count

The empty sails are the waiting places the ferry must reach with nothing aboard —
a filter of a deduplicated list, so duplicate-free, and its length moves by the
same two shapes as any other set count.
-/

theorem emptySails_mono (d : Data) (s s' : State)
    (h : ∀ x ∈ (waitingLocs d s).filter (fun l =>
            !(destinations d s).contains l && !(ferryEmpty d s && ferryLoc d s == some l)),
        x ∈ (waitingLocs d s').filter (fun l =>
            !(destinations d s').contains l && !(ferryEmpty d s' && ferryLoc d s' == some l))) :
    emptySails d s ≤ emptySails d s' :=
  length_le_of_subset _ _ ((distinct_nodup _).filter _) h

theorem emptySails_le_succ (d : Data) (s s' : State) (a : Nat)
    (h : ∀ x ∈ (waitingLocs d s).filter (fun l =>
            !(destinations d s).contains l && !(ferryEmpty d s && ferryLoc d s == some l)),
        x ∈ (waitingLocs d s').filter (fun l =>
            !(destinations d s').contains l && !(ferryEmpty d s' && ferryLoc d s' == some l))
          ∨ x = a) :
    emptySails d s ≤ emptySails d s' + 1 :=
  length_le_succ_of_subset _ _ a ((distinct_nodup _).filter _) h

end Planner.ExampleHeuristics.Ferry

/- -------------------------------------------------------------------------- -/
/-
Ferry, stated at the schema level.

`Effect` in `Improved.lean` assumes how one action moves the per-car count and the
sailing bound.  This file assumes only what the domain's schemas do to the
predicates — where the ferry is, whether it is empty, which car is aboard, where a
car waits — and derives both counters.

`debark` splits in two, and the split is syntactic: dropping a car at its
destination discharges a car, dropping it anywhere else does not, and the two need
different bounds on the sailing term.
-/

namespace Planner.ExampleHeuristics.Ferry

open Planner

/-! ### The counters, over the whole car list -/

/-- Still to deliver. -/
def live (s : State) (c : CarInfo) : Bool := !s.test c.goalFact
/-- Still to deliver, waiting ashore. -/
def waitP (s : State) (c : CarInfo) : Bool :=
  !onBoard s c && !s.test c.goalFact
/-- Still to deliver, aboard. -/
def rideP (s : State) (c : CarInfo) : Bool := onBoard s c && !s.test c.goalFact

theorem ashore_eq (d : Data) (s : State) :
    ashore d s = 3 * (d.cars.toList.filter (waitP s)).length := by
  unfold ashore ashoreCars unmetCars waitP
  rw [← Array.length_toList, Array.toList_filter, Array.toList_filter, List.filter_filter]

theorem aboard_eq (d : Data) (s : State) :
    aboard d s = (d.cars.toList.map fun c =>
      if rideP s c then (if ferryLoc d s == some c.goalLoc then 1 else 2) else 0).sum := by
  unfold aboard aboardCars unmetCars rideP
  rw [← Array.foldl_toList, foldl_add_eq_sum, Array.toList_filter, Array.toList_filter,
    List.filter_filter, ← sum_filter_eq_ite]
  simp

theorem waitingLocs_eq (d : Data) (s : State) :
    waitingLocs d s = distinct ((d.cars.toList.filter (waitP s)).filterMap (fun c => carLoc s c)) := by
  unfold waitingLocs ashoreCars unmetCars waitP
  rw [Array.toList_filter, Array.toList_filter, List.filter_filter]

theorem destinations_eq (d : Data) (s : State) :
    destinations d s = distinct ((d.cars.toList.filter (live s)).map (·.goalLoc)) := by
  unfold destinations unmetCars live
  rw [Array.toList_filter]

/-! ### Membership in the two location sets -/

theorem mem_waitingLocs {d : Data} {s : State} {x : Nat} :
    x ∈ waitingLocs d s ↔ ∃ c ∈ d.cars, waitP s c = true ∧ carLoc s c = some x := by
  rw [waitingLocs_eq, mem_distinct, List.mem_filterMap]
  constructor
  · rintro ⟨c, hc, hcx⟩
    rw [List.mem_filter] at hc
    exact ⟨c, by simpa using hc.1, hc.2, hcx⟩
  · rintro ⟨c, hc, hw, hcx⟩
    exact ⟨c, by rw [List.mem_filter]; exact ⟨by simpa using hc, hw⟩, hcx⟩

theorem mem_destinations {d : Data} {s : State} {x : Nat} :
    x ∈ destinations d s ↔ ∃ c ∈ d.cars, live s c = true ∧ c.goalLoc = x := by
  rw [destinations_eq, mem_distinct, List.mem_map]
  constructor
  · rintro ⟨c, hc, hcx⟩
    rw [List.mem_filter] at hc
    exact ⟨c, by simpa using hc.1, hc.2, hcx⟩
  · rintro ⟨c, hc, hl, hcx⟩
    exact ⟨c, by rw [List.mem_filter]; exact ⟨by simpa using hc, hl⟩, hcx⟩

/-! ### What each schema does -/

/-- `board`: the empty ferry at `l` takes on a car waiting there. -/
structure BoardStep (d : Data) (s s' : State) (l : Nat) (q : CarInfo) : Prop where
  memQ : q ∈ d.cars
  ferryAt : ferryLoc d s = some l
  ferryAt' : ferryLoc d s' = some l
  emptyBefore : ferryEmpty d s = true
  notEmptyAfter : ferryEmpty d s' = false
  carAt : carLoc s q = some l
  carGone : carLoc s' q = none
  onQ : onBoard s q = false
  onQ' : onBoard s' q = true
  unmetQ : s.test q.goalFact = false
  /-- A car waiting where it is meant to end up would already be delivered. -/
  goalNe : q.goalLoc ≠ l
  frameServed : ∀ c ∈ d.cars, s'.test c.goalFact = s.test c.goalFact
  frameOn : ∀ c ∈ d.cars, c ≠ q → onBoard s' c = onBoard s c
  frameLoc : ∀ c ∈ d.cars, c ≠ q → carLoc s' c = carLoc s c

/-- `debark` at the car's own destination: the car is delivered. -/
structure DebarkGoalStep (d : Data) (s s' : State) (l : Nat) (q : CarInfo) : Prop where
  memQ : q ∈ d.cars
  ferryAt : ferryLoc d s = some l
  ferryAt' : ferryLoc d s' = some l
  notEmptyBefore : ferryEmpty d s = false
  emptyAfter : ferryEmpty d s' = true
  onQ : onBoard s q = true
  onQ' : onBoard s' q = false
  unmetQ : s.test q.goalFact = false
  servedQ' : s'.test q.goalFact = true
  goalEq : q.goalLoc = l
  /-- The ferry carries one car at a time. -/
  aloneQ : ∀ c ∈ d.cars, onBoard s c = true → c = q
  frameServed : ∀ c ∈ d.cars, c ≠ q → s'.test c.goalFact = s.test c.goalFact
  frameOn : ∀ c ∈ d.cars, c ≠ q → onBoard s' c = onBoard s c
  frameLoc : ∀ c ∈ d.cars, c ≠ q → carLoc s' c = carLoc s c

/-- `debark` anywhere else: the car goes ashore, still to deliver. -/
structure DebarkAwayStep (d : Data) (s s' : State) (l : Nat) (q : CarInfo) : Prop where
  memQ : q ∈ d.cars
  ferryAt : ferryLoc d s = some l
  ferryAt' : ferryLoc d s' = some l
  notEmptyBefore : ferryEmpty d s = false
  emptyAfter : ferryEmpty d s' = true
  onQ : onBoard s q = true
  onQ' : onBoard s' q = false
  carAt' : carLoc s' q = some l
  unmetQ : s.test q.goalFact = false
  unmetQ' : s'.test q.goalFact = false
  goalNe : q.goalLoc ≠ l
  aloneQ : ∀ c ∈ d.cars, onBoard s c = true → c = q
  frameServed : ∀ c ∈ d.cars, c ≠ q → s'.test c.goalFact = s.test c.goalFact
  frameOn : ∀ c ∈ d.cars, c ≠ q → onBoard s' c = onBoard s c
  frameLoc : ∀ c ∈ d.cars, c ≠ q → carLoc s' c = carLoc s c

/-- `sail`: only the ferry moves. -/
structure SailStep (d : Data) (s s' : State) (l2 : Nat) : Prop where
  ferryAt' : ferryLoc d s' = some l2
  emptySame : ferryEmpty d s' = ferryEmpty d s
  /-- An empty ferry carries nothing. -/
  emptyNoCar : ferryEmpty d s = true → ∀ c ∈ d.cars, onBoard s c = false
  aloneAboard : ∀ c₁ ∈ d.cars, ∀ c₂ ∈ d.cars,
    onBoard s c₁ = true → onBoard s c₂ = true → c₁ = c₂
  frameServed : ∀ c ∈ d.cars, s'.test c.goalFact = s.test c.goalFact
  frameOn : ∀ c ∈ d.cars, onBoard s' c = onBoard s c
  frameLoc : ∀ c ∈ d.cars, carLoc s' c = carLoc s c

/-- One action of the domain. -/
inductive SchemaStep (d : Data) (s s' : State) : Prop
  | board (l : Nat) (q : CarInfo) (h : BoardStep d s s' l q)
  | debarkGoal (l : Nat) (q : CarInfo) (h : DebarkGoalStep d s s' l q)
  | debarkAway (l : Nat) (q : CarInfo) (h : DebarkAwayStep d s s' l q)
  | sail (l2 : Nat) (h : SailStep d s s' l2)

theorem ashoreCars_toList (d : Data) (s : State) :
    (ashoreCars d s).toList = d.cars.toList.filter (waitP s) := by
  unfold ashoreCars unmetCars waitP
  rw [Array.toList_filter, Array.toList_filter, List.filter_filter]

/-! ### The per-car count, derived from the shapes -/

namespace BoardStep
variable {d : Data} {s s' : State} {l : Nat} {q : CarInfo}

theorem wait_count (h : BoardStep d s s' l q) (hnd : d.cars.toList.Nodup) :
    (d.cars.toList.filter (waitP s')).length + 1
      = (d.cars.toList.filter (waitP s)).length := by
  refine length_filter_erase_one _ (waitP s) (waitP s') q (by simpa using h.memQ) hnd ?_ ?_ ?_
  · simp [waitP, h.onQ, h.carAt, h.unmetQ]
  · simp [waitP, h.onQ']
  · intro y hy hne
    have hm : y ∈ d.cars := by simpa using hy
    simp [waitP, h.frameOn y hm hne, h.frameLoc y hm hne, h.frameServed y hm]

theorem aboard_shift (h : BoardStep d s s' l q) (hnd : d.cars.toList.Nodup) :
    aboard d s + 2 = aboard d s' := by
  rw [aboard_eq, aboard_eq]
  refine sum_map_shift _ _ _ q 2 (by simpa using h.memQ) hnd ?_ ?_
  · have hlive : s'.test q.goalFact = false := by
      rw [h.frameServed q h.memQ]; exact h.unmetQ
    simp [rideP, h.onQ, h.onQ', h.unmetQ, hlive, h.ferryAt', Ne.symm h.goalNe]
  · intro y hy hne
    have hm : y ∈ d.cars := by simpa using hy
    simp [rideP, h.frameOn y hm hne, h.frameServed y hm, h.ferryAt, h.ferryAt']

theorem Sc_drop (h : BoardStep d s s' l q) (hnd : d.cars.toList.Nodup) :
    Sc d s' + 1 = Sc d s := by
  show ashore d s' + aboard d s' + 1 = ashore d s + aboard d s
  rw [ashore_eq, ashore_eq]
  have h1 := h.wait_count hnd
  have h2 := h.aboard_shift hnd
  omega

end BoardStep

namespace DebarkGoalStep
variable {d : Data} {s s' : State} {l : Nat} {q : CarInfo}

theorem wait_count (h : DebarkGoalStep d s s' l q) :
    (d.cars.toList.filter (waitP s')).length = (d.cars.toList.filter (waitP s)).length := by
  refine length_filter_congr _ (waitP s') (waitP s) ?_
  intro y hy
  have hm : y ∈ d.cars := by simpa using hy
  by_cases hne : y = q
  · subst hne; simp [waitP, h.onQ, h.servedQ']
  · simp [waitP, h.frameOn y hm hne, h.frameLoc y hm hne, h.frameServed y hm hne]

theorem aboard_shift (h : DebarkGoalStep d s s' l q) (hnd : d.cars.toList.Nodup) :
    aboard d s' + 1 = aboard d s := by
  rw [aboard_eq, aboard_eq]
  refine sum_map_shift _ _ _ q 1 (by simpa using h.memQ) hnd ?_ ?_
  · simp [rideP, h.onQ, h.onQ', h.unmetQ, h.servedQ', h.ferryAt, h.goalEq]
  · intro y hy hne
    have hm : y ∈ d.cars := by simpa using hy
    simp [rideP, h.frameOn y hm hne, h.frameServed y hm hne, h.ferryAt, h.ferryAt']

theorem Sc_drop (h : DebarkGoalStep d s s' l q) (hnd : d.cars.toList.Nodup) :
    Sc d s' + 1 = Sc d s := by
  show ashore d s' + aboard d s' + 1 = ashore d s + aboard d s
  rw [ashore_eq, ashore_eq]
  have h1 := h.wait_count
  have h2 := h.aboard_shift hnd
  omega

end DebarkGoalStep

namespace DebarkAwayStep
variable {d : Data} {s s' : State} {l : Nat} {q : CarInfo}

theorem wait_count (h : DebarkAwayStep d s s' l q) (hnd : d.cars.toList.Nodup) :
    (d.cars.toList.filter (waitP s)).length + 1
      = (d.cars.toList.filter (waitP s')).length := by
  refine length_filter_erase_one _ (waitP s') (waitP s) q (by simpa using h.memQ) hnd ?_ ?_ ?_
  · simp [waitP, h.onQ', h.carAt', h.unmetQ']
  · simp [waitP, h.onQ]
  · intro y hy hne
    have hm : y ∈ d.cars := by simpa using hy
    simp [waitP, h.frameOn y hm hne, h.frameLoc y hm hne, h.frameServed y hm hne]

theorem aboard_shift (h : DebarkAwayStep d s s' l q) (hnd : d.cars.toList.Nodup) :
    aboard d s' + 2 = aboard d s := by
  rw [aboard_eq, aboard_eq]
  refine sum_map_shift _ _ _ q 2 (by simpa using h.memQ) hnd ?_ ?_
  · simp [rideP, h.onQ, h.onQ', h.unmetQ, h.unmetQ', h.ferryAt, Ne.symm h.goalNe]
  · intro y hy hne
    have hm : y ∈ d.cars := by simpa using hy
    simp [rideP, h.frameOn y hm hne, h.frameServed y hm hne, h.ferryAt, h.ferryAt']

theorem Sc_rise (h : DebarkAwayStep d s s' l q) (hnd : d.cars.toList.Nodup) :
    Sc d s ≤ Sc d s' := by
  show ashore d s + aboard d s ≤ ashore d s' + aboard d s'
  rw [ashore_eq, ashore_eq]
  have h1 := h.wait_count hnd
  have h2 := h.aboard_shift hnd
  omega

end DebarkAwayStep

namespace SailStep
variable {d : Data} {s s' : State} {l2 : Nat}

theorem wait_count (h : SailStep d s s' l2) :
    (d.cars.toList.filter (waitP s')).length = (d.cars.toList.filter (waitP s)).length := by
  refine length_filter_congr _ (waitP s') (waitP s) ?_
  intro y hy
  have hm : y ∈ d.cars := by simpa using hy
  simp [waitP, h.frameOn y hm, h.frameLoc y hm, h.frameServed y hm]

theorem aboard_le (h : SailStep d s s' l2) (hnd : d.cars.toList.Nodup) :
    aboard d s ≤ aboard d s' + 1 := by
  rw [aboard_eq, aboard_eq]
  by_cases hex : ∃ q ∈ d.cars, rideP s q = true
  · obtain ⟨q, hq, hrq⟩ := hex
    refine sum_map_le_succ _ _ _ q hnd ?_ ?_
    · have : rideP s' q = true := by
        simpa [rideP, h.frameOn q hq, h.frameServed q hq] using hrq
      simp only [hrq, this, if_true]
      split <;> split <;> omega
    · intro y hy hne
      have hm : y ∈ d.cars := by simpa using hy
      have hoff : rideP s y = false := by
        by_contra hcon
        have hry : rideP s y = true := by simpa using hcon
        have h1 : onBoard s y = true := by
          simpa [rideP] using (by simpa [rideP, Bool.and_eq_true] using hry : onBoard s y = true ∧ _).1
        have h2 : onBoard s q = true := by
          simpa [rideP] using (by simpa [rideP, Bool.and_eq_true] using hrq : onBoard s q = true ∧ _).1
        exact hne (h.aloneAboard y hm q hq h1 h2)
      simp [hoff]
  · push_neg at hex
    have hall : ∀ y ∈ d.cars.toList, rideP s y = false := by
      intro y hy
      have := hex y (by simpa using hy)
      simpa using this
    have h1 : (d.cars.toList.map fun c =>
        if rideP s c then (if ferryLoc d s == some c.goalLoc then 1 else 2) else 0).sum = 0 := by
      have : ∀ y ∈ d.cars.toList,
          (if rideP s y then (if ferryLoc d s == some y.goalLoc then 1 else 2) else 0) = 0 :=
        fun y hy => by simp [hall y hy]
      rw [List.map_congr_left this]; simp
    omega

theorem aboard_zero (h : SailStep d s s' l2) (hempty : ferryEmpty d s = true) :
    aboard d s = 0 ∧ aboard d s' = 0 := by
  have hoff : ∀ c ∈ d.cars, onBoard s c = false := h.emptyNoCar hempty
  have key : ∀ t : State, (∀ c ∈ d.cars, rideP t c = false) →
      (d.cars.toList.map fun c =>
        if rideP t c then (if ferryLoc d t == some c.goalLoc then 1 else 2) else 0).sum = 0 := by
    intro t ht
    have hmap : (d.cars.toList.map fun c =>
        if rideP t c then (if ferryLoc d t == some c.goalLoc then 1 else 2) else 0)
        = d.cars.toList.map fun _ => 0 := by
      refine List.map_congr_left ?_
      intro y hy
      simp [ht y (by simpa using hy)]
    rw [hmap]
    simp
  refine ⟨?_, ?_⟩
  · rw [aboard_eq]; exact key s fun c hc => by simp [rideP, hoff c hc]
  · rw [aboard_eq]; exact key s' fun c hc => by simp [rideP, h.frameOn c hc, hoff c hc]

end SailStep

/-! ### The sailing bound, derived from the shapes -/

theorem repositioning_le_one (d : Data) (s : State) : repositioning d s ≤ 1 := by
  unfold repositioning
  repeat' split
  all_goals omega

theorem destinations_congr {d : Data} {s s' : State}
    (hf : ∀ c ∈ d.cars, s'.test c.goalFact = s.test c.goalFact) :
    destinations d s' = destinations d s := by
  rw [destinations_eq, destinations_eq]
  congr 2
  refine List.filter_congr ?_
  intro c hc
  simp [live, hf c (by simpa using hc)]

theorem waitingLocs_congr {d : Data} {s s' : State}
    (hs : ∀ c ∈ d.cars, s'.test c.goalFact = s.test c.goalFact)
    (ho : ∀ c ∈ d.cars, onBoard s' c = onBoard s c)
    (hl : ∀ c ∈ d.cars, carLoc s' c = carLoc s c) :
    waitingLocs d s' = waitingLocs d s := by
  rw [waitingLocs_eq, waitingLocs_eq]
  congr 1
  have hfil : d.cars.toList.filter (waitP s') = d.cars.toList.filter (waitP s) := by
    refine List.filter_congr ?_
    intro c hc
    have hm : c ∈ d.cars := by simpa using hc
    simp [waitP, hs c hm, ho c hm, hl c hm]
  rw [hfil]
  refine List.filterMap_congr ?_
  intro c hc
  rw [List.mem_filter] at hc
  exact hl c (by simpa using hc.1)

namespace BoardStep
variable {d : Data} {s s' : State} {l : Nat} {q : CarInfo}

theorem rep_zero (h : BoardStep d s s' l q) : repositioning d s = 0 := by
  have hq : q ∈ ashoreCars d s := by
    simp [ashoreCars, unmetCars, h.memQ, h.unmetQ, h.onQ, h.carAt]
  have hne : (ashoreCars d s).isEmpty = false := by
    by_contra hcon
    have hemp : (ashoreCars d s) = #[] := by
      have : (ashoreCars d s).isEmpty = true := by simpa using hcon
      simpa [Array.isEmpty_iff] using this
    rw [hemp] at hq
    simp at hq
  have hwl : l ∈ waitingLocs d s := by
    rw [mem_waitingLocs]
    exact ⟨q, h.memQ, by simp [waitP, h.onQ, h.carAt, h.unmetQ], h.carAt⟩
  have hwh : waitingHere d s = true := by
    simp [waitingHere, h.ferryAt]
    exact hwl
  simp [repositioning, hne, h.emptyBefore, hwh]

theorem emptySails_le (h : BoardStep d s s' l q) : emptySails d s ≤ emptySails d s' := by
  refine emptySails_mono d s s' ?_
  intro x hx
  rw [List.mem_filter] at hx ⊢
  obtain ⟨hxw, hxp⟩ := hx
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hxp
  obtain ⟨hxd, hxf⟩ := hxp
  have hxl : x ≠ l := by
    intro hcon
    subst hcon
    simp [h.emptyBefore, h.ferryAt] at hxf
  refine ⟨?_, ?_⟩
  · rw [mem_waitingLocs] at hxw ⊢
    obtain ⟨c, hc, hw, hcx⟩ := hxw
    have hcq : c ≠ q := by
      intro hcon; subst hcon; rw [h.carAt] at hcx; exact hxl (Option.some.inj hcx).symm
    refine ⟨c, hc, ?_, ?_⟩
    · simpa [waitP, h.frameOn c hc hcq, h.frameLoc c hc hcq, h.frameServed c hc] using hw
    · rw [h.frameLoc c hc hcq]; exact hcx
  · simp only [Bool.and_eq_true, Bool.not_eq_true', destinations_congr h.frameServed, hxd,
      h.notEmptyAfter]
    simp

theorem Rc_le (h : BoardStep d s s' l q) : Rc d s ≤ Rc d s' := by
  show max (repositioning d s) (emptySails d s) ≤ max (repositioning d s') (emptySails d s')
  have h1 := h.rep_zero
  have h2 := h.emptySails_le
  omega

end BoardStep

namespace DebarkGoalStep
variable {d : Data} {s s' : State} {l : Nat} {q : CarInfo}

theorem waiting_eq (h : DebarkGoalStep d s s' l q) : waitingLocs d s' = waitingLocs d s := by
  rw [waitingLocs_eq, waitingLocs_eq]
  have hfil : d.cars.toList.filter (waitP s') = d.cars.toList.filter (waitP s) := by
    refine List.filter_congr ?_
    intro c hc
    have hm : c ∈ d.cars := by simpa using hc
    by_cases hne : c = q
    · subst hne; simp [waitP, h.onQ, h.servedQ']
    · simp [waitP, h.frameServed c hm hne, h.frameOn c hm hne, h.frameLoc c hm hne]
  congr 1
  rw [hfil]
  refine List.filterMap_congr ?_
  intro c hc
  rw [List.mem_filter] at hc
  have hm : c ∈ d.cars := by simpa using hc.1
  by_cases hne : c = q
  · subst hne; simp [waitP, h.onQ] at hc
  · exact h.frameLoc c hm hne

theorem dest_subset (h : DebarkGoalStep d s s' l q) {x : Nat}
    (hx : x ∈ destinations d s') : x ∈ destinations d s := by
  rw [mem_destinations] at hx ⊢
  obtain ⟨c, hc, hl, hcx⟩ := hx
  refine ⟨c, hc, ?_, hcx⟩
  by_cases hne : c = q
  · subst hne; simp [live, h.servedQ'] at hl
  · simpa [live, h.frameServed c hc hne] using hl

theorem l_mem_dest (h : DebarkGoalStep d s s' l q) : l ∈ destinations d s := by
  rw [mem_destinations]
  exact ⟨q, h.memQ, by simp [live, h.unmetQ], h.goalEq⟩

theorem emptySails_le (h : DebarkGoalStep d s s' l q) :
    emptySails d s ≤ emptySails d s' := by
  refine emptySails_mono d s s' ?_
  intro x hx
  rw [List.mem_filter] at hx ⊢
  obtain ⟨hxw, hxp⟩ := hx
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hxp
  obtain ⟨hxd, -⟩ := hxp
  have hxdm : x ∉ destinations d s := by simpa using hxd
  have hxl : x ≠ l := by rintro rfl; exact hxdm h.l_mem_dest
  refine ⟨by rw [h.waiting_eq]; exact hxw, ?_⟩
  simp only [Bool.and_eq_true, Bool.not_eq_true', h.emptyAfter, h.ferryAt']
  refine ⟨?_, ?_⟩
  · simpa using fun hc => hxdm (h.dest_subset hc)
  · simp [Ne.symm hxl]

theorem carried (h : DebarkGoalStep d s s' l q) (hnd : d.cars.toList.Nodup) :
    carriedGoal d s = some l := by
  have hmem : q ∈ (unmetCars d s).toList := by
    simp [unmetCars, h.memQ, h.unmetQ]
  have hnodup : (unmetCars d s).toList.Nodup := by
    simp only [unmetCars, Array.toList_filter]
    exact hnd.filter _
  have huniq : ∀ y ∈ (unmetCars d s).toList, onBoard s y = true → y = q := by
    intro y hy hoy
    have : y ∈ d.cars := by
      simp only [unmetCars, Array.toList_filter, List.mem_filter] at hy
      simpa using hy.1
    exact h.aloneQ y this hoy
  have hlist : (aboardCars d s).toList = [q] := by
    show ((unmetCars d s).filter (fun c => onBoard s c)).toList = [q]
    rw [Array.toList_filter]
    exact filter_eq_singleton q (fun c => onBoard s c) h.onQ _ hmem hnodup huniq
  have harr : aboardCars d s = #[q] := Array.toList_inj.mp (by simpa using hlist)
  simp [carriedGoal, harr, h.goalEq]

theorem Rc_le (h : DebarkGoalStep d s s' l q) (hnd : d.cars.toList.Nodup) :
    Rc d s ≤ Rc d s' := by
  show max (repositioning d s) (emptySails d s) ≤ max (repositioning d s') (emptySails d s')
  have hes := h.emptySails_le
  have hrep : repositioning d s ≤ repositioning d s' := by
    have hwaitP : ∀ c ∈ d.cars.toList, waitP s' c = waitP s c := by
      intro c hc
      have hm : c ∈ d.cars := by simpa using hc
      by_cases hne : c = q
      · subst hne; simp [waitP, h.onQ, h.servedQ']
      · simp [waitP, h.frameServed c hm hne, h.frameOn c hm hne, h.frameLoc c hm hne]
    have hash : ashoreCars d s' = ashoreCars d s :=
      Array.toList_inj.mp (by
        rw [ashoreCars_toList, ashoreCars_toList, List.filter_congr hwaitP])
    by_cases hemp : (ashoreCars d s).isEmpty
    · simp [repositioning, hemp]
    · by_cases hw : (waitingLocs d s).contains l = true
      · have hwh : waitingHere d s' = true := by
          simp only [waitingHere, h.ferryAt', h.waiting_eq]; exact hw
        have hmem : l ∈ waitingLocs d s := by simpa using hw
        simp [repositioning, hash, hemp, h.notEmptyBefore, h.emptyAfter,
          h.carried hnd, hwh, hmem]
      · have hwf : (waitingLocs d s).contains l = false := by simpa using hw
        have hwh : waitingHere d s' = false := by
          simp only [waitingHere, h.ferryAt', h.waiting_eq]; exact hwf
        have hnmem : l ∉ waitingLocs d s := by simpa using hw
        simp [repositioning, hash, hemp, h.notEmptyBefore, h.emptyAfter,
          h.carried hnd, hwh, hnmem]
  omega

end DebarkGoalStep

namespace DebarkAwayStep
variable {d : Data} {s s' : State} {l : Nat} {q : CarInfo}

theorem live_congr (h : DebarkAwayStep d s s' l q) :
    ∀ c ∈ d.cars, s'.test c.goalFact = s.test c.goalFact := by
  intro c hc
  by_cases hne : c = q
  · subst hne; rw [h.unmetQ', h.unmetQ]
  · exact h.frameServed c hc hne

theorem emptySails_le (h : DebarkAwayStep d s s' l q) :
    emptySails d s ≤ emptySails d s' + 1 := by
  refine emptySails_le_succ d s s' l ?_
  intro x hx
  rw [List.mem_filter] at hx
  obtain ⟨hxw, hxp⟩ := hx
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hxp
  obtain ⟨hxd, -⟩ := hxp
  by_cases hxl : x = l
  · exact Or.inr hxl
  · refine Or.inl ?_
    rw [List.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [mem_waitingLocs] at hxw ⊢
      obtain ⟨c, hc, hw, hcx⟩ := hxw
      have hcq : c ≠ q := by
        rintro rfl; simp [waitP, h.onQ] at hw
      exact ⟨c, hc, by
        simpa [waitP, h.frameOn c hc hcq, h.frameLoc c hc hcq,
          h.frameServed c hc hcq] using hw,
        by rw [h.frameLoc c hc hcq]; exact hcx⟩
    · simp only [Bool.and_eq_true, Bool.not_eq_true', destinations_congr h.live_congr,
        hxd, h.emptyAfter, h.ferryAt']
      exact ⟨trivial, by simp [Ne.symm hxl]⟩

theorem Rc_le (h : DebarkAwayStep d s s' l q) : Rc d s ≤ Rc d s' + 1 := by
  show max (repositioning d s) (emptySails d s) ≤ max (repositioning d s') (emptySails d s') + 1
  have h1 := repositioning_le_one d s
  have h2 := h.emptySails_le
  omega

end DebarkAwayStep

namespace SailStep
variable {d : Data} {s s' : State} {l2 : Nat}

theorem waiting_eq (h : SailStep d s s' l2) : waitingLocs d s' = waitingLocs d s :=
  waitingLocs_congr h.frameServed h.frameOn h.frameLoc

theorem ashore_eq' (h : SailStep d s s' l2) : ashoreCars d s' = ashoreCars d s :=
  Array.toList_inj.mp (by
    rw [ashoreCars_toList, ashoreCars_toList]
    refine List.filter_congr ?_
    intro c hc
    have hm : c ∈ d.cars := by simpa using hc
    simp [waitP, h.frameServed c hm, h.frameOn c hm, h.frameLoc c hm])

theorem aboardCars_eq (h : SailStep d s s' l2) : aboardCars d s' = aboardCars d s := by
  show (unmetCars d s').filter _ = (unmetCars d s).filter _
  have h1 : unmetCars d s' = unmetCars d s :=
    array_filter_congr _ _ _ fun c hc => by simp [h.frameServed c hc]
  rw [h1]
  refine array_filter_congr _ _ _ ?_
  intro c hc
  have hm : c ∈ d.cars := by
    simp only [unmetCars, Array.mem_filter] at hc; exact hc.1
  exact h.frameOn c hm

theorem Rc_eq_of_loaded (h : SailStep d s s' l2) (hne : ferryEmpty d s = false) :
    Rc d s' = Rc d s := by
  have hfe : ferryEmpty d s' = false := by rw [h.emptySame]; exact hne
  have hrep : repositioning d s' = repositioning d s := by
    simp [repositioning, h.ashore_eq', hfe, hne, carriedGoal, h.aboardCars_eq, h.waiting_eq]
  have hes : emptySails d s' = emptySails d s := by
    unfold emptySails
    rw [h.waiting_eq]
    congr 1
    refine List.filter_congr ?_
    intro x _
    simp [destinations_congr h.frameServed, hfe, hne]
  show max (repositioning d s') (emptySails d s') = max (repositioning d s) (emptySails d s)
  rw [hrep, hes]

theorem Rc_le_of_empty (h : SailStep d s s' l2) (hemp : ferryEmpty d s = true) :
    Rc d s ≤ Rc d s' + 1 := by
  have hfe : ferryEmpty d s' = true := by rw [h.emptySame]; exact hemp
  have hes : emptySails d s ≤ emptySails d s' + 1 := by
    refine emptySails_le_succ d s s' l2 ?_
    intro x hx
    rw [List.mem_filter] at hx
    obtain ⟨hxw, hxp⟩ := hx
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hxp
    obtain ⟨hxd, -⟩ := hxp
    by_cases hxl : x = l2
    · exact Or.inr hxl
    · refine Or.inl ?_
      rw [List.mem_filter]
      refine ⟨by rw [h.waiting_eq]; exact hxw, ?_⟩
      simp only [Bool.and_eq_true, Bool.not_eq_true',
        destinations_congr h.frameServed, hxd, hfe, h.ferryAt']
      exact ⟨trivial, by simp [Ne.symm hxl]⟩
  have h1 := repositioning_le_one d s
  show max (repositioning d s) (emptySails d s) ≤ max (repositioning d s') (emptySails d s') + 1
  omega

theorem Sc_le (h : SailStep d s s' l2) (hnd : d.cars.toList.Nodup) :
    Sc d s ≤ Sc d s' + 1 := by
  show ashore d s + aboard d s ≤ ashore d s' + aboard d s' + 1
  rw [ashore_eq, ashore_eq]
  have h1 := h.wait_count
  have h2 := h.aboard_le hnd
  omega

theorem Sc_eq_of_empty (h : SailStep d s s' l2) (hemp : ferryEmpty d s = true) :
    Sc d s = Sc d s' := by
  show ashore d s + aboard d s = ashore d s' + aboard d s'
  rw [ashore_eq, ashore_eq]
  obtain ⟨ha, ha'⟩ := h.aboard_zero hemp
  have h1 := h.wait_count
  omega

end SailStep

/-! ### The consistency step, with nothing about the counters assumed -/

theorem value_step_of_schema (d : Data) (s s' : State) (hnd : d.cars.toList.Nodup)
    (he : SchemaStep d s s') (cost : Nat) (hcost : 1 ≤ cost) :
    value d s ≤ cost + value d s' := by
  show Sc d s + Rc d s ≤ cost + (Sc d s' + Rc d s')
  cases he with
  | board l q h =>
      have h1 := h.Sc_drop hnd
      have h2 := h.Rc_le
      omega
  | debarkGoal l q h =>
      have h1 := h.Sc_drop hnd
      have h2 := h.Rc_le hnd
      omega
  | debarkAway l q h =>
      have h1 := h.Sc_rise hnd
      have h2 := h.Rc_le
      omega
  | sail l2 h =>
      by_cases hemp : ferryEmpty d s = true
      · have h1 := h.Sc_eq_of_empty hemp
        have h2 := h.Rc_le_of_empty hemp
        omega
      · have hne : ferryEmpty d s = false := by simpa using hemp
        have h1 := h.Sc_le hnd
        have h2 := h.Rc_eq_of_loaded hne
        omega

/-- Zero at every goal state, assuming only what the schemas do. -/
theorem improved_goalAware_of_schema (t : Task)
    (hcompiled : ∀ c ∈ (compile t).cars, c.goalFact ∈ t.goal) :
    t.GoalAware (improved t).eval := improved_goalAware t hcompiled

/-- And never falls by more than one action costs. -/
theorem improved_consistent_of_schema (t : Task)
    (hnd : (compile t).cars.toList.Nodup)
    (hstep : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      SchemaStep (compile t) s (op.apply s))
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost) :
    t.Consistent (improved t).eval :=
  t.consistent_of_ops _ fun op hop s hs happ =>
    value_step_of_schema _ s _ hnd (hstep op hop s hs happ) op.cost (hcost op hop)

/-- Never overestimates, assuming only that every operator is one of the schemas. -/
theorem improved_admissible_of_schema (t : Task)
    (hcompiled : ∀ c ∈ (compile t).cars, c.goalFact ∈ t.goal)
    (hnd : (compile t).cars.toList.Nodup)
    (hstep : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      SchemaStep (compile t) s (op.apply s))
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost) :
    t.Admissible (improved t).eval :=
  t.admissible _ (improved_goalAware_of_schema t hcompiled)
    (improved_consistent_of_schema t hnd hstep hcost)

end Planner.ExampleHeuristics.Ferry

/- -------------------------------------------------------------------------- -/
/-
Ferry's improved heuristic, at the lifted level.

The same shape as miconic: a per-car count of the boardings, sailings and
debarkings still owed, plus a bound on the sailings, and nothing in the file
mentions a `Fact` or a `State`.

  * a car still ashore owes a `board`, a loaded `sail` and a `debark` — three;
  * one already aboard owes a `sail` and a `debark`, or just a `debark` if the
    ferry is already where it is going;
  * and every place a car waits, other than a destination and other than where
    an empty ferry already stands, costs a sail the ferry must make empty.
-/

namespace Planner.Lifted.Ferry

open Planner Planner.Pddl

/-! ### The domain's atoms -/

def atC (car loc : Name) : GroundAtom := { pred := "at", args := [car, loc] }
def atFerry (loc : Name) : GroundAtom := { pred := "at-ferry", args := [loc] }
def notAtFerry (loc : Name) : GroundAtom := { pred := "not-at-ferry", args := [loc] }
def onC (car : Name) : GroundAtom := { pred := "on", args := [car] }
def emptyFerry : GroundAtom := { pred := "empty-ferry", args := [] }

/-- What the problem fixes: the cars to deliver, the places, and each car's
destination. -/
structure Cfg where
  cars : List Name
  locations : List Name
  dest : Name → Option Name

/-! ### Reading the state -/

/-- The car has arrived. -/
def delivered (c : Cfg) (σ : AtomState) (q : Name) : Bool :=
  match c.dest q with
  | some g => σ (atC q g)
  | none => true

/-- Where the ferry is. -/
def ferryLoc (c : Cfg) (σ : AtomState) : Option Name :=
  c.locations.find? fun l => σ (atFerry l)

/-- Where a car stands, if it is ashore. -/
def carLoc (c : Cfg) (σ : AtomState) (q : Name) : Option Name :=
  c.locations.find? fun l => σ (atC q l)

/-- Still to deliver and still ashore. -/
def ashore (c : Cfg) (σ : AtomState) : List Name :=
  c.cars.filter fun q => !delivered c σ q && !σ (onC q)

/-- Still to deliver and aboard. -/
def aboard (c : Cfg) (σ : AtomState) : List Name :=
  c.cars.filter fun q => !delivered c σ q && σ (onC q)

/-- Three actions for a car ashore, two for one aboard, one if it is already
where it is going. -/
def carCost (c : Cfg) (σ : AtomState) (q : Name) : Nat :=
  if delivered c σ q then 0
  else if σ (onC q) then (if ferryLoc c σ = c.dest q then 1 else 2)
  else 3

/-- The boarding, sailing and debarking still owed. -/
def load (c : Cfg) (σ : AtomState) : Nat := (c.cars.map (carCost c σ)).sum

/-- The places a car still waits at. -/
def waitingLocs (c : Cfg) (σ : AtomState) : List Name :=
  ((ashore c σ).filterMap fun q => carLoc c σ q).dedup

/-- The places a car still has to reach. -/
def destinations (c : Cfg) (σ : AtomState) : List Name :=
  ((c.cars.filter fun q => !delivered c σ q).filterMap fun q => c.dest q).dedup

/-- Places the ferry must reach empty, and can only reach by sailing empty. -/
def emptySails (c : Cfg) (σ : AtomState) : Nat :=
  ((waitingLocs c σ).filter fun l =>
    !(destinations c σ).contains l && !(σ emptyFerry && ferryLoc c σ = some l)).length

/-- Does a car wait where the ferry stands? -/
def waitingHere (c : Cfg) (σ : AtomState) : Bool :=
  match ferryLoc c σ with
  | some l => (waitingLocs c σ).contains l
  | none => false

/-- Where the car aboard is going. -/
def carriedGoal (c : Cfg) (σ : AtomState) : Option Name :=
  (aboard c σ).getLast?.bind c.dest

/--
One action is always forced while a car waits ashore.  An empty ferry parked
where nobody waits must sail empty; a loaded ferry must first put its car down,
and unless it puts it down where a car waits, that costs more than was counted.
-/
def repositioning (c : Cfg) (σ : AtomState) : Nat :=
  if (ashore c σ).isEmpty then 0
  else if σ emptyFerry then (if waitingHere c σ then 0 else 1)
  else match carriedGoal c σ with
       | some g => if (waitingLocs c σ).contains g then 0 else 1
       | none => 1

theorem repositioning_le_one (c : Cfg) (σ : AtomState) : repositioning c σ ≤ 1 := by
  unfold repositioning
  split
  · omega
  · split
    · split <;> omega
    · split
      · split <;> omega
      · omega

/-- The per-car count plus the sails the ferry must make. -/
def value (c : Cfg) (σ : AtomState) : Nat :=
  load c σ + max (repositioning c σ) (emptySails c σ)

/-! ### Goal awareness -/

theorem value_eq_zero (c : Cfg) (σ : AtomState)
    (h : ∀ q ∈ c.cars, delivered c σ q = true) : value c σ = 0 := by
  have hload : load c σ = 0 := by
    unfold load
    have : ∀ q ∈ c.cars, carCost c σ q = 0 := by
      intro q hq
      simp [carCost, h q hq]
    rw [List.map_congr_left this]
    simp
  have hashore : ashore c σ = [] := by
    refine List.filter_eq_nil_iff.mpr ?_
    intro q hq
    simp [h q hq]
  have hempty : emptySails c σ = 0 := by
    unfold emptySails waitingLocs
    rw [hashore]
    simp
  have hrep : repositioning c σ = 0 := by
    unfold repositioning
    rw [hashore]
    simp
  simp [value, hload, hempty, hrep]

/-- Zero once every car's `at` goal holds. -/
theorem liftedGoalAware (c : Cfg) (p : Problem)
    (hsub : ∀ q ∈ c.cars, ∀ g, c.dest q = some g → atC q g ∈ p.goal)
    (hdest : ∀ q ∈ c.cars, (c.dest q).isSome) :
    LiftedGoalAware p (value c) := by
  intro σ hgoal
  refine value_eq_zero c σ fun q hq => ?_
  unfold delivered
  rcases hd : c.dest q with _ | g
  · exact absurd (hdest q hq) (by simp [hd])
  · exact hgoal (atC q g) (by simpa using hsub q hq g hd)

end Planner.Lifted.Ferry

/- -------------------------------------------------------------------------- -/
/-
Which domain a ferry task came from.

The same two decidable checks as miconic: the schema list, and — since ferry
has no static predicate the heuristic reads — nothing else.
-/

namespace Planner.Lifted.Ferry

open Planner Planner.Pddl

/-! ### Which predicates the schemas touch -/

theorem atFerry_dynamic {d : Domain} (hd : FerryDomain d) :
    (staticPredicates d).contains "at-ferry" = false :=
  not_static_of_mem_del (a := sailA) (by rw [hd]; simp) (y := atFerryV "?from")
    (by simp [sailA])

theorem at_dynamic {d : Domain} (hd : FerryDomain d) :
    (staticPredicates d).contains "at" = false :=
  not_static_of_mem_del (a := boardA) (by rw [hd]; simp) (y := atV "?car" "?loc")
    (by simp [boardA])

theorem on_dynamic {d : Domain} (hd : FerryDomain d) :
    (staticPredicates d).contains "on" = false :=
  not_static_of_mem_del (a := debarkA) (by rw [hd]; simp) (y := onV "?car")
    (by simp [debarkA])

theorem empty_dynamic {d : Domain} (hd : FerryDomain d) :
    (staticPredicates d).contains "empty-ferry" = false :=
  not_static_of_mem_del (a := boardA) (by rw [hd]; simp) (y := emptyV)
    (by simp [boardA])

/-! ### What an instance of it looks like -/

theorem instance_shape {d : Domain} {objects : List TypedName} (hd : FerryDomain d)
    (i : Instance d objects) :
    (∃ f g, i.schema = sailA ∧ i.args = [f, g] ∧
      WellTyped d objects "location" f ∧ WellTyped d objects "location" g) ∨
    (∃ q l, i.schema = boardA ∧ i.args = [q, l] ∧
      WellTyped d objects "car" q ∧ WellTyped d objects "location" l) ∨
    (∃ q l, i.schema = debarkA ∧ i.args = [q, l] ∧
      WellTyped d objects "car" q ∧ WellTyped d objects "location" l) := by
  have hmem : i.schema ∈ [sailA, boardA, debarkA] := hd ▸ i.mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h
  · obtain ⟨f, g, hargs, h1, h2⟩ := i.args_two (by rw [h])
    exact Or.inl ⟨f, g, h, hargs, by simpa [locP] using h1, by simpa [locP] using h2⟩
  · obtain ⟨q, l, hargs, h1, h2⟩ := i.args_two (by rw [h])
    exact Or.inr (Or.inl ⟨q, l, h, hargs, by simpa [carP] using h1,
      by simpa [locP] using h2⟩)
  · obtain ⟨q, l, hargs, h1, h2⟩ := i.args_two (by rw [h])
    exact Or.inr (Or.inr ⟨q, l, h, hargs, by simpa [carP] using h1,
      by simpa [locP] using h2⟩)

/-! ### The atoms of each shape, computed -/

theorem sail_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {f g : Pddl.Name} (hs : i.schema = sailA) (ha : i.args = [f, g]) :
    atFerryV "?from" ∈ i.schema.pre ∧
    instAtom i.schema.params i.args (atFerryV "?from") = atFerry f ∧
    atFerryV "?from" ∈ i.schema.del ∧
    i.add = [atFerry g, notAtFerry f] ∧ i.del = [notAtFerry g, atFerry f] := by
  refine ⟨by rw [hs]; simp [sailA], by rw [hs, ha]; rfl,
    by rw [hs]; simp [sailA], ?_, ?_⟩
  · rw [Pddl.Instance.add_eq, hs, ha]; rfl
  · rw [Pddl.Instance.del_eq, hs, ha]; rfl

theorem board_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {q l : Pddl.Name} (hs : i.schema = boardA) (ha : i.args = [q, l]) :
    atV "?car" "?loc" ∈ i.schema.pre ∧
    instAtom i.schema.params i.args (atV "?car" "?loc") = atC q l ∧
    atFerryV "?loc" ∈ i.schema.pre ∧
    instAtom i.schema.params i.args (atFerryV "?loc") = atFerry l ∧
    emptyV ∈ i.schema.pre ∧
    instAtom i.schema.params i.args emptyV = emptyFerry ∧
    atV "?car" "?loc" ∈ i.schema.del ∧ emptyV ∈ i.schema.del ∧
    i.add = [onC q] ∧ i.del = [atC q l, emptyFerry] := by
  refine ⟨by rw [hs]; simp [boardA], by rw [hs, ha]; rfl,
    by rw [hs]; simp [boardA], by rw [hs, ha]; rfl,
    by rw [hs]; simp [boardA], by rw [hs, ha]; rfl,
    by rw [hs]; simp [boardA], by rw [hs]; simp [boardA], ?_, ?_⟩
  · rw [Pddl.Instance.add_eq, hs, ha]; rfl
  · rw [Pddl.Instance.del_eq, hs, ha]; rfl

theorem debark_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {q l : Pddl.Name} (hs : i.schema = debarkA) (ha : i.args = [q, l]) :
    onV "?car" ∈ i.schema.pre ∧
    instAtom i.schema.params i.args (onV "?car") = onC q ∧
    atFerryV "?loc" ∈ i.schema.pre ∧
    instAtom i.schema.params i.args (atFerryV "?loc") = atFerry l ∧
    onV "?car" ∈ i.schema.del ∧
    i.add = [atC q l, emptyFerry] ∧ i.del = [onC q] := by
  refine ⟨by rw [hs]; simp [debarkA], by rw [hs, ha]; rfl,
    by rw [hs]; simp [debarkA], by rw [hs, ha]; rfl,
    by rw [hs]; simp [debarkA], ?_, ?_⟩
  · rw [Pddl.Instance.add_eq, hs, ha]; rfl
  · rw [Pddl.Instance.del_eq, hs, ha]; rfl

end Planner.Lifted.Ferry

/- -------------------------------------------------------------------------- -/
/-
Ferry's improved heuristic: the invariant it needs, and its preservation.

The ferry is at one place, each car is at one place, the ferry carries at most one
car, and it is empty exactly when it carries none.  All four are true of `:init`
and survive every action.
-/

namespace Planner.Lifted.Ferry

open Planner Planner.Pddl

structure Inv (σ : AtomState) : Prop where
  oneFerry : ∀ f g, σ (atFerry f) = true → σ (atFerry g) = true → f = g
  oneCar : ∀ q f g, σ (atC q f) = true → σ (atC q g) = true → f = g
  oneOn : ∀ q r, σ (onC q) = true → σ (onC r) = true → q = r
  emptyNone : σ emptyFerry = true → ∀ q, σ (onC q) = false
  onNotAt : ∀ q l, σ (onC q) = true → σ (atC q l) = false

/-! ### Atoms of different predicates are different -/

@[simp] theorem atC_ne_atFerry (q l f : Name) : atC q l ≠ atFerry f := by
  simp [atC, atFerry]
@[simp] theorem atC_ne_notAtFerry (q l f : Name) : atC q l ≠ notAtFerry f := by
  simp [atC, notAtFerry]
@[simp] theorem atC_ne_onC (q l r : Name) : atC q l ≠ onC r := by simp [atC, onC]
@[simp] theorem atC_ne_empty (q l : Name) : atC q l ≠ emptyFerry := by
  simp [atC, emptyFerry]
@[simp] theorem atFerry_ne_atC (f q l : Name) : atFerry f ≠ atC q l := by
  simp [atFerry, atC]
@[simp] theorem atFerry_ne_notAtFerry (f g : Name) : atFerry f ≠ notAtFerry g := by
  simp [atFerry, notAtFerry]
@[simp] theorem atFerry_ne_onC (f q : Name) : atFerry f ≠ onC q := by
  simp [atFerry, onC]
@[simp] theorem atFerry_ne_empty (f : Name) : atFerry f ≠ emptyFerry := by
  simp [atFerry, emptyFerry]
@[simp] theorem onC_ne_atC (q r l : Name) : onC q ≠ atC r l := by simp [onC, atC]
@[simp] theorem onC_ne_atFerry (q f : Name) : onC q ≠ atFerry f := by simp [onC, atFerry]
@[simp] theorem onC_ne_notAtFerry (q f : Name) : onC q ≠ notAtFerry f := by
  simp [onC, notAtFerry]
@[simp] theorem onC_ne_empty (q : Name) : onC q ≠ emptyFerry := by simp [onC, emptyFerry]
@[simp] theorem empty_ne_atC (q l : Name) : emptyFerry ≠ atC q l := by
  simp [emptyFerry, atC]
@[simp] theorem empty_ne_atFerry (f : Name) : emptyFerry ≠ atFerry f := by
  simp [emptyFerry, atFerry]
@[simp] theorem empty_ne_onC (q : Name) : emptyFerry ≠ onC q := by simp [emptyFerry, onC]
@[simp] theorem empty_ne_notAtFerry (f : Name) : emptyFerry ≠ notAtFerry f := by
  simp [emptyFerry, notAtFerry]

/-! ### Frames

Each schema's add and delete lists are short, so an atom outside them is
untouched.  These are the two shapes that recur.
-/

private theorem framed1 {o : AtomOp} {i : Instance d objects} {a x y z : GroundAtom}
    (hadd : ∀ b ∈ o.add, b ∈ i.add) (hdel : ∀ b ∈ o.del, b ∈ i.del)
    (hia : i.add = [x]) (hid : i.del = [y, z])
    (hax : a ≠ x) (hay : a ≠ y) (haz : a ≠ z) (σ : AtomState) :
    o.applyA σ a = σ a := by
  refine applyA_frame σ (fun hmem => ?_) (fun hmem => ?_)
  · have h := hadd a hmem; rw [hia] at h; exact hax (by simpa using h)
  · have h := hdel a hmem; rw [hid] at h
    rcases (by simpa using h : a = y ∨ a = z) with h1 | h1
    · exact hay h1
    · exact haz h1

private theorem framed2 {o : AtomOp} {i : Instance d objects} {a x y z : GroundAtom}
    (hadd : ∀ b ∈ o.add, b ∈ i.add) (hdel : ∀ b ∈ o.del, b ∈ i.del)
    (hia : i.add = [x, y]) (hid : i.del = [z])
    (hax : a ≠ x) (hay : a ≠ y) (haz : a ≠ z) (σ : AtomState) :
    o.applyA σ a = σ a := by
  refine applyA_frame σ (fun hmem => ?_) (fun hmem => ?_)
  · have h := hadd a hmem; rw [hia] at h
    rcases (by simpa using h : a = x ∨ a = y) with h1 | h1
    · exact hax h1
    · exact hay h1
  · have h := hdel a hmem; rw [hid] at h; exact haz (by simpa using h)

private theorem framed22 {o : AtomOp} {i : Instance d objects} {a w x y z : GroundAtom}
    (hadd : ∀ b ∈ o.add, b ∈ i.add) (hdel : ∀ b ∈ o.del, b ∈ i.del)
    (hia : i.add = [w, x]) (hid : i.del = [y, z])
    (haw : a ≠ w) (hax : a ≠ x) (hay : a ≠ y) (haz : a ≠ z) (σ : AtomState) :
    o.applyA σ a = σ a := by
  refine applyA_frame σ (fun hmem => ?_) (fun hmem => ?_)
  · have h := hadd a hmem; rw [hia] at h
    rcases (by simpa using h : a = w ∨ a = x) with h1 | h1
    · exact haw h1
    · exact hax h1
  · have h := hdel a hmem; rw [hid] at h
    rcases (by simpa using h : a = y ∨ a = z) with h1 | h1
    · exact hay h1
    · exact haz h1

/-- An atom only the delete list can touch never becomes true. -/
private theorem falls1 {o : AtomOp} {i : Instance d objects} {a x : GroundAtom}
    (hadd : ∀ b ∈ o.add, b ∈ i.add) (hia : i.add = [x]) (hax : a ≠ x)
    {σ : AtomState} (h : o.applyA σ a = true) : σ a = true := by
  by_cases hd : a ∈ o.del
  · rw [applyA_del σ hd (fun hmem => hax (by
      have := hadd a hmem; rw [hia] at this; simpa using this))] at h
    exact absurd h (by simp)
  · rwa [applyA_frame σ (fun hmem => hax (by
      have := hadd a hmem; rw [hia] at this; simpa using this)) hd] at h

private theorem falls2 {o : AtomOp} {i : Instance d objects} {a x y : GroundAtom}
    (hadd : ∀ b ∈ o.add, b ∈ i.add) (hia : i.add = [x, y])
    (hax : a ≠ x) (hay : a ≠ y) {σ : AtomState} (h : o.applyA σ a = true) :
    σ a = true := by
  have hna : a ∉ o.add := by
    intro hmem
    have hm2 := hadd a hmem; rw [hia] at hm2
    rcases (by simpa using hm2 : a = x ∨ a = y) with h1 | h1
    · exact hax h1
    · exact hay h1
  by_cases hd : a ∈ o.del
  · rw [applyA_del σ hd hna] at h; exact absurd h (by simp)
  · rwa [applyA_frame σ hna hd] at h

/-! ### The invariant survives every action -/

theorem inv_preserved {d : Domain} {p : Problem} (hd : FerryDomain d)
    {o : AtomOp} (hf : OpFacts d p o) {σ : AtomState} (hinv : Inv σ)
    (happ : o.applicableA σ) : Inv (o.applyA σ) := by
  rcases instance_shape hd hf.inst with
    ⟨f, g, hs, ha, -, -⟩ | ⟨q, l, hs, ha, -, -⟩ | ⟨q, l, hs, ha, -, -⟩
  · -- sail: only the ferry's place moves
    obtain ⟨hpreS, hinst, hdelS, hia, hid⟩ := sail_atoms hf.inst hs ha
    have hff : σ (atFerry f) = true := by
      have := hf.preComplete (atFerryV "?from") hpreS (atFerry_dynamic hd)
      rw [hinst] at this; exact happ _ this
    have hframe : ∀ a : GroundAtom, a ≠ atFerry g → a ≠ notAtFerry f →
        a ≠ notAtFerry g → a ≠ atFerry f → (o.applyA σ) a = σ a := by
      intro a h1 h2 h3 h4
      exact framed22 hf.subAdd hf.subDel hia hid h1 h2 h3 h4 σ
    have honly : ∀ x, (o.applyA σ) (atFerry x) = true → x = g := by
      intro x hx
      by_cases hxg : x = g
      · exact hxg
      · exfalso
        have hxadd : atFerry x ∉ o.add := by
          intro hmem
          have h2 := hf.subAdd _ hmem; rw [hia] at h2
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
          rcases h2 with h1 | h1
          · exact hxg (by simpa [atFerry] using h1)
          · simp [atFerry, notAtFerry] at h1
        by_cases hxf : x = f
        · subst hxf
          have hdelmem : atFerry x ∈ o.del := by
            have hraw := hf.delComplete (atFerryV "?from") hdelS ?_ ?_
            · rwa [hinst] at hraw
            · rw [hinst, hia]
              intro hmem
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
              rcases hmem with h1 | h1
              · exact hxg (by simpa [atFerry] using h1)
              · simp [atFerry, notAtFerry] at h1
            · rw [hinst]
              have := hf.preComplete (atFerryV "?from") hpreS (atFerry_dynamic hd)
              rwa [hinst] at this
          rw [applyA_del σ hdelmem hxadd] at hx
          exact absurd hx (by simp)
        · have hxdel : atFerry x ∉ o.del := by
            intro hmem
            have h2 := hf.subDel _ hmem; rw [hid] at h2
            simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
            rcases h2 with h1 | h1
            · simp [atFerry, notAtFerry] at h1
            · exact hxf (by simpa [atFerry] using h1)
          rw [applyA_frame σ hxadd hxdel] at hx
          exact hxf (hinv.oneFerry x f hx hff)
    refine ⟨fun x y hx hy => by rw [honly x hx, honly y hy], ?_, ?_, ?_, ?_⟩
    · intro r x y hx hy
      rw [hframe _ (by simp) (by simp) (by simp) (by simp)] at hx hy
      exact hinv.oneCar r x y hx hy
    · intro r t hr ht
      rw [hframe _ (by simp) (by simp) (by simp) (by simp)] at hr ht
      exact hinv.oneOn r t hr ht
    · intro he r
      rw [hframe _ (by simp) (by simp) (by simp) (by simp)] at he ⊢
      exact hinv.emptyNone he r
    · intro r x hr
      rw [hframe _ (by simp) (by simp) (by simp) (by simp)] at hr ⊢
      exact hinv.onNotAt r x hr
  · -- board: the car goes aboard, the ferry stops being empty
    obtain ⟨hatS, hatI, -, -, hempS, hempI, hatD, hempD, hia, hid⟩ :=
      board_atoms hf.inst hs ha
    have hempty : σ emptyFerry = true := by
      have := hf.preComplete emptyV hempS (empty_dynamic hd)
      rw [hempI] at this; exact happ _ this
    have hnone := hinv.emptyNone hempty
    have hatql : σ (atC q l) = true := by
      have := hf.preComplete (atV "?car" "?loc") hatS (at_dynamic hd)
      rw [hatI] at this; exact happ _ this
    have hemptyDel : emptyFerry ∈ o.del := by
      have hraw := hf.delComplete emptyV hempD ?_ ?_
      · rwa [hempI] at hraw
      · rw [hempI, hia]; simp [emptyFerry, onC]
      · rw [hempI]
        have := hf.preComplete emptyV hempS (empty_dynamic hd)
        rwa [hempI] at this
    have hatDel : atC q l ∈ o.del := by
      have hraw := hf.delComplete (atV "?car" "?loc") hatD ?_ ?_
      · rwa [hatI] at hraw
      · rw [hatI, hia]; simp [atC, onC]
      · rw [hatI]
        have := hf.preComplete (atV "?car" "?loc") hatS (at_dynamic hd)
        rwa [hatI] at this
    have honAdd : ∀ a : GroundAtom, a ∈ o.add → a = onC q := by
      intro a hmem
      have h2 := hf.subAdd _ hmem; rw [hia] at h2; simpa using h2
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x y hx hy
      rw [framed1 hf.subAdd hf.subDel hia hid (by simp) (by simp) (by simp) σ] at hx hy
      exact hinv.oneFerry x y hx hy
    · intro r x y hx hy
      exact hinv.oneCar r x y (falls1 hf.subAdd hia (by simp) hx)
        (falls1 hf.subAdd hia (by simp) hy)
    · intro r t hr ht
      have key : ∀ z, (o.applyA σ) (onC z) = true → z = q := by
        intro z hz
        by_contra hne
        rw [applyA_frame σ (fun hmem => hne (by simpa [onC] using honAdd _ hmem))
          (fun hmem => by
            have h2 := hf.subDel _ hmem; rw [hid] at h2
            simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
            rcases h2 with h1 | h1
            · simp [onC, atC] at h1
            · simp [onC, emptyFerry] at h1)] at hz
        rw [hnone z] at hz; exact Bool.noConfusion hz
      rw [key r hr, key t ht]
    · intro he r
      rw [applyA_del σ hemptyDel (fun hmem => by
        have := honAdd _ hmem; simp [emptyFerry, onC] at this)] at he
      exact absurd he (by simp)
    · intro r x hr
      by_cases hrq : r = q
      · subst hrq
        by_cases hxl : x = l
        · subst hxl
          exact applyA_del σ hatDel (fun hmem => by
            have := honAdd _ hmem; simp [atC, onC] at this)
        · rw [applyA_frame σ (fun hmem => by
            have := honAdd _ hmem; simp [atC, onC] at this) (fun hmem => by
              have h2 := hf.subDel _ hmem; rw [hid] at h2
              simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
              rcases h2 with h1 | h1
              · exact hxl (by simpa [atC] using h1)
              · simp [atC, emptyFerry] at h1)]
          by_contra hcon
          exact hxl (hinv.oneCar r x l (by simpa using hcon) hatql)
      · have hfr : (o.applyA σ) (onC r) = σ (onC r) :=
          applyA_frame (a := onC r) σ
            (fun hmem => hrq (by simpa [onC] using honAdd _ hmem))
            (fun hmem => by
              have h2 := hf.subDel _ hmem; rw [hid] at h2
              simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
              rcases h2 with h1 | h1
              · simp [onC, atC] at h1
              · simp [onC, emptyFerry] at h1)
        rw [hfr, hnone r] at hr; exact Bool.noConfusion hr
  · -- debark: the car comes ashore, the ferry becomes empty
    obtain ⟨honS, honI, -, -, hdelS, hia, hid⟩ := debark_atoms hf.inst hs ha
    have honq : σ (onC q) = true := by
      have := hf.preComplete (onV "?car") honS (on_dynamic hd)
      rw [honI] at this; exact happ _ this
    have honDel : onC q ∈ o.del := by
      have hraw := hf.delComplete (onV "?car") hdelS ?_ ?_
      · rwa [honI] at hraw
      · rw [honI, hia]; simp [onC, atC, emptyFerry]
      · rw [honI]
        have := hf.preComplete (onV "?car") honS (on_dynamic hd)
        rwa [honI] at this
    have haddIs : ∀ a : GroundAtom, a ∈ o.add → a = atC q l ∨ a = emptyFerry := by
      intro a hmem
      have h2 := hf.subAdd _ hmem; rw [hia] at h2
      simpa using h2
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x y hx hy
      rw [framed2 hf.subAdd hf.subDel hia hid (by simp) (by simp) (by simp) σ] at hx hy
      exact hinv.oneFerry x y hx hy
    · intro r x y hx hy
      by_cases hrq : r = q
      · subst hrq
        have key : ∀ z, (o.applyA σ) (atC r z) = true → z = l := by
          intro z hz
          by_cases hzl : z = l
          · exact hzl
          · exfalso
            have hfr : (o.applyA σ) (atC r z) = σ (atC r z) :=
              applyA_frame (a := atC r z) σ
                (fun hmem => by
                  rcases haddIs _ hmem with h1 | h1
                  · exact hzl (by simpa [atC] using h1)
                  · simp [atC, emptyFerry] at h1)
                (fun hmem => by
                  have h2 := hf.subDel _ hmem; rw [hid] at h2
                  simp [atC, onC] at h2)
            rw [hfr, hinv.onNotAt r z honq] at hz
            exact Bool.noConfusion hz
        rw [key x hx, key y hy]
      · have hfr : ∀ z, (o.applyA σ) (atC r z) = σ (atC r z) := fun z =>
          applyA_frame (a := atC r z) σ
            (fun hmem => by
              rcases haddIs _ hmem with h1 | h1
              · have h3 : r = q ∧ z = l := by simpa [atC] using h1
                exact hrq h3.1
              · simp [atC, emptyFerry] at h1)
            (fun hmem => by
              have h2 := hf.subDel _ hmem; rw [hid] at h2
              simp [atC, onC] at h2)
        rw [hfr] at hx hy
        exact hinv.oneCar r x y hx hy
    · intro r t hr ht
      exact hinv.oneOn r t (falls2 hf.subAdd hia (by simp) (by simp) hr)
        (falls2 hf.subAdd hia (by simp) (by simp) ht)
    · intro he r
      by_cases hrq : r = q
      · subst hrq
        exact applyA_del σ honDel (fun hmem => by
          rcases haddIs _ hmem with h1 | h1
          · simp [onC, atC] at h1
          · simp [onC, emptyFerry] at h1)
      · rw [applyA_frame σ (fun hmem => by
          rcases haddIs _ hmem with h1 | h1
          · simp [onC, atC] at h1
          · simp [onC, emptyFerry] at h1) (fun hmem => by
            have h2 := hf.subDel _ hmem; rw [hid] at h2
            exact hrq (by simpa [onC] using h2))]
        by_contra hcon
        exact hrq (hinv.oneOn r q (by simpa using hcon) honq)
    · intro r x hr
      have hrq : r ≠ q := by
        rintro rfl
        rw [applyA_del σ honDel (fun hmem => by
          rcases haddIs _ hmem with h1 | h1
          · simp [onC, atC] at h1
          · simp [onC, emptyFerry] at h1)] at hr
        exact Bool.noConfusion hr
      have honr : σ (onC r) = true := falls2 hf.subAdd hia (by simp) (by simp) hr
      exact absurd (hinv.oneOn r q honr honq) hrq

/-! ### What the configuration owes the problem -/

structure CfgOK (d : Domain) (p : Problem) (c : Cfg) : Prop where
  locs : ∀ l, WellTyped d (allObjects d p) "location" l → l ∈ c.locations
  cars : ∀ q, WellTyped d (allObjects d p) "car" q → q ∈ c.cars
  nodup : c.cars.Nodup

/-! ### Reading a position -/

theorem ferryLoc_congr {c : Cfg} {σ τ : AtomState}
    (h : ∀ x, τ (atFerry x) = σ (atFerry x)) : ferryLoc c τ = ferryLoc c σ :=
  find?_congr _ _ _ fun x _ => h x

theorem carLoc_congr {c : Cfg} {σ τ : AtomState} (q : Name)
    (h : ∀ x, τ (atC q x) = σ (atC q x)) : carLoc c τ q = carLoc c σ q :=
  find?_congr _ _ _ fun x _ => h x

/-- With one `at-ferry` holding, the ferry is there. -/
theorem ferryLoc_eq {c : Cfg} {σ : AtomState} (hinv : Inv σ) {l : Name}
    (hl : l ∈ c.locations) (hs : σ (atFerry l) = true) : ferryLoc c σ = some l := by
  unfold ferryLoc
  rcases hfind : c.locations.find? (fun x => σ (atFerry x)) with _ | x
  · rw [List.find?_eq_none] at hfind
    exact absurd hs (by simpa using hfind l hl)
  · rw [hinv.oneFerry x l (by simpa using List.find?_some hfind) hs]

/-- And with one `at` holding, that is where the car stands. -/
theorem carLoc_eq {c : Cfg} {σ : AtomState} (hinv : Inv σ) {q l : Name}
    (hl : l ∈ c.locations) (hs : σ (atC q l) = true) : carLoc c σ q = some l := by
  unfold carLoc
  rcases hfind : c.locations.find? (fun x => σ (atC q x)) with _ | x
  · rw [List.find?_eq_none] at hfind
    exact absurd hs (by simpa using hfind l hl)
  · rw [hinv.oneCar q x l (by simpa using List.find?_some hfind) hs]

/-- Wherever `carLoc` points, the atom holds. -/
theorem carLoc_holds {c : Cfg} {σ : AtomState} {q x : Name}
    (h : carLoc c σ q = some x) : σ (atC q x) = true := by
  simpa using List.find?_some h

theorem ferryLoc_holds {c : Cfg} {σ : AtomState} {x : Name}
    (h : ferryLoc c σ = some x) : σ (atFerry x) = true := by
  simpa using List.find?_some h

/-! ### The per-car sum -/

theorem load_congr {c : Cfg} {σ τ : AtomState}
    (h : ∀ q ∈ c.cars, carCost c σ q = carCost c τ q) : load c σ = load c τ := by
  unfold load; rw [List.map_congr_left h]

theorem load_le {c : Cfg} {σ τ : AtomState} {q : Name} (hnd : c.cars.Nodup)
    (hstep : carCost c σ q ≤ carCost c τ q + 1)
    (hrest : ∀ r ∈ c.cars, r ≠ q → carCost c σ r ≤ carCost c τ r) :
    load c σ ≤ load c τ + 1 :=
  sum_map_le_succ _ _ _ q hnd hstep hrest

theorem load_drop {c : Cfg} {σ τ : AtomState} {q : Name} (hq : q ∈ c.cars)
    (hnd : c.cars.Nodup) (hstep : carCost c σ q + 1 ≤ carCost c τ q)
    (hrest : ∀ r ∈ c.cars, r ≠ q → carCost c σ r ≤ carCost c τ r) :
    load c σ + 1 ≤ load c τ :=
  sum_map_add_le _ _ _ q 1 hq hnd hstep hrest

/-! ### The places that force an empty sail, as a set -/

/-- `emptySails` counts this list. -/
def esList (c : Cfg) (σ : AtomState) : List Name :=
  (waitingLocs c σ).filter fun l =>
    !(destinations c σ).contains l && !(σ emptyFerry && ferryLoc c σ = some l)

theorem emptySails_eq (c : Cfg) (σ : AtomState) :
    emptySails c σ = (esList c σ).length := rfl

theorem esList_nodup (c : Cfg) (σ : AtomState) : (esList c σ).Nodup :=
  (List.nodup_dedup _).filter _

theorem mem_ashore {c : Cfg} {σ : AtomState} {q : Name} :
    q ∈ ashore c σ ↔ q ∈ c.cars ∧ delivered c σ q = false ∧ σ (onC q) = false := by
  unfold ashore
  rw [List.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h2
    exact ⟨h1, h2.1, h2.2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, by simp [h2, h3]⟩

theorem mem_aboard {c : Cfg} {σ : AtomState} {q : Name} :
    q ∈ aboard c σ ↔ q ∈ c.cars ∧ delivered c σ q = false ∧ σ (onC q) = true := by
  unfold aboard
  rw [List.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h2
    exact ⟨h1, h2.1, h2.2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, by simp [h2, h3]⟩

/-- Whatever `carriedGoal` names is the goal of a car aboard. -/
theorem carriedGoal_mem {c : Cfg} {σ : AtomState} {g : Name}
    (h : carriedGoal c σ = some g) : ∃ r ∈ aboard c σ, c.dest r = some g := by
  unfold carriedGoal at h
  rcases hl : (aboard c σ).getLast? with _ | r
  · rw [hl] at h; exact absurd h (by simp)
  · rw [hl] at h
    exact ⟨r, List.mem_of_getLast? hl, by simpa using h⟩

theorem mem_waitingLocs {c : Cfg} {σ : AtomState} {x : Name} :
    x ∈ waitingLocs c σ ↔ ∃ q ∈ ashore c σ, carLoc c σ q = some x := by
  unfold waitingLocs
  rw [List.mem_dedup, List.mem_filterMap]

theorem mem_destinations {c : Cfg} {σ : AtomState} {x : Name} :
    x ∈ destinations c σ ↔ ∃ q ∈ c.cars, delivered c σ q = false ∧ c.dest q = some x := by
  unfold destinations
  rw [List.mem_dedup, List.mem_filterMap]
  constructor
  · rintro ⟨q, hq, hx⟩
    rw [List.mem_filter] at hq
    exact ⟨q, hq.1, by simpa using hq.2, hx⟩
  · rintro ⟨q, hq, hd, hx⟩
    exact ⟨q, by rw [List.mem_filter]; exact ⟨hq, by simp [hd]⟩, hx⟩

theorem mem_esList {c : Cfg} {σ : AtomState} {x : Name} :
    x ∈ esList c σ ↔ x ∈ waitingLocs c σ ∧ x ∉ destinations c σ ∧
      ¬(σ emptyFerry = true ∧ ferryLoc c σ = some x) := by
  unfold esList
  rw [List.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h2
    exact ⟨h1, by simpa using h2.1, by
      intro ⟨he, hf⟩
      rw [he, hf] at h2
      simp at h2⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_⟩
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
    refine ⟨by simpa using h2, ?_⟩
    by_cases he : σ emptyFerry
    · by_cases hf : ferryLoc c σ = some x
      · exact absurd ⟨he, hf⟩ h3
      · simp [he, hf]
    · simp [he]

theorem emptySails_mono {c : Cfg} {σ τ : AtomState}
    (h : ∀ x ∈ esList c σ, x ∈ esList c τ) : emptySails c σ ≤ emptySails c τ :=
  length_le_of_subset' _ _ (esList_nodup c σ) h

theorem emptySails_le_succ {c : Cfg} {σ τ : AtomState} (a : Name)
    (h : ∀ x ∈ esList c σ, x ∈ esList c τ ∨ x = a) :
    emptySails c σ ≤ emptySails c τ + 1 :=
  length_le_succ_of_subset' _ _ a (esList_nodup c σ) h

/-! ### A sail: only the ferry's place moves

This is the whole `sail` case, and it needs to know nothing about the schema
beyond what it leaves alone.  Either the ferry is empty, and then no car's term
depends on where it is, so only one place can leave the empty-sail set; or it is
loaded, and then the empty-sail set does not mention the ferry at all, and only
the one car aboard can change its term.
-/

theorem value_le_of_ferry_only {c : Cfg} {σ τ : AtomState} (hinv : Inv σ)
    (hnd : c.cars.Nodup)
    (hat : ∀ q x, τ (atC q x) = σ (atC q x))
    (hon : ∀ q, τ (onC q) = σ (onC q))
    (hem : τ emptyFerry = σ emptyFerry) :
    value c σ ≤ value c τ + 1 := by
  have hdel : ∀ q, delivered c τ q = delivered c σ q := by
    intro q; unfold delivered
    rcases c.dest q with _ | g
    · rfl
    · exact hat q g
  have hcl : ∀ q, carLoc c τ q = carLoc c σ q := fun q => carLoc_congr q (hat q)
  have hash : ashore c τ = ashore c σ := by
    unfold ashore
    exact List.filter_congr fun q _ => by rw [hdel q, hon q]
  have hwait : waitingLocs c τ = waitingLocs c σ := by
    unfold waitingLocs
    rw [hash]
    congr 1
    exact List.filterMap_congr (fun q _ => hcl q)
  have hdst : destinations c τ = destinations c σ := by
    unfold destinations
    congr 2
    exact List.filter_congr fun q _ => by rw [hdel q]
  -- the empty-sail set, in both directions
  have hesub : ∀ x ∈ esList c σ, x ∈ waitingLocs c τ ∧ x ∉ destinations c τ := by
    intro x hx
    obtain ⟨h1, h2, -⟩ := mem_esList.mp hx
    exact ⟨by rw [hwait]; exact h1, by rw [hdst]; exact h2⟩
  by_cases he : σ emptyFerry = true
  · -- empty: no car is aboard, so the per-car sum does not move at all
    have hnone := hinv.emptyNone he
    have hload : load c σ = load c τ := by
      refine load_congr fun q _ => ?_
      unfold carCost
      rw [hdel q, hon q, hnone q]
      simp
    have hes : emptySails c σ ≤ emptySails c τ + 1 := by
      rcases hf : ferryLoc c τ with _ | a
      · refine Nat.le_trans (emptySails_mono ?_) (Nat.le_add_right _ 1)
        intro x hx
        obtain ⟨h1, h2⟩ := hesub x hx
        exact mem_esList.mpr ⟨h1, h2, by rw [hf]; simp⟩
      · refine emptySails_le_succ a fun x hx => ?_
        by_cases hxa : x = a
        · exact Or.inr hxa
        · obtain ⟨h1, h2⟩ := hesub x hx
          have h3 : ¬(τ emptyFerry = true ∧ ferryLoc c τ = some x) := by
            rintro ⟨-, hc⟩
            rw [hf] at hc
            have hax : a = x := by simpa using hc
            exact hxa hax.symm
          exact Or.inl (mem_esList.mpr ⟨h1, h2, h3⟩)
    have hr1 := repositioning_le_one c σ
    unfold value; omega
  · -- loaded: the empty-sail set does not mention the ferry
    have he' : σ emptyFerry = false := by simpa using he
    have hes : emptySails c σ ≤ emptySails c τ := by
      refine emptySails_mono fun x hx => ?_
      obtain ⟨h1, h2⟩ := hesub x hx
      exact mem_esList.mpr ⟨h1, h2, by rintro ⟨hc, -⟩; rw [hem, he'] at hc; simp at hc⟩
    have hstep : ∀ r, carCost c σ r ≤ carCost c τ r + 1 := by
      intro r
      unfold carCost
      rw [hdel r, hon r]
      split
      · omega
      · split
        · split <;> split <;> omega
        · omega
    have hload : load c σ ≤ load c τ + 1 := by
      refine load_le (q := (c.cars.find? fun r => σ (onC r)).getD "") hnd (hstep _) ?_
      intro r hrmem hrq
      have hoff : σ (onC r) = false := by
        by_contra hc
        have hct : σ (onC r) = true := by simpa using hc
        rcases hfind : c.cars.find? (fun z => σ (onC z)) with _ | r'
        · rw [List.find?_eq_none] at hfind
          exact absurd hct (by simpa using hfind r hrmem)
        · have hr' : σ (onC r') = true := by simpa using List.find?_some hfind
          exact hrq (by rw [hfind]; exact hinv.oneOn r r' hct hr')
      unfold carCost
      rw [hdel r, hon r, hoff]
      simp
    -- a loaded ferry's repositioning does not read where it stands
    have habd : aboard c τ = aboard c σ := by
      unfold aboard
      exact List.filter_congr fun q _ => by rw [hdel q, hon q]
    have hrep : repositioning c τ = repositioning c σ := by
      unfold repositioning carriedGoal
      rw [hash, hem, he', habd, hwait]
      simp
    unfold value; omega

/-! ### The three schemas' bounds -/

theorem sail_value {d : Domain} {p : Problem} {c : Cfg} {o : AtomOp}
    (hf : OpFacts d p o) {f g : Name} (hs : hf.inst.schema = sailA)
    (ha : hf.inst.args = [f, g]) (hnd : c.cars.Nodup) {σ : AtomState} (hinv : Inv σ) :
    value c σ ≤ value c (o.applyA σ) + 1 := by
  obtain ⟨-, -, -, hia, hid⟩ := sail_atoms hf.inst hs ha
  exact value_le_of_ferry_only hinv hnd
    (fun r x => framed22 hf.subAdd hf.subDel hia hid (by simp) (by simp) (by simp)
      (by simp) σ)
    (fun r => framed22 hf.subAdd hf.subDel hia hid (by simp) (by simp) (by simp)
      (by simp) σ)
    (framed22 hf.subAdd hf.subDel hia hid (by simp) (by simp) (by simp) (by simp) σ)

theorem board_value {d : Domain} {p : Problem} {c : Cfg} (hd : FerryDomain d)
    (hok : CfgOK d p c) {o : AtomOp} (hf : OpFacts d p o) {q l : Name}
    (hs : hf.inst.schema = boardA) (ha : hf.inst.args = [q, l])
    (hq : WellTyped d (allObjects d p) "car" q)
    (hl : WellTyped d (allObjects d p) "location" l)
    {σ : AtomState} (hinv : Inv σ) (happ : o.applicableA σ) :
    value c σ ≤ value c (o.applyA σ) + 1 := by
  obtain ⟨hatS, hatI, hfS, hfI, hempS, hempI, hatD, hempD, hia, hid⟩ :=
    board_atoms hf.inst hs ha
  set τ := o.applyA σ with hτ
  have hqc : q ∈ c.cars := hok.cars q hq
  have hlc : l ∈ c.locations := hok.locs l hl
  -- the preconditions
  have hatql : σ (atC q l) = true := by
    have := hf.preComplete (atV "?car" "?loc") hatS (at_dynamic hd)
    rw [hatI] at this; exact happ _ this
  have hferry : σ (atFerry l) = true := by
    have := hf.preComplete (atFerryV "?loc") hfS (atFerry_dynamic hd)
    rw [hfI] at this; exact happ _ this
  have hempty : σ emptyFerry = true := by
    have := hf.preComplete emptyV hempS (empty_dynamic hd)
    rw [hempI] at this; exact happ _ this
  have hnone := hinv.emptyNone hempty
  -- what the step does
  have honAdd : ∀ a : GroundAtom, a ∈ o.add → a = onC q := by
    intro a hmem
    have h2 := hf.subAdd _ hmem; rw [hia] at h2; simpa using h2
  have hdelIs : ∀ a : GroundAtom, a ∈ o.del → a = atC q l ∨ a = emptyFerry := by
    intro a hmem
    have h2 := hf.subDel _ hmem; rw [hid] at h2; simpa using h2
  have hframe : ∀ a : GroundAtom, a ≠ onC q → a ≠ atC q l → a ≠ emptyFerry →
      τ a = σ a := fun a h1 h2 h3 =>
    framed1 hf.subAdd hf.subDel hia hid h1 h2 h3 σ
  have hatDel : atC q l ∈ o.del := by
    have hraw := hf.delComplete (atV "?car" "?loc") hatD ?_ ?_
    · rwa [hatI] at hraw
    · rw [hatI, hia]; simp [atC, onC]
    · rw [hatI]
      have := hf.preComplete (atV "?car" "?loc") hatS (at_dynamic hd)
      rwa [hatI] at this
  have hempDel : emptyFerry ∈ o.del := by
    have hraw := hf.delComplete emptyV hempD ?_ ?_
    · rwa [hempI] at hraw
    · rw [hempI, hia]; simp [emptyFerry, onC]
    · rw [hempI]
      have := hf.preComplete emptyV hempS (empty_dynamic hd)
      rwa [hempI] at this
  have hatqlF : τ (atC q l) = false :=
    applyA_del σ hatDel (fun hmem => by have := honAdd _ hmem; simp [atC, onC] at this)
  have hempF : τ emptyFerry = false :=
    applyA_del σ hempDel (fun hmem => by
      have := honAdd _ hmem; simp [emptyFerry, onC] at this)
  have hatFrame : ∀ r x, (r, x) ≠ (q, l) → τ (atC r x) = σ (atC r x) := by
    intro r x hne
    refine hframe _ (by simp [atC, onC]) ?_ (by simp [atC, emptyFerry])
    simp only [ne_eq, atC, GroundAtom.mk.injEq, true_and, List.cons.injEq, and_true]
    rintro ⟨rfl, rfl⟩; exact hne rfl
  have honFrame : ∀ r, r ≠ q → τ (onC r) = σ (onC r) := fun r hr =>
    hframe _ (by simpa [onC] using hr) (by simp [onC, atC]) (by simp [onC, emptyFerry])
  have hferryLoc : ferryLoc c τ = some l := by
    rw [ferryLoc_congr (σ := σ) (τ := τ) fun x => hframe _ (by simp [atFerry, onC])
      (by simp [atFerry, atC]) (by simp [atFerry, emptyFerry])]
    exact ferryLoc_eq hinv hlc hferry
  have hferryLocσ : ferryLoc c σ = some l := ferryLoc_eq hinv hlc hferry
  -- the per-car sum falls by at most one
  have hdelR : ∀ r, r ≠ q → delivered c τ r = delivered c σ r := by
    intro r hr; unfold delivered
    rcases c.dest r with _ | y
    · rfl
    · exact hatFrame r y (by simp [hr])
  have hload : load c σ ≤ load c τ + 1 := by
    refine load_le (q := q) hok.nodup ?_ ?_
    · by_cases hdq : delivered c σ q = true
      · simp [carCost, hdq]
      · have hdq' : delivered c σ q = false := by simpa using hdq
        have hτq : delivered c τ q = false := by
          rcases hdd : c.dest q with _ | y
          · exact absurd (by simp [delivered, hdd] : delivered c σ q = true)
              (by rw [hdq']; simp)
          · simp only [delivered, hdd] at hdq' ⊢
            by_cases hyl : y = l
            · subst hyl; exact hatqlF
            · rw [hatFrame q y (by simp [hyl])]; exact hdq'
        by_cases hoq : τ (onC q) = true
        · have hne : ferryLoc c τ ≠ c.dest q := by
            rw [hferryLoc]
            intro hc
            have hdt : delivered c σ q = true := by
              unfold delivered; rw [← hc]; exact hatql
            rw [hdt] at hdq'; simp at hdq'
          simp only [carCost, hdq', hτq, hnone q, hoq, Bool.false_eq_true, if_false,
            if_true, hne]
          omega
        · have hoq' : τ (onC q) = false := by simpa using hoq
          simp [carCost, hdq', hτq, hnone q, hoq']
    · intro r _ hrq
      unfold carCost
      rw [hdelR r hrq, honFrame r hrq, hnone r]
      simp
  -- and the empty sails do not fall
  have hes : emptySails c σ ≤ emptySails c τ := by
    refine emptySails_mono fun x hx => ?_
    obtain ⟨h1, h2, h3⟩ := mem_esList.mp hx
    have hxl : x ≠ l := by
      rintro rfl
      exact h3 ⟨hempty, hferryLocσ⟩
    obtain ⟨r, hr, hcx⟩ := mem_waitingLocs.mp h1
    obtain ⟨hrc, hrd, hro⟩ := mem_ashore.mp hr
    have hrq : r ≠ q := by
      rintro rfl
      exact hxl (hinv.oneCar r x l (carLoc_holds hcx) hatql)
    have hclr : carLoc c τ r = carLoc c σ r :=
      carLoc_congr r fun y => hatFrame r y (by simp [hrq])
    refine mem_esList.mpr ⟨mem_waitingLocs.mpr ⟨r, mem_ashore.mpr ⟨hrc, ?_, ?_⟩,
      by rw [hclr]; exact hcx⟩, ?_, by rw [hempF]; simp⟩
    · rw [hdelR r hrq]; exact hrd
    · rw [honFrame r hrq]; exact hro
    · intro hmem
      obtain ⟨y, hyc, hyd, hyx⟩ := mem_destinations.mp hmem
      by_cases hyq : y = q
      · subst hyq
        apply hxl
        have : delivered c σ y = false := by
          by_contra hc
          have hct : delivered c σ y = true := by simpa using hc
          unfold delivered at hct
          rw [hyx] at hct
          exact absurd (hinv.oneCar y x l hct hatql) hxl
        exact absurd h2 (by
          simp only [not_not]
          exact mem_destinations.mpr ⟨y, hyc, this, hyx⟩)
      · exact h2 (mem_destinations.mpr ⟨y, hyc, by rw [← hdelR y hyq]; exact hyd, hyx⟩)
  -- and if a reposition was forced before the boarding, it still is
  have hrep1 : repositioning c σ = 1 → repositioning c τ = 1 := by
    intro h1
    unfold repositioning at h1
    have hae : (ashore c σ).isEmpty = false := by
      by_contra hc
      rw [if_pos (by simpa using hc)] at h1
      exact absurd h1 (by simp)
    rw [if_neg (by simp [hae]), if_pos hempty] at h1
    have hwh : waitingHere c σ = false := by
      by_contra hc
      rw [if_pos (by simpa using hc)] at h1
      exact absurd h1 (by simp)
    have hlnw : l ∉ waitingLocs c σ := by
      intro hc
      rw [show waitingHere c σ = true from by
        unfold waitingHere; rw [hferryLocσ]; simpa using hc] at hwh
      exact Bool.noConfusion hwh
    have hqnash : q ∉ ashore c σ := by
      intro hc
      exact hlnw (mem_waitingLocs.mpr ⟨q, hc, carLoc_eq hinv hlc hatql⟩)
    have hashsub : ∀ r ∈ ashore c σ, r ∈ ashore c τ := by
      intro r hr
      obtain ⟨hrc, hrd, hro⟩ := mem_ashore.mp hr
      have hrq : r ≠ q := by rintro rfl; exact hqnash hr
      exact mem_ashore.mpr ⟨hrc, by rw [hdelR r hrq]; exact hrd,
        by rw [honFrame r hrq]; exact hro⟩
    have hτne : (ashore c τ).isEmpty = false := by
      rcases hcc : ashore c σ with _ | ⟨a, t⟩
      · rw [hcc] at hae; simp at hae
      · have hm := hashsub a (by rw [hcc]; simp)
        rcases hcc2 : ashore c τ with _ | ⟨b, u⟩
        · rw [hcc2] at hm; simp at hm
        · rfl
    have hwsub : ∀ x ∈ waitingLocs c τ, x ∈ waitingLocs c σ := by
      intro x hx
      obtain ⟨r, hr, hcx⟩ := mem_waitingLocs.mp hx
      obtain ⟨hrc, hrd, hro⟩ := mem_ashore.mp hr
      have hrq : r ≠ q := by
        rintro rfl
        have hxa : τ (atC r x) = true := carLoc_holds hcx
        by_cases hxl : x = l
        · rw [hxl, hatqlF] at hxa; exact Bool.noConfusion hxa
        · rw [hatFrame r x (by simp [hxl])] at hxa
          exact hxl (hinv.oneCar r x l hxa hatql)
      refine mem_waitingLocs.mpr ⟨r, mem_ashore.mpr ⟨hrc,
        by rw [← hdelR r hrq]; exact hrd, by rw [← honFrame r hrq]; exact hro⟩, ?_⟩
      rw [← carLoc_congr r fun y => hatFrame r y (by simp [hrq])]
      exact hcx
    unfold repositioning
    rw [hempF, if_neg (by simp [hτne])]
    simp only [Bool.false_eq_true, if_false]
    rcases hcg : carriedGoal c τ with _ | g
    · rfl
    · obtain ⟨r, hr, hdr⟩ := carriedGoal_mem hcg
      obtain ⟨hrc, hrd, hro⟩ := mem_aboard.mp hr
      have hrq : r = q := by
        by_contra hne
        rw [honFrame r hne, hnone r] at hro; exact Bool.noConfusion hro
      subst hrq
      have hdσ : delivered c σ r = true := by
        by_contra hc
        exact hqnash (mem_ashore.mpr ⟨hrc, by simpa using hc, hnone r⟩)
      have hgl : g = l := by
        unfold delivered at hdσ
        rw [hdr] at hdσ
        exact hinv.oneCar r g l hdσ hatql
      subst hgl
      show (if (waitingLocs c τ).contains g = true then 0 else 1) = 1
      rw [if_neg (by simpa using fun hc => hlnw (hwsub g hc))]
  have hrepLe : repositioning c σ ≤ repositioning c τ := by
    have h1 := repositioning_le_one c σ
    rcases Nat.lt_or_ge (repositioning c σ) 1 with h | h
    · omega
    · have := hrep1 (by omega); omega
  unfold value; omega

theorem debark_value {d : Domain} {p : Problem} {c : Cfg} (hd : FerryDomain d)
    (hok : CfgOK d p c) {o : AtomOp} (hf : OpFacts d p o) {q l : Name}
    (hs : hf.inst.schema = debarkA) (ha : hf.inst.args = [q, l])
    (hq : WellTyped d (allObjects d p) "car" q)
    (hl : WellTyped d (allObjects d p) "location" l)
    {σ : AtomState} (hinv : Inv σ) (happ : o.applicableA σ) :
    value c σ ≤ value c (o.applyA σ) + 1 := by
  obtain ⟨honS, honI, hfS, hfI, hdelS, hia, hid⟩ := debark_atoms hf.inst hs ha
  set τ := o.applyA σ with hτ
  have hqc : q ∈ c.cars := hok.cars q hq
  have hlc : l ∈ c.locations := hok.locs l hl
  have honq : σ (onC q) = true := by
    have := hf.preComplete (onV "?car") honS (on_dynamic hd)
    rw [honI] at this; exact happ _ this
  have hferry : σ (atFerry l) = true := by
    have := hf.preComplete (atFerryV "?loc") hfS (atFerry_dynamic hd)
    rw [hfI] at this; exact happ _ this
  have hempσ : σ emptyFerry = false := by
    by_contra hc
    have := hinv.emptyNone (by simpa using hc) q
    rw [this] at honq; exact Bool.noConfusion honq
  have haddIs : ∀ a : GroundAtom, a ∈ o.add → a = atC q l ∨ a = emptyFerry := by
    intro a hmem
    have h2 := hf.subAdd _ hmem; rw [hia] at h2; simpa using h2
  have hframe : ∀ a : GroundAtom, a ≠ atC q l → a ≠ emptyFerry → a ≠ onC q →
      τ a = σ a := fun a h1 h2 h3 => framed2 hf.subAdd hf.subDel hia hid h1 h2 h3 σ
  have hatFrame : ∀ r x, (r, x) ≠ (q, l) → τ (atC r x) = σ (atC r x) := by
    intro r x hne
    refine hframe _ ?_ (by simp [atC, emptyFerry]) (by simp [atC, onC])
    simp only [ne_eq, atC, GroundAtom.mk.injEq, true_and, List.cons.injEq, and_true]
    rintro ⟨rfl, rfl⟩; exact hne rfl
  have honFrame : ∀ r, r ≠ q → τ (onC r) = σ (onC r) := fun r hr =>
    hframe _ (by simp [onC, atC]) (by simp [onC, emptyFerry]) (by simpa [onC] using hr)
  have honDel : onC q ∈ o.del := by
    have hraw := hf.delComplete (onV "?car") hdelS ?_ ?_
    · rwa [honI] at hraw
    · rw [honI, hia]; simp [onC, atC, emptyFerry]
    · rw [honI]
      have := hf.preComplete (onV "?car") honS (on_dynamic hd)
      rwa [honI] at this
  have honqF : τ (onC q) = false :=
    applyA_del σ honDel (fun hmem => by
      rcases haddIs _ hmem with h1 | h1
      · simp [onC, atC] at h1
      · simp [onC, emptyFerry] at h1)
  have hferryLocσ : ferryLoc c σ = some l := ferryLoc_eq hinv hlc hferry
  have hferryLoc : ferryLoc c τ = some l := by
    rw [ferryLoc_congr (σ := σ) (τ := τ) fun x => hframe _ (by simp [atFerry, atC])
      (by simp [atFerry, emptyFerry]) (by simp [atFerry, onC])]
    exact hferryLocσ
  have hdelR : ∀ r, r ≠ q → delivered c τ r = delivered c σ r := by
    intro r hr; unfold delivered
    rcases c.dest r with _ | y
    · rfl
    · exact hatFrame r y (by simp [hr])
  have hcost : ∀ r, r ≠ q → carCost c σ r = carCost c τ r := by
    intro r hr
    unfold carCost
    rw [hdelR r hr, honFrame r hr, hferryLoc, hferryLocσ]
  -- a car aboard stands nowhere, so it is not yet delivered
  have hundel : ∀ y, c.dest q = some y → delivered c σ q = false := by
    intro y hy
    unfold delivered; rw [hy]; exact hinv.onNotAt q y honq
  -- every place still forcing an empty sail, other than where the ferry stands
  have hesGen : ∀ x ∈ esList c σ, x ≠ l → x ∈ esList c τ := by
    intro x hx hxl
    obtain ⟨h1, h2, -⟩ := mem_esList.mp hx
    obtain ⟨r, hr, hcx⟩ := mem_waitingLocs.mp h1
    obtain ⟨hrc, hrd, hro⟩ := mem_ashore.mp hr
    have hrq : r ≠ q := by rintro rfl; rw [honq] at hro; exact Bool.noConfusion hro
    have hclr : carLoc c τ r = carLoc c σ r :=
      carLoc_congr r fun y => hatFrame r y (by simp [hrq])
    refine mem_esList.mpr ⟨mem_waitingLocs.mpr ⟨r, mem_ashore.mpr ⟨hrc, ?_, ?_⟩,
      by rw [hclr]; exact hcx⟩, ?_, ?_⟩
    · rw [hdelR r hrq]; exact hrd
    · rw [honFrame r hrq]; exact hro
    · intro hmem
      obtain ⟨y, hyc, hyd, hyx⟩ := mem_destinations.mp hmem
      by_cases hyq : y = q
      · subst hyq
        exact h2 (mem_destinations.mpr ⟨y, hyc, hundel x hyx, hyx⟩)
      · exact h2 (mem_destinations.mpr ⟨y, hyc, by rw [← hdelR y hyq]; exact hyd, hyx⟩)
    · rintro ⟨-, hc⟩
      rw [hferryLoc] at hc
      have hlx : l = x := by simpa using hc
      exact hxl hlx.symm
  rcases hdd : c.dest q with _ | g
  · -- the car has no destination: its term is zero either way
    have hload : load c σ = load c τ := by
      refine load_congr fun r _ => ?_
      by_cases hrq : r = q
      · subst hrq
        have h1 : delivered c σ r = true := by simp [delivered, hdd]
        have h2 : delivered c τ r = true := by simp [delivered, hdd]
        simp [carCost, h1, h2]
      · exact hcost r hrq
    have hes : emptySails c σ ≤ emptySails c τ + 1 :=
      emptySails_le_succ l fun x hx => by
        by_cases hxl : x = l
        · exact Or.inr hxl
        · exact Or.inl (hesGen x hx hxl)
    have hr1 := repositioning_le_one c σ
    unfold value; omega
  · by_cases hgl : g = l
    · -- the car is put down where it belongs
      subst hgl
      have hdσ : delivered c σ q = false := hundel g hdd
      have hcq : carCost c σ q = 1 := by
        simp [carCost, hdσ, honq, hferryLocσ, hdd]
      have hload : load c σ ≤ load c τ + 1 := by
        refine load_le (q := q) hok.nodup (by rw [hcq]; omega) fun r _ hrq =>
          le_of_eq (hcost r hrq)
      have hes : emptySails c σ ≤ emptySails c τ := by
        refine emptySails_mono fun x hx => ?_
        obtain ⟨-, h2, -⟩ := mem_esList.mp hx
        exact hesGen x hx (by
          rintro rfl
          exact h2 (mem_destinations.mpr ⟨q, hqc, hdσ, hdd⟩))
      -- a reposition forced before the car came off is still forced after
      have hrep1 : repositioning c σ = 1 → repositioning c τ = 1 := by
        intro h1
        unfold repositioning at h1
        have hae : (ashore c σ).isEmpty = false := by
          by_contra hc
          rw [if_pos (by simpa using hc)] at h1
          exact absurd h1 (by simp)
        rw [if_neg (by simp [hae]), if_neg (by simp [hempσ])] at h1
        have hqab : q ∈ aboard c σ := mem_aboard.mpr ⟨hqc, hdσ, honq⟩
        have hcgσ : carriedGoal c σ = some g := by
          unfold carriedGoal
          rcases hg : (aboard c σ).getLast? with _ | r
          · rw [List.getLast?_eq_none_iff] at hg
            rw [hg] at hqab; simp at hqab
          · have hr := List.mem_of_getLast? hg
            obtain ⟨-, -, hro⟩ := mem_aboard.mp hr
            rw [hinv.oneOn r q hro honq]
            simpa using hdd
        rw [hcgσ] at h1
        have h1' : (if (waitingLocs c σ).contains g = true then 0 else 1) = 1 := h1
        have hlnw : g ∉ waitingLocs c σ := by
          intro hc
          rw [if_pos (by simpa using hc)] at h1'
          exact absurd h1' (by simp)
        have hqnash : q ∉ ashore c σ := by
          intro hc
          have := (mem_ashore.mp hc).2.2
          rw [honq] at this; exact Bool.noConfusion this
        have hashsub : ∀ r ∈ ashore c σ, r ∈ ashore c τ := by
          intro r hr
          obtain ⟨hrc, hrd, hro⟩ := mem_ashore.mp hr
          have hrq : r ≠ q := by rintro rfl; exact hqnash hr
          exact mem_ashore.mpr ⟨hrc, by rw [hdelR r hrq]; exact hrd,
            by rw [honFrame r hrq]; exact hro⟩
        have hτne : (ashore c τ).isEmpty = false := by
          rcases hcc : ashore c σ with _ | ⟨a, t⟩
          · rw [hcc] at hae; simp at hae
          · have hm := hashsub a (by rw [hcc]; simp)
            rcases hcc2 : ashore c τ with _ | ⟨b, u⟩
            · rw [hcc2] at hm; simp at hm
            · rfl
        have hwsub : ∀ x ∈ waitingLocs c τ, x ∈ waitingLocs c σ := by
          intro x hx
          obtain ⟨r, hr, hcx⟩ := mem_waitingLocs.mp hx
          obtain ⟨hrc, hrd, hro⟩ := mem_ashore.mp hr
          have hrq : r ≠ q := by
            rintro rfl
            have hxa : τ (atC r x) = true := carLoc_holds hcx
            by_cases hxl : x = g
            · subst hxl
              have : delivered c τ r = true := by unfold delivered; rw [hdd]; exact hxa
              rw [this] at hrd; exact Bool.noConfusion hrd
            · rw [hatFrame r x (by simp [hxl])] at hxa
              rw [hinv.onNotAt r x honq] at hxa; exact Bool.noConfusion hxa
          refine mem_waitingLocs.mpr ⟨r, mem_ashore.mpr ⟨hrc,
            by rw [← hdelR r hrq]; exact hrd, by rw [← honFrame r hrq]; exact hro⟩, ?_⟩
          rw [← carLoc_congr r fun y => hatFrame r y (by simp [hrq])]
          exact hcx
        unfold repositioning
        rw [if_neg (by simp [hτne])]
        by_cases hte : τ emptyFerry = true
        · rw [if_pos hte]
          refine if_neg ?_
          intro hc
          have hcc : (waitingLocs c τ).contains g = true := by
            unfold waitingHere at hc; rw [hferryLoc] at hc; exact hc
          exact hlnw (hwsub g (by simpa using hcc))
        · rw [if_neg hte]
          rcases hcg : carriedGoal c τ with _ | g2
          · rfl
          · exfalso
            obtain ⟨r, hr, -⟩ := carriedGoal_mem hcg
            obtain ⟨-, -, hro⟩ := mem_aboard.mp hr
            have hrq : r ≠ q := by rintro rfl; rw [honqF] at hro; exact Bool.noConfusion hro
            rw [honFrame r hrq] at hro
            exact hrq (hinv.oneOn r q hro honq)
      have hrepLe : repositioning c σ ≤ repositioning c τ := by
        have hb := repositioning_le_one c σ
        rcases Nat.lt_or_ge (repositioning c σ) 1 with h | h
        · omega
        · have := hrep1 (by omega); omega
      unfold value; omega
    · -- the car is put down short of its destination: its term rises
      have hdσ : delivered c σ q = false := hundel g hdd
      have hdτ : delivered c τ q = false := by
        simp only [delivered, hdd]
        rw [hatFrame q g (by simp [hgl])]
        simpa [delivered, hdd] using hdσ
      have hne : ferryLoc c σ ≠ c.dest q := by
        rw [hferryLocσ, hdd]; simp; exact fun hc => hgl hc.symm
      have hcσ : carCost c σ q = 2 := by simp [carCost, hdσ, honq, hne]
      have hcτ : carCost c τ q = 3 := by simp [carCost, hdτ, honqF]
      have hload : load c σ + 1 ≤ load c τ :=
        load_drop hqc hok.nodup (by rw [hcσ, hcτ]) fun r _ hrq => le_of_eq (hcost r hrq)
      have hes : emptySails c σ ≤ emptySails c τ + 1 :=
        emptySails_le_succ l fun x hx => by
          by_cases hxl : x = l
          · exact Or.inr hxl
          · exact Or.inl (hesGen x hx hxl)
      have hr1 := repositioning_le_one c σ
      unfold value; omega

/-! ### Assembly -/

theorem liftedConsistent {d : Domain} {p : Problem} {c : Cfg} (hd : FerryDomain d)
    (hok : CfgOK d p c) (relevance : Bool)
    (hfacts : ∀ o ∈ groundedOps d p relevance, Nonempty (OpFacts d p o))
    (hcost : ∀ o ∈ groundedOps d p relevance, 0 < o.cost) :
    LiftedConsistentOn d p relevance (fun σ => Inv σ) (value c) := by
  intro o ho σ hinv happ
  obtain ⟨hf⟩ := hfacts o ho
  have hc1 := hcost o ho
  rcases instance_shape hd hf.inst with
    ⟨f, g, hs, ha, -, -⟩ | ⟨q, l, hs, ha, hqt, hlt⟩ | ⟨q, l, hs, ha, hqt, hlt⟩
  · have := sail_value hf hs ha hok.nodup hinv; omega
  · have := board_value hd hok hf hs ha hqt hlt hinv happ; omega
  · have := debark_value hd hok hf hs ha hqt hlt hinv happ; omega

theorem invPreserved {d : Domain} {p : Problem} (hd : FerryDomain d) (relevance : Bool)
    (hfacts : ∀ o ∈ groundedOps d p relevance, Nonempty (OpFacts d p o)) :
    ∀ o ∈ groundedOps d p relevance, ∀ σ, Inv σ → o.applicableA σ → Inv (o.applyA σ) :=
  fun o ho σ hinv happ => inv_preserved hd (hfacts o ho).some hinv happ

/--
**Ferry's improved heuristic is goal-aware.**  It is zero at every goal state the
search can reach.
-/
theorem improved_goalAwareOn (d : Domain) (p : Problem) (relevance : Bool)
    (c : Cfg) (hd : FerryDomain d) (hok : CfgOK d p c)
    (hwf : Task.WF (ground d p relevance))
    (hcost : ∀ o ∈ groundedOps d p relevance, 0 < o.cost)
    (hfacts : ∀ o ∈ groundedOps d p relevance, Nonempty (OpFacts d p o))
    (hsub : ∀ q ∈ c.cars, ∀ g, c.dest q = some g → atC q g ∈ p.goal)
    (hdest : ∀ q ∈ c.cars, (c.dest q).isSome)
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hv : State → Nat)
    (hcomp : ComputesOn (ground d p relevance) (fun σ => Inv σ) hv (value c)) :
    (ground d p relevance).GoalAwareOn (Reachable (ground d p relevance)) hv :=
  goalAwareOn_of_lifted d p relevance hwf hcost hv (value c) (fun σ => Inv σ) hcomp
    hinit (invPreserved hd relevance hfacts) (liftedGoalAware c p hsub hdest)

/--
**Ferry's improved heuristic is consistent.**  One action never lowers the value
by more than it costs, on every state the search can reach.
-/
theorem improved_consistentOn (d : Domain) (p : Problem) (relevance : Bool)
    (c : Cfg) (hd : FerryDomain d) (hok : CfgOK d p c)
    (hwf : Task.WF (ground d p relevance))
    (hcost : ∀ o ∈ groundedOps d p relevance, 0 < o.cost)
    (hfacts : ∀ o ∈ groundedOps d p relevance, Nonempty (OpFacts d p o))
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hv : State → Nat)
    (hcomp : ComputesOn (ground d p relevance) (fun σ => Inv σ) hv (value c)) :
    (ground d p relevance).ConsistentOn (Reachable (ground d p relevance)) hv :=
  consistentOn_of_lifted d p relevance hwf hcost hv (value c) (fun σ => Inv σ) hcomp
    hinit (invPreserved hd relevance hfacts)
    (liftedConsistent hd hok relevance hfacts hcost)

/--
**Ferry's improved heuristic is admissible.**  Anything that computes the lifted
value is admissible on every state the search can reach.
-/
theorem improved_admissibleOn (d : Domain) (p : Problem) (relevance : Bool)
    (c : Cfg) (hd : FerryDomain d) (hok : CfgOK d p c)
    (hwf : Task.WF (ground d p relevance))
    (hcost : ∀ o ∈ groundedOps d p relevance, 0 < o.cost)
    (hfacts : ∀ o ∈ groundedOps d p relevance, Nonempty (OpFacts d p o))
    (hsub : ∀ q ∈ c.cars, ∀ g, c.dest q = some g → atC q g ∈ p.goal)
    (hdest : ∀ q ∈ c.cars, (c.dest q).isSome)
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hv : State → Nat)
    (hcomp : ComputesOn (ground d p relevance) (fun σ => Inv σ) hv (value c)) :
    (ground d p relevance).AdmissibleOn (Reachable (ground d p relevance)) hv :=
  admissibleOn_of_lifted d p relevance hwf hcost hv (value c) (fun σ => Inv σ) hcomp
    hinit (invPreserved hd relevance hfacts) (liftedGoalAware c p hsub hdest)
    (liftedConsistent hd hok relevance hfacts hcost)

end Planner.Lifted.Ferry

/- -------------------------------------------------------------------------- -/
/-
What the compiled ferry heuristic must match.

`Computes` is the last obligation: the number `improved t` returns on a packed
state is the number the lifted heuristic returns on the atoms that state stands
for.  `CarMatch` and `FerryMatch` say what the compiled tables have to be for
that, entry by entry, and neither adds anything to the running code — the atom a
stored fact names is recoverable from the task.

Three quantities have to agree, not two: the per-car count, the empty sails, and
the one reposition a waiting car forces.
-/

namespace Planner.Lifted.Ferry

open Planner Planner.Pddl

/-- The compiled heuristic's per-task record. -/
abbrev CData := ExampleHeuristics.Ferry.Data
abbrev CCar := ExampleHeuristics.Ferry.CarInfo

/-- The location a compiled index stands for. -/
def nameOf (c : Cfg) (i : Nat) : Pddl.Name := c.locations.getD i ""

theorem nameOf_mem {c : Cfg} {i : Nat} (h : i < c.locations.length) :
    nameOf c i ∈ c.locations := by
  unfold nameOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

theorem nameOf_inj {c : Cfg} (hnd : c.locations.Nodup) {i j : Nat}
    (hi : i < c.locations.length) (hj : j < c.locations.length)
    (h : nameOf c i = nameOf c j) : i = j := by
  unfold nameOf at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] at h
  exact (List.getElem_inj hnd).mp (by simpa using h)

/-- What one compiled entry must say about one car. -/
structure CarMatch (t : Task) (c : Cfg) (ci : CCar) (q : Pddl.Name) : Prop where
  goalName : t.factNames.getD ci.goalFact default = atC q (nameOf c ci.goalLoc)
  goalRange : ci.goalFact < t.factNames.size
  goalIdx : ci.goalLoc < c.locations.length
  /-- The destination the `Cfg` records is the one the entry indexes. -/
  dest : c.dest q = some (nameOf c ci.goalLoc)
  /-- Each `at` entry names that location's atom, and its index is a real place. -/
  atNames : ∀ x ∈ ci.atFacts,
    t.factNames.getD x.1 default = atC q (nameOf c x.2) ∧ x.1 < t.factNames.size ∧
    x.2 < c.locations.length
  /-- And every location has an entry. -/
  atOnto : ∀ g ∈ c.locations, ∃ x ∈ ci.atFacts, nameOf c x.2 = g
  onSome : ∀ f, ci.onFact = some f →
    t.factNames.getD f default = onC q ∧ f < t.factNames.size
  onNone : ci.onFact = none → ∀ σ : AtomState, σ (onC q) = false

/-- The compiled tables read the same cars as the `Cfg`, entry for entry. -/
def DataMatches (t : Task) (c : Cfg) (dd : CData) : Prop :=
  List.Forall₂ (CarMatch t c) dd.cars.toList c.cars

/-- What the compiled ferry tables must say. -/
structure FerryMatch (t : Task) (c : Cfg) (dd : CData) : Prop where
  nodup : c.locations.Nodup
  carsNodup : c.cars.Nodup
  ferryNames : ∀ x ∈ dd.ferryAt,
    t.factNames.getD x.1 default = atFerry (nameOf c x.2) ∧ x.1 < t.factNames.size ∧
    x.2 < c.locations.length
  ferryOnto : ∀ g ∈ c.locations, ∃ x ∈ dd.ferryAt, nameOf c x.2 = g
  emptySome : ∀ f, dd.emptyFact = some f →
    t.factNames.getD f default = emptyFerry ∧ f < t.factNames.size
  emptyNone : dd.emptyFact = none → ∀ σ : AtomState, σ emptyFerry = false

/-! ### Reading one atom -/

theorem test_eq {t : Task} {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) {f : Fact} {a : GroundAtom}
    (hname : t.factNames.getD f default = a) (hrange : f < t.factNames.size) :
    s.test f = σ a := by
  rw [← hname]
  exact (habs.numbered f (by rw [hn]; exact hrange)).symm

theorem delivered_matches {t : Task} {c : Cfg} {ci : CCar} {q : Pddl.Name}
    (hc : CarMatch t c ci q) {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) : s.test ci.goalFact = delivered c σ q := by
  rw [test_eq habs hn hc.goalName hc.goalRange]
  unfold delivered
  rw [hc.dest]

theorem onBoard_matches {t : Task} {c : Cfg} {ci : CCar} {q : Pddl.Name}
    (hc : CarMatch t c ci q) {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Ferry.onBoard s ci = σ (onC q) := by
  unfold ExampleHeuristics.Ferry.onBoard
  rcases hf : ci.onFact with _ | f
  · rw [hc.onNone hf σ]
  · obtain ⟨hname, hrange⟩ := hc.onSome f hf
    exact test_eq habs hn hname hrange

theorem ferryEmpty_matches {t : Task} {c : Cfg} {dd : CData} (hm : FerryMatch t c dd)
    {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Ferry.ferryEmpty dd s = σ emptyFerry := by
  unfold ExampleHeuristics.Ferry.ferryEmpty
  rcases hf : dd.emptyFact with _ | f
  · rw [hm.emptyNone hf σ]
  · obtain ⟨hname, hrange⟩ := hm.emptySome f hf
    exact test_eq habs hn hname hrange

/-! ### Reading a position -/

/-- Where the ferry is, read compiled or lifted, is the same place. -/
theorem ferryLoc_matches {t : Task} {c : Cfg} {dd : CData} (hm : FerryMatch t c dd)
    {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) (hinv : Inv σ) :
    (ExampleHeuristics.Ferry.ferryLoc dd s).map (nameOf c) = ferryLoc c σ := by
  unfold ExampleHeuristics.Ferry.ferryLoc
  rcases hfind : dd.ferryAt.find? (fun x => s.test x.1) with _ | x
  · rw [hfind]
    simp only [Option.map_none]
    symm
    unfold ferryLoc
    rw [List.find?_eq_none]
    intro g hg
    obtain ⟨y, hy, hyg⟩ := hm.ferryOnto g hg
    obtain ⟨hname, hrange, -⟩ := hm.ferryNames y hy
    have hfalse : s.test y.1 = false := by
      have := Array.find?_eq_none.mp hfind y hy
      simpa using this
    have hσ : σ (atFerry (nameOf c y.2)) = false := by
      rw [← test_eq habs hn hname hrange]; exact hfalse
    rw [hyg] at hσ
    simp [hσ]
  · rw [hfind]
    obtain ⟨hname, hrange, hidx⟩ := hm.ferryNames x (Array.mem_of_find?_eq_some hfind)
    have htrue : σ (atFerry (nameOf c x.2)) = true := by
      rw [← test_eq habs hn hname hrange]
      simpa using Array.find?_some hfind
    simp only [Option.map_some]
    exact (ferryLoc_eq hinv (nameOf_mem hidx) htrue).symm

/-- And where a car stands. -/
theorem carLoc_matches {t : Task} {c : Cfg} {ci : CCar} {q : Pddl.Name}
    (hc : CarMatch t c ci q) (hnd : c.locations.Nodup) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) (hinv : Inv σ) :
    (ExampleHeuristics.Ferry.carLoc s ci).map (nameOf c) = carLoc c σ q := by
  unfold ExampleHeuristics.Ferry.carLoc
  rcases hfind : ci.atFacts.find? (fun x => s.test x.1) with _ | x
  · rw [hfind]
    simp only [Option.map_none]
    symm
    unfold carLoc
    rw [List.find?_eq_none]
    intro g hg
    obtain ⟨y, hy, hyg⟩ := hc.atOnto g hg
    obtain ⟨hname, hrange, -⟩ := hc.atNames y hy
    have hfalse : s.test y.1 = false := by
      have := Array.find?_eq_none.mp hfind y hy
      simpa using this
    have hσ : σ (atC q (nameOf c y.2)) = false := by
      rw [← test_eq habs hn hname hrange]; exact hfalse
    rw [hyg] at hσ
    simp [hσ]
  · rw [hfind]
    obtain ⟨hname, hrange, hidx⟩ := hc.atNames x (Array.mem_of_find?_eq_some hfind)
    have htrue : σ (atC q (nameOf c x.2)) = true := by
      rw [← test_eq habs hn hname hrange]
      simpa using Array.find?_some hfind
    simp only [Option.map_some]
    exact (carLoc_eq hinv (nameOf_mem hidx) htrue).symm

/-- The compiled ferry position, when it names one, names a real place. -/
theorem ferryLoc_range {t : Task} {c : Cfg} {dd : CData} (hm : FerryMatch t c dd)
    {s : State} {k : Nat} (h : ExampleHeuristics.Ferry.ferryLoc dd s = some k) :
    k < c.locations.length := by
  unfold ExampleHeuristics.Ferry.ferryLoc at h
  rcases hfind : dd.ferryAt.find? (fun x => s.test x.1) with _ | x
  · rw [hfind] at h; simp at h
  · rw [hfind] at h
    simp only [Option.map_some, Option.some.injEq] at h
    obtain ⟨-, -, hidx⟩ := hm.ferryNames x (Array.mem_of_find?_eq_some hfind)
    rw [← h]; exact hidx

theorem carLoc_range {t : Task} {c : Cfg} {ci : CCar} {q : Pddl.Name}
    (hc : CarMatch t c ci q) {s : State} {k : Nat}
    (h : ExampleHeuristics.Ferry.carLoc s ci = some k) : k < c.locations.length := by
  unfold ExampleHeuristics.Ferry.carLoc at h
  rcases hfind : ci.atFacts.find? (fun x => s.test x.1) with _ | x
  · rw [hfind] at h; simp at h
  · rw [hfind] at h
    simp only [Option.map_some, Option.some.injEq] at h
    obtain ⟨-, -, hidx⟩ := hc.atNames x (Array.mem_of_find?_eq_some hfind)
    rw [← h]; exact hidx

/-! ### The per-car sum -/

/-- The compiled per-car term, in the shape `carCost` has. -/
def ccost (dd : CData) (s : State) (ci : CCar) : Nat :=
  if s.test ci.goalFact then 0
  else if ExampleHeuristics.Ferry.onBoard s ci then
    (if ExampleHeuristics.Ferry.ferryLoc dd s == some ci.goalLoc then 1 else 2)
  else 3

/-- The two compiled pieces are one sum, exactly as `load` is. -/
theorem compiled_load (dd : CData) (s : State) :
    ExampleHeuristics.Ferry.ashore dd s + ExampleHeuristics.Ferry.aboard dd s
      = (dd.cars.toList.map (ccost dd s)).sum := by
  rw [ExampleHeuristics.Ferry.ashore_eq, ExampleHeuristics.Ferry.aboard_eq]
  unfold ExampleHeuristics.Ferry.waitP ExampleHeuristics.Ferry.rideP ccost
  induction dd.cars.toList with
  | nil => rfl
  | cons ci rest ih =>
      by_cases hg : s.test ci.goalFact
      · simp only [List.filter_cons, hg, List.map_cons, List.sum_cons]
        simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, if_false,
          if_true, reduceIte]
        omega
      · by_cases hb : ExampleHeuristics.Ferry.onBoard s ci
        · simp only [List.filter_cons, hg, hb, List.map_cons, List.sum_cons,
            Bool.false_eq_true, if_false, if_true, Bool.not_false, Bool.not_true,
            Bool.and_true, Bool.and_false, List.length_cons]
          omega
        · simp only [List.filter_cons, hg, hb, List.map_cons, List.sum_cons,
            Bool.false_eq_true, if_false, if_true, Bool.not_false, Bool.not_true,
            Bool.and_true, Bool.and_false, List.length_cons]
          omega

/-- Asking whether the ferry stands at a car's destination is the same question
either way. -/
theorem atGoal_matches {t : Task} {c : Cfg} {dd : CData} {ci : CCar} {q : Pddl.Name}
    (hm : FerryMatch t c dd) (hc : CarMatch t c ci q) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) (hinv : Inv σ) :
    (ExampleHeuristics.Ferry.ferryLoc dd s == some ci.goalLoc)
      = decide (ferryLoc c σ = c.dest q) := by
  have hfl := ferryLoc_matches hm habs hn hinv
  rcases hf : ExampleHeuristics.Ferry.ferryLoc dd s with _ | k
  · rw [hf] at hfl
    simp only [Option.map_none] at hfl
    rw [← hfl, hc.dest]
    simp
  · rw [hf] at hfl
    simp only [Option.map_some] at hfl
    rw [← hfl, hc.dest]
    have hkr := ferryLoc_range hm hf
    by_cases hk : k = ci.goalLoc
    · subst hk; simp
    · have hne : nameOf c k ≠ nameOf c ci.goalLoc := fun hcc =>
        hk (nameOf_inj hm.nodup hkr hc.goalIdx hcc)
      simp [hk, hne]

/-- Entry for entry, the compiled per-car sum is the lifted one. -/
theorem load_lists {t : Task} {c : Cfg} {dd : CData} (hm : FerryMatch t c dd)
    {l : List CCar} {qs : List Pddl.Name} (hp : List.Forall₂ (CarMatch t c) l qs)
    {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) (hinv : Inv σ) :
    (l.map (ccost dd s)).sum = (qs.map (carCost c σ)).sum := by
  induction hp with
  | nil => rfl
  | @cons ci q rest1 rest2 hc _ ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      congr 1
      unfold ccost carCost
      rw [delivered_matches hc habs hn, onBoard_matches hc habs hn,
        atGoal_matches hm hc habs hn hinv]
      simp

theorem load_matches {t : Task} {c : Cfg} {dd : CData} (hm : FerryMatch t c dd)
    (hdm : DataMatches t c dd) {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) (hinv : Inv σ) :
    ExampleHeuristics.Ferry.ashore dd s + ExampleHeuristics.Ferry.aboard dd s
      = load c σ := by
  rw [compiled_load]
  exact load_lists hm hdm habs hn hinv

/-! ### Pairing the two lists -/

/-- The pairing survives the two filters the heuristic takes. -/
theorem ashore_pairs {t : Task} {c : Cfg} {dd : CData} (hdm : DataMatches t c dd)
    {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) :
    List.Forall₂ (CarMatch t c) (ExampleHeuristics.Ferry.ashoreCars dd s).toList
      (ashore c σ) := by
  rw [ExampleHeuristics.Ferry.ashoreCars_toList]
  unfold ExampleHeuristics.Ferry.waitP ashore
  refine forall₂_filter hdm fun ci q hc => ?_
  rw [delivered_matches hc habs hn, onBoard_matches hc habs hn]
  simp [Bool.and_comm]

theorem aboard_pairs {t : Task} {c : Cfg} {dd : CData} (hdm : DataMatches t c dd)
    {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) :
    List.Forall₂ (CarMatch t c) (ExampleHeuristics.Ferry.aboardCars dd s).toList
      (aboard c σ) := by
  show List.Forall₂ _ ((ExampleHeuristics.Ferry.unmetCars dd s).filter _).toList _
  unfold ExampleHeuristics.Ferry.unmetCars aboard
  rw [Array.toList_filter, Array.toList_filter, List.filter_filter]
  refine forall₂_filter hdm fun ci q hc => ?_
  rw [delivered_matches hc habs hn, onBoard_matches hc habs hn]
  simp [Bool.and_comm]

theorem unmet_pairs {t : Task} {c : Cfg} {dd : CData} (hdm : DataMatches t c dd)
    {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) :
    List.Forall₂ (CarMatch t c) (ExampleHeuristics.Ferry.unmetCars dd s).toList
      (c.cars.filter fun q => !delivered c σ q) := by
  unfold ExampleHeuristics.Ferry.unmetCars
  rw [Array.toList_filter]
  refine forall₂_filter hdm fun ci q hc => ?_
  rw [delivered_matches hc habs hn]

/-! ### The two location sets -/

section Sets
variable {t : Task} {c : Cfg} {dd : CData} {s : State} {σ : AtomState}

theorem waitingLocs_into (hdm : DataMatches t c dd) (hnd : c.locations.Nodup)
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) (hinv : Inv σ) :
    ∀ k ∈ ExampleHeuristics.Ferry.waitingLocs dd s,
      k < c.locations.length ∧ nameOf c k ∈ waitingLocs c σ := by
  intro k hk
  obtain ⟨ci, hci, hw, hcx⟩ := ExampleHeuristics.Ferry.mem_waitingLocs.mp hk
  obtain ⟨q, hq, hc⟩ := forall₂_mem_left hdm (by simpa using hci)
  simp only [ExampleHeuristics.Ferry.waitP, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true] at hw
  refine ⟨carLoc_range hc hcx, ?_⟩
  refine mem_waitingLocs.mpr ⟨q, mem_ashore.mpr ⟨hq, ?_, ?_⟩, ?_⟩
  · rw [← delivered_matches hc habs hn]; exact hw.2
  · rw [← onBoard_matches hc habs hn]; exact hw.1
  · rw [← carLoc_matches hc hnd habs hn hinv, hcx]; rfl

theorem waitingLocs_onto (hdm : DataMatches t c dd) (hnd : c.locations.Nodup)
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) (hinv : Inv σ) :
    ∀ g ∈ waitingLocs c σ, ∃ k ∈ ExampleHeuristics.Ferry.waitingLocs dd s,
      nameOf c k = g := by
  intro g hg
  obtain ⟨q, hq, hcx⟩ := mem_waitingLocs.mp hg
  obtain ⟨hqc, hqd, hqo⟩ := mem_ashore.mp hq
  obtain ⟨ci, hci, hc⟩ := forall₂_mem_right hdm hqc
  have hml := carLoc_matches hc hnd habs hn hinv
  rw [hcx] at hml
  rcases hcl : ExampleHeuristics.Ferry.carLoc s ci with _ | k
  · rw [hcl] at hml; simp at hml
  · rw [hcl] at hml
    simp only [Option.map_some, Option.some.injEq] at hml
    refine ⟨k, ExampleHeuristics.Ferry.mem_waitingLocs.mpr ⟨ci, by simpa using hci, ?_, hcl⟩,
      hml⟩
    simp only [ExampleHeuristics.Ferry.waitP, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true]
    exact ⟨by rw [onBoard_matches hc habs hn]; exact hqo,
      by rw [delivered_matches hc habs hn]; exact hqd⟩

theorem destinations_into (hdm : DataMatches t c dd)
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    ∀ k ∈ ExampleHeuristics.Ferry.destinations dd s,
      k < c.locations.length ∧ nameOf c k ∈ destinations c σ := by
  intro k hk
  obtain ⟨ci, hci, hl, hgl⟩ := ExampleHeuristics.Ferry.mem_destinations.mp hk
  obtain ⟨q, hq, hc⟩ := forall₂_mem_left hdm (by simpa using hci)
  subst hgl
  refine ⟨hc.goalIdx, mem_destinations.mpr ⟨q, hq, ?_, hc.dest⟩⟩
  rw [← delivered_matches hc habs hn]
  simpa [ExampleHeuristics.Ferry.live] using hl

theorem destinations_onto (hdm : DataMatches t c dd)
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    ∀ g ∈ destinations c σ, ∃ k ∈ ExampleHeuristics.Ferry.destinations dd s,
      nameOf c k = g := by
  intro g hg
  obtain ⟨q, hqc, hqd, hqg⟩ := mem_destinations.mp hg
  obtain ⟨ci, hci, hc⟩ := forall₂_mem_right hdm hqc
  have hgl : nameOf c ci.goalLoc = g := by
    have := hc.dest; rw [hqg] at this; exact (Option.some.injEq _ _ ▸ this).symm
  refine ⟨ci.goalLoc, ExampleHeuristics.Ferry.mem_destinations.mpr
    ⟨ci, by simpa using hci, ?_, rfl⟩, hgl⟩
  simp only [ExampleHeuristics.Ferry.live, Bool.not_eq_eq_eq_not, Bool.not_true]
  rw [delivered_matches hc habs hn]; exact hqd

theorem wl_contains (hdm : DataMatches t c dd) (hnd : c.locations.Nodup)
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) (hinv : Inv σ)
    {k : Nat} (hk : k < c.locations.length) :
    (ExampleHeuristics.Ferry.waitingLocs dd s).contains k
      = (waitingLocs c σ).contains (nameOf c k) := by
  by_cases h : k ∈ ExampleHeuristics.Ferry.waitingLocs dd s
  · have := (waitingLocs_into hdm hnd habs hn hinv k h).2
    simp [h, this]
  · have hno : nameOf c k ∉ waitingLocs c σ := by
      intro hc
      obtain ⟨k', hk', hname⟩ := waitingLocs_onto hdm hnd habs hn hinv _ hc
      have hkr := (waitingLocs_into hdm hnd habs hn hinv k' hk').1
      exact h (nameOf_inj hnd hkr hk hname ▸ hk')
    simp [h, hno]

theorem dest_contains (hdm : DataMatches t c dd) (hnd : c.locations.Nodup)
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size)
    {k : Nat} (hk : k < c.locations.length) :
    (ExampleHeuristics.Ferry.destinations dd s).contains k
      = (destinations c σ).contains (nameOf c k) := by
  by_cases h : k ∈ ExampleHeuristics.Ferry.destinations dd s
  · have := (destinations_into hdm habs hn k h).2
    simp [h, this]
  · have hno : nameOf c k ∉ destinations c σ := by
      intro hc
      obtain ⟨k', hk', hname⟩ := destinations_onto hdm habs hn _ hc
      have hkr := (destinations_into hdm habs hn k' hk').1
      exact h (nameOf_inj hnd hkr hk hname ▸ hk')
    simp [h, hno]

end Sets

/-! ### The empty sails, and the forced reposition -/

section Value
variable {t : Task} {c : Cfg} {dd : CData} {s : State} {σ : AtomState}

/-- Asking whether the ferry stands at an indexed place is the same question
either way. -/
theorem ferryAt_k (hm : FerryMatch t c dd) (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) (hinv : Inv σ)
    {k : Nat} (hk : k < c.locations.length) :
    (ExampleHeuristics.Ferry.ferryLoc dd s == some k)
      = decide (ferryLoc c σ = some (nameOf c k)) := by
  have hfl := ferryLoc_matches hm habs hn hinv
  rcases hf : ExampleHeuristics.Ferry.ferryLoc dd s with _ | j
  · rw [hf] at hfl; simp only [Option.map_none] at hfl
    rw [← hfl]; simp
  · rw [hf] at hfl; simp only [Option.map_some] at hfl
    rw [← hfl]
    have hjr := ferryLoc_range hm hf
    by_cases hjk : j = k
    · subst hjk; simp
    · have hne : nameOf c j ≠ nameOf c k := fun hcc =>
        hjk (nameOf_inj hm.nodup hjr hk hcc)
      simp [hjk, hne]

/-- **The empty-sail counts agree.** -/
theorem emptySails_matches (hm : FerryMatch t c dd) (hdm : DataMatches t c dd)
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) (hinv : Inv σ) :
    ExampleHeuristics.Ferry.emptySails dd s = emptySails c σ := by
  have hemp := ferryEmpty_matches hm habs hn
  refine length_eq_of_naming _ _ (nameOf c)
    ((distinct_nodup _).filter _) (esList_nodup c σ) ?_ ?_ ?_
  · intro i hi j hj hij
    rw [List.mem_filter] at hi hj
    exact nameOf_inj hm.nodup (waitingLocs_into hdm hm.nodup habs hn hinv i hi.1).1
      (waitingLocs_into hdm hm.nodup habs hn hinv j hj.1).1 hij
  · intro k hk
    rw [List.mem_filter] at hk
    obtain ⟨hkw, hkp⟩ := hk
    obtain ⟨hkr, hkl⟩ := waitingLocs_into hdm hm.nodup habs hn hinv k hkw
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hkp
    refine mem_esList.mpr ⟨hkl, ?_, ?_⟩
    · have hc2 : (destinations c σ).contains (nameOf c k) = false := by
        rw [← dest_contains hdm hm.nodup habs hn hkr]; exact hkp.1
      simpa using hc2
    · rintro ⟨he, hfl⟩
      rw [← hemp] at he
      have : (ExampleHeuristics.Ferry.ferryLoc dd s == some k) = true := by
        rw [ferryAt_k hm habs hn hinv hkr]; simpa using hfl
      rw [he, this] at hkp
      simp at hkp
  · intro g hg
    obtain ⟨hgw, hgd, hgf⟩ := mem_esList.mp hg
    obtain ⟨k, hk, hkg⟩ := waitingLocs_onto hdm hm.nodup habs hn hinv g hgw
    have hkr := (waitingLocs_into hdm hm.nodup habs hn hinv k hk).1
    refine ⟨k, ?_, hkg⟩
    rw [List.mem_filter]
    refine ⟨hk, ?_⟩
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
    constructor
    · rw [dest_contains hdm hm.nodup habs hn hkr, hkg]
      simpa using hgd
    · rw [ferryAt_k hm habs hn hinv hkr, hkg]
      by_cases he : ExampleHeuristics.Ferry.ferryEmpty dd s
      · have heσ : σ emptyFerry = true := by rw [← hemp]; exact he
        simp only [he, Bool.true_and, decide_eq_false_iff_not]
        exact fun hcc => hgf ⟨heσ, hcc⟩
      · simp [he]

theorem waitingHere_matches (hm : FerryMatch t c dd) (hdm : DataMatches t c dd)
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) (hinv : Inv σ) :
    ExampleHeuristics.Ferry.waitingHere dd s = waitingHere c σ := by
  unfold ExampleHeuristics.Ferry.waitingHere waitingHere
  have hfl := ferryLoc_matches hm habs hn hinv
  rcases hf : ExampleHeuristics.Ferry.ferryLoc dd s with _ | k
  · rw [hf] at hfl; simp only [Option.map_none] at hfl
    rw [← hfl]
  · rw [hf] at hfl; simp only [Option.map_some] at hfl
    rw [← hfl]
    exact wl_contains hdm hm.nodup habs hn hinv (ferryLoc_range hm hf)

theorem ashore_isEmpty (hdm : DataMatches t c dd) (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) :
    (ExampleHeuristics.Ferry.ashoreCars dd s).isEmpty = (ashore c σ).isEmpty := by
  have hlen := (ashore_pairs hdm habs hn).length_eq
  rw [← Array.isEmpty_toList]
  rcases h1 : (ExampleHeuristics.Ferry.ashoreCars dd s).toList with _ | ⟨a, l1⟩ <;>
    rcases h2 : ashore c σ with _ | ⟨b, l2⟩
  · rfl
  · rw [h1, h2] at hlen; simp at hlen
  · rw [h1, h2] at hlen; simp at hlen
  · rfl

/-- **The forced repositions agree.** -/
theorem repositioning_matches (hm : FerryMatch t c dd) (hdm : DataMatches t c dd)
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) (hinv : Inv σ) :
    ExampleHeuristics.Ferry.repositioning dd s = repositioning c σ := by
  unfold ExampleHeuristics.Ferry.repositioning repositioning
  rw [ashore_isEmpty hdm habs hn]
  by_cases hae : (ashore c σ).isEmpty
  · rw [if_pos hae, if_pos hae]
  · rw [if_neg hae, if_neg hae, ferryEmpty_matches hm habs hn]
    by_cases he : σ emptyFerry
    · rw [if_pos he, if_pos he, waitingHere_matches hm hdm habs hn hinv]
    · rw [if_neg he, if_neg he]
      unfold ExampleHeuristics.Ferry.carriedGoal carriedGoal
      rw [← Array.getLast?_toList]
      rcases forall₂_getLast? (aboard_pairs hdm habs hn) with ⟨h1, h2⟩ | ⟨ci, q, h1, h2, hc⟩
      · rw [h1, h2]; rfl
      · rw [h1, h2]
        simp only [Option.map_some, Option.bind_some, hc.dest]
        rw [wl_contains hdm hm.nodup habs hn hinv hc.goalIdx]

/-! ### `Computes`, for ferry -/

/--
**The compiled ferry heuristic computes the lifted one.**  All three quantities:
the per-car count, the empty sails, and the forced reposition.
-/
theorem computes (hm : FerryMatch t c dd) (hdm : DataMatches t c dd)
    (hn : t.numFacts = t.factNames.size) :
    ComputesOn t (fun σ => Inv σ) (ExampleHeuristics.Ferry.value dd) (value c) := by
  intro s σ habs hinv
  show ExampleHeuristics.Ferry.ashore dd s + ExampleHeuristics.Ferry.aboard dd s
    + max (ExampleHeuristics.Ferry.repositioning dd s)
        (ExampleHeuristics.Ferry.emptySails dd s) = _
  rw [load_matches hm hdm habs hn hinv, repositioning_matches hm hdm habs hn hinv,
    emptySails_matches hm hdm habs hn hinv]
  rfl

end Value

end Planner.Lifted.Ferry

/- -------------------------------------------------------------------------- -/
/-
What `compile` produces for a ferry task.

`Proofs/Lifted/FerryComputes.lean` proves the compiled heuristic computes the
lifted one *given* `FerryMatch` and `DataMatches` — a statement about the record
`compile` returns.  This file discharges them, so that ferry's chain runs from a
domain and a problem file to admissibility with nothing assumed about the
heuristic in between.

Two ingredients meet here.  `Proofs/FactTables.lean` says what the accessors
return, which gives the fields that name atoms and bound indices.  The fields that
say a table is *complete* — every location has an `at-ferry` entry, every location
has an `at` entry for each car — need to know that those atoms were numbered at
all, and that is `Proofs/GroundingComplete.lean`.

Grounding is used without the relevance analysis.  Pruning can drop a whole
operator, and with it the only mention of an atom, so the statement would need the
fixpoint's set supplied per task; `ground_names_instance_pruned` is where that
lives.
-/

namespace Planner.Lifted.Ferry

open Planner Planner.Pddl

/-! ### What one decidable pass over the problem establishes

Every field below is a property of the parsed domain and problem, decidable and
checked once.  Three of them — distinct object names, well-typed goal atoms, and
a goal that names each car once — are consequences of `validateProblem`; mining
them out of its `Except` monad is not done, so they are asked for here.
-/

/-- The `at` goals of the problem, as (car, destination) pairs. -/
def goalPairs (p : Problem) : List (Name × Name) :=
  p.goal.filterMap fun a =>
    match a.pred == "at", a.args with
    | true, [q, g] => some (q, g)
    | _, _ => none

/-! ### A decidable test for the invariant on `:init`

`Inv` quantifies over every name, so it is not decidable as it stands.  On the
initial state it is, because only the atoms `:init` lists hold: the three lists
below are what the state says, and the check reads them.
-/

/-- The `at` atoms of `:init`, as (car, place) pairs. -/
def atPairs (p : Problem) : List (Name × Name) :=
  p.init.filterMap fun a =>
    match a.pred == "at", a.args with
    | true, [q, f] => some (q, f)
    | _, _ => none

/-- The cars `:init` puts aboard. -/
def onCars (p : Problem) : List Name :=
  p.init.filterMap fun a =>
    match a.pred == "on", a.args with
    | true, [q] => some q
    | _, _ => none

/-- The places `:init` puts the ferry. -/
def ferryPlaces (p : Problem) : List Name :=
  p.init.filterMap fun a =>
    match a.pred == "at-ferry", a.args with
    | true, [f] => some f
    | _, _ => none

/-- The ferry stands in one place, each car in one place, at most one car is
aboard, an empty ferry carries none, and a car aboard stands nowhere. -/
def initInvCheck (p : Problem) : Bool :=
  (ferryPlaces p).all (fun f => (ferryPlaces p).all fun g => f == g) &&
  (atPairs p).all (fun x => (atPairs p).all fun y => !(x.1 == y.1) || x.2 == y.2) &&
  (onCars p).all (fun q => (onCars p).all fun r => q == r) &&
  (!p.init.contains emptyFerry || (onCars p).isEmpty) &&
  (onCars p).all fun q => (atPairs p).all fun x => x.1 != q

theorem mem_ferryPlaces {p : Problem} {f : Name} :
    f ∈ ferryPlaces p ↔ atFerry f ∈ p.init := by
  constructor
  · intro h
    rw [ferryPlaces, List.mem_filterMap] at h
    obtain ⟨a, ha, hval⟩ := h
    by_cases hpred : (a.pred == "at-ferry") = true
    · rcases hargs : a.args with _ | ⟨f', rest⟩
      · simp [hpred, hargs] at hval
      · cases rest with
        | cons _ _ => simp [hpred, hargs] at hval
        | nil =>
            simp only [hpred, hargs, Option.some.injEq] at hval
            have : a = atFerry f := by
              show a = { pred := "at-ferry", args := [f] }
              rw [← hval, ← hargs, ← (by simpa using hpred : a.pred = "at-ferry")]
            rwa [← this]
    · simp only [Bool.not_eq_true] at hpred
      simp [hpred] at hval
  · intro h
    exact List.mem_filterMap.mpr ⟨atFerry f, h, by simp [atFerry]⟩

theorem mem_onCars {p : Problem} {q : Name} : q ∈ onCars p ↔ onC q ∈ p.init := by
  constructor
  · intro h
    rw [onCars, List.mem_filterMap] at h
    obtain ⟨a, ha, hval⟩ := h
    by_cases hpred : (a.pred == "on") = true
    · rcases hargs : a.args with _ | ⟨q', rest⟩
      · simp [hpred, hargs] at hval
      · cases rest with
        | cons _ _ => simp [hpred, hargs] at hval
        | nil =>
            simp only [hpred, hargs, Option.some.injEq] at hval
            have : a = onC q := by
              show a = { pred := "on", args := [q] }
              rw [← hval, ← hargs, ← (by simpa using hpred : a.pred = "on")]
            rwa [← this]
    · simp only [Bool.not_eq_true] at hpred
      simp [hpred] at hval
  · intro h
    exact List.mem_filterMap.mpr ⟨onC q, h, by simp [onC]⟩

theorem mem_atPairs {p : Problem} {q f : Name} :
    (q, f) ∈ atPairs p ↔ atC q f ∈ p.init := by
  constructor
  · intro h
    rw [atPairs, List.mem_filterMap] at h
    obtain ⟨a, ha, hval⟩ := h
    by_cases hpred : (a.pred == "at") = true
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
                have : a = atC q f := by
                  show a = { pred := "at", args := [q, f] }
                  rw [← e1, ← e2, ← hargs, ← (by simpa using hpred : a.pred = "at")]
                rwa [← this]
    · simp only [Bool.not_eq_true] at hpred
      simp [hpred] at hval
  · intro h
    exact List.mem_filterMap.mpr ⟨atC q f, h, by simp [atC]⟩

theorem initInv_of_check {p : Problem} (h : initInvCheck p = true) :
    Inv (fun a => p.init.toArray.contains a) := by
  simp only [initInvCheck, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f g hf hg
    have := h1 f (mem_ferryPlaces.mpr (by simpa using hf))
    simpa using this g (mem_ferryPlaces.mpr (by simpa using hg))
  · intro q f g hf hg
    have := h2 (q, f) (mem_atPairs.mpr (by simpa using hf))
    simpa using this (q, g) (mem_atPairs.mpr (by simpa using hg))
  · intro q r hq hr
    have := h3 q (mem_onCars.mpr (by simpa using hq))
    simpa using this r (mem_onCars.mpr (by simpa using hr))
  · intro he q
    rcases hq : (p.init.toArray.contains (onC q)) with _ | _
    · rfl
    · exfalso
      have hmem : q ∈ onCars p := mem_onCars.mpr (by simpa using hq)
      have hcon : p.init.contains emptyFerry = true := by simpa using he
      rw [hcon] at h4
      simp only [Bool.not_true, Bool.false_or, List.isEmpty_iff] at h4
      rw [h4] at hmem
      simp at hmem
  · intro q l hq
    rcases hl : (p.init.toArray.contains (atC q l)) with _ | _
    · rfl
    · exfalso
      have := h5 q (mem_onCars.mpr (by simpa using hq))
      have := this (q, l) (mem_atPairs.mpr (by simpa using hl))
      simp at this

structure FerryPinned (d : Domain) (p : Problem) : Prop where
  /-- The domain is ferry. -/
  domain : FerryDomain d
  /-- Both parameter types are declared. -/
  carType : "car" ∈ d.typeNames
  locType : "location" ∈ d.typeNames
  /-- Parser validation supplies shared facts such as object-name uniqueness. -/
  validated : Validated d p
  /-- The problem has a location.  Without one the ferry has nowhere to be. -/
  someLoc : ∃ o ∈ allObjects d p, o.type = "location"
  /-- The problem has a car. -/
  someCar : ∃ o ∈ allObjects d p, o.type = "car"
  /-- Every `at` goal names a car and a location.  `validateProblem` checks it. -/
  goalTyped : ∀ x ∈ goalPairs p,
    (∃ o ∈ allObjects d p, o.name = x.1 ∧ o.type = "car") ∧
    (∃ o ∈ allObjects d p, o.name = x.2 ∧ o.type = "location")
  /-- The goal names each car once. -/
  goalNodup : (goalPairs p).Nodup ∧ ((goalPairs p).map (·.1)).Nodup
  /-- Every car has a destination goal. -/
  carGoal : ∀ o ∈ allObjects d p, o.type = "car" → ∃ x ∈ goalPairs p, x.1 = o.name
  /-- Neither type has a subtype among the objects. -/
  locExact : ∀ o ∈ allObjects d p, d.isSubtype o.type "location" = true → o.type = "location"
  carExact : ∀ o ∈ allObjects d p, d.isSubtype o.type "car" = true → o.type = "car"
  /-- `:init` satisfies the invariant the value reads positions under. -/
  initCheck : initInvCheck p = true

/-! ### The task, and where its locations come from -/

/-- The places the compiled heuristic indexes. -/
abbrev locs (t : Task) : Array Name := t.objectsOfTypes ["location"]

theorem locs_wellTyped {d : Domain} {p : Problem} {l : Name}
    (h : l ∈ locs (taskOf d p rel)) : WellTyped d (allObjects d p) "location" l :=
  objsOf_wellTyped h

/-! ### An instance of each schema, built to order -/

theorem notAtFerry_dynamic {d : Domain} (hd : FerryDomain d) :
    (staticPredicates d).contains "not-at-ferry" = false :=
  not_static_of_mem_del (a := sailA) (by rw [hd]; simp) (y := notAtFerryV "?to")
    (by simp [sailA])

/-- Ferry has no static precondition, so an instance never has one to check. -/
theorem no_static {d : Domain} (hd : FerryDomain d) {a : Action} (ha : a ∈ d.actions)
    {y : Atom} (hy : y ∈ a.pre) : (staticPredicates d).contains y.pred = false := by
  rw [hd] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · rcases (by simpa [sailA] using hy : y = atFerryV "?from" ∨ y = notAtFerryV "?to") with
      rfl | rfl
    · exact atFerry_dynamic hd
    · exact notAtFerry_dynamic hd
  · rcases (by simpa [boardA] using hy :
      y = atV "?car" "?loc" ∨ y = atFerryV "?loc" ∨ y = emptyV) with rfl | rfl | rfl
    · exact at_dynamic hd
    · exact atFerry_dynamic hd
    · exact empty_dynamic hd
  · rcases (by simpa [debarkA] using hy : y = onV "?car" ∨ y = atFerryV "?loc") with rfl | rfl
    · exact on_dynamic hd
    · exact atFerry_dynamic hd

/-- One `sail`, between any two locations. -/
def sailInst {d : Domain} {p : Problem} (hd : FerryDomain d) {l1 l2 : Name}
    (h1 : WellTyped d (allObjects d p) "location" l1)
    (h2 : WellTyped d (allObjects d p) "location" l2) : Instance d (allObjects d p) where
  schema := sailA
  mem := by rw [hd]; simp
  args := [l1, l2]
  typed := by
    refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil)
    · exact h1
    · exact h2

/-- One `debark`, for any car at any location. -/
def debarkInst {d : Domain} {p : Problem} (hd : FerryDomain d) {q l : Name}
    (h1 : WellTyped d (allObjects d p) "car" q)
    (h2 : WellTyped d (allObjects d p) "location" l) : Instance d (allObjects d p) where
  schema := debarkA
  mem := by rw [hd]; simp
  args := [q, l]
  typed := List.Forall₂.cons h1 (List.Forall₂.cons h2 List.Forall₂.nil)

/-- One `board`, for any car at any location. -/
def boardInst {d : Domain} {p : Problem} (hd : FerryDomain d) {q l : Name}
    (h1 : WellTyped d (allObjects d p) "car" q)
    (h2 : WellTyped d (allObjects d p) "location" l) : Instance d (allObjects d p) where
  schema := boardA
  mem := by rw [hd]; simp
  args := [q, l]
  typed := by
    refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil)
    · exact h1
    · exact h2

/-- Every parameter of a ferry schema has a declared type. -/
theorem inst_hty {d : Domain} {p : Problem} (hd : FerryDomain d)
    (hcar : "car" ∈ d.typeNames) (hloc : "location" ∈ d.typeNames)
    (i : Instance d (allObjects d p)) : ∀ pm ∈ i.schema.params, pm.type ∈ d.typeNames := by
  intro pm hpm
  have hmem : i.schema ∈ [sailA, boardA, debarkA] := hd ▸ i.mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  have hpm' : pm.type = "location" ∨ pm.type = "car" := by
    rcases hmem with h | h | h <;> rw [h] at hpm <;>
      simp only [sailA, boardA, debarkA, locP, carP, List.mem_cons,
        List.not_mem_nil, or_false] at hpm <;>
      rcases hpm with rfl | rfl <;> simp
  rcases hpm' with hh | hh <;> rw [hh]
  · exact hloc
  · exact hcar

/-- And ferry has no static precondition to check. -/
theorem inst_hstat {d : Domain} {p : Problem} (hd : FerryDomain d)
    (i : Instance d (allObjects d p)) :
    ∀ y ∈ i.schema.pre, (staticPredicates d).contains y.pred = true →
      instAtom i.schema.params i.args y ∈ p.init := by
  intro z hz hc
  rw [no_static hd i.mem hz] at hc
  exact absurd hc (by simp)

/-- Every atom an instance of a ferry schema mentions is numbered. -/
theorem named_of_instance {d : Domain} {p : Problem} (hd : FerryDomain d)
    (hcar : "car" ∈ d.typeNames) (hloc : "location" ∈ d.typeNames)
    (i : Instance d (allObjects d p)) {y : Atom}
    (hy : y ∈ i.schema.pre ∨ y ∈ i.schema.add ∨ y ∈ i.schema.del) :
    ∃ f, f < (taskOf d p false).numFacts ∧
      (taskOf d p false).factNames.getD f default = instAtom i.schema.params i.args y := by
  refine ground_names_instance d p i (inst_hty hd hcar hloc i) (inst_hstat hd i) ?_
  rcases hy with h | h | h
  · exact Or.inl ⟨h, no_static hd i.mem h⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-! ### The four atoms the heuristic reads, all numbered

`FerryNumbered` is what the tables need of the task: every atom the heuristic ever
looks up has a fact.  With pruning off it follows from grounding completeness
alone.  With pruning on it follows from the relevance analysis's own closure,
proved further down.
-/

structure FerryNumbered (d : Domain) (p : Problem) (rel : Bool) : Prop where
  atFerryF : ∀ l, WellTyped d (allObjects d p) "location" l →
    ∃ f, f < (taskOf d p rel).numFacts ∧
      (taskOf d p rel).factNames.getD f default = atFerry l
  atCF : ∀ q l, WellTyped d (allObjects d p) "car" q →
    WellTyped d (allObjects d p) "location" l →
    ∃ f, f < (taskOf d p rel).numFacts ∧
      (taskOf d p rel).factNames.getD f default = atC q l
  onCF : ∀ q, WellTyped d (allObjects d p) "car" q →
    ∃ f, f < (taskOf d p rel).numFacts ∧
      (taskOf d p rel).factNames.getD f default = onC q
  emptyF : ∃ f, f < (taskOf d p rel).numFacts ∧
    (taskOf d p rel).factNames.getD f default = emptyFerry

section Named

variable {d : Domain} {p : Problem} (hd : FerryDomain d)
  (hcar : "car" ∈ d.typeNames) (hloc : "location" ∈ d.typeNames)

include hd hcar hloc

theorem atFerry_named {l : Name} (hl : WellTyped d (allObjects d p) "location" l) :
    ∃ f, f < (taskOf d p false).numFacts ∧
      (taskOf d p false).factNames.getD f default = atFerry l := by
  have h := named_of_instance hd hcar hloc (sailInst (p := p) hd hl hl)
    (y := atFerryV "?to") (Or.inr (Or.inl (by simp [sailInst, sailA])))
  simpa [sailInst, instAtom, sailA, locP, atFerryV, atFerry] using h

theorem at_named {q l : Name} (hq : WellTyped d (allObjects d p) "car" q)
    (hl : WellTyped d (allObjects d p) "location" l) :
    ∃ f, f < (taskOf d p false).numFacts ∧
      (taskOf d p false).factNames.getD f default = atC q l := by
  have h := named_of_instance hd hcar hloc (boardInst (p := p) hd hq hl)
    (y := atV "?car" "?loc") (Or.inl (by simp [boardInst, boardA]))
  simpa [boardInst, instAtom, boardA, locP, carP, atV, atC] using h

theorem on_named {q l : Name} (hq : WellTyped d (allObjects d p) "car" q)
    (hl : WellTyped d (allObjects d p) "location" l) :
    ∃ f, f < (taskOf d p false).numFacts ∧
      (taskOf d p false).factNames.getD f default = onC q := by
  have h := named_of_instance hd hcar hloc (boardInst (p := p) hd hq hl)
    (y := onV "?car") (Or.inr (Or.inl (by simp [boardInst, boardA])))
  simpa [boardInst, instAtom, boardA, locP, carP, onV, onC] using h

theorem empty_named {q l : Name} (hq : WellTyped d (allObjects d p) "car" q)
    (hl : WellTyped d (allObjects d p) "location" l) :
    ∃ f, f < (taskOf d p false).numFacts ∧
      (taskOf d p false).factNames.getD f default = emptyFerry := by
  have h := named_of_instance hd hcar hloc (boardInst (p := p) hd hq hl)
    (y := emptyV) (Or.inl (by simp [boardInst, boardA]))
  simpa [boardInst, instAtom, boardA, locP, carP, emptyV, emptyFerry] using h

end Named

/-! ### The `Cfg` the task describes

The lifted `Cfg` is read off the task the same way `compile` reads it: the places
are the objects of type `location`, and the cars are the `at` goals that name a
place the task knows, in goal order.
-/

/-- The (car, destination) pair one goal entry contributes, if any. -/
def goalEntry (t : Task) (x : GroundAtom × Nat) : Option (Name × Name) :=
  match x.1.pred == "at", x.1.args with
  | true, [q, g] => if ((locs t).findIdx? (· == g)).isSome then some (q, g) else none
  | _, _ => none

/-- The goal entries the heuristic keeps, in order. -/
def entries (t : Task) : List (Name × Name) :=
  t.goalAtoms.zipIdx.toList.filterMap (goalEntry t)

/-- The configuration a ferry task describes. -/
def cfgOf (t : Task) : Cfg where
  cars := (entries t).map (·.1)
  locations := (locs t).toList
  dest := fun q => (entries t).lookup q

theorem cfgOf_locations (t : Task) : (cfgOf t).locations = (locs t).toList := rfl

theorem nameOf_cfgOf (t : Task) (i : Nat) : nameOf (cfgOf t) i = (locs t).getD i "" := by
  unfold nameOf
  rw [cfgOf_locations, List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?]
  simp

/-! ### Where a location index points -/

theorem locIndex_sound {t : Task} {l : Name} {i : Nat}
    (h : (locs t).findIdx? (· == l) = some i) :
    i < (locs t).size ∧ nameOf (cfgOf t) i = l := by
  obtain ⟨hlt, hval⟩ := findIdx_sound h
  exact ⟨hlt, by rw [nameOf_cfgOf]; exact hval⟩

theorem locIndex_total {t : Task} {l : Name} (h : l ∈ locs t) :
    ∃ i, (locs t).findIdx? (· == l) = some i := findIdx_total h

theorem mem_locs_of_nameOf {t : Task} {i : Nat} (h : i < (locs t).size) :
    nameOf (cfgOf t) i ∈ (cfgOf t).locations := by
  rw [cfgOf_locations, nameOf_cfgOf, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem h]
  simpa using Array.getElem_mem h

/-! ### The car list, as a `filterMap` over the goal -/

theorem entries_eq (t : Task) :
    entries t = t.goalAtoms.toList.filterMap (fun a => goalEntry t (a, 0)) := by
  unfold entries
  rw [show t.goalAtoms.zipIdx.toList = t.goalAtoms.toList.zipIdx 0 from by simp]
  exact filterMap_zipIdx (fun a => goalEntry t (a, 0)) _ 0

theorem entries_sublist (d : Domain) (p : Problem) (rel : Bool) :
    (entries (taskOf d p rel)).Sublist (goalPairs p) := by
  rw [entries_eq, show (taskOf d p rel).goalAtoms.toList = p.goal from by simp [taskOf_goalAtoms]]
  refine filterMap_sublist ?_ p.goal
  intro a b hb
  by_cases hpred : (a.pred == "at") = true
  · rcases hargs : a.args with _ | ⟨q, rest⟩
    · simp [goalEntry, hpred, hargs] at hb
    · cases rest with
      | nil => simp [goalEntry, hpred, hargs] at hb
      | cons g rest' =>
          cases rest' with
          | cons _ _ => simp [goalEntry, hpred, hargs] at hb
          | nil =>
              simp only [goalEntry, hpred, hargs] at hb ⊢
              split at hb
              · exact hb
              · simp at hb
  · simp only [Bool.not_eq_true] at hpred
    simp [goalEntry, hpred] at hb

/-! ### What `compile` returns, named -/

theorem compile_ferryAt (t : Task) :
    (ExampleHeuristics.Ferry.compile t).ferryAt
      = (t.factsWith "at-ferry").filterMap (fun y =>
          match y.2.args with
          | [l] => ((locs t).findIdx? (· == l)).map ((y.1, ·))
          | _ => none) := rfl

theorem compile_emptyFact (t : Task) :
    (ExampleHeuristics.Ferry.compile t).emptyFact
      = ((t.factsWith "empty-ferry").find? fun y => y.2.args == []).map (·.1) := rfl

theorem compile_cars (t : Task) :
    (ExampleHeuristics.Ferry.compile t).cars
      = t.goalAtoms.zipIdx.filterMap
          (ExampleHeuristics.Ferry.carEntry t (t.factsWith "at") (t.factsWith "on")
            (fun l => (locs t).findIdx? (· == l))) := rfl

/-! ### The ferry tables -/

section Match

variable {d : Domain} {p : Problem} {rel : Bool} (hp : FerryPinned d p)
  (hn : FerryNumbered d p rel)

include hp

theorem locations_nodup : (cfgOf (taskOf d p rel)).locations.Nodup := by
  rw [cfgOf_locations]
  exact objsOf_nodup hp.validated.namesNodup

/-- Some object is a car and some object is a location, so `board` has an instance. -/
theorem some_car_loc : ∃ q l, WellTyped d (allObjects d p) "car" q ∧
    WellTyped d (allObjects d p) "location" l := by
  obtain ⟨oc, hoc, htc⟩ := hp.someCar
  obtain ⟨ol, hol, htl⟩ := hp.someLoc
  exact ⟨oc.name, ol.name, wellTyped_of_type hoc htc, wellTyped_of_type hol htl⟩

include hn in
theorem emptyFact_isSome :
    ∃ f, (ExampleHeuristics.Ferry.compile (taskOf d p rel)).emptyFact = some f := by
  obtain ⟨q, l, hq, hl⟩ := some_car_loc hp
  obtain ⟨f, hlt, hname⟩ := hn.emptyF
  have hmem : (f, emptyFerry) ∈ (taskOf d p rel).factsWith "empty-ferry" :=
    mem_factsWith_of_named (by rwa [← taskOf_numFacts]) hname rfl
  rw [compile_emptyFact]
  rcases hfind : (((taskOf d p rel).factsWith "empty-ferry").find?
      fun y => y.2.args == []) with _ | x
  · rw [Array.find?_eq_none] at hfind
    exact absurd (hfind _ hmem) (by simp [emptyFerry])
  · exact ⟨x.1, by rw [hfind]; simp⟩

/-- The car of a kept goal entry is a car, and its destination a place. -/
theorem entry_typed {x : Name × Name} (hx : x ∈ entries (taskOf d p rel)) :
    WellTyped d (allObjects d p) "car" x.1 ∧
    WellTyped d (allObjects d p) "location" x.2 := by
  obtain ⟨hc, hl⟩ := hp.goalTyped x ((entries_sublist d p rel).mem hx)
  obtain ⟨oc, hoc, hnc, htc⟩ := hc
  obtain ⟨ol, hol, hnl, htl⟩ := hl
  exact ⟨hnc ▸ wellTyped_of_type hoc htc, hnl ▸ wellTyped_of_type hol htl⟩

/-- With pruning off, grounding completeness numbers all four atom families. -/
theorem ferryNumbered_false : FerryNumbered d p false := by
  obtain ⟨q0, l0, hq0, hl0⟩ := some_car_loc hp
  exact ⟨fun l hl => atFerry_named hp.domain hp.carType hp.locType hl,
    fun q l hq hl => at_named hp.domain hp.carType hp.locType hq hl,
    fun q hq => on_named hp.domain hp.carType hp.locType hq hl0,
    empty_named hp.domain hp.carType hp.locType hq0 hl0⟩

include hn in
/-- One compiled car entry says the right things. -/
theorem carMatch_entry {x : GroundAtom × Nat} {q g : Name} {gl : Nat}
    (hx : x ∈ (taskOf d p rel).goalAtoms.zipIdx)
    (hpred : x.1.pred = "at") (hargs : x.1.args = [q, g])
    (hi : (locs (taskOf d p rel)).findIdx? (· == g) = some gl)
    (hmemE : (q, g) ∈ entries (taskOf d p rel)) :
    CarMatch (taskOf d p rel) (cfgOf (taskOf d p rel))
      { goalFact := (taskOf d p rel).goal.getD x.2 0, goalLoc := gl,
        atFacts := ((taskOf d p rel).factsWith "at").filterMap fun y =>
          match y.2.args with
          | [z, l] =>
              if z == q then ((locs (taskOf d p rel)).findIdx? (· == l)).map ((y.1, ·)) else none
          | _ => none,
        onFact := (((taskOf d p rel).factsWith "on").find? fun y => y.2.args == [q]).map (·.1) }
      q := by
  obtain ⟨hgl, hnm⟩ := locIndex_sound hi
  obtain ⟨hcarT, hlocT⟩ := entry_typed hp hmemE
  -- the goal atom this entry came from
  have hget : (taskOf d p rel).goalAtoms[x.2]? = some x.1 := Array.mem_zipIdx_iff_getElem?.mp hx
  have hlt : x.2 < (taskOf d p rel).goalAtoms.size := by
    by_contra hc
    rw [Array.getElem?_eq_none (by omega)] at hget
    simp at hget
  have hatom : (taskOf d p rel).goalAtoms[x.2]'hlt = atC q g := by
    rw [Array.getElem?_eq_getElem hlt] at hget
    have : x.1 = atC q g := by
      show x.1 = { pred := "at", args := [q, g] }
      rw [← hpred, ← hargs]
    rw [← this]
    simpa using hget
  obtain ⟨hname, hrange⟩ := goal_name_eq d p rel hlt
  refine ⟨?_, hrange, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hname, hatom, hnm]
  · rw [cfgOf_locations]; simpa using hgl
  · show (cfgOf (taskOf d p rel)).dest q = some (nameOf (cfgOf (taskOf d p rel)) gl)
    rw [hnm]
    exact lookup_of_mem
      (hp.goalNodup.2.sublist (List.Sublist.map _ (entries_sublist d p rel))) hmemE
  · intro y hy
    rw [Array.mem_filterMap] at hy
    obtain ⟨z, hz, hval⟩ := hy
    obtain ⟨hzr, hzn, hzp⟩ := mem_factsWith hz
    rcases hza : z.2.args with _ | ⟨c1, rest⟩
    · rw [hza] at hval; simp at hval
    · cases rest with
      | nil => rw [hza] at hval; simp at hval
      | cons l rest' =>
          cases rest' with
          | cons _ _ => rw [hza] at hval; simp at hval
          | nil =>
              rw [hza] at hval
              dsimp only at hval
              by_cases hc1 : (c1 == q) = true
              · rw [if_pos hc1] at hval
                rcases hj : (locs (taskOf d p rel)).findIdx? (· == l) with _ | j
                · rw [hj] at hval; simp at hval
                · rw [hj] at hval
                  simp only [Option.map_some, Option.some.injEq] at hval
                  subst hval
                  obtain ⟨hjl, hjn⟩ := locIndex_sound hj
                  refine ⟨?_, hzr, ?_⟩
                  · rw [hzn, hjn]
                    show z.2 = { pred := "at", args := [q, l] }
                    rw [(by simpa using hc1 : c1 = q)] at hza
                    rw [← hzp, ← hza]
                  · rw [cfgOf_locations]; simpa using hjl
              · rw [if_neg hc1] at hval; simp at hval
  · intro loc hloc
    rw [cfgOf_locations] at hloc
    have hlm : loc ∈ locs (taskOf d p rel) := by simpa using hloc
    obtain ⟨f, hflt, hfname⟩ :=
      hn.atCF q loc hcarT (locs_wellTyped hlm)
    obtain ⟨j, hj⟩ := locIndex_total hlm
    refine ⟨(f, j), ?_, (locIndex_sound hj).2⟩
    rw [Array.mem_filterMap]
    refine ⟨(f, atC q loc),
      mem_factsWith_of_named (by rwa [← taskOf_numFacts]) hfname rfl, ?_⟩
    simp [atC, hj]
  · intro f hf
    refine ⟨?_, ?_⟩
    · have := factsWith_find_args_map hf
      rw [this]; rfl
    · rcases hfind : (((taskOf d p rel).factsWith "on").find? fun y => y.2.args == [q]) with _ | z
      · rw [hfind] at hf; simp at hf
      · rw [hfind] at hf
        simp only [Option.map_some, Option.some.injEq] at hf
        subst hf
        exact (mem_factsWith (Array.mem_of_find?_eq_some hfind)).1
  · intro hnone
    obtain ⟨lq, ll, -, hll⟩ := some_car_loc hp
    obtain ⟨f, hflt, hfname⟩ := hn.onCF q hcarT
    have hmem : (f, onC q) ∈ (taskOf d p rel).factsWith "on" :=
      mem_factsWith_of_named (by rwa [← taskOf_numFacts]) hfname rfl
    rcases hfind : (((taskOf d p rel).factsWith "on").find? fun y => y.2.args == [q]) with _ | z
    · rw [Array.find?_eq_none] at hfind
      exact absurd (hfind _ hmem) (by simp [onC])
    · rw [hfind] at hnone; simp at hnone

include hn in
theorem ferryMatch :
    FerryMatch (taskOf d p rel) (cfgOf (taskOf d p rel))
      (ExampleHeuristics.Ferry.compile (taskOf d p rel)) := by
  refine ⟨locations_nodup hp, ?_, ?_, ?_, ?_, ?_⟩
  · exact hp.goalNodup.2.sublist (List.Sublist.map _ (entries_sublist d p rel))
  · intro x hx
    rw [compile_ferryAt, Array.mem_filterMap] at hx
    obtain ⟨y, hy, hval⟩ := hx
    obtain ⟨hrange, hname, hpred⟩ := mem_factsWith hy
    rcases hargs : y.2.args with _ | ⟨l, rest⟩
    · rw [hargs] at hval; simp at hval
    · cases rest with
      | cons _ _ => rw [hargs] at hval; simp at hval
      | nil =>
          rw [hargs] at hval
          dsimp only at hval
          rcases hi : (locs (taskOf d p rel)).findIdx? (· == l) with _ | i
          · rw [hi] at hval; simp at hval
          · rw [hi] at hval
            simp only [Option.map_some, Option.some.injEq] at hval
            subst hval
            obtain ⟨hlt, hnm⟩ := locIndex_sound hi
            refine ⟨?_, hrange, ?_⟩
            · rw [hname, hnm]
              show y.2 = atFerry l
              unfold atFerry
              rw [← hpred, ← hargs]
            · rw [cfgOf_locations]; simpa using hlt
  · intro g hg
    rw [cfgOf_locations] at hg
    have hgm : g ∈ locs (taskOf d p rel) := by simpa using hg
    obtain ⟨f, hlt, hname⟩ := hn.atFerryF g (locs_wellTyped hgm)
    obtain ⟨i, hi⟩ := locIndex_total hgm
    refine ⟨(f, i), ?_, (locIndex_sound hi).2⟩
    rw [compile_ferryAt, Array.mem_filterMap]
    refine ⟨(f, atFerry g), mem_factsWith_of_named (by rwa [← taskOf_numFacts]) hname rfl, ?_⟩
    simp [atFerry, hi]
  · intro f hf
    rw [compile_emptyFact] at hf
    refine ⟨factsWith_find_args_map hf, ?_⟩
    rcases hfind : (((taskOf d p rel).factsWith "empty-ferry").find?
        fun y => y.2.args == []) with _ | x
    · rw [hfind] at hf; simp at hf
    · rw [hfind] at hf
      simp only [Option.map_some, Option.some.injEq] at hf
      subst hf
      exact (mem_factsWith (Array.mem_of_find?_eq_some hfind)).1
  · intro hnone
    obtain ⟨f, hf⟩ := emptyFact_isSome hp hn
    rw [hf] at hnone
    simp at hnone

include hn in
theorem dataMatches :
    DataMatches (taskOf d p rel) (cfgOf (taskOf d p rel))
      (ExampleHeuristics.Ferry.compile (taskOf d p rel)) := by
  have hcars : (cfgOf (taskOf d p rel)).cars
      = (taskOf d p rel).goalAtoms.zipIdx.toList.filterMap
          (fun x => (goalEntry (taskOf d p rel) x).map (·.1)) := by
    show (entries (taskOf d p rel)).map (·.1) = _
    rw [entries, List.map_filterMap]
  show List.Forall₂ (CarMatch (taskOf d p rel) (cfgOf (taskOf d p rel)))
    (ExampleHeuristics.Ferry.compile (taskOf d p rel)).cars.toList (cfgOf (taskOf d p rel)).cars
  rw [compile_cars, hcars, Array.toList_filterMap]
  refine forall₂_filterMap _ ?_
  intro x hx
  by_cases hpred : (x.1.pred == "at") = true
  · rcases hargs : x.1.args with _ | ⟨q, rest⟩
    · exact ⟨fun ci hci => by
        simp [ExampleHeuristics.Ferry.carEntry, hpred, hargs] at hci,
      fun _ => by simp [goalEntry, hpred, hargs]⟩
    · cases rest with
      | nil =>
          exact ⟨fun ci hci => by
            simp [ExampleHeuristics.Ferry.carEntry, hpred, hargs] at hci,
          fun _ => by simp [goalEntry, hpred, hargs]⟩
      | cons g rest' =>
          cases rest' with
          | cons _ _ =>
              exact ⟨fun ci hci => by
                simp [ExampleHeuristics.Ferry.carEntry, hpred, hargs] at hci,
              fun _ => by simp [goalEntry, hpred, hargs]⟩
          | nil =>
              rcases hi : (locs (taskOf d p rel)).findIdx? (· == g) with _ | gl
              · exact ⟨fun ci hci => by
                  simp [ExampleHeuristics.Ferry.carEntry, hpred, hargs, hi] at hci,
                fun _ => by simp [goalEntry, hpred, hargs, hi]⟩
              · have hge : goalEntry (taskOf d p rel) x = some (q, g) := by
                  simp [goalEntry, hpred, hargs, hi]
                have hmemE : (q, g) ∈ entries (taskOf d p rel) :=
                  List.mem_filterMap.mpr ⟨x, hx, hge⟩
                refine ⟨fun ci hci => ⟨q, by rw [hge]; rfl, ?_⟩, fun hn => ?_⟩
                · simp only [ExampleHeuristics.Ferry.carEntry, hpred, hargs, hi,
                    Option.map_some, Option.some.injEq] at hci
                  rw [← hci]
                  refine carMatch_entry hp hn ?_ (by simpa using hpred) hargs hi hmemE
                  exact Array.mem_def.mpr (by simpa using hx)
                · simp [ExampleHeuristics.Ferry.carEntry, hpred, hargs, hi] at hn
  · simp only [Bool.not_eq_true] at hpred
    exact ⟨fun ci hci => by
      simp [ExampleHeuristics.Ferry.carEntry, hpred] at hci,
    fun _ => by simp [goalEntry, hpred]⟩

/-! ### From the goal to the configuration -/

theorem goal_of_goalPairs {q g : Name} (h : (q, g) ∈ goalPairs p) : atC q g ∈ p.goal := by
  rw [goalPairs, List.mem_filterMap] at h
  obtain ⟨a, ha, hval⟩ := h
  by_cases hpred : (a.pred == "at") = true
  · rcases hargs : a.args with _ | ⟨q', rest⟩
    · simp [hpred, hargs] at hval
    · cases rest with
      | nil => simp [hpred, hargs] at hval
      | cons g' rest' =>
          cases rest' with
          | cons _ _ => simp [hpred, hargs] at hval
          | nil =>
              simp only [hpred, hargs, Option.some.injEq, Prod.mk.injEq] at hval
              obtain ⟨h1, h2⟩ := hval
              have : a = atC q g := by
                show a = { pred := "at", args := [q, g] }
                rw [← h1, ← h2, ← hargs, ← (by simpa using hpred : a.pred = "at")]
              rwa [← this]
  · simp only [Bool.not_eq_true] at hpred
    simp [hpred] at hval

theorem mem_entries_of_goalPairs {x : Name × Name} (h : x ∈ goalPairs p) :
    x ∈ entries (taskOf d p rel) := by
  obtain ⟨-, ol, hol, hnl, htl⟩ := hp.goalTyped x h
  have hlm : x.2 ∈ locs (taskOf d p rel) := mem_objsOf hol hnl htl
  obtain ⟨i, hi⟩ := locIndex_total hlm
  rw [entries_eq, show (taskOf d p rel).goalAtoms.toList = p.goal from by simp [taskOf_goalAtoms],
    List.mem_filterMap]
  refine ⟨atC x.1 x.2, goal_of_goalPairs hp h, ?_⟩
  simp [goalEntry, atC, hi]

theorem cfgOK : CfgOK d p (cfgOf (taskOf d p rel)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro l hl
    obtain ⟨o, ho, hname, hsub⟩ := hl
    rw [cfgOf_locations]
    simpa using (mem_objsOf ho hname (hp.locExact o ho hsub) : l ∈ locs (taskOf d p rel))
  · intro q hq
    obtain ⟨o, ho, hname, hsub⟩ := hq
    obtain ⟨x, hx, hxn⟩ := hp.carGoal o ho (hp.carExact o ho hsub)
    exact List.mem_map.mpr ⟨x, mem_entries_of_goalPairs hp hx, by rw [hxn, hname]⟩
  · exact hp.goalNodup.2.sublist (List.Sublist.map _ (entries_sublist d p rel))

theorem dest_sub : ∀ q ∈ (cfgOf (taskOf d p rel)).cars, ∀ g,
    (cfgOf (taskOf d p rel)).dest q = some g → atC q g ∈ p.goal := by
  intro q _ g hdest
  exact goal_of_goalPairs hp ((entries_sublist d p rel).mem (mem_of_lookup hdest))

theorem dest_isSome : ∀ q ∈ (cfgOf (taskOf d p rel)).cars,
    ((cfgOf (taskOf d p rel)).dest q).isSome := by
  intro q hq
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
  rw [show (cfgOf (taskOf d p rel)).dest x.1 = (entries (taskOf d p rel)).lookup x.1 from rfl,
    lookup_of_mem (hp.goalNodup.2.sublist (List.Sublist.map _ (entries_sublist d p rel)))
      (show (x.1, x.2) ∈ entries (taskOf d p rel) from hx)]
  rfl

/-! ### Ferry, end to end -/

theorem opFacts_all : ∀ o ∈ groundedOps d p rel, Nonempty (OpFacts d p o) :=
  fun o ho => opFacts_ground d p rel ho

theorem cost_pos : ∀ o ∈ groundedOps d p rel, 0 < o.cost := by
  intro o ho
  obtain ⟨f⟩ := opFacts_all hp o ho
  rw [f.cost]
  show 0 < f.inst.schema.cost
  have hmem : f.inst.schema ∈ [sailA, boardA, debarkA] := hp.domain ▸ f.inst.mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h <;> rw [h] <;> simp [sailA, boardA, debarkA]

include hn in
/-- **Ferry's improved heuristic is goal-aware on the task the planner searches.** -/
theorem improved_goalAware :
    (ground d p rel).GoalAwareOn (Reachable (ground d p rel))
      (ExampleHeuristics.Ferry.improved (ground d p rel)).eval :=
  improved_goalAwareOn d p rel (cfgOf (taskOf d p rel)) hp.domain (cfgOK hp)
    (ground_wf d p rel (cost_pos hp)) (cost_pos hp) (opFacts_all hp)
    (dest_sub hp) (dest_isSome hp) (initInv_of_check hp.initCheck) _
    (computes (ferryMatch hp hn) (dataMatches hp hn) rfl)

include hn in
/-- **Ferry's improved heuristic is consistent on the task the planner searches.** -/
theorem improved_consistent :
    (ground d p rel).ConsistentOn (Reachable (ground d p rel))
      (ExampleHeuristics.Ferry.improved (ground d p rel)).eval :=
  improved_consistentOn d p rel (cfgOf (taskOf d p rel)) hp.domain (cfgOK hp)
    (ground_wf d p rel (cost_pos hp)) (cost_pos hp) (opFacts_all hp)
    (initInv_of_check hp.initCheck) _
    (computes (ferryMatch hp hn) (dataMatches hp hn) rfl)

include hn in
/--
**Ferry's improved heuristic is admissible on the task the planner searches.**

Nothing about the heuristic is assumed.  `compile` is the function the planner
runs, `ground d p false` is the task it runs on, and the only hypothesis is
`FerryPinned`, one decidable pass over the parsed domain and problem.
-/
theorem improved_admissible :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel))
      (ExampleHeuristics.Ferry.improved (ground d p rel)).eval :=
  improved_admissibleOn d p rel (cfgOf (taskOf d p rel)) hp.domain (cfgOK hp)
    (ground_wf d p rel (cost_pos hp)) (cost_pos hp) (opFacts_all hp)
    (dest_sub hp) (dest_isSome hp) (initInv_of_check hp.initCheck) _
    (computes (ferryMatch hp hn) (dataMatches hp hn) rfl)

end Match

/-! ### With the relevance analysis on

Pruning can drop the operator that is the only mention of an atom, so the four
families have to be shown *relevant* before they can be shown numbered.  Ferry's
chain is short.  A car's destination goal is relevant.  The `board` that would meet
it deletes that goal atom, so it survives, and closure puts its whole precondition
in the set, which is where `empty-ferry` comes from.  Every other `board` deletes
`empty-ferry`, so every `at` and every `at-ferry` follows, and every `debark` adds
an `at`, so every `on` follows.
-/

private theorem touches_of_del {o : AtomOp} {r : Std.HashSet GroundAtom} {x : GroundAtom}
    (hx : x ∈ o.del) (hr : r.contains x = true) : o.touches r = true := by
  simp only [AtomOp.touches, Bool.or_eq_true, Array.any_eq_true]
  obtain ⟨i, hi, hval⟩ := Array.getElem_of_mem hx
  exact Or.inr ⟨i, hi, by rw [hval]; exact hr⟩

private theorem touches_of_add {o : AtomOp} {r : Std.HashSet GroundAtom} {x : GroundAtom}
    (hx : x ∈ o.add) (hr : r.contains x = true) : o.touches r = true := by
  simp only [AtomOp.touches, Bool.or_eq_true, Array.any_eq_true]
  obtain ⟨i, hi, hval⟩ := Array.getElem_of_mem hx
  exact Or.inl ⟨i, hi, by rw [hval]; exact hr⟩

section Pruned

variable {d : Domain} {p : Problem} (hp : FerryPinned d p)

include hp

/-- The set the analysis settled on. -/
private abbrev rset : Std.HashSet GroundAtom := relevantSet (rawOps d p) p.goal.toArray

/-- The dynamic preconditions of a ferry schema are all of them. -/
private theorem dynAll {a : Action} (ha : a ∈ d.actions) :
    a.pre.filter (fun x => !(staticPredicates d).contains x.pred) = a.pre := by
  refine List.filter_eq_self.mpr ?_
  intro y hy
  have := no_static hp.domain ha hy
  simpa using this

/-- One `board`, as the grounder emits it. -/
private def boardRaw (q l : Name) : AtomOp :=
  mkOp boardA (boardA.pre.filter fun x => !(staticPredicates d).contains x.pred) #[q, l]

/-- One `debark`, as the grounder emits it. -/
private def debarkRaw (q l : Name) : AtomOp :=
  mkOp debarkA (debarkA.pre.filter fun x => !(staticPredicates d).contains x.pred) #[q, l]

private theorem boardRaw_mem {q l : Name} (hq : WellTyped d (allObjects d p) "car" q)
    (hl : WellTyped d (allObjects d p) "location" l) : boardRaw (d := d) q l ∈ rawOps d p := by
  rw [← groundedOps_false]
  refine groundedOps_complete d p (a := boardA) (by rw [hp.domain]; simp) #[q, l] rfl ?_ ?_ ?_
  · intro pm hpm
    have : pm = carP ∨ pm = locP "?loc" := by simpa [boardA] using hpm
    rcases this with rfl | rfl
    · exact hp.carType
    · exact hp.locType
  · exact List.Forall₂.cons hq (List.Forall₂.cons hl List.Forall₂.nil)
  · intro y hy hc
    rw [no_static hp.domain (by rw [hp.domain]; simp) hy] at hc
    exact absurd hc (by simp)

private theorem debarkRaw_mem {q l : Name} (hq : WellTyped d (allObjects d p) "car" q)
    (hl : WellTyped d (allObjects d p) "location" l) :
    debarkRaw (d := d) q l ∈ rawOps d p := by
  rw [← groundedOps_false]
  refine groundedOps_complete d p (a := debarkA) (by rw [hp.domain]; simp) #[q, l] rfl ?_ ?_ ?_
  · intro pm hpm
    have : pm = carP ∨ pm = locP "?loc" := by simpa [debarkA] using hpm
    rcases this with rfl | rfl
    · exact hp.carType
    · exact hp.locType
  · exact List.Forall₂.cons hq (List.Forall₂.cons hl List.Forall₂.nil)
  · intro y hy hc
    rw [no_static hp.domain (by rw [hp.domain]; simp) hy] at hc
    exact absurd hc (by simp)

variable (hok : relevantOK (rawOps d p) p.goal.toArray (rset (d := d) (p := p)) = true)

include hok

private theorem closedR : Closed (rawOps d p) (rset (d := d) (p := p)) :=
  (relevance_verified hok).1

private theorem goalR : ∀ a ∈ p.goal.toArray,
    (rset (d := d) (p := p)).contains a = true := (relevance_verified hok).2.1

omit hok in
private theorem board_del_at {q l : Name} :
    atC q l ∈ (boardRaw (d := d) q l).del := by
  have h := mem_mkOp_del boardA (boardA.pre.filter fun y =>
    !(staticPredicates d).contains y.pred) #[q, l] (y := atV "?car" "?loc")
    (by simp [boardA]) ?_
  · simpa [boardRaw, instAtom, boardA, carP, locP, atV, atC] using h
  · intro z hz
    have hz' : z = onV "?car" := by simpa [boardA] using hz
    subst hz'
    simp [instAtom, boardA, carP, locP, onV, atV, onC, atC]

omit hok in
private theorem board_del_empty {q l : Name} :
    emptyFerry ∈ (boardRaw (d := d) q l).del := by
  have h := mem_mkOp_del boardA (boardA.pre.filter fun y =>
    !(staticPredicates d).contains y.pred) #[q, l] (y := emptyV)
    (by simp [boardA]) ?_
  · simpa [boardRaw, instAtom, boardA, carP, locP, emptyV, emptyFerry] using h
  · intro z hz
    have hz' : z = onV "?car" := by simpa [boardA] using hz
    subst hz'
    simp [instAtom, boardA, carP, locP, onV, emptyV, onC, emptyFerry]

omit hok in
private theorem debark_add_at {q l : Name} :
    atC q l ∈ (debarkRaw (d := d) q l).add := by
  have h := mem_mkOp_add debarkA (debarkA.pre.filter fun y =>
    !(staticPredicates d).contains y.pred) #[q, l] (y := atV "?car" "?loc")
    (by simp [debarkA]) ?_
  · simpa [debarkRaw, instAtom, debarkA, carP, locP, atV, atC] using h
  · intro z hz
    rw [dynAll hp (by rw [hp.domain]; simp)] at hz
    have hz' : z = onV "?car" ∨ z = atFerryV "?loc" := by simpa [debarkA] using hz
    rcases hz' with rfl | rfl <;>
      simp [instAtom, debarkA, carP, locP, onV, atFerryV, atV, onC, atFerry, atC]

omit hok in
private theorem board_touches {q l : Name}
    (hx : (rset (d := d) (p := p)).contains (atC q l) = true ∨
      (rset (d := d) (p := p)).contains emptyFerry = true) :
    (boardRaw (d := d) q l).touches (rset (d := d) (p := p)) = true := by
  rcases hx with h | h
  · exact touches_of_del (board_del_at hp) h
  · exact touches_of_del (board_del_empty hp) h

omit hok in
private theorem debark_touches {q l : Name}
    (hx : (rset (d := d) (p := p)).contains (atC q l) = true) :
    (debarkRaw (d := d) q l).touches (rset (d := d) (p := p)) = true :=
  touches_of_add (debark_add_at hp) hx

/-- Every precondition of a `board` that writes into the set is in the set. -/
private theorem board_pre_rel {q l : Name}
    (hq : WellTyped d (allObjects d p) "car" q)
    (hl : WellTyped d (allObjects d p) "location" l)
    (hx : (rset (d := d) (p := p)).contains (atC q l) = true ∨
      (rset (d := d) (p := p)).contains emptyFerry = true) :
    (rset (d := d) (p := p)).contains (atC q l) = true ∧
    (rset (d := d) (p := p)).contains (atFerry l) = true ∧
    (rset (d := d) (p := p)).contains emptyFerry = true := by
  have hdyn : boardA.pre.filter (fun y => !(staticPredicates d).contains y.pred) = boardA.pre :=
    dynAll hp (by rw [hp.domain]; simp)
  have hpre := closedR hp hok _ (boardRaw_mem hp hq hl) (board_touches hp hx)
  have hin : ∀ y ∈ boardA.pre, instAtom boardA.params [q, l] y
      ∈ (boardRaw (d := d) q l).pre := by
    intro y hy
    have := mem_mkOp_pre boardA (boardA.pre.filter fun z =>
      !(staticPredicates d).contains z.pred) #[q, l] (y := y) (by rw [hdyn]; exact hy)
    simpa [boardRaw] using this
  refine ⟨?_, ?_, ?_⟩
  · have := hpre _ (hin (atV "?car" "?loc") (by simp [boardA]))
    simpa [instAtom, boardA, carP, locP, atV, atC] using this
  · have := hpre _ (hin (atFerryV "?loc") (by simp [boardA]))
    simpa [instAtom, boardA, carP, locP, atFerryV, atFerry] using this
  · have := hpre _ (hin emptyV (by simp [boardA]))
    simpa [instAtom, boardA, carP, locP, emptyV, emptyFerry] using this

/-- `empty-ferry` is relevant, because the `board` that meets a goal deletes it. -/
private theorem empty_rel : (rset (d := d) (p := p)).contains emptyFerry = true := by
  obtain ⟨o, ho, ht⟩ := hp.someCar
  obtain ⟨x, hx, -⟩ := hp.carGoal o ho ht
  obtain ⟨⟨oc, hoc, hnc, htc⟩, ⟨ol, hol, hnl, htl⟩⟩ := hp.goalTyped x hx
  have hgoal : atC x.1 x.2 ∈ p.goal := goal_of_goalPairs hp hx
  have hr : (rset (d := d) (p := p)).contains (atC x.1 x.2) = true :=
    goalR hp hok _ (by simpa using hgoal)
  exact (board_pre_rel hp hok (hnc ▸ wellTyped_of_type hoc htc)
    (hnl ▸ wellTyped_of_type hol htl) (Or.inl hr)).2.2

/-- And then every `at` and every `at-ferry` is. -/
private theorem at_rel {q l : Name} (hq : WellTyped d (allObjects d p) "car" q)
    (hl : WellTyped d (allObjects d p) "location" l) :
    (rset (d := d) (p := p)).contains (atC q l) = true ∧
    (rset (d := d) (p := p)).contains (atFerry l) = true :=
  let h := board_pre_rel hp hok hq hl (Or.inr (empty_rel hp hok))
  ⟨h.1, h.2.1⟩

/-- And every `on`, because the `debark` that would add an `at` survives. -/
private theorem on_rel {q : Name} (hq : WellTyped d (allObjects d p) "car" q) :
    (rset (d := d) (p := p)).contains (onC q) = true := by
  obtain ⟨o, ho, ht⟩ := hp.someLoc
  have hl : WellTyped d (allObjects d p) "location" o.name := wellTyped_of_type ho ht
  have hdyn : debarkA.pre.filter (fun y => !(staticPredicates d).contains y.pred)
      = debarkA.pre := dynAll hp (by rw [hp.domain]; simp)
  have hpre := closedR hp hok _ (debarkRaw_mem hp hq hl)
    (debark_touches hp (at_rel hp hok hq hl).1)
  have := hpre _ (by
    have := mem_mkOp_pre debarkA (debarkA.pre.filter fun z =>
      !(staticPredicates d).contains z.pred) #[q, o.name] (y := onV "?car")
      (by rw [hdyn]; simp [debarkA])
    simpa [debarkRaw] using this)
  simpa [instAtom, debarkA, carP, locP, onV, onC] using this

/-- **The four families are numbered with pruning on, too.** -/
theorem ferryNumbered_verified : FerryNumbered d p true := by
  have hrdef := (relevance_verified hok).2.2
  have hname : ∀ (i : Instance d (allObjects d p)) (y : Atom),
      (mkOp i.schema (i.schema.pre.filter fun x =>
        !(staticPredicates d).contains x.pred) i.args.toArray).touches
          (rset (d := d) (p := p)) = true →
      y ∈ i.schema.pre →
      ∃ f, f < (taskOf d p true).numFacts ∧
        (taskOf d p true).factNames.getD f default = instAtom i.schema.params i.args y := by
    intro i y htouch hy
    exact ground_names_instance_pruned d p i (inst_hty hp.domain hp.carType hp.locType i)
      (inst_hstat hp.domain i) _ hrdef htouch (Or.inl ⟨hy, no_static hp.domain i.mem hy⟩)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l hl
    obtain ⟨o, ho, ht⟩ := hp.someCar
    have hq : WellTyped d (allObjects d p) "car" o.name := wellTyped_of_type ho ht
    have h := hname (boardInst (p := p) hp.domain hq hl) (atFerryV "?loc")
      (board_touches hp (Or.inr (empty_rel hp hok))) (by simp [boardInst, boardA])
    simpa [boardInst, instAtom, boardA, carP, locP, atFerryV, atFerry] using h
  · intro q l hq hl
    have h := hname (boardInst (p := p) hp.domain hq hl) (atV "?car" "?loc")
      (board_touches hp (Or.inr (empty_rel hp hok))) (by simp [boardInst, boardA])
    simpa [boardInst, instAtom, boardA, carP, locP, atV, atC] using h
  · intro q hq
    obtain ⟨o, ho, ht⟩ := hp.someLoc
    have hl : WellTyped d (allObjects d p) "location" o.name := wellTyped_of_type ho ht
    have h := hname (debarkInst (p := p) hp.domain hq hl) (onV "?car")
      (debark_touches hp (at_rel hp hok hq hl).1) (by simp [debarkInst, debarkA])
    simpa [debarkInst, instAtom, debarkA, carP, locP, onV, onC] using h
  · obtain ⟨o, ho, ht⟩ := hp.someCar
    obtain ⟨o', ho', ht'⟩ := hp.someLoc
    have hq : WellTyped d (allObjects d p) "car" o.name := wellTyped_of_type ho ht
    have hl : WellTyped d (allObjects d p) "location" o'.name := wellTyped_of_type ho' ht'
    have h := hname (boardInst (p := p) hp.domain hq hl) emptyV
      (board_touches hp (Or.inr (empty_rel hp hok))) (by simp [boardInst, boardA])
    simpa [boardInst, instAtom, boardA, carP, locP, emptyV, emptyFerry] using h

end Pruned

section Numbered

variable {d : Domain} {p : Problem} (hp : FerryPinned d p)

include hp

/-- **The tables are complete on the task the planner grounds, pruning or not.** -/
theorem ferryNumbered (rel : Bool) : FerryNumbered d p rel := by
  cases rel with
  | false => exact ferryNumbered_false hp
  | true =>
      by_cases hok : relevantOK (rawOps d p) p.goal.toArray
          (relevantSet (rawOps d p) p.goal.toArray) = true
      · exact ferryNumbered_verified hp hok
      · have heq : taskOf d p true = taskOf d p false :=
          taskOf_eq_of_unverified d p (by simpa using hok)
        obtain ⟨f1, f2, f3, f4⟩ := ferryNumbered_false hp
        refine ⟨fun l hl => ?_, fun q l hq hl => ?_, fun q hq => ?_, ?_⟩
        · rw [heq]; exact f1 l hl
        · rw [heq]; exact f2 q l hq hl
        · rw [heq]; exact f3 q hq
        · rw [heq]; exact f4

/--
**Ferry's improved heuristic is admissible on the task the planner searches**,
with the relevance analysis on or off, and with nothing assumed but one decidable
pass over the parsed domain and problem.
-/
theorem improved_admissible_of_pinned (rel : Bool) :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel))
      (ExampleHeuristics.Ferry.improved (ground d p rel)).eval :=
  improved_admissible hp (ferryNumbered hp rel)

/-- And goal-aware, and consistent, which is what makes the closed list safe. -/
theorem improved_goalAware_of_pinned (rel : Bool) :
    (ground d p rel).GoalAwareOn (Reachable (ground d p rel))
      (ExampleHeuristics.Ferry.improved (ground d p rel)).eval :=
  improved_goalAware hp (ferryNumbered hp rel)

theorem improved_consistent_of_pinned (rel : Bool) :
    (ground d p rel).ConsistentOn (Reachable (ground d p rel))
      (ExampleHeuristics.Ferry.improved (ground d p rel)).eval :=
  improved_consistent hp (ferryNumbered hp rel)

end Numbered

end Planner.Lifted.Ferry

/- -------------------------------------------------------------------------- -/
/-
A ferry domain and problem that satisfy `FerryPinned`.

`Proofs/Lifted/FerryCompile.lean` proves ferry's improved heuristic admissible
for every `d` and `p` that pass one decidable check.  A hypothesis nothing
satisfies proves nothing, so here is a task that satisfies it, with every field
discharged by `decide`.
-/

namespace Planner.Lifted.Ferry

open Planner Planner.Pddl

def exDomain : Domain where
  name := "ferry"
  requirements := [":strips", ":typing"]
  types := [{ name := "car", parent := "object" }, { name := "location", parent := "object" }]
  constants := []
  predicates :=
    [ { name := "at-ferry", params := [locP "?l"] },
      { name := "at", params := [carP, locP "?l"] },
      { name := "on", params := [carP] },
      { name := "not-at-ferry", params := [locP "?l"] },
      { name := "empty-ferry", params := [] } ]
  actions := [sailA, boardA, debarkA]

def exProblem : Problem where
  name := "ferry-1"
  domainName := "ferry"
  objects :=
    [ { name := "c1", type := "car" },
      { name := "l1", type := "location" },
      { name := "l2", type := "location" } ]
  init := [atFerry "l1", emptyFerry, atC "c1" "l1", notAtFerry "l2"]
  goal := [atC "c1" "l2"]

theorem exPinned : FerryPinned exDomain exProblem := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try decide
  exact { domainOK := by decide, problemOK := by decide }

/-- And so the heuristic the planner runs is admissible on that task, with the
relevance analysis on, which is how the planner runs by default. -/
theorem ex_admissible :
    (ground exDomain exProblem true).AdmissibleOn
      (Reachable (ground exDomain exProblem true))
      (ExampleHeuristics.Ferry.improved (ground exDomain exProblem true)).eval :=
  improved_admissible_of_pinned exPinned true

end Planner.Lifted.Ferry

/- -------------------------------------------------------------------------- -/
/-
Soundness of the executable certificate for the improved Ferry heuristic.
-/

namespace Planner.Lifted.Ferry

open Planner Planner.Pddl

theorem certificate_sound {d : Domain} {p : Problem}
    (hv : Validated d p)
    (h : ExampleHeuristics.Ferry.Certificate.certified d p = true) : FerryPinned d p := by
  simp only [ExampleHeuristics.Ferry.Certificate.certified, Bool.and_eq_true] at h
  rcases h with
    ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hd, hcarType⟩, hlocType⟩, hsomeLoc⟩, hsomeCar⟩, htyped⟩,
      hgoalNodup⟩, hcarNodup⟩, hcarGoal⟩, hlocExact⟩, hcarExact⟩, hinit⟩
  refine
    { domain := ?_
      carType := ?_
      locType := ?_
      validated := hv
      someLoc := ?_
      someCar := ?_
      goalTyped := ?_
      goalNodup := ⟨of_decide_eq_true hgoalNodup, of_decide_eq_true hcarNodup⟩
      carGoal := ?_
      locExact := ?_
      carExact := ?_
      initCheck := ?_ }
  · simpa using hd
  · simpa using hcarType
  · simpa using hlocType
  · rw [Certificate.hasObject, List.any_eq_true] at hsomeLoc
    obtain ⟨o, ho, ht⟩ := hsomeLoc
    exact ⟨o, ho, by simpa using ht⟩
  · rw [Certificate.hasObject, List.any_eq_true] at hsomeCar
    obtain ⟨o, ho, ht⟩ := hsomeCar
    exact ⟨o, ho, by simpa using ht⟩
  · intro x hx
    rw [ExampleHeuristics.Ferry.Certificate.goalsTyped, List.all_eq_true] at htyped
    have hpair := htyped x
      (by simpa [ExampleHeuristics.Ferry.Certificate.goalPairs, goalPairs] using hx)
    simp only [Certificate.objectNamedWithType,
      Bool.and_eq_true] at hpair
    constructor
    · have hc := hpair.1
      rw [List.any_eq_true] at hc
      obtain ⟨o, ho, hboth⟩ := hc
      rw [Bool.and_eq_true] at hboth
      obtain ⟨hn, ht⟩ := hboth
      exact ⟨o, ho, by simpa using hn, by simpa using ht⟩
    · have hl := hpair.2
      rw [List.any_eq_true] at hl
      obtain ⟨o, ho, hboth⟩ := hl
      rw [Bool.and_eq_true] at hboth
      obtain ⟨hn, ht⟩ := hboth
      exact ⟨o, ho, by simpa using hn, by simpa using ht⟩
  · intro o ho ht
    rw [ExampleHeuristics.Ferry.Certificate.everyCarHasGoal, List.all_eq_true] at hcarGoal
    have hg := hcarGoal o ho
    simp only [bne_iff_ne, ne_eq, Bool.or_eq_true] at hg
    rcases hg with hnot | hg
    · exact absurd ht hnot
    · rw [List.any_eq_true] at hg
      obtain ⟨x, hx, heq⟩ := hg
      exact ⟨x, by simpa [ExampleHeuristics.Ferry.Certificate.goalPairs, goalPairs] using hx,
        by simpa using heq⟩
  · intro o ho hs
    rw [Certificate.exactType, List.all_eq_true] at hlocExact
    have ht := hlocExact o ho
    simp only [Bool.or_eq_true] at ht
    rcases ht with hnot | heq
    · have hf : d.isSubtype o.type "location" = false := by simpa using hnot
      rw [hf] at hs
      contradiction
    · simpa using heq
  · intro o ho hs
    rw [Certificate.exactType, List.all_eq_true] at hcarExact
    have ht := hcarExact o ho
    simp only [Bool.or_eq_true] at ht
    rcases ht with hnot | heq
    · have hf : d.isSubtype o.type "car" = false := by simpa using hnot
      rw [hf] at hs
      contradiction
    · simpa using heq
  · simpa [ExampleHeuristics.Ferry.Certificate.initInvCheck,
      ExampleHeuristics.Ferry.Certificate.ferryPlaces,
      ExampleHeuristics.Ferry.Certificate.atPairs,
      ExampleHeuristics.Ferry.Certificate.onCars,
      initInvCheck, ferryPlaces, atPairs, onCars, emptyFerry] using hinit

theorem improved_goalAware_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool)
    (h : ExampleHeuristics.Ferry.Certificate.certified d p = true) :
    (ground d p rel).GoalAwareOn (Reachable (ground d p rel))
      (ExampleHeuristics.Ferry.improved (ground d p rel)).eval :=
  improved_goalAware_of_pinned (certificate_sound hv h) rel

theorem improved_consistent_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool)
    (h : ExampleHeuristics.Ferry.Certificate.certified d p = true) :
    (ground d p rel).ConsistentOn (Reachable (ground d p rel))
      (ExampleHeuristics.Ferry.improved (ground d p rel)).eval :=
  improved_consistent_of_pinned (certificate_sound hv h) rel

theorem improved_proof_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool) :
    ImprovedProof d p rel
      (ExampleHeuristics.Ferry.Certificate.certified d p)
      (ExampleHeuristics.Ferry.improved (ground d p rel)) :=
  { goalAware := improved_goalAware_of_certificate hv rel
    consistent := improved_consistent_of_certificate hv rel }

theorem improved_admissible_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool)
    (h : ExampleHeuristics.Ferry.Certificate.certified d p = true) :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel))
      (ExampleHeuristics.Ferry.improved (ground d p rel)).eval :=
  (improved_proof_of_certificate hv rel).admissible h

end Planner.Lifted.Ferry
