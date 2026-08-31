/-
Satellite's improved heuristic, proved end to end in one file.

The order below is the order the argument is built in.  The schema-level proof
comes first: the improved value over the domain's own data, and what each schema
does to the counters.  The rest lifts that value to the parsed domain and
compiles it against the numbered task.

The runtime heuristic and its data stay under `Planner/`.  The simple heuristic
of this domain is proved in `Proofs/Domains/SatelliteSimple.lean`.
-/
import Proofs.Combinators
import Proofs.Certificates
import Proofs.SchemaSupport
import Proofs.LiftedHeuristic
import Proofs.FactTables
import Proofs.CompileSupport
import Proofs.Validation
import Proofs.Heuristic
import Planner.GeneratedDomains.Satellite
import Planner.ExampleHeuristics.Satellite.Improved
import Planner.ExampleHeuristics.Satellite.Certificate

/-
The whole Satellite argument is one module now, so the two proofs that were at
the default heartbeat limit in their own files are over it here.  This raises
the limit for the file.  It is a resource bound, not an assumption.
-/
set_option maxHeartbeats 1000000

/- -------------------------------------------------------------------------- -/
/-
Satellite, improved heuristic: goal-aware, consistent, admissible.

The value splits into the actions that are not turns — images, calibrations,
power — and the turns.  `Effect` says how one action may move the pair.

  * `take_image`, `calibrate`, `switch_on` and `switch_off` lower the action count
    by at most one and cannot lower the turn count.  The instrument counts are a
    set-cover bound: each `calibrate` readies exactly one instrument, so at least
    two are needed when no single instrument supports every mode still uncovered.
    That is safe against the image count because taking an image of a mode
    requires a ready instrument supporting it, so that mode is never in the
    uncovered set.
  * `turn_to` leaves the action count alone and moves the turn count by at most
    one.

This is the domain where an unproved argument was wrong once, so it is worth
recording what a proof rules out.  The turn count excludes the direction of an
unmet `pointing` goal, and that exclusion must be unconditional.  A refinement
excusing it only when the satellite could shoot on arrival overestimates, because
the satellite may calibrate elsewhere first and arrive at the direction last; on
`easy-p08` that gave an initial value of 9 against an optimal cost of 8.  With
`paidByGoal` unconditional, that case is simply not expressible.

There are no dead ends in this domain.

What is assumed rather than checked: that each grounded operator induces one of
the four effects.
-/

namespace Planner.ExampleHeuristics.Satellite

open Planner

/-! ### The two quantities -/

/-- Images, calibrations and power: everything that is not a turn. -/
abbrev Ac (d : Data) (s : State) : Nat := actionCount d s
/-- Turns. -/
abbrev Tc (d : Data) (s : State) : Nat := turns d s

/-- How an action may move the two quantities: one constructor per schema family. -/
inductive Effect (d : Data) (s s' : State) : Prop
  | image (hA : Ac d s ≤ Ac d s' + 1) (hT : Tc d s ≤ Tc d s')
  | ready (hA : Ac d s ≤ Ac d s' + 1) (hT : Tc d s ≤ Tc d s')
  | turn (hA : Ac d s ≤ Ac d s') (hT : Tc d s ≤ Tc d s' + 1)
  | other (hA : Ac d s ≤ Ac d s') (hT : Tc d s ≤ Tc d s')

/-! ### The step -/

private theorem step_arith (A T A' T' cost : Nat) (hcost : 1 ≤ cost)
    (h : (A ≤ A' + 1 ∧ T ≤ T') ∨ (A ≤ A' ∧ T ≤ T' + 1)) :
    A + T ≤ cost + (A' + T') := by
  rcases h with ⟨h1,h2⟩|⟨h1,h2⟩ <;> omega

theorem value_step (d : Data) (s s' : State) (he : Effect d s s')
    (cost : Nat) (hcost : 1 ≤ cost) : value d s ≤ cost + value d s' := by
  show Ac d s + Tc d s ≤ cost + (Ac d s' + Tc d s')
  refine step_arith _ _ _ _ cost hcost ?_
  cases he with
  | image hA hT => exact Or.inl ⟨hA, hT⟩
  | ready hA hT => exact Or.inl ⟨hA, hT⟩
  | turn hA hT => exact Or.inr ⟨hA, hT⟩
  | other hA hT => exact Or.inl ⟨by omega, hT⟩

/-! ### Assembly -/

theorem unmet_empty (d : Data) (s : State)
    (h1 : ∀ g ∈ d.images, s.test g.goalFact = true)
    (h2 : ∀ g ∈ d.pointingGoals, s.test g.goalFact = true) :
    unmetImages d s = #[] ∧ unmetPointing d s = #[] := by
  constructor
  · unfold unmetImages
    rw [Array.filter_eq_empty_iff]
    intro x hx; simp [h1 x hx]
  · unfold unmetPointing
    rw [Array.filter_eq_empty_iff]
    intro x hx; simp [h2 x hx]

theorem value_eq_zero_of_goal (d : Data) (s : State)
    (h1 : ∀ g ∈ d.images, s.test g.goalFact = true)
    (h2 : ∀ g ∈ d.pointingGoals, s.test g.goalFact = true) : value d s = 0 := by
  obtain ⟨e1, e2⟩ := unmet_empty d s h1 h2
  have hneeded : neededModes d s = [] := by
    unfold neededModes
    rw [e1]
    rfl
  have huncal : uncalibratedModes d s = [] := by
    simp [uncalibratedModes, hneeded]
  have happ : approach d s = 0 := by
    simp [approach, huncal]
  unfold value actionCount turns freeSlot uncalibratedModes unpoweredModes
    neededModes dirsToTurn coverCount
  rw [e1, e2]
  simp [distinct, happ]

theorem improved_goalAware (t : Task)
    (c1 : ∀ g ∈ (compile t).images, g.goalFact ∈ t.goal)
    (c2 : ∀ g ∈ (compile t).pointingGoals, g.goalFact ∈ t.goal) :
    t.GoalAware (improved t).eval := by
  refine t.goalAware_of _ fun s _ hgoal => ?_
  exact value_eq_zero_of_goal _ s (fun g hg => hgoal _ (c1 g hg)) (fun g hg => hgoal _ (c2 g hg))

theorem improved_consistent (t : Task)
    (heff : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      Effect (compile t) s (op.apply s))
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost) :
    t.Consistent (improved t).eval :=
  t.consistent_of_ops _ fun op hop s hs happ =>
    value_step _ s _ (heff op hop s hs happ) op.cost (hcost op hop)

/-- Never overestimates the cost of reaching the goal. -/
theorem improved_admissible (t : Task)
    (c1 : ∀ g ∈ (compile t).images, g.goalFact ∈ t.goal)
    (c2 : ∀ g ∈ (compile t).pointingGoals, g.goalFact ∈ t.goal)
    (heff : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      Effect (compile t) s (op.apply s))
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost) :
    t.Admissible (improved t).eval :=
  t.admissible _ (improved_goalAware t c1 c2) (improved_consistent t heff hcost)


/-! ### Discharging the goal-count components from the operator

The goal counts follow from decidable facts about the operator — which of each
family's goals it adds and deletes — so a certificate can establish them rather
than a hypothesis assuming them.
-/

theorem imageCount_drop_one (d : Data) {n : Nat} {op : Op} {s : State}
    (hop : Op.WF n op) (hs : State.WF n s) (hnd : (d.images).toList.Nodup)
    (x : _) (hx : x ∈ d.images)
    (hxadd : op.add.contains ((·.goalFact) x) = true) (hxs : s.test ((·.goalFact) x) = false)
    (hother : ∀ y ∈ d.images, y ≠ x → op.add.contains ((·.goalFact) y) = false)
    (hdel : ∀ y ∈ d.images, op.del.contains ((·.goalFact) y) = false) :
    ((d.images).filter fun y => !(op.apply s).test ((·.goalFact) y)).size + 1
      = ((d.images).filter fun y => !s.test ((·.goalFact) y)).size :=
  unmet_drop_one d.images (·.goalFact) hop hs hnd x hx hxadd hxs hother hdel

theorem imageCount_unchanged (d : Data) {n : Nat} {op : Op} {s : State}
    (hop : Op.WF n op) (hs : State.WF n s)
    (hadd : ∀ y ∈ d.images, op.add.contains ((·.goalFact) y) = false)
    (hdel : ∀ y ∈ d.images, op.del.contains ((·.goalFact) y) = false) :
    ((d.images).filter fun y => !(op.apply s).test ((·.goalFact) y)).size
      = ((d.images).filter fun y => !s.test ((·.goalFact) y)).size :=
  unmet_unchanged d.images (·.goalFact) hop hs hadd hdel

theorem pointingCount_drop_one (d : Data) {n : Nat} {op : Op} {s : State}
    (hop : Op.WF n op) (hs : State.WF n s) (hnd : (d.pointingGoals).toList.Nodup)
    (x : _) (hx : x ∈ d.pointingGoals)
    (hxadd : op.add.contains ((·.goalFact) x) = true) (hxs : s.test ((·.goalFact) x) = false)
    (hother : ∀ y ∈ d.pointingGoals, y ≠ x → op.add.contains ((·.goalFact) y) = false)
    (hdel : ∀ y ∈ d.pointingGoals, op.del.contains ((·.goalFact) y) = false) :
    ((d.pointingGoals).filter fun y => !(op.apply s).test ((·.goalFact) y)).size + 1
      = ((d.pointingGoals).filter fun y => !s.test ((·.goalFact) y)).size :=
  unmet_drop_one d.pointingGoals (·.goalFact) hop hs hnd x hx hxadd hxs hother hdel

theorem pointingCount_unchanged (d : Data) {n : Nat} {op : Op} {s : State}
    (hop : Op.WF n op) (hs : State.WF n s)
    (hadd : ∀ y ∈ d.pointingGoals, op.add.contains ((·.goalFact) y) = false)
    (hdel : ∀ y ∈ d.pointingGoals, op.del.contains ((·.goalFact) y) = false) :
    ((d.pointingGoals).filter fun y => !(op.apply s).test ((·.goalFact) y)).size
      = ((d.pointingGoals).filter fun y => !s.test ((·.goalFact) y)).size :=
  unmet_unchanged d.pointingGoals (·.goalFact) hop hs hadd hdel


/-! ### Discharging the directions an image still needs a turn to

Taking an image removes its direction and cannot add one; a turn changes which
directions are already covered, so the set gains at most one.  Both follow from how the length of a deduplicated list moves.
-/

theorem dirsToTurn_mono (d : Data) (s s' : State) {l l' : List Nat}
    (hl : dirsToTurn d s = distinct l) (hl' : dirsToTurn d s' = distinct l')
    (h : ∀ x ∈ l, x ∈ l') : (dirsToTurn d s).length ≤ (dirsToTurn d s').length := by
  rw [hl, hl']
  exact length_distinct_mono l l' h

theorem dirsToTurn_le_succ (d : Data) (s s' : State) {l l' : List Nat} (a : Nat)
    (hl : dirsToTurn d s = distinct l) (hl' : dirsToTurn d s' = distinct l')
    (h : ∀ x ∈ l, x ∈ l' ∨ x = a) : (dirsToTurn d s).length ≤ (dirsToTurn d s').length + 1 := by
  rw [hl, hl']
  exact length_distinct_le_succ l l' a h

end Planner.ExampleHeuristics.Satellite

/- -------------------------------------------------------------------------- -/
/-
Satellite, stated at the schema level.

`Effect` in `Improved.lean` assumes how one action moves the action count and the
turn count.  This file assumes only what the domain's five schemas do to the
predicates and to the four families the two counts are built from, and derives the
counts.

The two goal counts — images still to take, pointings still to reach — come out of
the goal facts by the standard counting lemmas.  What is still named rather than
derived are two bounds, and both are about the heuristic's own counters rather
than about the predicates:

  * `ReadyStep.instrumentBound` — the two set-cover terms and the free-slot term
    interact, and one instrument action discharges at most one of them;
  * `turnsLe` and `TurnStep.turnBound` — the three turn terms interact and are
    bounded together.

Every shape here used to state its turn behaviour term by term, and the splitting
was **false** in both directions.  Turning a satellite towards a direction an
unmet image needs makes that direction `covered`, so it leaves the list: "a turn
does not shorten the list of directions still to visit" is false of `turn_to`.
And a `switch_off` un-powers an instrument, so a direction it covered *enters*
the list while the instrument's calibration target comes into reach: "no
instrument action shortens the calibration detour" is false of `switch_off`.  A
shape no transition satisfies makes the theorem resting on it say nothing about
real satellite tasks.

So all three shapes bound the turn count jointly, which is what the informal
argument in the header of `Improved.lean` claims, what `Planner/ShapeSpecs.lean`
walks, and what `Proofs/Lifted/SatelliteClosed.lean` proves of every grounded
operator.
-/

namespace Planner.ExampleHeuristics.Satellite

open Planner

/-- Still to photograph. -/
def liveImg (s : State) (g : ImageGoal) : Bool := !s.test g.goalFact
/-- Still to point at. -/
def livePt (s : State) (g : PointingGoal) : Bool := !s.test g.goalFact

theorem unmetImages_eq (d : Data) (s : State) :
    (unmetImages d s).size = (d.images.toList.filter (liveImg s)).length := by
  unfold unmetImages liveImg
  rw [size_filter_toList]

theorem unmetPointing_eq (d : Data) (s : State) :
    (unmetPointing d s).size = (d.pointingGoals.toList.filter (livePt s)).length := by
  unfold unmetPointing livePt
  rw [size_filter_toList]

/-- The three instrument terms of the action count, taken together. -/
def instruments (d : Data) (s : State) : Nat :=
  coverCount d (uncalibratedModes d s) + coverCount d (unpoweredModes d s) + freeSlot d s

theorem actionCount_eq (d : Data) (s : State) :
    actionCount d s = (unmetImages d s).size + instruments d s := by
  unfold actionCount instruments
  omega

theorem turns_eq (d : Data) (s : State) :
    turns d s = (unmetPointing d s).size + (dirsToTurn d s).length + approach d s := rfl

/-! ### What each schema does -/

/-- `take_image`: one image goal is met by an instrument already ready for it. -/
structure ImageStep (d : Data) (s s' : State) (q : ImageGoal) : Prop where
  memQ : q ∈ d.images
  unmetQ : s.test q.goalFact = false
  metQ' : s'.test q.goalFact = true
  frameImages : ∀ g ∈ d.images, g ≠ q → s'.test g.goalFact = s.test g.goalFact
  /--
  The mode was supported by a ready, powered instrument, so it was in neither
  uncovered set, and neither cover count moves.

  The free-slot term *can* move, which is why this is an inequality and not an
  equation.  `slotFree` asks for an instrument that supports a **needed** mode
  and has a spare power slot.  Taking the image can stop a mode being needed,
  and the only instrument with a spare slot may be one that supported just that
  mode — so `slotFree` falls away and `freeSlot` rises from `0` to `1`.  The
  count of images falls by exactly one at the same time, so this direction is
  the one consistency needs.
  -/
  instrumentsLe : instruments d s ≤ instruments d s'
  /-- The satellite was already pointing at the direction, so no turn is
  discharged: the three turn terms together do not fall. -/
  turnsLe : turns d s ≤ turns d s'

/-- `switch_on`, `switch_off` and `calibrate`: only the instruments move. -/
structure ReadyStep (d : Data) (s s' : State) : Prop where
  frameImages : ∀ g ∈ d.images, s'.test g.goalFact = s.test g.goalFact
  /-- One instrument action discharges at most one of the three instrument bounds. -/
  instrumentBound : instruments d s ≤ instruments d s' + 1
  /--
  Nothing turns, so the three turn terms together do not fall.

  Term by term this is false.  A `switch_off` un-powers an instrument, so a
  direction that instrument covered enters `dirsToTurn` while its calibration
  target comes into reach and `approach` falls.  Only the sum is monotone.
  -/
  turnsLe : turns d s ≤ turns d s'

/--
`turn_to`: the satellite turns; no instrument and no image moves.

The turn count has to be bounded **jointly**, not term by term.  A turn towards a
direction an unmet image needs makes that direction `covered`, so `dirsToTurn`
really can get shorter — measuring says it does, on every satellite task tried.
What stays true is that the two deployed turn terms together fall by at most one.
-/
structure TurnStep (d : Data) (s s' : State) : Prop where
  frameImages : ∀ g ∈ d.images, s'.test g.goalFact = s.test g.goalFact
  instrumentsSame : instruments d s' = instruments d s
  /-- One turn discharges at most one turn. -/
  turnBound : turns d s ≤ turns d s' + 1

/-- One action of the domain. -/
inductive SchemaStep (d : Data) (s s' : State) : Prop
  | image (q : ImageGoal) (h : ImageStep d s s' q)
  | ready (h : ReadyStep d s s')
  | turn (h : TurnStep d s s')

/-! ### The counters, derived from the shapes -/

theorem unmetImages_congr {d : Data} {s s' : State}
    (h : ∀ g ∈ d.images, s'.test g.goalFact = s.test g.goalFact) :
    (unmetImages d s').size = (unmetImages d s).size := by
  rw [unmetImages_eq, unmetImages_eq]
  exact length_filter_congr _ _ _ fun y hy => by simp [liveImg, h y (by simpa using hy)]

theorem unmetPointing_congr {d : Data} {s s' : State}
    (h : ∀ g ∈ d.pointingGoals, s'.test g.goalFact = s.test g.goalFact) :
    (unmetPointing d s').size = (unmetPointing d s).size := by
  rw [unmetPointing_eq, unmetPointing_eq]
  exact length_filter_congr _ _ _ fun y hy => by simp [livePt, h y (by simpa using hy)]

theorem ImageStep.images_drop {d : Data} {s s' : State} {q : ImageGoal}
    (h : ImageStep d s s' q) (hnd : d.images.toList.Nodup) :
    (unmetImages d s').size + 1 = (unmetImages d s).size := by
  rw [unmetImages_eq, unmetImages_eq]
  refine length_filter_erase_one _ (liveImg s) (liveImg s') q (by simpa using h.memQ) hnd
    (by simp [liveImg, h.unmetQ]) (by simp [liveImg, h.metQ']) ?_
  intro y hy hne
  simp [liveImg, h.frameImages y (by simpa using hy) hne]

/--
A *sufficient* condition for the joint turn bound: an action that moves no
pointing goal, discharges no direction and shortens no detour does not lower the
turn count.

Not a necessary one, and not one every non-turn action meets — `switch_off`
trades the second term against the third.  Use it for the actions that leave all
three alone, and prove `turnsLe` directly for the rest.
-/
theorem turns_le_of_parts {d : Data} {s s' : State}
    (hp : ∀ g ∈ d.pointingGoals, s'.test g.goalFact = s.test g.goalFact)
    (hd : (dirsToTurn d s).length ≤ (dirsToTurn d s').length)
    (ha : approach d s ≤ approach d s') : turns d s ≤ turns d s' := by
  rw [turns_eq, turns_eq, unmetPointing_congr hp]
  omega

theorem effect_of_schema (d : Data) (s s' : State) (hnd : d.images.toList.Nodup)
    (he : SchemaStep d s s') : Effect d s s' := by
  cases he with
  | image q h =>
      refine .image ?_ h.turnsLe
      show actionCount d s ≤ actionCount d s' + 1
      rw [actionCount_eq, actionCount_eq]
      have := h.images_drop hnd
      have := h.instrumentsLe
      omega
  | ready h =>
      refine .ready ?_ h.turnsLe
      show actionCount d s ≤ actionCount d s' + 1
      rw [actionCount_eq, actionCount_eq, unmetImages_congr h.frameImages]
      have := h.instrumentBound
      omega
  | turn h =>
      refine .turn ?_ ?_
      · show actionCount d s ≤ actionCount d s'
        rw [actionCount_eq, actionCount_eq, unmetImages_congr h.frameImages,
          h.instrumentsSame]
      · exact h.turnBound

/-- Zero at every goal state, assuming only what the schemas do. -/
theorem improved_goalAware_of_schema (t : Task)
    (himg : ∀ g ∈ (compile t).images, g.goalFact ∈ t.goal)
    (hpt : ∀ g ∈ (compile t).pointingGoals, g.goalFact ∈ t.goal) :
    t.GoalAware (improved t).eval := improved_goalAware t himg hpt

/-- And never falls by more than one action costs. -/
theorem improved_consistent_of_schema (t : Task)
    (hnd : (compile t).images.toList.Nodup)
    (hstep : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      SchemaStep (compile t) s (op.apply s))
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost) :
    t.Consistent (improved t).eval :=
  improved_consistent t
    (fun op hop s hs happ => effect_of_schema _ s _ hnd (hstep op hop s hs happ)) hcost

/-- Never overestimates, assuming only that every operator is one of the schemas. -/
theorem improved_admissible_of_schema (t : Task)
    (himg : ∀ g ∈ (compile t).images, g.goalFact ∈ t.goal)
    (hpt : ∀ g ∈ (compile t).pointingGoals, g.goalFact ∈ t.goal)
    (hnd : (compile t).images.toList.Nodup)
    (hstep : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      SchemaStep (compile t) s (op.apply s))
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost) :
    t.Admissible (improved t).eval :=
  t.admissible _ (improved_goalAware_of_schema t himg hpt)
    (improved_consistent_of_schema t hnd hstep hcost)

end Planner.ExampleHeuristics.Satellite

/- -------------------------------------------------------------------------- -/
/-
Which domain a Satellite task came from.

The equation on `actions` fixes the five schemas exactly as the parser produces
them.  The remaining lemmas expose their instantiated atoms, which lets the
heuristic proof reason about one lifted transition without mentioning grounding
or fact numbers.
-/

namespace Planner.Lifted.Satellite

open Planner Planner.Pddl

/-! ### The domain's atoms -/

abbrev pointing (s d : Name) : GroundAtom := { pred := "pointing", args := [s, d] }
abbrev notPointing (s d : Name) : GroundAtom := { pred := "not-pointing", args := [s, d] }
abbrev powerOn (i : Name) : GroundAtom := { pred := "power_on", args := [i] }
abbrev powerAvail (s : Name) : GroundAtom := { pred := "power_avail", args := [s] }
abbrev calibrated (i : Name) : GroundAtom := { pred := "calibrated", args := [i] }
abbrev onBoard (i s : Name) : GroundAtom := { pred := "on_board", args := [i, s] }
abbrev calibTarget (i d : Name) : GroundAtom :=
  { pred := "calibration_target", args := [i, d] }
abbrev supports (i m : Name) : GroundAtom := { pred := "supports", args := [i, m] }
abbrev haveImage (d m : Name) : GroundAtom := { pred := "have_image", args := [d, m] }

/-! ### The schemas, as the parser produces them -/

abbrev satP (n : Name) : TypedName := { name := n, type := "satellite" }
abbrev dirP (n : Name) : TypedName := { name := n, type := "direction" }
abbrev insP (n : Name) : TypedName := { name := n, type := "instrument" }
abbrev modeP (n : Name) : TypedName := { name := n, type := "mode" }

abbrev pointingV (s d : Name) : Atom := { pred := "pointing", args := [.var s, .var d] }
abbrev notPointingV (s d : Name) : Atom :=
  { pred := "not-pointing", args := [.var s, .var d] }
abbrev powerOnV (i : Name) : Atom := { pred := "power_on", args := [.var i] }
abbrev powerAvailV (s : Name) : Atom := { pred := "power_avail", args := [.var s] }
abbrev calibratedV (i : Name) : Atom := { pred := "calibrated", args := [.var i] }
abbrev onBoardV (i s : Name) : Atom := { pred := "on_board", args := [.var i, .var s] }
abbrev calibTargetV (i d : Name) : Atom :=
  { pred := "calibration_target", args := [.var i, .var d] }
abbrev supportsV (i m : Name) : Atom := { pred := "supports", args := [.var i, .var m] }
abbrev haveImageV (d m : Name) : Atom := { pred := "have_image", args := [.var d, .var m] }

abbrev turnA : Action := Planner.GeneratedDomains.Satellite.action0
abbrev switchOnA : Action := Planner.GeneratedDomains.Satellite.action1
abbrev switchOffA : Action := Planner.GeneratedDomains.Satellite.action2
abbrev calibrateA : Action := Planner.GeneratedDomains.Satellite.action3
abbrev imageA : Action := Planner.GeneratedDomains.Satellite.action4

/-- The parsed domain is Satellite. -/
abbrev SatelliteDomain (d : Domain) : Prop :=
  d.actions = Planner.GeneratedDomains.Satellite.actions

theorem pointing_dynamic {d : Domain} (hd : SatelliteDomain d) :
    (staticPredicates d).contains "pointing" = false :=
  not_static_of_mem_add (a := turnA) (by rw [hd]; simp) (y := pointingV "?s" "?d_new")
    (by simp [turnA])

theorem powerOn_dynamic {d : Domain} (hd : SatelliteDomain d) :
    (staticPredicates d).contains "power_on" = false :=
  not_static_of_mem_add (a := switchOnA) (by rw [hd]; simp) (y := powerOnV "?i")
    (by simp [switchOnA])

theorem powerAvail_dynamic {d : Domain} (hd : SatelliteDomain d) :
    (staticPredicates d).contains "power_avail" = false :=
  not_static_of_mem_del (a := switchOnA) (by rw [hd]; simp) (y := powerAvailV "?s")
    (by simp [switchOnA])

theorem calibrated_dynamic {d : Domain} (hd : SatelliteDomain d) :
    (staticPredicates d).contains "calibrated" = false :=
  not_static_of_mem_add (a := calibrateA) (by rw [hd]; simp) (y := calibratedV "?i")
    (by simp [calibrateA])

theorem haveImage_dynamic {d : Domain} (hd : SatelliteDomain d) :
    (staticPredicates d).contains "have_image" = false :=
  not_static_of_mem_add (a := imageA) (by rw [hd]; simp) (y := haveImageV "?d" "?m")
    (by simp [imageA])

/-! ### Instances -/

theorem instance_shape {d : Domain} {objects : List TypedName} (hd : SatelliteDomain d)
    (i : Instance d objects) :
    (∃ s dn dp, i.schema = turnA ∧ i.args = [s, dn, dp]) ∨
    (∃ ins s, i.schema = switchOnA ∧ i.args = [ins, s]) ∨
    (∃ ins s, i.schema = switchOffA ∧ i.args = [ins, s]) ∨
    (∃ s ins dir, i.schema = calibrateA ∧ i.args = [s, ins, dir]) ∨
    (∃ s dir ins m, i.schema = imageA ∧ i.args = [s, dir, ins, m]) := by
  have hmem : i.schema ∈ [turnA, switchOnA, switchOffA, calibrateA, imageA] := by
    have hm : i.schema ∈ d.actions := i.mem
    rw [hd] at hm
    exact hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with hs | hs | hs | hs | hs
  · obtain ⟨s, dn, dp, ha, -, -, -⟩ := i.args_three (by rw [hs])
    exact Or.inl ⟨s, dn, dp, hs, ha⟩
  · obtain ⟨ins, s, ha, -, -⟩ := i.args_two (by rw [hs])
    exact Or.inr (Or.inl ⟨ins, s, hs, ha⟩)
  · obtain ⟨ins, s, ha, -, -⟩ := i.args_two (by rw [hs])
    exact Or.inr (Or.inr (Or.inl ⟨ins, s, hs, ha⟩))
  · obtain ⟨s, ins, dir, ha, -, -, -⟩ := i.args_three (by rw [hs])
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨s, ins, dir, hs, ha⟩)))
  · obtain ⟨s, dir, ins, m, ha, -, -, -, -⟩ := i.args_four (by rw [hs])
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨s, dir, ins, m, hs, ha⟩)))

theorem turn_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {s dn dp : Name} (hs : i.schema = turnA) (ha : i.args = [s, dn, dp]) :
    pointing s dp ∈ i.pre ∧ i.add = [pointing s dn, notPointing s dp] ∧
      i.del = [notPointing s dn, pointing s dp] := by
  have hp : i.pre = [pointing s dp, notPointing s dn] := by rw [i.pre_eq, hs, ha]; rfl
  have hadd : i.add = [pointing s dn, notPointing s dp] := by rw [i.add_eq, hs, ha]; rfl
  have hdel : i.del = [notPointing s dn, pointing s dp] := by rw [i.del_eq, hs, ha]; rfl
  simp [hp, hadd, hdel]

theorem switchOn_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {ins s : Name} (hs : i.schema = switchOnA) (ha : i.args = [ins, s]) :
    powerAvail s ∈ i.pre ∧ i.add = [powerOn ins] ∧
      i.del = [calibrated ins, powerAvail s] := by
  have hp : i.pre = [onBoard ins s, powerAvail s] := by rw [i.pre_eq, hs, ha]; rfl
  have hadd : i.add = [powerOn ins] := by rw [i.add_eq, hs, ha]; rfl
  have hdel : i.del = [calibrated ins, powerAvail s] := by rw [i.del_eq, hs, ha]; rfl
  simp [hp, hadd, hdel]

theorem switchOff_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {ins s : Name} (hs : i.schema = switchOffA) (ha : i.args = [ins, s]) :
    powerOn ins ∈ i.pre ∧ i.add = [powerAvail s] ∧ i.del = [powerOn ins] := by
  have hp : i.pre = [onBoard ins s, powerOn ins] := by rw [i.pre_eq, hs, ha]; rfl
  have hadd : i.add = [powerAvail s] := by rw [i.add_eq, hs, ha]; rfl
  have hdel : i.del = [powerOn ins] := by rw [i.del_eq, hs, ha]; rfl
  simp [hp, hadd, hdel]

theorem calibrate_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {s ins dir : Name} (hs : i.schema = calibrateA) (ha : i.args = [s, ins, dir]) :
    pointing s dir ∈ i.pre ∧ powerOn ins ∈ i.pre ∧
      i.add = [calibrated ins] ∧ i.del = [] := by
  have hp : i.pre = [onBoard ins s, calibTarget ins dir, pointing s dir, powerOn ins] := by
    rw [i.pre_eq, hs, ha]; rfl
  have hadd : i.add = [calibrated ins] := by rw [i.add_eq, hs, ha]; rfl
  have hdel : i.del = [] := by rw [i.del_eq, hs, ha]; rfl
  simp [hp, hadd, hdel]

theorem image_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {s dir ins m : Name} (hs : i.schema = imageA) (ha : i.args = [s, dir, ins, m]) :
    calibrated ins ∈ i.pre ∧ powerOn ins ∈ i.pre ∧ pointing s dir ∈ i.pre ∧
      i.add = [haveImage dir m] ∧ i.del = [] := by
  have hp : i.pre = [calibrated ins, onBoard ins s, supports ins m, powerOn ins,
      pointing s dir] := by rw [i.pre_eq, hs, ha]; rfl
  have hadd : i.add = [haveImage dir m] := by rw [i.add_eq, hs, ha]; rfl
  have hdel : i.del = [] := by rw [i.del_eq, hs, ha]; rfl
  simp [hp, hadd, hdel]

end Planner.Lifted.Satellite

/- -------------------------------------------------------------------------- -/
/-
Satellite's improved heuristic over ground atoms.

The data has the same shape as the compiled heuristic, but its tables contain
atoms instead of fact numbers.  This keeps the value close to the executable one
while making the consistency argument independent of grounding.
-/

namespace Planner.Lifted.Satellite

open Planner Planner.Pddl

/-- An unmet `have_image` goal. -/
structure ImageGoal where
  goalAtom : GroundAtom
  dir : Nat
  mode : Nat
  deriving Inhabited

/-- A `pointing` goal: which satellite must end up looking where. -/
structure PointingGoal where
  goalAtom : GroundAtom
  sat : Nat
  dir : Nat
  deriving Inhabited

structure Cfg where
  images : Array ImageGoal
  pointingGoals : Array PointingGoal
  calibratedAtoms : Array (Option GroundAtom)
  powerOnAtoms : Array (Option GroundAtom)
  powerAvailAtoms : Array (Option GroundAtom)
  supports : Array (Array Nat)
  onBoard : Array (Array Nat)
  calibTarget : Array (Option Nat)
  satelliteOf : Array (Option Nat)
  pointingByDir : Array (Array (GroundAtom × Nat))
  deriving Inhabited

@[inline] def activeInstruments (atoms : Array (Option GroundAtom)) (σ : AtomState) :
    Array Nat :=
  atoms.zipIdx.filterMap fun x =>
    match x.1 with
    | some a => if σ a then some x.2 else none
    | none => none

@[inline] def calibratedNow (c : Cfg) (σ : AtomState) : Array Nat :=
  activeInstruments c.calibratedAtoms σ
@[inline] def poweredNow (c : Cfg) (σ : AtomState) : Array Nat :=
  activeInstruments c.powerOnAtoms σ
@[inline] def readyNow (c : Cfg) (σ : AtomState) : Array Nat :=
  (calibratedNow c σ).filter (poweredNow c σ).contains

@[inline] def unmetImages (c : Cfg) (σ : AtomState) : Array ImageGoal :=
  c.images.filter fun g => !σ g.goalAtom
@[inline] def unmetPointing (c : Cfg) (σ : AtomState) : Array PointingGoal :=
  c.pointingGoals.filter fun g => !σ g.goalAtom

@[inline] def supportsMode (c : Cfg) (set : Array Nat) (m : Nat) : Bool :=
  set.any fun i => (c.supports.getD i #[]).contains m

@[inline] def pointsAt (c : Cfg) (σ : AtomState) (sat dir : Nat) : Bool :=
  (c.pointingByDir.getD dir #[]).any fun x => x.2 == sat && σ x.1

@[inline] def covered (c : Cfg) (σ : AtomState) (dir mode : Nat) : Bool :=
  (c.pointingByDir.getD dir #[]).any fun x =>
    σ x.1 &&
      (c.onBoard.getD x.2 #[]).any fun ins =>
        (c.supports.getD ins #[]).contains mode &&
          ((readyNow c σ).contains ins || c.calibTarget.getD ins none == some dir)

@[inline] def paidByGoal (c : Cfg) (σ : AtomState) (dir : Nat) : Bool :=
  (unmetPointing c σ).any fun g => g.dir == dir

@[inline] def dirsToTurn (c : Cfg) (σ : AtomState) : List Nat :=
  distinct ((unmetImages c σ).toList.filterMap fun img =>
    if !paidByGoal c σ img.dir && !covered c σ img.dir img.mode then some img.dir else none)

@[inline] def neededModes (c : Cfg) (σ : AtomState) : List Nat :=
  distinct ((unmetImages c σ).toList.map (·.mode))

@[inline] def uncalibratedModes (c : Cfg) (σ : AtomState) : List Nat :=
  (neededModes c σ).filter fun m => !supportsMode c (readyNow c σ) m
@[inline] def unpoweredModes (c : Cfg) (σ : AtomState) : List Nat :=
  (neededModes c σ).filter fun m => !supportsMode c (poweredNow c σ) m

@[inline] def coverCount (c : Cfg) (modesLeft : List Nat) : Nat :=
  if modesLeft.isEmpty then 0
  else if c.supports.any fun modesOf => modesLeft.all modesOf.contains then 1
  else 2

@[inline] def calibrationInReach (c : Cfg) (σ : AtomState) : Bool :=
  c.supports.zipIdx.any fun x =>
    x.1.any (neededModes c σ).contains &&
      (match c.calibTarget.getD x.2 none, c.satelliteOf.getD x.2 none with
       | some target, some sat =>
           pointsAt c σ sat target || (dirsToTurn c σ).contains target ||
             (unmetPointing c σ).any fun g => g.dir == target
       | _, _ => true)

@[inline] def approach (c : Cfg) (σ : AtomState) : Nat :=
  if !(uncalibratedModes c σ).isEmpty && !calibrationInReach c σ then 1 else 0

@[inline] def slotFree (c : Cfg) (σ : AtomState) : Bool :=
  c.supports.zipIdx.any fun x =>
    x.1.any (neededModes c σ).contains &&
      (match c.satelliteOf.getD x.2 none with
       | some sat =>
           (match c.powerAvailAtoms.getD sat none with
            | some a => σ a
            | none => true)
       | none => true)

@[inline] def freeSlot (c : Cfg) (σ : AtomState) : Nat :=
  if !(unpoweredModes c σ).isEmpty && !slotFree c σ then 1 else 0

@[inline] def actionCount (c : Cfg) (σ : AtomState) : Nat :=
  (unmetImages c σ).size + coverCount c (uncalibratedModes c σ)
    + coverCount c (unpoweredModes c σ) + freeSlot c σ

@[inline] def turns (c : Cfg) (σ : AtomState) : Nat :=
  (unmetPointing c σ).size + (dirsToTurn c σ).length + approach c σ

def value (c : Cfg) (σ : AtomState) : Nat := actionCount c σ + turns c σ

/-! ### The two quantities -/

/-- Images, calibrations and power: everything that is not a turn. -/
abbrev Ac (c : Cfg) (σ : AtomState) : Nat := actionCount c σ
/-- Turns. -/
abbrev Tc (c : Cfg) (σ : AtomState) : Nat := turns c σ

/-- The three instrument terms of the action count, taken together. -/
def instruments (c : Cfg) (σ : AtomState) : Nat :=
  coverCount c (uncalibratedModes c σ) + coverCount c (unpoweredModes c σ) + freeSlot c σ

theorem actionCount_eq (c : Cfg) (σ : AtomState) :
    actionCount c σ = (unmetImages c σ).size + instruments c σ := by
  unfold actionCount instruments
  omega

theorem turns_eq (c : Cfg) (σ : AtomState) :
    turns c σ = (unmetPointing c σ).size + (dirsToTurn c σ).length + approach c σ := rfl

/-! ### Counting the unmet goals -/

/-- Still to photograph. -/
def liveImg (σ : AtomState) (g : ImageGoal) : Bool := !σ g.goalAtom
/-- Still to point at. -/
def livePt (σ : AtomState) (g : PointingGoal) : Bool := !σ g.goalAtom

theorem unmetImages_eq (c : Cfg) (σ : AtomState) :
    (unmetImages c σ).size = (c.images.toList.filter (liveImg σ)).length := by
  unfold unmetImages liveImg
  rw [size_filter_toList]

theorem unmetPointing_eq (c : Cfg) (σ : AtomState) :
    (unmetPointing c σ).size = (c.pointingGoals.toList.filter (livePt σ)).length := by
  unfold unmetPointing livePt
  rw [size_filter_toList]

/-! ### Goal awareness -/

theorem unmet_empty (c : Cfg) (σ : AtomState)
    (h1 : ∀ g ∈ c.images, σ g.goalAtom = true)
    (h2 : ∀ g ∈ c.pointingGoals, σ g.goalAtom = true) :
    unmetImages c σ = #[] ∧ unmetPointing c σ = #[] := by
  constructor
  · unfold unmetImages
    rw [Array.filter_eq_empty_iff]
    intro x hx; simp [h1 x hx]
  · unfold unmetPointing
    rw [Array.filter_eq_empty_iff]
    intro x hx; simp [h2 x hx]

theorem value_eq_zero (c : Cfg) (σ : AtomState)
    (h1 : ∀ g ∈ c.images, σ g.goalAtom = true)
    (h2 : ∀ g ∈ c.pointingGoals, σ g.goalAtom = true) : value c σ = 0 := by
  obtain ⟨e1, e2⟩ := unmet_empty c σ h1 h2
  have hneeded : neededModes c σ = [] := by
    unfold neededModes
    rw [e1]
    rfl
  have huncal : uncalibratedModes c σ = [] := by
    simp [uncalibratedModes, hneeded]
  have happ : approach c σ = 0 := by
    simp [approach, huncal]
  unfold value actionCount turns freeSlot uncalibratedModes unpoweredModes
    neededModes dirsToTurn coverCount
  rw [e1, e2]
  simp [distinct, happ]

theorem liftedGoalAware (p : Problem) (c : Cfg)
    (h1 : ∀ g ∈ c.images, g.goalAtom ∈ p.goal)
    (h2 : ∀ g ∈ c.pointingGoals, g.goalAtom ∈ p.goal) : LiftedGoalAware p (value c) := by
  intro σ hgoal
  exact value_eq_zero c σ (fun g hg => hgoal _ (by simpa using h1 g hg))
    (fun g hg => hgoal _ (by simpa using h2 g hg))

end Planner.Lifted.Satellite

/- -------------------------------------------------------------------------- -/
/-
How Satellite's set-cover terms move.

`instruments` is three terms: the cover count of the modes no ready instrument
supports, the cover count of the modes no powered instrument supports, and the
free-slot term.  `ReadyStep.instrumentBound` says one instrument action moves
their sum by at most one, and that is the only place the three interact.

The lemmas here are what that argument is made of.  `coverCount` is `0` on an
empty list, `1` when one instrument covers everything left, and `2` otherwise —
so it is monotone under inclusion, and it falls by at most one, because a list
that becomes empty was covered by the single instrument that emptied it.
-/

namespace Planner.Lifted.Satellite

open Planner Planner.Pddl

/-! ### Reading the dynamic instrument tables -/

/-- An active-instrument table is unchanged when all atoms it contains keep
their truth value. -/
theorem activeInstruments_congr (atoms : Array (Option GroundAtom)) (σ τ : AtomState)
    (h : ∀ a, some a ∈ atoms → τ a = σ a) :
    activeInstruments atoms τ = activeInstruments atoms σ := by
  apply Array.toList_inj.mp
  simp only [activeInstruments, Array.toList_filterMap]
  refine List.filterMap_congr ?_
  intro x hx
  rw [Array.toList_zipIdx] at hx
  have hxget := List.mem_zipIdx_iff_getElem?.mp hx
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hxget
  rcases ha : x.1 with _ | a
  · simp [ha]
  · have hamem : some a ∈ atoms := by
      have hm : x.1 ∈ atoms.toList := by
        rw [← hget]
        exact List.getElem_mem hlt
      simpa [ha] using hm
    simp [ha, h a hamem]

theorem calibratedNow_congr (c : Cfg) (σ τ : AtomState)
    (h : ∀ a, some a ∈ c.calibratedAtoms → τ a = σ a) :
    calibratedNow c τ = calibratedNow c σ :=
  activeInstruments_congr c.calibratedAtoms σ τ h

theorem poweredNow_congr (c : Cfg) (σ τ : AtomState)
    (h : ∀ a, some a ∈ c.powerOnAtoms → τ a = σ a) :
    poweredNow c τ = poweredNow c σ :=
  activeInstruments_congr c.powerOnAtoms σ τ h

theorem readyNow_congr (c : Cfg) (σ τ : AtomState)
    (hc : ∀ a, some a ∈ c.calibratedAtoms → τ a = σ a)
    (hp : ∀ a, some a ∈ c.powerOnAtoms → τ a = σ a) :
    readyNow c τ = readyNow c σ := by
  unfold readyNow
  rw [calibratedNow_congr c σ τ hc, poweredNow_congr c σ τ hp]

/-- The exact unmet-image table is unchanged when every image goal is framed. -/
theorem unmetImages_array_congr (c : Cfg) (σ τ : AtomState)
    (h : ∀ g ∈ c.images, τ g.goalAtom = σ g.goalAtom) :
    unmetImages c τ = unmetImages c σ := by
  apply Array.toList_inj.mp
  simp only [unmetImages, Array.toList_filter]
  exact List.filter_congr fun g hg => by rw [h g (by simpa using hg)]

theorem neededModes_congr (c : Cfg) (σ τ : AtomState)
    (h : ∀ g ∈ c.images, τ g.goalAtom = σ g.goalAtom) :
    neededModes c τ = neededModes c σ := by
  unfold neededModes
  rw [unmetImages_array_congr c σ τ h]

theorem uncalibratedModes_congr (c : Cfg) (σ τ : AtomState)
    (hi : ∀ g ∈ c.images, τ g.goalAtom = σ g.goalAtom)
    (hc : ∀ a, some a ∈ c.calibratedAtoms → τ a = σ a)
    (hp : ∀ a, some a ∈ c.powerOnAtoms → τ a = σ a) :
    uncalibratedModes c τ = uncalibratedModes c σ := by
  unfold uncalibratedModes
  rw [neededModes_congr c σ τ hi, readyNow_congr c σ τ hc hp]

theorem unpoweredModes_congr (c : Cfg) (σ τ : AtomState)
    (hi : ∀ g ∈ c.images, τ g.goalAtom = σ g.goalAtom)
    (hp : ∀ a, some a ∈ c.powerOnAtoms → τ a = σ a) :
    unpoweredModes c τ = unpoweredModes c σ := by
  unfold unpoweredModes
  rw [neededModes_congr c σ τ hi, poweredNow_congr c σ τ hp]

theorem mem_of_getD_some {α : Type} {xs : Array (Option α)} {i : Nat} {a : α}
    (h : xs.getD i none = some a) : some a ∈ xs := by
  by_cases hi : i < xs.size
  · have hget : xs[i] = some a := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi] at h
      simpa using h
    rw [← hget]
    exact Array.getElem_mem hi
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_gt hi)] at h
    simp at h

theorem slotFree_congr (c : Cfg) (σ τ : AtomState)
    (hi : ∀ g ∈ c.images, τ g.goalAtom = σ g.goalAtom)
    (ha : ∀ a, some a ∈ c.powerAvailAtoms → τ a = σ a) :
    slotFree c τ = slotFree c σ := by
  unfold slotFree
  rw [neededModes_congr c σ τ hi]
  refine array_any_congr _ _ _ fun x hx => ?_
  congr 1
  rcases hs : c.satelliteOf.getD x.2 none with _ | sat
  · simp [hs]
  · rcases hp : c.powerAvailAtoms.getD sat none with _ | a
    · simp [hs, hp]
    · simp [hs, hp, ha a (mem_of_getD_some hp)]

theorem freeSlot_congr (c : Cfg) (σ τ : AtomState)
    (hi : ∀ g ∈ c.images, τ g.goalAtom = σ g.goalAtom)
    (hp : ∀ a, some a ∈ c.powerOnAtoms → τ a = σ a)
    (ha : ∀ a, some a ∈ c.powerAvailAtoms → τ a = σ a) :
    freeSlot c τ = freeSlot c σ := by
  unfold freeSlot
  rw [unpoweredModes_congr c σ τ hi hp, slotFree_congr c σ τ hi ha]

/-- The three instrument terms are exactly framed when images, calibration,
power, and free-power-slot atoms are framed. -/
theorem instruments_congr (c : Cfg) (σ τ : AtomState)
    (hi : ∀ g ∈ c.images, τ g.goalAtom = σ g.goalAtom)
    (hc : ∀ a, some a ∈ c.calibratedAtoms → τ a = σ a)
    (hp : ∀ a, some a ∈ c.powerOnAtoms → τ a = σ a)
    (ha : ∀ a, some a ∈ c.powerAvailAtoms → τ a = σ a) :
    instruments c τ = instruments c σ := by
  unfold instruments
  rw [uncalibratedModes_congr c σ τ hi hc hp,
    unpoweredModes_congr c σ τ hi hp, freeSlot_congr c σ τ hi hp ha]

/-- One instrument covers everything in the list. -/
abbrev Covers (c : Cfg) (l : List Nat) : Prop :=
  (c.supports.any fun ms => l.all ms.contains) = true

/-- An instrument covering a list covers any part of it. -/
theorem covers_mono (c : Cfg) {l l' : List Nat} (hsub : ∀ m ∈ l', m ∈ l)
    (h : Covers c l) : Covers c l' := by
  simp only [Covers, Array.any_eq_true] at h ⊢
  obtain ⟨i, hi, hall⟩ := h
  refine ⟨i, hi, ?_⟩
  simp only [List.all_eq_true] at hall ⊢
  exact fun m hm => hall m (hsub m hm)

theorem coverCount_le_two (c : Cfg) (l : List Nat) : coverCount c l ≤ 2 := by
  unfold coverCount
  split
  · omega
  · split <;> omega

/-- A list still to cover costs at least one action. -/
theorem coverCount_pos (c : Cfg) {l : List Nat} (h : l.isEmpty = false) :
    1 ≤ coverCount c l := by
  unfold coverCount
  rw [if_neg (by simp [h])]
  split <;> omega

theorem coverCount_nil (c : Cfg) {l : List Nat} (h : l.isEmpty = true) :
    coverCount c l = 0 := by
  unfold coverCount; rw [if_pos h]

/-- **The cover count is monotone.**  Fewer modes left never costs more. -/
theorem coverCount_mono (c : Cfg) {l l' : List Nat} (hsub : ∀ m ∈ l', m ∈ l) :
    coverCount c l' ≤ coverCount c l := by
  by_cases he : l'.isEmpty = true
  · rw [coverCount_nil c he]; omega
  · have hlne : l.isEmpty = false := by
      rcases hl : l with _ | ⟨x, rest⟩
      · rcases hl' : l' with _ | ⟨y, r⟩
        · rw [hl'] at he; simp at he
        · exact absurd (hsub y (by rw [hl']; simp)) (by rw [hl]; simp)
      · rfl
    have e1 : coverCount c l' = if Covers c l' then 1 else 2 := by
      unfold coverCount; rw [if_neg he]
    have e2 : coverCount c l = if Covers c l then 1 else 2 := by
      unfold coverCount; rw [if_neg (by simp [hlne])]
    rw [e1, e2]
    by_cases hc : Covers c l
    · have h' := covers_mono c hsub hc
      rw [if_pos h', if_pos hc]
    · rw [if_neg hc]
      split <;> omega

/--
**And it falls by at most one.**

If nothing is left afterwards, one instrument emptied the list, so the list
before cost one action, not two.  If something is left, it costs at least one
already, and nothing costs more than two.
-/
theorem coverCount_le_succ (c : Cfg) (l l' : List Nat)
    (h : l'.isEmpty = true → Covers c l) :
    coverCount c l ≤ coverCount c l' + 1 := by
  by_cases he : l'.isEmpty = true
  · rw [coverCount_nil c he]
    unfold coverCount
    by_cases hl : l.isEmpty = true
    · rw [if_pos hl]; omega
    · rw [if_neg hl, if_pos (h he)]
  · have h1 := coverCount_pos c (by simpa using he)
    have h2 := coverCount_le_two c l
    omega

/-! ### The mode lists

`uncalibratedModes` and `unpoweredModes` are the needed modes that no ready, or
no powered, instrument supports.  Both shrink when the instrument set grows.
-/

/-- A mode a set of instruments supports is supported by any larger set. -/
theorem supportsMode_mono (c : Cfg) {s s' : Array Nat} (h : ∀ i ∈ s, i ∈ s')
    {m : Nat} (hm : supportsMode c s m = true) : supportsMode c s' m = true := by
  simp only [supportsMode, Array.any_eq_true] at hm ⊢
  obtain ⟨i, hi, hcon⟩ := hm
  obtain ⟨j, hj, hget⟩ := Array.getElem_of_mem (h s[i] (Array.getElem_mem hi))
  exact ⟨j, hj, by rw [hget]; exact hcon⟩

/-- Growing the ready set shrinks the uncalibrated modes. -/
theorem uncalibratedModes_sub (c : Cfg) (σ τ : AtomState)
    (hneeded : ∀ m ∈ neededModes c τ, m ∈ neededModes c σ)
    (hready : ∀ i ∈ readyNow c σ, i ∈ readyNow c τ) :
    ∀ m ∈ uncalibratedModes c τ, m ∈ uncalibratedModes c σ := by
  intro m hm
  rw [uncalibratedModes, List.mem_filter] at hm
  obtain ⟨hm1, hm2⟩ := hm
  rw [uncalibratedModes, List.mem_filter]
  refine ⟨hneeded m hm1, ?_⟩
  rcases hs : supportsMode c (readyNow c σ) m with _ | _
  · simp
  · rw [supportsMode_mono c hready hs] at hm2; simp at hm2

/-- Growing the powered set shrinks the unpowered modes. -/
theorem unpoweredModes_sub (c : Cfg) (σ τ : AtomState)
    (hneeded : ∀ m ∈ neededModes c τ, m ∈ neededModes c σ)
    (hpow : ∀ i ∈ poweredNow c σ, i ∈ poweredNow c τ) :
    ∀ m ∈ unpoweredModes c τ, m ∈ unpoweredModes c σ := by
  intro m hm
  rw [unpoweredModes, List.mem_filter] at hm
  obtain ⟨hm1, hm2⟩ := hm
  rw [unpoweredModes, List.mem_filter]
  refine ⟨hneeded m hm1, ?_⟩
  rcases hs : supportsMode c (poweredNow c σ) m with _ | _
  · simp
  · rw [supportsMode_mono c hpow hs] at hm2; simp at hm2

/-! ### The joint bound

`instrumentBound` is the only place the three instrument terms interact.  One
action moves exactly one of them downwards, and never by more than one; the
other two cannot fall.  That is what this states, with the three drops named so
that each schema can say which of them is its own.
-/

/-- **One instrument action moves the three terms by at most one in total.** -/
theorem instruments_le_succ (c : Cfg) (σ τ : AtomState) {du dp df : Nat}
    (hu : coverCount c (uncalibratedModes c σ)
      ≤ coverCount c (uncalibratedModes c τ) + du)
    (hp : coverCount c (unpoweredModes c σ)
      ≤ coverCount c (unpoweredModes c τ) + dp)
    (hf : freeSlot c σ ≤ freeSlot c τ + df)
    (hsum : du + dp + df ≤ 1) :
    instruments c σ ≤ instruments c τ + 1 := by
  unfold instruments
  omega

/-! ### The directions still to turn to

`dirsToTurn` deduplicates the directions of unmet images that no `pointing` goal
pays for and no satellite already covers.  Its length is what the turn terms
count, so what matters is which directions belong — the list before the
deduplication is enough for that.
-/

/-- The directions of unmet images that still need a turn, before deduplication. -/
abbrev dirsList (c : Cfg) (σ : AtomState) : List Nat :=
  (unmetImages c σ).toList.filterMap fun img =>
    if !paidByGoal c σ img.dir && !covered c σ img.dir img.mode then some img.dir
    else none

theorem dirsToTurn_eq (c : Cfg) (σ : AtomState) :
    dirsToTurn c σ = distinct (dirsList c σ) := rfl

/-- **What belongs to that list.** -/
theorem mem_dirsList (c : Cfg) (σ : AtomState) {x : Nat} :
    x ∈ dirsList c σ ↔ ∃ img ∈ unmetImages c σ, img.dir = x ∧
      paidByGoal c σ x = false ∧ covered c σ x img.mode = false := by
  simp only [dirsList, List.mem_filterMap]
  constructor
  · rintro ⟨img, himg, hval⟩
    by_cases h : (!paidByGoal c σ img.dir && !covered c σ img.dir img.mode) = true
    · rw [if_pos h] at hval
      obtain rfl : img.dir = x := by simpa using hval
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
      exact ⟨img, by simpa using himg, rfl, h.1, h.2⟩
    · rw [if_neg h] at hval; simp at hval
  · rintro ⟨img, himg, rfl, hp, hc⟩
    exact ⟨img, by simpa using himg, by rw [if_pos (by simp [hp, hc])]⟩

/-- An image still unmet stays unmet when no image goal moves. -/
theorem mem_unmetImages_of (c : Cfg) {σ τ : AtomState}
    (himg : ∀ g ∈ c.images, τ g.goalAtom = σ g.goalAtom)
    {q : ImageGoal} (hq : q ∈ unmetImages c σ) : q ∈ unmetImages c τ := by
  simp only [unmetImages, Array.mem_filter] at hq ⊢
  exact ⟨hq.1, by rw [himg q hq.1]; exact hq.2⟩

/--
**A direction that still needs a turn keeps needing one, unless it is the one
just turned to.**

Images do not move, `pointing` goals are only met — never unmet — and coverage
is gained only at the new direction.
-/
theorem mem_dirsList_of (c : Cfg) (σ τ : AtomState) (dnew : Nat)
    (himg : ∀ g ∈ c.images, τ g.goalAtom = σ g.goalAtom)
    (hpaid : ∀ x, paidByGoal c τ x = true → paidByGoal c σ x = true)
    (hcov : ∀ x m, x ≠ dnew → covered c τ x m = true → covered c σ x m = true) :
    ∀ x ∈ dirsList c σ, x ∈ dirsList c τ ∨ x = dnew := by
  intro x hx
  obtain ⟨img, hq, rfl, hp, hc⟩ := (mem_dirsList c σ).mp hx
  by_cases hd : img.dir = dnew
  · exact Or.inr hd
  · refine Or.inl ((mem_dirsList c τ).mpr
      ⟨img, mem_unmetImages_of c himg hq, rfl, ?_, ?_⟩)
    · rcases hpt : paidByGoal c τ img.dir with _ | _
      · rfl
      · rw [hpaid _ hpt] at hp; exact absurd hp (by simp)
    · rcases hct : covered c τ img.dir img.mode with _ | _
      · rfl
      · rw [hcov _ _ hd hct] at hc; exact absurd hc (by simp)

/-- The corresponding two-exception form.  A turn can gain coverage at its new
direction, while invalidating the old pointing atom can make that old direction
newly paid for by an unmet goal. -/
theorem mem_dirsList_of_two (c : Cfg) (σ τ : AtomState) (dnew dold : Nat)
    (himg : ∀ g ∈ c.images, τ g.goalAtom = σ g.goalAtom)
    (hpaid : ∀ x, paidByGoal c τ x = true →
      paidByGoal c σ x = true ∨ x = dold)
    (hcov : ∀ x m, x ≠ dnew → covered c τ x m = true →
      covered c σ x m = true) :
    ∀ x ∈ dirsList c σ, x ∈ dirsList c τ ∨ x = dnew ∨ x = dold := by
  intro x hx
  obtain ⟨img, hq, rfl, hp, hc⟩ := (mem_dirsList c σ).mp hx
  by_cases hn : img.dir = dnew
  · exact Or.inr (Or.inl hn)
  by_cases ho : img.dir = dold
  · exact Or.inr (Or.inr ho)
  · refine Or.inl ((mem_dirsList c τ).mpr
      ⟨img, mem_unmetImages_of c himg hq, rfl, ?_, ?_⟩)
    · rcases hpt : paidByGoal c τ img.dir with _ | _
      · rfl
      · rcases hpaid _ hpt with hbefore | heq
        · rw [hbefore] at hp; exact absurd hp (by simp)
        · exact absurd heq ho
    · rcases hct : covered c τ img.dir img.mode with _ | _
      · rfl
      · rw [hcov _ _ hn hct] at hc; exact absurd hc (by simp)

/-- **The turn list never shortens** when nothing stops needing a turn. -/
theorem dirsToTurn_mono (c : Cfg) (σ τ : AtomState)
    (h : ∀ x ∈ dirsList c σ, x ∈ dirsList c τ) :
    (dirsToTurn c σ).length ≤ (dirsToTurn c τ).length :=
  length_distinct_mono _ _ h

/-- **And shortens by at most one** when a single direction may drop out. -/
theorem dirsToTurn_le_succ (c : Cfg) (σ τ : AtomState) (a : Nat)
    (h : ∀ x ∈ dirsList c σ, x ∈ dirsList c τ ∨ x = a) :
    (dirsToTurn c σ).length ≤ (dirsToTurn c τ).length + 1 :=
  length_distinct_le_succ _ _ a h

/-- With two exceptional directions the deduplicated list shortens by at most
two.  The turn proof later pairs the old-direction exception with the pointing
goal that became unmet. -/
theorem dirsToTurn_le_two (c : Cfg) (σ τ : AtomState) (a b : Nat)
    (h : ∀ x ∈ dirsList c σ, x ∈ dirsList c τ ∨ x = a ∨ x = b) :
    (dirsToTurn c σ).length ≤ (dirsToTurn c τ).length + 2 := by
  have h1 := length_distinct_le_succ (dirsList c σ) (a :: dirsList c τ) b
    (fun x hx => by
      rcases h x hx with hm | ha | hb
      · exact Or.inl (by simp [hm])
      · exact Or.inl (by simp [ha])
      · exact Or.inr hb)
  have h2 := length_distinct_le_succ (a :: dirsList c τ) (dirsList c τ) a
    (by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hm
      · exact Or.inr rfl
      · exact Or.inl hm)
  rw [dirsToTurn_eq, dirsToTurn_eq]
  omega

/-! ### The instrument sets

`calibratedNow`, `poweredNow` and `readyNow` are all `activeInstruments` over a
table of optional atoms.  Every step proof needs to know how they move, and all
of that follows from one membership rule.
-/

/-- **An instrument is active exactly when its table entry names a true atom.** -/
theorem mem_activeInstruments {atoms : Array (Option GroundAtom)} {σ : AtomState}
    {i : Nat} :
    i ∈ activeInstruments atoms σ ↔
      ∃ h : i < atoms.size, ∃ a, atoms[i] = some a ∧ σ a = true := by
  simp only [activeInstruments, Array.mem_filterMap]
  constructor
  · rintro ⟨y, hy, hval⟩
    obtain ⟨-, hlt, hget⟩ := Array.mem_zipIdx hy
    simp only [Nat.zero_add, Nat.sub_zero] at hlt hget
    rcases ha : y.1 with _ | a
    · rw [ha] at hval; simp at hval
    · rw [ha] at hval
      dsimp only at hval
      by_cases hs : σ a = true
      · rw [if_pos hs] at hval
        obtain rfl : y.2 = i := by simpa using hval
        exact ⟨hlt, a, by rw [← hget, ha], hs⟩
      · rw [if_neg hs] at hval; simp at hval
  · rintro ⟨hlt, a, hget, hs⟩
    refine ⟨(some a, i), ?_, by simp [hs]⟩
    rw [Array.mem_zipIdx_iff_getElem?]
    simp only [Array.getElem?_eq_getElem hlt, hget]

/-- Active instruments carry over when the atoms their entries name do. -/
theorem activeInstruments_mono {atoms : Array (Option GroundAtom)} {σ τ : AtomState}
    (h : ∀ i, ∀ hi : i < atoms.size, ∀ a, atoms[i] = some a → τ a = true → σ a = true)
    {i : Nat} (hi : i ∈ activeInstruments atoms τ) : i ∈ activeInstruments atoms σ := by
  obtain ⟨hlt, a, hget, hs⟩ := mem_activeInstruments.mp hi
  exact mem_activeInstruments.mpr ⟨hlt, a, hget, h i hlt a hget hs⟩

/-- **The ready set shrinks when neither `calibrated` nor `power_on` grows.** -/
theorem readyNow_mono (c : Cfg) {σ τ : AtomState}
    (hcal : ∀ i, ∀ hi : i < c.calibratedAtoms.size, ∀ a,
      c.calibratedAtoms[i] = some a → τ a = true → σ a = true)
    (hpow : ∀ i, ∀ hi : i < c.powerOnAtoms.size, ∀ a,
      c.powerOnAtoms[i] = some a → τ a = true → σ a = true)
    {i : Nat} (hi : i ∈ readyNow c τ) : i ∈ readyNow c σ := by
  simp only [readyNow, Array.mem_filter] at hi ⊢
  exact ⟨activeInstruments_mono hcal hi.1,
    by simpa using activeInstruments_mono hpow (by simpa using hi.2)⟩

/-- The same, phrased as `contains`, which is how `covered` reads it. -/
theorem readyNow_contains_mono (c : Cfg) {σ τ : AtomState}
    (hcal : ∀ i, ∀ hi : i < c.calibratedAtoms.size, ∀ a,
      c.calibratedAtoms[i] = some a → τ a = true → σ a = true)
    (hpow : ∀ i, ∀ hi : i < c.powerOnAtoms.size, ∀ a,
      c.powerOnAtoms[i] = some a → τ a = true → σ a = true)
    (i : Nat) (hi : (readyNow c τ).contains i = true) :
    (readyNow c σ).contains i = true := by
  simpa using readyNow_mono c hcal hpow (by simpa using hi)

/-! ### What pays for a direction, and what covers it

`paidByGoal` reads the unmet `pointing` goals, so it only shrinks when goals are
met.  `covered` reads the `pointing` atoms and the ready set, so it only shrinks
when neither of those grows — which is the case for every instrument action:
`switch_on` deletes `calibrated`, `switch_off` deletes `power_on`, and both
shrink the ready set.
-/

/-- A goal still unmet afterwards was unmet before: goals are only ever met. -/
theorem mem_unmetPointing_of (c : Cfg) {σ τ : AtomState}
    (h : ∀ g ∈ c.pointingGoals, σ g.goalAtom = true → τ g.goalAtom = true)
    {g : PointingGoal} (hg : g ∈ unmetPointing c τ) : g ∈ unmetPointing c σ := by
  simp only [unmetPointing, Array.mem_filter] at hg ⊢
  refine ⟨hg.1, ?_⟩
  rcases hs : σ g.goalAtom with _ | _
  · simp
  · rw [h g hg.1 hs] at hg; simp at hg

/-- A direction paid for afterwards was paid for before. -/
theorem paidByGoal_mono (c : Cfg) (σ τ : AtomState)
    (h : ∀ g ∈ c.pointingGoals, σ g.goalAtom = true → τ g.goalAtom = true)
    {x : Nat} (hx : paidByGoal c τ x = true) : paidByGoal c σ x = true := by
  simp only [paidByGoal, Array.any_eq_true] at hx ⊢
  obtain ⟨i, hi, hd⟩ := hx
  obtain ⟨j, hj, hget⟩ :=
    Array.getElem_of_mem (mem_unmetPointing_of c h (Array.getElem_mem hi))
  exact ⟨j, hj, by rw [hget]; exact hd⟩

/-- A direction covered afterwards was covered before, when neither the pointing
atoms nor the ready set grew. -/
theorem covered_mono (c : Cfg) (σ τ : AtomState) {x m : Nat}
    (hpoint : ∀ q ∈ c.pointingByDir.getD x #[], τ q.1 = true → σ q.1 = true)
    (hready : ∀ i, (readyNow c τ).contains i = true → (readyNow c σ).contains i = true)
    (h : covered c τ x m = true) : covered c σ x m = true := by
  simp only [covered, Array.any_eq_true] at h ⊢
  obtain ⟨i, hi, hp⟩ := h
  refine ⟨i, hi, ?_⟩
  simp only [Bool.and_eq_true, Array.any_eq_true] at hp ⊢
  refine ⟨hpoint _ (Array.getElem_mem hi) hp.1, ?_⟩
  obtain ⟨j, hj, hq⟩ := hp.2
  refine ⟨j, hj, ?_⟩
  simp only [Bool.or_eq_true] at hq ⊢
  refine ⟨hq.1, ?_⟩
  rcases hq.2 with hr | ht
  · exact Or.inl (hready _ hr)
  · exact Or.inr ht

/-! ### The turn count

`turns` is three terms: the unmet `pointing` goals, the directions still to turn
to, and the calibration detour.  `TurnStep.turnBound` says one turn moves their
sum by at most one, and — like `instrumentBound` — it cannot be split term by
term.  A turn towards a direction an unmet image needs makes that direction
covered, so `dirsToTurn` really does shorten; and meeting a `pointing` goal
un-pays a direction, which can push a *different* direction back into the list.

So the bound is stated the same way: name the drop of each term, and ask only
that they sum to one.  Which term is the turn's own is the step proof's business.
-/

/-- **One turn meets at most one `pointing` goal.** -/
theorem unmetPointing_le_succ (c : Cfg) (σ τ : AtomState) (q : PointingGoal)
    (hnd : c.pointingGoals.toList.Nodup)
    (h : ∀ g ∈ c.pointingGoals, g ≠ q → τ g.goalAtom = σ g.goalAtom) :
    (unmetPointing c σ).size ≤ (unmetPointing c τ).size + 1 := by
  rw [unmetPointing_eq, unmetPointing_eq]
  refine length_filter_le_succ _ _ _ q hnd fun y hy hyq => ?_
  simp [livePt, h y (by simpa using hy) hyq]

/-- The same one-goal bound when other goals may become unmet, but cannot
become met.  This is the form needed by `turn_to`, whose old direction can
invalidate a pointing goal while its new direction meets at most one. -/
theorem unmetPointing_le_succ_mono (c : Cfg) (σ τ : AtomState) (q : PointingGoal)
    (hnd : c.pointingGoals.toList.Nodup)
    (h : ∀ g ∈ c.pointingGoals, g ≠ q → σ g.goalAtom = false →
      τ g.goalAtom = false) :
    (unmetPointing c σ).size ≤ (unmetPointing c τ).size + 1 := by
  rw [unmetPointing_eq, unmetPointing_eq]
  refine length_filter_le_succ_mono _ _ _ q hnd fun y hy hyq hlive => ?_
  have hs : σ y.goalAtom = false := by
    cases hv : σ y.goalAtom <;> simp_all [livePt]
  have ht := h y (by simpa using hy) hyq hs
  simp [livePt, ht]

/-- If no pointing goal can change from unmet to met, their unmet count cannot
decrease. -/
theorem unmetPointing_le_mono (c : Cfg) (σ τ : AtomState)
    (h : ∀ g ∈ c.pointingGoals, σ g.goalAtom = false →
      τ g.goalAtom = false) :
    (unmetPointing c σ).size ≤ (unmetPointing c τ).size := by
  rw [unmetPointing_eq, unmetPointing_eq]
  refine length_filter_mono _ _ _ fun y hy hlive => ?_
  have hs : σ y.goalAtom = false := by
    cases hv : σ y.goalAtom <;> simp_all [livePt]
  have ht := h y (by simpa using hy) hs
  simp [livePt, ht]

/-- And meets none at all when no `pointing` goal atom moves. -/
theorem unmetPointing_le (c : Cfg) (σ τ : AtomState)
    (h : ∀ g ∈ c.pointingGoals, τ g.goalAtom = σ g.goalAtom) :
    (unmetPointing c σ).size ≤ (unmetPointing c τ).size := by
  rw [unmetPointing_eq, unmetPointing_eq]
  have heq : c.pointingGoals.toList.filter (livePt σ)
      = c.pointingGoals.toList.filter (livePt τ) :=
    List.filter_congr fun y hy => by simp [livePt, h y (by simpa using hy)]
  rw [heq]

/-- **The turn count, bounded from its three parts.** -/
theorem turns_le_succ_of_parts (c : Cfg) (σ τ : AtomState) {dp dd da : Nat}
    (hp : (unmetPointing c σ).size ≤ (unmetPointing c τ).size + dp)
    (hd : (dirsToTurn c σ).length ≤ (dirsToTurn c τ).length + dd)
    (ha : approach c σ ≤ approach c τ + da)
    (hsum : dp + dd + da ≤ 1) : turns c σ ≤ turns c τ + 1 := by
  rw [turns_eq, turns_eq]
  omega

/-- The calibration detour is one action at most, so naming its drop is enough. -/
theorem approach_le_two (c : Cfg) (σ : AtomState) : approach c σ ≤ 1 := by
  unfold approach; split <;> omega

end Planner.Lifted.Satellite

/- -------------------------------------------------------------------------- -/
/-
Satellite, stated over ground atoms at the schema level.

The value splits into the actions that are not turns — images, calibrations,
power — and the turns.  The shapes below say only what the domain's five schemas
do to the predicates and to the four families the two counts are built from, and
the counts are derived.

Two bounds are named rather than derived, and both are about the heuristic's own
counters:

  * `ReadyStep.instrumentBound` — the two set-cover terms and the free-slot term
    interact, and one instrument action discharges at most one of them;
  * `turnsLe` and `TurnStep.turnBound` — the pointing-goal and direction terms
    interact and are bounded together.

Both used to be split term by term, and both splittings were **false**.  A turn
towards a direction an unmet image needs makes that direction `covered`, so it
leaves the list: `dirsLe` is false of `turn_to`.  And a `switch_off` un-powers an
instrument, so a direction it covered *enters* the list.  The joint bound is
what the informal argument claims, and what `Planner/ShapeSpecs.lean` walks.
-/

namespace Planner.Lifted.Satellite

open Planner Planner.Pddl

/-! ### What each schema does -/

/-- `take_image`: one image goal is met by an instrument already ready for it. -/
structure ImageStep (c : Cfg) (σ τ : AtomState) (q : ImageGoal) : Prop where
  memQ : q ∈ c.images
  unmetQ : σ q.goalAtom = false
  metQ' : τ q.goalAtom = true
  frameImages : ∀ g ∈ c.images, g ≠ q → τ g.goalAtom = σ g.goalAtom
  /--
  The mode was supported by a ready, powered instrument, so it was in neither
  uncovered set, and neither cover count moves.

  The free-slot term *can* move, which is why this is an inequality and not an
  equation.  `slotFree` asks for an instrument that supports a **needed** mode
  and has a spare power slot.  Taking the image can stop a mode being needed,
  and the only instrument with a spare slot may be one that supported just that
  mode — so `slotFree` falls away and `freeSlot` rises from `0` to `1`.  The
  count of images falls by exactly one at the same time, so this direction is
  the one consistency needs.
  -/
  instrumentsLe : instruments c σ ≤ instruments c τ
  /-- The satellite was already pointing at the direction, so no turn is
  discharged. -/
  turnsLe : turns c σ ≤ turns c τ

/-- `switch_on`, `switch_off` and `calibrate`: only the instruments move. -/
structure ReadyStep (c : Cfg) (σ τ : AtomState) : Prop where
  frameImages : ∀ g ∈ c.images, τ g.goalAtom = σ g.goalAtom
  /-- One instrument action discharges at most one of the three instrument bounds. -/
  instrumentBound : instruments c σ ≤ instruments c τ + 1
  /-- Nothing turns, so the two deployed turn terms together do not fall. -/
  turnsLe : turns c σ ≤ turns c τ

/--
`turn_to`: the satellite turns; no instrument and no image moves.

The turn count has to be bounded **jointly**, not term by term.  A turn towards a
direction an unmet image needs makes that direction `covered`, so `dirsToTurn`
really can get shorter.  What stays true is that the two deployed turn terms
together fall by at most one.
-/
structure TurnStep (c : Cfg) (σ τ : AtomState) : Prop where
  frameImages : ∀ g ∈ c.images, τ g.goalAtom = σ g.goalAtom
  instrumentsSame : instruments c τ = instruments c σ
  /-- One turn discharges at most one turn. -/
  turnBound : turns c σ ≤ turns c τ + 1

/-- One action of the domain. -/
inductive SchemaStep (c : Cfg) (σ τ : AtomState) : Prop
  | image (q : ImageGoal) (h : ImageStep c σ τ q)
  | ready (h : ReadyStep c σ τ)
  | turn (h : TurnStep c σ τ)

/-! ### How an action may move the two quantities -/

inductive Effect (c : Cfg) (σ τ : AtomState) : Prop
  | image (hA : Ac c σ ≤ Ac c τ + 1) (hT : Tc c σ ≤ Tc c τ)
  | ready (hA : Ac c σ ≤ Ac c τ + 1) (hT : Tc c σ ≤ Tc c τ)
  | turn (hA : Ac c σ ≤ Ac c τ) (hT : Tc c σ ≤ Tc c τ + 1)

/-! ### The counters, derived from the shapes -/

theorem unmetImages_congr {c : Cfg} {σ τ : AtomState}
    (h : ∀ g ∈ c.images, τ g.goalAtom = σ g.goalAtom) :
    (unmetImages c τ).size = (unmetImages c σ).size := by
  rw [unmetImages_eq, unmetImages_eq]
  exact length_filter_congr _ _ _ fun y hy => by simp [liveImg, h y (by simpa using hy)]

theorem unmetPointing_congr {c : Cfg} {σ τ : AtomState}
    (h : ∀ g ∈ c.pointingGoals, τ g.goalAtom = σ g.goalAtom) :
    (unmetPointing c τ).size = (unmetPointing c σ).size := by
  rw [unmetPointing_eq, unmetPointing_eq]
  exact length_filter_congr _ _ _ fun y hy => by simp [livePt, h y (by simpa using hy)]

theorem ImageStep.images_drop {c : Cfg} {σ τ : AtomState} {q : ImageGoal}
    (h : ImageStep c σ τ q) (hnd : c.images.toList.Nodup) :
    (unmetImages c τ).size + 1 = (unmetImages c σ).size := by
  rw [unmetImages_eq, unmetImages_eq]
  refine length_filter_erase_one _ (liveImg σ) (liveImg τ) q (by simpa using h.memQ) hnd
    (by simp [liveImg, h.unmetQ]) (by simp [liveImg, h.metQ']) ?_
  intro y hy hne
  simp [liveImg, h.frameImages y (by simpa using hy) hne]

/-- The turn count never falls when no turn happens. -/
theorem turns_le_of_parts {c : Cfg} {σ τ : AtomState}
    (hp : ∀ g ∈ c.pointingGoals, τ g.goalAtom = σ g.goalAtom)
    (hd : (dirsToTurn c σ).length ≤ (dirsToTurn c τ).length)
    (ha : approach c σ ≤ approach c τ) : turns c σ ≤ turns c τ := by
  rw [turns_eq, turns_eq, unmetPointing_congr hp]
  omega

theorem effect_of_schema (c : Cfg) (σ τ : AtomState) (hnd : c.images.toList.Nodup)
    (he : SchemaStep c σ τ) : Effect c σ τ := by
  cases he with
  | image q h =>
      refine .image ?_ h.turnsLe
      show actionCount c σ ≤ actionCount c τ + 1
      rw [actionCount_eq, actionCount_eq]
      have := h.images_drop hnd
      have := h.instrumentsLe
      omega
  | ready h =>
      refine .ready ?_ h.turnsLe
      show actionCount c σ ≤ actionCount c τ + 1
      rw [actionCount_eq, actionCount_eq, unmetImages_congr h.frameImages]
      have := h.instrumentBound
      omega
  | turn h =>
      refine .turn ?_ h.turnBound
      show actionCount c σ ≤ actionCount c τ
      rw [actionCount_eq, actionCount_eq, unmetImages_congr h.frameImages,
        h.instrumentsSame]

/-! ### The step -/

private theorem step_arith (A T A' T' cost : Nat) (hcost : 1 ≤ cost)
    (h : (A ≤ A' + 1 ∧ T ≤ T') ∨ (A ≤ A' ∧ T ≤ T' + 1)) :
    A + T ≤ cost + (A' + T') := by
  rcases h with ⟨h1,h2⟩|⟨h1,h2⟩ <;> omega

theorem value_step (c : Cfg) (σ τ : AtomState) (hnd : c.images.toList.Nodup)
    (hshape : SchemaStep c σ τ) (cost : Nat) (hcost : 1 ≤ cost) :
    value c σ ≤ cost + value c τ := by
  show Ac c σ + Tc c σ ≤ cost + (Ac c τ + Tc c τ)
  refine step_arith _ _ _ _ cost hcost ?_
  cases effect_of_schema c σ τ hnd hshape with
  | image hA hT => exact Or.inl ⟨hA, hT⟩
  | ready hA hT => exact Or.inl ⟨hA, hT⟩
  | turn hA hT => exact Or.inr ⟨hA, hT⟩

theorem liftedConsistent {d : Domain} {p : Problem} (rel : Bool) (c : Cfg)
    (Inv : AtomState → Prop) (hnd : c.images.toList.Nodup)
    (hshape : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ → o.applicableA σ →
      SchemaStep c σ (o.applyA σ))
    (hcost : ∀ o ∈ groundedOps d p rel, 0 < o.cost) :
    LiftedConsistentOn d p rel Inv (value c) := by
  intro o ho σ hinv happ
  exact value_step c σ (o.applyA σ) hnd (hshape o ho σ hinv happ) o.cost (hcost o ho)

/-! ### The compiled boundary -/

theorem improved_goalAwareOn (d : Domain) (p : Problem) (rel : Bool) (c : Cfg)
    (Inv : AtomState → Prop)
    (hwf : Task.WF (ground d p rel))
    (hcost : ∀ o ∈ groundedOps d p rel, 0 < o.cost)
    (himg : ∀ g ∈ c.images, g.goalAtom ∈ p.goal)
    (hpt : ∀ g ∈ c.pointingGoals, g.goalAtom ∈ p.goal)
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hpres : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ →
      o.applicableA σ → Inv (o.applyA σ))
    (hv : State → Nat) (hcomp : ComputesOn (ground d p rel) Inv hv (value c)) :
    (ground d p rel).GoalAwareOn (Reachable (ground d p rel)) hv :=
  goalAwareOn_of_lifted d p rel hwf hcost hv (value c) Inv hcomp hinit hpres
    (liftedGoalAware p c himg hpt)

theorem improved_consistentOn (d : Domain) (p : Problem) (rel : Bool) (c : Cfg)
    (Inv : AtomState → Prop)
    (hwf : Task.WF (ground d p rel))
    (hcost : ∀ o ∈ groundedOps d p rel, 0 < o.cost)
    (hnd : c.images.toList.Nodup)
    (hshape : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ → o.applicableA σ →
      SchemaStep c σ (o.applyA σ))
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hpres : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ →
      o.applicableA σ → Inv (o.applyA σ))
    (hv : State → Nat) (hcomp : ComputesOn (ground d p rel) Inv hv (value c)) :
    (ground d p rel).ConsistentOn (Reachable (ground d p rel)) hv :=
  consistentOn_of_lifted d p rel hwf hcost hv (value c) Inv hcomp hinit hpres
    (liftedConsistent rel c Inv hnd hshape hcost)

theorem improved_admissibleOn (d : Domain) (p : Problem) (rel : Bool) (c : Cfg)
    (Inv : AtomState → Prop)
    (hwf : Task.WF (ground d p rel))
    (hcost : ∀ o ∈ groundedOps d p rel, 0 < o.cost)
    (himg : ∀ g ∈ c.images, g.goalAtom ∈ p.goal)
    (hpt : ∀ g ∈ c.pointingGoals, g.goalAtom ∈ p.goal)
    (hnd : c.images.toList.Nodup)
    (hshape : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ → o.applicableA σ →
      SchemaStep c σ (o.applyA σ))
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hpres : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ →
      o.applicableA σ → Inv (o.applyA σ))
    (hv : State → Nat) (hcomp : ComputesOn (ground d p rel) Inv hv (value c)) :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel)) hv :=
  admissibleOn_of_lifted d p rel hwf hcost hv (value c) Inv hcomp hinit hpres
    (liftedGoalAware p c himg hpt) (liftedConsistent rel c Inv hnd hshape hcost)

end Planner.Lifted.Satellite

/- -------------------------------------------------------------------------- -/
/-
The compiled Satellite tables and their atom-level meaning.

Each relation below says that a fact number names the atom in the corresponding
lifted entry.  The static tables — which modes an instrument supports, which
satellite carries it, what it calibrates against — hold no facts, so they are
asked to be equal.  The value theorem then follows structurally: paired filters
retain the same entries, and both sides read the same indices.
-/

namespace Planner.Lifted.Satellite

open Planner Planner.Pddl

abbrev CData := ExampleHeuristics.Satellite.Data
abbrev CImage := ExampleHeuristics.Satellite.ImageGoal
abbrev CPointing := ExampleHeuristics.Satellite.PointingGoal

structure FactMatch (t : Task) (f : Fact) (a : GroundAtom) : Prop where
  name : t.factNames.getD f default = a
  range : f < t.factNames.size

structure PairMatch (t : Task) (x : Fact × Nat) (y : GroundAtom × Nat) : Prop where
  fact : FactMatch t x.1 y.1
  index : x.2 = y.2

structure ImageMatch (t : Task) (x : CImage) (y : ImageGoal) : Prop where
  goal : FactMatch t x.goalFact y.goalAtom
  dir : x.dir = y.dir
  mode : x.mode = y.mode

structure PointingMatch (t : Task) (x : CPointing) (y : PointingGoal) : Prop where
  goal : FactMatch t x.goalFact y.goalAtom
  sat : x.sat = y.sat
  dir : x.dir = y.dir

/-- A table slot either holds a numbered fact and its atom, or is empty on both sides. -/
def OptMatch (t : Task) (x : Option Fact) (y : Option GroundAtom) : Prop :=
  match x, y with
  | some f, some a => FactMatch t f a
  | none, none => True
  | _, _ => False

structure DataMatches (t : Task) (c : Cfg) (dd : CData) : Prop where
  images : List.Forall₂ (ImageMatch t) dd.images.toList c.images.toList
  pointingGoals : List.Forall₂ (PointingMatch t) dd.pointingGoals.toList
    c.pointingGoals.toList
  calibrated : List.Forall₂ (OptMatch t) dd.calibratedFacts.toList c.calibratedAtoms.toList
  powerOn : List.Forall₂ (OptMatch t) dd.powerOnFacts.toList c.powerOnAtoms.toList
  powerAvail : List.Forall₂ (OptMatch t) dd.powerAvailFacts.toList c.powerAvailAtoms.toList
  supports : dd.supports = c.supports
  onBoard : dd.onBoard = c.onBoard
  calibTarget : dd.calibTarget = c.calibTarget
  satelliteOf : dd.satelliteOf = c.satelliteOf
  pointingByDir : List.Forall₂ (fun xs ys =>
    List.Forall₂ (PairMatch t) xs.toList ys.toList) dd.pointingByDir.toList
    c.pointingByDir.toList

theorem test_eq {t : Task} {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) {f : Fact} {a : GroundAtom}
    (h : FactMatch t f a) : s.test f = σ a := by
  rw [← h.name]
  exact (habs.numbered f (by rw [hn]; exact h.range)).symm

/-! ### Reading one slot of a paired table -/

private theorem array_getD_toList {α : Type} (xs : Array α) (i : Nat) (d : α) :
    xs.getD i d = xs.toList.getD i d := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

private theorem forall₂_getD {α β : Type} {R : α → β → Prop} {da : α} {db : β}
    (hd : R da db) : ∀ {l : List α} {m : List β}, List.Forall₂ R l m →
      ∀ i, R (l.getD i da) (m.getD i db) := by
  intro l m h
  induction h with
  | nil => intro i; simpa using hd
  | @cons x y rest1 rest2 hxy _ ih =>
      intro i
      cases i with
      | zero => simpa using hxy
      | succ k => simpa using ih k

private theorem nested_getD {t : Task} {xs : Array (Array (Fact × Nat))}
    {ys : Array (Array (GroundAtom × Nat))}
    (h : List.Forall₂ (fun a b => List.Forall₂ (PairMatch t) a.toList b.toList)
      xs.toList ys.toList) (i : Nat) :
    List.Forall₂ (PairMatch t) (xs.getD i #[]).toList (ys.getD i #[]).toList := by
  rw [array_getD_toList, array_getD_toList]
  exact forall₂_getD (da := (#[] : Array (Fact × Nat))) (db := (#[] : Array (GroundAtom × Nat)))
    (by simpa using List.Forall₂.nil) h i

private theorem opt_getD {t : Task} {xs : Array (Option Fact)}
    {ys : Array (Option GroundAtom)}
    (h : List.Forall₂ (OptMatch t) xs.toList ys.toList) (i : Nat) :
    OptMatch t (xs.getD i none) (ys.getD i none) := by
  rw [array_getD_toList, array_getD_toList]
  exact forall₂_getD (da := (none : Option Fact)) (db := (none : Option GroundAtom))
    trivial h i

/-! ### The instruments that are on, calibrated and ready -/

private theorem active_eq {t : Task} {xs : List (Option Fact)} {ys : List (Option GroundAtom)}
    (hm : List.Forall₂ (OptMatch t) xs ys) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) (n : Nat) :
    (xs.zipIdx n).filterMap (fun x =>
        match x.1 with | some f => if s.test f then some x.2 else none | none => none) =
      (ys.zipIdx n).filterMap (fun y =>
        match y.1 with | some a => if σ a then some y.2 else none | none => none) := by
  refine forall₂_filterMap_eq (forall₂_zipIdx hm n) ?_
  rintro ⟨x, i⟩ ⟨y, j⟩ ⟨hxy, hij⟩
  simp only at hxy hij ⊢
  subst hij
  rcases x with _ | f <;> rcases y with _ | a
  · rfl
  · exact absurd hxy (by simp [OptMatch])
  · exact absurd hxy (by simp [OptMatch])
  · show (if s.test f then some i else none) = (if σ a then some i else none)
    rw [test_eq habs hn hxy]

theorem calibratedNow_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Satellite.calibratedNow dd s = calibratedNow c σ := by
  apply Array.toList_inj.mp
  simpa [ExampleHeuristics.Satellite.calibratedNow, calibratedNow,
    ExampleHeuristics.Satellite.activeInstruments, activeInstruments,
    Array.toList_filterMap] using active_eq hm.calibrated habs hn 0

theorem poweredNow_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Satellite.poweredNow dd s = poweredNow c σ := by
  apply Array.toList_inj.mp
  simpa [ExampleHeuristics.Satellite.poweredNow, poweredNow,
    ExampleHeuristics.Satellite.activeInstruments, activeInstruments,
    Array.toList_filterMap] using active_eq hm.powerOn habs hn 0

theorem readyNow_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Satellite.readyNow dd s = readyNow c σ := by
  unfold ExampleHeuristics.Satellite.readyNow readyNow
  rw [calibratedNow_matches hm habs hn, poweredNow_matches hm habs hn]

/-! ### The goals still unmet -/

theorem unmetImages_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    List.Forall₂ (ImageMatch t) (ExampleHeuristics.Satellite.unmetImages dd s).toList
      (unmetImages c σ).toList := by
  have := forall₂_filter (P := fun g : CImage => !s.test g.goalFact)
    (Q := fun g : ImageGoal => !σ g.goalAtom) hm.images
    (fun a b hab => by dsimp only; rw [test_eq habs hn hab.goal])
  simpa [ExampleHeuristics.Satellite.unmetImages, unmetImages, Array.toList_filter]
    using this

theorem unmetPointing_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    List.Forall₂ (PointingMatch t) (ExampleHeuristics.Satellite.unmetPointing dd s).toList
      (unmetPointing c σ).toList := by
  have := forall₂_filter (P := fun g : CPointing => !s.test g.goalFact)
    (Q := fun g : PointingGoal => !σ g.goalAtom) hm.pointingGoals
    (fun a b hab => by dsimp only; rw [test_eq habs hn hab.goal])
  simpa [ExampleHeuristics.Satellite.unmetPointing, unmetPointing, Array.toList_filter]
    using this

theorem paidByGoal_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) (dir : Nat) :
    ExampleHeuristics.Satellite.paidByGoal dd s dir = paidByGoal c σ dir := by
  unfold ExampleHeuristics.Satellite.paidByGoal paidByGoal
  rw [← Array.any_toList, ← Array.any_toList]
  exact forall₂_any (unmetPointing_matches hm habs hn) fun a b hab => by rw [hab.dir]

theorem neededModes_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Satellite.neededModes dd s = neededModes c σ := by
  unfold ExampleHeuristics.Satellite.neededModes neededModes
  congr 1
  exact forall₂_map_eq (unmetImages_matches hm habs hn) fun a b hab => hab.mode

/-! ### The turn terms -/

theorem pointsAt_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) (sat dir : Nat) :
    ExampleHeuristics.Satellite.pointsAt dd s sat dir = pointsAt c σ sat dir := by
  unfold ExampleHeuristics.Satellite.pointsAt pointsAt
  rw [← Array.any_toList, ← Array.any_toList]
  refine forall₂_any (nested_getD hm.pointingByDir dir) (fun a b hab => ?_)
  dsimp only
  rw [test_eq habs hn hab.fact, hab.index]

theorem covered_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) (dir mode : Nat) :
    ExampleHeuristics.Satellite.covered dd s dir mode = covered c σ dir mode := by
  unfold ExampleHeuristics.Satellite.covered covered
  rw [← Array.any_toList, ← Array.any_toList]
  refine forall₂_any (nested_getD hm.pointingByDir dir) (fun a b hab => ?_)
  dsimp only
  rw [test_eq habs hn hab.fact, hab.index, hm.onBoard, hm.supports, hm.calibTarget,
    readyNow_matches hm habs hn]

theorem dirsToTurn_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Satellite.dirsToTurn dd s = dirsToTurn c σ := by
  unfold ExampleHeuristics.Satellite.dirsToTurn dirsToTurn
  congr 1
  refine forall₂_filterMap_eq (unmetImages_matches hm habs hn) (fun a b hab => ?_)
  rw [hab.dir, hab.mode, paidByGoal_matches hm habs hn, covered_matches hm habs hn]

/-! ### The instrument terms -/

theorem coverCount_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) (l : List Nat) :
    ExampleHeuristics.Satellite.coverCount dd l = coverCount c l := by
  unfold ExampleHeuristics.Satellite.coverCount coverCount
  rw [hm.supports]

theorem uncalibratedModes_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Satellite.uncalibratedModes dd s = uncalibratedModes c σ := by
  unfold ExampleHeuristics.Satellite.uncalibratedModes uncalibratedModes
  rw [neededModes_matches hm habs hn]
  refine List.filter_congr (fun m _ => ?_)
  show (!ExampleHeuristics.Satellite.supportsMode dd _ m) = (!supportsMode c _ m)
  unfold ExampleHeuristics.Satellite.supportsMode supportsMode
  rw [hm.supports, readyNow_matches hm habs hn]

theorem unpoweredModes_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Satellite.unpoweredModes dd s = unpoweredModes c σ := by
  unfold ExampleHeuristics.Satellite.unpoweredModes unpoweredModes
  rw [neededModes_matches hm habs hn]
  refine List.filter_congr (fun m _ => ?_)
  show (!ExampleHeuristics.Satellite.supportsMode dd _ m) = (!supportsMode c _ m)
  unfold ExampleHeuristics.Satellite.supportsMode supportsMode
  rw [hm.supports, poweredNow_matches hm habs hn]

theorem calibrationInReach_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Satellite.calibrationInReach dd s = calibrationInReach c σ := by
  unfold ExampleHeuristics.Satellite.calibrationInReach calibrationInReach
  rw [hm.supports, neededModes_matches hm habs hn, hm.calibTarget, hm.satelliteOf]
  refine array_any_congr _ _ _ (fun x _ => ?_)
  congr 1
  rcases ht : c.calibTarget.getD x.2 none with _ | target
  · rfl
  · rcases hs2 : c.satelliteOf.getD x.2 none with _ | sat
    · rfl
    · show (ExampleHeuristics.Satellite.pointsAt dd s sat target ||
          (ExampleHeuristics.Satellite.dirsToTurn dd s).contains target ||
          (ExampleHeuristics.Satellite.unmetPointing dd s).any fun g => g.dir == target)
        = (pointsAt c σ sat target || (dirsToTurn c σ).contains target ||
          (unmetPointing c σ).any fun g => g.dir == target)
      rw [pointsAt_matches hm habs hn, dirsToTurn_matches hm habs hn]
      congr 1
      rw [← Array.any_toList, ← Array.any_toList]
      exact forall₂_any (unmetPointing_matches hm habs hn)
        fun a b hab => by rw [hab.dir]

theorem approach_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Satellite.approach dd s = approach c σ := by
  unfold ExampleHeuristics.Satellite.approach approach
  rw [uncalibratedModes_matches hm habs hn, calibrationInReach_matches hm habs hn]

theorem slotFree_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Satellite.slotFree dd s = slotFree c σ := by
  unfold ExampleHeuristics.Satellite.slotFree slotFree
  rw [hm.supports, neededModes_matches hm habs hn, hm.satelliteOf]
  refine array_any_congr _ _ _ (fun x _ => ?_)
  congr 1
  rcases hsat : c.satelliteOf.getD x.2 none with _ | sat
  · rfl
  · show (match dd.powerAvailFacts.getD sat none with | some f => s.test f | none => true)
        = (match c.powerAvailAtoms.getD sat none with | some a => σ a | none => true)
    have hopt := opt_getD hm.powerAvail sat
    rcases hf : dd.powerAvailFacts.getD sat none with _ | f <;>
      rcases ha : c.powerAvailAtoms.getD sat none with _ | a <;>
      rw [hf, ha] at hopt <;>
      first
        | rfl
        | exact test_eq habs hn hopt
        | exact absurd hopt (by simp [OptMatch])

theorem freeSlot_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Satellite.freeSlot dd s = freeSlot c σ := by
  unfold ExampleHeuristics.Satellite.freeSlot freeSlot
  rw [unpoweredModes_matches hm habs hn, slotFree_matches hm habs hn]

/-- The executable Satellite value computes the atom-level value. -/
theorem computes {t : Task} {c : Cfg} {dd : CData} (hm : DataMatches t c dd)
    (hn : t.numFacts = t.factNames.size) :
    Computes t (ExampleHeuristics.Satellite.value dd) (value c) := by
  intro s σ habs _
  have himg : (ExampleHeuristics.Satellite.unmetImages dd s).size
      = (unmetImages c σ).size := by
    simpa using (unmetImages_matches hm habs hn).length_eq
  have hpt : (ExampleHeuristics.Satellite.unmetPointing dd s).size
      = (unmetPointing c σ).size := by
    simpa using (unmetPointing_matches hm habs hn).length_eq
  show ExampleHeuristics.Satellite.actionCount dd s
      + ExampleHeuristics.Satellite.turns dd s = actionCount c σ + turns c σ
  unfold ExampleHeuristics.Satellite.actionCount ExampleHeuristics.Satellite.turns
    actionCount turns
  rw [himg, hpt, uncalibratedModes_matches hm habs hn, unpoweredModes_matches hm habs hn,
    coverCount_matches hm, coverCount_matches hm, freeSlot_matches hm habs hn,
    dirsToTurn_matches hm habs hn, approach_matches hm habs hn]

theorem computesOn_of_matches {t : Task} {c : Cfg} {dd : CData}
    (Inv : AtomState → Prop) (hm : DataMatches t c dd)
    (hn : t.numFacts = t.factNames.size) :
    ComputesOn t Inv (ExampleHeuristics.Satellite.value dd) (value c) := by
  intro s σ habs _
  exact computes hm hn s σ habs trivial

/-! ### The executable boundary -/

set_option maxHeartbeats 1000000 in
/-- Goal awareness for the compiled value, after its tables have been matched. -/
theorem compiled_goalAwareOn (d : Domain) (p : Problem) (rel : Bool) (c : Cfg)
    (Inv : AtomState → Prop)
    (hm : DataMatches (ground d p rel) c
      (ExampleHeuristics.Satellite.compile (ground d p rel)))
    (hwf : Task.WF (ground d p rel))
    (hcost : ∀ o ∈ groundedOps d p rel, 0 < o.cost)
    (himg : ∀ g ∈ c.images, g.goalAtom ∈ p.goal)
    (hpt : ∀ g ∈ c.pointingGoals, g.goalAtom ∈ p.goal)
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hpres : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ →
      o.applicableA σ → Inv (o.applyA σ)) :
    (ground d p rel).GoalAwareOn (Reachable (ground d p rel))
      (ExampleHeuristics.Satellite.improved (ground d p rel)).eval :=
  improved_goalAwareOn d p rel c (Inv := Inv) hwf hcost himg hpt hinit hpres _
    (computesOn_of_matches Inv hm rfl)

set_option maxHeartbeats 1000000 in
/-- Consistency for the compiled value, after its tables have been matched. -/
theorem compiled_consistentOn (d : Domain) (p : Problem) (rel : Bool) (c : Cfg)
    (Inv : AtomState → Prop)
    (hm : DataMatches (ground d p rel) c
      (ExampleHeuristics.Satellite.compile (ground d p rel)))
    (hwf : Task.WF (ground d p rel))
    (hcost : ∀ o ∈ groundedOps d p rel, 0 < o.cost)
    (hnd : c.images.toList.Nodup)
    (hshape : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ → o.applicableA σ →
      SchemaStep c σ (o.applyA σ))
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hpres : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ →
      o.applicableA σ → Inv (o.applyA σ)) :
    (ground d p rel).ConsistentOn (Reachable (ground d p rel))
      (ExampleHeuristics.Satellite.improved (ground d p rel)).eval :=
  improved_consistentOn d p rel c (Inv := Inv) hwf hcost hnd hshape hinit hpres _
    (computesOn_of_matches Inv hm rfl)

set_option maxHeartbeats 1000000 in
/-- Admissibility follows from the two executable properties. -/
theorem compiled_admissibleOn (d : Domain) (p : Problem) (rel : Bool) (c : Cfg)
    (Inv : AtomState → Prop)
    (hm : DataMatches (ground d p rel) c
      (ExampleHeuristics.Satellite.compile (ground d p rel)))
    (hwf : Task.WF (ground d p rel))
    (hcost : ∀ o ∈ groundedOps d p rel, 0 < o.cost)
    (himg : ∀ g ∈ c.images, g.goalAtom ∈ p.goal)
    (hpt : ∀ g ∈ c.pointingGoals, g.goalAtom ∈ p.goal)
    (hnd : c.images.toList.Nodup)
    (hshape : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ → o.applicableA σ →
      SchemaStep c σ (o.applyA σ))
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hpres : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ →
      o.applicableA σ → Inv (o.applyA σ)) :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel))
      (ExampleHeuristics.Satellite.improved (ground d p rel)).eval :=
  improved_admissibleOn d p rel c (Inv := Inv) hwf hcost himg hpt hnd hshape hinit hpres _
    (computesOn_of_matches Inv hm rfl)

end Planner.Lifted.Satellite

/- -------------------------------------------------------------------------- -/
/-
The bridge from `compile` to the lifted `Cfg`.

`Proofs/Lifted/SatelliteComputes.lean` says what it takes for the compiled tables
and a lifted `Cfg` to agree: each fact number names the atom in the corresponding
lifted entry, and the static tables are the same.  This file supplies such a
`Cfg` — the one that reads every fact of `compile` through the task's own names —
and discharges the agreement outright.

What is left after this file is the shape of one transition, `SchemaStep`, which
is about the domain's schemas rather than about the tables.
-/

namespace Planner.Lifted.Satellite

open Planner Planner.Pddl

/-! ### The `Cfg` a task describes -/

/-- The atom a fact number names. -/
abbrev atomOf (t : Task) (f : Fact) : GroundAtom := t.factNames.getD f default

def imageOf (t : Task) (x : CImage) : ImageGoal where
  goalAtom := atomOf t x.goalFact
  dir := x.dir
  mode := x.mode

def pointingOf (t : Task) (x : CPointing) : PointingGoal where
  goalAtom := atomOf t x.goalFact
  sat := x.sat
  dir := x.dir

/-- The configuration a satellite task describes. -/
def cfgOf (t : Task) : Cfg where
  images := (ExampleHeuristics.Satellite.compile t).images.map (imageOf t)
  pointingGoals := (ExampleHeuristics.Satellite.compile t).pointingGoals.map (pointingOf t)
  calibratedAtoms :=
    (ExampleHeuristics.Satellite.compile t).calibratedFacts.map (Option.map (atomOf t))
  powerOnAtoms :=
    (ExampleHeuristics.Satellite.compile t).powerOnFacts.map (Option.map (atomOf t))
  powerAvailAtoms :=
    (ExampleHeuristics.Satellite.compile t).powerAvailFacts.map (Option.map (atomOf t))
  supports := (ExampleHeuristics.Satellite.compile t).supports
  onBoard := (ExampleHeuristics.Satellite.compile t).onBoard
  calibTarget := (ExampleHeuristics.Satellite.compile t).calibTarget
  satelliteOf := (ExampleHeuristics.Satellite.compile t).satelliteOf
  pointingByDir := (ExampleHeuristics.Satellite.compile t).pointingByDir.map fun xs =>
    xs.map fun y => (atomOf t y.1, y.2)

/-! ### Every fact the tables hold is numbered -/

/-- A slot read by searching one predicate's facts holds a numbered fact. -/
theorem findMap_range {t : Task} {pred : Name} {P : Fact × GroundAtom → Bool} {f : Fact}
    (h : (((t.factsWith pred).find? P).map (·.1)) = some f) : f < t.factNames.size := by
  rcases hf : (t.factsWith pred).find? P with _ | y
  · rw [hf] at h; simp at h
  · rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    rw [← h]
    exact factsWith_ok y (Array.mem_of_find?_eq_some hf)

/-- And so does an entry of the `pointing` table. -/
theorem pointingByDir_range (t : Task) (satIndex : Name → Option Nat) (dir : Name) :
    ∀ y ∈ (t.factsWith "pointing").filterMap (fun z =>
      match z.2.args with
      | [sat, x] => if x == dir then (satIndex sat).map ((z.1, ·)) else none
      | _ => none), y.1 < t.factNames.size := by
  intro y hy
  obtain ⟨z, hz, hval⟩ := Array.mem_filterMap.mp hy
  have hzr : z.1 < t.factNames.size := factsWith_ok z hz
  revert hval
  rcases hargs : z.2.args with _ | ⟨sat, rest⟩
  · simp
  · cases rest with
    | nil => simp
    | cons x rest' =>
        cases rest' with
        | cons _ _ => simp
        | nil =>
            simp only []
            by_cases hx : (x == dir) = true
            · simp only [hx, if_true]
              rcases hs : satIndex sat with _ | i
              · simp
              · simp only [Option.map_some, Option.some.injEq]
                intro h; rw [← h]; exact hzr
            · simp only [Bool.not_eq_true] at hx
              simp [hx]

/-- The goal facts the two goal tables hold are numbered. -/
theorem goalFact_range {t : Task} (hwf : Task.WF t) (hn : t.numFacts = t.factNames.size)
    (hsize : t.goalAtoms.size ≤ t.goal.size) {x : GroundAtom × Nat}
    (hx : x ∈ t.goalAtoms.zipIdx) : t.goal.getD x.2 0 < t.factNames.size := by
  have hlt : x.2 < t.goal.size := by
    obtain ⟨-, h2, -⟩ := Array.mem_zipIdx hx
    omega
  have hmem : t.goal.getD x.2 0 ∈ t.goal := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]
    simpa using Array.getElem_mem hlt
  rw [← hn]; exact hwf.goal _ hmem

theorem imageEntry_range {t : Task} (hwf : Task.WF t) (hn : t.numFacts = t.factNames.size)
    (hsize : t.goalAtoms.size ≤ t.goal.size) {dirIndex modeIndex : Name → Option Nat}
    {x : GroundAtom × Nat} (hx : x ∈ t.goalAtoms.zipIdx) {y : CImage}
    (h : ExampleHeuristics.Satellite.imageEntry t dirIndex modeIndex x = some y) :
    y.goalFact < t.factNames.size := by
  have hgoal := goalFact_range hwf hn hsize hx
  unfold ExampleHeuristics.Satellite.imageEntry at h
  by_cases hpred : (x.1.pred == "have_image") = true
  · rcases hargs : x.1.args with _ | ⟨dn, rest⟩
    · simp only [hpred, hargs] at h; simp at h
    · cases rest with
      | nil => simp only [hpred, hargs] at h; simp at h
      | cons mn rest' =>
          cases rest' with
          | cons _ _ => simp only [hpred, hargs] at h; simp at h
          | nil =>
              simp only [hpred, hargs] at h
              rcases hd : dirIndex dn with _ | di
              · rw [hd] at h; simp at h
              · rcases hmm : modeIndex mn with _ | mi
                · rw [hd, hmm] at h; simp at h
                · rw [hd, hmm] at h
                  simp only [Option.some.injEq] at h
                  rw [← h]; exact hgoal
  · simp only [Bool.not_eq_true] at hpred
    simp only [hpred] at h
    simp at h

theorem pointingEntry_range {t : Task} (hwf : Task.WF t)
    (hn : t.numFacts = t.factNames.size) (hsize : t.goalAtoms.size ≤ t.goal.size)
    {satIndex dirIndex : Name → Option Nat} {x : GroundAtom × Nat}
    (hx : x ∈ t.goalAtoms.zipIdx) {y : CPointing}
    (h : ExampleHeuristics.Satellite.pointingEntry t satIndex dirIndex x = some y) :
    y.goalFact < t.factNames.size := by
  have hgoal := goalFact_range hwf hn hsize hx
  unfold ExampleHeuristics.Satellite.pointingEntry at h
  by_cases hpred : (x.1.pred == "pointing") = true
  · rcases hargs : x.1.args with _ | ⟨sn, rest⟩
    · simp only [hpred, hargs] at h; simp at h
    · cases rest with
      | nil => simp only [hpred, hargs] at h; simp at h
      | cons dn rest' =>
          cases rest' with
          | cons _ _ => simp only [hpred, hargs] at h; simp at h
          | nil =>
              simp only [hpred, hargs] at h
              rcases hs : satIndex sn with _ | si
              · rw [hs] at h; simp at h
              · rcases hd : dirIndex dn with _ | di
                · rw [hs, hd] at h; simp at h
                · rw [hs, hd] at h
                  simp only [Option.some.injEq] at h
                  rw [← h]; exact hgoal
  · simp only [Bool.not_eq_true] at hpred
    simp only [hpred] at h
    simp at h

/-! ### The tables and the `Cfg` agree -/

private theorem optMatch_map {t : Task} {x : Option Fact}
    (h : ∀ f, x = some f → f < t.factNames.size) :
    OptMatch t x (x.map (atomOf t)) := by
  rcases hx : x with _ | f
  · trivial
  · exact ⟨rfl, h f hx⟩

/-- **The compiled tables say of the task exactly what the lifted `Cfg` says.** -/
theorem dataMatches (t : Task) (hwf : Task.WF t) (hn : t.numFacts = t.factNames.size)
    (hsize : t.goalAtoms.size ≤ t.goal.size) :
    DataMatches t (cfgOf t) (ExampleHeuristics.Satellite.compile t) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · show List.Forall₂ _ _ (((ExampleHeuristics.Satellite.compile t).images.map _).toList)
    rw [Array.toList_map]
    refine forall₂_map_right _ ?_
    intro x hx
    refine ⟨⟨rfl, ?_⟩, rfl, rfl⟩
    have hx' : x ∈ (ExampleHeuristics.Satellite.compile t).images := by simpa using hx
    obtain ⟨z, hz, hval⟩ := Array.mem_filterMap.mp hx'
    exact imageEntry_range hwf hn hsize hz hval
  · show List.Forall₂ _ _
      (((ExampleHeuristics.Satellite.compile t).pointingGoals.map _).toList)
    rw [Array.toList_map]
    refine forall₂_map_right _ ?_
    intro x hx
    refine ⟨⟨rfl, ?_⟩, rfl, rfl⟩
    have hx' : x ∈ (ExampleHeuristics.Satellite.compile t).pointingGoals := by simpa using hx
    obtain ⟨z, hz, hval⟩ := Array.mem_filterMap.mp hx'
    exact pointingEntry_range hwf hn hsize hz hval
  · show List.Forall₂ _ _
      (((ExampleHeuristics.Satellite.compile t).calibratedFacts.map _).toList)
    rw [Array.toList_map]
    refine forall₂_map_right _ ?_
    intro x hx
    refine optMatch_map ?_
    intro f hf
    have hx' : x ∈ (ExampleHeuristics.Satellite.compile t).calibratedFacts := by simpa using hx
    obtain ⟨ins, -, hval⟩ := Array.mem_map.mp hx'
    exact findMap_range (by rw [hval, hf])
  · show List.Forall₂ _ _
      (((ExampleHeuristics.Satellite.compile t).powerOnFacts.map _).toList)
    rw [Array.toList_map]
    refine forall₂_map_right _ ?_
    intro x hx
    refine optMatch_map ?_
    intro f hf
    have hx' : x ∈ (ExampleHeuristics.Satellite.compile t).powerOnFacts := by simpa using hx
    obtain ⟨ins, -, hval⟩ := Array.mem_map.mp hx'
    exact findMap_range (by rw [hval, hf])
  · show List.Forall₂ _ _
      (((ExampleHeuristics.Satellite.compile t).powerAvailFacts.map _).toList)
    rw [Array.toList_map]
    refine forall₂_map_right _ ?_
    intro x hx
    refine optMatch_map ?_
    intro f hf
    have hx' : x ∈ (ExampleHeuristics.Satellite.compile t).powerAvailFacts := by
      simpa using hx
    obtain ⟨sat, -, hval⟩ := Array.mem_map.mp hx'
    exact findMap_range (by rw [hval, hf])
  · show List.Forall₂ _ _
      (((ExampleHeuristics.Satellite.compile t).pointingByDir.map _).toList)
    rw [Array.toList_map]
    refine forall₂_map_right _ ?_
    intro xs hxs
    show List.Forall₂ (PairMatch t) xs.toList ((xs.map _).toList)
    rw [Array.toList_map]
    refine forall₂_map_right _ ?_
    intro y hy
    refine ⟨⟨rfl, ?_⟩, rfl⟩
    have hxs' : xs ∈ (ExampleHeuristics.Satellite.compile t).pointingByDir := by
      simpa using hxs
    obtain ⟨dir, -, hval⟩ := Array.mem_map.mp hxs'
    rw [← hval] at hy
    exact pointingByDir_range t _ dir y (by simpa using hy)

/-! ### On the task the planner grounds -/

theorem goal_size (d : Domain) (p : Problem) (rel : Bool) :
    (ground d p rel).goalAtoms.size ≤ (ground d p rel).goal.size := by
  show p.goal.toArray.size ≤ (p.goal.toArray.map _).size
  rw [Array.size_map]

/-- **The tables agree on the task the planner searches.** -/
theorem dataMatches_ground (d : Domain) (p : Problem) (rel : Bool)
    (hwf : Task.WF (ground d p rel)) :
    DataMatches (ground d p rel) (cfgOf (ground d p rel))
      (ExampleHeuristics.Satellite.compile (ground d p rel)) :=
  dataMatches _ hwf rfl (goal_size d p rel)


/-! ### The goal atoms the two goal tables name -/

/-- **Every image entry names a goal atom of the problem.** -/
theorem image_goalAtom_mem (d : Domain) (p : Problem) (rel : Bool) :
    ∀ g ∈ (cfgOf (ground d p rel)).images, g.goalAtom ∈ p.goal := by
  intro g hg
  have hg' : g ∈ (ExampleHeuristics.Satellite.compile (ground d p rel)).images.map
      (imageOf (ground d p rel)) := hg
  obtain ⟨x, hx, hval⟩ := Array.mem_map.mp hg'
  obtain ⟨z, hz, hzval⟩ := Array.mem_filterMap.mp
    (hx : x ∈ (ExampleHeuristics.Satellite.compile (ground d p rel)).images)
  obtain ⟨-, hlt, -⟩ := Array.mem_zipIdx hz
  have hi : z.2 < (ground d p rel).goalAtoms.size := by simpa using hlt
  have hgoal : x.goalFact = (ground d p rel).goal.getD z.2 0 := by
    unfold ExampleHeuristics.Satellite.imageEntry at hzval
    by_cases hpred : (z.1.pred == "have_image") = true
    · rcases hargs : z.1.args with _ | ⟨dn, rest⟩
      · simp only [hpred, hargs] at hzval; simp at hzval
      · cases rest with
        | nil => simp only [hpred, hargs] at hzval; simp at hzval
        | cons mn rest' =>
            cases rest' with
            | cons _ _ => simp only [hpred, hargs] at hzval; simp at hzval
            | nil =>
                simp only [hpred, hargs] at hzval
                rcases hd : (ground d p rel).objectsOfTypes ["direction"] |>.findIdx?
                    (· == dn) with _ | di
                · rw [hd] at hzval; simp at hzval
                · rcases hmm : (ground d p rel).objectsOfTypes ["mode"] |>.findIdx?
                      (· == mn) with _ | mi
                  · rw [hd, hmm] at hzval; simp at hzval
                  · rw [hd, hmm] at hzval
                    simp only [Option.some.injEq] at hzval
                    rw [← hzval]
    · simp only [Bool.not_eq_true] at hpred
      simp only [hpred] at hzval
      simp at hzval
  subst hval
  show atomOf (ground d p rel) x.goalFact ∈ p.goal
  rw [hgoal]
  exact goalAtom_of_index d p rel hi

/-- **And every pointing entry does.** -/
theorem pointing_goalAtom_mem (d : Domain) (p : Problem) (rel : Bool) :
    ∀ g ∈ (cfgOf (ground d p rel)).pointingGoals, g.goalAtom ∈ p.goal := by
  intro g hg
  have hg' : g ∈ (ExampleHeuristics.Satellite.compile (ground d p rel)).pointingGoals.map
      (pointingOf (ground d p rel)) := hg
  obtain ⟨x, hx, hval⟩ := Array.mem_map.mp hg'
  obtain ⟨z, hz, hzval⟩ := Array.mem_filterMap.mp
    (hx : x ∈ (ExampleHeuristics.Satellite.compile (ground d p rel)).pointingGoals)
  obtain ⟨-, hlt, -⟩ := Array.mem_zipIdx hz
  have hi : z.2 < (ground d p rel).goalAtoms.size := by simpa using hlt
  have hgoal : x.goalFact = (ground d p rel).goal.getD z.2 0 := by
    unfold ExampleHeuristics.Satellite.pointingEntry at hzval
    by_cases hpred : (z.1.pred == "pointing") = true
    · rcases hargs : z.1.args with _ | ⟨sn, rest⟩
      · simp only [hpred, hargs] at hzval; simp at hzval
      · cases rest with
        | nil => simp only [hpred, hargs] at hzval; simp at hzval
        | cons dn rest' =>
            cases rest' with
            | cons _ _ => simp only [hpred, hargs] at hzval; simp at hzval
            | nil =>
                simp only [hpred, hargs] at hzval
                rcases hs2 : (ground d p rel).objectsOfTypes ["satellite"] |>.findIdx?
                    (· == sn) with _ | si
                · rw [hs2] at hzval; simp at hzval
                · rcases hd : (ground d p rel).objectsOfTypes ["direction"] |>.findIdx?
                      (· == dn) with _ | di
                  · rw [hs2, hd] at hzval; simp at hzval
                  · rw [hs2, hd] at hzval
                    simp only [Option.some.injEq] at hzval
                    rw [← hzval]
    · simp only [Bool.not_eq_true] at hpred
      simp only [hpred] at hzval
      simp at hzval
  subst hval
  show atomOf (ground d p rel) x.goalFact ∈ p.goal
  rw [hgoal]
  exact goalAtom_of_index d p rel hi

/-- **Satellite's improved heuristic is zero at every reachable goal** once the
schema invariant has been connected to the executable tables. -/
theorem improved_goalAware_of_shape (d : Domain) (p : Problem) (rel : Bool)
    (Inv : AtomState → Prop)
    (hwf : Task.WF (ground d p rel))
    (hcost : ∀ o ∈ groundedOps d p rel, 0 < o.cost)
    (hshape : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ → o.applicableA σ →
      SchemaStep (cfgOf (ground d p rel)) σ (o.applyA σ))
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hpres : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ →
      o.applicableA σ → Inv (o.applyA σ)) :
    (ground d p rel).GoalAwareOn (Reachable (ground d p rel))
      (ExampleHeuristics.Satellite.improved (ground d p rel)).eval :=
  compiled_goalAwareOn d p rel _ Inv (dataMatches_ground d p rel hwf) hwf hcost
    (image_goalAtom_mem d p rel) (pointing_goalAtom_mem d p rel) hinit hpres

/-- **Satellite's improved heuristic is consistent on reachable states** once
the schema invariant has been connected to the executable tables. -/
theorem improved_consistent_of_shape (d : Domain) (p : Problem) (rel : Bool)
    (Inv : AtomState → Prop)
    (hwf : Task.WF (ground d p rel))
    (hcost : ∀ o ∈ groundedOps d p rel, 0 < o.cost)
    (hnd : (cfgOf (ground d p rel)).images.toList.Nodup)
    (hshape : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ → o.applicableA σ →
      SchemaStep (cfgOf (ground d p rel)) σ (o.applyA σ))
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hpres : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ →
      o.applicableA σ → Inv (o.applyA σ)) :
    (ground d p rel).ConsistentOn (Reachable (ground d p rel))
      (ExampleHeuristics.Satellite.improved (ground d p rel)).eval :=
  compiled_consistentOn d p rel _ Inv (dataMatches_ground d p rel hwf) hwf hcost
    hnd hshape hinit hpres

/-
**Satellite's improved heuristic is admissible on the task the planner searches**,
with nothing about its tables assumed.

What is left are the obligations about the domain's schemas: that every grounded
operator moves the state in one of the three shapes of `SchemaStep`, and that the
invariant the shapes need holds of `:init` and survives every operator.
-/
theorem improved_admissible_of_shape (d : Domain) (p : Problem) (rel : Bool)
    (Inv : AtomState → Prop)
    (hwf : Task.WF (ground d p rel))
    (hcost : ∀ o ∈ groundedOps d p rel, 0 < o.cost)
    (hnd : (cfgOf (ground d p rel)).images.toList.Nodup)
    (hshape : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ → o.applicableA σ →
      SchemaStep (cfgOf (ground d p rel)) σ (o.applyA σ))
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hpres : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ →
      o.applicableA σ → Inv (o.applyA σ)) :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel))
      (ExampleHeuristics.Satellite.improved (ground d p rel)).eval :=
  compiled_admissibleOn d p rel _ Inv (dataMatches_ground d p rel hwf) hwf hcost
    (image_goalAtom_mem d p rel) (pointing_goalAtom_mem d p rel) hnd hshape hinit hpres

end Planner.Lifted.Satellite

/- -------------------------------------------------------------------------- -/
/-
What a Satellite task's compiled tables say, read as atoms.

`Proofs/Lifted/SatelliteCompile.lean` pairs each compiled table with a lifted one
entry for entry.  That is enough to know the two sides compute the same number.
The step proof needs more: which atom each entry *is*, and that an entry exists
for every object the schemas name.  Both are read off `compile` here, once, so
that the schema cases are about the domain rather than about arrays.

`Pinned` lives here too, because half its fields are about these tables.
-/

namespace Planner

open Planner.Pddl

/-!
### A delete the grounder keeps

`OpFactsAdd` records the adds a *raw* operator keeps; this is the mirror image,
and it is what a domain needs whose value reads "this instrument is no longer
calibrated" off a delete the operator does not also read.  `OpFacts.delComplete`
is too weak for that: it asks the atom to be a precondition, which is exactly the
case the relevance analysis handles on its own.

Nothing here is about Satellite, and it belongs beside `opFacts_raw_add` in
`Proofs/GroundingSound.lean`; it is kept here while it has one user.
-/

/-- What a raw operator keeps of its schema's deletes. -/
structure OpFactsDel (d : Domain) (p : Problem) (op : AtomOp) extends OpFacts d p op where
  /-- The grounder drops a delete only when the schema also adds it. -/
  delCompleteRaw : ∀ y ∈ inst.schema.del,
    instAtom inst.schema.params inst.args y ∉ inst.add →
    instAtom inst.schema.params inst.args y ∈ op.del

theorem opFacts_raw_del (d : Domain) (p : Problem) {op : AtomOp} (hop : op ∈ rawOps d p) :
    Nonempty (OpFactsDel d p op) := by
  have fold : ∀ (l : List Action) (acc : Array AtomOp),
      (∀ q ∈ acc, ∃ a ∈ d.actions,
        Produced d (allObjects d p) a (a.pre.filter fun x =>
          !(staticPredicates d).contains x.pred)
          (a.pre.filter fun x => (staticPredicates d).contains x.pred)
          (Std.HashSet.ofList p.init) q) →
      (∀ a ∈ l, a ∈ d.actions) →
      ∀ q ∈ l.foldl (fun g a => g ++ groundSchema d (typeObjects d (allObjects d p))
        (staticPredicates d) (Std.HashSet.ofList p.init) a) acc,
        ∃ a ∈ d.actions, Produced d (allObjects d p) a (a.pre.filter fun x =>
          !(staticPredicates d).contains x.pred)
          (a.pre.filter fun x => (staticPredicates d).contains x.pred)
          (Std.HashSet.ofList p.init) q := by
    intro l
    induction l with
    | nil => intro acc hacc _ q hq; exact hacc q hq
    | cons a rest ih =>
        intro acc hacc hl q hq
        refine ih _ ?_ (fun b hb => hl b (by simp [hb])) q hq
        intro x hx
        rcases Array.mem_append.mp hx with h1 | h1
        · exact hacc x h1
        · exact ⟨a, hl a (by simp), groundSchema_produced d (allObjects d p) _
            (fun ty o ho => typeObjects_wellTyped d (allObjects d p) ho) _ _ a h1⟩
  obtain ⟨a, ha, hprod⟩ := fold d.actions #[] (by simp) (fun b hb => hb) op
    (by simpa [rawOps] using hop)
  obtain ⟨i, h1, h2, h3, h4, h5, h5a, h6, h7⟩ := instance_of_produced ha hprod
  exact ⟨⟨⟨i, h1, h2, h3, h4, h6, fun y hy hn _ => h5 y hy hn, h7⟩, h5 ⟩⟩

namespace Lifted.Satellite

/-! ### The four object tables the heuristic indexes -/

abbrev satsA (t : Task) : Array Name := objsOf t "satellite"
abbrev dirsA (t : Task) : Array Name := objsOf t "direction"
abbrev insA (t : Task) : Array Name := objsOf t "instrument"
abbrev modesA (t : Task) : Array Name := objsOf t "mode"

abbrev satIx (t : Task) (n : Name) : Option Nat := (satsA t).findIdx? (· == n)
abbrev dirIx (t : Task) (n : Name) : Option Nat := (dirsA t).findIdx? (· == n)
abbrev insIx (t : Task) (n : Name) : Option Nat := (insA t).findIdx? (· == n)
abbrev modeIx (t : Task) (n : Name) : Option Nat := (modesA t).findIdx? (· == n)

/-- Reading the entry a table built by `map` holds for one named object. -/
theorem map_getD_of_findIdx {α : Type} {xs : Array Name} {n : Name} {i : Nat}
    (h : xs.findIdx? (· == n) = some i) (f : Name → α) (dflt : α) :
    (xs.map f).getD i dflt = f n := by
  obtain ⟨hlt, hget⟩ := findIdx_sound h
  have hxi : xs[i]'hlt = n := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt] at hget
    simpa using hget
  have hlt' : i < (xs.map f).size := by simpa using hlt
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt']
  simp [Array.getElem_map, hxi]

/-- Distinct positions hold distinct names, so an index determines its object. -/
theorem findIdx_inj {xs : Array Name} {a b : Name} {i : Nat}
    (ha : xs.findIdx? (· == a) = some i) (hb : xs.findIdx? (· == b) = some i) : a = b := by
  obtain ⟨-, ha'⟩ := findIdx_sound ha
  obtain ⟨-, hb'⟩ := findIdx_sound hb
  rw [← ha', hb']

/-! ### The three one-argument fact tables

`calibrated`, `power_on` and `power_avail` are stored the same way: one slot per
object, holding the fact whose atom names that object, or nothing when the task
never numbered such an atom.
-/

/-- The compiled shape of those three tables, read through the task's names. -/
def optTable (t : Task) (pred : Name) (objs : Array Name) : Array (Option GroundAtom) :=
  (objs.map fun o => ((t.factsWith pred).find? fun y => y.2.args == [o]).map (·.1)).map
    (Option.map (atomOf t))

theorem calibratedAtoms_eq (t : Task) :
    (cfgOf t).calibratedAtoms = optTable t "calibrated" (insA t) := rfl

theorem powerOnAtoms_eq (t : Task) :
    (cfgOf t).powerOnAtoms = optTable t "power_on" (insA t) := rfl

theorem powerAvailAtoms_eq (t : Task) :
    (cfgOf t).powerAvailAtoms = optTable t "power_avail" (satsA t) := rfl

/-- A numbered atom is found by the search that builds the slot. -/
theorem findArgs_isSome {t : Task} {pred : Name} {args : List Name} {f : Fact}
    (hf : f < t.factNames.size)
    (hname : t.factNames.getD f default = { pred := pred, args := args }) :
    ∃ x, (t.factsWith pred).find? (fun y => y.2.args == args) = some x := by
  have hmem : (f, ({ pred := pred, args := args } : GroundAtom)) ∈ t.factsWith pred :=
    mem_factsWith_of_named hf hname rfl
  rcases hfind : (t.factsWith pred).find? (fun y => y.2.args == args) with _ | x
  · have := Array.find?_eq_none.mp hfind _ hmem
    simp at this
  · exact ⟨x, hfind⟩

/-- **Whatever a slot holds names the object it was built for.** -/
theorem optTable_mem {t : Task} {pred : Name} {objs : Array Name} {a : GroundAtom}
    (h : some a ∈ optTable t pred objs) : ∃ o ∈ objs, a = { pred := pred, args := [o] } := by
  obtain ⟨x, hx, hval⟩ := Array.mem_map.mp h
  obtain ⟨o, ho, hxval⟩ := Array.mem_map.mp hx
  rcases hxo : x with _ | f
  · rw [hxo] at hval; simp at hval
  · rw [hxo] at hval
    simp only [Option.map_some, Option.some.injEq] at hval
    refine ⟨o, ho, ?_⟩
    rw [← hval]
    exact factsWith_find_args_map (by rw [hxval, hxo])

/-- The same, read at the position of a named object. -/
theorem optTable_getD {t : Task} {pred : Name} {objs : Array Name} {o : Name} {i : Nat}
    {a : GroundAtom} (hi : objs.findIdx? (· == o) = some i)
    (h : (optTable t pred objs).getD i none = some a) :
    a = { pred := pred, args := [o] } := by
  rw [optTable, Array.map_map, map_getD_of_findIdx hi
    (Option.map (atomOf t) ∘ fun o =>
      ((t.factsWith pred).find? fun y => y.2.args == [o]).map (·.1)) none] at h
  simp only [Function.comp_apply] at h
  rcases hx : (t.factsWith pred).find? (fun y => y.2.args == [o]) with _ | x
  · rw [hx] at h; simp at h
  · rw [hx] at h
    simp only [Option.map_some, Option.some.injEq] at h
    rw [← h]
    exact factsWith_find_args hx

/-- **And the slot of a numbered atom really holds it.** -/
theorem optTable_getD_of_named {t : Task} {pred : Name} {objs : Array Name} {o : Name}
    {i : Nat} {f : Fact} (hi : objs.findIdx? (· == o) = some i)
    (hf : f < t.factNames.size)
    (hname : t.factNames.getD f default = { pred := pred, args := [o] }) :
    (optTable t pred objs).getD i none = some { pred := pred, args := [o] } := by
  obtain ⟨x, hx⟩ := findArgs_isSome hf hname
  rw [optTable, Array.map_map, map_getD_of_findIdx hi
    (Option.map (atomOf t) ∘ fun o =>
      ((t.factsWith pred).find? fun y => y.2.args == [o]).map (·.1)) none]
  simp only [Function.comp_apply]
  rw [hx]
  simp only [Option.map_some, Option.some.injEq]
  exact factsWith_find_args hx

/-! ### What a Satellite task must satisfy

Every field is a decidable fact about the parsed domain and problem, or about
the tables `compile` builds from them.
-/

/-- The decidable facts about a parsed Satellite domain and problem that the
concrete improved-heuristic proof uses. -/
structure Pinned (d : Domain) (p : Problem) : Prop where
  domain : SatelliteDomain d
  /-- The four parameter types index exactly their declared object tables;
  none of them has proper subtypes among the problem's objects. -/
  satType : ∀ o ∈ allObjects d p,
    d.isSubtype o.type "satellite" = true → o.type = "satellite"
  dirType : ∀ o ∈ allObjects d p,
    d.isSubtype o.type "direction" = true → o.type = "direction"
  insType : ∀ o ∈ allObjects d p,
    d.isSubtype o.type "instrument" = true → o.type = "instrument"
  modeType : ∀ o ∈ allObjects d p,
    d.isSubtype o.type "mode" = true → o.type = "mode"
  /-- And all four are declared. -/
  satTypeName : "satellite" ∈ d.typeNames
  dirTypeName : "direction" ∈ d.typeNames
  insTypeName : "instrument" ∈ d.typeNames
  modeTypeName : "mode" ∈ d.typeNames
  /-- The pair passed the planner's own validators.  `namesNodup` below is read
  off it rather than assumed: validation checks the objects for duplicates, the
  constants for duplicates, and rejects an object that shadows a constant. -/
  validated : Validated d p
  /-- The three structural predicates never move. -/
  onBoardStatic : (staticPredicates d).contains "on_board" = true
  supportsStatic : (staticPredicates d).contains "supports" = true
  targetStatic : (staticPredicates d).contains "calibration_target" = true
  /-- The goal mentions no static predicate, as in the shipped Satellite tasks. -/
  goalDynamic : ∀ a ∈ p.goal, (staticPredicates d).contains a.pred = false
  /-- An instrument is carried by one satellite and calibrates against one
  direction.  Both are read off `:init` with `find?`, so both are needed. -/
  oneBoard : ∀ x ∈ initPairs p "on_board", ∀ y ∈ initPairs p "on_board",
    x.1 = y.1 → x.2 = y.2
  oneTarget : ∀ x ∈ initPairs p "calibration_target",
    ∀ y ∈ initPairs p "calibration_target", x.1 = y.1 → x.2 = y.2
  /-- Each satellite starts pointing at one direction, and at no direction it is
  also declared not to point at.  This is the invariant the value's positions
  rest on. -/
  initOnePointing : ∀ x ∈ initPairs p "pointing", ∀ y ∈ initPairs p "pointing",
    x.1 = y.1 → x.2 = y.2
  initNotPointing : ∀ x ∈ initPairs p "pointing", x ∉ initPairs p "not-pointing"
  /-- No instrument that is on board a satellite starts switched on, so a
  satellite's free power slot really means none of its instruments is on. -/
  initPowerOff : ∀ x ∈ initPairs p "on_board", x.1 ∉ initOnes p "power_on"
  /-- The parsed goal names each atom once.  Both compiled goal-table uniqueness
  properties are derived from this shared compiler fact. -/
  goalNodup : p.goal.Nodup

/-! ### Goal-table uniqueness comes from the parsed goal -/

/-- The compiled image table contains each parsed goal at most once. -/
theorem images_nodup {d : Domain} {p : Problem} (hp : Pinned d p) (rel : Bool) :
    (cfgOf (ground d p rel)).images.toList.Nodup := by
  show ((ExampleHeuristics.Satellite.compile (ground d p rel)).images.map
    (imageOf (ground d p rel))).toList.Nodup
  have himg : (ExampleHeuristics.Satellite.compile (ground d p rel)).images =
      ((ground d p rel).goalAtoms.zipIdx).filterMap
        (ExampleHeuristics.Satellite.imageEntry (ground d p rel)
          (fun x => ((ground d p rel).objectsOfTypes ["direction"]).findIdx? (· == x))
          (fun x => ((ground d p rel).objectsOfTypes ["mode"]).findIdx? (· == x))) := rfl
  rw [himg, Array.map_filterMap]
  refine goalTable_nodup d p rel hp.goalNodup _ (·.goalAtom) ?_
  intro x hx b hb
  obtain ⟨hlt, -⟩ := List.mem_zipIdx' hx
  have hi : x.2 < (taskOf d p rel).goalAtoms.size := by simpa using hlt
  obtain ⟨y, hy, hval⟩ := Option.map_eq_some_iff.mp hb
  have hgoal : y.goalFact = (ground d p rel).goal.getD x.2 0 := by
    unfold ExampleHeuristics.Satellite.imageEntry at hy
    by_cases hpred : (x.1.pred == "have_image") = true
    · rcases hargs : x.1.args with _ | ⟨dn, rest⟩
      · simp only [hpred, hargs] at hy; simp at hy
      · cases rest with
        | nil => simp only [hpred, hargs] at hy; simp at hy
        | cons mn rest' =>
            cases rest' with
            | cons _ _ => simp only [hpred, hargs] at hy; simp at hy
            | nil =>
                simp only [hpred, hargs] at hy
                rcases hd : ((ground d p rel).objectsOfTypes ["direction"]).findIdx?
                    (· == dn) with _ | di
                · rw [hd] at hy; simp at hy
                · rcases hm : ((ground d p rel).objectsOfTypes ["mode"]).findIdx?
                      (· == mn) with _ | mi
                  · rw [hd, hm] at hy; simp at hy
                  · rw [hd, hm] at hy
                    simp only [Option.some.injEq] at hy
                    rw [← hy]
    · simp only [Bool.not_eq_true] at hpred
      simp only [hpred] at hy
      simp at hy
  rw [← hval]
  show atomOf (ground d p rel) y.goalFact = _
  rw [hgoal]
  exact atomOf_goal_getD d p rel hi

/-- The compiled pointing-goal table contains each parsed goal at most once. -/
theorem pointing_nodup {d : Domain} {p : Problem} (hp : Pinned d p) (rel : Bool) :
    (cfgOf (ground d p rel)).pointingGoals.toList.Nodup := by
  show ((ExampleHeuristics.Satellite.compile (ground d p rel)).pointingGoals.map
    (pointingOf (ground d p rel))).toList.Nodup
  have hpt : (ExampleHeuristics.Satellite.compile (ground d p rel)).pointingGoals =
      ((ground d p rel).goalAtoms.zipIdx).filterMap
        (ExampleHeuristics.Satellite.pointingEntry (ground d p rel)
          (fun x => ((ground d p rel).objectsOfTypes ["satellite"]).findIdx? (· == x))
          (fun x => ((ground d p rel).objectsOfTypes ["direction"]).findIdx? (· == x))) := rfl
  rw [hpt, Array.map_filterMap]
  refine goalTable_nodup d p rel hp.goalNodup _ (·.goalAtom) ?_
  intro x hx b hb
  obtain ⟨hlt, -⟩ := List.mem_zipIdx' hx
  have hi : x.2 < (taskOf d p rel).goalAtoms.size := by simpa using hlt
  obtain ⟨y, hy, hval⟩ := Option.map_eq_some_iff.mp hb
  have hgoal : y.goalFact = (ground d p rel).goal.getD x.2 0 := by
    unfold ExampleHeuristics.Satellite.pointingEntry at hy
    by_cases hpred : (x.1.pred == "pointing") = true
    · rcases hargs : x.1.args with _ | ⟨sn, rest⟩
      · simp only [hpred, hargs] at hy; simp at hy
      · cases rest with
        | nil => simp only [hpred, hargs] at hy; simp at hy
        | cons dn rest' =>
            cases rest' with
            | cons _ _ => simp only [hpred, hargs] at hy; simp at hy
            | nil =>
                simp only [hpred, hargs] at hy
                rcases hs : ((ground d p rel).objectsOfTypes ["satellite"]).findIdx?
                    (· == sn) with _ | si
                · rw [hs] at hy; simp at hy
                · rcases hd : ((ground d p rel).objectsOfTypes ["direction"]).findIdx?
                      (· == dn) with _ | di
                  · rw [hs, hd] at hy; simp at hy
                  · rw [hs, hd] at hy
                    simp only [Option.some.injEq] at hy
                    rw [← hy]
    · simp only [Bool.not_eq_true] at hpred
      simp only [hpred] at hy
      simp at hy
  rw [← hval]
  show atomOf (ground d p rel) y.goalFact = _
  rw [hgoal]
  exact atomOf_goal_getD d p rel hi

/-- The object names are distinct — decided by validation, not assumed. -/
theorem Pinned.namesNodup {d : Domain} {p : Problem} (hp : Pinned d p) :
    ((allObjects d p).map (·.name)).Nodup := hp.validated.namesNodup

variable {d : Domain} {p : Problem}

theorem mem_satellites (hp : Pinned d p) (rel : Bool) {s : Name}
    (hw : WellTyped d (allObjects d p) "satellite" s) : s ∈ satsA (ground d p rel) :=
  mem_objsOf_of_wellTyped hp.satType hw

theorem mem_directions (hp : Pinned d p) (rel : Bool) {x : Name}
    (hw : WellTyped d (allObjects d p) "direction" x) : x ∈ dirsA (ground d p rel) :=
  mem_objsOf_of_wellTyped hp.dirType hw

theorem mem_instruments (hp : Pinned d p) (rel : Bool) {x : Name}
    (hw : WellTyped d (allObjects d p) "instrument" x) : x ∈ insA (ground d p rel) :=
  mem_objsOf_of_wellTyped hp.insType hw

theorem mem_modes (hp : Pinned d p) (rel : Bool) {x : Name}
    (hw : WellTyped d (allObjects d p) "mode" x) : x ∈ modesA (ground d p rel) :=
  mem_objsOf_of_wellTyped hp.modeType hw

/-- Each of the four object tables lists distinct names. -/
theorem objs_nodup (hp : Pinned d p) (rel : Bool) (ty : Name) :
    (objsOf (ground d p rel) ty).toList.Nodup :=
  objsOf_nodup hp.namesNodup

/-- With distinct names, the position of an object is the index it is read at. -/
theorem findIdx_getElem {xs : Array Name} (hnd : xs.toList.Nodup) {i : Nat}
    (hi : i < xs.size) : xs.findIdx? (· == xs[i]) = some i := by
  rw [Array.findIdx?_eq_some_iff_getElem]
  refine ⟨hi, by simp, ?_⟩
  intro j hj
  simp only [beq_iff_eq]
  intro hc
  have hjlt : j < xs.size := Nat.lt_trans hj hi
  have : j = i := (List.Nodup.getElem_inj_iff hnd).mp (by simpa using hc)
  omega

/-! ### The static structure tables

`supports`, `on_board` and `calibration_target` never move, so `compile` reads
them out of `staticAtoms` once.  Each table is asked two things: that an entry it
holds names a static atom, and that a static atom the schemas read has an entry.
-/

theorem supports_getD {t : Task} {ins : Name} {i : Nat} (hi : insIx t ins = some i) :
    (cfgOf t).supports.getD i #[] =
      (t.staticWith "supports").filterMap (fun a =>
        match a.args with
        | [x, m] => if x == ins then modeIx t m else none
        | _ => none) :=
  map_getD_of_findIdx hi _ _

theorem onBoard_getD {t : Task} {sat : Name} {si : Nat} (hs : satIx t sat = some si) :
    (cfgOf t).onBoard.getD si #[] =
      (t.staticWith "on_board").filterMap (fun a =>
        match a.args with
        | [i, x] => if x == sat then insIx t i else none
        | _ => none) :=
  map_getD_of_findIdx hs _ _

theorem satelliteOf_getD {t : Task} {ins : Name} {i : Nat} (hi : insIx t ins = some i) :
    (cfgOf t).satelliteOf.getD i none =
      (((t.staticWith "on_board").find? fun a =>
          match a.args with
          | [x, _] => x == ins
          | _ => false).bind fun a =>
        match a.args with
        | [_, sat] => satIx t sat
        | _ => none) :=
  map_getD_of_findIdx hi _ _

theorem calibTarget_getD {t : Task} {ins : Name} {i : Nat} (hi : insIx t ins = some i) :
    (cfgOf t).calibTarget.getD i none =
      (((t.staticWith "calibration_target").find? fun a =>
          match a.args with
          | [x, _] => x == ins
          | _ => false).bind fun a =>
        match a.args with
        | [_, dd] => dirIx t dd
        | _ => none) :=
  map_getD_of_findIdx hi _ _

/-- A two-argument static atom of one predicate, read off its arguments. -/
theorem staticPair {t : Task} {pred : Name} {a : GroundAtom} {x y : Name}
    (ha : a ∈ t.staticWith pred) (hargs : a.args = [x, y]) :
    a = { pred := pred, args := [x, y] } := by
  have hpred : a.pred = pred := by simpa using (Array.mem_filter.mp ha).2
  cases a with
  | mk q args => simp_all

/-- **The mode table holds exactly the modes a static atom grants.** -/
theorem mem_supports {t : Task} {ins mn : Name} {i m : Nat}
    (hi : insIx t ins = some i) (hm : modeIx t mn = some m)
    (ha : supports ins mn ∈ t.staticWith "supports") :
    m ∈ (cfgOf t).supports.getD i #[] := by
  rw [supports_getD hi]
  refine Array.mem_filterMap.mpr ⟨supports ins mn, ha, ?_⟩
  show (match (supports ins mn).args with
        | [x, mm] => if x == ins then modeIx t mm else none
        | _ => none) = some m
  simp [supports, hm]

theorem supports_sound {t : Task} {ins : Name} {i m : Nat} (hi : insIx t ins = some i)
    (hm : m ∈ (cfgOf t).supports.getD i #[]) :
    ∃ mn, modeIx t mn = some m ∧ supports ins mn ∈ t.staticWith "supports" := by
  rw [supports_getD hi] at hm
  obtain ⟨a, ha, hval⟩ := Array.mem_filterMap.mp hm
  rcases hargs : a.args with _ | ⟨x, rest⟩
  · rw [hargs] at hval; simp at hval
  · cases rest with
    | nil => rw [hargs] at hval; simp at hval
    | cons mn rest' =>
        cases rest' with
        | cons _ _ => rw [hargs] at hval; simp at hval
        | nil =>
            rw [hargs] at hval
            simp only at hval
            by_cases hx : (x == ins) = true
            · rw [if_pos hx] at hval
              obtain rfl : x = ins := by simpa using hx
              refine ⟨mn, hval, ?_⟩
              have : a = supports x mn := staticPair ha hargs
              rwa [this] at ha
            · rw [if_neg (by simpa using hx)] at hval; simp at hval

/-- **And the instrument table holds exactly the instruments on board.** -/
theorem mem_onBoard {t : Task} {ins sat : Name} {i si : Nat}
    (hi : insIx t ins = some i) (hs : satIx t sat = some si)
    (ha : onBoard ins sat ∈ t.staticWith "on_board") :
    i ∈ (cfgOf t).onBoard.getD si #[] := by
  rw [onBoard_getD hs]
  refine Array.mem_filterMap.mpr ⟨onBoard ins sat, ha, ?_⟩
  show (match (onBoard ins sat).args with
        | [j, x] => if x == sat then insIx t j else none
        | _ => none) = some i
  simp [onBoard, hi]

theorem onBoard_sound {t : Task} {sat : Name} {si i : Nat} (hs : satIx t sat = some si)
    (hi : i ∈ (cfgOf t).onBoard.getD si #[]) :
    ∃ ins, insIx t ins = some i ∧ onBoard ins sat ∈ t.staticWith "on_board" := by
  rw [onBoard_getD hs] at hi
  obtain ⟨a, ha, hval⟩ := Array.mem_filterMap.mp hi
  rcases hargs : a.args with _ | ⟨ins, rest⟩
  · rw [hargs] at hval; simp at hval
  · cases rest with
    | nil => rw [hargs] at hval; simp at hval
    | cons x rest' =>
        cases rest' with
        | cons _ _ => rw [hargs] at hval; simp at hval
        | nil =>
            rw [hargs] at hval
            simp only at hval
            by_cases hx : (x == sat) = true
            · rw [if_pos hx] at hval
              obtain rfl : x = sat := by simpa using hx
              refine ⟨ins, hval, ?_⟩
              have : a = onBoard ins x := staticPair ha hargs
              rwa [this] at ha
            · rw [if_neg (by simpa using hx)] at hval; simp at hval

/-- A static atom of the task is an atom of `:init`. -/
theorem staticWith_init (rel : Bool) {pred : Name} {a : GroundAtom}
    (ha : a ∈ (ground d p rel).staticWith pred) : a ∈ p.init :=
  (staticWith_sub d p rel ha).1

/-- **The satellite an instrument is on.**  `compile` takes the first `on_board`
atom naming it, and `oneBoard` says there is only one. -/
theorem satelliteOf_eq (hp : Pinned d p) (rel : Bool) {ins sat : Name} {i si : Nat}
    (hi : insIx (ground d p rel) ins = some i)
    (hs : satIx (ground d p rel) sat = some si)
    (ha : onBoard ins sat ∈ (ground d p rel).staticWith "on_board") :
    (cfgOf (ground d p rel)).satelliteOf.getD i none = some si := by
  rw [satelliteOf_getD hi]
  rcases hfind : ((ground d p rel).staticWith "on_board").find? (fun a =>
      match a.args with
      | [x, _] => x == ins
      | _ => false) with _ | a
  · have := Array.find?_eq_none.mp hfind (onBoard ins sat) ha
    simp [onBoard] at this
  · have hamem : a ∈ (ground d p rel).staticWith "on_board" :=
      Array.mem_of_find?_eq_some hfind
    have hcond : (match a.args with
        | [x, _] => x == ins
        | _ => false) = true := by simpa using Array.find?_some hfind
    rcases hargs : a.args with _ | ⟨x, rest⟩
    · rw [hargs] at hcond; simp at hcond
    · cases rest with
      | nil => rw [hargs] at hcond; simp at hcond
      | cons y rest' =>
          cases rest' with
          | cons _ _ => rw [hargs] at hcond; simp at hcond
          | nil =>
              rw [hargs] at hcond
              have hxi : x = ins := by simpa using hcond
              have haeq : a = onBoard ins y := by
                have hv := staticPair hamem hargs
                rw [hxi] at hv
                exact hv
              have h1 : (ins, y) ∈ initPairs p "on_board" := by
                refine mem_initPairs.mpr ?_
                show onBoard ins y ∈ p.init
                rw [← haeq]; exact staticWith_init rel hamem
              have h2 : (ins, sat) ∈ initPairs p "on_board" :=
                mem_initPairs.mpr (staticWith_init rel ha)
              have hy : y = sat := hp.oneBoard _ h1 _ h2 rfl
              rw [hfind]
              simp [hargs, hy, hs]

/-- **The direction an instrument calibrates against**, by the same argument. -/
theorem calibTarget_eq (hp : Pinned d p) (rel : Bool) {ins dn : Name} {i di : Nat}
    (hi : insIx (ground d p rel) ins = some i)
    (hd : dirIx (ground d p rel) dn = some di)
    (ha : calibTarget ins dn ∈ (ground d p rel).staticWith "calibration_target") :
    (cfgOf (ground d p rel)).calibTarget.getD i none = some di := by
  rw [calibTarget_getD hi]
  rcases hfind : ((ground d p rel).staticWith "calibration_target").find? (fun a =>
      match a.args with
      | [x, _] => x == ins
      | _ => false) with _ | a
  · have := Array.find?_eq_none.mp hfind (calibTarget ins dn) ha
    simp [calibTarget] at this
  · have hamem : a ∈ (ground d p rel).staticWith "calibration_target" :=
      Array.mem_of_find?_eq_some hfind
    have hcond : (match a.args with
        | [x, _] => x == ins
        | _ => false) = true := by simpa using Array.find?_some hfind
    rcases hargs : a.args with _ | ⟨x, rest⟩
    · rw [hargs] at hcond; simp at hcond
    · cases rest with
      | nil => rw [hargs] at hcond; simp at hcond
      | cons y rest' =>
          cases rest' with
          | cons _ _ => rw [hargs] at hcond; simp at hcond
          | nil =>
              rw [hargs] at hcond
              have hxi : x = ins := by simpa using hcond
              have haeq : a = calibTarget ins y := by
                have hv := staticPair hamem hargs
                rw [hxi] at hv
                exact hv
              have h1 : (ins, y) ∈ initPairs p "calibration_target" := by
                refine mem_initPairs.mpr ?_
                show calibTarget ins y ∈ p.init
                rw [← haeq]; exact staticWith_init rel hamem
              have h2 : (ins, dn) ∈ initPairs p "calibration_target" :=
                mem_initPairs.mpr (staticWith_init rel ha)
              have hy : y = dn := hp.oneTarget _ h1 _ h2 rfl
              rw [hfind]
              simp [hargs, hy, hd]

/-- What a calibration-target entry names, read back. -/
theorem calibTarget_sound {t : Task} {ins : Name} {i di : Nat}
    (hi : insIx t ins = some i) (h : (cfgOf t).calibTarget.getD i none = some di) :
    ∃ dn, dirIx t dn = some di ∧
      calibTarget ins dn ∈ t.staticWith "calibration_target" := by
  rw [calibTarget_getD hi] at h
  rcases hfind : (t.staticWith "calibration_target").find? (fun a =>
      match a.args with
      | [x, _] => x == ins
      | _ => false) with _ | a
  · rw [hfind] at h; simp at h
  · rw [hfind] at h
    have hamem : a ∈ t.staticWith "calibration_target" := Array.mem_of_find?_eq_some hfind
    have hcond : (match a.args with
        | [x, _] => x == ins
        | _ => false) = true := by simpa using Array.find?_some hfind
    rcases hargs : a.args with _ | ⟨x, rest⟩
    · rw [hargs] at hcond; simp at hcond
    · cases rest with
      | nil => rw [hargs] at hcond; simp at hcond
      | cons y rest' =>
          cases rest' with
          | cons _ _ => rw [hargs] at hcond; simp at hcond
          | nil =>
              rw [hargs] at hcond
              have hxi : x = ins := by simpa using hcond
              have haeq : a = calibTarget ins y := by
                have hv := staticPair hamem hargs
                rw [hxi] at hv
                exact hv
              refine ⟨y, ?_, by rwa [haeq] at hamem⟩
              simp only [Option.bind_some, hargs] at h
              exact h

/-! ### Where each satellite is pointing

`pointingByDir` is the one dynamic table indexed by direction.  Its entries are
`pointing` facts paired with the satellite that would be looking that way.
-/

theorem pointingByDir_getD {t : Task} {dn : Name} {di : Nat} (h : dirIx t dn = some di) :
    (cfgOf t).pointingByDir.getD di #[] =
      ((t.factsWith "pointing").filterMap (fun y =>
        match y.2.args with
        | [sat, x] => if x == dn then (satIx t sat).map ((y.1, ·)) else none
        | _ => none)).map (fun y => (atomOf t y.1, y.2)) := by
  show (((dirsA t).map (fun dd => (t.factsWith "pointing").filterMap (fun y =>
      match y.2.args with
      | [sat, x] => if x == dd then (satIx t sat).map ((y.1, ·)) else none
      | _ => none))).map (fun xs => xs.map (fun y => (atomOf t y.1, y.2)))).getD di #[] = _
  rw [Array.map_map, map_getD_of_findIdx h _ #[]]
  rfl

/-- **Every entry of the table is a `pointing` atom on the direction it indexes.** -/
theorem pointingByDir_data {t : Task} {di : Nat} {q : GroundAtom × Nat}
    (hnd : (dirsA t).toList.Nodup)
    (hq : q ∈ (cfgOf t).pointingByDir.getD di #[]) :
    ∃ sn dn, q.1 = pointing sn dn ∧ satIx t sn = some q.2 ∧ dirIx t dn = some di := by
  by_cases hlt : di < (dirsA t).size
  · have hdn : dirIx t (dirsA t)[di] = some di := findIdx_getElem hnd hlt
    rw [pointingByDir_getD hdn] at hq
    obtain ⟨y, hy, hval⟩ := Array.mem_map.mp hq
    obtain ⟨z, hz, hzval⟩ := Array.mem_filterMap.mp hy
    obtain ⟨-, hzname, hzpred⟩ := mem_factsWith hz
    rcases hargs : z.2.args with _ | ⟨sat, rest⟩
    · rw [hargs] at hzval; simp at hzval
    · cases rest with
      | nil => rw [hargs] at hzval; simp at hzval
      | cons x rest' =>
          cases rest' with
          | cons _ _ => rw [hargs] at hzval; simp at hzval
          | nil =>
              rw [hargs] at hzval
              simp only at hzval
              by_cases hx : (x == (dirsA t)[di]) = true
              · rw [if_pos hx] at hzval
                rcases hsi : satIx t sat with _ | si
                · rw [hsi] at hzval; simp at hzval
                · rw [hsi] at hzval
                  simp only [Option.map_some, Option.some.injEq] at hzval
                  have hxv : x = (dirsA t)[di] := by simpa using hx
                  refine ⟨sat, x, ?_, ?_, by rw [hxv]; exact hdn⟩
                  · rw [← hval, ← hzval]
                    show t.factNames.getD z.1 default = pointing sat x
                    rw [hzname]
                    cases hz2 : z.2 with
                    | mk pr args => simp_all [pointing]
                  · rw [← hval, ← hzval]; exact hsi
              · rw [if_neg (by simpa using hx)] at hzval; simp at hzval
  · have hsize : (cfgOf t).pointingByDir.size = (dirsA t).size := by
      show (((dirsA t).map (fun dd => (t.factsWith "pointing").filterMap (fun y =>
        match y.2.args with
        | [sat, x] => if x == dd then (satIx t sat).map ((y.1, ·)) else none
        | _ => none))).map (fun xs => xs.map (fun y => (atomOf t y.1, y.2)))).size = _
      simp
    rw [Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none (by rw [hsize]; exact Nat.le_of_not_gt hlt)] at hq
    simp at hq

/-- **And a numbered `pointing` atom really has an entry.** -/
theorem mem_pointingByDir {t : Task} {sn dn : Name} {si di : Nat} {f : Fact}
    (hs : satIx t sn = some si) (hd : dirIx t dn = some di)
    (hf : f < t.factNames.size) (hname : t.factNames.getD f default = pointing sn dn) :
    (pointing sn dn, si) ∈ (cfgOf t).pointingByDir.getD di #[] := by
  rw [pointingByDir_getD hd]
  refine Array.mem_map.mpr ⟨(f, si), ?_, ?_⟩
  · refine Array.mem_filterMap.mpr ⟨(f, pointing sn dn),
      mem_factsWith_of_named hf hname rfl, ?_⟩
    show (match (pointing sn dn).args with
          | [sat, x] => if x == dn then (satIx t sat).map ((f, ·)) else none
          | _ => none) = some (f, si)
    simp [pointing, hs]
  · show (t.factNames.getD f default, si) = (pointing sn dn, si)
    rw [hname]

/-! ### The three instrument and satellite tables, named -/

theorem calibrated_atom {t : Task} {a : GroundAtom}
    (h : some a ∈ (cfgOf t).calibratedAtoms) : ∃ ins ∈ insA t, a = calibrated ins := by
  rw [calibratedAtoms_eq] at h
  exact optTable_mem h

theorem powerOn_atom {t : Task} {a : GroundAtom}
    (h : some a ∈ (cfgOf t).powerOnAtoms) : ∃ ins ∈ insA t, a = powerOn ins := by
  rw [powerOnAtoms_eq] at h
  exact optTable_mem h

theorem powerAvail_atom {t : Task} {a : GroundAtom}
    (h : some a ∈ (cfgOf t).powerAvailAtoms) : ∃ sat ∈ satsA t, a = powerAvail sat := by
  rw [powerAvailAtoms_eq] at h
  exact optTable_mem h

theorem calibrated_pred {t : Task} {a : GroundAtom}
    (h : some a ∈ (cfgOf t).calibratedAtoms) : a.pred = "calibrated" := by
  obtain ⟨ins, -, rfl⟩ := calibrated_atom h; rfl

theorem powerOn_pred {t : Task} {a : GroundAtom}
    (h : some a ∈ (cfgOf t).powerOnAtoms) : a.pred = "power_on" := by
  obtain ⟨ins, -, rfl⟩ := powerOn_atom h; rfl

theorem powerAvail_pred {t : Task} {a : GroundAtom}
    (h : some a ∈ (cfgOf t).powerAvailAtoms) : a.pred = "power_avail" := by
  obtain ⟨sat, -, rfl⟩ := powerAvail_atom h; rfl

theorem calibrated_slot {t : Task} {ins : Name} {i : Nat} {a : GroundAtom}
    (hi : insIx t ins = some i) (h : (cfgOf t).calibratedAtoms.getD i none = some a) :
    a = calibrated ins := by
  rw [calibratedAtoms_eq] at h; exact optTable_getD hi h

theorem powerOn_slot {t : Task} {ins : Name} {i : Nat} {a : GroundAtom}
    (hi : insIx t ins = some i) (h : (cfgOf t).powerOnAtoms.getD i none = some a) :
    a = powerOn ins := by
  rw [powerOnAtoms_eq] at h; exact optTable_getD hi h

theorem powerAvail_slot {t : Task} {sat : Name} {si : Nat} {a : GroundAtom}
    (hs : satIx t sat = some si) (h : (cfgOf t).powerAvailAtoms.getD si none = some a) :
    a = powerAvail sat := by
  rw [powerAvailAtoms_eq] at h; exact optTable_getD hs h

theorem calibrated_named {t : Task} {ins : Name} {i : Nat} {f : Fact}
    (hi : insIx t ins = some i) (hf : f < t.factNames.size)
    (hname : t.factNames.getD f default = calibrated ins) :
    (cfgOf t).calibratedAtoms.getD i none = some (calibrated ins) := by
  rw [calibratedAtoms_eq]; exact optTable_getD_of_named hi hf hname

theorem powerOn_named {t : Task} {ins : Name} {i : Nat} {f : Fact}
    (hi : insIx t ins = some i) (hf : f < t.factNames.size)
    (hname : t.factNames.getD f default = powerOn ins) :
    (cfgOf t).powerOnAtoms.getD i none = some (powerOn ins) := by
  rw [powerOnAtoms_eq]; exact optTable_getD_of_named hi hf hname

theorem powerAvail_named {t : Task} {sat : Name} {si : Nat} {f : Fact}
    (hs : satIx t sat = some si) (hf : f < t.factNames.size)
    (hname : t.factNames.getD f default = powerAvail sat) :
    (cfgOf t).powerAvailAtoms.getD si none = some (powerAvail sat) := by
  rw [powerAvailAtoms_eq]; exact optTable_getD_of_named hs hf hname

/-! ### Reading a static precondition of a schema back as a static atom -/

/-- A static precondition an instance names is one of the task's static atoms. -/
theorem static_of_pre (hp : Pinned d p) (rel : Bool) {o : AtomOp} (hf : OpFacts d p o)
    {a : GroundAtom} (hmem : a ∈ hf.inst.pre)
    (hstatic : (staticPredicates d).contains a.pred = true) :
    a ∈ (ground d p rel).staticWith a.pred := by
  have hmem' : a ∈ hf.inst.schema.pre.map (instAtom hf.inst.schema.params hf.inst.args) := hmem
  obtain ⟨y, hy, hval⟩ := List.mem_map.mp hmem'
  have hinit : a ∈ p.init := by
    have hpred : y.pred = a.pred := by rw [← hval]; rfl
    have := hf.staticHeld y hy (by rw [hpred]; exact hstatic)
    rw [hval] at this
    simpa using this
  have hnot : a ∉ allAtoms (groundedOps d p rel) p.goal.toArray := by
    intro hc
    have := hp.goalDynamic _ (mem_goal_of_static d p rel hc hstatic)
    rw [this] at hstatic
    exact Bool.noConfusion hstatic
  exact mem_staticWith d p rel hinit hnot rfl

end Lifted.Satellite

end Planner

/- -------------------------------------------------------------------------- -/
/-
The invariant Satellite's improved heuristic reads.

Two of its four clauses are about where a satellite is looking, and two are about
which instrument is drawing power.  Both are needed, and for the same reason: the
value reads a *position* — which satellite is pointing where, and whether a
satellite has a slot free — and a position is only well defined because one atom
of its family holds at a time.

  * a satellite points at one direction, and never at one it is also declared
    *not* to point at.  The second clause is what makes `turn_to`'s two
    directions different, which is what makes its old `pointing` atom a delete
    the grounder keeps.
  * a satellite with a free power slot has no instrument switched on, and no two
    instruments on one satellite are on at once.  Without them a `switch_on`
    could find its instrument already powered, and the ready set would *shrink*
    across an action that the value charges for growing it.

Every clause is decided on `:init` by one pass over the atoms of two predicates,
which is what `Pinned` records.
-/

namespace Planner.Lifted.Satellite

open Planner Planner.Pddl

variable {d : Domain} {p : Problem}

/-! ### The schemas' precondition lists -/

theorem turn_pre_eq {objects : List TypedName} (i : Instance d objects) {s dn dp : Name}
    (hs : i.schema = turnA) (ha : i.args = [s, dn, dp]) :
    i.pre = [pointing s dp, notPointing s dn] := by rw [i.pre_eq, hs, ha]; rfl

theorem switchOn_pre_eq {objects : List TypedName} (i : Instance d objects) {ins s : Name}
    (hs : i.schema = switchOnA) (ha : i.args = [ins, s]) :
    i.pre = [onBoard ins s, powerAvail s] := by rw [i.pre_eq, hs, ha]; rfl

theorem switchOff_pre_eq {objects : List TypedName} (i : Instance d objects) {ins s : Name}
    (hs : i.schema = switchOffA) (ha : i.args = [ins, s]) :
    i.pre = [onBoard ins s, powerOn ins] := by rw [i.pre_eq, hs, ha]; rfl

theorem calibrate_pre_eq {objects : List TypedName} (i : Instance d objects)
    {s ins dd : Name} (hs : i.schema = calibrateA) (ha : i.args = [s, ins, dd]) :
    i.pre = [onBoard ins s, calibTarget ins dd, pointing s dd, powerOn ins] := by
  rw [i.pre_eq, hs, ha]; rfl

theorem image_pre_eq {objects : List TypedName} (i : Instance d objects)
    {s dd ins m : Name} (hs : i.schema = imageA) (ha : i.args = [s, dd, ins, m]) :
    i.pre = [calibrated ins, onBoard ins s, supports ins m, powerOn ins,
      pointing s dd] := by rw [i.pre_eq, hs, ha]; rfl

/-! ### The predicates the value reads are all dynamic -/

theorem notPointing_dynamic (hd : SatelliteDomain d) :
    (staticPredicates d).contains "not-pointing" = false :=
  not_static_of_mem_add (a := turnA) (by rw [hd]; simp) (y := notPointingV "?s" "?d_prev")
    (by simp [turnA])

/-- An atom no add or delete of the instance mentions is untouched. -/
theorem frame_pred {o : AtomOp} (hf : OpFacts d p o) {add del : List GroundAtom}
    (hadd : hf.inst.add = add) (hdel : hf.inst.del = del) {a : GroundAtom}
    (hpreds : ∀ b ∈ add ++ del, b.pred ≠ a.pred) (σ : AtomState) :
    o.applyA σ a = σ a := by
  refine frame_of_lists hf hadd hdel ?_ ?_ σ
  · intro hc
    exact hpreds a (by simp [hc]) rfl
  · intro hc
    exact hpreds a (by simp [hc]) rfl

/-! ### The invariant -/

/-- What every state the search can reach satisfies. -/
structure Inv (p : Problem) (σ : AtomState) : Prop where
  /-- A satellite points at one direction at a time. -/
  onePointing : ∀ s d₁ d₂, σ (pointing s d₁) = true → σ (pointing s d₂) = true → d₁ = d₂
  /-- And never at one it is also declared not to point at. -/
  notBoth : ∀ s dd, σ (pointing s dd) = true → σ (notPointing s dd) = false
  /-- A free power slot means no instrument of that satellite is on. -/
  powerFree : ∀ i s, onBoard i s ∈ p.init → σ (powerAvail s) = true →
    σ (powerOn i) = false
  /-- And one satellite powers one instrument at a time. -/
  oneOn : ∀ i j s, onBoard i s ∈ p.init → onBoard j s ∈ p.init →
    σ (powerOn i) = true → σ (powerOn j) = true → i = j

/-! ### A static precondition holds in `:init` -/

theorem static_init {o : AtomOp} (hf : OpFacts d p o) {y : Atom}
    (hy : y ∈ hf.inst.schema.pre)
    (hst : (staticPredicates d).contains y.pred = true) :
    instAtom hf.inst.schema.params hf.inst.args y ∈ p.init := by
  have := hf.staticHeld y hy hst
  simpa using this

/-- The satellite a `switch_on` or `switch_off` names really carries its
instrument. -/
theorem onBoard_init (hp : Pinned d p) {o : AtomOp} (hf : OpFacts d p o) {ins s : Name}
    (hs : hf.inst.schema = switchOnA ∨ hf.inst.schema = switchOffA)
    (ha : hf.inst.args = [ins, s]) : onBoard ins s ∈ p.init := by
  rcases hs with hs | hs <;>
    · have hy : onBoardV "?i" "?s" ∈ hf.inst.schema.pre := by rw [hs]; simp [switchOnA, switchOffA]
      have := static_init hf hy (by simpa [onBoardV] using hp.onBoardStatic)
      have heq : instAtom hf.inst.schema.params hf.inst.args (onBoardV "?i" "?s")
          = onBoard ins s := by rw [hs, ha]; rfl
      rwa [heq] at this

/-! ### Everything a schema does not touch -/

/-- The four families the invariant reads, framed at once. -/
theorem inv_of_framed {o : AtomOp} (hf : OpFacts d p o) {add del : List GroundAtom}
    (hadd : hf.inst.add = add) (hdel : hf.inst.del = del)
    (hpreds : ∀ b ∈ add ++ del, b.pred ≠ "pointing" ∧ b.pred ≠ "not-pointing" ∧
      b.pred ≠ "power_on" ∧ b.pred ≠ "power_avail")
    {σ : AtomState} (hinv : Inv p σ) : Inv p (o.applyA σ) := by
  have hfr : ∀ a : GroundAtom, a.pred = "pointing" ∨ a.pred = "not-pointing" ∨
      a.pred = "power_on" ∨ a.pred = "power_avail" → o.applyA σ a = σ a := by
    intro a ha
    refine frame_pred hf hadd hdel ?_ σ
    intro b hb
    obtain ⟨h1, h2, h3, h4⟩ := hpreds b hb
    rcases ha with h | h | h | h <;> rw [h] <;> simp_all
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s d1 d2 h1 h2
    rw [hfr _ (Or.inl rfl)] at h1
    rw [hfr _ (Or.inl rfl)] at h2
    exact hinv.onePointing s d1 d2 h1 h2
  · intro s dd h1
    rw [hfr _ (Or.inl rfl)] at h1
    rw [hfr _ (Or.inr (Or.inl rfl))]
    exact hinv.notBoth s dd h1
  · intro i s hb h1
    rw [hfr _ (Or.inr (Or.inr (Or.inr rfl)))] at h1
    rw [hfr _ (Or.inr (Or.inr (Or.inl rfl)))]
    exact hinv.powerFree i s hb h1
  · intro i j s hb1 hb2 h1 h2
    rw [hfr _ (Or.inr (Or.inr (Or.inl rfl)))] at h1
    rw [hfr _ (Or.inr (Or.inr (Or.inl rfl)))] at h2
    exact hinv.oneOn i j s hb1 hb2 h1 h2

/-! ### `calibrate` and `take_image` touch nothing the invariant reads -/

theorem calibrate_inv {o : AtomOp} (hf : OpFacts d p o) {s ins dd : Name}
    (hs : hf.inst.schema = calibrateA) (ha : hf.inst.args = [s, ins, dd])
    {σ : AtomState} (hinv : Inv p σ) : Inv p (o.applyA σ) := by
  obtain ⟨-, -, hadd, hdel⟩ := calibrate_atoms hf.inst hs ha
  refine inv_of_framed hf hadd hdel ?_ hinv
  intro b hb
  simp only [List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hb
  subst hb
  exact ⟨by simp [calibrated], by simp [calibrated], by simp [calibrated],
    by simp [calibrated]⟩

theorem image_inv {o : AtomOp} (hf : OpFacts d p o) {s dd ins m : Name}
    (hs : hf.inst.schema = imageA) (ha : hf.inst.args = [s, dd, ins, m])
    {σ : AtomState} (hinv : Inv p σ) : Inv p (o.applyA σ) := by
  obtain ⟨-, -, -, hadd, hdel⟩ := image_atoms hf.inst hs ha
  refine inv_of_framed hf hadd hdel ?_ hinv
  intro b hb
  simp only [List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hb
  subst hb
  exact ⟨by simp [haveImage], by simp [haveImage], by simp [haveImage],
    by simp [haveImage]⟩

/-! ### The two power schemas -/

theorem switchOn_inv (hp : Pinned d p) {o : AtomOp} (hf : OpFacts d p o) {ins s : Name}
    (hs : hf.inst.schema = switchOnA) (ha : hf.inst.args = [ins, s])
    {σ : AtomState} (hinv : Inv p σ) (happ : o.applicableA σ) : Inv p (o.applyA σ) := by
  obtain ⟨hpa, hadd, hdel⟩ := switchOn_atoms hf.inst hs ha
  have hdyn : (staticPredicates d).contains (powerAvail s).pred = false := by
    simpa [powerAvail] using powerAvail_dynamic hp.domain
  have hboard : onBoard ins s ∈ p.init := onBoard_init hp hf (Or.inl hs) ha
  have havail : σ (powerAvail s) = true := pre_holds hf hpa hdyn happ
  have hav' : o.applyA σ (powerAvail s) = false :=
    falsified_of_lists hf hadd hdel (by simp [powerAvail, powerOn]) (by simp) hpa hdyn σ
  have hfr : ∀ a : GroundAtom, a ≠ powerOn ins → a ≠ calibrated ins → a ≠ powerAvail s →
      o.applyA σ a = σ a := by
    intro a h1 h2 h3
    exact frame_of_lists hf hadd hdel (by simp [h1]) (by simp [h2, h3]) σ
  have hup : ∀ k, o.applyA σ (powerOn k) = true → k = ins ∨ σ (powerOn k) = true := by
    intro k hk
    by_cases hki : k = ins
    · exact Or.inl hki
    · refine Or.inr ?_
      rw [hfr (powerOn k) (by simp [powerOn, hki]) (by simp [powerOn, calibrated])
        (by simp [powerOn, powerAvail])] at hk
      exact hk
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s' d1 d2 h1 h2
    rw [hfr (pointing s' d1) (by simp [pointing, powerOn]) (by simp [pointing, calibrated])
      (by simp [pointing, powerAvail])] at h1
    rw [hfr (pointing s' d2) (by simp [pointing, powerOn]) (by simp [pointing, calibrated])
      (by simp [pointing, powerAvail])] at h2
    exact hinv.onePointing s' d1 d2 h1 h2
  · intro s' dd h1
    rw [hfr (pointing s' dd) (by simp [pointing, powerOn]) (by simp [pointing, calibrated])
      (by simp [pointing, powerAvail])] at h1
    rw [hfr (notPointing s' dd) (by simp [notPointing, powerOn])
      (by simp [notPointing, calibrated]) (by simp [notPointing, powerAvail])]
    exact hinv.notBoth s' dd h1
  · intro i' s'' hb hpa'
    have hne : s'' ≠ s := by
      intro hc
      rw [hc, hav'] at hpa'
      exact Bool.noConfusion hpa'
    have hsig : σ (powerAvail s'') = true := by
      rw [← hfr (powerAvail s'') (by simp [powerAvail, powerOn])
        (by simp [powerAvail, calibrated]) (by simp [powerAvail, hne])]
      exact hpa'
    have hins : i' ≠ ins := by
      intro hc
      exact hne (hp.oneBoard (i', s'') (mem_initPairs.mpr hb) (ins, s)
        (mem_initPairs.mpr hboard) hc)
    rw [hfr (powerOn i') (by simp [powerOn, hins]) (by simp [powerOn, calibrated])
      (by simp [powerOn, powerAvail])]
    exact hinv.powerFree i' s'' hb hsig
  · intro i' j' s'' hb1 hb2 h1 h2
    rcases hup i' h1 with hi | hi
    · rcases hup j' h2 with hj | hj
      · rw [hi, hj]
      · exfalso
        have hss : s'' = s :=
          hp.oneBoard (i', s'') (mem_initPairs.mpr hb1) (ins, s) (mem_initPairs.mpr hboard) hi
        rw [hinv.powerFree j' s'' hb2 (by rw [hss]; exact havail)] at hj
        exact Bool.noConfusion hj
    · rcases hup j' h2 with hj | hj
      · exfalso
        have hss : s'' = s :=
          hp.oneBoard (j', s'') (mem_initPairs.mpr hb2) (ins, s) (mem_initPairs.mpr hboard) hj
        rw [hinv.powerFree i' s'' hb1 (by rw [hss]; exact havail)] at hi
        exact Bool.noConfusion hi
      · exact hinv.oneOn i' j' s'' hb1 hb2 hi hj

theorem switchOff_inv (hp : Pinned d p) {o : AtomOp} (hf : OpFacts d p o) {ins s : Name}
    (hs : hf.inst.schema = switchOffA) (ha : hf.inst.args = [ins, s])
    {σ : AtomState} (hinv : Inv p σ) (happ : o.applicableA σ) : Inv p (o.applyA σ) := by
  obtain ⟨hpre, hadd, hdel⟩ := switchOff_atoms hf.inst hs ha
  have hdyn : (staticPredicates d).contains (powerOn ins).pred = false := by
    simpa [powerOn] using powerOn_dynamic hp.domain
  have hboard : onBoard ins s ∈ p.init := onBoard_init hp hf (Or.inr hs) ha
  have hon : σ (powerOn ins) = true := pre_holds hf hpre hdyn happ
  have hoff : o.applyA σ (powerOn ins) = false :=
    falsified_of_lists hf hadd hdel (by simp [powerOn, powerAvail]) (by simp) hpre hdyn σ
  have hfr : ∀ a : GroundAtom, a ≠ powerAvail s → a ≠ powerOn ins → o.applyA σ a = σ a := by
    intro a h1 h2
    exact frame_of_lists hf hadd hdel (by simp [h1]) (by simp [h2]) σ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s' d1 d2 h1 h2
    rw [hfr (pointing s' d1) (by simp [pointing, powerAvail]) (by simp [pointing, powerOn])] at h1
    rw [hfr (pointing s' d2) (by simp [pointing, powerAvail]) (by simp [pointing, powerOn])] at h2
    exact hinv.onePointing s' d1 d2 h1 h2
  · intro s' dd h1
    rw [hfr (pointing s' dd) (by simp [pointing, powerAvail]) (by simp [pointing, powerOn])] at h1
    rw [hfr (notPointing s' dd) (by simp [notPointing, powerAvail])
      (by simp [notPointing, powerOn])]
    exact hinv.notBoth s' dd h1
  · intro i' s'' hb hpa'
    by_cases hi : i' = ins
    · rw [hi]; exact hoff
    · rw [hfr (powerOn i') (by simp [powerOn, powerAvail]) (by simp [powerOn, hi])]
      by_cases hss : s'' = s
      · by_contra hc
        have hitrue : σ (powerOn i') = true := by
          cases hv : σ (powerOn i') with
          | false => exact absurd hv hc
          | true => rfl
        exact hi (hinv.oneOn i' ins s'' hb (by rw [hss]; exact hboard) hitrue hon)
      · have hsig : σ (powerAvail s'') = true := by
          rw [← hfr (powerAvail s'') (by simp [powerAvail, hss]) (by simp [powerAvail, powerOn])]
          exact hpa'
        exact hinv.powerFree i' s'' hb hsig
  · intro i' j' s'' hb1 hb2 h1 h2
    have hi : i' ≠ ins := by
      intro hc
      rw [hc, hoff] at h1
      exact Bool.noConfusion h1
    have hj : j' ≠ ins := by
      intro hc
      rw [hc, hoff] at h2
      exact Bool.noConfusion h2
    rw [hfr (powerOn i') (by simp [powerOn, powerAvail]) (by simp [powerOn, hi])] at h1
    rw [hfr (powerOn j') (by simp [powerOn, powerAvail]) (by simp [powerOn, hj])] at h2
    exact hinv.oneOn i' j' s'' hb1 hb2 h1 h2

/-! ### `turn_to`

The two directions of a turn are different, and that is not an assumption: the
old direction is one the satellite points at and the new one is one it is
declared not to point at, so the invariant separates them.  Everything else
about the turn follows from its literal add and delete lists.
-/

/-- **A turn really turns.** -/
theorem turn_ne (hp : Pinned d p) {o : AtomOp} (hf : OpFacts d p o) {s dn dp : Name}
    (hs : hf.inst.schema = turnA) (ha : hf.inst.args = [s, dn, dp])
    {σ : AtomState} (hinv : Inv p σ) (happ : o.applicableA σ) : dn ≠ dp := by
  have hpre := turn_pre_eq hf.inst hs ha
  have hold : σ (pointing s dp) = true :=
    pre_holds hf (by rw [hpre]; simp)
      (by simpa [pointing] using pointing_dynamic hp.domain) happ
  have hnew : σ (notPointing s dn) = true :=
    pre_holds hf (by rw [hpre]; simp)
      (by simpa [notPointing] using notPointing_dynamic hp.domain) happ
  intro hc
  rw [hc] at hnew
  rw [hinv.notBoth s dp hold] at hnew
  exact Bool.noConfusion hnew

theorem turn_inv (hp : Pinned d p) {o : AtomOp} (hf : OpFacts d p o) {s dn dp : Name}
    (hs : hf.inst.schema = turnA) (ha : hf.inst.args = [s, dn, dp])
    {σ : AtomState} (hinv : Inv p σ) (happ : o.applicableA σ) : Inv p (o.applyA σ) := by
  have hne : dn ≠ dp := turn_ne hp hf hs ha hinv happ
  have hpre := turn_pre_eq hf.inst hs ha
  obtain ⟨-, hadd, hdel⟩ := turn_atoms hf.inst hs ha
  have hptDyn : (staticPredicates d).contains (pointing s dp).pred = false := by
    simpa [pointing] using pointing_dynamic hp.domain
  have hnpDyn : (staticPredicates d).contains (notPointing s dn).pred = false := by
    simpa [notPointing] using notPointing_dynamic hp.domain
  have hdpTrue : σ (pointing s dp) = true := pre_holds hf (by rw [hpre]; simp) hptDyn happ
  have holdFalse : o.applyA σ (pointing s dp) = false :=
    falsified_of_lists hf hadd hdel (by simp [pointing, notPointing, Ne.symm hne])
      (by simp) (by rw [hpre]; simp) hptDyn σ
  have hnewFalse : o.applyA σ (notPointing s dn) = false :=
    falsified_of_lists hf hadd hdel (by simp [pointing, notPointing, hne])
      (by simp) (by rw [hpre]; simp) hnpDyn σ
  -- the only `pointing` atom a turn can assert is the one at its new direction
  have hpos : ∀ s' dd, o.applyA σ (pointing s' dd) = true →
      (s' = s ∧ dd = dn) ∨ (σ (pointing s' dd) = true ∧ ¬(s' = s ∧ dd = dp)) := by
    intro s' dd h
    by_cases heq : pointing s' dd = pointing s dn
    · exact Or.inl (by simpa [pointing] using heq)
    · refine Or.inr ⟨falls_of_lists hf hadd (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro (hc | hc)
        · exact heq hc
        · exact absurd hc (by simp [pointing, notPointing])) h, ?_⟩
      rintro ⟨rfl, rfl⟩
      rw [holdFalse] at h
      exact Bool.noConfusion h
  have hfrPow : ∀ a : GroundAtom, a.pred = "power_on" ∨ a.pred = "power_avail" →
      o.applyA σ a = σ a := by
    intro a hpred
    refine frame_pred hf hadd hdel ?_ σ
    intro b hb
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with (h | h) | (h | h) <;> subst h <;> rcases hpred with h | h <;> rw [h] <;>
      simp [pointing, notPointing]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s' d1 d2 h1 h2
    rcases hpos s' d1 h1 with ⟨hs1, hd1⟩ | ⟨hs1, hn1⟩
    · rcases hpos s' d2 h2 with ⟨-, hd2⟩ | ⟨hs2, hn2⟩
      · rw [hd1, hd2]
      · exfalso
        have hdp2 : d2 = dp := by
          refine hinv.onePointing s' d2 dp hs2 ?_
          rw [hs1]; exact hdpTrue
        exact hn2 ⟨hs1, hdp2⟩
    · rcases hpos s' d2 h2 with ⟨hs2, hd2⟩ | ⟨hs2', -⟩
      · exfalso
        have hdp1 : d1 = dp := by
          refine hinv.onePointing s' d1 dp hs1 ?_
          rw [hs2]; exact hdpTrue
        exact hn1 ⟨hs2, hdp1⟩
      · exact hinv.onePointing s' d1 d2 hs1 hs2'
  · intro s' dd h1
    rcases hpos s' dd h1 with ⟨hs1, hd1⟩ | ⟨hs1, hn1⟩
    · rw [hs1, hd1]; exact hnewFalse
    · cases hv : o.applyA σ (notPointing s' dd) with
      | false => rfl
      | true =>
          exfalso
          have hbefore : σ (notPointing s' dd) = true :=
            falls_of_lists hf hadd (by
              simp only [List.mem_cons, List.not_mem_nil, or_false]
              rintro (h | h)
              · exact absurd h (by simp [pointing, notPointing])
              · exact hn1 (by simpa [notPointing] using h)) hv
          rw [hinv.notBoth s' dd hs1] at hbefore
          exact Bool.noConfusion hbefore
  · intro i' s'' hb hpa'
    rw [hfrPow (powerAvail s'') (Or.inr rfl)] at hpa'
    rw [hfrPow (powerOn i') (Or.inl rfl)]
    exact hinv.powerFree i' s'' hb hpa'
  · intro i' j' s'' hb1 hb2 h1 h2
    rw [hfrPow (powerOn i') (Or.inl rfl)] at h1
    rw [hfrPow (powerOn j') (Or.inl rfl)] at h2
    exact hinv.oneOn i' j' s'' hb1 hb2 h1 h2

/-! ### The invariant holds of `:init` and survives every operator -/

theorem inv_init (hp : Pinned d p) : Inv p (fun a => p.init.toArray.contains a) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s d1 d2 h1 h2
    have m1 : (s, d1) ∈ initPairs p "pointing" := mem_initPairs.mpr (by simpa using h1)
    have m2 : (s, d2) ∈ initPairs p "pointing" := mem_initPairs.mpr (by simpa using h2)
    exact hp.initOnePointing _ m1 _ m2 rfl
  · intro s dd h1
    have m1 : (s, dd) ∈ initPairs p "pointing" := mem_initPairs.mpr (by simpa using h1)
    have : (s, dd) ∉ initPairs p "not-pointing" := hp.initNotPointing _ m1
    simp only [Bool.eq_false_iff, ne_eq]
    intro hc
    exact this (mem_initPairs.mpr (by simpa using hc))
  · intro i s hb _
    have m1 : (i, s) ∈ initPairs p "on_board" := mem_initPairs.mpr hb
    have : i ∉ initOnes p "power_on" := hp.initPowerOff _ m1
    simp only [Bool.eq_false_iff, ne_eq]
    intro hc
    exact this (mem_initOnes.mpr (by simpa using hc))
  · intro i j s hb1 _ h1 _
    exfalso
    have m1 : (i, s) ∈ initPairs p "on_board" := mem_initPairs.mpr hb1
    exact hp.initPowerOff _ m1 (mem_initOnes.mpr (by simpa using h1))

/-- **Every operator keeps it.** -/
theorem inv_step (hp : Pinned d p) (rel : Bool) :
    ∀ o ∈ groundedOps d p rel, ∀ σ, Inv p σ → o.applicableA σ → Inv p (o.applyA σ) := by
  intro o ho σ hinv happ
  obtain ⟨hf⟩ := opFacts_ground d p rel ho
  rcases instance_shape hp.domain hf.inst with
    ⟨s, dn, dp, hs, ha⟩ | ⟨ins, s, hs, ha⟩ | ⟨ins, s, hs, ha⟩ |
      ⟨s, ins, dd, hs, ha⟩ | ⟨s, dd, ins, m, hs, ha⟩
  · exact turn_inv hp hf hs ha hinv happ
  · exact switchOn_inv hp hf hs ha hinv happ
  · exact switchOff_inv hp hf hs ha hinv happ
  · exact calibrate_inv hf hs ha hinv
  · exact image_inv hf hs ha hinv

end Planner.Lifted.Satellite

/- -------------------------------------------------------------------------- -/
/-
Every grounded Satellite operator has one of the three heuristic shapes.

This file is the concrete end of the lifted Satellite proof.  The bounds on the
heuristic's interacting terms live in `SatelliteBounds`; here they are attached
to the five parsed schemas and finally to the operators produced by grounding.
-/

namespace Planner.Lifted.Satellite

open Planner Planner.Pddl

variable {d : Domain} {p : Problem}

/-! ### What the goal tables contain -/

/-- Every image-table entry names a `have_image` atom. -/
theorem image_goal_pred (rel : Bool) :
    ∀ g ∈ (cfgOf (ground d p rel)).images, g.goalAtom.pred = "have_image" := by
  intro g hg
  have hg' : g ∈ (ExampleHeuristics.Satellite.compile (ground d p rel)).images.map
      (imageOf (ground d p rel)) := hg
  obtain ⟨x, hx, hval⟩ := Array.mem_map.mp hg'
  obtain ⟨z, hz, hzval⟩ := Array.mem_filterMap.mp
    (hx : x ∈ (ExampleHeuristics.Satellite.compile (ground d p rel)).images)
  obtain ⟨-, hlt, hzget⟩ := Array.mem_zipIdx hz
  have hi : z.2 < (ground d p rel).goalAtoms.size := by simpa using hlt
  have hzget' : z.1 = (ground d p rel).goalAtoms[z.2] := by simpa using hzget
  unfold ExampleHeuristics.Satellite.imageEntry at hzval
  by_cases hpred : (z.1.pred == "have_image") = true
  · rcases hargs : z.1.args with _ | ⟨dn, rest⟩
    · simp only [hpred, hargs] at hzval; simp at hzval
    · cases rest with
      | nil => simp only [hpred, hargs] at hzval; simp at hzval
      | cons mn rest' =>
          cases rest' with
          | cons _ _ => simp only [hpred, hargs] at hzval; simp at hzval
          | nil =>
              simp only [hpred, hargs] at hzval
              rcases hd : (ground d p rel).objectsOfTypes ["direction"] |>.findIdx?
                  (· == dn) with _ | di
              · rw [hd] at hzval; simp at hzval
              · rcases hm : (ground d p rel).objectsOfTypes ["mode"] |>.findIdx?
                    (· == mn) with _ | mi
                · rw [hd, hm] at hzval; simp at hzval
                · rw [hd, hm] at hzval
                  simp only [Option.some.injEq] at hzval
                  subst x
                  subst g
                  show (atomOf (ground d p rel)
                    ((ground d p rel).goal.getD z.2 0)).pred = "have_image"
                  change ((ground d p rel).factNames.getD
                    ((ground d p rel).goal.getD z.2 0) default).pred = "have_image"
                  rw [(goal_name_eq d p rel hi).1]
                  rw [← hzget']
                  simpa using hpred
  · simp only [Bool.not_eq_true] at hpred
    simp only [hpred] at hzval
    simp at hzval

/-- An image-table entry also carries the indices of the direction and mode
named by its goal atom. -/
theorem image_goal_data (rel : Bool) :
    ∀ g ∈ (cfgOf (ground d p rel)).images, ∃ dn mn,
      g.goalAtom = haveImage dn mn ∧
      ((ground d p rel).objectsOfTypes ["direction"]).findIdx? (· == dn) = some g.dir ∧
      ((ground d p rel).objectsOfTypes ["mode"]).findIdx? (· == mn) = some g.mode := by
  intro g hg
  have hg' : g ∈ (ExampleHeuristics.Satellite.compile (ground d p rel)).images.map
      (imageOf (ground d p rel)) := hg
  obtain ⟨x, hx, hval⟩ := Array.mem_map.mp hg'
  obtain ⟨z, hz, hzval⟩ := Array.mem_filterMap.mp
    (hx : x ∈ (ExampleHeuristics.Satellite.compile (ground d p rel)).images)
  obtain ⟨-, hlt, hzget⟩ := Array.mem_zipIdx hz
  have hi : z.2 < (ground d p rel).goalAtoms.size := by simpa using hlt
  have hzget' : z.1 = (ground d p rel).goalAtoms[z.2] := by simpa using hzget
  unfold ExampleHeuristics.Satellite.imageEntry at hzval
  by_cases hpred : (z.1.pred == "have_image") = true
  · rcases hargs : z.1.args with _ | ⟨dn, rest⟩
    · simp only [hpred, hargs] at hzval; simp at hzval
    · cases rest with
      | nil => simp only [hpred, hargs] at hzval; simp at hzval
      | cons mn rest' =>
          cases rest' with
          | cons _ _ => simp only [hpred, hargs] at hzval; simp at hzval
          | nil =>
              simp only [hpred, hargs] at hzval
              rcases hd : (ground d p rel).objectsOfTypes ["direction"] |>.findIdx?
                  (· == dn) with _ | di
              · rw [hd] at hzval; simp at hzval
              · rcases hm : (ground d p rel).objectsOfTypes ["mode"] |>.findIdx?
                    (· == mn) with _ | mi
                · rw [hd, hm] at hzval; simp at hzval
                · rw [hd, hm] at hzval
                  simp only [Option.some.injEq] at hzval
                  subst x
                  subst g
                  refine ⟨dn, mn, ?_, hd, hm⟩
                  have hzatom : z.1 = haveImage dn mn := by
                    cases hza : z.1 with
                    | mk pred args =>
                        congr
                        · simpa [hza] using hpred
                        · simpa [hza] using hargs
                  change (ground d p rel).factNames.getD
                    ((ground d p rel).goal.getD z.2 0) default = haveImage dn mn
                  rw [(goal_name_eq d p rel hi).1, ← hzget', hzatom]
  · simp only [Bool.not_eq_true] at hpred
    simp only [hpred] at hzval
    simp at hzval

/-- Every pointing-table entry names a `pointing` atom. -/
theorem pointing_goal_pred (rel : Bool) :
    ∀ g ∈ (cfgOf (ground d p rel)).pointingGoals, g.goalAtom.pred = "pointing" := by
  intro g hg
  have hg' : g ∈ (ExampleHeuristics.Satellite.compile (ground d p rel)).pointingGoals.map
      (pointingOf (ground d p rel)) := hg
  obtain ⟨x, hx, hval⟩ := Array.mem_map.mp hg'
  obtain ⟨z, hz, hzval⟩ := Array.mem_filterMap.mp
    (hx : x ∈ (ExampleHeuristics.Satellite.compile (ground d p rel)).pointingGoals)
  obtain ⟨-, hlt, hzget⟩ := Array.mem_zipIdx hz
  have hi : z.2 < (ground d p rel).goalAtoms.size := by simpa using hlt
  have hzget' : z.1 = (ground d p rel).goalAtoms[z.2] := by simpa using hzget
  unfold ExampleHeuristics.Satellite.pointingEntry at hzval
  by_cases hpred : (z.1.pred == "pointing") = true
  · rcases hargs : z.1.args with _ | ⟨sn, rest⟩
    · simp only [hpred, hargs] at hzval; simp at hzval
    · cases rest with
      | nil => simp only [hpred, hargs] at hzval; simp at hzval
      | cons dn rest' =>
          cases rest' with
          | cons _ _ => simp only [hpred, hargs] at hzval; simp at hzval
          | nil =>
              simp only [hpred, hargs] at hzval
              rcases hs : (ground d p rel).objectsOfTypes ["satellite"] |>.findIdx?
                  (· == sn) with _ | si
              · rw [hs] at hzval; simp at hzval
              · rcases hd : (ground d p rel).objectsOfTypes ["direction"] |>.findIdx?
                    (· == dn) with _ | di
                · rw [hs, hd] at hzval; simp at hzval
                · rw [hs, hd] at hzval
                  simp only [Option.some.injEq] at hzval
                  subst x
                  subst g
                  show (atomOf (ground d p rel)
                    ((ground d p rel).goal.getD z.2 0)).pred = "pointing"
                  change ((ground d p rel).factNames.getD
                    ((ground d p rel).goal.getD z.2 0) default).pred = "pointing"
                  rw [(goal_name_eq d p rel hi).1]
                  rw [← hzget']
                  simpa using hpred
  · simp only [Bool.not_eq_true] at hpred
    simp only [hpred] at hzval
    simp at hzval

/-- A pointing-table entry carries the indices of the satellite and direction
named by its goal atom. -/
theorem pointing_goal_data (rel : Bool) :
    ∀ g ∈ (cfgOf (ground d p rel)).pointingGoals, ∃ sn dn,
      g.goalAtom = pointing sn dn ∧
      ((ground d p rel).objectsOfTypes ["satellite"]).findIdx? (· == sn) = some g.sat ∧
      ((ground d p rel).objectsOfTypes ["direction"]).findIdx? (· == dn) = some g.dir := by
  intro g hg
  have hg' : g ∈ (ExampleHeuristics.Satellite.compile (ground d p rel)).pointingGoals.map
      (pointingOf (ground d p rel)) := hg
  obtain ⟨x, hx, hval⟩ := Array.mem_map.mp hg'
  obtain ⟨z, hz, hzval⟩ := Array.mem_filterMap.mp
    (hx : x ∈ (ExampleHeuristics.Satellite.compile (ground d p rel)).pointingGoals)
  obtain ⟨-, hlt, hzget⟩ := Array.mem_zipIdx hz
  have hi : z.2 < (ground d p rel).goalAtoms.size := by simpa using hlt
  have hzget' : z.1 = (ground d p rel).goalAtoms[z.2] := by simpa using hzget
  unfold ExampleHeuristics.Satellite.pointingEntry at hzval
  by_cases hpred : (z.1.pred == "pointing") = true
  · rcases hargs : z.1.args with _ | ⟨sn, rest⟩
    · simp only [hpred, hargs] at hzval; simp at hzval
    · cases rest with
      | nil => simp only [hpred, hargs] at hzval; simp at hzval
      | cons dn rest' =>
          cases rest' with
          | cons _ _ => simp only [hpred, hargs] at hzval; simp at hzval
          | nil =>
              simp only [hpred, hargs] at hzval
              rcases hs : (ground d p rel).objectsOfTypes ["satellite"] |>.findIdx?
                  (· == sn) with _ | si
              · rw [hs] at hzval; simp at hzval
              · rcases hd : (ground d p rel).objectsOfTypes ["direction"] |>.findIdx?
                    (· == dn) with _ | di
                · rw [hs, hd] at hzval; simp at hzval
                · rw [hs, hd] at hzval
                  simp only [Option.some.injEq] at hzval
                  subst x
                  subst g
                  refine ⟨sn, dn, ?_, hs, hd⟩
                  have hzatom : z.1 = pointing sn dn := by
                    cases hza : z.1 with
                    | mk pred args =>
                        congr
                        · simpa [hza] using hpred
                        · simpa [hza] using hargs
                  change (ground d p rel).factNames.getD
                    ((ground d p rel).goal.getD z.2 0) default = pointing sn dn
                  rw [(goal_name_eq d p rel hi).1, ← hzget', hzatom]
  · simp only [Bool.not_eq_true] at hpred
    simp only [hpred] at hzval
    simp at hzval

/-- The goal table cannot contain two different entries naming the same
pointing atom: the atom fixes both stored indices. -/
theorem pointing_goalAtom_inj (rel : Bool) {g q : PointingGoal}
    (hg : g ∈ (cfgOf (ground d p rel)).pointingGoals)
    (hq : q ∈ (cfgOf (ground d p rel)).pointingGoals)
    (heq : g.goalAtom = q.goalAtom) : g = q := by
  obtain ⟨sg, dg, hga, hsg, hdg⟩ := pointing_goal_data (d := d) (p := p) rel g hg
  obtain ⟨sq, dq, hqa, hsq, hdq⟩ := pointing_goal_data (d := d) (p := p) rel q hq
  have hnames : sg = sq ∧ dg = dq := by
    rw [hga, hqa] at heq
    simpa [pointing] using heq
  obtain ⟨rfl, rfl⟩ := hnames
  have hsat : g.sat = q.sat := by rw [hsg] at hsq; simpa using hsq
  have hdir : g.dir = q.dir := by rw [hdg] at hdq; simpa using hdq
  cases g
  cases q
  simp_all

/-! ### `turn_to` frames the non-turn terms -/

/-- The three parameters of a turn have indices in the same satellite and
direction tables used by the heuristic. -/
theorem turn_arg_indices (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (hf : OpFacts d p o) {s dn dp : Name}
    (hs : hf.inst.schema = turnA) (hargs : hf.inst.args = [s, dn, dp]) :
    ∃ si dni dpi,
      ((ground d p rel).objectsOfTypes ["satellite"]).findIdx? (· == s) = some si ∧
      ((ground d p rel).objectsOfTypes ["direction"]).findIdx? (· == dn) = some dni ∧
      ((ground d p rel).objectsOfTypes ["direction"]).findIdx? (· == dp) = some dpi := by
  obtain ⟨a1, a2, a3, ha, hw1, hw2, hw3⟩ :=
    hf.inst.args_three (show hf.inst.schema.params =
      [satP "?s", dirP "?d_new", dirP "?d_prev"] by rw [hs])
  rw [hargs] at ha
  obtain ⟨rfl, rfl, rfl⟩ : s = a1 ∧ dn = a2 ∧ dp = a3 := by simpa using ha
  obtain ⟨si, hsi⟩ := findIdx_total (mem_satellites hp rel hw1)
  obtain ⟨dni, hdni⟩ := findIdx_total (mem_directions hp rel hw2)
  obtain ⟨dpi, hdpi⟩ := findIdx_total (mem_directions hp rel hw3)
  exact ⟨si, dni, dpi, hsi, hdni, hdpi⟩

private theorem not_mem_turn_atoms {a : GroundAtom} {l : List GroundAtom}
    (hp : a.pred ≠ "pointing") (hn : a.pred ≠ "not-pointing")
    (hl : ∀ b ∈ l, b.pred = "pointing" ∨ b.pred = "not-pointing") : a ∉ l := by
  intro ha
  rcases hl a ha with h | h
  · exact hp h
  · exact hn h

theorem turn_instruments (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (hf : OpFacts d p o) {s dn dp : Name}
    (hs : hf.inst.schema = turnA) (hargs : hf.inst.args = [s, dn, dp])
    (σ : AtomState) :
    instruments (cfgOf (ground d p rel)) (o.applyA σ) =
      instruments (cfgOf (ground d p rel)) σ := by
  obtain ⟨-, hadd, hdel⟩ := turn_atoms hf.inst hs hargs
  refine instruments_congr _ σ (o.applyA σ) ?_ ?_ ?_ ?_
  · intro g hg
    have hpred := image_goal_pred (d := d) (p := p) rel g hg
    exact frame_of_lists hf hadd hdel
      (not_mem_turn_atoms (by rw [hpred]; decide) (by rw [hpred]; decide)
        (by intro b hb; simp at hb
            rcases hb with rfl | rfl <;> simp [pointing, notPointing]))
      (not_mem_turn_atoms (by rw [hpred]; decide) (by rw [hpred]; decide)
        (by intro b hb; simp at hb
            rcases hb with rfl | rfl <;> simp [pointing, notPointing])) σ

  · intro a ha
    have hpred := calibrated_pred ha
    exact frame_of_lists hf hadd hdel
      (not_mem_turn_atoms (by rw [hpred]; decide) (by rw [hpred]; decide)
        (by intro b hb; simp at hb
            rcases hb with rfl | rfl <;> simp [pointing, notPointing]))
      (not_mem_turn_atoms (by rw [hpred]; decide) (by rw [hpred]; decide)
        (by intro b hb; simp at hb
            rcases hb with rfl | rfl <;> simp [pointing, notPointing])) σ
  · intro a ha
    have hpred := powerOn_pred ha
    exact frame_of_lists hf hadd hdel
      (not_mem_turn_atoms (by rw [hpred]; decide) (by rw [hpred]; decide)
        (by intro b hb; simp at hb
            rcases hb with rfl | rfl <;> simp [pointing, notPointing]))
      (not_mem_turn_atoms (by rw [hpred]; decide) (by rw [hpred]; decide)
        (by intro b hb; simp at hb
            rcases hb with rfl | rfl <;> simp [pointing, notPointing])) σ
  · intro a ha
    have hpred := powerAvail_pred ha
    exact frame_of_lists hf hadd hdel
      (not_mem_turn_atoms (by rw [hpred]; decide) (by rw [hpred]; decide)
        (by intro b hb; simp at hb
            rcases hb with rfl | rfl <;> simp [pointing, notPointing]))
      (not_mem_turn_atoms (by rw [hpred]; decide) (by rw [hpred]; decide)
        (by intro b hb; simp at hb
            rcases hb with rfl | rfl <;> simp [pointing, notPointing])) σ

/-- A turn leaves the ready-instrument set unchanged. -/
theorem turn_readyNow (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (hf : OpFacts d p o) {s dn dp : Name}
    (hs : hf.inst.schema = turnA) (hargs : hf.inst.args = [s, dn, dp])
    (σ : AtomState) :
    readyNow (cfgOf (ground d p rel)) (o.applyA σ) =
      readyNow (cfgOf (ground d p rel)) σ := by
  obtain ⟨-, hadd, hdel⟩ := turn_atoms hf.inst hs hargs
  refine readyNow_congr _ σ (o.applyA σ) ?_ ?_
  · intro a ha
    have hpred := calibrated_pred ha
    exact frame_of_lists hf hadd hdel
      (not_mem_turn_atoms (by rw [hpred]; decide) (by rw [hpred]; decide)
        (by intro b hb; simp at hb
            rcases hb with rfl | rfl <;> simp [pointing, notPointing]))
      (not_mem_turn_atoms (by rw [hpred]; decide) (by rw [hpred]; decide)
        (by intro b hb; simp at hb
            rcases hb with rfl | rfl <;> simp [pointing, notPointing])) σ
  · intro a ha
    have hpred := powerOn_pred ha
    exact frame_of_lists hf hadd hdel
      (not_mem_turn_atoms (by rw [hpred]; decide) (by rw [hpred]; decide)
        (by intro b hb; simp at hb
            rcases hb with rfl | rfl <;> simp [pointing, notPointing]))
      (not_mem_turn_atoms (by rw [hpred]; decide) (by rw [hpred]; decide)
        (by intro b hb; simp at hb
            rcases hb with rfl | rfl <;> simp [pointing, notPointing])) σ

theorem turn_frame_images (rel : Bool) {o : AtomOp} (hf : OpFacts d p o)
    {s dn dp : Name} (hs : hf.inst.schema = turnA)
    (hargs : hf.inst.args = [s, dn, dp]) (σ : AtomState) :
    ∀ g ∈ (cfgOf (ground d p rel)).images,
      o.applyA σ g.goalAtom = σ g.goalAtom := by
  obtain ⟨-, hadd, hdel⟩ := turn_atoms hf.inst hs hargs
  intro g hg
  have hpred := image_goal_pred (d := d) (p := p) rel g hg
  exact frame_of_lists hf hadd hdel
    (not_mem_turn_atoms (by rw [hpred]; decide) (by rw [hpred]; decide)
      (by intro b hb; simp at hb
          rcases hb with rfl | rfl <;> simp [pointing, notPointing]))
    (not_mem_turn_atoms (by rw [hpred]; decide) (by rw [hpred]; decide)
      (by intro b hb; simp at hb
          rcases hb with rfl | rfl <;> simp [pointing, notPointing])) σ

/-- A turn changes no pointing goal except, possibly, the goal at its old or
new direction.  This is the pointwise transition fact used by the joint turn
bound. -/
theorem turn_frame_pointing_other (rel : Bool) {o : AtomOp} (hf : OpFacts d p o)
    {s dn dp : Name} (hs : hf.inst.schema = turnA)
    (hargs : hf.inst.args = [s, dn, dp]) (σ : AtomState) :
    ∀ g ∈ (cfgOf (ground d p rel)).pointingGoals,
      g.goalAtom ≠ pointing s dn → g.goalAtom ≠ pointing s dp →
      o.applyA σ g.goalAtom = σ g.goalAtom := by
  obtain ⟨-, hadd, hdel⟩ := turn_atoms hf.inst hs hargs
  intro g hg hn hp
  have hpred := pointing_goal_pred (d := d) (p := p) rel g hg
  have hnotOld : g.goalAtom ≠ notPointing s dp := by
    intro heq
    have : g.goalAtom.pred = "not-pointing" := by rw [heq]
    rw [hpred] at this
    contradiction
  have hnotNew : g.goalAtom ≠ notPointing s dn := by
    intro heq
    have : g.goalAtom.pred = "not-pointing" := by rw [heq]
    rw [hpred] at this
    contradiction
  exact frame_of_lists hf hadd hdel
    (by simp [hn, hnotOld]) (by simp [hnotNew, hp]) σ

/-- The old pointing atom is a dynamic precondition and a retained delete, so
it is false after a turn even when relevance pruning is enabled. -/
theorem turn_old_false (hp : Pinned d p) {o : AtomOp} (hf : OpFacts d p o)
    {s dn dp : Name} (hs : hf.inst.schema = turnA)
    (hargs : hf.inst.args = [s, dn, dp]) (hne : dn ≠ dp) (σ : AtomState) :
    o.applyA σ (pointing s dp) = false := by
  obtain ⟨hpre, hadd, hdel⟩ := turn_atoms hf.inst hs hargs
  exact falsified_of_lists hf hadd hdel
    (by simp [pointing, notPointing, Ne.symm hne]) (by simp) hpre
    (by simpa [pointing] using pointing_dynamic hp.domain) σ

/-- Whenever relevance pruning retained the new pointing atom, the transition
sets it.  The separate grounding lemma will discharge the membership premise. -/
theorem turn_new_true {o : AtomOp} {s dn : Name} {σ : AtomState}
    (hadd : pointing s dn ∈ o.add) : o.applyA σ (pointing s dn) = true :=
  applyA_add σ hadd

/-- A turn cannot meet a pointing goal other than the one at its new
direction.  This direction of the transition is independent of whether the
new add survived relevance pruning. -/
theorem turn_preserves_unmet_other (rel : Bool) {o : AtomOp} (hf : OpFacts d p o)
    {s dn dp : Name} (hs : hf.inst.schema = turnA)
    (hargs : hf.inst.args = [s, dn, dp]) {σ : AtomState}
    {g : PointingGoal} (hg : g ∈ (cfgOf (ground d p rel)).pointingGoals)
    (hne : g.goalAtom ≠ pointing s dn) (hunmet : σ g.goalAtom = false) :
    o.applyA σ g.goalAtom = false := by
  obtain ⟨-, hadd, -⟩ := turn_atoms hf.inst hs hargs
  have hpred := pointing_goal_pred (d := d) (p := p) rel g hg
  have hnotOld : g.goalAtom ≠ notPointing s dp := by
    intro heq
    have : g.goalAtom.pred = "not-pointing" := by rw [heq]
    rw [hpred] at this
    contradiction
  have hnot : g.goalAtom ∉ [pointing s dn, notPointing s dp] := by
    simp [hne, hnotOld]
  cases ht : o.applyA σ g.goalAtom with
  | false => rfl
  | true =>
      have hbefore := falls_of_lists hf hadd hnot ht
      rw [hunmet] at hbefore
      contradiction

/-- A single `turn_to` can meet at most the unique goal at its new direction.
Goals invalidated at the old direction only increase the unmet count. -/
theorem turn_unmetPointing_bound (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (hf : OpFacts d p o) {s dn dp : Name}
    (hs : hf.inst.schema = turnA) (hargs : hf.inst.args = [s, dn, dp])
    (σ : AtomState) :
    (unmetPointing (cfgOf (ground d p rel)) σ).size ≤
      (unmetPointing (cfgOf (ground d p rel)) (o.applyA σ)).size + 1 := by
  let c := cfgOf (ground d p rel)
  by_cases hex : ∃ q ∈ c.pointingGoals, q.goalAtom = pointing s dn
  · obtain ⟨q, hq, hqa⟩ := hex
    refine unmetPointing_le_succ_mono c σ (o.applyA σ) q
      (pointing_nodup hp rel) ?_
    intro g hg hne hunmet
    apply turn_preserves_unmet_other rel hf hs hargs hg ?_ hunmet
    intro heq
    exact hne (pointing_goalAtom_inj rel hg hq (heq.trans hqa.symm))
  · have hm : (unmetPointing c σ).size ≤
        (unmetPointing c (o.applyA σ)).size := by
      refine unmetPointing_le_mono c σ (o.applyA σ) ?_
      intro g hg hunmet
      apply turn_preserves_unmet_other rel hf hs hargs hg ?_ hunmet
      intro heq
      exact hex ⟨g, hg, heq⟩
    change (unmetPointing c σ).size ≤
      (unmetPointing c (o.applyA σ)).size + 1
    omega

/-- A direction paid for after a turn was already paid for before, except for
the old direction: deleting its pointing atom may make its goal unmet. -/
theorem turn_paidByGoal_of (rel : Bool) {o : AtomOp} (hf : OpFacts d p o)
    {s dn dp : Name} (hs : hf.inst.schema = turnA)
    (hargs : hf.inst.args = [s, dn, dp]) {σ : AtomState} {dpi x : Nat}
    (hdpi : ((ground d p rel).objectsOfTypes ["direction"]).findIdx? (· == dp) = some dpi)
    (hx : paidByGoal (cfgOf (ground d p rel)) (o.applyA σ) x = true) :
    paidByGoal (cfgOf (ground d p rel)) σ x = true ∨ x = dpi := by
  let c := cfgOf (ground d p rel)
  obtain ⟨-, -, hdel⟩ := turn_atoms hf.inst hs hargs
  change paidByGoal c (o.applyA σ) x = true at hx
  change paidByGoal c σ x = true ∨ x = dpi
  simp only [paidByGoal, Array.any_eq_true] at hx ⊢
  obtain ⟨i, hi, hix⟩ := hx
  let g := (unmetPointing c (o.applyA σ))[i]
  have hgu : g ∈ unmetPointing c (o.applyA σ) := Array.getElem_mem hi
  have hg : g ∈ c.pointingGoals := (Array.mem_filter.mp hgu).1
  have hgfalse : o.applyA σ g.goalAtom = false := by
    have := (Array.mem_filter.mp hgu).2
    simpa using this
  have hgdir : g.dir = x := by
    change (g.dir == x) = true at hix
    simpa using hix
  by_cases hold : g.goalAtom = pointing s dp
  · right
    obtain ⟨sg, dg, hga, -, hdg⟩ := pointing_goal_data (d := d) (p := p) rel g hg
    have hdname : dg = dp := by
      rw [hga] at hold
      have hnames : sg = s ∧ dg = dp := by simpa [pointing] using hold
      exact hnames.2
    subst hdname
    rw [hdg] at hdpi
    have : g.dir = dpi := by simpa using hdpi
    omega
  · left
    have hpred := pointing_goal_pred (d := d) (p := p) rel g hg
    have hnotNP : g.goalAtom ≠ notPointing s dn := by
      intro heq
      have : g.goalAtom.pred = "not-pointing" := by rw [heq]
      rw [hpred] at this
      contradiction
    have hbefore : σ g.goalAtom = false :=
      persists_false_of_lists hf hdel (by simp [hnotNP, hold]) hgfalse
    have hgb : g ∈ unmetPointing c σ :=
      Array.mem_filter.mpr ⟨hg, by simp [hbefore]⟩
    obtain ⟨j, hj, hget⟩ := Array.getElem_of_mem hgb
    refine ⟨j, hj, ?_⟩
    rw [hget, hgdir]
    simp

/-- Away from the new direction a turn cannot create coverage: the ready set
is framed, and the only pointing atom it may add is indexed by that direction. -/
theorem turn_covered_of (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (hf : OpFacts d p o) {s dn dp : Name}
    (hs : hf.inst.schema = turnA) (hargs : hf.inst.args = [s, dn, dp])
    {σ : AtomState} {dni x m : Nat}
    (hdni : ((ground d p rel).objectsOfTypes ["direction"]).findIdx? (· == dn) = some dni)
    (hne : x ≠ dni) (hcov : covered (cfgOf (ground d p rel)) (o.applyA σ) x m = true) :
    covered (cfgOf (ground d p rel)) σ x m = true := by
  let c := cfgOf (ground d p rel)
  obtain ⟨-, hadd, -⟩ := turn_atoms hf.inst hs hargs
  refine covered_mono c σ (o.applyA σ) ?_ ?_ hcov
  · intro q hq htrue
    obtain ⟨sn, qd, hqa, -, hqd⟩ := pointingByDir_data (objs_nodup hp rel "direction") hq
    have hnot : q.1 ∉ [pointing s dn, notPointing s dp] := by
      have hpred : q.1.pred = "pointing" := by rw [hqa]
      have hnp : q.1 ≠ notPointing s dp := by
        intro heq
        have : q.1.pred = "not-pointing" := by rw [heq]
        rw [hpred] at this
        contradiction
      have hn : q.1 ≠ pointing s dn := by
        intro heq
        rw [hqa] at heq
        have hnames : sn = s ∧ qd = dn := by simpa [pointing] using heq
        have hqd' : ((ground d p rel).objectsOfTypes ["direction"]).findIdx? (· == qd)
            = some x := hqd
        rw [hnames.2, hdni] at hqd'
        have : x = dni := by simpa using hqd'.symm
        exact hne this
      simp [hn, hnp]
    exact falls_of_lists hf hadd hnot htrue
  · intro i hi
    have hready := turn_readyNow hp rel hf hs hargs σ
    change readyNow c (o.applyA σ) = readyNow c σ at hready
    rw [hready] at hi
    exact hi

/-- Consequently the outstanding-direction list can lose only the new and old
directions.  This is the coarse two-slot bound; the final joint proof pairs the
old slot with the pointing goal made unmet there. -/
theorem turn_dirsToTurn_le_two (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (hf : OpFacts d p o) {s dn dp : Name}
    (hs : hf.inst.schema = turnA) (hargs : hf.inst.args = [s, dn, dp])
    (σ : AtomState) :
    (dirsToTurn (cfgOf (ground d p rel)) σ).length ≤
      (dirsToTurn (cfgOf (ground d p rel)) (o.applyA σ)).length + 2 := by
  obtain ⟨-, dni, dpi, -, hdni, hdpi⟩ := turn_arg_indices hp rel hf hs hargs
  let c := cfgOf (ground d p rel)
  refine dirsToTurn_le_two c σ (o.applyA σ) dni dpi
    (mem_dirsList_of_two c σ (o.applyA σ) dni dpi ?_ ?_ ?_)
  · exact turn_frame_images rel hf hs hargs σ
  · intro x hx
    exact turn_paidByGoal_of rel hf hs hargs hdpi hx
  · intro x m hne hx
    exact turn_covered_of hp rel hf hs hargs hdni hne hx

/-- Once the joint turn inequality is established, all remaining fields of the
`turn_to` schema case follow from its literal add/delete lists. -/
theorem turn_step_of_bound (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (hf : OpFacts d p o) {s dn dp : Name}
    (hs : hf.inst.schema = turnA) (hargs : hf.inst.args = [s, dn, dp])
    (σ : AtomState)
    (hbound : turns (cfgOf (ground d p rel)) σ ≤
      turns (cfgOf (ground d p rel)) (o.applyA σ) + 1) :
    SchemaStep (cfgOf (ground d p rel)) σ (o.applyA σ) :=
  .turn
    { frameImages := turn_frame_images rel hf hs hargs σ
      instrumentsSame := turn_instruments hp rel hf hs hargs σ
      turnBound := hbound }

/-! ### Costs -/

/-- Every grounded operator has the unit cost of its Satellite schema. -/
theorem cost_pos (hp : Pinned d p) (rel : Bool) :
    ∀ o ∈ groundedOps d p rel, 0 < o.cost := by
  intro o ho
  obtain ⟨hf⟩ := opFacts_ground d p rel ho
  rw [hf.cost]
  show 0 < hf.inst.schema.cost
  rcases instance_shape hp.domain hf.inst with
    ⟨s, dn, dp, hs, ha⟩ |
      ⟨ins, s, hs, ha⟩ |
      ⟨ins, s, hs, ha⟩ |
      ⟨s, ins, dir, hs, ha⟩ |
      ⟨s, dir, ins, m, hs, ha⟩ <;>
    rw [hs] <;> decide

end Planner.Lifted.Satellite

/- -------------------------------------------------------------------------- -/
/-
Everything the value reads, framed by the predicates an operator touches.

The value reads six things off a state: the two goal tables, the three
instrument tables, and the `pointing` atoms indexed by direction.  Each is a
family of atoms of one predicate, so an operator whose adds and deletes avoid
that predicate leaves the whole family alone.  Every schema case starts from
these six.
-/

namespace Planner.Lifted.Satellite

open Planner Planner.Pddl

variable {d : Domain} {p : Problem}

section Frames

variable {o : AtomOp} {add del : List GroundAtom}

theorem frame_ptGoals (rel : Bool) (hf : OpFacts d p o)
    (hadd : hf.inst.add = add) (hdel : hf.inst.del = del)
    (hpreds : ∀ b ∈ add ++ del, b.pred ≠ "pointing") (σ : AtomState) :
    ∀ g ∈ (cfgOf (ground d p rel)).pointingGoals,
      o.applyA σ g.goalAtom = σ g.goalAtom := fun g hg =>
  frame_pred hf hadd hdel
    (fun b hb => by rw [pointing_goal_pred rel g hg]; exact hpreds b hb) σ

theorem frame_imgGoals (rel : Bool) (hf : OpFacts d p o)
    (hadd : hf.inst.add = add) (hdel : hf.inst.del = del)
    (hpreds : ∀ b ∈ add ++ del, b.pred ≠ "have_image") (σ : AtomState) :
    ∀ g ∈ (cfgOf (ground d p rel)).images,
      o.applyA σ g.goalAtom = σ g.goalAtom := fun g hg =>
  frame_pred hf hadd hdel
    (fun b hb => by rw [image_goal_pred rel g hg]; exact hpreds b hb) σ

theorem frame_calib (rel : Bool) (hf : OpFacts d p o)
    (hadd : hf.inst.add = add) (hdel : hf.inst.del = del)
    (hpreds : ∀ b ∈ add ++ del, b.pred ≠ "calibrated") (σ : AtomState) :
    ∀ a, some a ∈ (cfgOf (ground d p rel)).calibratedAtoms →
      o.applyA σ a = σ a := fun a ha =>
  frame_pred hf hadd hdel (fun b hb => by rw [calibrated_pred ha]; exact hpreds b hb) σ

theorem frame_power (rel : Bool) (hf : OpFacts d p o)
    (hadd : hf.inst.add = add) (hdel : hf.inst.del = del)
    (hpreds : ∀ b ∈ add ++ del, b.pred ≠ "power_on") (σ : AtomState) :
    ∀ a, some a ∈ (cfgOf (ground d p rel)).powerOnAtoms →
      o.applyA σ a = σ a := fun a ha =>
  frame_pred hf hadd hdel (fun b hb => by rw [powerOn_pred ha]; exact hpreds b hb) σ

theorem frame_avail (rel : Bool) (hf : OpFacts d p o)
    (hadd : hf.inst.add = add) (hdel : hf.inst.del = del)
    (hpreds : ∀ b ∈ add ++ del, b.pred ≠ "power_avail") (σ : AtomState) :
    ∀ a, some a ∈ (cfgOf (ground d p rel)).powerAvailAtoms →
      o.applyA σ a = σ a := fun a ha =>
  frame_pred hf hadd hdel (fun b hb => by rw [powerAvail_pred ha]; exact hpreds b hb) σ

theorem frame_points (hp : Pinned d p) (rel : Bool) (hf : OpFacts d p o)
    (hadd : hf.inst.add = add) (hdel : hf.inst.del = del)
    (hpreds : ∀ b ∈ add ++ del, b.pred ≠ "pointing") (σ : AtomState) :
    ∀ x, ∀ q ∈ (cfgOf (ground d p rel)).pointingByDir.getD x #[],
      o.applyA σ q.1 = σ q.1 := by
  intro x q hq
  obtain ⟨sn, dn, hqa, -, -⟩ := pointingByDir_data (objs_nodup hp rel "direction") hq
  exact frame_pred hf hadd hdel
    (fun b hb => by rw [show q.1.pred = "pointing" from by rw [hqa]]; exact hpreds b hb) σ

end Frames

/-! ### The instrument sets under a single changed entry -/

/-- An instrument active afterwards was active before, unless it is the one the
action names. -/
theorem active_sub {atoms : Array (Option GroundAtom)} {σ τ : AtomState} {k : Nat}
    (h : ∀ j, j ≠ k → ∀ hj : j < atoms.size, ∀ a, atoms[j] = some a → τ a = true →
      σ a = true)
    {j : Nat} (hj : j ∈ activeInstruments atoms τ) :
    j = k ∨ j ∈ activeInstruments atoms σ := by
  by_cases hjk : j = k
  · exact Or.inl hjk
  · obtain ⟨hlt, a, hget, hσ⟩ := mem_activeInstruments.mp hj
    exact Or.inr (mem_activeInstruments.mpr ⟨hlt, a, hget, h j hjk hlt a hget hσ⟩)

/-- And an instrument active before is active afterwards when its atom is kept. -/
theorem active_mono {atoms : Array (Option GroundAtom)} {σ τ : AtomState}
    (h : ∀ j, ∀ hj : j < atoms.size, ∀ a, atoms[j] = some a → σ a = true → τ a = true)
    {j : Nat} (hj : j ∈ activeInstruments atoms σ) : j ∈ activeInstruments atoms τ := by
  obtain ⟨hlt, a, hget, hσ⟩ := mem_activeInstruments.mp hj
  exact mem_activeInstruments.mpr ⟨hlt, a, hget, h j hlt a hget hσ⟩

/-- The atom a slot of the calibration table holds names the instrument at that
position. -/
theorem calibrated_at {t : Task} (hnd : (insA t).toList.Nodup) {j : Nat}
    (hj : j < (insA t).size) {a : GroundAtom}
    (h : (cfgOf t).calibratedAtoms[j]? = some (some a)) : a = calibrated (insA t)[j] :=
  calibrated_slot (findIdx_getElem hnd hj)
    (by rw [Array.getD_eq_getD_getElem?, h]; rfl)

theorem powerOn_at {t : Task} (hnd : (insA t).toList.Nodup) {j : Nat}
    (hj : j < (insA t).size) {a : GroundAtom}
    (h : (cfgOf t).powerOnAtoms[j]? = some (some a)) : a = powerOn (insA t)[j] :=
  powerOn_slot (findIdx_getElem hnd hj)
    (by rw [Array.getD_eq_getD_getElem?, h]; rfl)

/-- Distinct positions name distinct instruments. -/
theorem ins_ne_of_index {t : Task} (hnd : (insA t).toList.Nodup) {ins : Name} {i j : Nat}
    (hi : insIx t ins = some i) (hj : j < (insA t).size) (hne : j ≠ i) :
    (insA t)[j] ≠ ins := by
  intro hc
  have hi' : (insA t).findIdx? (· == ins) = some i := hi
  have hget := findIdx_getElem hnd hj
  rw [hc, hi'] at hget
  exact hne (by simpa using hget.symm)

/-! ### Building the value's `any`s from a witness -/

theorem mem_zipIdx_self {α : Type} (xs : Array α) {j : Nat} (hj : j < xs.size) :
    (xs[j], j) ∈ xs.zipIdx := by
  rw [Array.mem_zipIdx_iff_getElem?]
  simp [Array.getElem?_eq_getElem hj]

theorem getD_eq_getElem {α : Type} (xs : Array α) (dflt : α) {j : Nat} (hj : j < xs.size) :
    xs.getD j dflt = xs[j] := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]; rfl

theorem array_any_elim {α : Type} {xs : Array α} {P : α → Bool} (h : xs.any P = true) :
    ∃ x ∈ xs, P x = true := by
  rw [← Array.any_toList, List.any_eq_true] at h
  obtain ⟨x, hx, hpx⟩ := h
  exact ⟨x, by simpa using hx, hpx⟩

theorem array_any_false {α : Type} {xs : Array α} {P : α → Bool} (h : xs.any P = false)
    {x : α} (hx : x ∈ xs) : P x = false := by
  by_contra hc
  have hall : xs.any P = true := array_any_of_mem hx (by simpa using hc)
  rw [h] at hall
  exact Bool.noConfusion hall

/-- The indexed form of a hypothesis about every atom a table holds. -/
theorem active_of_mem_hyp {atoms : Array (Option GroundAtom)} {σ τ : AtomState}
    (h : ∀ a, some a ∈ atoms → σ a = true → τ a = true) :
    ∀ j, ∀ hj : j < atoms.size, ∀ a, atoms[j] = some a → σ a = true → τ a = true := by
  intro j hj a hget
  exact h a (by rw [← hget]; exact Array.getElem_mem hj)

/-! ### Deduplicated lists, strictly -/

/-- A list contained in another that misses one of its elements is strictly
shorter once deduplicated.  This is what pairs a direction that *enters* the
turn list against a term that fell. -/
theorem length_distinct_lt (l l' : List Nat) (hsub : ∀ x ∈ l, x ∈ l') {y : Nat}
    (hy : y ∈ l') (hny : y ∉ l) : (distinct l).length + 1 ≤ (distinct l').length := by
  have hnd : (distinct l).Nodup := distinct_nodup l
  have hsub' : ∀ x ∈ distinct l, x ∈ (distinct l').erase y := by
    intro x hx
    have hxl : x ∈ l := (mem_distinct l).mp hx
    have hxy : x ≠ y := fun hc => hny (hc ▸ hxl)
    exact (List.mem_erase_of_ne hxy).mpr ((mem_distinct l').mpr (hsub x hxl))
  have hlen := length_le_of_subset (distinct l) ((distinct l').erase y) hnd hsub'
  have hyd : y ∈ distinct l' := (mem_distinct l').mpr hy
  rw [List.length_erase_of_mem hyd] at hlen
  have hpos : 0 < (distinct l').length := List.length_pos_of_mem hyd
  omega

/-- The free-slot term is one action at most. -/
theorem freeSlot_le_one (c : Cfg) (σ : AtomState) : freeSlot c σ ≤ 1 := by
  unfold freeSlot; split <;> omega

/-! ### Coverage, read through the instruments that could provide it -/

/-- Coverage at one direction and mode is lost, not gained, when the pointing
atoms do not grow and no instrument *that supports that mode* becomes ready. -/
theorem covered_mono_supp (c : Cfg) (σ τ : AtomState) {x m : Nat}
    (hpoint : ∀ q ∈ c.pointingByDir.getD x #[], τ q.1 = true → σ q.1 = true)
    (hready : ∀ j, (c.supports.getD j #[]).contains m = true →
      (readyNow c τ).contains j = true → (readyNow c σ).contains j = true)
    (h : covered c τ x m = true) : covered c σ x m = true := by
  simp only [covered, Array.any_eq_true] at h ⊢
  obtain ⟨i, hi, hq⟩ := h
  refine ⟨i, hi, ?_⟩
  simp only [Bool.and_eq_true, Array.any_eq_true] at hq ⊢
  refine ⟨hpoint _ (Array.getElem_mem hi) hq.1, ?_⟩
  obtain ⟨j, hj, hcond⟩ := hq.2
  refine ⟨j, hj, ?_⟩
  simp only [Bool.and_eq_true, Bool.or_eq_true] at hcond ⊢
  refine ⟨hcond.1, ?_⟩
  rcases hcond.2 with hr | ht
  · exact Or.inl (hready _ hcond.1 hr)
  · exact Or.inr ht

/-! ### The free power slot -/

/-- The `power_avail` half of the free-slot test, with the table lookups pulled
out so that the case split is on plain values. -/
def availCond (σ : AtomState) (A : Option GroundAtom) : Bool :=
  match A with
  | some a => σ a
  | none => true

def slotCond (c : Cfg) (σ : AtomState) (S : Option Nat) : Bool :=
  match S with
  | some sat => availCond σ (c.powerAvailAtoms.getD sat none)
  | none => true

theorem slotFree_eq (c : Cfg) (σ : AtomState) :
    slotFree c σ = c.supports.zipIdx.any fun x => x.1.any (neededModes c σ).contains &&
      slotCond c σ (c.satelliteOf.getD x.2 none) := rfl

theorem slotCond_mono (c : Cfg) (σ τ : AtomState)
    (havail : ∀ a, some a ∈ c.powerAvailAtoms → τ a = true → σ a = true)
    (S : Option Nat) (h : slotCond c τ S = true) : slotCond c σ S = true := by
  revert h
  cases S with
  | none => intro _; rfl
  | some sat =>
      show availCond τ (c.powerAvailAtoms.getD sat none) = true →
        availCond σ (c.powerAvailAtoms.getD sat none) = true
      rcases hA : c.powerAvailAtoms.getD sat none with _ | a
      · intro _; rfl
      · intro h
        exact havail a (mem_of_getD_some hA) h

/-- A satellite with a free slot for a needed mode keeps one when nothing gains
power. -/
theorem slotFree_mono (c : Cfg) (σ τ : AtomState)
    (hneeded : ∀ m ∈ neededModes c τ, m ∈ neededModes c σ)
    (havail : ∀ a, some a ∈ c.powerAvailAtoms → τ a = true → σ a = true)
    (h : slotFree c τ = true) : slotFree c σ = true := by
  rw [slotFree_eq] at h ⊢
  obtain ⟨y, hy, hcond⟩ := array_any_elim h
  refine array_any_of_mem hy ?_
  simp only [Bool.and_eq_true] at hcond ⊢
  refine ⟨?_, slotCond_mono c σ τ havail _ hcond.2⟩
  obtain ⟨m, hm, hmc⟩ := array_any_elim hcond.1
  exact array_any_of_mem hm (by simpa using hneeded m (by simpa using hmc))

end Planner.Lifted.Satellite

/- -------------------------------------------------------------------------- -/
/-
The delete that `switch_on` must keep.

`switch_on` powers an instrument *and* takes away its calibration.  The proof
needs the second: an instrument that came out of a `switch_on` both powered and
still calibrated would be newly ready, and the value would fall by two across one
action — one for the power cover count and one for the calibration cover count.

Grounding keeps that delete, because the schema does not add the atom back.  The
relevance analysis is the question.  It keeps a delete only of a *relevant* atom,
and `calibrated ?i` is relevant exactly when it matters: if the instrument
supports a mode some image goal asks for, then the `take_image` that would use it
is an operator of the task, it adds a goal atom, so the analysis keeps it, so —
the set being closed — everything it reads is relevant, `calibrated ?i` included.

The other direction is the cheap half: if the instrument supports no needed mode,
making it ready changes no count the value reads.
-/

namespace Planner.Lifted.Satellite

open Planner Planner.Pddl

variable {d : Domain} {p : Problem}

/-- The instrument supports a mode some `have_image` goal asks for. -/
def NeedsCalib (d : Domain) (p : Problem) (rel : Bool) (ins : Name) : Prop :=
  ∃ dn mn, haveImage dn mn ∈ p.goal ∧ supports ins mn ∈ p.init ∧
    dn ∈ dirsA (ground d p rel) ∧ mn ∈ modesA (ground d p rel)

/-- The `take_image` that would use the instrument is an operator of the task. -/
theorem raw_image (hp : Pinned d p) {ins s dn mn : Name}
    (hins : WellTyped d (allObjects d p) "instrument" ins)
    (hsat : WellTyped d (allObjects d p) "satellite" s)
    (hdir : WellTyped d (allObjects d p) "direction" dn)
    (hmode : WellTyped d (allObjects d p) "mode" mn)
    (hboard : onBoard ins s ∈ p.init) (hsupp : supports ins mn ∈ p.init) :
    mkOp imageA (imageA.pre.filter fun x => !(staticPredicates d).contains x.pred)
      #[s, dn, ins, mn] ∈ rawOps d p := by
  rw [← groundedOps_false]
  refine groundedOps_complete d p (a := imageA) (by rw [hp.domain]; simp) #[s, dn, ins, mn]
    rfl ?_ ?_ ?_
  · intro pm hpm
    simp only [imageA, List.mem_cons, List.not_mem_nil, or_false] at hpm
    rcases hpm with rfl | rfl | rfl | rfl
    · exact hp.satTypeName
    · exact hp.dirTypeName
    · exact hp.insTypeName
    · exact hp.modeTypeName
  · show List.Forall₂ _ imageA.params [s, dn, ins, mn]
    exact List.Forall₂.cons hsat (List.Forall₂.cons hdir (List.Forall₂.cons hins
      (List.Forall₂.cons hmode List.Forall₂.nil)))
  · intro y hy hst
    simp only [imageA, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · rw [show (calibratedV "?i").pred = (calibrated "").pred from rfl,
        show (calibrated "").pred = "calibrated" from rfl,
        calibrated_dynamic hp.domain] at hst
      exact absurd hst (by simp)
    · exact hboard
    · exact hsupp
    · rw [show (powerOnV "?i").pred = "power_on" from rfl,
        powerOn_dynamic hp.domain] at hst
      exact absurd hst (by simp)
    · rw [show (pointingV "?s" "?d").pred = "pointing" from rfl,
        pointing_dynamic hp.domain] at hst
      exact absurd hst (by simp)

/-- **Its `calibrated` precondition is relevant.** -/
theorem calibrated_relevant (hp : Pinned d p) (rel : Bool) {r : Std.HashSet GroundAtom}
    (hclosed : Closed (rawOps d p) r)
    (hgoal : ∀ a ∈ p.goal.toArray, r.contains a = true)
    {ins s : Name} (hboard : onBoard ins s ∈ p.init)
    (hins : WellTyped d (allObjects d p) "instrument" ins)
    (hsat : WellTyped d (allObjects d p) "satellite" s)
    (hneed : NeedsCalib d p rel ins) : r.contains (calibrated ins) = true := by
  obtain ⟨dn, mn, hgim, hsupp, hdmem, hmmem⟩ := hneed
  have hdir : WellTyped d (allObjects d p) "direction" dn := objsOf_wellTyped hdmem
  have hmode : WellTyped d (allObjects d p) "mode" mn := objsOf_wellTyped hmmem
  set dyn := imageA.pre.filter fun x => !(staticPredicates d).contains x.pred with hdyn
  set op := mkOp imageA dyn #[s, dn, ins, mn] with hop
  have hmem : op ∈ rawOps d p := raw_image hp hins hsat hdir hmode hboard hsupp
  -- it adds a goal atom, so the analysis keeps it
  have hadd : haveImage dn mn ∈ op.add := by
    have heq : instAtom imageA.params (#[s, dn, ins, mn] : Array Name).toList
        (haveImageV "?d" "?m") = haveImage dn mn := rfl
    rw [hop, ← heq]
    refine mem_mkOp_add imageA dyn _ (by simp [imageA]) ?_
    intro z hz
    have hz' : z ∈ imageA.pre := (List.mem_filter.mp (by rw [hdyn] at hz; exact hz)).1
    simp only [imageA, List.mem_cons, List.not_mem_nil, or_false] at hz'
    rcases hz' with rfl | rfl | rfl | rfl | rfl
    · show calibrated ins ≠ haveImage dn mn
      simp [calibrated, haveImage]
    · show onBoard ins s ≠ haveImage dn mn
      simp [onBoard, haveImage]
    · show supports ins mn ≠ haveImage dn mn
      simp [supports, haveImage]
    · show powerOn ins ≠ haveImage dn mn
      simp [powerOn, haveImage]
    · show pointing s dn ≠ haveImage dn mn
      simp [pointing, haveImage]
  have htouch : op.touches r = true := by
    unfold AtomOp.touches
    have hany : op.add.any r.contains = true :=
      array_any_of_mem hadd (hgoal _ (by simpa using hgim))
    rw [hany]; rfl
  -- and everything it reads is relevant
  refine hclosed op hmem htouch (calibrated ins) ?_
  have heq : instAtom imageA.params (#[s, dn, ins, mn] : Array Name).toList
      (calibratedV "?i") = calibrated ins := rfl
  rw [hop, ← heq]
  refine mem_mkOp_pre imageA dyn _ ?_
  rw [hdyn]
  refine List.mem_filter.mpr ⟨by simp [imageA], ?_⟩
  simp only [Bool.not_eq_true']
  exact calibrated_dynamic hp.domain

/-! ### The delete, on the raw operator and on the pruned one -/

/-- Grounding keeps it: the schema does not add the atom back. -/
theorem switchOn_del_raw {q : AtomOp} (hfd : OpFactsDel d p q) {ins s : Name}
    (hs : hfd.inst.schema = switchOnA) (ha : hfd.inst.args = [ins, s]) :
    calibrated ins ∈ q.del := by
  have hy : calibratedV "?i" ∈ hfd.inst.schema.del := by rw [hs]; simp [switchOnA]
  have heq : instAtom hfd.inst.schema.params hfd.inst.args (calibratedV "?i")
      = calibrated ins := by rw [hs, ha]; rfl
  have hadd : hfd.inst.add = [powerOn ins] := (switchOn_atoms hfd.inst hs ha).2.1
  have hnadd : instAtom hfd.inst.schema.params hfd.inst.args (calibratedV "?i")
      ∉ hfd.inst.add := by
    rw [heq, hadd]
    simp [calibrated, powerOn]
  have hmem := hfd.delCompleteRaw _ hy hnadd
  rwa [heq] at hmem

/--
**What every Satellite operator carries.**

Its schema instance, as always — and, when it is a `switch_on` whose instrument
supports a mode an image goal needs, the `calibrated` delete, whether or not the
relevance analysis ran.
-/
theorem satellite_opFacts (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (ho : o ∈ groundedOps d p rel) :
    ∃ hf : OpFacts d p o, ∀ ins s : Name, hf.inst.schema = switchOnA →
      hf.inst.args = [ins, s] → NeedsCalib d p rel ins → calibrated ins ∈ o.del := by
  cases rel with
  | false =>
      obtain ⟨hfd⟩ := opFacts_raw_del d p (by rwa [← groundedOps_false])
      exact ⟨hfd.toOpFacts, fun ins s hs ha _ => switchOn_del_raw hfd hs ha⟩
  | true =>
      rcases relevance_cases (rawOps d p) p.goal.toArray with ⟨r, hclosed, hgoal, hrdef⟩ | hall
      · obtain ⟨op, hop, hval, hpre, -⟩ := pruned_op ho hclosed hrdef
        obtain ⟨hfd⟩ := opFacts_raw_del d p hop
        subst hval
        refine ⟨⟨hfd.inst, ?_, ?_, ?_, ?_, hfd.staticHeld, ?_, hfd.cost⟩, ?_⟩
        · intro a ha; exact hfd.subPre a ha
        · intro a ha; exact hfd.subAdd a (Array.mem_filter.mp ha).1
        · intro a ha; exact hfd.subDel a (Array.mem_filter.mp ha).1
        · intro y hy hdyn; exact hfd.preComplete y hy hdyn
        · intro y hy hn hp2
          exact Array.mem_filter.mpr ⟨hfd.delComplete y hy hn hp2, hpre _ hp2⟩
        · intro ins s hs ha hneed
          refine Array.mem_filter.mpr ⟨switchOn_del_raw hfd hs ha, ?_⟩
          obtain ⟨a1, a2, hargs, hw1, hw2⟩ :=
            hfd.inst.args_two (show hfd.inst.schema.params = [insP "?i", satP "?s"] by
              rw [hs])
          rw [ha] at hargs
          obtain ⟨rfl, rfl⟩ : ins = a1 ∧ s = a2 := by simpa using hargs
          exact calibrated_relevant hp true hclosed hgoal
            (onBoard_init hp hfd.toOpFacts (Or.inl hs) ha) hw1 hw2 hneed
      · have heq : groundedOps d p true = rawOps d p := by rw [groundedOps_true, hall]
        rw [heq] at ho
        obtain ⟨hfd⟩ := opFacts_raw_del d p ho
        exact ⟨hfd.toOpFacts, fun ins s hs ha _ => switchOn_del_raw hfd hs ha⟩

end Planner.Lifted.Satellite

/- -------------------------------------------------------------------------- -/
/-
`calibrate`, `switch_on` and `switch_off`: the three actions that move only the
instruments.

Each has to move the three instrument terms by at most one *in total*, and to
leave both turn terms alone.  Which of the three is its own is the whole content:

  * `calibrate` makes one instrument ready, so the calibration cover count may
    fall.  It cannot also shorten the turn list — a satellite points one way at a
    time, so the only direction where the new ready instrument creates coverage
    is the calibration target it was already pointing at, and that direction was
    covered before.
  * `switch_on` powers one instrument, so the power cover count may fall.  It
    cannot make the ready set grow — the instrument it switches on loses its
    calibration — nor shrink, because a satellite with a free power slot has no
    instrument on, so the one being switched on was not ready either.
  * `switch_off` frees one power slot, so the free-slot term may fall.  Nothing
    else can: it only ever removes power.
-/

namespace Planner.Lifted.Satellite

open Planner Planner.Pddl

variable {d : Domain} {p : Problem}

/-! ### Two facts about an action that deletes nothing -/

theorem applyA_mono_nodel {o : AtomOp} (hf : OpFacts d p o) (hdel : hf.inst.del = [])
    {σ : AtomState} {a : GroundAtom} (h : σ a = true) : o.applyA σ a = true := by
  by_cases hadd : a ∈ o.add
  · exact applyA_add σ hadd
  · rw [applyA_frame σ hadd (fun hc => absurd (hf.subDel a hc) (by rw [hdel]; simp))]
    exact h

/-! ### The arguments of a schema, as table indices -/

theorem calibrate_indices (hp : Pinned d p) (rel : Bool) {o : AtomOp} (hf : OpFacts d p o)
    {s ins dd : Name} (hs : hf.inst.schema = calibrateA) (ha : hf.inst.args = [s, ins, dd]) :
    ∃ si i di, satIx (ground d p rel) s = some si ∧ insIx (ground d p rel) ins = some i ∧
      dirIx (ground d p rel) dd = some di := by
  obtain ⟨a1, a2, a3, hargs, hw1, hw2, hw3⟩ :=
    hf.inst.args_three (show hf.inst.schema.params = [satP "?s", insP "?i", dirP "?d"] by
      rw [hs])
  rw [ha] at hargs
  obtain ⟨rfl, rfl, rfl⟩ : s = a1 ∧ ins = a2 ∧ dd = a3 := by simpa using hargs
  obtain ⟨si, hsi⟩ := findIdx_total (mem_satellites hp rel hw1)
  obtain ⟨i, hi⟩ := findIdx_total (mem_instruments hp rel hw2)
  obtain ⟨di, hdi⟩ := findIdx_total (mem_directions hp rel hw3)
  exact ⟨si, i, di, hsi, hi, hdi⟩

theorem switch_indices (hp : Pinned d p) (rel : Bool) {o : AtomOp} (hf : OpFacts d p o)
    {ins s : Name} (hs : hf.inst.schema = switchOnA ∨ hf.inst.schema = switchOffA)
    (ha : hf.inst.args = [ins, s]) :
    ∃ i si, insIx (ground d p rel) ins = some i ∧ satIx (ground d p rel) s = some si := by
  have hpar : hf.inst.schema.params = [insP "?i", satP "?s"] := by
    rcases hs with h | h <;> rw [h]
  obtain ⟨a1, a2, hargs, hw1, hw2⟩ := hf.inst.args_two hpar
  rw [ha] at hargs
  obtain ⟨rfl, rfl⟩ : ins = a1 ∧ s = a2 := by simpa using hargs
  obtain ⟨i, hi⟩ := findIdx_total (mem_instruments hp rel hw1)
  obtain ⟨si, hsi⟩ := findIdx_total (mem_satellites hp rel hw2)
  exact ⟨i, si, hi, hsi⟩

theorem image_indices (hp : Pinned d p) (rel : Bool) {o : AtomOp} (hf : OpFacts d p o)
    {s dd ins m : Name} (hs : hf.inst.schema = imageA)
    (ha : hf.inst.args = [s, dd, ins, m]) :
    ∃ si di i mi, satIx (ground d p rel) s = some si ∧
      dirIx (ground d p rel) dd = some di ∧ insIx (ground d p rel) ins = some i ∧
      modeIx (ground d p rel) m = some mi := by
  obtain ⟨a1, a2, a3, a4, hargs, hw1, hw2, hw3, hw4⟩ :=
    hf.inst.args_four (show hf.inst.schema.params
      = [satP "?s", dirP "?d", insP "?i", modeP "?m"] by rw [hs])
  rw [ha] at hargs
  obtain ⟨rfl, rfl, rfl, rfl⟩ : s = a1 ∧ dd = a2 ∧ ins = a3 ∧ m = a4 := by simpa using hargs
  obtain ⟨si, hsi⟩ := findIdx_total (mem_satellites hp rel hw1)
  obtain ⟨di, hdi⟩ := findIdx_total (mem_directions hp rel hw2)
  obtain ⟨i, hi⟩ := findIdx_total (mem_instruments hp rel hw3)
  obtain ⟨mi, hmi⟩ := findIdx_total (mem_modes hp rel hw4)
  exact ⟨si, di, i, mi, hsi, hdi, hi, hmi⟩

/-! ### `calibrate` -/

/-- The two static atoms a `calibrate` reads. -/
theorem calibrate_static (hp : Pinned d p) (rel : Bool) {o : AtomOp} (hf : OpFacts d p o)
    {s ins dd : Name} (hs : hf.inst.schema = calibrateA) (ha : hf.inst.args = [s, ins, dd]) :
    onBoard ins s ∈ (ground d p rel).staticWith "on_board" ∧
      calibTarget ins dd ∈ (ground d p rel).staticWith "calibration_target" := by
  have hpre := calibrate_pre_eq hf.inst hs ha
  refine ⟨?_, ?_⟩
  · exact static_of_pre (a := onBoard ins s) hp rel hf (by rw [hpre]; simp)
      (by simpa [onBoard] using hp.onBoardStatic)
  · exact static_of_pre (a := calibTarget ins dd) hp rel hf (by rw [hpre]; simp)
      (by simpa [calibTarget] using hp.targetStatic)

/-- Everything but the calibration table is untouched by a `calibrate`. -/
theorem calibrate_frames (hp : Pinned d p) (rel : Bool) {o : AtomOp} (hf : OpFacts d p o)
    {s ins dd : Name} (hs : hf.inst.schema = calibrateA) (ha : hf.inst.args = [s, ins, dd])
    (σ : AtomState) :
    (∀ g ∈ (cfgOf (ground d p rel)).images, o.applyA σ g.goalAtom = σ g.goalAtom) ∧
    (∀ g ∈ (cfgOf (ground d p rel)).pointingGoals,
      o.applyA σ g.goalAtom = σ g.goalAtom) ∧
    (∀ a, some a ∈ (cfgOf (ground d p rel)).powerOnAtoms → o.applyA σ a = σ a) ∧
    (∀ a, some a ∈ (cfgOf (ground d p rel)).powerAvailAtoms → o.applyA σ a = σ a) ∧
    (∀ x, ∀ q ∈ (cfgOf (ground d p rel)).pointingByDir.getD x #[],
      o.applyA σ q.1 = σ q.1) := by
  obtain ⟨-, -, hadd, hdel⟩ := calibrate_atoms hf.inst hs ha
  have hpred : ∀ b ∈ [calibrated ins] ++ ([] : List GroundAtom), b.pred = "calibrated" := by
    intro b hb
    simp only [List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hb
    rw [hb]
  refine ⟨frame_imgGoals rel hf hadd hdel (fun b hb => by rw [hpred b hb]; decide) σ,
    frame_ptGoals rel hf hadd hdel (fun b hb => by rw [hpred b hb]; decide) σ,
    frame_power rel hf hadd hdel (fun b hb => by rw [hpred b hb]; decide) σ,
    frame_avail rel hf hadd hdel (fun b hb => by rw [hpred b hb]; decide) σ,
    frame_points hp rel hf hadd hdel (fun b hb => by rw [hpred b hb]; decide) σ⟩

/-- A `calibrate` grows the ready set by at most the instrument it names. -/
theorem calibrate_ready_sub (hp : Pinned d p) (rel : Bool) {o : AtomOp} (hf : OpFacts d p o)
    {s ins dd : Name} (hs : hf.inst.schema = calibrateA) (ha : hf.inst.args = [s, ins, dd])
    {i : Nat} (hi : insIx (ground d p rel) ins = some i) (σ : AtomState) :
    ∀ j ∈ readyNow (cfgOf (ground d p rel)) (o.applyA σ),
      j = i ∨ j ∈ readyNow (cfgOf (ground d p rel)) σ := by
  intro j hj
  obtain ⟨-, -, hadd, hdel⟩ := calibrate_atoms hf.inst hs ha
  obtain ⟨-, -, hpow, -, -⟩ := calibrate_frames hp rel hf hs ha σ
  have hpoweq : poweredNow (cfgOf (ground d p rel)) (o.applyA σ)
      = poweredNow (cfgOf (ground d p rel)) σ := poweredNow_congr _ σ _ hpow
  have hsize : (cfgOf (ground d p rel)).calibratedAtoms.size
      = (insA (ground d p rel)).size := by
    rw [calibratedAtoms_eq]; simp [optTable]
  have hkey : ∀ j', j' ≠ i →
      ∀ hlt : j' < (cfgOf (ground d p rel)).calibratedAtoms.size, ∀ a,
      (cfgOf (ground d p rel)).calibratedAtoms[j'] = some a →
      o.applyA σ a = true → σ a = true := by
    intro j' hj' hlt a hget htrue
    have hjlt : j' < (insA (ground d p rel)).size := hsize ▸ hlt
    have hname : a = calibrated (insA (ground d p rel))[j'] :=
      calibrated_at (objs_nodup hp rel "instrument") hjlt
        (by rw [Array.getElem?_eq_getElem hlt, hget])
    have hne : a ≠ calibrated ins := by
      rw [hname]
      intro hc
      exact ins_ne_of_index (objs_nodup hp rel "instrument") hi hjlt hj'
        (by simpa [calibrated] using hc)
    rw [frame_of_lists hf hadd hdel (by simp [hne]) (by simp) σ] at htrue
    exact htrue
  simp only [readyNow, Array.mem_filter] at hj ⊢
  rcases active_sub (k := i) hkey hj.1 with hjk | hjc
  · exact Or.inl hjk
  · exact Or.inr ⟨hjc, by rw [← hpoweq]; exact hj.2⟩

/-- And never shrinks it. -/
theorem calibrate_ready_mono (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (hf : OpFacts d p o) {s ins dd : Name} (hs : hf.inst.schema = calibrateA)
    (ha : hf.inst.args = [s, ins, dd]) (σ : AtomState) :
    ∀ j ∈ readyNow (cfgOf (ground d p rel)) σ,
      j ∈ readyNow (cfgOf (ground d p rel)) (o.applyA σ) := by
  intro j hj
  obtain ⟨-, -, hadd, hdel⟩ := calibrate_atoms hf.inst hs ha
  obtain ⟨-, -, hpow, -, -⟩ := calibrate_frames hp rel hf hs ha σ
  have hpoweq : poweredNow (cfgOf (ground d p rel)) (o.applyA σ)
      = poweredNow (cfgOf (ground d p rel)) σ := poweredNow_congr _ σ _ hpow
  simp only [readyNow, Array.mem_filter] at hj ⊢
  refine ⟨active_mono (fun j' hlt a hget htrue => applyA_mono_nodel hf hdel htrue) hj.1, ?_⟩
  rw [hpoweq]; exact hj.2

/-- Coverage is lost, not gained, unless a newly ready instrument calibrates
against the very direction in question. -/
theorem covered_mono' (c : Cfg) (σ τ : AtomState) {x m : Nat}
    (hpoint : ∀ q ∈ c.pointingByDir.getD x #[], τ q.1 = true → σ q.1 = true)
    (hready : ∀ q ∈ c.pointingByDir.getD x #[], σ q.1 = true →
      ∀ j ∈ c.onBoard.getD q.2 #[], (readyNow c τ).contains j = true →
      (readyNow c σ).contains j = true ∨ (c.calibTarget.getD j none == some x) = true)
    (h : covered c τ x m = true) : covered c σ x m = true := by
  simp only [covered, Array.any_eq_true] at h ⊢
  obtain ⟨i, hi, hq⟩ := h
  refine ⟨i, hi, ?_⟩
  simp only [Bool.and_eq_true, Array.any_eq_true] at hq ⊢
  have hσq : σ (c.pointingByDir.getD x #[])[i].1 = true :=
    hpoint _ (Array.getElem_mem hi) hq.1
  refine ⟨hσq, ?_⟩
  obtain ⟨j, hj, hcond⟩ := hq.2
  refine ⟨j, hj, ?_⟩
  simp only [Bool.and_eq_true, Bool.or_eq_true] at hcond ⊢
  refine ⟨hcond.1, ?_⟩
  rcases hcond.2 with hr | ht
  · exact hready _ (Array.getElem_mem hi) hσq _ (Array.getElem_mem hj) hr
  · exact Or.inr ht

/-- **A `calibrate` covers no direction that was not covered before.** -/
theorem calibrate_covered (hp : Pinned d p) (rel : Bool) {o : AtomOp} (hf : OpFacts d p o)
    {s ins dd : Name} (hs : hf.inst.schema = calibrateA) (ha : hf.inst.args = [s, ins, dd])
    {i di : Nat} (hi : insIx (ground d p rel) ins = some i)
    (hdi : dirIx (ground d p rel) dd = some di)
    {σ : AtomState} (hinv : Inv p σ) (happ : o.applicableA σ) {x m : Nat}
    (hcov : covered (cfgOf (ground d p rel)) (o.applyA σ) x m = true) :
    covered (cfgOf (ground d p rel)) σ x m = true := by
  obtain ⟨hboard, htarget⟩ := calibrate_static hp rel hf hs ha
  obtain ⟨-, -, -, -, hpoints⟩ := calibrate_frames hp rel hf hs ha σ
  have hpre := calibrate_pre_eq hf.inst hs ha
  have hpointing : σ (pointing s dd) = true :=
    pre_holds hf (by rw [hpre]; simp)
      (by simpa [pointing] using pointing_dynamic hp.domain) happ
  have htgt : (cfgOf (ground d p rel)).calibTarget.getD i none = some di :=
    calibTarget_eq hp rel hi hdi htarget
  refine covered_mono' _ σ (o.applyA σ) ?_ ?_ hcov
  · intro q hq htrue
    rw [← hpoints x q hq]; exact htrue
  · intro q hq hσq j hj hready
    rcases calibrate_ready_sub hp rel hf hs ha hi σ j (by simpa using hready) with hji | hin
    · -- the newly ready instrument: it is on the satellite that is pointing, and
      -- that satellite points at the calibration target
      refine Or.inr ?_
      obtain ⟨sn, dn, hqa, hsn, hdn⟩ :=
        pointingByDir_data (objs_nodup hp rel "direction") hq
      obtain ⟨ins2, hins2, hboard2⟩ := onBoard_sound hsn (hji ▸ hj)
      have hsame : ins2 = ins := findIdx_inj hins2 hi
      have hb2 : onBoard ins sn ∈ p.init := by
        rw [hsame] at hboard2
        exact staticWith_init rel hboard2
      have hsatEq : sn = s :=
        hp.oneBoard (ins, sn) (mem_initPairs.mpr hb2) (ins, s)
          (mem_initPairs.mpr (staticWith_init rel hboard)) rfl
      have hpt : σ (pointing sn dn) = true := by rw [← hqa]; exact hσq
      have hdirEq : dn = dd := by
        refine hinv.onePointing s dn dd ?_ hpointing
        rw [← hsatEq]; exact hpt
      have hxdi : x = di := by
        rw [hdirEq, hdi] at hdn
        simpa using hdn.symm
      rw [hji, htgt, hxdi]
      simp
    · exact Or.inl (by simpa using hin)

theorem pointsAt_of_mem (c : Cfg) (σ : AtomState) {sat dir : Nat} {q : GroundAtom × Nat}
    (hq : q ∈ c.pointingByDir.getD dir #[]) (hsat : q.2 = sat) (htrue : σ q.1 = true) :
    pointsAt c σ sat dir = true :=
  array_any_of_mem hq (by simp [hsat, htrue])

theorem supportsMode_of (c : Cfg) {set : Array Nat} {j m : Nat} (hj : j ∈ set)
    (hm : (c.supports.getD j #[]).contains m = true) : supportsMode c set m = true :=
  array_any_of_mem hj hm

/-- One instrument that supports a needed mode and whose calibration target a
satellite already faces puts a calibration in reach. -/
theorem inReach_of_points (c : Cfg) (σ : AtomState) {j target sat : Nat}
    (hj : j < c.supports.size)
    (hneed : (c.supports.getD j #[]).any (neededModes c σ).contains = true)
    (htgt : c.calibTarget.getD j none = some target)
    (hsat : c.satelliteOf.getD j none = some sat)
    (hpt : pointsAt c σ sat target = true) : calibrationInReach c σ = true := by
  refine array_any_of_mem (mem_zipIdx_self c.supports hj) ?_
  simp only [Bool.and_eq_true]
  refine ⟨by rw [← getD_eq_getElem c.supports #[] hj]; exact hneed, ?_⟩
  rw [htgt, hsat]
  simp [hpt]

theorem supports_size (t : Task) : (cfgOf t).supports.size = (insA t).size := by
  show ((insA t).map _).size = _
  simp

/-- The unmet pointing goals are unchanged when no pointing goal moves. -/
theorem unmetPointing_array_congr (c : Cfg) (σ τ : AtomState)
    (h : ∀ g ∈ c.pointingGoals, τ g.goalAtom = σ g.goalAtom) :
    unmetPointing c τ = unmetPointing c σ := by
  apply Array.toList_inj.mp
  simp only [unmetPointing, Array.toList_filter]
  exact List.filter_congr fun g hg => by rw [h g (by simpa using hg)]

/-- The condition `calibrationInReach` puts on one instrument, with the two
table lookups pulled out so that the case split is on plain values. -/
def reachCond (c : Cfg) (σ : AtomState) (T S : Option Nat) : Bool :=
  match T, S with
  | some target, some sat =>
      pointsAt c σ sat target || (dirsToTurn c σ).contains target ||
        (unmetPointing c σ).any fun g => g.dir == target
  | _, _ => true

theorem inReach_eq (c : Cfg) (σ : AtomState) :
    calibrationInReach c σ =
      c.supports.zipIdx.any fun x => x.1.any (neededModes c σ).contains &&
        reachCond c σ (c.calibTarget.getD x.2 none) (c.satelliteOf.getD x.2 none) := rfl

theorem reachCond_mono (c : Cfg) (σ τ : AtomState)
    (hpoints : ∀ sat dir, pointsAt c τ sat dir = true → pointsAt c σ sat dir = true)
    (hdirs : ∀ x, (dirsToTurn c τ).contains x = true → (dirsToTurn c σ).contains x = true)
    (hunmet : unmetPointing c τ = unmetPointing c σ)
    (T S : Option Nat) (h : reachCond c τ T S = true) : reachCond c σ T S = true := by
  revert h
  cases T with
  | none => intro _; rfl
  | some target =>
      cases S with
      | none => intro _; rfl
      | some sat =>
          intro h
          simp only [reachCond, Bool.or_eq_true] at h ⊢
          rcases h with (h1 | h1) | h1
          · exact Or.inl (Or.inl (hpoints sat target h1))
          · exact Or.inl (Or.inr (hdirs target h1))
          · exact Or.inr (by rw [hunmet] at h1; exact h1)

/-- A calibration in reach stays in reach when nothing the test reads has moved
against it. -/
theorem inReach_mono (c : Cfg) (σ τ : AtomState)
    (hneeded : ∀ m ∈ neededModes c τ, m ∈ neededModes c σ)
    (hpoints : ∀ sat dir, pointsAt c τ sat dir = true → pointsAt c σ sat dir = true)
    (hdirs : ∀ x, (dirsToTurn c τ).contains x = true → (dirsToTurn c σ).contains x = true)
    (hunmet : unmetPointing c τ = unmetPointing c σ)
    (h : calibrationInReach c τ = true) : calibrationInReach c σ = true := by
  rw [inReach_eq] at h ⊢
  obtain ⟨y, hy, hcond⟩ := array_any_elim h
  refine array_any_of_mem hy ?_
  simp only [Bool.and_eq_true] at hcond ⊢
  refine ⟨?_, reachCond_mono c σ τ hpoints hdirs hunmet _ _ hcond.2⟩
  obtain ⟨m, hm, hmc⟩ := array_any_elim hcond.1
  exact array_any_of_mem hm (by simpa using hneeded m (by simpa using hmc))

/-- The satellite of a `calibrate` already faces the calibration target, so an
instrument that supports a needed mode puts a calibration in reach. -/
theorem calibrate_inReach (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (ho : o ∈ groundedOps d p rel) (hf : OpFacts d p o)
    {s ins dd : Name} (hs : hf.inst.schema = calibrateA) (ha : hf.inst.args = [s, ins, dd])
    {si i di : Nat} (hsi : satIx (ground d p rel) s = some si)
    (hi : insIx (ground d p rel) ins = some i) (hdi : dirIx (ground d p rel) dd = some di)
    {σ : AtomState} (happ : o.applicableA σ)
    (hneed : ((cfgOf (ground d p rel)).supports.getD i #[]).any
      (neededModes (cfgOf (ground d p rel)) σ).contains = true) :
    calibrationInReach (cfgOf (ground d p rel)) σ = true := by
  obtain ⟨hboard, htarget⟩ := calibrate_static hp rel hf hs ha
  have hpre := calibrate_pre_eq hf.inst hs ha
  have hdyn : (staticPredicates d).contains (pointing s dd).pred = false := by
    simpa [pointing] using pointing_dynamic hp.domain
  have hptTrue : σ (pointing s dd) = true := pre_holds hf (by rw [hpre]; simp) hdyn happ
  obtain ⟨f, hflt, hfname⟩ :=
    numbered_of_op d p rel ho (Or.inl (pre_mem_op hf (by rw [hpre]; simp) hdyn))
  refine inReach_of_points _ σ (by rw [supports_size]; exact (findIdx_sound hi).1) hneed
    (calibTarget_eq hp rel hi hdi htarget) (satelliteOf_eq hp rel hi hsi hboard)
    (pointsAt_of_mem _ σ (mem_pointingByDir hsi hdi hflt hfname) rfl hptTrue)

/-- **`calibrate` is a `ReadyStep`.** -/
theorem calibrate_ready (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (ho : o ∈ groundedOps d p rel) (hf : OpFacts d p o)
    {s ins dd : Name} (hs : hf.inst.schema = calibrateA) (ha : hf.inst.args = [s, ins, dd])
    {σ : AtomState} (hinv : Inv p σ) (happ : o.applicableA σ) :
    ReadyStep (cfgOf (ground d p rel)) σ (o.applyA σ) := by
  obtain ⟨si, i, di, hsi, hi, hdi⟩ := calibrate_indices hp rel hf hs ha
  obtain ⟨himg, hpt, hpow, havail, hpoints⟩ := calibrate_frames hp rel hf hs ha σ
  have hsub := calibrate_ready_sub hp rel hf hs ha hi σ
  have hmono := calibrate_ready_mono hp rel hf hs ha σ
  have hneededEq := neededModes_congr (cfgOf (ground d p rel)) σ (o.applyA σ) himg
  have hup := unmetPointing_array_congr (cfgOf (ground d p rel)) σ (o.applyA σ) hpt
  have hpaidEq : ∀ x, paidByGoal (cfgOf (ground d p rel)) (o.applyA σ) x
      = paidByGoal (cfgOf (ground d p rel)) σ x := by
    intro x; simp only [paidByGoal, hup]
  have hcovτσ : ∀ x m, covered (cfgOf (ground d p rel)) σ x m = true →
      covered (cfgOf (ground d p rel)) (o.applyA σ) x m = true := by
    intro x m hc
    refine covered_mono _ (o.applyA σ) σ ?_ ?_ hc
    · intro q hq htrue; rw [hpoints x q hq]; exact htrue
    · intro j hj; simpa using hmono j (by simpa using hj)
  -- the outstanding directions do not move
  have hdirsSub : ∀ x ∈ dirsList (cfgOf (ground d p rel)) σ,
      x ∈ dirsList (cfgOf (ground d p rel)) (o.applyA σ) := by
    intro x hx
    obtain ⟨img, hq, hxd, hpaid, hcov⟩ := (mem_dirsList _ σ).mp hx
    refine (mem_dirsList _ (o.applyA σ)).mpr ⟨img, mem_unmetImages_of _ himg hq, hxd, ?_, ?_⟩
    · rw [hpaidEq, hxd] at *; exact hpaid
    · rcases hct : covered (cfgOf (ground d p rel)) (o.applyA σ) x img.mode with _ | _
      · rfl
      · rw [calibrate_covered hp rel hf hs ha hi hdi hinv happ hct] at hcov
        exact absurd hcov (by simp)
  have hdirsSub' : ∀ x ∈ dirsList (cfgOf (ground d p rel)) (o.applyA σ),
      x ∈ dirsList (cfgOf (ground d p rel)) σ := by
    intro x hx
    obtain ⟨img, hq, hxd, hpaid, hcov⟩ := (mem_dirsList _ (o.applyA σ)).mp hx
    refine (mem_dirsList _ σ).mpr ⟨img, mem_unmetImages_of _ (fun g hg => (himg g hg).symm) hq,
      hxd, ?_, ?_⟩
    · rw [← hpaidEq]; exact hpaid
    · rcases hct : covered (cfgOf (ground d p rel)) σ x img.mode with _ | _
      · rfl
      · rw [hcovτσ x img.mode hct] at hcov
        exact absurd hcov (by simp)
  refine ⟨himg, ?_, ?_⟩
  · -- one instrument action moves the three terms by at most one
    refine instruments_le_succ _ σ (o.applyA σ) (du := 1) (dp := 0) (df := 0) ?_ ?_ ?_ (by omega)
    · refine coverCount_le_succ _ _ _ ?_
      intro hempty
      have hilt : i < (cfgOf (ground d p rel)).supports.size := by
        rw [supports_size]; exact (findIdx_sound hi).1
      refine array_any_of_mem (Array.getElem_mem hilt) ?_
      rw [List.all_eq_true]
      intro mm hmm
      rw [uncalibratedModes, List.mem_filter] at hmm
      obtain ⟨hneed, hnsup⟩ := hmm
      have hnotτ : mm ∉ uncalibratedModes (cfgOf (ground d p rel)) (o.applyA σ) := by
        rw [List.isEmpty_iff] at hempty
        rw [hempty]; simp
      have hsupτ : supportsMode (cfgOf (ground d p rel)) (readyNow (cfgOf (ground d p rel))
          (o.applyA σ)) mm = true := by
        by_contra hc
        exact hnotτ (by
          rw [uncalibratedModes, List.mem_filter]
          exact ⟨by rw [hneededEq]; exact hneed, by simpa using hc⟩)
      obtain ⟨j, hj, hjc⟩ := array_any_elim hsupτ
      rcases hsub j hj with hji | hjσ
      · rw [← getD_eq_getElem _ #[] hilt, ← hji]; exact hjc
      · exact absurd (supportsMode_of _ hjσ hjc) (by simpa using hnsup)
    · rw [unpoweredModes_congr _ σ (o.applyA σ) himg hpow]; omega
    · rw [freeSlot_congr _ σ (o.applyA σ) himg hpow havail]; omega
  · -- the turn terms, which no instrument action moves
    refine turns_le_of_parts hpt (dirsToTurn_mono _ σ (o.applyA σ) hdirsSub) ?_
    by_cases hc : (!(uncalibratedModes (cfgOf (ground d p rel)) σ).isEmpty &&
        !calibrationInReach (cfgOf (ground d p rel)) σ) = true
    · obtain ⟨hne, hnr⟩ : (uncalibratedModes (cfgOf (ground d p rel)) σ).isEmpty = false ∧
          calibrationInReach (cfgOf (ground d p rel)) σ = false := by simpa using hc
      have hnoneed : ((cfgOf (ground d p rel)).supports.getD i #[]).any
          (neededModes (cfgOf (ground d p rel)) σ).contains = false := by
        by_contra hcc
        rw [calibrate_inReach hp rel ho hf hs ha hsi hi hdi happ (by simpa using hcc)] at hnr
        exact Bool.noConfusion hnr
      have hsupEq : ∀ mm ∈ neededModes (cfgOf (ground d p rel)) σ,
          (!supportsMode (cfgOf (ground d p rel)) (readyNow (cfgOf (ground d p rel))
            (o.applyA σ)) mm)
            = (!supportsMode (cfgOf (ground d p rel)) (readyNow (cfgOf (ground d p rel)) σ) mm) := by
        intro mm hmm
        congr 1
        rcases hστ : supportsMode (cfgOf (ground d p rel)) (readyNow (cfgOf (ground d p rel)) σ) mm
          with _ | _
        · rcases hτ : supportsMode (cfgOf (ground d p rel)) (readyNow (cfgOf (ground d p rel))
            (o.applyA σ)) mm with _ | _
          · rfl
          · exfalso
            obtain ⟨j, hj, hjc⟩ := array_any_elim hτ
            rcases hsub j hj with hji | hjσ
            · rw [hji] at hjc
              have : ((cfgOf (ground d p rel)).supports.getD i #[]).any
                  (neededModes (cfgOf (ground d p rel)) σ).contains = true :=
                array_any_of_mem (by simpa using hjc) (by simpa using hmm)
              rw [hnoneed] at this
              exact Bool.noConfusion this
            · rw [supportsMode_of _ hjσ hjc] at hστ
              exact Bool.noConfusion hστ
        · rw [supportsMode_mono _ (fun j hj => hmono j hj) hστ]
      have huncal : uncalibratedModes (cfgOf (ground d p rel)) (o.applyA σ)
          = uncalibratedModes (cfgOf (ground d p rel)) σ := by
        rw [uncalibratedModes, uncalibratedModes, hneededEq]
        exact List.filter_congr hsupEq
      have hirFalse : calibrationInReach (cfgOf (ground d p rel)) (o.applyA σ) = false := by
        rcases hir : calibrationInReach (cfgOf (ground d p rel)) (o.applyA σ) with _ | _
        · rfl
        · exfalso
          have := inReach_mono _ σ (o.applyA σ) (fun m hm => by rw [hneededEq] at hm; exact hm)
            (fun sat dir hpts => by
              simp only [pointsAt] at hpts ⊢
              obtain ⟨q, hq, hqc⟩ := array_any_elim hpts
              refine array_any_of_mem hq ?_
              simp only [Bool.and_eq_true] at hqc ⊢
              exact ⟨hqc.1, by rw [← hpoints dir q hq]; exact hqc.2⟩)
            (fun x hx => by
              have hx' : x ∈ dirsToTurn (cfgOf (ground d p rel)) (o.applyA σ) := by simpa using hx
              have hx2 : x ∈ dirsToTurn (cfgOf (ground d p rel)) σ := by
                rw [dirsToTurn_eq, mem_distinct] at hx' ⊢
                exact hdirsSub' x hx'
              simpa using hx2)
            hup hir
          rw [hnr] at this
          exact Bool.noConfusion this
      have hcondτ : (!(uncalibratedModes (cfgOf (ground d p rel)) (o.applyA σ)).isEmpty &&
          !calibrationInReach (cfgOf (ground d p rel)) (o.applyA σ)) = true := by
        rw [huncal, hne, hirFalse]; rfl
      rw [approach, if_pos hc, approach, if_pos hcondτ]
    · rw [approach, if_neg hc]; omega

theorem reachCond_none_left (c : Cfg) (σ : AtomState) (S : Option Nat) :
    reachCond c σ none S = true := by cases S <;> rfl

theorem reachCond_none_right (c : Cfg) (σ : AtomState) (T : Option Nat) :
    reachCond c σ T none = true := by cases T <;> rfl

/-- **What a newly reachable calibration must be.**  When the detour is charged
before and not after, one instrument's target is the reason, and the test it now
passes is one it failed before. -/
theorem inReach_witness (c : Cfg) (σ τ : AtomState)
    (hneeded : neededModes c τ = neededModes c σ)
    (hσ : calibrationInReach c σ = false) (hτ : calibrationInReach c τ = true) :
    ∃ target sat, reachCond c τ (some target) (some sat) = true ∧
      reachCond c σ (some target) (some sat) = false := by
  rw [inReach_eq] at hσ hτ
  obtain ⟨y, hy, hcond⟩ := array_any_elim hτ
  have hfail := array_any_false hσ hy
  simp only [Bool.and_eq_true] at hcond
  have hneed' : y.1.any (neededModes c σ).contains = true := by rw [← hneeded]; exact hcond.1
  have hrc : reachCond c σ (c.calibTarget.getD y.2 none) (c.satelliteOf.getD y.2 none)
      = false := by
    simp only [hneed', Bool.true_and] at hfail
    exact hfail
  rcases hT : c.calibTarget.getD y.2 none with _ | target
  · rw [hT, reachCond_none_left] at hrc; exact Bool.noConfusion hrc
  · rcases hS : c.satelliteOf.getD y.2 none with _ | sat
    · rw [hT, hS, reachCond_none_right] at hrc; exact Bool.noConfusion hrc
    · exact ⟨target, sat, by rw [hT, hS] at hcond; exact hcond.2,
        by rw [hT, hS] at hrc; exact hrc⟩

/-! ### `switch_off` -/

/-- **`switch_off` is a `ReadyStep`.**  It only ever removes power, so the two
cover counts can only grow; the slot it frees is the one term that may fall, and
the coverage it costs pays for any calibration it brings into reach. -/
theorem switchOff_ready (hp : Pinned d p) (rel : Bool) {o : AtomOp} (hf : OpFacts d p o)
    {ins s : Name} (hs : hf.inst.schema = switchOffA) (ha : hf.inst.args = [ins, s])
    (σ : AtomState) : ReadyStep (cfgOf (ground d p rel)) σ (o.applyA σ) := by
  obtain ⟨-, hadd, hdel⟩ := switchOff_atoms hf.inst hs ha
  have hpred : ∀ b ∈ [powerAvail s] ++ [powerOn ins],
      b.pred = "power_avail" ∨ b.pred = "power_on" := by
    intro b hb
    simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have himg := frame_imgGoals rel hf hadd hdel
    (fun b hb => by rcases hpred b hb with h | h <;> rw [h] <;> decide) σ
  have hpt := frame_ptGoals rel hf hadd hdel
    (fun b hb => by rcases hpred b hb with h | h <;> rw [h] <;> decide) σ
  have hcal := frame_calib rel hf hadd hdel
    (fun b hb => by rcases hpred b hb with h | h <;> rw [h] <;> decide) σ
  have hpoints := frame_points hp rel hf hadd hdel
    (fun b hb => by rcases hpred b hb with h | h <;> rw [h] <;> decide) σ
  -- power only falls
  have hpowFall : ∀ j, ∀ hj : j < (cfgOf (ground d p rel)).powerOnAtoms.size, ∀ a,
      (cfgOf (ground d p rel)).powerOnAtoms[j] = some a → o.applyA σ a = true →
      σ a = true := by
    intro j hj a hget htrue
    have hmem : some a ∈ (cfgOf (ground d p rel)).powerOnAtoms := by
      rw [← hget]; exact Array.getElem_mem hj
    refine falls_of_lists hf hadd ?_ htrue
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro hc
    rw [hc] at hmem
    have hpp : ("power_avail" : Name) = "power_on" := powerOn_pred hmem
    exact absurd hpp (by decide)
  have hpowSub : ∀ j ∈ poweredNow (cfgOf (ground d p rel)) (o.applyA σ),
      j ∈ poweredNow (cfgOf (ground d p rel)) σ := fun j hj =>
    active_mono (σ := o.applyA σ) (τ := σ) hpowFall hj
  have hcalEq : calibratedNow (cfgOf (ground d p rel)) (o.applyA σ)
      = calibratedNow (cfgOf (ground d p rel)) σ := calibratedNow_congr _ σ _ hcal
  have hreadySub : ∀ j ∈ readyNow (cfgOf (ground d p rel)) (o.applyA σ),
      j ∈ readyNow (cfgOf (ground d p rel)) σ := by
    intro j hj
    simp only [readyNow, Array.mem_filter] at hj ⊢
    exact ⟨by rw [← hcalEq]; exact hj.1, by simpa using hpowSub j (by simpa using hj.2)⟩
  have hneededEq := neededModes_congr (cfgOf (ground d p rel)) σ (o.applyA σ) himg
  have hup := unmetPointing_array_congr (cfgOf (ground d p rel)) σ (o.applyA σ) hpt
  have hpaidEq : ∀ x, paidByGoal (cfgOf (ground d p rel)) (o.applyA σ) x
      = paidByGoal (cfgOf (ground d p rel)) σ x := by
    intro x; simp only [paidByGoal, hup]
  -- coverage is only lost
  have hcovSub : ∀ x m, covered (cfgOf (ground d p rel)) (o.applyA σ) x m = true →
      covered (cfgOf (ground d p rel)) σ x m = true := by
    intro x m hc
    refine covered_mono _ σ (o.applyA σ) ?_ ?_ hc
    · intro q hq htrue; rw [← hpoints x q hq]; exact htrue
    · intro j hj; simpa using hreadySub j (by simpa using hj)
  have hdirsSub : ∀ x ∈ dirsList (cfgOf (ground d p rel)) σ,
      x ∈ dirsList (cfgOf (ground d p rel)) (o.applyA σ) := by
    intro x hx
    obtain ⟨img, hq, hxd, hpaid, hcov⟩ := (mem_dirsList _ σ).mp hx
    refine (mem_dirsList _ (o.applyA σ)).mpr ⟨img, mem_unmetImages_of _ himg hq, hxd, ?_, ?_⟩
    · rw [hpaidEq, hxd] at *; exact hpaid
    · rcases hct : covered (cfgOf (ground d p rel)) (o.applyA σ) x img.mode with _ | _
      · rfl
      · rw [hcovSub x img.mode hct] at hcov
        exact absurd hcov (by simp)
  refine ⟨himg, ?_, ?_⟩
  · refine instruments_le_succ _ σ (o.applyA σ) (du := 0) (dp := 0) (df := 1) ?_ ?_ ?_ (by omega)
    · have hsub := uncalibratedModes_sub (cfgOf (ground d p rel)) (o.applyA σ) σ
        (fun m hm => by rw [hneededEq]; exact hm) (fun j hj => hreadySub j hj)
      have := coverCount_mono (cfgOf (ground d p rel)) hsub
      omega
    · have hsub := unpoweredModes_sub (cfgOf (ground d p rel)) (o.applyA σ) σ
        (fun m hm => by rw [hneededEq]; exact hm) (fun j hj => hpowSub j hj)
      have := coverCount_mono (cfgOf (ground d p rel)) hsub
      omega
    · have := freeSlot_le_one (cfgOf (ground d p rel)) σ
      omega
  · -- the turn terms, jointly
    rw [turns_eq, turns_eq, unmetPointing_congr hpt]
    have hdlen := length_distinct_mono _ _ hdirsSub
    rw [← dirsToTurn_eq, ← dirsToTurn_eq] at hdlen
    by_cases happ2 : approach (cfgOf (ground d p rel)) σ ≤
        approach (cfgOf (ground d p rel)) (o.applyA σ)
    · omega
    · -- the detour fell, so a direction it names entered the turn list
      have hb1 := approach_le_two (cfgOf (ground d p rel)) σ
      have hb2 := approach_le_two (cfgOf (ground d p rel)) (o.applyA σ)
      have hσ1 : approach (cfgOf (ground d p rel)) σ = 1 := by omega
      have hτ0 : approach (cfgOf (ground d p rel)) (o.applyA σ) = 0 := by omega
      have hcondσ : (!(uncalibratedModes (cfgOf (ground d p rel)) σ).isEmpty &&
          !calibrationInReach (cfgOf (ground d p rel)) σ) = true := by
        by_contra hc
        rw [approach, if_neg hc] at hσ1
        exact absurd hσ1 (by simp)
      obtain ⟨-, hnrσ⟩ : (uncalibratedModes (cfgOf (ground d p rel)) σ).isEmpty = false ∧
          calibrationInReach (cfgOf (ground d p rel)) σ = false := by simpa using hcondσ
      have hnrτ : calibrationInReach (cfgOf (ground d p rel)) (o.applyA σ) = true := by
        by_contra hc
        have hcτ : calibrationInReach (cfgOf (ground d p rel)) (o.applyA σ) = false := by
          simpa using hc
        have huncτ : (uncalibratedModes (cfgOf (ground d p rel)) (o.applyA σ)).isEmpty
            = false := by
          rcases hemp : (uncalibratedModes (cfgOf (ground d p rel)) (o.applyA σ)).isEmpty with
            _ | _
          · rfl
          · exfalso
            have hsub := uncalibratedModes_sub (cfgOf (ground d p rel)) (o.applyA σ) σ
              (fun m hm => by rw [hneededEq]; exact hm) (fun j hj => hreadySub j hj)
            rw [List.isEmpty_iff] at hemp
            obtain ⟨mm, hmm⟩ : ∃ mm, mm ∈ uncalibratedModes (cfgOf (ground d p rel)) σ := by
              rcases hl : uncalibratedModes (cfgOf (ground d p rel)) σ with _ | ⟨z, zs⟩
              · rw [hl] at hcondσ; simp at hcondσ
              · exact ⟨z, by simp⟩
            have := hsub mm hmm
            rw [hemp] at this
            simp at this
        rw [approach, if_pos (by rw [huncτ, hcτ]; rfl)] at hτ0
        exact absurd hτ0 (by simp)
      obtain ⟨target, sat, hτcond, hσcond⟩ :=
        inReach_witness _ σ (o.applyA σ) hneededEq hnrσ hnrτ
      simp only [reachCond, Bool.or_eq_true, Bool.or_eq_false_iff] at hτcond hσcond
      have hpts : pointsAt (cfgOf (ground d p rel)) (o.applyA σ) sat target = false := by
        rcases hv : pointsAt (cfgOf (ground d p rel)) (o.applyA σ) sat target with _ | _
        · rfl
        · exfalso
          obtain ⟨q, hq, hqc⟩ := array_any_elim hv
          have : pointsAt (cfgOf (ground d p rel)) σ sat target = true := by
            refine array_any_of_mem hq ?_
            simp only [Bool.and_eq_true] at hqc ⊢
            exact ⟨hqc.1, by rw [← hpoints target q hq]; exact hqc.2⟩
          rw [hσcond.1.1] at this
          exact Bool.noConfusion this
      have hgoal : ((unmetPointing (cfgOf (ground d p rel)) (o.applyA σ)).any
          fun g => g.dir == target) = false := by rw [hup]; exact hσcond.2
      have hmemτ : (dirsToTurn (cfgOf (ground d p rel)) (o.applyA σ)).contains target
          = true := by
        rcases hτcond with (h | h) | h
        · rw [hpts] at h; exact absurd h (by simp)
        · exact h
        · rw [hgoal] at h; exact absurd h (by simp)
      have hnotσ : target ∉ dirsList (cfgOf (ground d p rel)) σ := by
        intro hc
        have : (dirsToTurn (cfgOf (ground d p rel)) σ).contains target = true := by
          simp only [dirsToTurn_eq]
          simpa using (mem_distinct _).mpr hc
        rw [hσcond.1.2] at this
        exact Bool.noConfusion this
      have hlt := length_distinct_lt (dirsList (cfgOf (ground d p rel)) σ)
        (dirsList (cfgOf (ground d p rel)) (o.applyA σ)) hdirsSub
        ((mem_distinct _).mp (by simpa [dirsToTurn_eq] using hmemτ)) hnotσ
      rw [← dirsToTurn_eq, ← dirsToTurn_eq] at hlt
      omega

/-! ### `switch_on` -/

/-- A needed mode an instrument supports is a mode some image goal asks for. -/
theorem needsCalib_of (hp : Pinned d p) (rel : Bool) {ins : Name} {i m : Nat}
    (hi : insIx (ground d p rel) ins = some i) {σ : AtomState}
    (hm : m ∈ neededModes (cfgOf (ground d p rel)) σ)
    (hcon : ((cfgOf (ground d p rel)).supports.getD i #[]).contains m = true) :
    NeedsCalib d p rel ins := by
  obtain ⟨g, hg, hgm⟩ : ∃ g ∈ unmetImages (cfgOf (ground d p rel)) σ, g.mode = m := by
    rw [neededModes, mem_distinct, List.mem_map] at hm
    obtain ⟨g, hg, hgm⟩ := hm
    exact ⟨g, by simpa using hg, hgm⟩
  have hgim : g ∈ (cfgOf (ground d p rel)).images := (Array.mem_filter.mp hg).1
  obtain ⟨dn, mn, hgatom, hdix, hmix⟩ := image_goal_data rel g hgim
  obtain ⟨mn2, hmn2, hstatic⟩ := supports_sound hi (by simpa using hcon)
  have hmneq : mn2 = mn := findIdx_inj hmn2 (by rw [← hgm]; exact hmix)
  refine ⟨dn, mn, ?_, ?_, ?_, ?_⟩
  · rw [← hgatom]; exact image_goalAtom_mem d p rel g hgim
  · rw [← hmneq]; exact staticWith_init rel hstatic
  · obtain ⟨hlt, hget⟩ := findIdx_sound hdix
    rw [← hget, getD_eq_getElem _ _ hlt]
    exact Array.getElem_mem hlt
  · obtain ⟨hlt, hget⟩ := findIdx_sound hmix
    rw [← hget, getD_eq_getElem _ _ hlt]
    exact Array.getElem_mem hlt

/-- The mode of an unmet image is a needed mode. -/
theorem mode_needed (c : Cfg) (σ : AtomState) {img : ImageGoal}
    (h : img ∈ unmetImages c σ) : img.mode ∈ neededModes c σ := by
  rw [neededModes, mem_distinct]
  exact List.mem_map.mpr ⟨img, by simpa using h, rfl⟩

/--
**`switch_on` is a `ReadyStep`.**

The instrument it powers was not on — a free power slot means none of the
satellite's instruments is — and it loses its calibration whenever that could
matter, so the ready set does not move where a needed mode is concerned.  What
moves is the power cover count, and that is the one term the bound allows.
-/
theorem switchOn_ready (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (ho : o ∈ groundedOps d p rel) (hf : OpFacts d p o)
    (hdelOf : ∀ ins s : Name, hf.inst.schema = switchOnA → hf.inst.args = [ins, s] →
      NeedsCalib d p rel ins → calibrated ins ∈ o.del)
    {ins s : Name} (hs : hf.inst.schema = switchOnA) (ha : hf.inst.args = [ins, s])
    {σ : AtomState} (hinv : Inv p σ) (happ : o.applicableA σ) :
    ReadyStep (cfgOf (ground d p rel)) σ (o.applyA σ) := by
  obtain ⟨i, si, hi, hsi⟩ := switch_indices hp rel hf (Or.inl hs) ha
  obtain ⟨hpa, hadd, hdel⟩ := switchOn_atoms hf.inst hs ha
  have hpre := switchOn_pre_eq hf.inst hs ha
  have hboard : onBoard ins s ∈ p.init := onBoard_init hp hf (Or.inl hs) ha
  have hboardS : onBoard ins s ∈ (ground d p rel).staticWith "on_board" :=
    static_of_pre (a := onBoard ins s) hp rel hf (by rw [hpre]; simp)
      (by simpa [onBoard] using hp.onBoardStatic)
  have hdynA : (staticPredicates d).contains (powerAvail s).pred = false := by
    simpa [powerAvail] using powerAvail_dynamic hp.domain
  have havail : σ (powerAvail s) = true := pre_holds hf hpa hdynA happ
  have hoff : σ (powerOn ins) = false := hinv.powerFree ins s hboard havail
  have hpred : ∀ b ∈ [powerOn ins] ++ [calibrated ins, powerAvail s],
      b.pred = "power_on" ∨ b.pred = "calibrated" ∨ b.pred = "power_avail" := by
    intro b hb
    simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have himg := frame_imgGoals rel hf hadd hdel
    (fun b hb => by rcases hpred b hb with h | h | h <;> rw [h] <;> decide) σ
  have hpt := frame_ptGoals rel hf hadd hdel
    (fun b hb => by rcases hpred b hb with h | h | h <;> rw [h] <;> decide) σ
  have hpoints := frame_points hp rel hf hadd hdel
    (fun b hb => by rcases hpred b hb with h | h | h <;> rw [h] <;> decide) σ
  have hcalFall : ∀ a, some a ∈ (cfgOf (ground d p rel)).calibratedAtoms →
      o.applyA σ a = true → σ a = true := by
    intro a hmem htrue
    refine falls_of_lists hf hadd ?_ htrue
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro hc
    rw [hc] at hmem
    have hpp : ("power_on" : Name) = "calibrated" := calibrated_pred hmem
    exact absurd hpp (by decide)
  have havailFall : ∀ a, some a ∈ (cfgOf (ground d p rel)).powerAvailAtoms →
      o.applyA σ a = true → σ a = true := by
    intro a hmem htrue
    refine falls_of_lists hf hadd ?_ htrue
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro hc
    rw [hc] at hmem
    have hpp : ("power_on" : Name) = "power_avail" := powerAvail_pred hmem
    exact absurd hpp (by decide)
  have hsizeP : (cfgOf (ground d p rel)).powerOnAtoms.size
      = (insA (ground d p rel)).size := by rw [powerOnAtoms_eq]; simp [optTable]
  have hsizeC : (cfgOf (ground d p rel)).calibratedAtoms.size
      = (insA (ground d p rel)).size := by rw [calibratedAtoms_eq]; simp [optTable]
  have hinotpow : i ∉ poweredNow (cfgOf (ground d p rel)) σ := by
    intro hc
    obtain ⟨hlt, a, hget, hσa⟩ := mem_activeInstruments.mp hc
    have hgetD : (cfgOf (ground d p rel)).powerOnAtoms.getD i none = some a := by
      rw [getD_eq_getElem _ _ hlt, hget]
    rw [powerOn_slot hi hgetD, hoff] at hσa
    exact Bool.noConfusion hσa
  have hpowSub : ∀ j ∈ poweredNow (cfgOf (ground d p rel)) (o.applyA σ),
      j = i ∨ j ∈ poweredNow (cfgOf (ground d p rel)) σ := by
    intro j hj
    refine active_sub (k := i) ?_ hj
    intro k hki hlt a hget htrue
    have hklt : k < (insA (ground d p rel)).size := hsizeP ▸ hlt
    have hname : a = powerOn (insA (ground d p rel))[k] :=
      powerOn_at (objs_nodup hp rel "instrument") hklt
        (by rw [Array.getElem?_eq_getElem hlt, hget])
    have hne : a ≠ powerOn ins := by
      rw [hname]
      intro hc
      exact ins_ne_of_index (objs_nodup hp rel "instrument") hi hklt hki
        (by simpa [powerOn] using hc)
    exact falls_of_lists hf hadd (by simp [hne]) htrue
  have hpowMono : ∀ j ∈ poweredNow (cfgOf (ground d p rel)) σ,
      j ∈ poweredNow (cfgOf (ground d p rel)) (o.applyA σ) := by
    intro j hj
    obtain ⟨hlt, a, hget, hσa⟩ := mem_activeInstruments.mp hj
    refine mem_activeInstruments.mpr ⟨hlt, a, hget, ?_⟩
    have hjlt : j < (insA (ground d p rel)).size := hsizeP ▸ hlt
    by_cases hji : j = i
    · exfalso
      have hgetD : (cfgOf (ground d p rel)).powerOnAtoms.getD i none = some a := by
        rw [← hji, getD_eq_getElem _ _ hlt, hget]
      rw [powerOn_slot hi hgetD, hoff] at hσa
      exact Bool.noConfusion hσa
    · have hname : a = powerOn (insA (ground d p rel))[j] :=
        powerOn_at (objs_nodup hp rel "instrument") hjlt
          (by rw [Array.getElem?_eq_getElem hlt, hget])
      have hne : a ≠ powerOn ins := by
        rw [hname]
        intro hc
        exact ins_ne_of_index (objs_nodup hp rel "instrument") hi hjlt hji
          (by simpa [powerOn] using hc)
      rw [frame_of_lists hf hadd hdel (by simp [hne]) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro (hc | hc)
        · rw [hname] at hc; exact absurd hc (by simp [powerOn, calibrated])
        · rw [hname] at hc; exact absurd hc (by simp [powerOn, powerAvail])) σ]
      exact hσa
  have hreadyMono : ∀ j ∈ readyNow (cfgOf (ground d p rel)) σ,
      j ∈ readyNow (cfgOf (ground d p rel)) (o.applyA σ) := by
    intro j hj
    simp only [readyNow, Array.mem_filter] at hj ⊢
    have hjne : j ≠ i := by
      intro hc
      exact hinotpow (by rw [← hc]; simpa using hj.2)
    refine ⟨?_, by simpa using hpowMono j (by simpa using hj.2)⟩
    obtain ⟨hlt, a, hget, hσa⟩ := mem_activeInstruments.mp hj.1
    refine mem_activeInstruments.mpr ⟨hlt, a, hget, ?_⟩
    have hjlt : j < (insA (ground d p rel)).size := hsizeC ▸ hlt
    have hname : a = calibrated (insA (ground d p rel))[j] :=
      calibrated_at (objs_nodup hp rel "instrument") hjlt
        (by rw [Array.getElem?_eq_getElem hlt, hget])
    have hne : a ≠ calibrated ins := by
      rw [hname]
      intro hc
      exact ins_ne_of_index (objs_nodup hp rel "instrument") hi hjlt hjne
        (by simpa [calibrated] using hc)
    rw [frame_of_lists hf hadd hdel (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      intro hc
      rw [hname] at hc
      exact absurd hc (by simp [calibrated, powerOn])) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro (hc | hc)
      · exact hne hc
      · rw [hname] at hc; exact absurd hc (by simp [calibrated, powerAvail])) σ]
    exact hσa
  have hreadySub : ∀ j ∈ readyNow (cfgOf (ground d p rel)) (o.applyA σ),
      j = i ∨ j ∈ readyNow (cfgOf (ground d p rel)) σ := by
    intro j hj
    simp only [readyNow, Array.mem_filter] at hj ⊢
    have hc : j ∈ calibratedNow (cfgOf (ground d p rel)) σ :=
      active_mono (active_of_mem_hyp hcalFall) hj.1
    rcases hpowSub j (by simpa using hj.2) with hji | hjp
    · exact Or.inl hji
    · exact Or.inr ⟨hc, by simpa using hjp⟩
  -- the ready set does not move where a needed mode is concerned
  have hkey : ∀ m ∈ neededModes (cfgOf (ground d p rel)) σ, ∀ j,
      ((cfgOf (ground d p rel)).supports.getD j #[]).contains m = true →
      (readyNow (cfgOf (ground d p rel)) (o.applyA σ)).contains j = true →
      (readyNow (cfgOf (ground d p rel)) σ).contains j = true := by
    intro m hm j hjs hjr
    rcases hreadySub j (by simpa using hjr) with hji | hjσ
    · exfalso
      have hneed : NeedsCalib d p rel ins :=
        needsCalib_of hp rel hi hm (by rw [← hji]; exact hjs)
      have hfalse : o.applyA σ (calibrated ins) = false :=
        applyA_del σ (hdelOf ins s hs ha hneed) (by
          intro hc
          have hmem := hf.subAdd _ hc
          rw [hadd] at hmem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          exact absurd hmem (by simp [calibrated, powerOn]))
      have hmemτ : i ∈ calibratedNow (cfgOf (ground d p rel)) (o.applyA σ) := by
        have hjr' : j ∈ readyNow (cfgOf (ground d p rel)) (o.applyA σ) := by simpa using hjr
        simp only [readyNow, Array.mem_filter] at hjr'
        rw [← hji]
        exact hjr'.1
      obtain ⟨hlt, a, hget, hσa⟩ := mem_activeInstruments.mp hmemτ
      have hgetD : (cfgOf (ground d p rel)).calibratedAtoms.getD i none = some a := by
        rw [getD_eq_getElem _ _ hlt, hget]
      rw [calibrated_slot hi hgetD, hfalse] at hσa
      exact Bool.noConfusion hσa
    · simpa using hjσ
  have hsupEq : ∀ m ∈ neededModes (cfgOf (ground d p rel)) σ,
      (!supportsMode (cfgOf (ground d p rel))
          (readyNow (cfgOf (ground d p rel)) (o.applyA σ)) m)
        = (!supportsMode (cfgOf (ground d p rel))
          (readyNow (cfgOf (ground d p rel)) σ) m) := by
    intro m hm
    congr 1
    rcases hτ : supportsMode (cfgOf (ground d p rel))
      (readyNow (cfgOf (ground d p rel)) (o.applyA σ)) m with _ | _
    · rcases hσ2 : supportsMode (cfgOf (ground d p rel))
        (readyNow (cfgOf (ground d p rel)) σ) m with _ | _
      · rfl
      · exfalso
        rw [supportsMode_mono _ (fun j hj => hreadyMono j hj) hσ2] at hτ
        exact Bool.noConfusion hτ
    · obtain ⟨j, hj, hjc⟩ := array_any_elim hτ
      exact (supportsMode_of _ (by simpa using hkey m hm j hjc (by simpa using hj)) hjc).symm
  have hneededEq := neededModes_congr (cfgOf (ground d p rel)) σ (o.applyA σ) himg
  have huncal : uncalibratedModes (cfgOf (ground d p rel)) (o.applyA σ)
      = uncalibratedModes (cfgOf (ground d p rel)) σ := by
    rw [uncalibratedModes, uncalibratedModes, hneededEq]
    exact List.filter_congr hsupEq
  have hup := unmetPointing_array_congr (cfgOf (ground d p rel)) σ (o.applyA σ) hpt
  have hpaidEq : ∀ x, paidByGoal (cfgOf (ground d p rel)) (o.applyA σ) x
      = paidByGoal (cfgOf (ground d p rel)) σ x := by
    intro x; simp only [paidByGoal, hup]
  -- the outstanding directions do not move either
  have hdirsSub : ∀ x ∈ dirsList (cfgOf (ground d p rel)) σ,
      x ∈ dirsList (cfgOf (ground d p rel)) (o.applyA σ) := by
    intro x hx
    obtain ⟨img, hq, hxd, hpaid, hcov⟩ := (mem_dirsList _ σ).mp hx
    refine (mem_dirsList _ (o.applyA σ)).mpr ⟨img, mem_unmetImages_of _ himg hq, hxd, ?_, ?_⟩
    · rw [hpaidEq, hxd] at *; exact hpaid
    · rcases hct : covered (cfgOf (ground d p rel)) (o.applyA σ) x img.mode with _ | _
      · rfl
      · exfalso
        have hcs : covered (cfgOf (ground d p rel)) σ x img.mode = true := by
          refine covered_mono_supp _ σ (o.applyA σ) ?_ ?_ hct
          · intro q hq2 htrue; rw [← hpoints x q hq2]; exact htrue
          · intro j hjs hjr
            exact hkey img.mode (mode_needed _ σ hq) j hjs hjr
        rw [hcs] at hcov
        exact absurd hcov (by simp)
  have hdirsSub' : ∀ x ∈ dirsList (cfgOf (ground d p rel)) (o.applyA σ),
      x ∈ dirsList (cfgOf (ground d p rel)) σ := by
    intro x hx
    obtain ⟨img, hq, hxd, hpaid, hcov⟩ := (mem_dirsList _ (o.applyA σ)).mp hx
    refine (mem_dirsList _ σ).mpr ⟨img, mem_unmetImages_of _ (fun g hg => (himg g hg).symm) hq,
      hxd, ?_, ?_⟩
    · rw [← hpaidEq]; exact hpaid
    · rcases hct : covered (cfgOf (ground d p rel)) σ x img.mode with _ | _
      · rfl
      · exfalso
        have hcs : covered (cfgOf (ground d p rel)) (o.applyA σ) x img.mode = true := by
          refine covered_mono _ (o.applyA σ) σ ?_ ?_ hct
          · intro q hq2 htrue; rw [hpoints x q hq2]; exact htrue
          · intro j hj; simpa using hreadyMono j (by simpa using hj)
        rw [hcs] at hcov
        exact absurd hcov (by simp)
  refine ⟨himg, ?_, ?_⟩
  · -- the power cover count is the one term that may fall
    refine instruments_le_succ _ σ (o.applyA σ) (du := 0) (dp := 1) (df := 0) ?_ ?_ ?_ (by omega)
    · rw [huncal]; omega
    · refine coverCount_le_succ _ _ _ ?_
      intro hempty
      have hilt : i < (cfgOf (ground d p rel)).supports.size := by
        rw [supports_size]; exact (findIdx_sound hi).1
      refine array_any_of_mem (Array.getElem_mem hilt) ?_
      rw [List.all_eq_true]
      intro mm hmm
      rw [unpoweredModes, List.mem_filter] at hmm
      obtain ⟨hneed, hnsup⟩ := hmm
      have hnotτ : mm ∉ unpoweredModes (cfgOf (ground d p rel)) (o.applyA σ) := by
        rw [List.isEmpty_iff] at hempty
        rw [hempty]; simp
      have hsupτ : supportsMode (cfgOf (ground d p rel))
          (poweredNow (cfgOf (ground d p rel)) (o.applyA σ)) mm = true := by
        by_contra hc
        exact hnotτ (by
          rw [unpoweredModes, List.mem_filter]
          exact ⟨by rw [hneededEq]; exact hneed, by simpa using hc⟩)
      obtain ⟨j, hj, hjc⟩ := array_any_elim hsupτ
      rcases hpowSub j hj with hji | hjσ
      · rw [← getD_eq_getElem _ #[] hilt, ← hji]; exact hjc
      · exact absurd (supportsMode_of _ hjσ hjc) (by simpa using hnsup)
    · -- the free slot cannot fall: the instrument is on a satellite whose slot
      -- was free, so it supports no needed mode
      by_cases hfs : freeSlot (cfgOf (ground d p rel)) σ = 0
      · omega
      · have hcond : (!(unpoweredModes (cfgOf (ground d p rel)) σ).isEmpty &&
            !slotFree (cfgOf (ground d p rel)) σ) = true := by
          by_contra hc
          rw [freeSlot, if_neg hc] at hfs
          exact hfs rfl
        obtain ⟨hne, hnsf⟩ : (unpoweredModes (cfgOf (ground d p rel)) σ).isEmpty = false ∧
            slotFree (cfgOf (ground d p rel)) σ = false := by simpa using hcond
        -- the instrument supports no needed mode
        have hnoneed : ∀ m ∈ neededModes (cfgOf (ground d p rel)) σ,
            ((cfgOf (ground d p rel)).supports.getD i #[]).contains m = false := by
          intro m hm
          by_contra hc
          have hilt : i < (cfgOf (ground d p rel)).supports.size := by
            rw [supports_size]; exact (findIdx_sound hi).1
          obtain ⟨f, hflt, hfname⟩ :=
            numbered_of_op d p rel ho (Or.inl (pre_mem_op hf hpa hdynA))
          have hslot : slotFree (cfgOf (ground d p rel)) σ = true := by
            rw [slotFree_eq]
            refine array_any_of_mem (mem_zipIdx_self _ hilt) ?_
            simp only [Bool.and_eq_true]
            have hcon : ((cfgOf (ground d p rel)).supports.getD i #[]).contains m = true := by
              simpa using hc
            refine ⟨by
              rw [← getD_eq_getElem _ #[] hilt]
              exact array_any_of_mem (by simpa using hcon) (by simpa using hm), ?_⟩
            rw [satelliteOf_eq hp rel hi hsi hboardS]
            show availCond σ ((cfgOf (ground d p rel)).powerAvailAtoms.getD si none) = true
            rw [powerAvail_named hsi hflt hfname]
            exact havail
          rw [hnsf] at hslot
          exact Bool.noConfusion hslot
        -- so the unpowered modes do not move, and no slot opens
        have hunpow : unpoweredModes (cfgOf (ground d p rel)) (o.applyA σ)
            = unpoweredModes (cfgOf (ground d p rel)) σ := by
          rw [unpoweredModes, unpoweredModes, hneededEq]
          refine List.filter_congr ?_
          intro m hm
          congr 1
          rcases hτ : supportsMode (cfgOf (ground d p rel))
            (poweredNow (cfgOf (ground d p rel)) (o.applyA σ)) m with _ | _
          · rcases hσ2 : supportsMode (cfgOf (ground d p rel))
              (poweredNow (cfgOf (ground d p rel)) σ) m with _ | _
            · rfl
            · exfalso
              rw [supportsMode_mono _ (fun j hj => hpowMono j hj) hσ2] at hτ
              exact Bool.noConfusion hτ
          · obtain ⟨j, hj, hjc⟩ := array_any_elim hτ
            rcases hpowSub j hj with hji | hjσ
            · exfalso
              rw [hji] at hjc
              rw [hnoneed m hm] at hjc
              exact Bool.noConfusion hjc
            · exact (supportsMode_of _ hjσ hjc).symm
        have hslotτ : slotFree (cfgOf (ground d p rel)) (o.applyA σ) = false := by
          rcases hv : slotFree (cfgOf (ground d p rel)) (o.applyA σ) with _ | _
          · rfl
          · exfalso
            have := slotFree_mono _ σ (o.applyA σ)
              (fun m hm => by rw [← hneededEq]; exact hm) havailFall hv
            rw [hnsf] at this
            exact Bool.noConfusion this
        have hτ1 : freeSlot (cfgOf (ground d p rel)) (o.applyA σ) = 1 := by
          rw [freeSlot, if_pos (by rw [hunpow, hne, hslotτ]; rfl)]
        have hσ1 : freeSlot (cfgOf (ground d p rel)) σ = 1 := by
          rw [freeSlot, if_pos hcond]
        omega
  · -- no turn moves
    refine turns_le_of_parts hpt (dirsToTurn_mono _ σ (o.applyA σ) hdirsSub) ?_
    by_cases hc : (!(uncalibratedModes (cfgOf (ground d p rel)) σ).isEmpty &&
        !calibrationInReach (cfgOf (ground d p rel)) σ) = true
    · obtain ⟨hne, hnr⟩ : (uncalibratedModes (cfgOf (ground d p rel)) σ).isEmpty = false ∧
          calibrationInReach (cfgOf (ground d p rel)) σ = false := by simpa using hc
      have hirFalse : calibrationInReach (cfgOf (ground d p rel)) (o.applyA σ) = false := by
        rcases hir : calibrationInReach (cfgOf (ground d p rel)) (o.applyA σ) with _ | _
        · rfl
        · exfalso
          have := inReach_mono _ σ (o.applyA σ) (fun m hm => by rw [hneededEq] at hm; exact hm)
            (fun sat dir hpts => by
              obtain ⟨q, hq, hqc⟩ := array_any_elim hpts
              refine array_any_of_mem hq ?_
              simp only [Bool.and_eq_true] at hqc ⊢
              exact ⟨hqc.1, by rw [← hpoints dir q hq]; exact hqc.2⟩)
            (fun x hx => by
              have hx' : x ∈ dirsToTurn (cfgOf (ground d p rel)) (o.applyA σ) := by
                simpa using hx
              have hx2 : x ∈ dirsToTurn (cfgOf (ground d p rel)) σ := by
                rw [dirsToTurn_eq, mem_distinct] at hx' ⊢
                exact hdirsSub' x hx'
              simpa using hx2)
            hup hir
          rw [hnr] at this
          exact Bool.noConfusion this
      have hcondτ : (!(uncalibratedModes (cfgOf (ground d p rel)) (o.applyA σ)).isEmpty &&
          !calibrationInReach (cfgOf (ground d p rel)) (o.applyA σ)) = true := by
        rw [huncal, hne, hirFalse]; rfl
      rw [approach, if_pos hc, approach, if_pos hcondτ]
    · rw [approach, if_neg hc]; omega

end Planner.Lifted.Satellite

/- -------------------------------------------------------------------------- -/
/-
`take_image`: the action the image count is about.

Two things have to be said, and the second is what makes the turn terms safe.
The image it takes is one goal, so the count of unmet images falls by exactly
one — that is the `ImageStep`.  And the direction it shot was already *covered*:
the satellite was pointing at it with an instrument that was ready and supported
the mode, which is what `covered` asks for.  So that direction never belonged to
the turn list, and taking the image discharges no turn.

A `take_image` whose atom is no goal of the table — or one already taken, or one
whose add the relevance analysis dropped — moves nothing at all, and is a
`ReadyStep` with every term equal.
-/

namespace Planner.Lifted.Satellite

open Planner Planner.Pddl

variable {d : Domain} {p : Problem}

/-- The image table cannot hold two entries for one atom: the atom fixes both
stored indices. -/
theorem image_goalAtom_inj (rel : Bool) {g q : ImageGoal}
    (hg : g ∈ (cfgOf (ground d p rel)).images)
    (hq : q ∈ (cfgOf (ground d p rel)).images)
    (heq : g.goalAtom = q.goalAtom) : g = q := by
  obtain ⟨dg, mg, hga, hdg, hmg⟩ := image_goal_data (d := d) (p := p) rel g hg
  obtain ⟨dq, mq, hqa, hdq, hmq⟩ := image_goal_data (d := d) (p := p) rel q hq
  have hnames : dg = dq ∧ mg = mq := by
    rw [hga, hqa] at heq
    simpa [haveImage] using heq
  obtain ⟨rfl, rfl⟩ := hnames
  have hdir : g.dir = q.dir := by rw [hdg] at hdq; simpa using hdq
  have hmode : g.mode = q.mode := by rw [hmg] at hmq; simpa using hmq
  cases g
  cases q
  simp_all

/-- One witness is enough to make a direction covered. -/
theorem covered_of (c : Cfg) (σ : AtomState) {x mm si i : Nat} {q : GroundAtom × Nat}
    (hq : q ∈ c.pointingByDir.getD x #[]) (hq2 : q.2 = si) (htrue : σ q.1 = true)
    (hb : i ∈ c.onBoard.getD si #[]) (hsup : (c.supports.getD i #[]).contains mm = true)
    (hready : (readyNow c σ).contains i = true) : covered c σ x mm = true := by
  refine array_any_of_mem hq ?_
  simp only [Bool.and_eq_true]
  refine ⟨htrue, ?_⟩
  refine array_any_of_mem (by rw [hq2]; exact hb) ?_
  simp only [Bool.and_eq_true, Bool.or_eq_true]
  exact ⟨hsup, Or.inl hready⟩

/-! ### The frames a `take_image` keeps -/

theorem image_frames (hp : Pinned d p) (rel : Bool) {o : AtomOp} (hf : OpFacts d p o)
    {s dd ins m : Name} (hs : hf.inst.schema = imageA)
    (ha : hf.inst.args = [s, dd, ins, m]) (σ : AtomState) :
    (∀ g ∈ (cfgOf (ground d p rel)).pointingGoals,
      o.applyA σ g.goalAtom = σ g.goalAtom) ∧
    (∀ a, some a ∈ (cfgOf (ground d p rel)).calibratedAtoms → o.applyA σ a = σ a) ∧
    (∀ a, some a ∈ (cfgOf (ground d p rel)).powerOnAtoms → o.applyA σ a = σ a) ∧
    (∀ a, some a ∈ (cfgOf (ground d p rel)).powerAvailAtoms → o.applyA σ a = σ a) ∧
    (∀ x, ∀ q ∈ (cfgOf (ground d p rel)).pointingByDir.getD x #[],
      o.applyA σ q.1 = σ q.1) := by
  obtain ⟨-, -, -, hadd, hdel⟩ := image_atoms hf.inst hs ha
  have hpred : ∀ b ∈ [haveImage dd m] ++ ([] : List GroundAtom), b.pred = "have_image" := by
    intro b hb
    simp only [List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hb
    rw [hb]
  exact ⟨frame_ptGoals rel hf hadd hdel (fun b hb => by rw [hpred b hb]; decide) σ,
    frame_calib rel hf hadd hdel (fun b hb => by rw [hpred b hb]; decide) σ,
    frame_power rel hf hadd hdel (fun b hb => by rw [hpred b hb]; decide) σ,
    frame_avail rel hf hadd hdel (fun b hb => by rw [hpred b hb]; decide) σ,
    frame_points hp rel hf hadd hdel (fun b hb => by rw [hpred b hb]; decide) σ⟩

/-- **A `take_image` that meets no image goal moves nothing the value reads.** -/
theorem image_stall_ready (hp : Pinned d p) (rel : Bool) {o : AtomOp} (hf : OpFacts d p o)
    {s dd ins m : Name} (hs : hf.inst.schema = imageA)
    (ha : hf.inst.args = [s, dd, ins, m]) {σ : AtomState}
    (himg : ∀ g ∈ (cfgOf (ground d p rel)).images,
      o.applyA σ g.goalAtom = σ g.goalAtom) :
    ReadyStep (cfgOf (ground d p rel)) σ (o.applyA σ) := by
  obtain ⟨hpt, hcal, hpow, havail, hpoints⟩ := image_frames hp rel hf hs ha σ
  have hready : readyNow (cfgOf (ground d p rel)) (o.applyA σ)
      = readyNow (cfgOf (ground d p rel)) σ := readyNow_congr _ σ _ hcal hpow
  have hinstr : instruments (cfgOf (ground d p rel)) (o.applyA σ)
      = instruments (cfgOf (ground d p rel)) σ :=
    instruments_congr _ σ _ himg hcal hpow havail
  have hneededEq := neededModes_congr (cfgOf (ground d p rel)) σ (o.applyA σ) himg
  have hup := unmetPointing_array_congr (cfgOf (ground d p rel)) σ (o.applyA σ) hpt
  have hpaidEq : ∀ x, paidByGoal (cfgOf (ground d p rel)) (o.applyA σ) x
      = paidByGoal (cfgOf (ground d p rel)) σ x := by
    intro x; simp only [paidByGoal, hup]
  have hcovEq : ∀ x mm, covered (cfgOf (ground d p rel)) (o.applyA σ) x mm
      = covered (cfgOf (ground d p rel)) σ x mm := by
    intro x mm
    rcases hv : covered (cfgOf (ground d p rel)) (o.applyA σ) x mm with _ | _
    · rcases hw : covered (cfgOf (ground d p rel)) σ x mm with _ | _
      · rfl
      · rw [covered_mono _ (o.applyA σ) σ (fun q hq htrue => by rw [hpoints x q hq]; exact htrue)
          (fun j hj => by rw [hready]; exact hj) hw] at hv
        exact absurd hv (by simp)
    · rw [covered_mono _ σ (o.applyA σ) (fun q hq htrue => by rw [← hpoints x q hq]; exact htrue)
        (fun j hj => by rw [hready] at hj; exact hj) hv]
  have hdirsEq : ∀ x, x ∈ dirsList (cfgOf (ground d p rel)) σ ↔
      x ∈ dirsList (cfgOf (ground d p rel)) (o.applyA σ) := by
    intro x
    constructor
    · intro hx
      obtain ⟨img, hq, hxd, hpaid, hcov⟩ := (mem_dirsList _ σ).mp hx
      exact (mem_dirsList _ (o.applyA σ)).mpr ⟨img, mem_unmetImages_of _ himg hq, hxd,
        by rw [hpaidEq, hxd] at *; exact hpaid, by rw [hcovEq]; exact hcov⟩
    · intro hx
      obtain ⟨img, hq, hxd, hpaid, hcov⟩ := (mem_dirsList _ (o.applyA σ)).mp hx
      refine (mem_dirsList _ σ).mpr ⟨img,
        mem_unmetImages_of _ (fun g hg => (himg g hg).symm) hq, hxd, ?_, ?_⟩
      · rw [← hpaidEq]; exact hpaid
      · rw [← hcovEq]; exact hcov
  have huncal : uncalibratedModes (cfgOf (ground d p rel)) (o.applyA σ)
      = uncalibratedModes (cfgOf (ground d p rel)) σ := by
    rw [uncalibratedModes, uncalibratedModes, hneededEq, hready]
  have hreach : ∀ (A B : AtomState), (∀ g ∈ (cfgOf (ground d p rel)).images, B g.goalAtom = A g.goalAtom) →
      True := fun _ _ _ => trivial
  refine ⟨himg, by omega, ?_⟩
  refine turns_le_of_parts hpt
    (length_distinct_mono _ _ (fun x hx => (hdirsEq x).mp hx)) ?_
  by_cases hc : (!(uncalibratedModes (cfgOf (ground d p rel)) σ).isEmpty &&
      !calibrationInReach (cfgOf (ground d p rel)) σ) = true
  · obtain ⟨hne, hnr⟩ : (uncalibratedModes (cfgOf (ground d p rel)) σ).isEmpty = false ∧
        calibrationInReach (cfgOf (ground d p rel)) σ = false := by simpa using hc
    have hirFalse : calibrationInReach (cfgOf (ground d p rel)) (o.applyA σ) = false := by
      rcases hir : calibrationInReach (cfgOf (ground d p rel)) (o.applyA σ) with _ | _
      · rfl
      · exfalso
        have := inReach_mono _ σ (o.applyA σ) (fun mm hm => by rw [hneededEq] at hm; exact hm)
          (fun sat dir hpts => by
            obtain ⟨q, hq, hqc⟩ := array_any_elim hpts
            refine array_any_of_mem hq ?_
            simp only [Bool.and_eq_true] at hqc ⊢
            exact ⟨hqc.1, by rw [← hpoints dir q hq]; exact hqc.2⟩)
          (fun x hx => by
            have hx' : x ∈ dirsToTurn (cfgOf (ground d p rel)) (o.applyA σ) := by simpa using hx
            have hx2 : x ∈ dirsToTurn (cfgOf (ground d p rel)) σ := by
              rw [dirsToTurn_eq, mem_distinct] at hx' ⊢
              exact (hdirsEq x).mpr hx'
            simpa using hx2)
          hup hir
        rw [hnr] at this
        exact Bool.noConfusion this
    have hcondτ : (!(uncalibratedModes (cfgOf (ground d p rel)) (o.applyA σ)).isEmpty &&
        !calibrationInReach (cfgOf (ground d p rel)) (o.applyA σ)) = true := by
      rw [huncal, hne, hirFalse]; rfl
    rw [approach, if_pos hc, approach, if_pos hcondτ]
  · rw [approach, if_neg hc]; omega

end Planner.Lifted.Satellite

/- -------------------------------------------------------------------------- -/
/-
The closed Satellite proof.

The preceding files establish the table facts, invariant, and the individual
instrument-action arguments.  This file discharges the two interactions left
at that boundary: taking an image may remove its last needed mode, and turning
may move both deployed turn counters at once.  It then assembles the schema cases
for every grounded operator.
-/

namespace Planner.Lifted.Satellite

open Planner Planner.Pddl

/-! ### Two finite-set exchanges used by the turn proof -/

private theorem length_lt_of_subset_extra {α : Type} [DecidableEq α]
    (l l' : List α) (hnd : l.Nodup) (hsub : ∀ x ∈ l, x ∈ l')
    {y : α} (hy : y ∈ l') (hny : y ∉ l) : l.length + 1 ≤ l'.length := by
  have hsub' : ∀ x ∈ l, x ∈ l'.erase y := by
    intro x hx
    have hxy : x ≠ y := by
      intro heq
      subst x
      exact hny hx
    exact (List.mem_erase_of_ne hxy).mpr (hsub x hx)
  have hlen := length_le_of_subset' l (l'.erase y) hnd hsub'
  rw [List.length_erase_of_mem hy] at hlen
  have hpos : 0 < l'.length := List.length_pos_of_mem hy
  omega

private theorem not_mem_erase_of_nodup {α : Type} [DecidableEq α] (a : α) :
    ∀ l : List α, l.Nodup → a ∉ l.erase a := by
  intro l hnd
  induction l with
  | nil => simp
  | cons x xs ih =>
      by_cases hxa : x = a
      · subst x
        simpa using hnd.notMem
      · simp only [List.erase]
        have hbeq : (x == a) = false := by simpa using hxa
        rw [hbeq]
        simp only [List.mem_cons, not_or]
        exact ⟨(fun h => hxa h.symm), ih hnd.of_cons⟩

/-- A filtered finite set may lose one distinguished element and gain a fresh
one without becoming smaller. -/
private theorem filter_exchange {α : Type} [DecidableEq α]
    (l : List α) (P Q : α → Bool) (a b : α) (hnd : l.Nodup)
    (hb : b ∈ l) (hPb : P b = false) (hQb : Q b = true)
    (hsub : ∀ x ∈ l, P x = true → Q x = true ∨ x = a) :
    (l.filter P).length ≤ (l.filter Q).length := by
  by_cases ha : a ∈ l.filter P
  · have hsub' : ∀ x ∈ (l.filter P).erase a, x ∈ l.filter Q := by
      intro x hx
      have hxP : x ∈ l.filter P := List.mem_of_mem_erase hx
      obtain ⟨hxl, hpx⟩ := List.mem_filter.mp hxP
      rcases hsub x hxl hpx with hqx | hxa
      · exact List.mem_filter.mpr ⟨hxl, hqx⟩
      · subst x
        exact absurd hx (not_mem_erase_of_nodup a _ (hnd.filter _))
    have hnotb : b ∉ (l.filter P).erase a := by
      intro hbmem
      have := (List.mem_filter.mp (List.mem_of_mem_erase hbmem)).2
      rw [hPb] at this
      exact Bool.noConfusion this
    have hlt := length_lt_of_subset_extra ((l.filter P).erase a) (l.filter Q)
      ((hnd.filter _).erase _) hsub' (List.mem_filter.mpr ⟨hb, hQb⟩) hnotb
    rw [List.length_erase_of_mem ha] at hlt
    have hpos : 0 < (l.filter P).length := List.length_pos_of_mem ha
    omega
  · exact length_le_of_subset' (l.filter P) (l.filter Q) (hnd.filter _)
      (fun x hx => by
        obtain ⟨hxl, hpx⟩ := List.mem_filter.mp hx
        rcases hsub x hxl hpx with hqx | rfl
        · exact List.mem_filter.mpr ⟨hxl, hqx⟩
        · exact absurd hx ha)

/-- If the possible loss is absent, the fresh gain makes the filtered set
strictly larger. -/
private theorem filter_gain {α : Type} [DecidableEq α]
    (l : List α) (P Q : α → Bool) (a b : α) (hnd : l.Nodup)
    (ha : P a = false) (hb : b ∈ l) (hPb : P b = false) (hQb : Q b = true)
    (hsub : ∀ x ∈ l, P x = true → Q x = true ∨ x = a) :
    (l.filter P).length + 1 ≤ (l.filter Q).length := by
  have hsubset : ∀ x ∈ l.filter P, x ∈ l.filter Q := by
    intro x hx
    obtain ⟨hxl, hpx⟩ := List.mem_filter.mp hx
    rcases hsub x hxl hpx with hqx | hxa
    · exact List.mem_filter.mpr ⟨hxl, hqx⟩
    · subst x
      rw [ha] at hpx
      exact Bool.noConfusion hpx
  have hbnot : b ∉ l.filter P := by
    intro h
    have := (List.mem_filter.mp h).2
    rw [hPb] at this
    exact Bool.noConfusion this
  exact length_lt_of_subset_extra (l.filter P) (l.filter Q) (hnd.filter _)
    hsubset (List.mem_filter.mpr ⟨hb, hQb⟩) hbnot

/-! ### Removing one met image -/

variable {c : Cfg} {q : ImageGoal} {σ τ : AtomState}

/-- Every mode needed after one image is taken was needed before. -/
theorem neededModes_sub_of_image
    (hq : q ∈ c.images) (hbefore : σ q.goalAtom = false)
    (hframe : ∀ g ∈ c.images, g ≠ q → τ g.goalAtom = σ g.goalAtom) :
    ∀ m ∈ neededModes c τ, m ∈ neededModes c σ := by
  intro m hm
  rw [neededModes, mem_distinct, List.mem_map] at hm ⊢
  obtain ⟨g, hg, rfl⟩ := hm
  have hgA : g ∈ unmetImages c τ := by simpa using hg
  simp only [unmetImages, Array.mem_filter] at hgA
  refine ⟨g, ?_, rfl⟩
  have : g ∈ unmetImages c σ := by
    simp only [unmetImages, Array.mem_filter]
    refine ⟨hgA.1, ?_⟩
    by_cases heq : g = q
    · subst g; simp [hbefore]
    · rw [← hframe g hgA.1 heq]
      exact hgA.2
  simpa using this

/-- A needed mode other than the photographed mode stays needed. -/
theorem neededModes_of_ne_image
    (hq : q ∈ c.images) (hafter : τ q.goalAtom = true)
    (hinj : ∀ g ∈ c.images, g.goalAtom = q.goalAtom → g = q)
    (hframe : ∀ g ∈ c.images, g ≠ q → τ g.goalAtom = σ g.goalAtom) :
    ∀ m ∈ neededModes c σ, m ≠ q.mode → m ∈ neededModes c τ := by
  intro m hm hmq
  rw [neededModes, mem_distinct, List.mem_map] at hm ⊢
  obtain ⟨g, hg, hgm⟩ := hm
  have hgA : g ∈ unmetImages c σ := by simpa using hg
  simp only [unmetImages, Array.mem_filter] at hgA
  refine ⟨g, ?_, hgm⟩
  have : g ∈ unmetImages c τ := by
    simp only [unmetImages, Array.mem_filter]
    refine ⟨hgA.1, ?_⟩
    have hne : g ≠ q := by
      intro heq
      subst g
      exact hmq hgm.symm
    rw [hframe g hgA.1 hne]
    exact hgA.2
  simpa using this

/-- If the photographed mode was already supported, the unsupported-mode
lists can only grow.  This is the direction required by consistency. -/
theorem unsupported_mono_of_image
    (hq : q ∈ c.images) (hbefore : σ q.goalAtom = false)
    (hafter : τ q.goalAtom = true)
    (hinj : ∀ g ∈ c.images, g.goalAtom = q.goalAtom → g = q)
    (hframe : ∀ g ∈ c.images, g ≠ q → τ g.goalAtom = σ g.goalAtom)
    (hready : readyNow c τ = readyNow c σ)
    (hpow : poweredNow c τ = poweredNow c σ)
    (hsReady : supportsMode c (readyNow c σ) q.mode = true)
    (hsPow : supportsMode c (poweredNow c σ) q.mode = true) :
    (∀ m ∈ uncalibratedModes c σ, m ∈ uncalibratedModes c τ) ∧
      (∀ m ∈ unpoweredModes c σ, m ∈ unpoweredModes c τ) := by
  have hkeep := neededModes_of_ne_image hq hafter hinj hframe
  constructor
  · intro m hm
    rw [uncalibratedModes, List.mem_filter] at hm ⊢
    obtain ⟨hneed, hns⟩ := hm
    have hne : m ≠ q.mode := by
      intro heq
      subst m
      rw [hsReady] at hns
      exact Bool.noConfusion hns
    exact ⟨hkeep m hneed hne, by rw [hready]; exact hns⟩
  · intro m hm
    rw [unpoweredModes, List.mem_filter] at hm ⊢
    obtain ⟨hneed, hns⟩ := hm
    have hne : m ≠ q.mode := by
      intro heq
      subst m
      rw [hsPow] at hns
      exact Bool.noConfusion hns
    exact ⟨hkeep m hneed hne, by rw [hpow]; exact hns⟩

set_option maxHeartbeats 1000000 in
/-- The two non-image parts of the value cannot fall when a photograph is
taken with an already ready instrument at an already covered direction. -/
theorem image_noncount_mono
    (hq : q ∈ c.images) (hbefore : σ q.goalAtom = false)
    (hafter : τ q.goalAtom = true)
    (hinj : ∀ g ∈ c.images, g.goalAtom = q.goalAtom → g = q)
    (hframe : ∀ g ∈ c.images, g ≠ q → τ g.goalAtom = σ g.goalAtom)
    (hpt : ∀ g ∈ c.pointingGoals, τ g.goalAtom = σ g.goalAtom)
    (hcal : ∀ a, some a ∈ c.calibratedAtoms → τ a = σ a)
    (hpow : ∀ a, some a ∈ c.powerOnAtoms → τ a = σ a)
    (havail : ∀ a, some a ∈ c.powerAvailAtoms → τ a = σ a)
    (hpoints : ∀ x, ∀ z ∈ c.pointingByDir.getD x #[], τ z.1 = σ z.1)
    (hcovered : covered c σ q.dir q.mode = true)
    (hsReady : supportsMode c (readyNow c σ) q.mode = true)
    (hsPow : supportsMode c (poweredNow c σ) q.mode = true) :
    instruments c σ ≤ instruments c τ ∧ turns c σ ≤ turns c τ := by
  have hreadyEq := readyNow_congr c σ τ hcal hpow
  have hpowEq := poweredNow_congr c σ τ hpow
  have hneedSub := neededModes_sub_of_image hq hbefore hframe
  obtain ⟨huncalSub, hunpowSub⟩ := unsupported_mono_of_image hq hbefore hafter hinj
    hframe hreadyEq hpowEq hsReady hsPow
  have hcoverU := coverCount_mono c huncalSub
  have hcoverP := coverCount_mono c hunpowSub
  have hslot : freeSlot c σ ≤ freeSlot c τ := by
    by_cases hold : freeSlot c σ = 0
    · omega
    · have hold1 : freeSlot c σ = 1 := by
        have := freeSlot_le_one c σ
        omega
      have hcond : (!(unpoweredModes c σ).isEmpty && !slotFree c σ) = true := by
        by_contra hc
        rw [freeSlot, if_neg hc] at hold1
        contradiction
      obtain ⟨hne, hsf⟩ : (unpoweredModes c σ).isEmpty = false ∧
          slotFree c σ = false := by simpa using hcond
      obtain ⟨m, hm⟩ : ∃ m, m ∈ unpoweredModes c σ := by
        rcases hl : unpoweredModes c σ with _ | ⟨m, ms⟩
        · rw [hl] at hne; simp at hne
        · exact ⟨m, by simpa [hl]⟩
      have hne' : (unpoweredModes c τ).isEmpty = false := by
        rcases hl : unpoweredModes c τ with _ | ⟨z, zs⟩
        · have := hunpowSub m hm
          rw [hl] at this
          simp at this
        · rfl
      have hsf' : slotFree c τ = false := by
        rcases hs : slotFree c τ with _ | _
        · rfl
        · have hs0 := slotFree_mono c σ τ hneedSub
            (fun a ha ht => by rw [← havail a ha]; exact ht) hs
          rw [hsf] at hs0
          exact Bool.noConfusion hs0
      have hnew1 : freeSlot c τ = 1 := by
        rw [freeSlot, if_pos (by rw [hne', hsf']; rfl)]
      omega
  have hinstr : instruments c σ ≤ instruments c τ := by
    unfold instruments
    omega
  have hup := unmetPointing_array_congr c σ τ hpt
  have hpaidEq : ∀ x, paidByGoal c τ x = paidByGoal c σ x := by
    intro x; simp only [paidByGoal, hup]
  have hready : readyNow c τ = readyNow c σ := hreadyEq
  have hcovEq : ∀ x m, covered c τ x m = covered c σ x m := by
    intro x m
    rcases ht : covered c τ x m with _ | _
    · rcases hs : covered c σ x m with _ | _
      · rfl
      · have := covered_mono c τ σ
          (fun z hz hztrue => by rw [hpoints x z hz]; exact hztrue)
          (fun i hi => by rw [← hready] at hi; exact hi) hs
        rw [ht] at this
        exact Bool.noConfusion this
    · have := covered_mono c σ τ
        (fun z hz hztrue => by rw [← hpoints x z hz]; exact hztrue)
        (fun i hi => by rw [hready] at hi; exact hi) ht
      rw [this]
  have hdirs : ∀ x ∈ dirsList c σ, x ∈ dirsList c τ := by
    intro x hx
    obtain ⟨g, hg, hdir, hpaid, hcov⟩ := (mem_dirsList c σ).mp hx
    have hne : g ≠ q := by
      intro heq
      subst g
      rw [← hdir, hcovered] at hcov
      exact Bool.noConfusion hcov
    have hgmem : g ∈ c.images := (Array.mem_filter.mp hg).1
    have hg' : g ∈ unmetImages c τ := by
      simp only [unmetImages, Array.mem_filter]
      refine ⟨hgmem, ?_⟩
      rw [hframe g hgmem hne]
      exact (Array.mem_filter.mp hg).2
    exact (mem_dirsList c τ).mpr ⟨g, hg', hdir,
      by rw [hpaidEq, hdir] at *; exact hpaid, by rw [hcovEq]; exact hcov⟩
  have hdirsBack : ∀ x ∈ dirsList c τ, x ∈ dirsList c σ := by
    intro x hx
    obtain ⟨g, hg, hdir, hpaid, hcov⟩ := (mem_dirsList c τ).mp hx
    have hgmem : g ∈ c.images := (Array.mem_filter.mp hg).1
    have hne : g ≠ q := by
      intro heq
      subst g
      have := (Array.mem_filter.mp hg).2
      simp [hafter] at this
    have hg' : g ∈ unmetImages c σ := by
      simp only [unmetImages, Array.mem_filter]
      refine ⟨hgmem, ?_⟩
      rw [← hframe g hgmem hne]
      exact (Array.mem_filter.mp hg).2
    exact (mem_dirsList c σ).mpr ⟨g, hg', hdir,
      by rw [← hpaidEq, hdir] at *; exact hpaid, by rw [← hcovEq]; exact hcov⟩
  have hdirLen := dirsToTurn_mono c σ τ hdirs
  have happ : approach c σ ≤ approach c τ := by
    by_cases hle : approach c σ ≤ approach c τ
    · exact hle
    · have hσ1 : approach c σ = 1 := by
        have := approach_le_two c σ
        have := approach_le_two c τ
        omega
      have hcond : (!(uncalibratedModes c σ).isEmpty &&
          !calibrationInReach c σ) = true := by
        by_contra hc
        rw [approach, if_neg hc] at hσ1
        contradiction
      obtain ⟨hne, hreach⟩ : (uncalibratedModes c σ).isEmpty = false ∧
          calibrationInReach c σ = false := by simpa using hcond
      obtain ⟨m, hm⟩ : ∃ m, m ∈ uncalibratedModes c σ := by
        rcases hl : uncalibratedModes c σ with _ | ⟨m, ms⟩
        · rw [hl] at hne; simp at hne
        · exact ⟨m, by simpa [hl]⟩
      have hne' : (uncalibratedModes c τ).isEmpty = false := by
        rcases hl : uncalibratedModes c τ with _ | ⟨z, zs⟩
        · have := huncalSub m hm
          rw [hl] at this
          simp at this
        · rfl
      have hreach' : calibrationInReach c τ = false := by
        rcases hr : calibrationInReach c τ with _ | _
        · rfl
        · have hr0 := inReach_mono c σ τ hneedSub
            (fun sat dir hpts => by
              obtain ⟨z, hz, hzc⟩ := array_any_elim hpts
              refine array_any_of_mem hz ?_
              simp only [Bool.and_eq_true] at hzc ⊢
              exact ⟨hzc.1, by rw [← hpoints dir z hz]; exact hzc.2⟩)
            (fun x hx => by
              have hxmem : x ∈ dirsToTurn c τ := by simpa using hx
              have hxlist : x ∈ dirsList c τ := by
                rw [dirsToTurn_eq, mem_distinct] at hxmem
                exact hxmem
              have hout : x ∈ dirsToTurn c σ := by
                rw [dirsToTurn_eq, mem_distinct]
                exact hdirsBack x hxlist
              simpa using hout) hup hr
          rw [hreach] at hr0
          exact Bool.noConfusion hr0
      have hτ1 : approach c τ = 1 := by
        rw [approach, if_pos (by rw [hne', hreach']; rfl)]
      omega
  refine ⟨hinstr, ?_⟩
  exact turns_le_of_parts hpt hdirLen happ

/-! ### The concrete `take_image` case -/

variable {d : Domain} {p : Problem}

/-- The preconditions of `take_image`, read through the compiled tables, say
exactly that its mode is supported by a ready powered instrument and its
direction is already covered. -/
theorem image_prepared (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (ho : o ∈ groundedOps d p rel) (hf : OpFacts d p o)
    {s dd ins m : Name} (hs : hf.inst.schema = imageA)
    (ha : hf.inst.args = [s, dd, ins, m]) {σ : AtomState}
    (happ : o.applicableA σ) {q : ImageGoal}
    (hq : q ∈ (cfgOf (ground d p rel)).images)
    (hqa : q.goalAtom = haveImage dd m) :
    covered (cfgOf (ground d p rel)) σ q.dir q.mode = true ∧
      supportsMode (cfgOf (ground d p rel))
        (readyNow (cfgOf (ground d p rel)) σ) q.mode = true ∧
      supportsMode (cfgOf (ground d p rel))
        (poweredNow (cfgOf (ground d p rel)) σ) q.mode = true := by
  let t := ground d p rel
  let c := cfgOf t
  obtain ⟨si, di, i, mi, hsi, hdi, hi, hmi⟩ := image_indices hp rel hf hs ha
  obtain ⟨dn, mn, hqatom, hqdi, hqmi⟩ := image_goal_data rel q hq
  have hnames : dn = dd ∧ mn = m := by
    rw [hqatom] at hqa
    simpa [haveImage] using hqa
  rcases hnames with ⟨rfl, rfl⟩
  have hdi' : Array.findIdx? (fun x => x == dn)
      ((ground d p rel).objectsOfTypes ["direction"]) = some di := hdi
  have hmi' : Array.findIdx? (fun x => x == mn)
      ((ground d p rel).objectsOfTypes ["mode"]) = some mi := hmi
  have hqdir : q.dir = di := by rw [hdi'] at hqdi; simpa using hqdi.symm
  have hqmode : q.mode = mi := by rw [hmi'] at hqmi; simpa using hqmi.symm
  obtain ⟨hpreCal, hprePow, hprePt, -, -⟩ := image_atoms hf.inst hs ha
  have hcalTrue : σ (calibrated ins) = true := pre_holds hf hpreCal
    (by simpa [calibrated] using calibrated_dynamic hp.domain) happ
  have hpowTrue : σ (powerOn ins) = true := pre_holds hf hprePow
    (by simpa [powerOn] using powerOn_dynamic hp.domain) happ
  have hptTrue : σ (pointing s dn) = true := pre_holds hf hprePt
    (by simpa [pointing] using pointing_dynamic hp.domain) happ
  obtain ⟨fcal, hfcal, hncal⟩ := numbered_of_op d p rel ho
    (Or.inl (pre_mem_op hf hpreCal (by simpa [calibrated] using calibrated_dynamic hp.domain)))
  obtain ⟨fpow, hfpow, hnpow⟩ := numbered_of_op d p rel ho
    (Or.inl (pre_mem_op hf hprePow (by simpa [powerOn] using powerOn_dynamic hp.domain)))
  obtain ⟨fpt, hfpt, hnpt⟩ := numbered_of_op d p rel ho
    (Or.inl (pre_mem_op hf hprePt (by simpa [pointing] using pointing_dynamic hp.domain)))
  have hcalSlot := calibrated_named (t := t) hi hfcal hncal
  have hpowSlot := powerOn_named (t := t) hi hfpow hnpow
  have hcalLt : i < c.calibratedAtoms.size := by
    dsimp [c, t]
    rw [calibratedAtoms_eq]
    simp only [optTable, Array.size_map]
    exact (findIdx_sound hi).1
  have hpowLt : i < c.powerOnAtoms.size := by
    dsimp [c, t]
    rw [powerOnAtoms_eq]
    simp only [optTable, Array.size_map]
    exact (findIdx_sound hi).1
  have hcalMem : i ∈ calibratedNow c σ := by
    apply mem_activeInstruments.mpr
    refine ⟨hcalLt, calibrated ins, ?_, hcalTrue⟩
    rw [← getD_eq_getElem c.calibratedAtoms none hcalLt]
    exact hcalSlot
  have hpowMem : i ∈ poweredNow c σ := by
    apply mem_activeInstruments.mpr
    refine ⟨hpowLt, powerOn ins, ?_, hpowTrue⟩
    rw [← getD_eq_getElem c.powerOnAtoms none hpowLt]
    exact hpowSlot
  have hreadyMem : i ∈ readyNow c σ := by
    simp only [readyNow, Array.mem_filter]
    exact ⟨hcalMem, by simpa using hpowMem⟩
  have hpreEq := image_pre_eq hf.inst hs ha
  have hboardS : onBoard ins s ∈ t.staticWith "on_board" :=
    static_of_pre (a := onBoard ins s) hp rel hf (by rw [hpreEq]; simp)
      (by simpa [onBoard] using hp.onBoardStatic)
  have hsupportS : supports ins mn ∈ t.staticWith "supports" :=
    static_of_pre (a := supports ins mn) hp rel hf (by rw [hpreEq]; simp)
      (by simpa [supports] using hp.supportsStatic)
  have hboard : i ∈ c.onBoard.getD si #[] := mem_onBoard hi hsi hboardS
  have hsupport : mi ∈ c.supports.getD i #[] := mem_supports hi hmi hsupportS
  have hpointEntry : (pointing s dn, si) ∈ c.pointingByDir.getD di #[] :=
    mem_pointingByDir hsi hdi hfpt hnpt
  have hcovered : covered c σ di mi = true :=
    covered_of c σ hpointEntry rfl hptTrue hboard (by simpa using hsupport)
      (by simpa using hreadyMem)
  have hsready : supportsMode c (readyNow c σ) mi = true := by
    exact array_any_of_mem hreadyMem (by simpa using hsupport)
  have hspow : supportsMode c (poweredNow c σ) mi = true := by
    exact array_any_of_mem hpowMem (by simpa using hsupport)
  simpa [c, t, hqdir, hqmode] using And.intro hcovered (And.intro hsready hspow)

set_option maxHeartbeats 1000000 in
/-- **Every `take_image` operator has one of the value's schema shapes.**  If
its add was pruned, is not a goal, or was already true, it is a stuttering
`ReadyStep`; otherwise it is the unique `ImageStep` for that goal. -/
theorem image_schemaStep (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (ho : o ∈ groundedOps d p rel) (hf : OpFacts d p o)
    {s dd ins m : Name} (hs : hf.inst.schema = imageA)
    (ha : hf.inst.args = [s, dd, ins, m]) {σ : AtomState}
    (happ : o.applicableA σ) :
    SchemaStep (cfgOf (ground d p rel)) σ (o.applyA σ) := by
  let c := cfgOf (ground d p rel)
  obtain ⟨-, -, -, hadd, hdel⟩ := image_atoms hf.inst hs ha
  have hother : ∀ g ∈ c.images, g.goalAtom ≠ haveImage dd m →
      o.applyA σ g.goalAtom = σ g.goalAtom := by
    intro g hg hne
    exact frame_of_lists hf hadd hdel (by simpa [hne]) (by simp) σ
  by_cases hex : ∃ q ∈ c.images, q.goalAtom = haveImage dd m
  · obtain ⟨q, hq, hqa⟩ := hex
    have hinj : ∀ g ∈ c.images, g.goalAtom = q.goalAtom → g = q := by
      intro g hg heq
      exact image_goalAtom_inj rel hg hq heq
    by_cases hbefore : σ q.goalAtom = false
    · by_cases hafter : o.applyA σ q.goalAtom = true
      · obtain ⟨hpt, hcal, hpow, havail, hpoints⟩ := image_frames hp rel hf hs ha σ
        obtain ⟨hcovered, hsready, hspow⟩ :=
          image_prepared hp rel ho hf hs ha happ hq hqa
        have hframe : ∀ g ∈ c.images, g ≠ q →
            o.applyA σ g.goalAtom = σ g.goalAtom := by
          intro g hg hne
          exact hother g hg (fun heq => hne (hinj g hg (heq.trans hqa.symm)))
        obtain ⟨hinstr, hturns⟩ := image_noncount_mono hq hbefore hafter hinj hframe
          hpt hcal hpow havail hpoints hcovered hsready hspow
        exact .image q
          { memQ := hq, unmetQ := hbefore, metQ' := hafter,
            frameImages := hframe, instrumentsLe := hinstr, turnsLe := hturns }
      · have hframe : ∀ g ∈ c.images,
            o.applyA σ g.goalAtom = σ g.goalAtom := by
          intro g hg
          by_cases heq : g = q
          · subst g
            have hafter' : o.applyA σ q.goalAtom = false := by simpa using hafter
            rw [hbefore, hafter']
          · exact hother g hg (fun hatom => heq (hinj g hg (hatom.trans hqa.symm)))
        exact .ready (image_stall_ready hp rel hf hs ha hframe)
    · have hbefore' : σ q.goalAtom = true := by
        cases hv : σ q.goalAtom <;> simp_all
      have hqAfter : o.applyA σ q.goalAtom = true := by
        obtain ⟨-, -, -, -, hdel0⟩ := image_atoms hf.inst hs ha
        exact applyA_mono_nodel hf hdel0 hbefore'
      have hframe : ∀ g ∈ c.images,
          o.applyA σ g.goalAtom = σ g.goalAtom := by
        intro g hg
        by_cases heq : g = q
        · subst g; rw [hbefore', hqAfter]
        · exact hother g hg (fun hatom => heq (hinj g hg (hatom.trans hqa.symm)))
      exact .ready (image_stall_ready hp rel hf hs ha hframe)
  · have hframe : ∀ g ∈ c.images,
        o.applyA σ g.goalAtom = σ g.goalAtom := by
      intro g hg
      exact hother g hg (fun heq => hex ⟨g, hg, heq⟩)
    exact .ready (image_stall_ready hp rel hf hs ha hframe)

/-! ### The concrete `turn_to` case -/

/-- Making an old pointing goal unmet pays for the one possible new pointing
goal that a turn can meet.  If the new direction paid for no goal before the
turn, the unmet-goal count grows strictly. -/
theorem turn_unmet_exchange (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (hf : OpFacts d p o) {s dn dp : Name}
    (hs : hf.inst.schema = turnA) (ha : hf.inst.args = [s, dn, dp])
    (σ : AtomState) {qold : PointingGoal}
    (hqold : qold ∈ (cfgOf (ground d p rel)).pointingGoals)
    (hqatom : qold.goalAtom = pointing s dp)
    (hbefore : σ qold.goalAtom = true)
    (hafter : o.applyA σ qold.goalAtom = false)
    {dni : Nat}
    (hdni : ((ground d p rel).objectsOfTypes ["direction"]).findIdx?
      (· == dn) = some dni) :
    (unmetPointing (cfgOf (ground d p rel)) σ).size ≤
        (unmetPointing (cfgOf (ground d p rel)) (o.applyA σ)).size ∧
      (paidByGoal (cfgOf (ground d p rel)) σ dni = false →
        (unmetPointing (cfgOf (ground d p rel)) σ).size + 1 ≤
          (unmetPointing (cfgOf (ground d p rel)) (o.applyA σ)).size) := by
  classical
  let c := cfgOf (ground d p rel)
  change (unmetPointing c σ).size ≤ (unmetPointing c (o.applyA σ)).size ∧
    (paidByGoal c σ dni = false →
      (unmetPointing c σ).size + 1 ≤ (unmetPointing c (o.applyA σ)).size)
  have hnd : c.pointingGoals.toList.Nodup := pointing_nodup hp rel
  have hbP : livePt σ qold = false := by simp [livePt, hbefore]
  have hbQ : livePt (o.applyA σ) qold = true := by simp [livePt, hafter]
  by_cases hex : ∃ qnew ∈ c.pointingGoals, qnew.goalAtom = pointing s dn
  · obtain ⟨qnew, hqnew, hqnewAtom⟩ := hex
    have hsub : ∀ g ∈ c.pointingGoals.toList, livePt σ g = true →
        livePt (o.applyA σ) g = true ∨ g = qnew := by
      intro g hg hlive
      have hgA : g ∈ c.pointingGoals := by simpa using hg
      by_cases heq : g.goalAtom = pointing s dn
      · exact Or.inr (pointing_goalAtom_inj rel hgA hqnew (heq.trans hqnewAtom.symm))
      · left
        have hfalse : σ g.goalAtom = false := by
          cases hv : σ g.goalAtom <;> simp_all [livePt]
        have := turn_preserves_unmet_other rel hf hs ha hgA heq hfalse
        simp [livePt, this]
    have hle := filter_exchange c.pointingGoals.toList (livePt σ)
      (livePt (o.applyA σ)) qnew qold hnd (by simpa using hqold) hbP hbQ hsub
    have hstrict : paidByGoal c σ dni = false →
        (c.pointingGoals.toList.filter (livePt σ)).length + 1 ≤
          (c.pointingGoals.toList.filter (livePt (o.applyA σ))).length := by
      intro hpaid
      have hqnewP : livePt σ qnew = false := by
        by_contra hc
        have hqmem : qnew ∈ unmetPointing c σ := by
          apply Array.mem_filter.mpr
          exact ⟨hqnew, by simpa [livePt] using hc⟩
        have hdir : qnew.dir = dni := by
          obtain ⟨sn, dd, hqat, -, hqdi⟩ := pointing_goal_data rel qnew hqnew
          have hnames : sn = s ∧ dd = dn := by
            rw [hqat] at hqnewAtom
            simpa [pointing] using hqnewAtom
          rw [hnames.2] at hqdi
          rw [hdni] at hqdi
          simpa using hqdi.symm
        have hptrue : paidByGoal c σ dni = true := by
          simp only [paidByGoal, Array.any_eq_true]
          obtain ⟨j, hj, hget⟩ := Array.getElem_of_mem hqmem
          exact ⟨j, hj, by rw [hget, hdir]; simp⟩
        rw [hpaid] at hptrue
        exact Bool.noConfusion hptrue
      exact filter_gain c.pointingGoals.toList (livePt σ)
        (livePt (o.applyA σ)) qnew qold hnd hqnewP (by simpa using hqold) hbP hbQ hsub
    rw [unmetPointing_eq, unmetPointing_eq]
    exact ⟨hle, hstrict⟩
  · have hsub : ∀ g ∈ c.pointingGoals.toList, livePt σ g = true →
        livePt (o.applyA σ) g = true ∨ g = qold := by
      intro g hg hlive
      have hgA : g ∈ c.pointingGoals := by simpa using hg
      left
      have hne : g.goalAtom ≠ pointing s dn := fun heq => hex ⟨g, hgA, heq⟩
      have hfalse : σ g.goalAtom = false := by
        cases hv : σ g.goalAtom <;> simp_all [livePt]
      have := turn_preserves_unmet_other rel hf hs ha hgA hne hfalse
      simp [livePt, this]
    have hstrict := filter_gain c.pointingGoals.toList (livePt σ)
      (livePt (o.applyA σ)) qold qold hnd hbP (by simpa using hqold) hbP hbQ hsub
    rw [unmetPointing_eq, unmetPointing_eq]
    exact ⟨by omega, fun _ => hstrict⟩

/-- If the new direction paid for no unmet goal before the turn, the turn can
meet no goal, so the unmet-pointing count cannot fall. -/
theorem turn_unmet_mono_of_unpaid (rel : Bool) {o : AtomOp}
    (hf : OpFacts d p o) {s dn dp : Name}
    (hs : hf.inst.schema = turnA) (ha : hf.inst.args = [s, dn, dp])
    (σ : AtomState) {dni : Nat}
    (hdni : ((ground d p rel).objectsOfTypes ["direction"]).findIdx?
      (· == dn) = some dni)
    (hunpaid : paidByGoal (cfgOf (ground d p rel)) σ dni = false) :
    (unmetPointing (cfgOf (ground d p rel)) σ).size ≤
      (unmetPointing (cfgOf (ground d p rel)) (o.applyA σ)).size := by
  let c := cfgOf (ground d p rel)
  apply unmetPointing_le_mono c σ (o.applyA σ)
  intro g hg hfalse
  apply turn_preserves_unmet_other rel hf hs ha hg
  · intro heq
    have hdir : g.dir = dni := by
      obtain ⟨sn, dd, hqatom, -, hgdi⟩ := pointing_goal_data rel g hg
      have hnames : sn = s ∧ dd = dn := by
        rw [hqatom] at heq
        simpa [pointing] using heq
      rw [hnames.2] at hgdi
      rw [hdni] at hgdi
      simpa using hgdi.symm
    have hgmem : g ∈ unmetPointing c σ :=
      Array.mem_filter.mpr ⟨hg, by simp [hfalse]⟩
    have hptrue : paidByGoal c σ dni = true := by
      simp only [paidByGoal, Array.any_eq_true]
      obtain ⟨j, hj, hget⟩ := Array.getElem_of_mem hgmem
      exact ⟨j, hj, by rw [hget, hdir]; simp⟩
    rw [hunpaid] at hptrue
    exact Bool.noConfusion hptrue
  · exact hfalse

/-- Away from the new direction a turn cannot create a `pointing` fact: the only
atom it adds is indexed by the direction it turned to. -/
theorem turn_pointsAt_of (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (hf : OpFacts d p o) {s dn dp : Name}
    (hs : hf.inst.schema = turnA) (hargs : hf.inst.args = [s, dn, dp])
    {σ : AtomState} {dni x sat : Nat}
    (hdni : ((ground d p rel).objectsOfTypes ["direction"]).findIdx?
      (· == dn) = some dni)
    (hne : x ≠ dni)
    (hpt : pointsAt (cfgOf (ground d p rel)) (o.applyA σ) sat x = true) :
    pointsAt (cfgOf (ground d p rel)) σ sat x = true := by
  obtain ⟨-, hadd, -⟩ := turn_atoms hf.inst hs hargs
  obtain ⟨q, hq, hqc⟩ := array_any_elim hpt
  refine array_any_of_mem hq ?_
  simp only [Bool.and_eq_true] at hqc ⊢
  refine ⟨hqc.1, ?_⟩
  obtain ⟨sn, qd, hqa, -, hqd⟩ := pointingByDir_data (objs_nodup hp rel "direction") hq
  have hpred : q.1.pred = "pointing" := by rw [hqa]
  have hnot : q.1 ∉ [pointing s dn, notPointing s dp] := by
    have hnp : q.1 ≠ notPointing s dp := by
      intro heq
      have hnpp : q.1.pred = "not-pointing" := by rw [heq]
      rw [hpred] at hnpp
      contradiction
    have hn : q.1 ≠ pointing s dn := by
      intro heq
      rw [hqa] at heq
      have hnames : sn = s ∧ qd = dn := by simpa [pointing] using heq
      have hqd' : ((ground d p rel).objectsOfTypes ["direction"]).findIdx? (· == qd)
          = some x := hqd
      rw [hnames.2, hdni] at hqd'
      exact hne (by simpa using hqd'.symm)
    simp [hn, hnp]
  exact falls_of_lists hf hadd hnot hqc.2

/-- Away from the old direction a turn cannot destroy coverage: the ready set is
framed, and the only `pointing` atom it deletes is indexed by that direction. -/
theorem turn_covered_keep (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (hf : OpFacts d p o) {s dn dp : Name}
    (hs : hf.inst.schema = turnA) (hargs : hf.inst.args = [s, dn, dp])
    {σ : AtomState} {dpi x m : Nat}
    (hdpi : ((ground d p rel).objectsOfTypes ["direction"]).findIdx?
      (· == dp) = some dpi)
    (hne : x ≠ dpi)
    (hcov : covered (cfgOf (ground d p rel)) σ x m = true) :
    covered (cfgOf (ground d p rel)) (o.applyA σ) x m = true := by
  obtain ⟨-, -, hdel⟩ := turn_atoms hf.inst hs hargs
  refine covered_mono _ (o.applyA σ) σ ?_ ?_ hcov
  · intro q hq htrue
    obtain ⟨sn, qd, hqa, -, hqd⟩ := pointingByDir_data (objs_nodup hp rel "direction") hq
    have hpred : q.1.pred = "pointing" := by rw [hqa]
    have hnot : q.1 ∉ [notPointing s dn, pointing s dp] := by
      have hnp : q.1 ≠ notPointing s dn := by
        intro heq
        have hnpp : q.1.pred = "not-pointing" := by rw [heq]
        rw [hpred] at hnpp
        contradiction
      have hn : q.1 ≠ pointing s dp := by
        intro heq
        rw [hqa] at heq
        have hnames : sn = s ∧ qd = dp := by simpa [pointing] using heq
        have hqd' : ((ground d p rel).objectsOfTypes ["direction"]).findIdx? (· == qd)
            = some x := hqd
        rw [hnames.2, hdpi] at hqd'
        exact hne (by simpa using hqd'.symm)
      simp [hn, hnp]
    have hnotDel : q.1 ∉ o.del := fun hm => hnot (hdel ▸ hf.subDel _ hm)
    by_cases hmemAdd : q.1 ∈ o.add
    · exact applyA_add σ hmemAdd
    · rw [applyA_frame σ hmemAdd hnotDel]; exact htrue
  · intro i hi
    rw [turn_readyNow hp rel hf hs hargs σ]
    exact hi

/-- A `pointing` goal that a turn makes unmet is the goal at the direction the
satellite turned away from: that atom is the only `pointing` atom deleted. -/
theorem turn_unmet_atom (rel : Bool) {o : AtomOp} (hf : OpFacts d p o)
    {s dn dp : Name} (hs : hf.inst.schema = turnA) (ha : hf.inst.args = [s, dn, dp])
    {σ : AtomState} {q : PointingGoal}
    (hq : q ∈ (cfgOf (ground d p rel)).pointingGoals)
    (hbefore : σ q.goalAtom = true)
    (hafter : o.applyA σ q.goalAtom = false) :
    q.goalAtom = pointing s dp := by
  obtain ⟨-, -, hdel⟩ := turn_atoms hf.inst hs ha
  have hpred := pointing_goal_pred (d := d) (p := p) rel q hq
  have hmemDel : q.goalAtom ∈ [notPointing s dn, pointing s dp] := by
    by_contra hnot
    have hnotDel : q.goalAtom ∉ o.del := fun hm => hnot (hdel ▸ hf.subDel _ hm)
    by_cases hmemAdd : q.goalAtom ∈ o.add
    · rw [applyA_add σ hmemAdd] at hafter
      exact Bool.noConfusion hafter
    · rw [applyA_frame σ hmemAdd hnotDel, hbefore] at hafter
      exact Bool.noConfusion hafter
  have hnp : q.goalAtom ≠ notPointing s dn := by
    intro heq
    have hnpp : q.goalAtom.pred = "not-pointing" := by rw [heq]
    rw [hpred] at hnpp
    contradiction
  simpa [hnp] using hmemDel

/-- A turn moves neither the image goals nor the ready instruments, so the modes
that still owe a calibration are the same before and after. -/
theorem turn_uncalibratedModes (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (hf : OpFacts d p o) {s dn dp : Name}
    (hs : hf.inst.schema = turnA) (ha : hf.inst.args = [s, dn, dp])
    (σ : AtomState) :
    uncalibratedModes (cfgOf (ground d p rel)) (o.applyA σ) =
      uncalibratedModes (cfgOf (ground d p rel)) σ := by
  unfold uncalibratedModes
  rw [neededModes_congr _ σ (o.applyA σ) (turn_frame_images rel hf hs ha σ),
    turn_readyNow hp rel hf hs ha σ]

/-- **The old direction leaving the turn list is paid for by a pointing goal.**

When the direction the satellite turned away from still needed a turn before the
turn and does not after it, the only reason available is that the `pointing` goal
at that direction became unmet.  That goal pays for the lost direction, and pays
one more when the new direction owed no goal at all. -/
theorem turn_old_exchange (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (hf : OpFacts d p o) {s dn dp : Name}
    (hs : hf.inst.schema = turnA) (ha : hf.inst.args = [s, dn, dp])
    {σ : AtomState} {dni dpi : Nat}
    (hdni : ((ground d p rel).objectsOfTypes ["direction"]).findIdx?
      (· == dn) = some dni)
    (hdpi : ((ground d p rel).objectsOfTypes ["direction"]).findIdx?
      (· == dp) = some dpi)
    (hneIdx : dni ≠ dpi)
    (holdBefore : dpi ∈ dirsList (cfgOf (ground d p rel)) σ)
    (holdAfter : dpi ∉ dirsList (cfgOf (ground d p rel)) (o.applyA σ)) :
    (unmetPointing (cfgOf (ground d p rel)) σ).size ≤
        (unmetPointing (cfgOf (ground d p rel)) (o.applyA σ)).size ∧
      (paidByGoal (cfgOf (ground d p rel)) σ dni = false →
        (unmetPointing (cfgOf (ground d p rel)) σ).size + 1 ≤
          (unmetPointing (cfgOf (ground d p rel)) (o.applyA σ)).size) := by
  let c := cfgOf (ground d p rel)
  obtain ⟨img, himg, himgDir, hpaidBefore, hcovBefore⟩ :=
    (mem_dirsList c σ).mp holdBefore
  have himgAfter : img ∈ unmetImages c (o.applyA σ) :=
    mem_unmetImages_of c (turn_frame_images rel hf hs ha σ) himg
  have hpaidAfter : paidByGoal c (o.applyA σ) dpi = true := by
    rcases hpa : paidByGoal c (o.applyA σ) dpi with _ | _
    · have hcovAfter : covered c (o.applyA σ) dpi img.mode = false := by
        rcases hca : covered c (o.applyA σ) dpi img.mode with _ | _
        · rfl
        · have hcb := turn_covered_of hp rel hf hs ha hdni
            (fun hc => hneIdx hc.symm) hca
          rw [hcb] at hcovBefore
          exact Bool.noConfusion hcovBefore
      have : dpi ∈ dirsList c (o.applyA σ) :=
        (mem_dirsList c (o.applyA σ)).mpr
          ⟨img, himgAfter, himgDir, hpa, hcovAfter⟩
      exact absurd this holdAfter
    · rfl
  simp only [paidByGoal, Array.any_eq_true] at hpaidAfter
  obtain ⟨j, hj, hjdir⟩ := hpaidAfter
  let qold := (unmetPointing c (o.applyA σ))[j]
  have hqUnmet : qold ∈ unmetPointing c (o.applyA σ) := Array.getElem_mem hj
  have hqold : qold ∈ c.pointingGoals := (Array.mem_filter.mp hqUnmet).1
  have hqfalse : o.applyA σ qold.goalAtom = false := by
    have := (Array.mem_filter.mp hqUnmet).2
    simpa using this
  have hqdir : qold.dir = dpi := by
    change (qold.dir == dpi) = true at hjdir
    simpa using hjdir
  obtain ⟨sn, dd, hqatom0, -, hqdi⟩ := pointing_goal_data rel qold hqold
  have hdd : dd = dp := by
    rw [hqdir] at hqdi
    exact findIdx_inj hqdi hdpi
  have hsn : sn = s := by
    have hboardOld : qold.goalAtom = pointing sn dp := by rw [hqatom0, hdd]
    -- The transition can only make a `pointing` goal false by deleting the
    -- old pointing atom of this very satellite.
    obtain ⟨-, hadd, hdel⟩ := turn_atoms hf.inst hs ha
    have hmemDel : qold.goalAtom ∈ [notPointing s dn, pointing s dp] := by
      by_contra hnot
      have hnotDel : qold.goalAtom ∉ o.del := fun hm => hnot (hdel ▸ hf.subDel _ hm)
      by_cases hmemAdd : qold.goalAtom ∈ o.add
      · rw [applyA_add σ hmemAdd] at hqfalse
        exact Bool.noConfusion hqfalse
      · rw [applyA_frame σ hmemAdd hnotDel] at hqfalse
        have hbeforePaid : σ qold.goalAtom = false := hqfalse
        have hqBefore : qold ∈ unmetPointing c σ :=
          Array.mem_filter.mpr ⟨hqold, by simp [hbeforePaid]⟩
        have hptrue : paidByGoal c σ dpi = true := by
          simp only [paidByGoal, Array.any_eq_true]
          obtain ⟨k, hk, hget⟩ := Array.getElem_of_mem hqBefore
          exact ⟨k, hk, by rw [hget, hqdir]; simp⟩
        rw [hpaidBefore] at hptrue
        exact Bool.noConfusion hptrue
    rw [hboardOld] at hmemDel
    simpa [pointing, notPointing] using hmemDel
  have hqatom : qold.goalAtom = pointing s dp := by rw [hqatom0, hsn, hdd]
  have hqbefore : σ qold.goalAtom = true := by
    cases hb : σ qold.goalAtom with
    | true => rfl
    | false =>
        have hqBefore : qold ∈ unmetPointing c σ :=
          Array.mem_filter.mpr ⟨hqold, by simp [hb]⟩
        have hptrue : paidByGoal c σ dpi = true := by
          simp only [paidByGoal, Array.any_eq_true]
          obtain ⟨k, hk, hget⟩ := Array.getElem_of_mem hqBefore
          exact ⟨k, hk, by rw [hget, hqdir]; simp⟩
        rw [hpaidBefore] at hptrue
        exact Bool.noConfusion hptrue
  obtain ⟨hU, hUstrict⟩ := turn_unmet_exchange hp rel hf hs ha σ hqold
    hqatom hqbefore hqfalse hdni
  exact ⟨hU, hUstrict⟩

set_option maxHeartbeats 1000000 in
/-- The unmet-pointing and outstanding-direction terms, taken together, fall
by at most the turn itself.  Losing the old direction from the latter means an
old pointing goal became unmet, which pays for that loss in the former. -/
theorem turn_core_bound (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (hf : OpFacts d p o) {s dn dp : Name}
    (hs : hf.inst.schema = turnA) (ha : hf.inst.args = [s, dn, dp])
    {σ : AtomState} (hinv : Inv p σ) (happ : o.applicableA σ) :
    (unmetPointing (cfgOf (ground d p rel)) σ).size +
        (dirsToTurn (cfgOf (ground d p rel)) σ).length ≤
      (unmetPointing (cfgOf (ground d p rel)) (o.applyA σ)).size +
        (dirsToTurn (cfgOf (ground d p rel)) (o.applyA σ)).length + 1 := by
  let c := cfgOf (ground d p rel)
  change (unmetPointing c σ).size + (dirsToTurn c σ).length ≤
    (unmetPointing c (o.applyA σ)).size +
      (dirsToTurn c (o.applyA σ)).length + 1
  obtain ⟨si, dni, dpi, hsi, hdni, hdpi⟩ := turn_arg_indices hp rel hf hs ha
  have hneName : dn ≠ dp := turn_ne hp hf hs ha hinv happ
  have hneIdx : dni ≠ dpi := by
    intro heq
    have hname := findIdx_inj hdni (heq ▸ hdpi)
    exact hneName hname
  have hmemtwo : ∀ x ∈ dirsList c σ,
      x ∈ dirsList c (o.applyA σ) ∨ x = dni ∨ x = dpi := by
    apply mem_dirsList_of_two c σ (o.applyA σ) dni dpi
    · exact turn_frame_images rel hf hs ha σ
    · intro x hx
      exact turn_paidByGoal_of rel hf hs ha hdpi hx
    · intro x m hnx hx
      exact turn_covered_of hp rel hf hs ha hdni hnx hx
  by_cases holdBefore : dpi ∈ dirsList c σ
  · by_cases holdAfter : dpi ∈ dirsList c (o.applyA σ)
    · by_cases hnewBefore : dni ∈ dirsList c σ
      · obtain ⟨-, -, -, hpaidNew, -⟩ := (mem_dirsList c σ).mp hnewBefore
        have hdir := dirsToTurn_le_succ c σ (o.applyA σ) dni (by
          intro x hx
          rcases hmemtwo x hx with hm | hn | ho
          · exact Or.inl hm
          · exact Or.inr hn
          · exact Or.inl (ho ▸ holdAfter))
        have hgoal := turn_unmet_mono_of_unpaid rel hf hs ha σ hdni
          (by simpa using hpaidNew)
        change (unmetPointing c σ).size ≤
          (unmetPointing c (o.applyA σ)).size at hgoal
        omega
      · have hdir := dirsToTurn_mono c σ (o.applyA σ) (by
          intro x hx
          rcases hmemtwo x hx with hm | hn | ho
          · exact hm
          · exact absurd (hn ▸ hx) hnewBefore
          · exact ho ▸ holdAfter)
        have hgoal := turn_unmetPointing_bound hp rel hf hs ha σ
        change (unmetPointing c σ).size ≤
          (unmetPointing c (o.applyA σ)).size + 1 at hgoal
        omega
    · obtain ⟨hU, hUstrict⟩ := turn_old_exchange hp rel hf hs ha hdni hdpi hneIdx
        holdBefore holdAfter
      have hUc : (unmetPointing c σ).size ≤
          (unmetPointing c (o.applyA σ)).size := by simpa [c] using hU
      by_cases hnewBefore : dni ∈ dirsList c σ
      · obtain ⟨-, -, -, hpaidNew, -⟩ := (mem_dirsList c σ).mp hnewBefore
        have hD := turn_dirsToTurn_le_two hp rel hf hs ha σ
        have hDc : (dirsToTurn c σ).length ≤
            (dirsToTurn c (o.applyA σ)).length + 2 := by simpa [c] using hD
        have hUs : (unmetPointing c σ).size + 1 ≤
            (unmetPointing c (o.applyA σ)).size := by
          simpa [c] using hUstrict (by simpa using hpaidNew)
        omega
      · have hD := dirsToTurn_le_succ c σ (o.applyA σ) dpi (by
          intro x hx
          rcases hmemtwo x hx with hm | hn | ho
          · exact Or.inl hm
          · exact absurd (hn ▸ hx) hnewBefore
          · exact Or.inr ho)
        omega
  · by_cases hnewBefore : dni ∈ dirsList c σ
    · obtain ⟨-, -, -, hpaidNew, -⟩ := (mem_dirsList c σ).mp hnewBefore
      have hD := dirsToTurn_le_succ c σ (o.applyA σ) dni (by
        intro x hx
        rcases hmemtwo x hx with hm | hn | ho
        · exact Or.inl hm
        · exact Or.inr hn
        · exact absurd (ho ▸ hx) holdBefore)
      have hU := turn_unmet_mono_of_unpaid rel hf hs ha σ hdni
        (by simpa using hpaidNew)
      change (unmetPointing c σ).size ≤
        (unmetPointing c (o.applyA σ)).size at hU
      omega
    · have hD := dirsToTurn_mono c σ (o.applyA σ) (by
        intro x hx
        rcases hmemtwo x hx with hm | hn | ho
        · exact hm
        · exact absurd (hn ▸ hx) hnewBefore
        · exact absurd (ho ▸ hx) holdBefore)
      have hU := turn_unmetPointing_bound hp rel hf hs ha σ
      change (unmetPointing c σ).size ≤
        (unmetPointing c (o.applyA σ)).size + 1 at hU
      omega

set_option maxHeartbeats 1000000 in
/-- **A turn that pays off the calibration detour buys nothing else.**

The instrument whose target came into reach names a direction, and the reach test
it now passes and failed before decides which direction that is.  Either it is
the direction just turned to — which then owed no pointing goal and was not
outstanding, so neither of the other two terms fell — or it is the direction just
left, which entered the turn list or made its own pointing goal unmet, and either
way pays for itself.  So the other two turn terms together do not fall. -/
theorem turn_tight_of_approach (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (hf : OpFacts d p o) {s dn dp : Name}
    (hs : hf.inst.schema = turnA) (ha : hf.inst.args = [s, dn, dp])
    {σ : AtomState} (hinv : Inv p σ) (happ : o.applicableA σ)
    (hσ1 : approach (cfgOf (ground d p rel)) σ = 1)
    (hτ0 : approach (cfgOf (ground d p rel)) (o.applyA σ) = 0) :
    (unmetPointing (cfgOf (ground d p rel)) σ).size
        + (dirsToTurn (cfgOf (ground d p rel)) σ).length ≤
      (unmetPointing (cfgOf (ground d p rel)) (o.applyA σ)).size
        + (dirsToTurn (cfgOf (ground d p rel)) (o.applyA σ)).length := by
  classical
  let c := cfgOf (ground d p rel)
  change (unmetPointing c σ).size + (dirsToTurn c σ).length ≤
    (unmetPointing c (o.applyA σ)).size + (dirsToTurn c (o.applyA σ)).length
  obtain ⟨si, dni, dpi, hsi, hdni, hdpi⟩ := turn_arg_indices hp rel hf hs ha
  have hneName : dn ≠ dp := turn_ne hp hf hs ha hinv happ
  have hneIdx : dni ≠ dpi := by
    intro heq
    exact hneName (findIdx_inj hdni (heq ▸ hdpi))
  have hframe := turn_frame_images rel hf hs ha σ
  have hmemtwo : ∀ x ∈ dirsList c σ,
      x ∈ dirsList c (o.applyA σ) ∨ x = dni ∨ x = dpi := by
    apply mem_dirsList_of_two c σ (o.applyA σ) dni dpi hframe
    · intro x hx
      exact turn_paidByGoal_of rel hf hs ha hdpi hx
    · intro x m hnx hx
      exact turn_covered_of hp rel hf hs ha hdni hnx hx
  -- the detour is charged before the turn and not after it
  have hcondσ : (!(uncalibratedModes c σ).isEmpty && !calibrationInReach c σ) = true := by
    by_contra hc
    rw [approach, if_neg hc] at hσ1
    exact absurd hσ1 (by simp)
  obtain ⟨huncσ, hnrσ⟩ : (uncalibratedModes c σ).isEmpty = false ∧
      calibrationInReach c σ = false := by simpa using hcondσ
  have hnrτ : calibrationInReach c (o.applyA σ) = true := by
    by_contra hc
    have hcτ : calibrationInReach c (o.applyA σ) = false := by simpa using hc
    have huncτ : (uncalibratedModes c (o.applyA σ)).isEmpty = false := by
      rw [turn_uncalibratedModes hp rel hf hs ha σ]; exact huncσ
    rw [approach, if_pos (by rw [huncτ, hcτ]; rfl)] at hτ0
    exact absurd hτ0 (by simp)
  obtain ⟨target, sat, hτcond, hσcond⟩ :=
    inReach_witness c σ (o.applyA σ)
      (neededModes_congr c σ (o.applyA σ) hframe) hnrσ hnrτ
  simp only [reachCond, Bool.or_eq_true, Bool.or_eq_false_iff] at hτcond hσcond
  have hpaidσ : paidByGoal c σ target = false := hσcond.2
  have hnotσ : target ∉ dirsList c σ := by
    intro hc
    have hcon : (dirsToTurn c σ).contains target = true := by
      simp only [dirsToTurn_eq]
      simpa using (mem_distinct _).mpr hc
    rw [hσcond.1.2] at hcon
    exact Bool.noConfusion hcon
  -- the target is the new direction: it was neither owed a goal nor outstanding
  have hclose_dni : target = dni →
      (unmetPointing c σ).size + (dirsToTurn c σ).length ≤
        (unmetPointing c (o.applyA σ)).size + (dirsToTurn c (o.applyA σ)).length := by
    intro htd
    have hpaidNew : paidByGoal c σ dni = false := by rw [← htd]; exact hpaidσ
    have hnotNew : dni ∉ dirsList c σ := by rw [← htd]; exact hnotσ
    have hU := turn_unmet_mono_of_unpaid rel hf hs ha σ hdni (by simpa [c] using hpaidNew)
    have hUc : (unmetPointing c σ).size ≤
        (unmetPointing c (o.applyA σ)).size := by simpa [c] using hU
    by_cases holdBefore : dpi ∈ dirsList c σ
    · by_cases holdAfter : dpi ∈ dirsList c (o.applyA σ)
      · have hD := dirsToTurn_mono c σ (o.applyA σ) (by
          intro x hx
          rcases hmemtwo x hx with hm | hn | ho
          · exact hm
          · exact absurd (hn ▸ hx) hnotNew
          · exact ho ▸ holdAfter)
        omega
      · obtain ⟨-, hUstrict⟩ := turn_old_exchange hp rel hf hs ha hdni hdpi hneIdx
          holdBefore holdAfter
        have hUs : (unmetPointing c σ).size + 1 ≤
            (unmetPointing c (o.applyA σ)).size := by
          simpa [c] using hUstrict (by simpa [c] using hpaidNew)
        have hD := dirsToTurn_le_succ c σ (o.applyA σ) dpi (by
          intro x hx
          rcases hmemtwo x hx with hm | hn | ho
          · exact Or.inl hm
          · exact absurd (hn ▸ hx) hnotNew
          · exact Or.inr ho)
        omega
    · have hD := dirsToTurn_mono c σ (o.applyA σ) (by
        intro x hx
        rcases hmemtwo x hx with hm | hn | ho
        · exact hm
        · exact absurd (hn ▸ hx) hnotNew
        · exact absurd (ho ▸ hx) holdBefore)
      omega
  -- the target is the old direction, and it is outstanding after the turn
  have hclose_dpi : target = dpi → target ∈ dirsList c (o.applyA σ) →
      (unmetPointing c σ).size + (dirsToTurn c σ).length ≤
        (unmetPointing c (o.applyA σ)).size + (dirsToTurn c (o.applyA σ)).length := by
    intro htd hmem
    have hnotOld : dpi ∉ dirsList c σ := by rw [← htd]; exact hnotσ
    have hdpiAfter : dpi ∈ dirsList c (o.applyA σ) := by rw [← htd]; exact hmem
    rw [dirsToTurn_eq, dirsToTurn_eq]
    by_cases hnewBefore : dni ∈ dirsList c σ
    · obtain ⟨-, -, -, hpaidNew, -⟩ := (mem_dirsList c σ).mp hnewBefore
      have hU := turn_unmet_mono_of_unpaid rel hf hs ha σ hdni (by simpa [c] using hpaidNew)
      have hUc : (unmetPointing c σ).size ≤
          (unmetPointing c (o.applyA σ)).size := by simpa [c] using hU
      have hlt := length_distinct_lt (dirsList c σ) (dni :: dirsList c (o.applyA σ))
        (by
          intro x hx
          rcases hmemtwo x hx with hm | hn | ho
          · exact List.mem_cons.mpr (Or.inr hm)
          · exact List.mem_cons.mpr (Or.inl hn)
          · exact absurd (ho ▸ hx) hnotOld)
        (List.mem_cons.mpr (Or.inr hdpiAfter)) hnotOld
      have hle := length_distinct_le_succ (dni :: dirsList c (o.applyA σ))
        (dirsList c (o.applyA σ)) dni (by
          intro x hx
          rcases List.mem_cons.mp hx with h | h
          · exact Or.inr h
          · exact Or.inl h)
      omega
    · have hsub : ∀ x ∈ dirsList c σ, x ∈ dirsList c (o.applyA σ) := by
        intro x hx
        rcases hmemtwo x hx with hm | hn | ho
        · exact hm
        · exact absurd (hn ▸ hx) hnewBefore
        · exact absurd (ho ▸ hx) hnotOld
      have hlt := length_distinct_lt (dirsList c σ) (dirsList c (o.applyA σ)) hsub
        hdpiAfter hnotOld
      have hU := turn_unmetPointing_bound hp rel hf hs ha σ
      have hUc : (unmetPointing c σ).size ≤
          (unmetPointing c (o.applyA σ)).size + 1 := by simpa [c] using hU
      omega
  rcases hτcond with (hpt | hdir) | hgoal
  · -- the satellite now points at the target, so the target is the new direction
    refine hclose_dni ?_
    by_contra hne
    have hbefore := turn_pointsAt_of hp rel hf hs ha hdni hne hpt
    rw [hσcond.1.1] at hbefore
    exact Bool.noConfusion hbefore
  · -- the target entered the turn list, so it lost coverage: the old direction
    have hmemAfter : target ∈ dirsList c (o.applyA σ) :=
      (mem_distinct _).mp (by simpa [dirsToTurn_eq] using hdir)
    refine hclose_dpi ?_ hmemAfter
    obtain ⟨img, himgτ, himgDir, hpaidτ, hcovτ⟩ :=
      (mem_dirsList c (o.applyA σ)).mp hmemAfter
    have himgσ : img ∈ unmetImages c σ := by
      rw [unmetImages_array_congr c σ (o.applyA σ) hframe] at himgτ
      exact himgτ
    by_contra hne
    have hcovσ : covered c σ target img.mode = true := by
      rcases hcv : covered c σ target img.mode with _ | _
      · exact absurd ((mem_dirsList c σ).mpr ⟨img, himgσ, himgDir, hpaidσ, hcv⟩) hnotσ
      · rfl
    have hkeep := turn_covered_keep hp rel hf hs ha hdpi hne hcovσ
    rw [hkeep] at hcovτ
    exact Bool.noConfusion hcovτ
  · -- a pointing goal at the target became unmet: it is the old direction's own
    obtain ⟨q, hqmem, hqdir0⟩ := array_any_elim hgoal
    have hq : q ∈ c.pointingGoals := (Array.mem_filter.mp hqmem).1
    have hqdir : q.dir = target := by simpa using hqdir0
    have hafter : o.applyA σ q.goalAtom = false := by
      have hqf := (Array.mem_filter.mp hqmem).2
      simpa using hqf
    have hbefore : σ q.goalAtom = true := by
      cases hb : σ q.goalAtom with
      | true => rfl
      | false =>
          exfalso
          have hqBefore : q ∈ unmetPointing c σ :=
            Array.mem_filter.mpr ⟨hq, by simp [hb]⟩
          have hptrue : paidByGoal c σ target = true := by
            simp only [paidByGoal, Array.any_eq_true]
            obtain ⟨k, hk, hget⟩ := Array.getElem_of_mem hqBefore
            exact ⟨k, hk, by rw [hget, hqdir]; simp⟩
          rw [hpaidσ] at hptrue
          exact Bool.noConfusion hptrue
    have hqatom : q.goalAtom = pointing s dp :=
      turn_unmet_atom rel hf hs ha hq hbefore hafter
    have htd : target = dpi := by
      obtain ⟨sn, dd, hqa, -, hqdi⟩ := pointing_goal_data rel q hq
      have hdd : dd = dp := by
        rw [hqa] at hqatom
        have hnames : sn = s ∧ dd = dp := by simpa [pointing] using hqatom
        exact hnames.2
      rw [hdd, hdpi] at hqdi
      have hqd : q.dir = dpi := by simpa using hqdi.symm
      rw [← hqdir, hqd]
    by_cases hdpiAfter : dpi ∈ dirsList c (o.applyA σ)
    · exact hclose_dpi htd (by rw [htd]; exact hdpiAfter)
    · obtain ⟨hU, hUstrict⟩ :=
        turn_unmet_exchange hp rel hf hs ha σ hq hqatom hbefore hafter hdni
      have hUc : (unmetPointing c σ).size ≤
          (unmetPointing c (o.applyA σ)).size := by simpa [c] using hU
      have hnotOld : dpi ∉ dirsList c σ := by rw [← htd]; exact hnotσ
      by_cases hnewBefore : dni ∈ dirsList c σ
      · obtain ⟨-, -, -, hpaidNew, -⟩ := (mem_dirsList c σ).mp hnewBefore
        have hUs : (unmetPointing c σ).size + 1 ≤
            (unmetPointing c (o.applyA σ)).size := by
          simpa [c] using hUstrict (by simpa [c] using hpaidNew)
        have hD := dirsToTurn_le_succ c σ (o.applyA σ) dni (by
          intro x hx
          rcases hmemtwo x hx with hm | hn | ho
          · exact Or.inl hm
          · exact Or.inr hn
          · exact absurd (ho ▸ hx) hnotOld)
        omega
      · have hD := dirsToTurn_mono c σ (o.applyA σ) (by
          intro x hx
          rcases hmemtwo x hx with hm | hn | ho
          · exact hm
          · exact absurd (hn ▸ hx) hnewBefore
          · exact absurd (ho ▸ hx) hnotOld)
        omega

/-- **The joint turn bound, with the calibration detour included.**  Away from
the detour the two counting terms give it directly; when the detour itself falls,
the turn that paid it moved nothing else. -/
theorem turn_bound (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (hf : OpFacts d p o) {s dn dp : Name}
    (hs : hf.inst.schema = turnA) (ha : hf.inst.args = [s, dn, dp])
    {σ : AtomState} (hinv : Inv p σ) (happ : o.applicableA σ) :
    turns (cfgOf (ground d p rel)) σ ≤
      turns (cfgOf (ground d p rel)) (o.applyA σ) + 1 := by
  let c := cfgOf (ground d p rel)
  rw [turns_eq, turns_eq]
  change (unmetPointing c σ).size + (dirsToTurn c σ).length + approach c σ ≤
    (unmetPointing c (o.applyA σ)).size + (dirsToTurn c (o.applyA σ)).length
      + approach c (o.applyA σ) + 1
  have hb1 := approach_le_two c σ
  have hb2 := approach_le_two c (o.applyA σ)
  by_cases hA : approach c σ ≤ approach c (o.applyA σ)
  · have hcore : (unmetPointing c σ).size + (dirsToTurn c σ).length ≤
        (unmetPointing c (o.applyA σ)).size
          + (dirsToTurn c (o.applyA σ)).length + 1 :=
      turn_core_bound hp rel hf hs ha hinv happ
    omega
  · have hσ1 : approach c σ = 1 := by omega
    have hτ0 : approach c (o.applyA σ) = 0 := by omega
    have htight : (unmetPointing c σ).size + (dirsToTurn c σ).length ≤
        (unmetPointing c (o.applyA σ)).size
          + (dirsToTurn c (o.applyA σ)).length :=
      turn_tight_of_approach hp rel hf hs ha hinv happ hσ1 hτ0
    omega

/-- The joint turn bound is exactly `TurnStep.turnBound`, so the `turn_to` case
of the schema follows from it and the literal add/delete lists. -/
theorem turn_schemaStep (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (hf : OpFacts d p o) {s dn dp : Name}
    (hs : hf.inst.schema = turnA) (ha : hf.inst.args = [s, dn, dp])
    {σ : AtomState} (hinv : Inv p σ) (happ : o.applicableA σ) :
    SchemaStep (cfgOf (ground d p rel)) σ (o.applyA σ) := by
  apply turn_step_of_bound hp rel hf hs ha σ
  exact turn_bound hp rel hf hs ha hinv happ

/-! ### Closing the grounded schema bridge -/

/-- **Every grounded Satellite operator has a proved schema shape.** -/
theorem schemaStep_of_ops (hp : Pinned d p) (rel : Bool) :
    ∀ o ∈ groundedOps d p rel, ∀ σ, Inv p σ → o.applicableA σ →
      SchemaStep (cfgOf (ground d p rel)) σ (o.applyA σ) := by
  intro o ho σ hinv happ
  obtain ⟨hf, hswitchDel⟩ := satellite_opFacts hp rel ho
  rcases instance_shape hp.domain hf.inst with
    ⟨s, dn, dp, hs, ha⟩ | ⟨ins, s, hs, ha⟩ | ⟨ins, s, hs, ha⟩ |
      ⟨s, ins, dd, hs, ha⟩ | ⟨s, dd, ins, m, hs, ha⟩
  · exact turn_schemaStep hp rel hf hs ha hinv happ
  · exact .ready (switchOn_ready hp rel ho hf hswitchDel hs ha hinv happ)
  · exact .ready (switchOff_ready hp rel hf hs ha σ)
  · exact .ready (calibrate_ready hp rel ho hf hs ha hinv happ)
  · exact image_schemaStep hp rel ho hf hs ha happ

/-- **Satellite's shipped improved heuristic is zero at every reachable goal**,
for relevance pruning both on and off, from the parsed-domain record alone. -/
theorem improved_goalAware_of_pinned (hp : Pinned d p) (rel : Bool) :
    (ground d p rel).GoalAwareOn (Reachable (ground d p rel))
      (ExampleHeuristics.Satellite.improved (ground d p rel)).eval := by
  have hcost := cost_pos hp rel
  exact improved_goalAware_of_shape d p rel (Inv p)
    (ground_wf d p rel hcost) hcost (schemaStep_of_ops hp rel)
    (inv_init hp) (inv_step hp rel)

/-- **Satellite's shipped improved heuristic is consistent on reachable states**,
for relevance pruning both on and off, from the parsed-domain record alone. -/
theorem improved_consistent_of_pinned (hp : Pinned d p) (rel : Bool) :
    (ground d p rel).ConsistentOn (Reachable (ground d p rel))
      (ExampleHeuristics.Satellite.improved (ground d p rel)).eval := by
  have hcost := cost_pos hp rel
  exact improved_consistent_of_shape d p rel (Inv p)
    (ground_wf d p rel hcost) hcost (images_nodup hp rel)
    (schemaStep_of_ops hp rel) (inv_init hp) (inv_step hp rel)

/-- **Satellite's shipped improved heuristic is admissible**, for relevance
pruning both on and off, from the decidable parsed-domain record alone. -/
theorem improved_admissible_of_pinned (hp : Pinned d p) (rel : Bool) :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel))
      (ExampleHeuristics.Satellite.improved (ground d p rel)).eval := by
  have hcost := cost_pos hp rel
  exact improved_admissible_of_shape d p rel (Inv p)
    (ground_wf d p rel hcost) hcost (images_nodup hp rel)
    (schemaStep_of_ops hp rel) (inv_init hp) (inv_step hp rel)

end Planner.Lifted.Satellite

/- -------------------------------------------------------------------------- -/
/-
Soundness of the executable certificate for the improved Satellite heuristic.
-/

namespace Planner.Lifted.Satellite

open Planner Planner.Pddl

theorem certificate_sound {d : Domain} {p : Problem}
    (hv : Validated d p)
    (h : ExampleHeuristics.Satellite.Certificate.certified d p = true) :
    Pinned d p := by
  simp only [ExampleHeuristics.Satellite.Certificate.certified,
    ExampleHeuristics.Satellite.Certificate.conditions, Certificate.passes,
    List.all_cons, List.all_nil, Bool.and_eq_true] at h
  rcases h with
    ⟨hactions, hsat, hdir, hins, hmode, hsatName, hdirName, hinsName, hmodeName,
      hboardStatic, hsupportsStatic, htargetStatic, hgoalDynamic, hboard, htarget,
      hpointing, hnotPointing, hpowerOff, hgoalNodup, -⟩
  have hpairs : ∀ pred : Pddl.Name,
      Planner.Certificate.initPairs p pred = initPairs p pred := fun _ => rfl
  have hones : ∀ pred : Pddl.Name,
      Planner.Certificate.initOnes p pred = initOnes p pred := fun _ => rfl
  have hunique : ∀ pred : Pddl.Name,
      ExampleHeuristics.Satellite.Certificate.firstUnique p pred = true →
      ∀ x ∈ initPairs p pred, ∀ y ∈ initPairs p pred, x.1 = y.1 → x.2 = y.2 := by
    intro pred hu x hx y hy h1
    rw [ExampleHeuristics.Satellite.Certificate.firstUnique] at hu
    simp only [hpairs, List.all_eq_true] at hu
    have hxy := hu x hx y hy
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hxy
    rcases hxy with hxy | hxy
    · exact absurd h1 hxy
    · exact hxy
  refine
    { domain := by simpa using hactions
      satType := Certificate.exactType_sound hsat
      dirType := Certificate.exactType_sound hdir
      insType := Certificate.exactType_sound hins
      modeType := Certificate.exactType_sound hmode
      satTypeName := by simpa using hsatName
      dirTypeName := by simpa using hdirName
      insTypeName := by simpa using hinsName
      modeTypeName := by simpa using hmodeName
      validated := hv
      onBoardStatic := by simpa using hboardStatic
      supportsStatic := by simpa using hsupportsStatic
      targetStatic := by simpa using htargetStatic
      goalDynamic := ?_
      oneBoard := hunique "on_board" hboard
      oneTarget := hunique "calibration_target" htarget
      initOnePointing := hunique "pointing" hpointing
      initNotPointing := ?_
      initPowerOff := ?_
      goalNodup := of_decide_eq_true hgoalNodup }
  · rw [List.all_eq_true] at hgoalDynamic
    intro a ha
    have hdyn := hgoalDynamic a ha
    simpa using hdyn
  · intro x hx
    rw [ExampleHeuristics.Satellite.Certificate.pointingConsistent] at hnotPointing
    simp only [hpairs, List.all_eq_true] at hnotPointing
    simpa using hnotPointing x hx
  · intro x hx
    rw [ExampleHeuristics.Satellite.Certificate.boardPowerOff] at hpowerOff
    simp only [hpairs, hones, List.all_eq_true] at hpowerOff
    simpa using hpowerOff x hx

theorem improved_goalAware_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool)
    (h : ExampleHeuristics.Satellite.Certificate.certified d p = true) :
    (ground d p rel).GoalAwareOn (Reachable (ground d p rel))
      (ExampleHeuristics.Satellite.improved (ground d p rel)).eval :=
  improved_goalAware_of_pinned (certificate_sound hv h) rel

theorem improved_consistent_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool)
    (h : ExampleHeuristics.Satellite.Certificate.certified d p = true) :
    (ground d p rel).ConsistentOn (Reachable (ground d p rel))
      (ExampleHeuristics.Satellite.improved (ground d p rel)).eval :=
  improved_consistent_of_pinned (certificate_sound hv h) rel

theorem improved_proof_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool) :
    ImprovedProof d p rel
      (ExampleHeuristics.Satellite.Certificate.certified d p)
      (ExampleHeuristics.Satellite.improved (ground d p rel)) :=
  { goalAware := improved_goalAware_of_certificate hv rel
    consistent := improved_consistent_of_certificate hv rel }

theorem improved_admissible_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool)
    (h : ExampleHeuristics.Satellite.Certificate.certified d p = true) :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel))
      (ExampleHeuristics.Satellite.improved (ground d p rel)).eval :=
  (improved_proof_of_certificate hv rel).admissible h

end Planner.Lifted.Satellite
