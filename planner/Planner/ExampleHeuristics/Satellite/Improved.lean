/-
Satellite, improved heuristic.

Four schemas that never share an action — `take_image`, `calibrate`, `switch_on`,
`turn_to` — are bounded separately and added.

  * `take_image` produces exactly one `have_image` atom, so one is needed per
    unmet imaging goal.
  * `take_image` also requires an instrument that is powered *and* calibrated at
    the same moment.  If no such instrument supports some unmet image's mode, a
    `calibrate` is still to come: `switch_on` deletes `calibrated`, so an
    instrument that is calibrated but off cannot be used without recalibrating.
  * If no *powered* instrument supports some unmet image's mode, a `switch_on` is
    still to come.
  * `turn_to` points one satellite at one direction.  Two disjoint sets of turns
    are counted, and added.

The turn count is where the information is.  A direction an unmet image needs
costs a turn unless a satellite is already pointing at it *with an instrument
that can take the picture without looking away*: the instrument must support the
mode, and it must either be ready — powered and calibrated — or calibrate against
that same direction, so that it can be made ready without the satellite turning
away and back.  A satellite parked on the right direction whose only suitable
instrument calibrates against somewhere else does not save the turn; it merely
postpones it.

Those turns are counted only for directions no *unmet* `pointing` goal mentions,
since a turn towards one of those is already paid for by the goal count.  The
exclusion has to be unconditional: the satellite that owes the `pointing` goal may
calibrate somewhere else first and arrive at the direction only at the end, so its
final turn serves the goal and the image together even when it could not have shot
the picture on arrival.  Restricting the exclusion to unmet goals is what keeps it
sharp: a `pointing` goal that already holds costs nothing, so its direction must
still be charged when an image needs it, and the satellite sitting there will have
to come back.

One `calibrate` is not always enough.  The instruments that are ready cover some
of the modes the missing images need; the rest have to be made ready, and each
`calibrate` makes exactly one instrument ready, so the number still to come is at
least the number of instruments needed to cover the uncovered modes.  When no
single instrument covers them all, that is at least two.  This cannot clash with
the image count: taking an image of mode `m` needs a ready instrument supporting
`m`, so `m` is covered already and the image does not sit in the uncovered set.
The same argument, with `power_on` in place of `calibrated`, bounds `switch_on`.

`switch_on` needs a free power slot: if every instrument that could serve a needed
mode is on a satellite whose slot is already taken, a `switch_off` has to come
first, and that is a fifth family of its own.

One further turn is charged when a calibration is still needed and no satellite
is looking at the calibration target of any instrument that could serve a needed
mode.  `calibrate` requires the satellite to be pointing at that target, so one
of them must be turned to — and that turn is charged only when the target is
none of the directions already counted.  This cannot be double-counted with the
calibration itself: performing a `calibrate` requires already pointing at a
target, which is exactly the case where this term is zero.
-/
import Planner.ExampleHeuristics.Base

namespace Planner.ExampleHeuristics.Satellite

open Planner.Pddl

/-- An unmet `have_image` goal. -/
structure ImageGoal where
  goalFact : Fact
  /-- The direction, as an index. -/
  dir : Nat
  /-- The mode, as an index. -/
  mode : Nat
  deriving Inhabited

/-- A `pointing` goal: which satellite must end up looking where. -/
structure PointingGoal where
  goalFact : Fact
  sat : Nat
  dir : Nat
  deriving Inhabited

structure Data where
  images : Array ImageGoal
  pointingGoals : Array PointingGoal
  /-- For each instrument, its `calibrated` and `power_on` facts. -/
  calibratedFacts : Array (Option Fact)
  powerOnFacts : Array (Option Fact)
  /-- For each satellite, its `power_avail` fact. -/
  powerAvailFacts : Array (Option Fact)
  /-- Static structure: the modes each instrument supports, the instruments each
      satellite carries, and the direction each instrument calibrates against. -/
  supports : Array (Array Nat)
  onBoard : Array (Array Nat)
  calibTarget : Array (Option Nat)
  /-- The satellite each instrument is on board. -/
  satelliteOf : Array (Option Nat)
  /-- For each direction, the facts `pointing(s, d)` paired with the satellite. -/
  pointingByDir : Array (Array (Fact × Nat))
  deriving Inhabited

/--
The entry one `have_image` goal contributes.

Split out of `compile` as a named `filterMap` rather than written as a loop over
a mutable array: `Proofs/Lifted/SatelliteCompile.lean` reads the table entry by
entry, and a `filterMap` is what that reading needs.  It computes exactly what
the loop did.
-/
def imageEntry (t : Task) (dirIndex modeIndex : Name → Option Nat)
    (x : GroundAtom × Nat) : Option ImageGoal :=
  match x.1.pred == "have_image", x.1.args with
  | true, [d, m] =>
      match dirIndex d, modeIndex m with
      | some di, some mi => some { goalFact := t.goal.getD x.2 0, dir := di, mode := mi }
      | _, _ => none
  | _, _ => none

/-- The entry one `pointing` goal contributes. -/
def pointingEntry (t : Task) (satIndex dirIndex : Name → Option Nat)
    (x : GroundAtom × Nat) : Option PointingGoal :=
  match x.1.pred == "pointing", x.1.args with
  | true, [sat, dir] =>
      match satIndex sat, dirIndex dir with
      | some si, some di => some { goalFact := t.goal.getD x.2 0, sat := si, dir := di }
      | _, _ => none
  | _, _ => none

def compile (t : Task) : Data :=
  let directions := t.objectsOfTypes ["direction"]
  let modes := t.objectsOfTypes ["mode"]
  let instruments := t.objectsOfTypes ["instrument"]
  let satellites := t.objectsOfTypes ["satellite"]
  let dirIndex : Name → Option Nat := fun d => directions.findIdx? (· == d)
  let modeIndex : Name → Option Nat := fun m => modes.findIdx? (· == m)
  let instrIndex : Name → Option Nat := fun i => instruments.findIdx? (· == i)
  let satIndex : Name → Option Nat := fun x => satellites.findIdx? (· == x)
  let supportsAtoms := t.staticWith "supports"
  let onBoardAtoms := t.staticWith "on_board"
  let targetAtoms := t.staticWith "calibration_target"
  { images := t.goalAtoms.zipIdx.filterMap (imageEntry t dirIndex modeIndex)
    pointingGoals := t.goalAtoms.zipIdx.filterMap (pointingEntry t satIndex dirIndex)
    powerAvailFacts := satellites.map fun sat =>
      ((t.factsWith "power_avail").find? fun y => y.2.args == [sat]).map (·.1)
    calibratedFacts := instruments.map fun ins =>
      ((t.factsWith "calibrated").find? fun y => y.2.args == [ins]).map (·.1)
    powerOnFacts := instruments.map fun ins =>
      ((t.factsWith "power_on").find? fun y => y.2.args == [ins]).map (·.1)
    supports := instruments.map fun ins =>
      supportsAtoms.filterMap fun a =>
        match a.args with
        | [x, m] => if x == ins then modeIndex m else none
        | _ => none
    calibTarget := instruments.map fun ins =>
      (targetAtoms.find? fun a =>
        match a.args with
        | [x, _] => x == ins
        | _ => false).bind fun a =>
          match a.args with
          | [_, dir] => dirIndex dir
          | _ => none
    onBoard := satellites.map fun sat =>
      onBoardAtoms.filterMap fun a =>
        match a.args with
        | [i, x] => if x == sat then instrIndex i else none
        | _ => none
    satelliteOf := instruments.map fun ins =>
      (onBoardAtoms.find? fun a =>
        match a.args with
        | [i, _] => i == ins
        | _ => false).bind fun a =>
          match a.args with
          | [_, sat] => satIndex sat
          | _ => none
    pointingByDir := directions.map fun d =>
      (t.factsWith "pointing").filterMap fun y =>
        match y.2.args with
        | [sat, x] => if x == d then (satIndex sat).map ((y.1, ·)) else none
        | _ => none }

/-- Instruments whose fact is currently true. -/
@[inline] def activeInstruments (facts : Array (Option Fact)) (s : State) : Array Nat :=
  facts.zipIdx.filterMap fun (f, i) =>
    match f with
    | some x => if s.test x then some i else none
    | none => none

@[inline] def calibratedNow (d : Data) (s : State) : Array Nat :=
  activeInstruments d.calibratedFacts s
@[inline] def poweredNow (d : Data) (s : State) : Array Nat :=
  activeInstruments d.powerOnFacts s
/-- Only an instrument that is powered *and* calibrated can take an image. -/
@[inline] def readyNow (d : Data) (s : State) : Array Nat :=
  (calibratedNow d s).filter (poweredNow d s).contains

@[inline] def unmetImages (d : Data) (s : State) : Array ImageGoal :=
  d.images.filter fun g => !s.test g.goalFact
@[inline] def unmetPointing (d : Data) (s : State) : Array PointingGoal :=
  d.pointingGoals.filter fun g => !s.test g.goalFact

@[inline] def supportsMode (d : Data) (set : Array Nat) (m : Nat) : Bool :=
  set.any fun i => (d.supports.getD i #[]).contains m

@[inline] def pointsAt (d : Data) (s : State) (sat dir : Nat) : Bool :=
  (d.pointingByDir.getD dir #[]).any fun x => x.2 == sat && s.test x.1

/-- A satellite already pointing at `dir` that can shoot without looking away. -/
@[inline] def covered (d : Data) (s : State) (dir mode : Nat) : Bool :=
  (d.pointingByDir.getD dir #[]).any fun x =>
    s.test x.1 &&
      (d.onBoard.getD x.2 #[]).any fun ins =>
        (d.supports.getD ins #[]).contains mode &&
          ((readyNow d s).contains ins || d.calibTarget.getD ins none == some dir)

/-- A turn already paid for by an unmet `pointing` goal at the same direction. -/
@[inline] def paidByGoal (d : Data) (s : State) (dir : Nat) : Bool :=
  (unmetPointing d s).any fun g => g.dir == dir

/-- Directions an unmet image needs that nothing else already pays for. -/
@[inline] def dirsToTurn (d : Data) (s : State) : List Nat :=
  distinct ((unmetImages d s).toList.filterMap fun img =>
    if !paidByGoal d s img.dir && !covered d s img.dir img.mode then some img.dir else none)

@[inline] def neededModes (d : Data) (s : State) : List Nat :=
  distinct ((unmetImages d s).toList.map (·.mode))

@[inline] def uncalibratedModes (d : Data) (s : State) : List Nat :=
  (neededModes d s).filter fun m => !supportsMode d (readyNow d s) m
@[inline] def unpoweredModes (d : Data) (s : State) : List Nat :=
  (neededModes d s).filter fun m => !supportsMode d (poweredNow d s) m

/-- Instruments that must be made ready: two when no single one covers every mode. -/
@[inline] def coverCount (d : Data) (modesLeft : List Nat) : Nat :=
  if modesLeft.isEmpty then 0
  else if d.supports.any fun modesOf => modesLeft.all modesOf.contains then 1
  else 2

@[inline] def calibrationInReach (d : Data) (s : State) : Bool :=
  d.supports.zipIdx.any fun x =>
    x.1.any (neededModes d s).contains &&
      (match d.calibTarget.getD x.2 none, d.satelliteOf.getD x.2 none with
       | some target, some sat =>
           pointsAt d s sat target || (dirsToTurn d s).contains target ||
             (unmetPointing d s).any fun g => g.dir == target
       | _, _ => true)

/-- One turn to a calibration target, when none is already in reach. -/
@[inline] def approach (d : Data) (s : State) : Nat :=
  if !(uncalibratedModes d s).isEmpty && !calibrationInReach d s then 1 else 0

@[inline] def slotFree (d : Data) (s : State) : Bool :=
  d.supports.zipIdx.any fun x =>
    x.1.any (neededModes d s).contains &&
      (match d.satelliteOf.getD x.2 none with
       | some sat =>
           (match d.powerAvailFacts.getD sat none with
            | some f => s.test f
            | none => true)
       | none => true)

/-- One `switch_off` when every candidate instrument's satellite is already full. -/
@[inline] def freeSlot (d : Data) (s : State) : Nat :=
  if !(unpoweredModes d s).isEmpty && !slotFree d s then 1 else 0

/-- Images, calibrations, power: the actions that are not turns. -/
@[inline] def actionCount (d : Data) (s : State) : Nat :=
  (unmetImages d s).size + coverCount d (uncalibratedModes d s)
    + coverCount d (unpoweredModes d s) + freeSlot d s

/-- Turns: the unmet pointing goals, the image directions, and the calibration detour. -/
@[inline] def turns (d : Data) (s : State) : Nat :=
  (unmetPointing d s).size + (dirsToTurn d s).length + approach d s

/--
Four families that never share an action, bounded separately and added.

Written as named pieces rather than a loop over mutable counters: the pieces are
what the correctness argument talks about, so they are what the proof needs to
name.  It computes exactly what the loop version did.
-/
def value (d : Data) (s : State) : Nat := actionCount d s + turns d s

def improved (t : Task) : Heuristic :=
  let d := compile t
  { name := "satellite-improved", eval := value d }

end Planner.ExampleHeuristics.Satellite
