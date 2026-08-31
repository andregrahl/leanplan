/-
Ferry, improved heuristic.

The ferry carries one car at a time, which is what makes an exact per-car count
admissible.  For every car whose destination goal is unmet:

  * ashore at the wrong place — `board`, at least one loaded `sail`, `debark`: 3;
  * aboard, with the ferry elsewhere than its destination — `sail`, `debark`: 2;
  * aboard, with the ferry already at its destination — `debark`: 1.

`board` and `debark` name one car each, so those never overlap between cars, and
no two cars are ever aboard at once, so neither do the loaded sails.

Empty sails are counted too.  To board a car the ferry has to be standing empty
where that car waits, and it can only get there empty by sailing empty or by
putting a car down there.  So every location holding a misplaced car, other than
the destination of some misplaced car and other than where an empty ferry already
stands, costs an empty sail — and empty sails are nobody's loaded sail.  (A plan
could instead land a *correctly placed* car there, but that costs a board, a sail
and a debark, three actions the count never claimed.)

One more action is always forced while a car is still waiting ashore:

  * an empty ferry parked where no car waits must sail — empty — before it can
    board anything, and an empty sail is nobody's loaded sail;
  * a ferry carrying a car must first put it down.  If it puts it down at its
    destination, and no car waits there, the ferry must then sail empty; if it
    puts it down anywhere else, that car needs a further `board`, `sail` and
    `debark`, three actions where only two were counted.  Either way at least one
    action beyond the count is required.
-/
import Planner.ExampleHeuristics.Base

namespace Planner.ExampleHeuristics.Ferry

open Planner.Pddl

/-- What the heuristic needs to know about one car with an unmet goal. -/
structure CarInfo where
  /-- The fact `at(car, destination)`. -/
  goalFact : Fact
  /-- The destination, as a location index. -/
  goalLoc : Nat
  /-- The facts `at(car, l)`, with `l`. -/
  atFacts : Array (Fact × Nat)
  /-- The fact `on(car)`. -/
  onFact : Option Fact
  deriving Inhabited

structure Data where
  /-- The facts `at-ferry(l)`, with `l`. -/
  ferryAt : Array (Fact × Nat)
  /-- The fact `empty-ferry`. -/
  emptyFact : Option Fact
  cars : Array CarInfo
  deriving Inhabited

/--
The entry for one goal atom: a car, its destination, where it can stand, and
whether it is aboard.  `none` when the atom is not a car's destination at a place
the task names.

Split out of `compile` as a `filterMap` rather than written as a loop over a
mutable array: `Proofs/Domains/Ferry.lean` pairs this list with the lifted
`Cfg`'s car list entry for entry, and a `filterMap` is what that pairing needs.
It computes exactly what the loop did.
-/
def carEntry (t : Task) (atFacts onFacts : Array (Fact × GroundAtom))
    (locIndex : Name → Option Nat) (x : GroundAtom × Nat) : Option CarInfo :=
  match x.1.pred == "at", x.1.args with
  | true, [c, g] =>
      (locIndex g).map fun gl =>
        { goalFact := t.goal.getD x.2 0
          goalLoc := gl
          atFacts := atFacts.filterMap fun (fa, b) =>
            match b.args with
            | [y, l] => if y == c then (locIndex l).map ((fa, ·)) else none
            | _ => none
          onFact := (onFacts.find? fun (_, b) => b.args == [c]).map (·.1) }
  | _, _ => none

def compile (t : Task) : Data :=
  let locations := t.objectsOfTypes ["location"]
  let locIndex : Name → Option Nat := fun l => locations.findIdx? (· == l)
  { ferryAt := (t.factsWith "at-ferry").filterMap fun (f, a) =>
      match a.args with
      | [l] => (locIndex l).map ((f, ·))
      | _ => none
    emptyFact := ((t.factsWith "empty-ferry").find? fun y => y.2.args == []).map (·.1)
    cars := t.goalAtoms.zipIdx.filterMap
      (carEntry t (t.factsWith "at") (t.factsWith "on") locIndex) }

/-- Cars whose destination goal is unmet. -/
@[inline] def unmetCars (d : Data) (s : State) : Array CarInfo :=
  d.cars.filter fun c => !s.test c.goalFact

/-- Is this car on the ferry? -/
@[inline] def onBoard (s : State) (c : CarInfo) : Bool :=
  match c.onFact with
  | some f => s.test f
  | none => false

/-- Where a car sits ashore, if it does. -/
@[inline] def carLoc (s : State) (c : CarInfo) : Option Nat :=
  (c.atFacts.find? fun x => s.test x.1).map (·.2)

/-- Where the ferry is. -/
@[inline] def ferryLoc (d : Data) (s : State) : Option Nat :=
  (d.ferryAt.find? fun x => s.test x.1).map (·.2)

/-- Is the ferry carrying nothing?  A task with no `empty-ferry` fact never says
so, and the count is only stronger for it. -/
@[inline] def ferryEmpty (d : Data) (s : State) : Bool :=
  match d.emptyFact with
  | some f => s.test f
  | none => false

@[inline] def aboardCars (d : Data) (s : State) : Array CarInfo :=
  (unmetCars d s).filter fun c => onBoard s c

@[inline] def ashoreCars (d : Data) (s : State) : Array CarInfo :=
  (unmetCars d s).filter fun c => !onBoard s c

/-- Three actions per car still ashore: board, sail, debark. -/
@[inline] def ashore (d : Data) (s : State) : Nat := 3 * (ashoreCars d s).size

/-- A car aboard needs a sail and a debark, or only a debark if already home. -/
@[inline] def aboard (d : Data) (s : State) : Nat :=
  (aboardCars d s).foldl (init := 0) fun acc c =>
    acc + (if ferryLoc d s == some c.goalLoc then 1 else 2)

@[inline] def waitingLocs (d : Data) (s : State) : List Nat :=
  distinct ((ashoreCars d s).toList.filterMap fun c => carLoc s c)

@[inline] def destinations (d : Data) (s : State) : List Nat :=
  distinct ((unmetCars d s).toList.map (·.goalLoc))

@[inline] def waitingHere (d : Data) (s : State) : Bool :=
  match ferryLoc d s with
  | some l => (waitingLocs d s).contains l
  | none => false

@[inline] def carriedGoal (d : Data) (s : State) : Option Nat :=
  (aboardCars d s).back?.map (·.goalLoc)

/-- One sail to bring the ferry to a car that is waiting. -/
@[inline] def repositioning (d : Data) (s : State) : Nat :=
  if (ashoreCars d s).isEmpty then 0
  else if ferryEmpty d s then (if waitingHere d s then 0 else 1)
  else match carriedGoal d s with
       | some g => if (waitingLocs d s).contains g then 0 else 1
       | none => 1

/-- Places the ferry must reach empty, and can only reach by sailing empty. -/
@[inline] def emptySails (d : Data) (s : State) : Nat :=
  ((waitingLocs d s).filter fun l =>
      !(destinations d s).contains l && !(ferryEmpty d s && ferryLoc d s == some l)).length

/--
Per-car boarding and sailing, plus the sails the ferry must make empty.

Written as named pieces rather than a loop over mutable counters: the pieces are
what the correctness argument talks about, so they are what the proof needs to
name.  It computes exactly what the loop version did.
-/
def value (d : Data) (s : State) : Nat :=
  ashore d s + aboard d s + max (repositioning d s) (emptySails d s)

def improved (t : Task) : Heuristic :=
  let d := compile t
  { name := "ferry-improved", eval := value d }

end Planner.ExampleHeuristics.Ferry
