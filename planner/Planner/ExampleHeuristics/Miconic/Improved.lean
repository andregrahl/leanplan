/-
Miconic, improved heuristic.

Three disjoint families.

*Boarding and departing.*  A passenger who is still waiting needs a `board` and a
`depart`; one already aboard needs only a `depart`.  Both schemas name a single
passenger, so these counts add: `2·waiting + aboard`.

*Moving.*  The lift must stand on a passenger's origin floor to board them and on
their destination floor to let them out.  Every such floor other than the one the
lift is on now costs at least one `up` or `down`, and a move visits one floor, so
the number of distinct needed floors excluding the current one is a lower bound.

The moving term survives `board` and `depart` because those two only ever
discharge a floor the lift is *already* standing on, which the count excludes.

`up` and `down` reach any floor above or below in a single step, so a distance
table would say nothing here; counting distinct floors is what carries the
information.
-/
import Planner.ExampleHeuristics.Base

namespace Planner.ExampleHeuristics.Miconic

open Planner.Pddl

/-- What the heuristic needs to know about one passenger with an unmet goal. -/
structure PassengerInfo where
  /-- The fact `served(passenger)`. -/
  goalFact : Fact
  /-- The fact `boarded(passenger)`. -/
  boardedFact : Option Fact
  /-- The facts `origin(passenger, f)`, with the floor index. -/
  originFacts : Array (Fact × Nat)
  /-- The destination floor; `destin` is static, so it is fixed at compile time. -/
  destFloor : Option Nat
  deriving Inhabited

structure Data where
  /-- The facts `lift-at(f)`, with the floor index. -/
  liftAt : Array (Fact × Nat)
  passengers : Array PassengerInfo
  deriving Inhabited

/--
The entry for one goal atom: a passenger, where they wait, whether they are
aboard, and where they are going.  `none` when the atom is not a `served` goal.

Split out of `compile` as a `filterMap` rather than written as a loop over a
mutable array: `Proofs/Lifted/MiconicCompile.lean` pairs this list with the lifted
`Cfg`'s passenger list entry for entry, and a `filterMap` is what that pairing
needs.  It computes exactly what the loop did.
-/
def passengerEntry (t : Task) (originFacts boardedFacts : Array (Fact × GroundAtom))
    (destinAtoms : Array GroundAtom) (floorIndex : Name → Option Nat)
    (x : GroundAtom × Nat) : Option PassengerInfo :=
  match x.1.pred == "served", x.1.args with
  | true, [p] =>
      some
        { goalFact := t.goal.getD x.2 0
          boardedFact := (boardedFacts.find? fun (_, b) => b.args == [p]).map (·.1)
          originFacts := originFacts.filterMap fun (fo, b) =>
            match b.args with
            | [y, f] => if y == p then (floorIndex f).map ((fo, ·)) else none
            | _ => none
          destFloor := (destinAtoms.find? fun b =>
            match b.args with
            | [y, _] => y == p
            | _ => false).bind fun b =>
              match b.args with
              | [_, f] => floorIndex f
              | _ => none }
  | _, _ => none

def compile (t : Task) : Data :=
  let floors := t.objectsOfTypes ["floor"]
  let floorIndex : Name → Option Nat := fun f => floors.findIdx? (· == f)
  { liftAt := (t.factsWith "lift-at").filterMap fun (f, a) =>
      match a.args with
      | [x] => (floorIndex x).map ((f, ·))
      | _ => none
    passengers := t.goalAtoms.zipIdx.filterMap
      (passengerEntry t (t.factsWith "origin") (t.factsWith "boarded")
        (t.staticWith "destin") floorIndex) }

/-- Is this passenger already aboard? -/
@[inline] def aboard (p : PassengerInfo) (s : State) : Bool :=
  match p.boardedFact with
  | some f => s.test f
  | none => false

/-- The floor the lift is standing on. -/
@[inline] def currentFloor (d : Data) (s : State) : Option Nat :=
  (d.liftAt.find? fun (f, _) => s.test f).map (·.2)

/-- Passengers whose `served` goal is unmet. -/
@[inline] def unserved (d : Data) (s : State) : Array PassengerInfo :=
  d.passengers.filter fun p => !s.test p.goalFact

/-- Unserved and still waiting: they need a `board` and a `depart`. -/
@[inline] def waiting (d : Data) (s : State) : Array PassengerInfo :=
  (unserved d s).filter fun p => !aboard p s

/-- Unserved but aboard: they need only a `depart`. -/
@[inline] def riding (d : Data) (s : State) : Array PassengerInfo :=
  (unserved d s).filter fun p => aboard p s

/-- The floors one passenger still forces the lift to visit. -/
@[inline] def floorsNeeded (d : Data) (s : State) (p : PassengerInfo) : List Nat :=
  (if aboard p s then [] else
     match p.originFacts.find? fun (f, _) => s.test f with
     | some (_, fl) => [fl]
     | none => []) ++
  (match p.destFloor with
   | some fl => [fl]
   | none => [])

/-- The distinct floors still to visit, other than the one the lift is on. -/
@[inline] def neededFloors (d : Data) (s : State) : List Nat :=
  distinct (((unserved d s).toList.flatMap (floorsNeeded d s)).filter
      fun fl => currentFloor d s != some fl)

/--
Two actions per waiting passenger, one per rider, plus one move per floor still
needed other than the current one.

Written as named pieces rather than a loop over mutable counters: the pieces are
what the correctness argument talks about, so they are what the proof needs to
name.  It computes exactly what the loop version did.
-/
def value (d : Data) (s : State) : Nat :=
  2 * (waiting d s).size + (riding d s).size + (neededFloors d s).length

def improved (t : Task) : Heuristic :=
  let d := compile t
  { name := "miconic-improved", eval := value d }

end Planner.ExampleHeuristics.Miconic
