/-
Transport, improved heuristic.

Two disjoint families of actions are bounded separately and added.

*Loading.*  A package whose goal is unmet needs its own `drop`, and one more
`pick-up` if it is still on the ground; no `pick-up` or `drop` ever serves two
packages, so these counts add.

*Driving.*  A package must be carried over at least `d` roads, where `d` is the
road distance from where it is to where it must go — and if it is still on the
ground, some vehicle must first come and fetch it, which is `d` roads more from
the nearest vehicle.  A `drive` moves one vehicle one road, so it advances only
one package's requirement by one; taking the *maximum* over packages is therefore
a lower bound on the number of `drive` actions, while the sum would not be.

A second, quite different bound on the same `drive` actions: every location a
package still sits at, and every location one still has to reach, must have a
vehicle standing on it at some point.  A `drive` brings one vehicle to one
location, so the number of such locations that no vehicle occupies right now is
also a lower bound on the drives — and on a spread-out map it is much the larger
of the two.  The two drive bounds are combined with `max`.

The bounds add across schemas because `pick-up`/`drop` and `drive` are different
ones.  `pick-up` and `drop` leave both driving bounds exactly unchanged — a
package picked up at `l` is in a vehicle that is at `l`, and a package dropped at
its destination is at a location a vehicle occupies — which is what makes the sum
consistent as well as admissible.
-/
import Planner.ExampleHeuristics.Base
import Planner.Distance

namespace Planner.ExampleHeuristics.Transport

open Planner.Pddl

/-- What the heuristic needs to know about one package with an unmet goal. -/
structure PackageInfo where
  /-- The fact `at(package, destination)`. -/
  goalFact : Fact
  /-- The destination, as a node of the road graph. -/
  goalLoc : Nat
  /-- The facts `at(package, l)`, with `l`. -/
  atFacts : Array (Fact × Nat)
  /-- The facts `in(package, v)`, with the vehicle's index. -/
  inFacts : Array (Fact × Nat)
  deriving Inhabited

/-- Everything read from the task once, before search. -/
structure Data where
  dist : Distances
  /-- For each vehicle, the facts `at(vehicle, l)` with `l`. -/
  vehAt : Array (Array (Fact × Nat))
  packages : Array PackageInfo
  deriving Inhabited

/--
The `at` facts of one object, each paired with the graph node of the place it
names.

Split out of `compile` as a named `filterMap` rather than written inside it:
`Proofs/Lifted/TransportCompile.lean` reads the table entry by entry, and a named
function is what that reading needs.  It computes exactly what the loop did.
-/
def atOf (atFacts : Array (Fact × GroundAtom)) (graph : Graph) (who : Name) :
    Array (Fact × Nat) :=
  atFacts.filterMap fun y =>
    match y.2.args with
    | [x, l] => if x == who then (graph.find? l).map ((y.1, ·)) else none
    | _ => none

/-- The `in` facts of one package, each paired with the carrying vehicle's index. -/
def inOf (inFacts : Array (Fact × GroundAtom)) (vehicles : Array Name) (who : Name) :
    Array (Fact × Nat) :=
  inFacts.filterMap fun y =>
    match y.2.args with
    | [x, v] => if x == who then (vehicles.findIdx? (· == v)).map ((y.1, ·)) else none
    | _ => none

/-- The entry one goal atom contributes: a package whose destination is a node. -/
def packageEntry (t : Task) (graph : Graph) (at? in? : Name → Array (Fact × Nat))
    (x : GroundAtom × Nat) : Option PackageInfo :=
  match x.1.pred == "at", x.1.args with
  | true, [q, g] =>
      (graph.find? g).map fun gl =>
        { goalFact := t.goal.getD x.2 0
          goalLoc := gl
          atFacts := at? q
          inFacts := in? q }
  | _, _ => none

/-- Collect the road graph, the vehicles and the goal packages. -/
def compile (t : Task) : Data :=
  let graph := Graph.ofStatic t "road" (t.objectsOfTypes ["location"])
  let vehicles := t.objectsOfTypes ["vehicle"]
  let at? := atOf (t.factsWith "at") graph
  let in? := inOf (t.factsWith "in") vehicles
  { dist := Distances.of graph
    vehAt := vehicles.map at?
    packages := t.goalAtoms.zipIdx.filterMap (packageEntry t graph at? in?) }

/-- Where each vehicle currently is; `dist.bound` when it has no `at` fact. -/
@[inline] def vehicleLocations (d : Data) (s : State) : Array Nat :=
  d.vehAt.map fun facts =>
    match facts.find? fun (f, _) => s.test f with
    | some (_, l) => l
    | none => d.dist.bound

/-- Packages whose destination goal is unmet. -/
@[inline] def unmet (d : Data) (s : State) : Array PackageInfo :=
  d.packages.filter fun pk => !s.test pk.goalFact

/-- Where a package sits on the ground, if it does. -/
@[inline] def groundLoc (s : State) (pk : PackageInfo) : Option Nat :=
  (pk.atFacts.find? fun x => s.test x.1).map (·.2)

/-- The vehicle carrying a package, if one is. -/
@[inline] def carrier (s : State) (pk : PackageInfo) : Option Nat :=
  (pk.inFacts.find? fun x => s.test x.1).map (·.2)

/-- A package on the ground owes a `pick-up` and a `drop`; a loaded one owes a `drop`. -/
@[inline] def handlingCost (s : State) (pk : PackageInfo) : Nat :=
  match groundLoc s pk with
  | some _ => 2
  | none => match carrier s pk with
            | some _ => 1
            | none => 0

@[inline] def handling (d : Data) (s : State) : Nat :=
  (unmet d s).foldl (init := 0) fun acc pk => acc + handlingCost s pk

/-- How far some vehicle must still drive on this package's account. -/
@[inline] def drivingOf (d : Data) (s : State) (veh : Array Nat) (pk : PackageInfo) : Nat :=
  match groundLoc s pk with
  | some l => d.dist.minFrom veh l + d.dist.get l pk.goalLoc
  | none => match carrier s pk with
            | some v => d.dist.get (veh.getD v d.dist.bound) pk.goalLoc
            | none => 0

@[inline] def driving (d : Data) (s : State) : Nat :=
  (unmet d s).foldl (init := 0) fun acc pk =>
    max acc (drivingOf d s (vehicleLocations d s) pk)

/-- Locations a vehicle must still stand on, and is not standing on now. -/
@[inline] def requiredLocs (d : Data) (s : State) : List Nat :=
  distinct (((unmet d s).toList.flatMap fun pk =>
      pk.goalLoc :: (match groundLoc s pk with
                     | some l => [l]
                     | none => [])).filter
      fun l => !(vehicleLocations d s).contains l)

/--
The load and unload actions still required, plus the driving bound.

Written as named pieces rather than a loop over mutable counters: the pieces are
what the correctness argument talks about, so they are what the proof needs to
name.  It computes exactly what the loop version did.
-/
def value (d : Data) (s : State) : Nat :=
  handling d s + max (driving d s) (requiredLocs d s).length

def improved (t : Task) : Heuristic :=
  let d := compile t
  { name := "transport-improved", eval := value d }

end Planner.ExampleHeuristics.Transport
