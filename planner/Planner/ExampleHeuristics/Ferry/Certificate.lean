/-
Executable certificate for the improved Ferry heuristic.

Every quantified condition is evaluated over the finite object, goal, or
initial-state list.  Validation remains the first link in the loader chain and
supplies the object-name uniqueness used by the proof.
-/
import Planner.ExampleHeuristics.Certificate
import Planner.ExampleHeuristics.Ferry.Domain
import Planner.Pddl.Validation
import Planner.Task

namespace Planner.ExampleHeuristics.Ferry.Certificate

open Planner.Pddl

def goalPairs (p : Problem) : List (Name × Name) :=
  p.goal.filterMap fun a =>
    match a.pred == "at", a.args with
    | true, [q, g] => some (q, g)
    | _, _ => none

def atPairs (p : Problem) : List (Name × Name) :=
  p.init.filterMap fun a =>
    match a.pred == "at", a.args with
    | true, [q, f] => some (q, f)
    | _, _ => none

def onCars (p : Problem) : List Name :=
  p.init.filterMap fun a =>
    match a.pred == "on", a.args with
    | true, [q] => some q
    | _, _ => none

def ferryPlaces (p : Problem) : List Name :=
  p.init.filterMap fun a =>
    match a.pred == "at-ferry", a.args with
    | true, [f] => some f
    | _, _ => none

def initInvCheck (p : Problem) : Bool :=
  (ferryPlaces p).all (fun f => (ferryPlaces p).all fun g => f == g) &&
  (atPairs p).all (fun x => (atPairs p).all fun y => !(x.1 == y.1) || x.2 == y.2) &&
  (onCars p).all (fun q => (onCars p).all fun r => q == r) &&
  (!p.init.contains { pred := "empty-ferry", args := [] } || (onCars p).isEmpty) &&
  (onCars p).all fun q => (atPairs p).all fun x => x.1 != q

def goalsTyped (d : Domain) (p : Problem) : Bool :=
  (goalPairs p).all fun x =>
    Planner.Certificate.objectNamedWithType d p x.1 "car" &&
      Planner.Certificate.objectNamedWithType d p x.2 "location"

def everyCarHasGoal (d : Domain) (p : Problem) : Bool :=
  (allObjects d p).all fun o =>
    o.type != "car" || (goalPairs p).any fun x => x.1 == o.name

def certified (d : Domain) (p : Problem) : Bool :=
  (d.actions == Planner.GeneratedDomains.Ferry.actions) &&
  d.typeNames.contains "car" &&
  d.typeNames.contains "location" &&
  Planner.Certificate.hasObject d p "location" &&
  Planner.Certificate.hasObject d p "car" &&
  goalsTyped d p &&
  decide (goalPairs p).Nodup &&
  decide ((goalPairs p).map (·.1)).Nodup &&
  everyCarHasGoal d p &&
  Planner.Certificate.exactType d p "location" &&
  Planner.Certificate.exactType d p "car" &&
  initInvCheck p

def check (d : Domain) (p : Problem) (_rel : Bool) (_t : Task) : Planner.Certificate :=
  Planner.Certificate.one "Ferry pinned conditions" (certified d p)

end Planner.ExampleHeuristics.Ferry.Certificate
