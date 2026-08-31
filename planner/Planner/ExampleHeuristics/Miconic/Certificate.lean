/-
Executable certificate for the improved Miconic heuristic.
-/
import Planner.ExampleHeuristics.Certificate
import Planner.ExampleHeuristics.Miconic.Domain
import Planner.Grounding

namespace Planner.ExampleHeuristics.Miconic.Certificate

open Planner.Pddl

def goalPass (p : Problem) : List Name :=
  p.goal.filterMap fun a =>
    match a.pred == "served", a.args with
    | true, [q] => some q
    | _, _ => none

def liftPlaces (p : Problem) : List Name :=
  p.init.filterMap fun a =>
    match a.pred == "lift-at", a.args with
    | true, [f] => some f
    | _, _ => none

def originPairs (p : Problem) : List (Name × Name) :=
  p.init.filterMap fun a =>
    match a.pred == "origin", a.args with
    | true, [q, f] => some (q, f)
    | _, _ => none

def initInvCheck (p : Problem) : Bool :=
  (liftPlaces p).all (fun f => (liftPlaces p).all fun g => f == g) &&
  (originPairs p).all fun x =>
    (originPairs p).all fun y => !(x.1 == y.1) || x.2 == y.2

def goalShape (p : Problem) : Bool :=
  p.goal.all fun a =>
    match a.pred == "served", a.args with
    | true, [_] => true
    | _, _ => false

def goalsTyped (d : Domain) (p : Problem) : Bool :=
  (goalPass p).all fun q =>
    Planner.Certificate.objectNamedWithType d p q "passenger"

def destinationsUnique (p : Problem) : Bool :=
  p.init.all fun a =>
    p.init.all fun b =>
      !(a.pred == "destin" && b.pred == "destin" && a.args.head? == b.args.head?) ||
        a == b

def destinationsTyped (d : Domain) (p : Problem) : Bool :=
  p.init.all fun a =>
    a.pred != "destin" ||
      match a.args with
      | [_, f] => Planner.Certificate.objectNamedWithType d p f "floor"
      | _ => false

def destinationsComplete (p : Problem) : Bool :=
  (goalPass p).all fun q =>
    p.init.any fun a => a.pred == "destin" && a.args.headD "" == q

def conditions (d : Domain) (p : Problem) : Planner.Certificate :=
  [{ name := "Miconic schemas", passed :=
       d.actions == Planner.GeneratedDomains.Miconic.actions },
   { name := "Miconic destin is static", passed :=
       (staticPredicates d).contains "destin" },
   { name := "Miconic floor type is declared", passed := d.typeNames.contains "floor" },
   { name := "Miconic passenger type is declared", passed :=
       d.typeNames.contains "passenger" },
   { name := "Miconic has a floor", passed := Planner.Certificate.hasObject d p "floor" },
   { name := "Miconic has a passenger", passed :=
       Planner.Certificate.hasObject d p "passenger" },
   { name := "Miconic goal shape", passed := goalShape p },
   { name := "Miconic goal passenger types", passed := goalsTyped d p },
   { name := "Miconic goal passengers are unique", passed := decide (goalPass p).Nodup },
   { name := "Miconic floor type is exact", passed :=
       Planner.Certificate.exactType d p "floor" },
   { name := "Miconic destinations are unique", passed := destinationsUnique p },
   { name := "Miconic destinations are typed", passed := destinationsTyped d p },
   { name := "Miconic goal is nonempty", passed := !(goalPass p).isEmpty },
   { name := "Miconic destinations are complete", passed := destinationsComplete p },
   { name := "Miconic initial invariant", passed := initInvCheck p }]

def certified (d : Domain) (p : Problem) : Bool :=
  (conditions d p).passes

def check (d : Domain) (p : Problem) (_rel : Bool) (_t : Task) : Planner.Certificate :=
  conditions d p

end Planner.ExampleHeuristics.Miconic.Certificate
