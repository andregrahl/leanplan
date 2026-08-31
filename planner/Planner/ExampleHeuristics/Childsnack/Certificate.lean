/-
Executable certificate for the improved Childsnack heuristic.
-/
import Planner.ExampleHeuristics.Certificate
import Planner.ExampleHeuristics.Childsnack.Domain
import Planner.Grounding

namespace Planner.ExampleHeuristics.Childsnack.Certificate

open Planner.Pddl

def goalKids (p : Problem) : List Name :=
  p.goal.filterMap fun a =>
    match a.pred == "served", a.args with
    | true, [k] => some k
    | _, _ => none

def atPairs (p : Problem) : List (Name × Name) :=
  p.init.filterMap fun a =>
    match a.pred == "at", a.args with
    | true, [t, q] => some (t, q)
    | _, _ => none

def onPairs (p : Problem) : List (Name × Name) :=
  p.init.filterMap fun a =>
    match a.pred == "ontray", a.args with
    | true, [sw, t] => some (sw, t)
    | _, _ => none

def notexistSws (p : Problem) : List Name :=
  p.init.filterMap fun a =>
    match a.pred == "notexist", a.args with
    | true, [sw] => some sw
    | _, _ => none

def kitchenSws (p : Problem) : List Name :=
  p.init.filterMap fun a =>
    match a.pred == "at_kitchen_sandwich", a.args with
    | true, [sw] => some sw
    | _, _ => none

def freeSws (p : Problem) : List Name :=
  p.init.filterMap fun a =>
    match a.pred == "no_gluten_sandwich", a.args with
    | true, [sw] => some sw
    | _, _ => none

def initInvCheck (p : Problem) : Bool :=
  (atPairs p).all (fun x => (atPairs p).all fun y => !(x.1 == y.1) || x.2 == y.2) &&
  (notexistSws p).all (fun sw =>
    ((onPairs p).all fun x => x.1 != sw) && !(kitchenSws p).contains sw &&
      !(freeSws p).contains sw) &&
  (kitchenSws p).all (fun sw => (onPairs p).all fun x => x.1 != sw) &&
  (onPairs p).all fun x => (onPairs p).all fun y => !(x.1 == y.1) || x.2 == y.2

def goalShape (p : Problem) : Bool :=
  p.goal.all fun a =>
    match a.pred == "served", a.args with
    | true, [_] => true
    | _, _ => false

def waitingUnique (p : Problem) : Bool :=
  p.init.all fun a =>
    p.init.all fun b =>
      !(a.pred == "waiting" && b.pred == "waiting" && a.args.head? == b.args.head?) ||
        a == b

def waitingTyped (d : Domain) (p : Problem) : Bool :=
  p.init.all fun a =>
    a.pred != "waiting" ||
      match a.args with
      | [_, q] => Planner.Certificate.objectNamedWithType d p q "place"
      | _ => false

def allergySeparated (p : Problem) : Bool :=
  p.init.all fun a =>
    p.init.all fun b =>
      !(a.pred == "not_allergic_gluten" && b.pred == "allergic_gluten") ||
        a.args != b.args

def noFreeInitially (p : Problem) : Bool :=
  p.init.all fun a => a.pred != "no_gluten_sandwich"

def goalChildrenTyped (d : Domain) (p : Problem) : Bool :=
  (goalKids p).all fun k => Planner.Certificate.objectNamedWithType d p k "child"

def childServable (p : Problem) : Bool :=
  (goalKids p).all fun k =>
    (p.init.any fun a => a.pred == "waiting" && a.args.headD "" == k) &&
      (p.init.contains { pred := "allergic_gluten", args := [k] } ||
        p.init.contains { pred := "not_allergic_gluten", args := [k] })

def conditions (d : Domain) (p : Problem) : Planner.Certificate :=
  [{ name := "Childsnack schemas", passed :=
       d.actions == Planner.GeneratedDomains.Childsnack.actions },
   { name := "Childsnack allergic predicate is static", passed :=
       (staticPredicates d).contains "allergic_gluten" },
   { name := "Childsnack nonallergic predicate is static", passed :=
       (staticPredicates d).contains "not_allergic_gluten" },
   { name := "Childsnack waiting predicate is static", passed :=
       (staticPredicates d).contains "waiting" },
   { name := "Childsnack sandwich type is declared", passed :=
       d.typeNames.contains "sandwich" },
   { name := "Childsnack tray type is declared", passed := d.typeNames.contains "tray" },
   { name := "Childsnack place type is declared", passed := d.typeNames.contains "place" },
   { name := "Childsnack child type is declared", passed := d.typeNames.contains "child" },
   { name := "Childsnack bread type is declared", passed :=
       d.typeNames.contains "bread-portion" },
   { name := "Childsnack content type is declared", passed :=
       d.typeNames.contains "content-portion" },
   { name := "Childsnack has a tray", passed := Planner.Certificate.hasObject d p "tray" },
   { name := "Childsnack has a sandwich", passed :=
       Planner.Certificate.hasObject d p "sandwich" },
   { name := "Childsnack kitchen is a place", passed :=
       Planner.Certificate.objectNamedWithType d p "kitchen" "place" },
   { name := "Childsnack goal shape", passed := goalShape p },
   { name := "Childsnack goal children are unique", passed := decide (goalKids p).Nodup },
   { name := "Childsnack sandwich type is exact", passed :=
       Planner.Certificate.exactType d p "sandwich" },
   { name := "Childsnack tray type is exact", passed :=
       Planner.Certificate.exactType d p "tray" },
   { name := "Childsnack place type is exact", passed :=
       Planner.Certificate.exactType d p "place" },
   { name := "Childsnack waiting places are unique", passed := waitingUnique p },
   { name := "Childsnack waiting places are typed", passed := waitingTyped d p },
   { name := "Childsnack allergy status is separated", passed := allergySeparated p },
   { name := "Childsnack sandwiches do not start gluten free", passed := noFreeInitially p },
   { name := "Childsnack goal is nonempty", passed := !(goalKids p).isEmpty },
   { name := "Childsnack goal children are typed", passed := goalChildrenTyped d p },
   { name := "Childsnack goal children are servable", passed := childServable p },
   { name := "Childsnack initial invariant", passed := initInvCheck p }]

def certified (d : Domain) (p : Problem) : Bool :=
  (conditions d p).passes

def check (d : Domain) (p : Problem) (_rel : Bool) (_t : Task) : Planner.Certificate :=
  conditions d p

end Planner.ExampleHeuristics.Childsnack.Certificate
