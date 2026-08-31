/-
Executable certificate for the improved Transport heuristic.

The value counts packages, so the certificate refuses a task whose goal names a
vehicle or asks for a road, and refuses a goal that names one object twice: two
destinations for one package are unreachable together and the value would count
both.
-/
import Planner.ExampleHeuristics.Certificate
import Planner.ExampleHeuristics.Transport.Improved
import Planner.GeneratedDomains.Transport
import Planner.Grounding

namespace Planner.ExampleHeuristics.Transport.Certificate

open Planner.Pddl

/-- No object is in two places, in two vehicles, or both at a place and inside a
vehicle. -/
def initInvCheck (p : Problem) : Bool :=
  ((Planner.Certificate.initPairs p "at").all fun x =>
    (Planner.Certificate.initPairs p "at").all fun y => !(x.1 == y.1) || (x.2 == y.2)) &&
  ((Planner.Certificate.initPairs p "in").all fun x =>
    (Planner.Certificate.initPairs p "in").all fun y => !(x.1 == y.1) || (x.2 == y.2)) &&
  ((Planner.Certificate.initPairs p "at").all fun x =>
    (Planner.Certificate.initPairs p "in").all fun y => !(x.1 == y.1))

/-- No `at` goal names a vehicle. -/
def goalNotVehicle (d : Domain) (p : Problem) : Bool :=
  p.goal.all fun a =>
    a.pred != "at" ||
      (allObjects d p).all fun o => o.name != a.args.headD "" || o.type != "vehicle"

/-- The goal names each object at most once. -/
def goalObjUnique (p : Problem) : Bool :=
  p.goal.all fun a =>
    p.goal.all fun b =>
      !(a.pred == "at" && b.pred == "at" && a.args.headD "" == b.args.headD "") || a == b

/-- No vehicle is also a package. -/
def vehNotPackage (d : Domain) (p : Problem) : Bool :=
  (allObjects d p).all fun o => o.type != "vehicle" || !(d.isSubtype o.type "package")

/-- Named conditions make a failed proof boundary visible at task load time. -/
def conditions (d : Domain) (p : Problem) : Planner.Certificate :=
  [{ name := "Transport schemas", passed :=
       d.actions == Planner.GeneratedDomains.Transport.actions },
   { name := "Transport location type is exact", passed :=
       Planner.Certificate.exactType d p "location" },
   { name := "Transport vehicle type is exact", passed :=
       Planner.Certificate.exactType d p "vehicle" },
   { name := "Transport no goal names a vehicle", passed := goalNotVehicle d p },
   { name := "Transport road predicate is static", passed :=
       (staticPredicates d).contains "road" },
   { name := "Transport no goal asks for a road", passed :=
       p.goal.all fun a => a.pred != "road" },
   { name := "Transport goal names each object once", passed := goalObjUnique p },
   { name := "Transport goals are unique", passed := decide p.goal.Nodup },
   { name := "Transport no vehicle is a package", passed := vehNotPackage d p },
   { name := "Transport initial position invariant", passed := initInvCheck p },
   { name := "Transport loading parameter types are declared", passed :=
       Planner.GeneratedDomains.Transport.action2.params.all fun pm =>
         d.typeNames.contains pm.type },
   { name := "Transport capacity-predecessor is static", passed :=
       (staticPredicates d).contains "capacity-predecessor" }]

def certified (d : Domain) (p : Problem) : Bool :=
  (conditions d p).passes

def check (d : Domain) (p : Problem) (_rel : Bool) (_t : Task) : Planner.Certificate :=
  conditions d p

end Planner.ExampleHeuristics.Transport.Certificate
