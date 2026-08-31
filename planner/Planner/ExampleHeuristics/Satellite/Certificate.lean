/-
Executable certificate for the improved Satellite heuristic.

All checks inspect only the parsed domain and problem.  In particular, the
single parsed-goal uniqueness check implies uniqueness of both compiled goal
tables for either relevance setting.
-/
import Planner.ExampleHeuristics.Certificate
import Planner.ExampleHeuristics.Satellite.Improved
import Planner.GeneratedDomains.Satellite
import Planner.Grounding

namespace Planner.ExampleHeuristics.Satellite.Certificate

open Planner.Pddl

/-- A two-argument initial relation is a partial function on its first argument. -/
def firstUnique (p : Problem) (pred : Name) : Bool :=
  (Planner.Certificate.initPairs p pred).all fun x =>
    (Planner.Certificate.initPairs p pred).all fun y =>
      x.1 != y.1 || x.2 == y.2

/-- No initial pointing fact is contradicted by `not-pointing`. -/
def pointingConsistent (p : Problem) : Bool :=
  (Planner.Certificate.initPairs p "pointing").all fun x =>
    !(Planner.Certificate.initPairs p "not-pointing").contains x

/-- Every instrument assigned to a satellite starts switched off. -/
def boardPowerOff (p : Problem) : Bool :=
  (Planner.Certificate.initPairs p "on_board").all fun x =>
    !(Planner.Certificate.initOnes p "power_on").contains x.1

/-- Named conditions make a failed proof boundary visible at task load time. -/
def conditions (d : Domain) (p : Problem) : Planner.Certificate :=
  [{ name := "Satellite schemas", passed :=
       d.actions == Planner.GeneratedDomains.Satellite.actions },
   { name := "Satellite satellite type is exact", passed :=
       Planner.Certificate.exactType d p "satellite" },
   { name := "Satellite direction type is exact", passed :=
       Planner.Certificate.exactType d p "direction" },
   { name := "Satellite instrument type is exact", passed :=
       Planner.Certificate.exactType d p "instrument" },
   { name := "Satellite mode type is exact", passed :=
       Planner.Certificate.exactType d p "mode" },
   { name := "Satellite satellite type is declared", passed :=
       d.typeNames.contains "satellite" },
   { name := "Satellite direction type is declared", passed :=
       d.typeNames.contains "direction" },
   { name := "Satellite instrument type is declared", passed :=
       d.typeNames.contains "instrument" },
   { name := "Satellite mode type is declared", passed :=
       d.typeNames.contains "mode" },
   { name := "Satellite on_board predicate is static", passed :=
       (staticPredicates d).contains "on_board" },
   { name := "Satellite supports predicate is static", passed :=
       (staticPredicates d).contains "supports" },
   { name := "Satellite calibration_target predicate is static", passed :=
       (staticPredicates d).contains "calibration_target" },
   { name := "Satellite goals are dynamic", passed :=
       p.goal.all fun a => !(staticPredicates d).contains a.pred },
   { name := "Satellite instruments have one carrier", passed :=
       firstUnique p "on_board" },
   { name := "Satellite instruments have one calibration target", passed :=
       firstUnique p "calibration_target" },
   { name := "Satellite satellites have one initial pointing", passed :=
       firstUnique p "pointing" },
   { name := "Satellite initial pointing is consistent", passed :=
       pointingConsistent p },
   { name := "Satellite on-board instruments start powered off", passed :=
       boardPowerOff p },
   { name := "Satellite goals are unique", passed := decide p.goal.Nodup }]

def certified (d : Domain) (p : Problem) : Bool :=
  (conditions d p).passes

def check (d : Domain) (p : Problem) (_rel : Bool) (_t : Task) : Planner.Certificate :=
  conditions d p

end Planner.ExampleHeuristics.Satellite.Certificate
