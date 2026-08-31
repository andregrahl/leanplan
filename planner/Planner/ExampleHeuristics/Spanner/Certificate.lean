/-
Executable certificate for the improved Spanner heuristic.
-/
import Planner.ExampleHeuristics.Certificate
import Planner.ExampleHeuristics.Spanner.Domain
import Planner.ExampleHeuristics.Spanner.Improved
import Planner.Grounding

namespace Planner.ExampleHeuristics.Spanner.Certificate

open Planner.Pddl

def initInvCheck (p : Problem) : Bool :=
  ((Planner.Certificate.initPairs p "at").all fun x =>
    (Planner.Certificate.initPairs p "at").all fun y =>
      !(x.1 == y.1) || x.2 == y.2) &&
  ((Planner.Certificate.initOnes p "loose").all fun n =>
    !(p.init.contains { pred := "tightened", args := [n] })) &&
  ((Planner.Certificate.initPairs p "carrying").all fun x =>
    (Planner.Certificate.initPairs p "at").all fun y => !(y.1 == x.2))

def sizeBound (t : Task) : Bool :=
  let c := ExampleHeuristics.Spanner.compile t
  decide (2 * c.nuts.size + c.dist.bound ≤ deadEnd)

def conditions (d : Domain) (p : Problem) (t : Task) : Planner.Certificate :=
  [{ name := "Spanner schemas", passed :=
       d.actions == Planner.GeneratedDomains.Spanner.actions },
   { name := "Spanner location type is exact", passed :=
       Planner.Certificate.exactType d p "location" },
   { name := "Spanner man type is exact", passed :=
       Planner.Certificate.exactType d p "man" },
   { name := "Spanner object type is exact", passed :=
       Planner.Certificate.exactType d p "spanner" },
   { name := "Spanner nuts are not men", passed :=
       Planner.Certificate.disjointTypes d p "nut" "man" },
   { name := "Spanner nuts are not spanners", passed :=
       Planner.Certificate.disjointTypes d p "nut" "spanner" },
   { name := "Spanner objects are not men", passed :=
       Planner.Certificate.disjointTypes d p "spanner" "man" },
   { name := "Spanner link predicate is static", passed :=
       (staticPredicates d).contains "link" },
   { name := "Spanner goals contain no links", passed :=
       p.goal.all fun a => a.pred != "link" },
   { name := "Spanner goals are unique", passed := decide p.goal.Nodup },
   { name := "Spanner initial invariant", passed := initInvCheck p },
   { name := "Spanner heuristic bound fits dead end", passed := sizeBound t }]

def certified (d : Domain) (p : Problem) (t : Task) : Bool :=
  (conditions d p t).passes

def check (d : Domain) (p : Problem) (_rel : Bool) (t : Task) : Planner.Certificate :=
  conditions d p t

end Planner.ExampleHeuristics.Spanner.Certificate
