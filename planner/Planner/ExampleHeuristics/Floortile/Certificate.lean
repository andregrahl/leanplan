/-
Executable certificate for the improved Floortile heuristic.

Floortile's record speaks about the grounded task, not only about the parsed
domain and problem, and it speaks about both relevance settings.  The
certificate therefore grounds the task both ways and checks the task-level
conditions on each.  This costs two groundings once, when the task is loaded,
and nothing during search.
-/
import Planner.ExampleHeuristics.Certificate
import Planner.ExampleHeuristics.Floortile.Improved
import Planner.GeneratedDomains.Floortile
import Planner.Grounding

namespace Planner.ExampleHeuristics.Floortile.Certificate

open Planner.Pddl

/-- The grid, the robots, and the colours never move. -/
def initInvCheck (p : Problem) : Bool :=
  ((Planner.Certificate.initPairs p "robot-at").all fun x =>
    (Planner.Certificate.initPairs p "robot-at").all fun y =>
      !(x.1 == y.1) || (x.2 == y.2)) &&
  ((Planner.Certificate.initPairs p "robot-has").all fun x =>
    (Planner.Certificate.initPairs p "robot-has").all fun y =>
      !(x.1 == y.1) || (x.2 == y.2)) &&
  ((Planner.Certificate.initPairs p "robot-at").all fun x =>
    (Planner.Certificate.initPairs p "robot-at").all fun y =>
      !(x.2 == y.2) || (x.1 == y.1)) &&
  ((Planner.Certificate.initPairs p "robot-at").all fun x =>
    !(Planner.Certificate.initOnes p "clear").contains x.2) &&
  ((Planner.Certificate.initOnes p "clear").all fun x =>
    (Planner.Certificate.initPairs p "painted").all fun y => !(y.1 == x)) &&
  ((Planner.Certificate.initPairs p "robot-at").all fun x =>
    (Planner.Certificate.initPairs p "painted").all fun y => !(y.1 == x.2))

/-- The map conditions, on one grounded task. -/
def mapConds (t : Task) : Bool :=
  let ups := t.staticWith "up"
  let downs := t.staticWith "down"
  (ups.all fun a => a.args.length == 2) &&
  (downs.all fun a => a.args.length == 2) &&
  (ups.all fun a => ups.all fun b =>
    !(a.args.getD 0 "" == b.args.getD 0 "") || a.args.getD 1 "" == b.args.getD 1 "") &&
  (ups.all fun a => ups.all fun b =>
    !(a.args.getD 1 "" == b.args.getD 1 "") || a.args.getD 0 "" == b.args.getD 0 "") &&
  (downs.all fun a =>
    ups.contains { pred := "up", args := [a.args.getD 1 "", a.args.getD 0 ""] })

/-- The table conditions, on one grounded task. -/
def tableConds (t : Task) : Bool :=
  let tiles := t.objectsOfTypes ["tile"]
  let colours := t.objectsOfTypes ["color"]
  let graph := moveGraph t tiles
  let data := compile t
  (t.goalAtomsWith "painted").all (fun a => colours.contains (a.args.getD 1 "")) &&
  (data.clearFacts.zipIdx.all fun x =>
    match x.1 with
    | none => true
    | some f =>
        t.factNames.getD f default ==
          ({ pred := "clear", args := [graph.nodes.getD x.2 ""] } : GroundAtom)) &&
  (data.tiles.all fun q1 => data.tiles.all fun q2 =>
    !((t.factNames.getD q1.goalFact default).args.getD 0 "" ==
      (t.factNames.getD q2.goalFact default).args.getD 0 "") ||
      t.factNames.getD q1.goalFact default == t.factNames.getD q2.goalFact default) &&
  decide (2 * data.tiles.size + max data.dist.bound data.tiles.size ≤ deadEnd)

/-- Everything the record asks of the task, for one relevance setting. -/
def taskConds (d : Domain) (p : Problem) (rel : Bool) : Bool :=
  let t := Planner.ground d p rel
  mapConds t && tableConds t

/-- The goal names each tile once, so the compiled tile table has one entry per
tile and no two entries agree on the tile they name. -/
def goalTileUnique (p : Problem) : Bool :=
  p.goal.all fun a =>
    p.goal.all fun b =>
      !(a.pred == "painted" && b.pred == "painted" &&
        a.args.getD 0 "" == b.args.getD 0 "") || a == b

/-- Named conditions make a failed proof boundary visible at task load time. -/
def conditions (d : Domain) (p : Problem) : Planner.Certificate :=
  [{ name := "Floortile schemas", passed :=
       d.actions == Planner.GeneratedDomains.Floortile.actions },
   { name := "Floortile up predicate is static", passed :=
       (staticPredicates d).contains "up" },
   { name := "Floortile down predicate is static", passed :=
       (staticPredicates d).contains "down" },
   { name := "Floortile left predicate is static", passed :=
       (staticPredicates d).contains "left" },
   { name := "Floortile right predicate is static", passed :=
       (staticPredicates d).contains "right" },
   { name := "Floortile no goal asks for a grid edge", passed :=
       p.goal.all fun a =>
         a.pred != "up" && a.pred != "down" && a.pred != "left" && a.pred != "right" },
   { name := "Floortile initial state invariant", passed := initInvCheck p },
   { name := "Floortile tile type is exact", passed :=
       Planner.Certificate.exactType d p "tile" },
   { name := "Floortile robot type is exact", passed :=
       Planner.Certificate.exactType d p "robot" },
   { name := "Floortile color type is exact", passed :=
       Planner.Certificate.exactType d p "color" },
   { name := "Floortile goals are unique", passed := decide p.goal.Nodup },
   { name := "Floortile goal names each tile once", passed := goalTileUnique p },
   { name := "Floortile grid and tables, relevance disabled", passed :=
       taskConds d p false },
   { name := "Floortile grid and tables, relevance enabled", passed :=
       taskConds d p true }]

def certified (d : Domain) (p : Problem) : Bool :=
  (conditions d p).passes

def check (d : Domain) (p : Problem) (_rel : Bool) (_t : Task) : Planner.Certificate :=
  conditions d p

end Planner.ExampleHeuristics.Floortile.Certificate
