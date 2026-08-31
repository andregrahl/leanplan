/-
Executable certificate for the improved Sokoban heuristic.

The certificate checks only the parsed domain and problem.  Its goal-box
condition therefore applies to both relevance settings, while the loader still
checks it for the exact task it is about to run.
-/
import Planner.ExampleHeuristics.Certificate
import Planner.ExampleHeuristics.Sokoban.Improved
import Planner.GeneratedDomains.Sokoban
import Planner.Grounding

namespace Planner.ExampleHeuristics.Sokoban.Certificate

open Planner.Pddl

/-- The map edges recorded in the initial state. -/
def adjacentTriples (p : Problem) : List (Name × Name × Name) :=
  p.init.filterMap fun a =>
    match a.pred == "adjacent", a.args with
    | true, [x, y, dd] => some (x, y, dd)
    | _, _ => none

/-- No map edge is a self-loop. -/
def noSelfAdjacent (p : Problem) : Bool :=
  (adjacentTriples p).all fun x => x.1 != x.2.1

/-- Every directed map edge has a reverse edge whose direction is well typed. -/
def adjacentReverses (d : Domain) (p : Problem) : Bool :=
  (adjacentTriples p).all fun x =>
    (adjacentTriples p).any fun y =>
      y.1 == x.2.1 && y.2.1 == x.1 &&
        Planner.Certificate.objectNamedWithType d p y.2.2 "direction"

/-- The box and destination named by every `at` goal. -/
def goalPairs (p : Problem) : List (Name × Name) :=
  p.goal.filterMap fun a =>
    match a.pred == "at", a.args with
    | true, [b, l] => some (b, l)
    | _, _ => none

/-- One goal destination per box. -/
def goalBoxesOne (p : Problem) : Bool :=
  (goalPairs p).all fun x =>
    (goalPairs p).all fun y => x.1 != y.1 || x.2 == y.2

/-- The position invariant required by the compiled position readers. -/
def initInvCheck (p : Problem) : Bool :=
  !(Planner.Certificate.initOnes p "at-robot").isEmpty &&
  ((Planner.Certificate.initOnes p "at-robot").all fun l =>
    (Planner.Certificate.initOnes p "at-robot").all fun l' => l == l') &&
  ((Planner.Certificate.initPairs p "at").all fun x =>
    (Planner.Certificate.initPairs p "at").all fun y =>
      (!(x.1 == y.1) || x.2 == y.2) && (!(x.2 == y.2) || x.1 == y.1)) &&
  ((Planner.Certificate.initOnes p "at-robot").all fun l =>
    (Planner.Certificate.initOnes p "clear").contains l) &&
  ((Planner.Certificate.initPairs p "at").all fun x =>
    !((Planner.Certificate.initOnes p "clear").contains x.2))

/-- Named conditions make a failed proof boundary visible at task load time. -/
def conditions (d : Domain) (p : Problem) : Planner.Certificate :=
  [{ name := "Sokoban schemas", passed :=
       d.actions == Planner.GeneratedDomains.Sokoban.actions },
   { name := "Sokoban location type is declared", passed :=
       d.typeNames.contains "location" },
   { name := "Sokoban direction type is declared", passed :=
       d.typeNames.contains "direction" },
   { name := "Sokoban box type is declared", passed :=
       d.typeNames.contains "box" },
   { name := "Sokoban location type is exact", passed :=
       Planner.Certificate.exactType d p "location" },
   { name := "Sokoban box type is exact", passed :=
       Planner.Certificate.exactType d p "box" },
   { name := "Sokoban goals are unique", passed := decide p.goal.Nodup },
   { name := "Sokoban adjacent predicate is static", passed :=
       (staticPredicates d).contains "adjacent" },
   { name := "Sokoban goals are dynamic", passed :=
       p.goal.all fun a => !(staticPredicates d).contains a.pred },
   { name := "Sokoban map has no self edges", passed := noSelfAdjacent p },
   { name := "Sokoban map edges reverse", passed := adjacentReverses d p },
   { name := "Sokoban initial position invariant", passed := initInvCheck p },
   { name := "Sokoban goal names each box once", passed := goalBoxesOne p }]

def certified (d : Domain) (p : Problem) : Bool :=
  (conditions d p).passes

def check (d : Domain) (p : Problem) (_rel : Bool) (_t : Task) : Planner.Certificate :=
  conditions d p

end Planner.ExampleHeuristics.Sokoban.Certificate
