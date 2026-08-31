/-
Executable certificate for the improved Rovers heuristic.

Every quantified condition of the proof's record is evaluated over the finite
object list, goal list, or initial state.  The two map conditions are the ones
the relevance argument rests on: a traversal that reverses keeps a rover's
destination relevant, and a traversal that is not a self-loop keeps the `at`
delete visible to `OpFacts`.
-/
import Planner.ExampleHeuristics.Certificate
import Planner.ExampleHeuristics.Rovers.Improved
import Planner.GeneratedDomains.Rovers
import Planner.Grounding

namespace Planner.ExampleHeuristics.Rovers.Certificate

open Planner.Pddl

/-- No rover has two initial positions. -/
def initInvCheck (p : Problem) : Bool :=
  (Planner.Certificate.initPairs p "at").all fun x =>
    (Planner.Certificate.initPairs p "at").all fun y =>
      !(x.1 == y.1) || (x.2 == y.2)

/-- No waypoint is traversable to itself. -/
def noSelfTraverse (p : Problem) : Bool :=
  (Planner.Certificate.initTriples p "can_traverse").all fun x => x.2.1 != x.2.2

/-- Every traversal a rover can see reverses, both in `can_traverse` and in
`visible`. -/
def traverseReverses (p : Problem) : Bool :=
  (Planner.Certificate.initTriples p "can_traverse").all fun x =>
    !((Planner.Certificate.initPairs p "visible").contains (x.2.1, x.2.2)) ||
      ((Planner.Certificate.initTriples p "can_traverse").contains (x.1, x.2.2, x.2.1) &&
        (Planner.Certificate.initPairs p "visible").contains (x.2.2, x.2.1))

/-- Named conditions make a failed proof boundary visible at task load time. -/
def conditions (d : Domain) (p : Problem) : Planner.Certificate :=
  [{ name := "Rovers schemas", passed :=
       d.actions == Planner.GeneratedDomains.Rovers.actions },
   { name := "Rovers rover type is declared", passed := d.typeNames.contains "rover" },
   { name := "Rovers waypoint type is declared", passed :=
       d.typeNames.contains "waypoint" },
   { name := "Rovers store type is declared", passed := d.typeNames.contains "store" },
   { name := "Rovers camera type is declared", passed := d.typeNames.contains "camera" },
   { name := "Rovers mode type is declared", passed := d.typeNames.contains "mode" },
   { name := "Rovers lander type is declared", passed := d.typeNames.contains "lander" },
   { name := "Rovers objective type is declared", passed :=
       d.typeNames.contains "objective" },
   { name := "Rovers rover type is exact", passed :=
       Planner.Certificate.exactType d p "rover" },
   { name := "Rovers waypoint type is exact", passed :=
       Planner.Certificate.exactType d p "waypoint" },
   { name := "Rovers goals are unique", passed := decide p.goal.Nodup },
   { name := "Rovers can_traverse predicate is static", passed :=
       (staticPredicates d).contains "can_traverse" },
   { name := "Rovers visible predicate is static", passed :=
       (staticPredicates d).contains "visible" },
   { name := "Rovers soil equipment predicate is static", passed :=
       (staticPredicates d).contains "equipped_for_soil_analysis" },
   { name := "Rovers rock equipment predicate is static", passed :=
       (staticPredicates d).contains "equipped_for_rock_analysis" },
   { name := "Rovers goals are dynamic", passed :=
       p.goal.all fun a => !(staticPredicates d).contains a.pred },
   { name := "Rovers initial position invariant", passed := initInvCheck p },
   { name := "Rovers map has no self traversals", passed := noSelfTraverse p },
   { name := "Rovers traversals reverse", passed := traverseReverses p }]

def certified (d : Domain) (p : Problem) : Bool :=
  (conditions d p).passes

def check (d : Domain) (p : Problem) (_rel : Bool) (_t : Task) : Planner.Certificate :=
  conditions d p

end Planner.ExampleHeuristics.Rovers.Certificate
