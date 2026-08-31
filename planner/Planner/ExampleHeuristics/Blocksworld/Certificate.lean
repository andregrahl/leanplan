/-
Executable certificate for the improved Blocks World heuristic.

Blocks World is the only domain whose record carries a second invariant beside
the physical one: no block stands above itself.  A cycle is not a physical
state, but nothing in the physical invariant rules it out, and the must-move
analysis climbs towers and has to reach the bottom of one.  The check below
follows each block's support and requires the climb to fall off the top of the
tower within the number of `on` facts.
-/
import Planner.ExampleHeuristics.Certificate
import Planner.ExampleHeuristics.Blocksworld.Improved
import Planner.GeneratedDomains.Blocksworld
import Planner.Grounding

namespace Planner.ExampleHeuristics.Blocksworld.Certificate

open Planner.Pddl

/-- The block a block stands on, as `:init` records it. -/
def supportOf (p : Problem) (x : Name) : Option Name :=
  ((Planner.Certificate.initPairs p "on").find? fun y => y.1 == x).map (·.2)

/-- Follow the supports `k` times. -/
def climb (p : Problem) : Nat → Name → Option Name
  | 0, x => some x
  | k + 1, x => (supportOf p x).bind (climb p k)

/-- Every tower ends: from every block, following supports falls off within the
number of `on` facts. -/
def acyclicCheck (p : Problem) : Bool :=
  (Planner.Certificate.initPairs p "on").all fun e =>
    climb p ((Planner.Certificate.initPairs p "on").length + 1) e.1 == none

/-- The physical invariant, decided over `:init`. -/
def initInvCheck (p : Problem) : Bool :=
  let ons := Planner.Certificate.initPairs p "on"
  let tables := Planner.Certificate.initOnes p "on-table"
  let helds := Planner.Certificate.initOnes p "holding"
  let clears := Planner.Certificate.initOnes p "clear"
  -- at most one block on any block, and a block on at most one block
  (ons.all fun x => ons.all fun y => !(x.2 == y.2) || (x.1 == y.1)) &&
  (ons.all fun x => ons.all fun y => !(x.1 == y.1) || (x.2 == y.2)) &&
  -- the hand holds at most one block
  (helds.all fun x => helds.all fun y => x == y) &&
  -- a block standing on something is not on the table
  (ons.all fun x => !tables.contains x.1) &&
  -- `arm-empty` holds exactly when nothing is held
  ((p.init.contains { pred := "arm-empty", args := [] }) == helds.isEmpty) &&
  -- a held block is free, and never clear
  (helds.all fun x =>
    (ons.all fun y => y.1 != x && y.2 != x) && !tables.contains x && !clears.contains x) &&
  -- nothing on the table is also standing on a block
  (ons.all fun x => tables.all fun y => x.1 != y) &&
  -- a clear block supports nothing
  (clears.all fun y => ons.all fun z => z.2 != y)

/-- Named conditions make a failed proof boundary visible at task load time. -/
def conditions (d : Domain) (p : Problem) : Planner.Certificate :=
  [{ name := "Blocksworld schemas", passed :=
       d.actions == Planner.GeneratedDomains.Blocksworld.actions },
   { name := "Blocksworld object type is declared", passed :=
       d.typeNames.contains "object" },
   { name := "Blocksworld goal on atoms name two blocks", passed :=
       p.goal.all fun a => a.pred != "on" || a.args.length == 2 },
   { name := "Blocksworld task has a block", passed :=
       !(allObjects d p).isEmpty },
   { name := "Blocksworld goals are unique", passed := decide p.goal.Nodup },
   { name := "Blocksworld initial state is physical", passed := initInvCheck p },
   { name := "Blocksworld no block stands above itself", passed := acyclicCheck p }]

def certified (d : Domain) (p : Problem) : Bool :=
  (conditions d p).passes

def check (d : Domain) (p : Problem) (_rel : Bool) (_t : Task) : Planner.Certificate :=
  conditions d p

end Planner.ExampleHeuristics.Blocksworld.Certificate
