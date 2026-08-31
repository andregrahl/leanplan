/-
Floortile, improved heuristic.

Three schema families that never share an action — `paint_*`, `change_color`,
`move_*` — are bounded separately and added.

  * `paint_up` and `paint_down` colour exactly one tile, so one is needed per
    unpainted goal tile.
  * `change_color` gives one robot one colour.  A colour some goal tile still
    needs and no robot is holding costs at least one, and those counts are one
    per colour, so they add.
  * `move_*` shifts one robot one square.  Three bounds are available and the
    largest is used; the third is by far the strongest.

The third comes from painting making a tile permanently impassable.  Take a goal
tile with nothing but goal tiles above it, all the way to the top of the grid.
The topmost of them has no square above it at all, so it can only be painted from
below.  The one under it therefore cannot be painted from above — that square
gets painted first, and nobody can stand on it afterwards — so it too must be
painted from below, and so on all the way down.  Every such tile has a *forced*
painting square, the one directly beneath it; a robot has to stand on each, they
are all distinct, and each one no robot occupies now costs at least one move.

The same fact gives a dead-end test.  A painted tile is never clear again, so the
region a robot can walk in only ever shrinks.  If no square a tile could be
painted from is still reachable, that tile can never be painted and the state has
no plan at all — which happens constantly here, because a robot that paints in
the wrong order walls itself off.  Those states are reported as dead ends and the
search drops them.

Painting cannot collapse the colour term: `paint_up` needs the robot to be
holding the colour it paints with, so that colour was never being counted.  Nor
can it collapse either movement term: the robot doing the painting is already in
a painting position for that tile, so the tile's distance is zero and it was not
among the tiles nobody stands ready to paint.
-/
import Planner.ExampleHeuristics.Base
import Planner.Distance

namespace Planner.ExampleHeuristics.Floortile

open Planner.Pddl

/-- One unpainted goal tile. -/
structure TileGoal where
  goalFact : Fact
  /-- The colour it must end up, as an index. -/
  colour : Nat
  /-- The squares a robot can paint it from: those directly below and above it. -/
  paintFrom : Array Nat
  /-- The square directly beneath, when this tile can only be painted from there. -/
  forcedFrom : Option Nat
  deriving Inhabited

structure Data where
  dist : Distances
  /-- Adjacency of the move graph, for walking the still-clear region. -/
  adj : Array (Array Nat)
  /-- For each tile, its `clear` fact. -/
  clearFacts : Array (Option Fact)
  /-- For each robot, the facts `robot-at(r, x)` with the tile index. -/
  robotAt : Array (Array (Fact × Nat))
  /-- For each colour, the facts `robot-has(r, c)` over all robots. -/
  hasColour : Array (Array Fact)
  tiles : Array TileGoal
  deriving Inhabited

/--
The edges robots may walk along.

`move_up(r, x, y)` needs `up(y, x)`, so the robot goes from `x` to `y`: the atom
names its ends in the opposite order to the edge, and the four map relations are
all read the same way.
-/
def moveEdges (t : Task) : Array GroundAtom :=
  t.staticAtoms.filterMap fun a =>
    if ["up", "down", "left", "right"].contains a.pred then
      match a.args with
      | [y, x] => some { pred := a.pred, args := [x, y] }
      | _ => none
    else none

/-- Robots move to a neighbouring square along `up`, `down`, `left` or `right`. -/
def moveGraph (t : Task) (tiles : Array Name) : Graph :=
  Graph.ofEdges tiles (moveEdges t)

/-- The `robot-at` facts of one robot, each with the tile's node index. -/
def robotAtOf (atFacts : Array (Fact × GroundAtom)) (graph : Graph) (r : Name) :
    Array (Fact × Nat) :=
  atFacts.filterMap fun y =>
    match y.2.args with
    | [x, l] => if x == r then (graph.find? l).map ((y.1, ·)) else none
    | _ => none

/-- The `robot-has` facts naming one colour. -/
def hasColourOf (hasFacts : Array (Fact × GroundAtom)) (col : Name) : Array Fact :=
  hasFacts.filterMap fun y =>
    match y.2.args with
    | [_, x] => if x == col then some y.1 else none
    | _ => none

/--
The entry one `painted` goal contributes.

Split out of `compile` as a named `filterMap` rather than written as a loop over
a mutable array: `Proofs/Lifted/FloortileCompile.lean` reads the table entry by
entry.  It computes exactly what the loop did.
-/
def tileEntry (t : Task) (colours : Array Name) (paintPositions : Name → Array Nat)
    (forced : Name → Option Nat) (x : GroundAtom × Nat) : Option TileGoal :=
  match x.1.pred == "painted", x.1.args with
  | true, [y, c] =>
      (colours.findIdx? (· == c)).map fun ci =>
        { goalFact := t.goal.getD x.2 0, colour := ci
          paintFrom := paintPositions y, forcedFrom := forced y }
  | _, _ => none

/--
The squares a robot can paint tile `y` from.

`paint_up(r, y, x, c)` needs `up(y, x)`, `paint_down(r, y, x, c)` needs
`down(y, x)`; either way the robot stands on `x`.
-/
def paintPositions (ups downs : Array GroundAtom) (graph : Graph) (y : Name) :
    Array Nat :=
  (ups ++ downs).filterMap fun a =>
    match a.args with
    | [t', x] => if t' == y then graph.find? x else none
    | _ => none

/-- The two tiles a map atom names, when it names two. -/
def argPair (a : GroundAtom) : Option (Name × Name) :=
  match a.args with
  | [x, y] => some (x, y)
  | _ => none

/-- The tile directly beneath `y`, which `up(y, x)` names. -/
def belowOf (ups : Array GroundAtom) (y : Name) : Option Name :=
  (ups.find? fun a => (argPair a).any fun q => q.1 == y).bind fun a =>
    (argPair a).map (·.2)

/-- The tile directly above `y`. -/
def aboveOf (ups : Array GroundAtom) (y : Name) : Option Name :=
  (ups.find? fun a => (argPair a).any fun q => q.2 == y).bind fun a =>
    (argPair a).map (·.1)

/--
Is everything above this tile, right up to the top of the grid, a goal tile?

Running out of fuel answers no, not yes.  The chain above a tile is shorter than
the grid, so the answer is the same on any real map, and the proof then has the
one fact it needs: more fuel never turns a yes into a no.
-/
def cappedByGoals (ups : Array GroundAtom) (goalTiles : Array Name) :
    Nat → Name → Bool
  | 0, _ => false
  | fuel + 1, y =>
      match aboveOf ups y with
      | none => true
      | some z => goalTiles.contains z && cappedByGoals ups goalTiles fuel z

/-- The square a capped tile can only be painted from. -/
def forcedOf (ups : Array GroundAtom) (goalTiles : Array Name) (graph : Graph)
    (fuel : Nat) (y : Name) : Option Nat :=
  if cappedByGoals ups goalTiles fuel y then (belowOf ups y).bind graph.find? else none

/-- The goal tiles, in the order the goal names them. -/
def goalTilesOf (t : Task) : Array Name :=
  (t.goalAtomsWith "painted").filterMap fun a =>
    match a.args with
    | [y, _] => some y
    | _ => none

/-- The `clear` fact of one tile. -/
def clearFactOf (clearAtoms : Array (Fact × GroundAtom)) (x : Name) : Option Fact :=
  (clearAtoms.find? fun z => z.2.args == [x]).map (·.1)

def compile (t : Task) : Data :=
  let tileNames := t.objectsOfTypes ["tile"]
  let colours := t.objectsOfTypes ["color"]
  let graph := moveGraph t tileNames
  let robots := t.objectsOfTypes ["robot"]
  let ups := t.staticWith "up"
  let downs := t.staticWith "down"
  let goalTiles := goalTilesOf t
  { dist := Distances.of graph
    adj := graph.adj
    clearFacts := tileNames.map (clearFactOf (t.factsWith "clear"))
    robotAt := robots.map (robotAtOf (t.factsWith "robot-at") graph)
    hasColour := colours.map (hasColourOf (t.factsWith "robot-has"))
    tiles := t.goalAtoms.zipIdx.filterMap (tileEntry t colours
      (paintPositions ups downs graph)
      (forcedOf ups goalTiles graph tileNames.size)) }

/-- Where the robots are standing. -/
@[inline] def robotPos (d : Data) (s : State) : Array Nat :=
  d.robotAt.filterMap fun facts => (facts.find? fun (f, _) => s.test f).map (·.2)

/-- The squares a robot can still walk to: clear ones, plus the ones robots stand
on.  Another robot may move out of the way, so its square is treated as passable. -/
def reachable (d : Data) (s : State) : Array Bool :=
  let robots := robotPos d s
  reachFrom d.adj robots fun x =>
    robots.contains x ||
      (match d.clearFacts.getD x none with
       | some f => s.test f
       | none => false)

/-- Goal tiles still to be painted. -/
@[inline] def unpaintedTiles (d : Data) (s : State) : Array TileGoal :=
  d.tiles.filter fun t => !s.test t.goalFact

/-- A tile with nowhere left to paint it from: the state has no plan. -/
def isDead (d : Data) (s : State) : Bool :=
  let seen := reachable d s
  (unpaintedTiles d s).any fun tile =>
    match tile.forcedFrom with
    | some p => !seen.getD p false
    | none => !tile.paintFrom.any fun p => seen.getD p false

@[inline] def unpainted (d : Data) (s : State) : Nat := (unpaintedTiles d s).size

@[inline] def coloursNeeded (d : Data) (s : State) : List Nat :=
  distinct ((unpaintedTiles d s).toList.map (·.colour))

/-- One colour change per colour some tile needs and no robot holds. -/
@[inline] def recolours (d : Data) (s : State) : Nat :=
  ((coloursNeeded d s).filter fun c =>
      !(d.hasColour.getD c #[]).any fun f => s.test f).length

/-- The distance to the farthest square a tile can still be painted from. -/
@[inline] def travel (d : Data) (s : State) : Nat :=
  (unpaintedTiles d s).foldl (init := 0) fun acc tile =>
    max acc (tile.paintFrom.foldl (init := d.dist.bound) fun a x =>
      min a (d.dist.minFrom (robotPos d s) x))

/-- Tiles no robot is standing ready to paint; a square serves at most two. -/
@[inline] def unattended (d : Data) (s : State) : Nat :=
  ((unpaintedTiles d s).filter fun tile =>
      !tile.paintFrom.any (robotPos d s).contains).size

/-- Forced squares no robot occupies: each costs a move, and they are distinct. -/
@[inline] def forcedSquares (d : Data) (s : State) : List Nat :=
  distinct ((unpaintedTiles d s).toList.filterMap fun tile =>
    match tile.forcedFrom with
    | some p => if !(robotPos d s).contains p then some p else none
    | none => none)

/-- The movement bound: three lower bounds on the same family, combined by `max`. -/
@[inline] def movement (d : Data) (s : State) : Nat :=
  max (max (travel d s) ((unattended d s + 1) / 2)) (forcedSquares d s).length

/-- The numeric part, with the dead-end test removed. -/
@[inline] def baseValue (d : Data) (s : State) : Nat :=
  unpainted d s + recolours d s + movement d s

/--
Paints, colour changes and movement, guarded by the dead-end test.

Written as named pieces rather than a loop over mutable counters: the pieces are
what the correctness argument talks about, so they are what the proof needs to
name.  It computes exactly what the loop version did.
-/
def value (d : Data) (s : State) : Nat :=
  if isDead d s then deadEnd else baseValue d s

def improved (t : Task) : Heuristic :=
  let d := compile t
  { name := "floortile-improved", eval := value d }

end Planner.ExampleHeuristics.Floortile
