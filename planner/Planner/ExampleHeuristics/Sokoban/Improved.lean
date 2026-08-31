/-
Sokoban, improved heuristic.

Two lower bounds, and the larger is used.

*Pushes.*  Every `push` moves exactly one box exactly one square, so the pushes
different boxes need never overlap and their distances add.  The distance is
measured in the *push graph*, not the grid: there is an edge from `b` to `f` only
when some `adjacent(r, b, d)` and `adjacent(b, f, d)` line up, so a box can only
leave a square in a direction the robot can stand behind, which makes walls and
corners visible where plain cell adjacency sees nothing.

*One box, exactly.*  Almost all the work in this domain is walking, which the
push count ignores entirely.  So for each box a second distance is computed in
the product space of *(box square, robot square)*: a `move` is an edge that
changes the robot's square, a `push` is an edge that changes both.  Every action
of any plan — including pushes of other boxes, which shift the robot one square —
is exactly one edge of that graph, so the distance to a state where this box sits
on its goal is a lower bound on the whole plan, and it drops by at most one per
action.  It is the exact cost of the relaxation that keeps one box and drops the
rest, which is why it is so much sharper than counting pushes.

Because those walks are shared between boxes, the per-box distances are combined
with `max` rather than summed.

*Pushes plus the approach.*  The push count alone says nothing about walking, and
the product distance only ever describes one box, so a third bound adds the two
kinds of action, which are disjoint: `push` and `move` are different schemas.
Every push needs the robot standing beside the box it moves, so before the very
first push of the plan the robot has to walk to *some* square a box can be pushed
from, and those moves precede every push.  Writing `D` for that walk, `Σ pushDist
+ D` is a lower bound.

`D` is also exactly what makes the sum safe.  A `push` is only legal with the
robot already on a pushing square, so `D` is zero whenever a push is available:
the push takes one off `Σ pushDist` and cannot take anything off `D`, which is
already at the floor.  A `move` leaves `Σ pushDist` untouched and shifts `D` by at
most one, since the walk graph is symmetrised and distances from adjacent squares
differ by at most one.  Neither action can lower both terms at once, which is
what consistency needs.  `D` ranges over every box, not just the unsolved ones,
so that a push of an already-placed box cannot slip past the argument.

The same table detects dead ends.  If a box's product distance is infinite — the
square it stands on cannot be pushed towards its goal at all, whatever the robot
does — then no plan exists, since the relaxation only ever admits more behaviour
than the real problem.  That is the classic Sokoban deadlock, a box shoved into a
corner or flat against a wall, and reporting it lets the search drop the whole
subtree.
-/
import Planner.ExampleHeuristics.Sokoban.Simple
import Planner.Distance

namespace Planner.ExampleHeuristics.Sokoban

open Planner.Pddl

/-- One box with an unmet `at` goal. -/
structure BoxInfo where
  goalFact : Fact
  /-- The target square, as a location index. -/
  goalLoc : Nat
  /-- The facts `at(box, l)`, with `l`. -/
  atFacts : Array (Fact × Nat)
  /-- Distance to "this box is home", indexed by `boxSquare * n + robotSquare`. -/
  jointDist : Array Nat
  deriving Inhabited

structure Data where
  /-- Number of squares. -/
  n : Nat
  /-- The value `jointDist` uses for "no route at all". -/
  unreachable : Nat
  /-- Distances in the push graph, for the additive push bound. -/
  dist : Distances
  /-- Distances in the robot's walk graph, for the approach bound. -/
  walk : Distances
  /-- For each square, the squares a robot can push a box standing there from. -/
  pushPos : Array (Array Nat)
  /-- For every box, its `at` facts with the square index. -/
  boxAt : Array (Array (Fact × Nat))
  /-- The facts `at-robot(l)` with `l`. -/
  robotAt : Array (Fact × Nat)
  boxes : Array BoxInfo
  deriving Inhabited

/--
The squares `adjacent(x, y, _)` lets the robot walk to from the square `u`.

Written as a `filterMap` over the static facts rather than as a loop with a
mutable table: a proof has to say what an entry *is*, and an imperative fold
hides that behind its own induction.  It computes exactly what the loop did.
-/
def robotStepsAt (t : Task) (index : Std.HashMap Name Nat) (u : Nat) : Array Nat :=
  (t.staticWith "adjacent").filterMap fun a =>
    match a.args with
    | [x, y, _] => if index[x]? == some u then index[y]? else none
    | _ => none

/-- Robot steps: `adjacent(x, y, d)` lets the robot walk from `x` to `y`. -/
def robotSteps (t : Task) (index : Std.HashMap Name Nat) (n : Nat) :
    Array (Array Nat) :=
  (Array.range n).map (robotStepsAt t index)

/--
The `(robotSquare, destination)` pairs one `adjacent(r, b, d)` fact contributes
for a box standing on `b`: the robot stands behind the box, and the square the
box goes to is the one `adjacent(b, f, d)` names in the same direction.
-/
def pushStepsOf (t : Task) (index : Std.HashMap Name Nat)
    (r b d : Name) : Array (Nat × Nat) :=
  (t.staticWith "adjacent").filterMap fun c =>
    match c.args with
    | [x, f, e] =>
        if x == b && e == d then
          match index[r]?, index[f]? with
          | some ur, some uf => some (ur, uf)
          | _, _ => none
        else none
    | _ => none

/-- The pairs for one box square, over every `adjacent` fact that lines up. -/
def pushStepsAt (t : Task) (index : Std.HashMap Name Nat) (ub : Nat) :
    Array (Nat × Nat) :=
  (t.staticWith "adjacent").flatMap fun a =>
    match a.args with
    | [r, b, d] => if index[b]? == some ub then pushStepsOf t index r b d else #[]
    | _ => #[]

/-- Pushes: `pushes[b]` lists `(robotSquare, destination)` for a box standing on `b`. -/
def pushSteps (t : Task) (index : Std.HashMap Name Nat) (n : Nat) :
    Array (Array (Nat × Nat)) :=
  (Array.range n).map (pushStepsAt t index)

/--
Backward breadth-first search over the *(box, robot)* product for one target
square.  `dist[b * n + r]` is the number of actions still needed, when the box is
on `b` and the robot on `r`, to get that box home.
-/
def jointDistancesRaw (n : Nat) (walk : Array (Array Nat))
    (pushes : Array (Array (Nat × Nat))) (goal : Nat) : Array Nat := Id.run do
  let size := n * n
  let unreachable := size
  -- Predecessors of every product node.
  let mut pred : Array (Array Nat) := Array.replicate size #[]
  for b in [0:n] do
    for r in [0:n] do
      if r == b then
        continue
      -- Walking from `r` to `r'` leads from (b, r) to (b, r').
      for r' in walk.getD r #[] do
        if r' != b then
          let node := b * n + r'
          pred := pred.setIfInBounds node ((pred.getD node #[]).push (b * n + r))
      -- Pushing from `r` sends the box from `b` to `f` and the robot onto `b`.
      for (pr, f) in pushes.getD b #[] do
        if pr == r && f != b then
          let node := f * n + b
          pred := pred.setIfInBounds node ((pred.getD node #[]).push (b * n + r))
  let mut dist : Array Nat := Array.replicate size unreachable
  let mut queue : Array Nat := #[]
  for r in [0:n] do
    if r != goal then
      dist := dist.setIfInBounds (goal * n + r) 0
      queue := queue.push (goal * n + r)
  let mut head := 0
  for _ in [0:size] do
    if head ≥ queue.size then
      break
    let u := queue.getD head 0
    head := head + 1
    let du := dist.getD u unreachable
    for v in pred.getD u #[] do
      if dist.getD v unreachable == unreachable then
        dist := dist.setIfInBounds v (du + 1)
        queue := queue.push v
  return dist

/--
The successors of a product node.

A `move` takes `(b, r)` to `(b, r')` for any robot step `r → r'` onto a square
the box does not stand on; a `push` takes `(b, r)` to `(f, b)` when the robot on
`r` can push the box from `b` to `f`.  Every action of any plan — pushes of other
boxes included, which shift the robot one square — is exactly one of these, which
is why the distance in this graph is a lower bound on the whole plan.
-/
def jointSucc (n : Nat) (walk : Array (Array Nat))
    (pushes : Array (Array (Nat × Nat))) (b r : Nat) : Array Nat :=
  if r == b then #[]
  else
    ((walk.getD r #[]).filterMap fun r' => if r' == b then none else some (b * n + r'))
      ++ ((pushes.getD b #[]).filterMap fun x =>
            if x.1 == r && x.2 != b then some (x.2 * n + b) else none)

/--
The decidable check one `jointDist` table has to pass: zero wherever the box is
already home, never above the cap, and falling by at most one along every edge
of the product graph — plus the cap surviving a step back, which is what lets an
entry at the cap be read as a genuine deadlock.

Checked against the table the search actually built rather than derived from a
proof that breadth-first search is optimal, exactly as `Distances.check` is.
-/
def jointCheck (n : Nat) (walk : Array (Array Nat))
    (pushes : Array (Array (Nat × Nat))) (goal : Nat) (dist : Array Nat) : Bool :=
  decide (dist.size = n * n) &&
  ((List.range n).all fun r => (r == goal) || dist.getD (goal * n + r) (n * n) == 0) &&
  (dist.all fun x => decide (x ≤ n * n)) &&
  ((List.range n).all fun b => (List.range n).all fun r =>
      (jointSucc n walk pushes b r).all fun v =>
        decide (dist.getD (b * n + r) (n * n) ≤ 1 + dist.getD v (n * n) ∧
          (dist.getD v (n * n) < n * n → dist.getD (b * n + r) (n * n) < n * n)))

/-- A universally safe product-distance lower bound. -/
def jointZero (n : Nat) : Array Nat := Array.replicate (n * n) 0

/--
Build and validate the product-distance table.  If validation ever detects a
regression in the optimized backward BFS, use zero lower bounds instead.
-/
def jointDistances (n : Nat) (walk : Array (Array Nat))
    (pushes : Array (Array (Nat × Nat))) (goal : Nat) : Array Nat :=
  let dist := jointDistancesRaw n walk pushes goal
  if jointCheck n walk pushes goal dist then dist else jointZero n

/--
The robot's walk graph, symmetrised.  `adjacent` is given in both directions in
these instances, but the consistency argument rests on distances changing by at
most one per robot step, so the symmetry is imposed rather than assumed.
-/
def walkAdjAt (walk : Array (Array Nat)) (k : Nat) : Array Nat :=
  walk.zipIdx.flatMap fun x =>
    x.1.flatMap fun v =>
      (if x.2 == k then #[v] else #[]) ++ (if v == k then #[x.2] else #[])

def walkGraph (locations : Array Name) (index : Std.HashMap Name Nat)
    (walk : Array (Array Nat)) : Graph :=
  { nodes := locations, index,
    adj := (Array.range locations.size).map (walkAdjAt walk) }

/-- The push graph, used for the additive bound. -/
def pushGraph (locations : Array Name) (index : Std.HashMap Name Nat)
    (pushes : Array (Array (Nat × Nat))) : Graph :=
  { nodes := locations, index, adj := pushes.map fun ps => ps.map (·.2) }

def compile (t : Task) : Data := Id.run do
  let locations := t.objectsOfTypes ["location"]
  let n := locations.size
  -- The same index `Graph` builds, so the graph lemmas read this table too.
  let index := Graph.nodeIndex locations
  let walk := robotSteps t index n
  let pushes := pushSteps t index n
  let graph := pushGraph locations index pushes
  let robotAt := (t.factsWith "at-robot").filterMap fun (f, a) =>
    match a.args with
    | [l] => (index[l]?).map ((f, ·))
    | _ => none
  let atFacts := t.factsWith "at"
  -- The box table, a filter of the goal atoms.  Written this way rather than as a
  -- loop with an accumulator so that a proof can say what an entry is: an
  -- imperative fold hides that behind its own induction, and every reader lemma
  -- would have to unfold it first.
  let boxes : Array BoxInfo := t.goalAtoms.zipIdx.filterMap fun (a, i) =>
    if a.pred == "at" then
      match a.args with
      | [b, g] =>
          (index[g]?).map fun gl =>
            { goalFact := t.goal.getD i 0
              goalLoc := gl
              atFacts := atFacts.filterMap fun (f, c) =>
                match c.args with
                | [x, l] => if x == b then (index[l]?).map ((f, ·)) else none
                | _ => none
              jointDist := jointDistances n walk pushes gl }
      | _ => none
    else none
  let boxAt := (t.objectsOfTypes ["box"]).map fun b =>
    atFacts.filterMap fun (f, c) =>
      match c.args with
      | [x, l] => if x == b then (index[l]?).map ((f, ·)) else none
      | _ => none
  return { n, unreachable := n * n, dist := Distances.of graph,
           walk := Distances.of (walkGraph locations index walk),
           pushPos := pushes.map fun ps => ps.map (·.1), boxAt, robotAt, boxes }

/-- Boxes whose `at` goal is unmet. -/
@[inline] def unmetBoxes (d : Data) (s : State) : Array BoxInfo :=
  d.boxes.filter fun b => !s.test b.goalFact

@[inline] def robotLoc (d : Data) (s : State) : Option Nat :=
  (d.robotAt.find? fun x => s.test x.1).map (·.2)

@[inline] def boxLoc (s : State) (b : BoxInfo) : Option Nat :=
  (b.atFacts.find? fun x => s.test x.1).map (·.2)

/--
The exact one-box distance in the *(box square, robot square)* product.

A box whose position the state does not record reads as unreachable, not as
zero.  Relevance pruning may drop an `at` fact it judges cannot lead to the goal,
and then a push onto that square leaves the box with no position at all — from
which no push of that box is ever applicable again, so its goal is out of reach.
Reading that as zero would let the value fall by the whole table in one step.
-/
@[inline] def jointOf (d : Data) (s : State) (b : BoxInfo) : Nat :=
  match robotLoc d s with
  | none => 0
  | some r =>
      match boxLoc s b with
      | some l => b.jointDist.getD (l * d.n + r) d.unreachable
      | none => d.unreachable

/-- Pushes summed over the boxes, in the push graph.  A box with no recorded
position reads as the cap, for the reason `jointOf` gives. -/
@[inline] def pushesRaw (d : Data) (s : State) : Nat :=
  (unmetBoxes d s).foldl (init := 0) fun acc b =>
    acc + (match boxLoc s b with
           | some l => d.dist.get l b.goalLoc
           | none => d.dist.bound)

/-- The largest one-box product distance. -/
@[inline] def hardestRaw (d : Data) (s : State) : Nat :=
  (unmetBoxes d s).foldl (init := 0) fun acc b => max acc (jointOf d s b)

/-- A box that cannot be pushed home whatever the robot does: the classic deadlock. -/
@[inline] def deadlocked (d : Data) (s : State) : Bool :=
  (unmetBoxes d s).any fun b =>
    match boxLoc s b, robotLoc d s with
    | some _, some _ => decide (jointOf d s b ≥ d.unreachable)
    | _, _ => false

/-- The robot's walk to the nearest square any box can be pushed from. -/
@[inline] def approachRaw (d : Data) (s : State) : Nat :=
  match robotLoc d s with
  | none => 0
  | some r =>
      d.boxAt.foldl (init := d.walk.bound) fun best facts =>
        match facts.find? fun x => s.test x.1 with
        | some (_, l) =>
            (d.pushPos.getD l #[]).foldl (init := best) fun acc p => min acc (d.walk.get r p)
        | none => best

/-- No box is reachable at all: nothing can ever be pushed. -/
@[inline] def approachStuck (d : Data) (s : State) : Bool :=
  match robotLoc d s with
  | none => false
  | some _ => decide (approachRaw d s ≥ d.walk.bound)

@[inline] def approachCost (d : Data) (s : State) : Nat :=
  match robotLoc d s with
  | none => 0
  | some _ => approachRaw d s

/-- Every box home, so nothing is owed. -/
@[inline] def solved (d : Data) (s : State) : Bool := (unmetBoxes d s).isEmpty

/-- Pushes, the walk to the first push, and the one-box bound, all zero once solved. -/
@[inline] def pushes (d : Data) (s : State) : Nat := if solved d s then 0 else pushesRaw d s
@[inline] def approach (d : Data) (s : State) : Nat := if solved d s then 0 else approachCost d s
@[inline] def hardest (d : Data) (s : State) : Nat := if solved d s then 0 else hardestRaw d s

/-- A state with no plan: a deadlocked box, or no box the robot can reach. -/
def isDead (d : Data) (s : State) : Bool :=
  !solved d s && (deadlocked d s || approachStuck d s)

/--
The larger of the additive push bound plus the approaching walk, and the exact
one-box product distance.

Written as named pieces rather than a loop over mutable counters: the pieces are
what the correctness argument talks about, so they are what the proof needs to
name.  It computes exactly what the loop version did.
-/
def baseValue (d : Data) (s : State) : Nat :=
  max (pushes d s + approach d s) (hardest d s)

/--
The same value, with the dead-end test in front of it.

A box whose product distance is infinite cannot be pushed home whatever the
robot does, so the state has no plan at all and the search may drop it.  This
branch is **not** deployed: it needs the dead-state closure argument, and on the
shipped tasks it changes nothing, because an unreachable entry already makes
`hardest` large enough to prune.
-/
def value (d : Data) (s : State) : Nat :=
  if isDead d s then deadEnd else baseValue d s

/--
The deployed improved heuristic: the larger of the additive push bound plus the
approaching walk, and the exact one-box product distance.
-/
def improved (t : Task) : Heuristic :=
  let dd := compile t
  { name := "sokoban-improved", eval := baseValue dd }

end Planner.ExampleHeuristics.Sokoban
