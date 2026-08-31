/-
A*.

Mirrors pyperplan's `search/a_star.py`, with the data structures of
`Planner/State.lean`, `OpenList.lean` and `Node.lean`.

The loop is a *tail-recursive structural recursion on a `Nat` fuel*.  That shape
is deliberate: Lean compiles it to a real loop, so the search neither grows the
stack nor pays for `WellFounded.fix`, while `Proofs/AStarCorrect.lean` still gets
a total function to reason about.  `Main.lean` passes a fuel that no search
fitting in memory can exhaust, and the completeness theorem says exactly what
running out would mean.

The goal test happens on *pop*, not on generation: that is what makes the first
goal node expanded an optimal one.  `best` maps a state to the cheapest `g` at
which it has been pushed, and doubles as the closed list; an entry whose `g`
exceeds the recorded one is stale and is discarded.

A successor whose heuristic value reaches `deadEnd` is dropped rather than
pushed.  A heuristic returns that value only on states it has shown to have no
goal-reaching plan, so nothing optimal is lost; the optimality theorem states the
side condition explicitly, as `deadEnd` exceeding the cost of an optimal plan.
-/
import Std.Data.HashMap
import Planner.Search.Node
import Planner.Search.OpenList
import Planner.ExampleHeuristics.Base

namespace Planner

/-- What the search found. -/
inductive Outcome where
  /-- Operator indices of an optimal plan, and its cost. -/
  | solved (plan : Array Nat) (cost : Nat)
  /-- The open list ran dry: the task has no plan. -/
  | unsolvable
  /-- The fuel ran out before either of the above. -/
  | outOfFuel
  deriving Inhabited

namespace Outcome

/-- The plan of a solved outcome, for stating the soundness theorem. -/
def planOf : Outcome → Array Nat
  | .solved plan _ => plan
  | _ => #[]

/-- The cost of a solved outcome, for stating the soundness theorem. -/
def costOf : Outcome → Nat
  | .solved _ cost => cost
  | _ => 0

end Outcome

/-- Everything the search carries from one iteration to the next. -/
structure Search where
  openList : OpenList
  nodes : Array Node
  /-- Cheapest `g` at which each state has been reached so far. -/
  best : Std.HashMap State Nat
  expanded : Nat
  generated : Nat
  evaluated : Nat
  /-- Successors dropped because the heuristic proved them dead ends. -/
  pruned : Nat
  deriving Inhabited

/-- The search outcome together with its statistics. -/
structure Result where
  outcome : Outcome
  expanded : Nat
  generated : Nat
  evaluated : Nat
  pruned : Nat
  deriving Inhabited

/-- Record a successor: prune it if the heuristic proves it a dead end, else push it. -/
@[inline] def record (heur : Heuristic) (id i : Nat) (succ : State) (g : Nat)
    (s : Search) : Search :=
  let h := heur.eval succ
  if h ≥ deadEnd then
    { s with
      generated := s.generated + 1
      evaluated := s.evaluated + 1
      pruned := s.pruned + 1
      best := s.best.insert succ g }
  else
    { s with
      generated := s.generated + 1
      evaluated := s.evaluated + 1
      best := s.best.insert succ g
      nodes := s.nodes.push { state := succ, g, parent := id, op := some i }
      openList := s.openList.push { f := g + h, h, node := s.nodes.size } }

/--
Try one operator on the node being expanded.

Written as an explicit step rather than a loop body so that
`Proofs/Search/AStar.lean` can induct on the operator index; the fuel-driven
`expandFrom` below is tail-recursive, so this costs nothing at run time.
-/
@[inline] def expandOne (t : Task) (heur : Heuristic) (id : Nat) (node : Node)
    (i : Nat) (s : Search) : Search :=
  let op := t.ops.getD i default
  if op.applicable node.state then
    let succ := op.apply node.state
    let g := node.g + op.cost
    match s.best.get? succ with
    | some previous =>
        if g < previous then record heur id i succ g s
        else { s with generated := s.generated + 1 }
    | none => record heur id i succ g s
  else s

/-- Apply every operator from index `i` onwards. -/
def expandFrom (t : Task) (heur : Heuristic) (id : Nat) (node : Node) :
    Nat → Nat → Search → Search
  | 0, _, s => s
  | fuel + 1, i, s =>
      if i < t.ops.size then
        expandFrom t heur id node fuel (i + 1) (expandOne t heur id node i s)
      else s

/-- Generate the successors of `node`, pushing every one that improves on `best`. -/
def expand (t : Task) (heur : Heuristic) (id : Nat) (node : Node)
    (s : Search) : Search :=
  expandFrom t heur id node t.ops.size 0 { s with expanded := s.expanded + 1 }

/-- One iteration per unit of fuel: pop, discard-if-stale, goal-test, expand. -/
def loop (t : Task) (heur : Heuristic) : Nat → Search → Result
  | 0, s => { outcome := .outOfFuel, expanded := s.expanded,
              generated := s.generated, evaluated := s.evaluated, pruned := s.pruned }
  | fuel + 1, s =>
      match s.openList.pop? with
      | none => { outcome := .unsolvable, expanded := s.expanded,
                  generated := s.generated, evaluated := s.evaluated, pruned := s.pruned }
      | some (entry, rest) =>
          match s.nodes[entry.node]? with
          | none =>
              -- Unreachable: every open-list entry names a node that exists.
              -- Handling it here rather than indexing blindly keeps the
              -- soundness proof free of an open-list invariant.
              loop t heur fuel { s with openList := rest }
          | some node =>
          if s.best.getD node.state node.g < node.g then
            loop t heur fuel { s with openList := rest }
          else if t.isGoal node.state then
            { outcome := .solved (extractPlan s.nodes entry.node) node.g
              expanded := s.expanded, generated := s.generated, evaluated := s.evaluated
              pruned := s.pruned }
          else
            loop t heur fuel (expand t heur entry.node node { s with openList := rest })

/-- Run A* on `t` with `heur`, giving up after `fuel` iterations. -/
def astar (t : Task) (heur : Heuristic) (fuel : Nat) : Result :=
  let root := Node.root t
  let h := heur.eval root.state
  let start : Search :=
    { openList := OpenList.empty
      nodes := #[root]
      best := (∅ : Std.HashMap State Nat).insert root.state 0
      expanded := 0, generated := 0, evaluated := 1, pruned := 0 }
  if h ≥ deadEnd then
    loop t heur fuel { start with pruned := 1 }
  else
    loop t heur fuel { start with openList := start.openList.push { f := h, h, node := 0 } }

/-- Emit an opt-in progress line without changing the proved `loop` function. -/
@[inline] def traceExpansionCheckpoint (interval : Nat) (s : Search) : Search :=
  if s.expanded > 0 && s.expanded % interval == 0 then
    match dbgTrace s!"Expansion checkpoint: {s.expanded} state(s)." fun _ => () with
    | () => s
  else s

/-- `loop` with periodic expansion checkpoints for externally timed benchmarks. -/
def loopWithCheckpoints (t : Task) (heur : Heuristic) (interval : Nat) :
    Nat → Search → Result
  | 0, s => { outcome := .outOfFuel, expanded := s.expanded,
              generated := s.generated, evaluated := s.evaluated, pruned := s.pruned }
  | fuel + 1, s =>
      match s.openList.pop? with
      | none => { outcome := .unsolvable, expanded := s.expanded,
                  generated := s.generated, evaluated := s.evaluated, pruned := s.pruned }
      | some (entry, rest) =>
          match s.nodes[entry.node]? with
          | none =>
              loopWithCheckpoints t heur interval fuel { s with openList := rest }
          | some node =>
              if s.best.getD node.state node.g < node.g then
                loopWithCheckpoints t heur interval fuel { s with openList := rest }
              else if t.isGoal node.state then
                { outcome := .solved (extractPlan s.nodes entry.node) node.g
                  expanded := s.expanded, generated := s.generated,
                  evaluated := s.evaluated, pruned := s.pruned }
              else
                let next := expand t heur entry.node node { s with openList := rest }
                loopWithCheckpoints t heur interval fuel
                  (traceExpansionCheckpoint interval next)

/-- Run A* with progress output every `interval` expansions. -/
def astarWithCheckpoints (t : Task) (heur : Heuristic) (fuel interval : Nat) : Result :=
  let root := Node.root t
  let h := heur.eval root.state
  let start : Search :=
    { openList := OpenList.empty
      nodes := #[root]
      best := (∅ : Std.HashMap State Nat).insert root.state 0
      expanded := 0, generated := 0, evaluated := 1, pruned := 0 }
  if h ≥ deadEnd then
    loopWithCheckpoints t heur interval fuel { start with pruned := 1 }
  else
    loopWithCheckpoints t heur interval fuel
      { start with openList := start.openList.push { f := h, h, node := 0 } }

/--
The fuel `Main.lean` passes.  Each iteration pops one open-list entry, so a search
that exhausts this has performed 2^62 pops; since every push allocates a node,
such a run cannot fit in any real machine's memory.
-/
def defaultFuel : Nat := 1 <<< 62

end Planner
