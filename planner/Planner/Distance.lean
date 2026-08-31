/-
Shortest-path tables over a task's static structure.

Several domains hide a graph in their static predicates: `road` in transport,
`link` in spanner, `adjacent` in sokoban, the four move relations in floortile,
`can_traverse`/`visible` in rovers.  A heuristic that knows how far a thing still
has to travel is far better informed than one that only counts goals, and the
graph never changes during search, so the whole distance table is computed once
when the heuristic is compiled.

Unreachable pairs are capped at the node count rather than left infinite.  That
is still a lower bound on the true (infinite) distance, so admissibility is
unaffected, and the cap preserves the triangle inequality `d l g ≤ 1 + d l' g`
across every edge `l → l'`, which is what consistency needs.
-/
import Std.Data.HashMap
import Planner.Task

namespace Planner

open Planner.Pddl

/-- A directed graph on a set of named objects. -/
structure Graph where
  /-- The nodes, in a fixed order; a node is referred to by its index. -/
  nodes : Array Name
  index : Std.HashMap Name Nat
  /-- `adj[i]` lists the successors of node `i`. -/
  adj : Array (Array Nat)
  deriving Inhabited

namespace Graph

/-- The number of nodes; also the value used for "no path". -/
@[inline] def size (g : Graph) : Nat := g.nodes.size

/-- The index of a named node, if it is one. -/
@[inline] def find? (g : Graph) (n : Name) : Option Nat := g.index[n]?

/--
Build a graph whose nodes are `nodes` and whose edges are the two-argument
static atoms of `pred`.  Edges naming an object outside `nodes` are dropped.
-/
def nodeIndex (nodes : Array Name) : Std.HashMap Name Nat :=
  nodes.zipIdx.foldl (init := {}) fun m x => m.insert x.1 x.2

/-- One atom's contribution to the adjacency lists. -/
def addEdge (index : Std.HashMap Name Nat) (adj : Array (Array Nat))
    (a : GroundAtom) : Array (Array Nat) :=
  match a.args with
  | [x, y] =>
      match index[x]?, index[y]? with
      | some i, some j => adj.setIfInBounds i ((adj.getD i #[]).push j)
      | _, _ => adj
  | _ => adj

/-- The graph on `nodes` whose edges are the two-argument atoms of `edges`. -/
def ofEdges (nodes : Array Name) (edges : Array GroundAtom) : Graph :=
  let index := nodeIndex nodes
  { nodes, index,
    adj := edges.foldl (init := Array.replicate nodes.size #[]) (addEdge index) }

def ofStatic (t : Task) (pred : Name) (nodes : Array Name) : Graph :=
  ofEdges nodes (t.staticAtoms.filter (·.pred == pred))

/-- Like `ofStatic`, but the edge is read from argument positions `i` and `j`. -/
def ofStaticAt (t : Task) (pred : Name) (nodes : Array Name) (i j : Nat) :
    Graph := Id.run do
  let mut index : Std.HashMap Name Nat := {}
  for (n, k) in nodes.zipIdx do
    index := index.insert n k
  let mut adj : Array (Array Nat) := Array.replicate nodes.size #[]
  for a in t.staticAtoms do
    if a.pred == pred then
      let args := a.args.toArray
      match index[args.getD i ""]?, index[args.getD j ""]? with
      | some u, some v => adj := adj.setIfInBounds u ((adj.getD u #[]).push v)
      | _, _ => pure ()
  return { nodes, index, adj }

/-- Breadth-first distances from `src`; `size` means unreachable. -/
def bfs (g : Graph) (src : Nat) : Array Nat := Id.run do
  let n := g.size
  let mut dist : Array Nat := Array.replicate n n
  if src ≥ n then return dist
  dist := dist.setIfInBounds src 0
  let mut queue : Array Nat := #[src]
  let mut head := 0
  -- Each node enters the queue at most once, so `n` rounds suffice.
  for _ in [0:n] do
    if head ≥ queue.size then break
    let u := queue.getD head 0
    head := head + 1
    let du := dist.getD u n
    for v in g.adj.getD u #[] do
      if dist.getD v n == n && v != src then
        dist := dist.setIfInBounds v (du + 1)
        queue := queue.push v
  return dist

/-- All-pairs shortest distances, `dist[i][j]` from `i` to `j`. -/
def allPairs (g : Graph) : Array (Array Nat) :=
  (Array.range g.size).map g.bfs

end Graph

/-- A compiled distance table: `d i j` is a lower bound on the steps from `i` to `j`. -/
structure Distances where
  bound : Nat
  table : Array (Array Nat)
  deriving Inhabited

namespace Distances

@[inline] def get (d : Distances) (i j : Nat) : Nat :=
  (d.table.getD i #[]).getD j d.bound

/-- The finite conditions downstream proofs need from a distance table. -/
def check (g : Graph) (d : Distances) : Bool :=
  (List.range g.size).all (fun i => d.get i i == 0) &&
  ((List.range g.size).all fun i =>
    (g.adj.getD i #[]).all fun i' =>
      (List.range g.size).all fun j => d.get i j ≤ 1 + d.get i' j) &&
  (d.table.toList.all fun row => row.toList.all fun x => decide (x ≤ d.bound)) &&
  decide (d.table.size ≤ g.size) && decide (g.size ≤ d.bound) &&
  ((List.range g.size).all fun i =>
    (g.adj.getD i #[]).all fun i' =>
      (List.range g.size).all fun j =>
        decide (d.get i' j < d.bound → d.get i j < d.bound)) &&
  d.table.toList.all fun row => decide (row.size ≤ g.size)

/-- The raw breadth-first-search table. -/
def raw (g : Graph) : Distances := { bound := g.size, table := g.allPairs }

/-- A universally safe lower-bound table, used only if the BFS result fails its check. -/
def zero (g : Graph) : Distances :=
  { bound := g.size
    table := Array.replicate g.size (Array.replicate g.size 0) }

/--
Build the BFS table and validate exactly the properties used by the proofs.  A
failed validation falls back to zero lower bounds, so construction is sound even
if the optimized BFS implementation is changed incorrectly in the future.
-/
def of (g : Graph) : Distances :=
  let d := raw g
  if check g d then d else zero g

/-- The smallest distance from any of `sources` to `j`. -/
@[inline] def minFrom (d : Distances) (sources : Array Nat) (j : Nat) : Nat :=
  sources.foldl (init := d.bound) fun acc i => min acc (d.get i j)

end Distances

end Planner
