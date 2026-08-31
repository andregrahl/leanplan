/-
Search nodes and plan extraction.

Mirrors pyperplan's `search/searchspace.py`.  Nodes live in one flat array and
name their predecessor by index, so a node is four machine words and a plan is a
walk up the parent chain.

`planTo` builds the plan front to back — the recursive call comes first and the
operator is appended after it — which is what makes the induction in
`Proofs/Search/AStar.lean` follow the chain in the direction the plan runs.
`fuel` bounds the walk; the search always passes the node count, and every node's
parent has a strictly smaller index, so that is always enough.
-/
import Planner.Task

namespace Planner

/-- A node of the search space. -/
structure Node where
  state : State
  /-- Cost of the cheapest path found so far from the initial state. -/
  g : Nat
  /-- Index of the predecessor node; the root points at itself. -/
  parent : Nat
  /-- Index of the operator that produced this node; `none` at the root. -/
  op : Option Nat
  deriving Inhabited

/-- The root node of a task's search space. -/
def Node.root (t : Task) : Node :=
  { state := t.init, g := 0, parent := 0, op := none }

/-- The operators leading from the root to node `id`, in order. -/
def planTo (nodes : Array Node) : Nat → Nat → Array Nat
  | 0, _ => #[]
  | fuel + 1, id =>
      let node := nodes.getD id default
      match node.op with
      | none => #[]
      | some op => (planTo nodes fuel node.parent).push op

/-- The plan reaching node `id`. -/
def extractPlan (nodes : Array Node) (id : Nat) : Array Nat :=
  planTo nodes (nodes.size + 1) id

end Planner
