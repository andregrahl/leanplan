/-
The grounded STRIPS task the search runs on.

Mirrors pyperplan's `task.py`.  Facts are indices, operators are three index
arrays, and a state is a bit set (`Planner/State.lean`).  `Task` also carries the
lifted information a domain-dependent heuristic needs — the objects with their
types, the atoms that hold in every state, and the name of every fact — so that a
heuristic can be compiled once per task and then run on bare bit sets.
-/
import Planner.State
import Planner.Pddl.Validation

namespace Planner

open Planner.Pddl

/-- A grounded operator. -/
structure Op where
  /-- Lisp-style name, e.g. `(unstack b1 b2)`; this is what a plan file prints. -/
  name : String
  pre : Array Fact
  add : Array Fact
  del : Array Fact
  cost : Nat
  deriving Inhabited

/-- A grounded planning task. -/
structure Task where
  numFacts : Nat
  /-- `factNames[f]` is the atom that fact `f` stands for. -/
  factNames : Array GroundAtom
  ops : Array Op
  init : State
  goal : Array Fact
  /-- Atoms that hold in every reachable state and therefore carry no fact index. -/
  staticAtoms : Array GroundAtom
  /-- The goal as atoms, for heuristics that reason about goal structure. -/
  goalAtoms : Array GroundAtom
  /-- Every object of the task with its declared type. -/
  objects : Array TypedName
  /-- The domain name, used to select the domain-dependent heuristics. -/
  domainName : Name
  deriving Inhabited

namespace Op

/-- Whether `op` is applicable in `s`: all its preconditions hold. -/
@[inline] def applicable (op : Op) (s : State) : Bool :=
  s.holdsAll op.pre

/-- The successor of `s` under `op`.  Deletes are applied before adds. -/
@[inline] def apply (op : Op) (s : State) : State :=
  let s := op.del.foldl (init := s) fun s f => s.erase f
  op.add.foldl (init := s) fun s f => s.insert f

end Op

namespace Task

/-- Whether `s` satisfies the goal. -/
@[inline] def isGoal (t : Task) (s : State) : Bool :=
  s.holdsAll t.goal

/-- Look up the index of an atom, or `none` when it is static or unreachable. -/
def factOf? (t : Task) (a : GroundAtom) : Option Fact :=
  t.factNames.findIdx? (· == a)

/-- Whether an atom holds in `s`, taking static atoms into account. -/
def atomHolds (t : Task) (s : State) (a : GroundAtom) : Bool :=
  match t.factOf? a with
  | some f => s.test f
  | none => t.staticAtoms.contains a

instance : ToString Task where
  toString t :=
    s!"<Task {t.domainName}, facts: {t.numFacts}, ops: {t.ops.size}, " ++
    s!"goal: {t.goal.size}, static: {t.staticAtoms.size}>"

end Task

end Planner
