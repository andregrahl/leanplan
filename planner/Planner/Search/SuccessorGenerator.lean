/-
An exact, task-compiled candidate generator for grounded operators.

Every operator is assigned one trigger: its first in-range precondition.  An
operator without such a trigger is kept in the fallback bucket.  At a state we
visit only the buckets of true facts, append the fallback bucket, and finally
run the ordinary full applicability check.  The latter makes the generator
exact while the trigger index avoids testing most operators.
-/
import Planner.Task

namespace Planner

/-- A single-trigger inverted index over a task's grounded operators. -/
structure SuccessorGenerator where
  numFacts : Nat
  fallback : Array Nat
  byFact : Array (Array Nat)
  deriving Inhabited

/-- The indexed precondition of operator `i`, when it has an in-range one. -/
def operatorTrigger? (t : Task) (i : Nat) : Option Fact :=
  match t.ops[i]? with
  | none => none
  | some op =>
      match op.pre[0]? with
      | some f => if f < t.numFacts then some f else none
      | none => none

/-- Whether an operator's compiled trigger permits it at this state. -/
@[inline] def triggerSatisfied (t : Task) (i : Nat) (s : State) : Bool :=
  match operatorTrigger? t i with
  | some f => s.test f
  | none => true

/-- Compile the trigger buckets once per task. -/
def compileSuccessorGenerator (t : Task) : SuccessorGenerator :=
  let ids := Array.range t.ops.size
  { numFacts := t.numFacts
    fallback := ids.filter fun i => (operatorTrigger? t i).isNone
    byFact := (Array.range t.numFacts).map fun f =>
      ids.filter fun i => operatorTrigger? t i == some f }

namespace SuccessorGenerator

/-- Visit fact buckets from `i` onwards. -/
def collect (g : SuccessorGenerator) (s : State) :
    Nat → Nat → Array Nat → Array Nat
  | 0, _, ids => ids
  | fuel + 1, i, ids =>
      if i < g.numFacts then
        let ids := if s.test i then ids ++ g.byFact.getD i #[] else ids
        collect g s fuel (i + 1) ids
      else ids

/-- Candidate IDs before the final exact applicability check. -/
def candidates (g : SuccessorGenerator) (s : State) : Array Nat :=
  collect g s g.numFacts 0 g.fallback

/-- Exactly the applicable operator IDs, drawn from the compiled candidates. -/
def applicableIds (g : SuccessorGenerator) (t : Task) (s : State) : Array Nat :=
  (g.candidates s).filter fun i => (t.ops.getD i default).applicable s

end SuccessorGenerator

end Planner
