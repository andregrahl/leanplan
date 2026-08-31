/-
Measuring whether a domain's transition shape is satisfiable at all.

Every closed heuristic proof rests on a statement of the form "each grounded
operator moves the state in one of these ways".  Four times now such a statement
has turned out to hold of *no* transition of a real task, which makes the theorem
that rests on it vacuous.  Each time it was found only by attempting the proof,
which costs hours.

A shape is a list of named cases, each a decidable claim about a pair of
consecutive states.  A transition no case covers is what makes the shape
unsatisfiable, and finding one is a breadth-first walk.  That is what this does,
and it is what a generated heuristic should be run through before any proof
effort is spent on it.
-/
import Std.Data.HashSet
import Planner.Task

namespace Planner

/-- One case of a transition shape, as a decidable claim. -/
structure ShapeCase where
  name : String
  holds : State → State → Bool

/-- A domain's transition shape. -/
structure ShapeSpec where
  cases : Array ShapeCase
  /--
  A guard the value uses to cut a subtree, such as a dead-end test.

  Such a guard has to be closed under successors, or the value it returns is not
  consistent.  That is a claim about every transition, so the walk checks it.
  -/
  guard : Option (State → Bool) := none

/-- What the walk found. -/
structure ShapeReport where
  states : Nat
  transitions : Nat
  /-- How often each case was the one that covered a transition. -/
  covered : Array (String × Nat)
  /-- Transitions no case covered, by operator name. -/
  uncovered : Array String
  /-- Transitions that left the guard, which no closed guard has. -/
  leaks : Array String

/--
Walk the reachable states and test every transition against the shape.

The first case that holds is the one credited, so the order of the cases is the
order the proof would case on.  A transition none of them covers is reported by
the operator that made it.
-/
def auditShapes (task : Task) (spec : ShapeSpec) (limit : Nat) : ShapeReport := Id.run do
  let mut seen : Std.HashSet State := Std.HashSet.emptyWithCapacity 1024
  seen := seen.insert task.init
  let mut queue : Array State := #[task.init]
  let mut head := 0
  let mut states := 0
  let mut transitions := 0
  let mut counts : Array Nat := Array.replicate spec.cases.size 0
  let mut uncovered : Array String := #[]
  let mut leaks : Array String := #[]
  while head < queue.size && states < limit do
    let s := queue[head]!
    head := head + 1
    states := states + 1
    for op in task.ops do
      if op.applicable s then
        let s' := op.apply s
        transitions := transitions + 1
        match spec.cases.findIdx? (fun c => c.holds s s') with
        | some i => counts := counts.modify i (· + 1)
        | none => if uncovered.size < 64 then uncovered := uncovered.push op.name
        match spec.guard with
        | some g => if g s && !g s' then
            if leaks.size < 64 then leaks := leaks.push op.name
        | none => pure ()
        if !seen.contains s' then
          seen := seen.insert s'
          queue := queue.push s'
  let covered := spec.cases.zipIdx.map fun (c, i) => (c.name, counts.getD i 0)
  return { states, transitions, covered, uncovered, leaks }

end Planner
