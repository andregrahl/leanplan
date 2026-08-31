/-
The runtime boundary between the logical grounded task and the representation
searched by A*.

The first compiler is intentionally an identity representation: it gives every
operator its stable logical index and otherwise preserves the task exactly.
Later preprocessing and representation passes refine this structure while the
logical `Task` remains the specification used by certificates and proofs.
-/
import Planner.Search.SuccessorGenerator

namespace Planner

/-- The add/delete masks that update one state word. -/
structure EffectWord where
  index : Nat
  add : UInt64
  del : UInt64
  deriving Inhabited

namespace EffectWord

@[inline] def apply (effect : EffectWord) (words : Array UInt64) : Array UInt64 :=
  let word := words.getD effect.index 0
  words.setIfInBounds effect.index ((word &&& ~~~effect.del) ||| effect.add)

end EffectWord

@[inline] def compileEffectWord? (addMask delMask : State) (index : Nat) : Option EffectWord :=
  let add := addMask.words.getD index 0
  let del := delMask.words.getD index 0
  if add == 0 && del == 0 then none else some { index, add, del }

/-- Group all effects by state word. -/
def compileEffectWords (numFacts : Nat) (add del : Array Fact) : Array EffectWord :=
  let addMask := State.ofFacts numFacts add
  let delMask := State.ofFacts numFacts del
  (Array.range (State.wordsFor numFacts)).filterMap
    (compileEffectWord? addMask delMask)

/-- A runtime operator together with its index in the logical task. -/
structure CompiledOp where
  sourceId : Nat
  logical : Op
  remainingPre : Array Fact
  effects : Array EffectWord
  deriving Inhabited

namespace CompiledOp

@[inline] def applicable (op : CompiledOp) (s : State) : Bool :=
  s.holdsAll op.remainingPre

@[inline] def apply (op : CompiledOp) (s : State) : State :=
  { words := op.effects.foldl (init := s.words) fun words effect => effect.apply words }

end CompiledOp

/--
The task boundary consumed by the eventual single compiled A* engine.

`source` remains available as the proof specification.  The other fields are
duplicated deliberately: they are the fields later compiler passes will replace
with pruned operators and packed runtime data.
-/
structure CompiledTask where
  source : Task
  ops : Array CompiledOp
  init : State
  goal : Array Fact
  successors : SuccessorGenerator
  deriving Inhabited

/-- Attach stable source IDs without changing the task searched. -/
def compileTaskIdentity (t : Task) : CompiledTask :=
  { source := t
    ops := t.ops.zipIdx.map fun (op, sourceId) =>
      let remainingPre :=
        match operatorTrigger? t sourceId with
        | some trigger => op.pre.filter (· != trigger)
        | none => op.pre
      { sourceId
        logical := op
        remainingPre
        effects := compileEffectWords t.numFacts op.add op.del }
    init := t.init
    goal := t.goal
    successors := compileSuccessorGenerator t }

namespace CompiledTask

/-- Whether the compiled task's current state satisfies its compiled goal. -/
@[inline] def isGoal (t : CompiledTask) (s : State) : Bool :=
  s.holdsAll t.goal

/-- Resolve an operator ID back to the operator in the logical task. -/
def sourceOp? (t : CompiledTask) (i : Nat) : Option Op :=
  t.source.ops[i]?

/-- Applicable source-operator IDs from the task-compiled successor index. -/
def applicableIds (t : CompiledTask) (s : State) : Array Nat :=
  t.successors.applicableIds t.source s

end CompiledTask

end Planner
