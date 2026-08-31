/-
The lifted model: PDDL read directly, without grounding.

A state is an assignment of truth values to ground atoms; an action is one
well-typed instance of a schema — a schema of the domain together with one object
per parameter, each object of the parameter's declared type.  Applying an action
deletes and then adds, so an atom both deleted and added ends up true, which is
the STRIPS convention the grounder and `Op.apply` both follow.

This is the model the heuristics are *supposed* to be admissible for and the model
a plan is checked against by `validate`.  What the planner actually searches is
the grounded task of `Planner/Task.lean`, whose facts are numbers.
`Proofs/GroundingCorrect.lean` connects the two.

Instantiation is written to mirror `compileAtom` followed by
`instantiateSlots`, so that the bridge is a rewriting argument rather
than a re-derivation: a variable is looked up by position among the parameters,
and anything else — a constant, or a variable the validator has already ruled out
— stands for itself.
-/
import Proofs.Task
import Planner.Grounding

namespace Planner.Pddl

open Planner

/-- A state of the lifted model: which ground atoms hold. -/
abbrev AtomState := GroundAtom → Bool

/-- Instantiate one schema atom under an assignment of objects to parameters. -/
def instAtom (params : List TypedName) (args : List Name) (a : Atom) : GroundAtom :=
  { pred := a.pred
    args := a.args.map fun
      | .var v =>
          match params.findIdx? (·.name == v) with
          | some i => args.getD i ""
          | none => v
      | .const c => c }

/-- `o` is one of the task's objects, of a type at or below `ty`. -/
def WellTyped (d : Domain) (objects : List TypedName) (ty : Name) (o : Name) : Prop :=
  ∃ decl ∈ objects, decl.name = o ∧ d.isSubtype decl.type ty = true

/-- One well-typed instance of one of the domain's schemas. -/
structure Instance (d : Domain) (objects : List TypedName) where
  schema : Action
  /-- The schema is one of the domain's. -/
  mem : schema ∈ d.actions
  /-- One object per parameter. -/
  args : List Name
  /-- Each object has the parameter's declared type. -/
  typed : List.Forall₂ (fun (p : TypedName) (o : Name) => WellTyped d objects p.type o)
    schema.params args

namespace Instance

variable {d : Domain} {objects : List TypedName}

/-- The instance's preconditions, as ground atoms. -/
def pre (i : Instance d objects) : List GroundAtom :=
  i.schema.pre.map (instAtom i.schema.params i.args)

/-- The atoms the instance makes true. -/
def add (i : Instance d objects) : List GroundAtom :=
  i.schema.add.map (instAtom i.schema.params i.args)

/-- The atoms the instance makes false. -/
def del (i : Instance d objects) : List GroundAtom :=
  i.schema.del.map (instAtom i.schema.params i.args)

/-- What the instance costs. -/
def cost (i : Instance d objects) : Nat := i.schema.cost

end Instance

/-- Whether every precondition of the instance holds. -/
def applicableL {d : Domain} {objects : List TypedName}
    (s : AtomState) (i : Instance d objects) : Prop :=
  ∀ a ∈ i.pre, s a = true

/-- The successor state: delete, then add. -/
def applyL {d : Domain} {objects : List TypedName}
    (s : AtomState) (i : Instance d objects) : AtomState := fun a =>
  if i.add.contains a then true
  else if i.del.contains a then false
  else s a

/-- The goal holds when every goal atom does. -/
def isGoalL (p : Problem) (s : AtomState) : Prop := ∀ a ∈ p.goal, s a = true

/-- The state `:init` describes: exactly the atoms it lists. -/
def initL (p : Problem) : AtomState := fun a => p.init.contains a

/-- **The lifted model.**  PDDL as a transition system, with no grounding in sight. -/
def pddlModel (d : Domain) (p : Problem) :
    PlanningModel AtomState (Instance d (allObjects d p)) where
  transition s i s' := applicableL s i ∧ s' = applyL s i
  actionCost i := i.cost
  isGoal s := isGoalL p s

@[simp] theorem pddlModel_transition (d : Domain) (p : Problem)
    (s : AtomState) (i : Instance d (allObjects d p)) (s' : AtomState) :
    (pddlModel d p).transition s i s' ↔ (applicableL s i ∧ s' = applyL s i) := Iff.rfl

@[simp] theorem pddlModel_actionCost (d : Domain) (p : Problem)
    (i : Instance d (allObjects d p)) : (pddlModel d p).actionCost i = i.cost := rfl

@[simp] theorem pddlModel_isGoal (d : Domain) (p : Problem) (s : AtomState) :
    (pddlModel d p).isGoal s ↔ isGoalL p s := Iff.rfl

/-! ### Instantiation is what the grounder computes

`compileAtom` resolves each argument to a slot once per schema, and
`instantiateSlots` fills the slots in.  Doing both is `instAtom`, which
is what makes the bridge a rewrite rather than an argument.
-/

theorem instantiate_compile (params : List TypedName) (args : Array Name) (a : Atom) :
    instantiateSlots args (compileAtom params a)
      = instAtom params args.toList a := by
  unfold Planner.instantiateSlots Planner.compileAtom instAtom
  simp only [GroundAtom.mk.injEq, true_and]
  simp only [Array.toList_map, List.map_map]
  refine List.map_congr_left fun x _ => ?_
  cases x with
  | var v =>
      cases hf : params.findIdx? (·.name == v) with
      | none => simp [hf]
      | some i => simp [hf, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  | const c => simp

end Planner.Pddl
