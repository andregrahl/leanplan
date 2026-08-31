/-
Grounding a validated domain and problem into a `Task`.

Mirrors pyperplan's `grounding.py` step for step, so that the two planners search
the same state space:

  1. objects = problem objects + domain constants, indexed by type;
  2. a predicate is *static* when no schema adds or deletes it;
  3. each schema is instantiated over well-typed objects, with static
     preconditions checked against `:init` during instantiation (pyperplan filters
     the same assignments, only afterwards);
  4. a true static precondition is dropped from the operator, a false one discards
     the operator;
  5. `del := del \ add` and `add := add \ pre`, as in `_create_operator`;
  6. backward relevance analysis prunes effects and operators that cannot
     contribute to the goal;
  7. the surviving atoms are numbered and the state bit sets are built.

Step 3 differs from pyperplan only in *when* the static test happens: pruning a
partial assignment as soon as all of a static atom's variables are bound is a
large constant-factor win and yields exactly the same operator set.
-/
import Std.Data.HashMap
import Std.Data.HashSet
import Planner.Task

namespace Planner

open Planner.Pddl

/-- An argument position of a schema atom: a parameter slot or a fixed object. -/
inductive Slot where
  | param (index : Nat)
  | obj (name : Name)
  deriving Inhabited

/-- A schema atom with its parameter references resolved to positions. -/
structure SlotAtom where
  pred : Name
  slots : Array Slot
  /-- One past the largest parameter index mentioned; `0` for a ground atom. -/
  level : Nat
  deriving Inhabited

/-- Fill a compiled schema atom's slots from an assignment.  Not private: the
grounding correctness proof names it. -/
@[inline] def instantiateSlots (assign : Array Name) (a : SlotAtom) : GroundAtom :=
  { pred := a.pred
    args := a.slots.toList.map fun
      | .param i => assign.getD i ""
      | .obj n => n }

/-- Resolve a schema atom's arguments to parameter positions, once per schema. -/
def compileAtom (params : List TypedName) (atom : Atom) : SlotAtom :=
  let slots := atom.args.toArray.map fun
    | .var v => match params.findIdx? (·.name == v) with
      | some i => Slot.param i
      | none => Slot.obj v          -- unreachable: `Validation` binds every variable
    | .const c => Slot.obj c
  let level := slots.foldl (init := 0) fun acc s =>
    match s with
    | .param i => max acc (i + 1)
    | .obj _ => acc
  { pred := atom.pred, slots, level }

/-- Objects of each declared type, including objects of its subtypes. -/
def typeObjects (d : Domain) (objects : List TypedName) :
    Std.HashMap Name (Array Name) := Id.run do
  let mut m : Std.HashMap Name (Array Name) := {}
  for ty in d.typeNames do
    let members := objects.filter (d.isSubtype ·.type ty) |>.map (·.name)
    m := m.insert ty members.toArray
  return m

/-- Predicates that no schema adds or deletes; their truth never changes. -/
def staticPredicates (d : Domain) : List Name :=
  let changed := d.actions.flatMap fun a => (a.add ++ a.del).map (·.pred)
  d.predicates.map (·.name) |>.filter (!changed.contains ·)

/-- An operator before facts are numbered. -/
structure AtomOp where
  name : String
  pre : Array GroundAtom
  add : Array GroundAtom
  del : Array GroundAtom
  cost : Nat
  deriving Inhabited

/-- The printed name of a grounded operator. -/
def opName (schema : Name) (args : Array Name) : String :=
  if args.isEmpty then "(" ++ schema ++ ")"
  else "(" ++ schema ++ " " ++ " ".intercalate args.toList ++ ")"

/-- Remove duplicate atoms, keeping the first occurrence. -/
def dedup (xs : Array GroundAtom) : Array GroundAtom :=
  xs.foldl (init := #[]) fun acc a => if acc.contains a then acc else acc.push a

/--
Instantiate one schema.  `assign` grows one object at a time; whenever a static
precondition becomes fully bound it is checked against `:init` and a failing
partial assignment is abandoned immediately.
-/
def groundSchema (d : Domain) (types : Std.HashMap Name (Array Name))
    (statics : List Name) (init : Std.HashSet GroundAtom) (a : Action) : Array AtomOp :=
  let params := a.params
  let staticPre := a.pre.filter (statics.contains ·.pred) |>.map (compileAtom params)
  let dynamicPre := a.pre.filter (!statics.contains ·.pred) |>.map (compileAtom params)
  let addAtoms := a.add.map (compileAtom params)
  let delAtoms := a.del.map (compileAtom params)
  -- Static atoms grouped by the parameter count at which they become checkable.
  let byLevel : Array (List SlotAtom) :=
    (Array.range (params.length + 1)).map fun level => staticPre.filter (·.level == level)
  let checkAt : Nat → List SlotAtom := fun level => byLevel.getD level []
  let rec go : List TypedName → Array Name → Array AtomOp → Array AtomOp
    | [], assign, acc =>
        let pre := dedup ((dynamicPre.map (instantiateSlots assign)).toArray)
        let add := dedup ((addAtoms.map (instantiateSlots assign)).toArray)
        let del := dedup ((delAtoms.map (instantiateSlots assign)).toArray)
        -- STRIPS: a fact both added and deleted ends up true; a fact already in the
        -- precondition need not be re-added.
        let del := del.filter (!add.contains ·)
        let add := add.filter (!pre.contains ·)
        acc.push { name := opName a.name assign, pre, add, del, cost := a.cost }
    | p :: rest, assign, acc =>
        let candidates := types.getD p.type #[]
        candidates.foldl (init := acc) fun acc o =>
          let assign := assign.push o
          if (checkAt assign.size).all (fun s => init.contains (instantiateSlots assign s))
          then go rest assign acc
          else acc
  -- Ground atoms among the static preconditions (`level = 0`) are checked first.
  if (checkAt 0).all (fun s => init.contains (instantiateSlots #[] s)) then
    go params #[] #[]
  else #[]

/-- The operator writes some fact of `r`, and so cannot be dropped. -/
def AtomOp.touches (o : AtomOp) (r : Std.HashSet GroundAtom) : Bool :=
  o.add.any r.contains || o.del.any r.contains

/-- One round: every operator that writes into the set contributes what it reads. -/
def relevantStep (ops : Array AtomOp) (relevant : Std.HashSet GroundAtom) :
    Std.HashSet GroundAtom :=
  ops.foldl (init := relevant) fun acc op =>
    if op.touches relevant then op.pre.foldl (init := acc) fun acc f => acc.insert f
    else acc

/-- Rounds until nothing is added, or until the fuel runs out. -/
def relevantFix (ops : Array AtomOp) : Nat → Std.HashSet GroundAtom → Std.HashSet GroundAtom
  | 0, relevant => relevant
  | fuel + 1, relevant =>
      let next := relevantStep ops relevant
      if next.size == relevant.size then relevant else relevantFix ops fuel next

/--
The set the analysis settles on.  Each round that changes anything adds at least
one fact, and there are at most as many facts as operator preconditions plus
goals, which is where the fuel comes from.
-/
def relevantSet (ops : Array AtomOp) (goal : Array GroundAtom) : Std.HashSet GroundAtom :=
  relevantFix ops ((ops.foldl (init := goal.size) fun acc op => acc + op.pre.size) + 1)
    (Std.HashSet.ofArray goal)

/--
What the analysis needs of that set: it holds every goal atom, and every operator
that writes into it reads only from it.

The fixpoint is meant to reach such a set, and this is the decidable test that it
did.  Deriving closure from the fuel bound instead is arithmetic about
`Std.HashSet` sizes and is not done, so the planner checks rather than assumes:
pruning on an unverified set would put an unproved step under every plan returned.
The check is one linear pass and it has never failed on any task measured.
-/
def relevantOK (ops : Array AtomOp) (goal : Array GroundAtom)
    (r : Std.HashSet GroundAtom) : Bool :=
  goal.all r.contains && ops.all fun o => !o.touches r || o.pre.all r.contains

/--
Backward relevance analysis.  A fact is relevant if it is a goal or a precondition
of an operator that touches a relevant fact.  At the fixpoint every surviving
operator's preconditions are relevant, so facts outside the set are never read and
their add and delete effects can be discarded.

If the fixpoint does not verify, nothing is pruned.  `Proofs/Relevance.lean` proves
that pruning with a verified set keeps every plan, so the two branches together
make the analysis unconditionally safe.
-/
def relevanceAnalysis (ops : Array AtomOp) (goal : Array GroundAtom) :
    Array AtomOp :=
  let r := relevantSet ops goal
  if relevantOK ops goal r then
    ops.filterMap fun op =>
      let add := op.add.filter r.contains
      let del := op.del.filter r.contains
      if add.isEmpty && del.isEmpty then none
      else some { op with add, del }
  else ops

/--
Every atom the surviving operators mention, followed by the goal's.

Kept as a named function rather than folded into `ground`'s loop: the fact
numbering is what every downstream proof rests on, so it is what the proofs need
to name.
-/
def allAtoms (ops : Array AtomOp) (goalAtoms : Array GroundAtom) : Array GroundAtom :=
  (ops.foldl (init := #[]) fun acc op => acc ++ op.pre ++ op.add ++ op.del) ++ goalAtoms

/--
Number the atoms in order of first appearance, giving the index and the names.

The invariant that matters, and that `Proofs/Grounding.lean` proves, is that every
atom of the input receives an index below the number of names — which is what
makes every fact the planner ever touches lie in range.
-/
def factIndex (atoms : Array GroundAtom) : Std.HashMap GroundAtom Nat × Array GroundAtom :=
  atoms.foldl (init := ({}, #[])) fun st a =>
    if st.1.contains a then st else (st.1.insert a st.2.size, st.2.push a)

/--
Assemble the numbered task from the surviving operators and the goal.

Split out of `ground` so that `Proofs/Grounding.lean` can state well-formedness
about it: every fact it emits comes from `factIndex`, so every fact is in range.
-/
def assemble (ops : Array AtomOp) (goalAtoms : Array GroundAtom)
    (initAtoms : Array GroundAtom) (objects : Array TypedName) (domainName : Name) : Task :=
  let (index, names) := factIndex (allAtoms ops goalAtoms)
  let numFacts := names.size
  let idx : GroundAtom → Nat := fun a => index.getD a 0
  { numFacts
    factNames := names
    ops := ops.map fun op =>
      { name := op.name
        pre := op.pre.map idx
        add := op.add.map idx
        del := op.del.map idx
        cost := op.cost }
    init := State.ofFacts numFacts (initAtoms.filterMap fun a => index.get? a)
    -- Atoms true in `:init` that received no index are true in every reachable state.
    staticAtoms := initAtoms.filter (!index.contains ·)
    goal := goalAtoms.map idx
    goalAtoms
    objects
    domainName }

/-- The operators the grounder keeps, before facts are numbered. -/
def groundedOps (d : Domain) (p : Problem) (relevance : Bool) : Array AtomOp := Id.run do
  let objects := allObjects d p
  let types := typeObjects d objects
  let statics := staticPredicates d
  let initSet := Std.HashSet.ofList p.init
  let mut grounded : Array AtomOp := #[]
  for a in d.actions do
    grounded := grounded ++ groundSchema d types statics initSet a
  return if relevance then relevanceAnalysis grounded p.goal.toArray else grounded

/-- Ground a validated domain and problem. -/
def ground (d : Domain) (p : Problem) (relevance : Bool := true) : Task :=
  assemble (groundedOps d p relevance) p.goal.toArray p.init.toArray
    (allObjects d p).toArray d.name

end Planner
