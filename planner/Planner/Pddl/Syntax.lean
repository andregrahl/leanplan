/-
Abstract syntax for the fragment of PDDL that pyperplan supports.

Mirrors pyperplan's `pddl/pddl.py`.  The fragment is typed (or untyped) STRIPS:
positive conjunctive preconditions, conjunctive add and delete effects, a positive
conjunctive ground goal, and unit action costs.  Everything outside it is rejected
by `Planner/Pddl/Validation.lean` rather than silently mis-planned.

Lists rather than arrays are used throughout: a parsed domain has a handful of
predicates and schemas, it is consumed exactly once by grounding, and `List` is
what the proofs in `Proofs/` induct over.  The hot data structure is the *grounded*
task in `Planner/Task.lean`, which is array-based.
-/

namespace Planner.Pddl

/-- Names of types, predicates, schemas, variables and objects.  Always lowercase. -/
abbrev Name := String

/-- A name together with its declared type; `"object"` when the domain is untyped. -/
structure TypedName where
  name : Name
  type : Name
  deriving Repr, DecidableEq, Inhabited

/-- One entry of the `:types` hierarchy: `name` is a direct subtype of `parent`. -/
structure TypeDecl where
  name : Name
  parent : Name
  deriving Repr, DecidableEq, Inhabited

/-- A `:predicates` declaration. -/
structure Predicate where
  name : Name
  params : List TypedName
  deriving Repr, DecidableEq, Inhabited

/-- An argument position inside a schema: a `?variable` or a domain constant. -/
inductive Term where
  | var (name : Name)
  | const (name : Name)
  deriving Repr, DecidableEq, Inhabited

/-- A possibly-lifted atom, as it appears inside a schema. -/
structure Atom where
  pred : Name
  args : List Term
  deriving Repr, DecidableEq, Inhabited

/-- A fully instantiated atom, as it appears in `:init` and `:goal`. -/
structure GroundAtom where
  pred : Name
  args : List Name
  deriving Repr, DecidableEq, Inhabited, Hashable

instance : ToString GroundAtom where
  toString a := "(" ++ " ".intercalate (a.pred :: a.args) ++ ")"

/--
An action schema.  `cost` is always `1` in this fragment; it is kept explicit so
that the semantics and the A* optimality proof never assume unit costs.
-/
structure Action where
  name : Name
  params : List TypedName
  pre : List Atom
  add : List Atom
  del : List Atom
  cost : Nat := 1
  deriving Repr, DecidableEq, Inhabited

/-- A parsed `(define (domain ...))`. -/
structure Domain where
  name : Name
  requirements : List Name
  types : List TypeDecl
  constants : List TypedName
  predicates : List Predicate
  actions : List Action
  deriving Repr, DecidableEq, Inhabited

/-- A parsed `(define (problem ...))`. -/
structure Problem where
  name : Name
  domainName : Name
  objects : List TypedName
  init : List GroundAtom
  goal : List GroundAtom
  deriving Repr, DecidableEq, Inhabited

namespace Domain

def findType? (d : Domain) (n : Name) : Option TypeDecl :=
  d.types.find? (·.name == n)

def findPredicate? (d : Domain) (n : Name) : Option Predicate :=
  d.predicates.find? (·.name == n)

def findAction? (d : Domain) (n : Name) : Option Action :=
  d.actions.find? (·.name == n)

/-- Every type name the domain declares, plus the implicit root `object`. -/
def typeNames (d : Domain) : List Name :=
  "object" :: d.types.map (·.name)

/--
Whether `sub` is `super` or, following declared parents, below it.  `fuel` bounds
the walk up the hierarchy; `Validation` rejects cycles, so the declared type count
always suffices.
-/
def isSubtypeFuel (d : Domain) : Nat → Name → Name → Bool
  | 0, sub, super => sub == super
  | fuel + 1, sub, super =>
      if sub == super then true
      else if super == "object" then true
      else match d.findType? sub with
        | some decl => isSubtypeFuel d fuel decl.parent super
        | none => false

/-- Whether `sub` is a (non-strict) subtype of `super`. -/
def isSubtype (d : Domain) (sub super : Name) : Bool :=
  isSubtypeFuel d (d.types.length + 1) sub super

end Domain

end Planner.Pddl
