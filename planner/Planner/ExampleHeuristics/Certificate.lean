/-
Runtime certificates for domain-dependent heuristics.

The executable keeps certificates as named Boolean checks.  The names make a
failed proof boundary visible to the user, while the Boolean conjunction is the
value read by the Lean soundness theorem.  This module belongs to `Planner`, so
checking a task never links Mathlib or the proof library into the executable.
-/
import Planner.Pddl.Validation

namespace Planner

open Pddl

/-- One finite condition required by a heuristic proof. -/
structure CertificateCheck where
  name : String
  passed : Bool
  deriving Repr, Inhabited

/-- The complete finite proof boundary for one parsed task. -/
abbrev Certificate := List CertificateCheck

namespace Certificate

/-- A certificate with no conditions. -/
def accept : Certificate := []

/-- A single named condition. -/
def one (name : String) (passed : Bool) : Certificate :=
  [{ name, passed }]

/-- Every condition succeeded. -/
def passes (c : Certificate) : Bool :=
  c.all (·.passed)

/-- The names of the conditions that failed. -/
def failures (c : Certificate) : List String :=
  (c.filter fun check => !check.passed).map (·.name)

theorem passes_accept : passes accept = true := rfl

/-! ### Common finite checks over parsed objects -/

/-- At least one task object has the exact declared type. -/
def hasObject (d : Domain) (p : Problem) (ty : Name) : Bool :=
  (allObjects d p).any fun o => o.type == ty

/-- A named task object has the exact declared type. -/
def objectNamedWithType (d : Domain) (p : Problem) (name ty : Name) : Bool :=
  (allObjects d p).any fun o => o.name == name && o.type == ty

/-- No object inhabiting `ty` through subtyping has a different declared type. -/
def exactType (d : Domain) (p : Problem) (ty : Name) : Bool :=
  (allObjects d p).all fun o => !(d.isSubtype o.type ty) || o.type == ty

/-- No task object inhabits both types through subtyping. -/
def disjointTypes (d : Domain) (p : Problem) (left right : Name) : Bool :=
  (allObjects d p).all fun o =>
    !(d.isSubtype o.type left) || !(d.isSubtype o.type right)

/-- Argument pairs of one two-argument predicate in the initial state. -/
def initPairs (p : Problem) (pred : Name) : List (Name × Name) :=
  p.init.filterMap fun a =>
    match a.pred == pred, a.args with
    | true, [x, y] => some (x, y)
    | _, _ => none

/-- Arguments of one one-argument predicate in the initial state. -/
def initOnes (p : Problem) (pred : Name) : List Name :=
  p.init.filterMap fun a =>
    match a.pred == pred, a.args with
    | true, [x] => some x
    | _, _ => none

/-- Argument triples of one three-argument predicate in the initial state. -/
def initTriples (p : Problem) (pred : Name) : List (Name × Name × Name) :=
  p.init.filterMap fun a =>
    match a.pred == pred, a.args with
    | true, [x, y, z] => some (x, y, z)
    | _, _ => none

end Certificate

end Planner
