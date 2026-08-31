/-
The parser-level Ferry schemas shared by the runtime certificate and proof.
-/
import Planner.GeneratedDomains.Ferry

namespace Planner.Lifted.Ferry

open Planner.Pddl

def locP (n : Name) : TypedName := { name := n, type := "location" }
def carP : TypedName := { name := "?car", type := "car" }

abbrev atV (a b : Name) : Atom := { pred := "at", args := [.var a, .var b] }
abbrev atFerryV (a : Name) : Atom := { pred := "at-ferry", args := [.var a] }
abbrev notAtFerryV (a : Name) : Atom := { pred := "not-at-ferry", args := [.var a] }
abbrev onV (a : Name) : Atom := { pred := "on", args := [.var a] }
abbrev emptyV : Atom := { pred := "empty-ferry", args := [] }

abbrev sailA : Action := Planner.GeneratedDomains.Ferry.action0
abbrev boardA : Action := Planner.GeneratedDomains.Ferry.action1
abbrev debarkA : Action := Planner.GeneratedDomains.Ferry.action2

/-- The task has the exact Ferry action schemas produced by the parser. -/
abbrev FerryDomain (d : Domain) : Prop :=
  d.actions = [sailA, boardA, debarkA]

end Planner.Lifted.Ferry
