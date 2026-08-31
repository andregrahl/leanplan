/-
The parser-level Miconic schemas shared by the runtime certificate and proof.
-/
import Planner.GeneratedDomains.Miconic

namespace Planner.Lifted.Miconic

open Planner.Pddl

def floorP : TypedName := { name := "?f", type := "floor" }
def passP : TypedName := { name := "?p", type := "passenger" }
def f1P : TypedName := { name := "?f1", type := "floor" }
def f2P : TypedName := { name := "?f2", type := "floor" }

abbrev liftAtV (v : Name) : Atom := { pred := "lift-at", args := [.var v] }
abbrev originV (a b : Name) : Atom := { pred := "origin", args := [.var a, .var b] }
abbrev boardedV (v : Name) : Atom := { pred := "boarded", args := [.var v] }
abbrev servedV (v : Name) : Atom := { pred := "served", args := [.var v] }
abbrev destinV (a b : Name) : Atom := { pred := "destin", args := [.var a, .var b] }
abbrev aboveV (a b : Name) : Atom := { pred := "above", args := [.var a, .var b] }

abbrev boardA : Action := Planner.GeneratedDomains.Miconic.action0
abbrev departA : Action := Planner.GeneratedDomains.Miconic.action1
abbrev upA : Action := Planner.GeneratedDomains.Miconic.action2
abbrev downA : Action := Planner.GeneratedDomains.Miconic.action3

/-- The task has the exact Miconic action schemas produced by the parser. -/
abbrev MiconicDomain (d : Domain) : Prop :=
  d.actions = [boardA, departA, upA, downA]

end Planner.Lifted.Miconic
