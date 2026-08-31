/-
The exact Spanner schemas produced by the PDDL parser.

This runtime module is shared by the executable certificate and the proof
library, so the two layers compare against one schema definition.
-/
import Planner.GeneratedDomains.Spanner

namespace Planner.Lifted.Spanner

open Planner.Pddl

def atAtom (x l : Name) : GroundAtom := { pred := "at", args := [x, l] }
def carrying (m s : Name) : GroundAtom := { pred := "carrying", args := [m, s] }
def usable (s : Name) : GroundAtom := { pred := "usable", args := [s] }
def link (l₁ l₂ : Name) : GroundAtom := { pred := "link", args := [l₁, l₂] }
def tightened (n : Name) : GroundAtom := { pred := "tightened", args := [n] }
def loose (n : Name) : GroundAtom := { pred := "loose", args := [n] }

def locP (n : Name) : TypedName := { name := n, type := "location" }
def manP : TypedName := { name := "?m", type := "man" }
def spannerP : TypedName := { name := "?s", type := "spanner" }
def nutP : TypedName := { name := "?n", type := "nut" }

abbrev atV (x l : Name) : Atom := { pred := "at", args := [.var x, .var l] }
abbrev carryingV (m s : Name) : Atom := { pred := "carrying", args := [.var m, .var s] }
abbrev usableV (s : Name) : Atom := { pred := "usable", args := [.var s] }
abbrev linkV (l₁ l₂ : Name) : Atom := { pred := "link", args := [.var l₁, .var l₂] }
abbrev tightenedV (n : Name) : Atom := { pred := "tightened", args := [.var n] }
abbrev looseV (n : Name) : Atom := { pred := "loose", args := [.var n] }

abbrev walkA : Action := Planner.GeneratedDomains.Spanner.action0
abbrev pickupA : Action := Planner.GeneratedDomains.Spanner.action1
abbrev tightenA : Action := Planner.GeneratedDomains.Spanner.action2

abbrev SpannerDomain (d : Domain) : Prop :=
  d.actions = [walkA, pickupA, tightenA]

end Planner.Lifted.Spanner
