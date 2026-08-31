/-
The parser-level Childsnack schemas shared by the runtime certificate and proof.
-/
import Planner.GeneratedDomains.Childsnack

namespace Planner.Lifted.Childsnack

open Planner.Pddl

def swP : TypedName := { name := "?s", type := "sandwich" }
def brP : TypedName := { name := "?b", type := "bread-portion" }
def coP : TypedName := { name := "?c", type := "content-portion" }
def trP (n : Name) : TypedName := { name := n, type := "tray" }
def chP : TypedName := { name := "?c", type := "child" }
def plP (n : Name) : TypedName := { name := n, type := "place" }

abbrev breadV (a : Name) : Atom := { pred := "at_kitchen_bread", args := [.var a] }
abbrev contentV (a : Name) : Atom := { pred := "at_kitchen_content", args := [.var a] }
abbrev ngBreadV (a : Name) : Atom := { pred := "no_gluten_bread", args := [.var a] }
abbrev ngContentV (a : Name) : Atom := { pred := "no_gluten_content", args := [.var a] }
abbrev notexistV (a : Name) : Atom := { pred := "notexist", args := [.var a] }
abbrev kitchenSwV (a : Name) : Atom := { pred := "at_kitchen_sandwich", args := [.var a] }
abbrev glutenFreeV (a : Name) : Atom := { pred := "no_gluten_sandwich", args := [.var a] }
abbrev ontrayV (a b : Name) : Atom := { pred := "ontray", args := [.var a, .var b] }
abbrev atKitchenV (a : Name) : Atom := { pred := "at", args := [.var a, .const "kitchen"] }
abbrev atV (a b : Name) : Atom := { pred := "at", args := [.var a, .var b] }
abbrev allergicV (a : Name) : Atom := { pred := "allergic_gluten", args := [.var a] }
abbrev notAllergicV (a : Name) : Atom := { pred := "not_allergic_gluten", args := [.var a] }
abbrev waitingV (a b : Name) : Atom := { pred := "waiting", args := [.var a, .var b] }
abbrev servedV (a : Name) : Atom := { pred := "served", args := [.var a] }

abbrev makeNGA : Action := Planner.GeneratedDomains.Childsnack.action0
abbrev makeA : Action := Planner.GeneratedDomains.Childsnack.action1
abbrev putA : Action := Planner.GeneratedDomains.Childsnack.action2
abbrev serveNGA : Action := Planner.GeneratedDomains.Childsnack.action3
abbrev serveA : Action := Planner.GeneratedDomains.Childsnack.action4
abbrev moveA : Action := Planner.GeneratedDomains.Childsnack.action5

/-- The task has the exact Childsnack action schemas produced by the parser. -/
abbrev ChildsnackDomain (d : Domain) : Prop :=
  d.actions = [makeNGA, makeA, putA, serveNGA, serveA, moveA]

end Planner.Lifted.Childsnack
