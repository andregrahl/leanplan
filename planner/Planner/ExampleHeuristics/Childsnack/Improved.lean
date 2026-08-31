/-
Childsnack, improved heuristic.

Four schemas families that never share an action — `serve*`, `put_on_tray`,
`make*`, `move_tray` — are bounded separately and added.

Write `nₐ` and `n` for the unserved goal children who are allergic and in total,
`Aɡ`, `Aᵣ` for the gluten-free and ordinary sandwiches already on a tray, and
`Kɡ`, `Kᵣ` for those still in the kitchen.

  * `serve`: exactly `n`, one per child.
  * `put_on_tray`: the sandwiches on trays have to cover the children, and an
    allergic child can only take a gluten-free one, so the shortfall is
    `max(nₐ - Aɡ, n - Aɡ - Aᵣ)` — matching gluten-free sandwiches to allergic
    children first and letting everyone else absorb the rest.
  * `make*`: the same shortfall measured against the kitchen instead of the
    trays, `max(X - Kɡ, put - Kɡ - Kᵣ)` where `X = nₐ - Aɡ`.
  * `move_tray`: a child is served from a tray standing at their place carrying a
    sandwich, so every place whose waiting children outnumber the sandwiches on
    the trays already standing there needs a tray brought to it — and if any
    sandwich still has to be loaded, a tray has to be standing in the kitchen to
    load it onto, which is one more move when none is.

The delicate case is `serve`, which drops `n` by one *and* takes a sandwich off a
tray.  Both terms move together and the shortfalls stay put, so the total falls
by exactly the one `serve` action — which is what consistency needs.
-/
import Planner.ExampleHeuristics.Base

namespace Planner.ExampleHeuristics.Childsnack

open Planner.Pddl

/-- What the heuristic needs to know about one sandwich. -/
structure SandwichInfo where
  /-- The fact `at_kitchen_sandwich(s)`. -/
  kitchenFact : Option Fact
  /-- The fact `no_gluten_sandwich(s)`. -/
  glutenFreeFact : Option Fact
  /-- The facts `ontray(s, t)`. -/
  onTrayFacts : Array Fact
  deriving Inhabited

/-- What the heuristic needs to know about one goal child. -/
structure ChildInfo where
  /-- The fact `served(c)`. -/
  goalFact : Fact
  /-- Whether the child is allergic; `allergic_gluten` is static. -/
  allergic : Bool
  /-- The place the child waits at; `waiting` is static. -/
  place : Option Nat
  deriving Inhabited

structure Data where
  children : Array ChildInfo
  sandwiches : Array SandwichInfo
  /-- For each tray, the facts `at(tray, p)` with the place index. -/
  trayAt : Array (Array (Fact × Nat))
  /-- For each tray, the `ontray(_, tray)` facts: what it is carrying. -/
  trayLoad : Array (Array Fact)
  /-- The place index of the kitchen, where sandwiches are loaded. -/
  kitchen : Option Nat
  /-- How many places there are. -/
  placeCount : Nat
  deriving Inhabited

/--
The entry for one goal atom: a child, whether they are allergic, and where they
wait.  `none` when the atom is not a `served` goal.

Split out of `compile` as a `filterMap` rather than written as a loop over a
mutable array: `Proofs/Lifted/ChildsnackCompile.lean` pairs this list with the
lifted `Cfg`'s child list entry for entry, and a `filterMap` is what that pairing
needs.  It computes exactly what the loop did.
-/
def childEntry (t : Task) (allergic waiting : Array GroundAtom)
    (placeIndex : Name → Option Nat) (x : GroundAtom × Nat) : Option ChildInfo :=
  match x.1.pred == "served", x.1.args with
  | true, [c] =>
      some
        { goalFact := t.goal.getD x.2 0
          allergic := allergic.any fun b => b.args == [c]
          place := (waiting.find? fun b =>
            match b.args with
            | [y, _] => y == c
            | _ => false).bind fun b =>
              match b.args with
              | [_, q] => placeIndex q
              | _ => none }
  | _, _ => none

def compile (t : Task) : Data :=
  let places := t.objectsOfTypes ["place"]
  let placeIndex : Name → Option Nat := fun p => places.findIdx? (· == p)
  let trays := t.objectsOfTypes ["tray"]
  let sandwichNames := t.objectsOfTypes ["sandwich"]
  let onTrayFacts := t.factsWith "ontray"
  -- The `ontray` fact for one sandwich on one tray, if the task numbered it.
  let onFact : Name → Name → Option Fact := fun sw tr =>
    (onTrayFacts.find? fun (_, a) => a.args == [sw, tr]).map (·.1)
  { children := t.goalAtoms.zipIdx.filterMap
      (childEntry t (t.staticWith "allergic_gluten") (t.staticWith "waiting") placeIndex)
    sandwiches := sandwichNames.map fun sw =>
      { kitchenFact :=
          ((t.factsWith "at_kitchen_sandwich").find? fun (_, a) => a.args == [sw]).map (·.1)
        glutenFreeFact :=
          ((t.factsWith "no_gluten_sandwich").find? fun (_, a) => a.args == [sw]).map (·.1)
        onTrayFacts := trays.filterMap (onFact sw) : SandwichInfo }
    trayAt := trays.map fun tr =>
      (t.factsWith "at").filterMap fun (f, a) =>
        match a.args with
        | [x, p] => if x == tr then (placeIndex p).map ((f, ·)) else none
        | _ => none
    trayLoad := trays.map fun tr => sandwichNames.filterMap (onFact · tr)
    kitchen := placeIndex "kitchen"
    placeCount := places.size }

/-- Children whose `served` goal is unmet. -/
@[inline] def unservedChildren (d : Data) (s : State) : Array ChildInfo :=
  d.children.filter fun c => !s.test c.goalFact

@[inline] def total (d : Data) (s : State) : Nat := (unservedChildren d s).size

@[inline] def allergicLeft (d : Data) (s : State) : Nat :=
  ((unservedChildren d s).filter fun c => c.allergic).size

@[inline] def waitingAt (d : Data) (s : State) (p : Nat) : Nat :=
  ((unservedChildren d s).filter fun c => c.place == some p).size

@[inline] def onTray (s : State) (sw : SandwichInfo) : Bool :=
  sw.onTrayFacts.any fun f => s.test f

@[inline] def isFree (s : State) (sw : SandwichInfo) : Bool :=
  match sw.glutenFreeFact with
  | some f => s.test f
  | none => false

@[inline] def inKitchen (s : State) (sw : SandwichInfo) : Bool :=
  !onTray s sw && (match sw.kitchenFact with
                   | some f => s.test f
                   | none => false)

@[inline] def trayAny (d : Data) (s : State) : Nat :=
  (d.sandwiches.filter fun sw => onTray s sw).size
@[inline] def trayFree (d : Data) (s : State) : Nat :=
  (d.sandwiches.filter fun sw => onTray s sw && isFree s sw).size
@[inline] def kitchenAny (d : Data) (s : State) : Nat :=
  (d.sandwiches.filter fun sw => inKitchen s sw).size
@[inline] def kitchenFree (d : Data) (s : State) : Nat :=
  (d.sandwiches.filter fun sw => inKitchen s sw && isFree s sw).size

/-- Sandwiches still to be loaded, matching gluten-free ones to allergic children first. -/
@[inline] def shortfall (d : Data) (s : State) : Nat :=
  max (allergicLeft d s - trayFree d s) (total d s - trayAny d s)

/-- The same shortfall measured against the kitchen instead of the trays. -/
@[inline] def toMake (d : Data) (s : State) : Nat :=
  max ((allergicLeft d s - trayFree d s) - kitchenFree d s) (shortfall d s - kitchenAny d s)

/-- Where a tray is standing. -/
@[inline] def trayPlace (d : Data) (s : State) (facts : Array (Fact × Nat)) : Option Nat :=
  (facts.find? fun x => s.test x.1).map (·.2)

/-- How many sandwiches sit on the trays standing at `p`. -/
@[inline] def loadedAt (d : Data) (s : State) (p : Nat) : Nat :=
  d.trayAt.zipIdx.foldl (init := 0) fun acc x =>
    if trayPlace d s x.1 == some p then acc + countHolding (d.trayLoad.getD x.2 #[]) s else acc

@[inline] def trayInKitchen (d : Data) (s : State) : Bool :=
  d.trayAt.any fun facts => trayPlace d s facts == d.kitchen

/-- Places whose waiting children outnumber the sandwiches standing there. -/
@[inline] def moveTargets (d : Data) (s : State) : List Nat :=
  (List.range d.placeCount).filter fun p =>
    d.kitchen != some p && decide (loadedAt d s p < waitingAt d s p)

/-- Tray moves: one per underserved place, and one to bring a tray to the kitchen. -/
@[inline] def moves (d : Data) (s : State) : Nat :=
  (moveTargets d s).length +
    (if decide (0 < shortfall d s) && !trayInKitchen d s then 1 else 0)

/--
Four families that never share an action, bounded separately and added.

Written as named pieces rather than a loop over mutable counters: the pieces are
what the correctness argument talks about, so they are what the proof needs to
name.  It computes exactly what the loop version did.
-/
def value (d : Data) (s : State) : Nat :=
  if total d s == 0 then 0
  else total d s + shortfall d s + toMake d s + moves d s

def improved (t : Task) : Heuristic :=
  let d := compile t
  { name := "childsnack-improved", eval := value d }

end Planner.ExampleHeuristics.Childsnack
