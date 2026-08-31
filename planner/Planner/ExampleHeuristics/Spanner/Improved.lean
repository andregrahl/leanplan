/-
Spanner, improved heuristic.

Three disjoint action families, plus a dead-end test.

*Tightening.*  Each nut whose `tightened` goal is unmet needs its own
`tighten_nut`.

*Collecting.*  Every `tighten_nut` consumes a spanner: it deletes `usable` of the
spanner it uses, and that spanner must be carried.  The only way to gain a
carried spanner is `pickup_spanner`, so at least `L` minus the number of usable
spanners already carried remain to be picked up.

*Walking.*  The man must stand at a nut's location to tighten it, so at least the
`link` distance from the man to the farthest loose goal nut remains to be walked.
`tighten_nut` only ever removes a nut the man is standing on, whose distance is
zero, so the maximum cannot jump when a nut is tightened.

*Dead ends.*  `link` is one-way: once the man walks past a spanner he can never
return for it.  If the usable spanners he carries plus those still ahead of him
number fewer than the loose goal nuts, no plan exists.  That comparison only ever
gets worse along a transition — walking shrinks what is ahead, and `tighten_nut`
decrements both sides — so returning a large constant on those states is
consistent, and it is admissible for the trivial reason that there is no plan to
underestimate.  This is where the heuristic earns its keep: blind search and
LM-cut both explore the whole doomed subtree.
-/
import Planner.ExampleHeuristics.Base
import Planner.Distance

namespace Planner.ExampleHeuristics.Spanner

open Planner.Pddl

/-- What the heuristic needs to know about one spanner. -/
structure SpannerInfo where
  /-- The fact `usable(spanner)`. -/
  usableFact : Fact
  /-- The facts `carrying(man, spanner)`. -/
  carryFacts : Array Fact
  /-- The facts `at(spanner, l)`, with `l`. -/
  atFacts : Array (Fact × Nat)
  deriving Inhabited

structure Data where
  dist : Distances
  /-- The facts `at(man, l)`, with `l`, for every man. -/
  menAt : Array (Array (Fact × Nat))
  /-- Goal facts `tightened(nut)` with the nut's fixed location. -/
  nuts : Array (Fact × Nat)
  spanners : Array SpannerInfo
  deriving Inhabited

/--
The `at` facts of one object, each paired with the graph node of the place it
names.

Split out of `compile` as a named `filterMap` rather than written inside it:
`Proofs/Lifted/SpannerCompile.lean` reads the table entry by entry, and a named
function is what that reading needs.  It computes exactly what the loop did.
-/
def atOf (atFacts : Array (Fact × GroundAtom)) (graph : Graph) (who : Name) :
    Array (Fact × Nat) :=
  atFacts.filterMap fun y =>
    match y.2.args with
    | [x, l] => if x == who then (graph.find? l).map ((y.1, ·)) else none
    | _ => none

/--
The entry one goal atom contributes: a `tightened` goal whose nut stands
somewhere `:init` names.  Nut positions never change — no schema adds or deletes
`at` for a nut — so the initial state settles them once.
-/
def nutEntry (t : Task) (at? : Name → Array (Fact × Nat)) (x : GroundAtom × Nat) :
    Option (Fact × Nat) :=
  match x.1.pred == "tightened", x.1.args with
  | true, [n] =>
      ((at? n).find? fun y => t.init.test y.1).map fun y => (t.goal.getD x.2 0, y.2)
  | _, _ => none

/-- The entry one spanner contributes, if the task numbers its `usable` fact. -/
def spannerEntry (usableFacts carryFacts : Array (Fact × GroundAtom))
    (at? : Name → Array (Fact × Nat)) (sp : Name) : Option SpannerInfo :=
  (usableFacts.find? fun y => y.2.args == [sp]).map fun y =>
    { usableFact := y.1
      carryFacts := carryFacts.filterMap fun z =>
        match z.2.args with
        | [_, x] => if x == sp then some z.1 else none
        | _ => none
      atFacts := at? sp }

def compile (t : Task) : Data :=
  let locations := t.objectsOfTypes ["location"]
  let graph := Graph.ofStatic t "link" locations
  let at? := atOf (t.factsWith "at") graph
  { dist := Distances.of graph
    menAt := (t.objectsOfTypes ["man"]).map at?
    nuts := t.goalAtoms.zipIdx.filterMap (nutEntry t at?)
    spanners := (t.objectsOfTypes ["spanner"]).filterMap
      (spannerEntry (t.factsWith "usable") (t.factsWith "carrying") at?) }

/-- Where the men currently stand. -/
@[inline] def menLocations (d : Data) (s : State) : Array Nat :=
  d.menAt.filterMap fun facts =>
    (facts.find? fun (f, _) => s.test f).map (·.2)

/-- The goal nuts still to be tightened. -/
@[inline] def looseNuts (d : Data) (s : State) : Array (Fact × Nat) :=
  d.nuts.filter fun x => !s.test x.1

/-- How far the nearest man is from the farthest nut still loose. -/
@[inline] def walkBound (d : Data) (s : State) (men : Array Nat) : Nat :=
  (looseNuts d s).foldl (init := 0) fun acc x => max acc (d.dist.minFrom men x.2)

/-- Usable spanners a man is already carrying. -/
@[inline] def carriedSpanners (d : Data) (s : State) : Array SpannerInfo :=
  d.spanners.filter fun sp =>
    s.test sp.usableFact && sp.carryFacts.any fun f => s.test f

/-- Usable spanners lying on the ground that some man can still reach. -/
@[inline] def aheadSpanners (d : Data) (s : State) (men : Array Nat) : Array SpannerInfo :=
  d.spanners.filter fun sp =>
    s.test sp.usableFact && !(sp.carryFacts.any fun f => s.test f) &&
      (match sp.atFacts.find? fun y => s.test y.1 with
       | some (_, l) => d.dist.minFrom men l < d.dist.bound
       | none => false)

/--
The value, as the three families of the header plus the dead-end test.

Written as named pieces rather than a loop over mutable counters: the pieces are
what the correctness argument talks about, so they are what the proof needs to
name.  It computes exactly what the loop version did.
-/
def value (d : Data) (s : State) : Nat :=
  let men := menLocations d s
  let loose := (looseNuts d s).size
  let carried := (carriedSpanners d s).size
  if loose == 0 then 0
  else if carried + (aheadSpanners d s men).size < loose then deadEnd
  else loose + (loose - carried) + walkBound d s men

def improved (t : Task) : Heuristic :=
  let d := compile t
  { name := "spanner-improved", eval := value d }

end Planner.ExampleHeuristics.Spanner
