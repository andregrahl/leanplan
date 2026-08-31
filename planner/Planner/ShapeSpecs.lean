/-
The transition shapes the proofs case on, as decidable claims.

Each entry mirrors, at the level of the counters, the shape its domain's proof
uses.  `planner --audit-shape` walks the reachable states and reports any
transition no case covers, which is what makes a shape unsatisfiable.
-/
import Planner.ShapeAudit
import Planner.ExampleHeuristics.Spanner.Improved
import Planner.ExampleHeuristics.Transport.Improved
import Planner.ExampleHeuristics.Satellite.Improved
import Planner.ExampleHeuristics.Floortile.Improved
import Planner.ExampleHeuristics.Sokoban.Improved

namespace Planner

/-! ### Spanner -/

namespace SpannerShape

open ExampleHeuristics.Spanner

private def L (d : Data) (s : State) : Nat := (looseNuts d s).size
private def C (d : Data) (s : State) : Nat := (carriedSpanners d s).size
private def A (d : Data) (s : State) : Nat := (aheadSpanners d s (menLocations d s)).size
private def W (d : Data) (s : State) : Nat := walkBound d s (menLocations d s)

def spec (t : Task) : ShapeSpec :=
  let d := compile t
  { cases := #[
      { name := "tighten"
        holds := fun s s' => L d s' + 1 == L d s && C d s' + 1 == C d s
          && W d s ≤ W d s' && A d s' ≤ A d s },
      { name := "pickup"
        holds := fun s s' => L d s' == L d s && C d s + 1 == C d s'
          && W d s == W d s' && C d s' + A d s' ≤ C d s + A d s },
      { name := "walk"
        holds := fun s s' => L d s' == L d s && C d s' == C d s
          && W d s ≤ W d s' + 1 && A d s' ≤ A d s },
      { name := "stall"
        holds := fun s s' => L d s' == L d s && C d s' ≤ C d s
          && W d s ≤ W d s' && A d s' ≤ A d s }] }

end SpannerShape

/-! ### Transport -/

namespace TransportShape

open ExampleHeuristics.Transport

private def H (d : Data) (s : State) : Nat := handling d s
private def D (d : Data) (s : State) : Nat := driving d s
private def R (d : Data) (s : State) : Nat := (requiredLocs d s).length

def spec (t : Task) : ShapeSpec :=
  let d := compile t
  { cases := #[
      { name := "load"
        holds := fun s s' => H d s ≤ H d s' + 1 && D d s ≤ D d s' && R d s ≤ R d s' },
      { name := "drive"
        holds := fun s s' => H d s' == H d s && D d s ≤ D d s' + 1 && R d s ≤ R d s' + 1 },
      { name := "stall"
        holds := fun s s' => H d s' == H d s && D d s' == D d s && R d s' == R d s }] }

end TransportShape

/-! ### Satellite -/

namespace SatelliteShape

open ExampleHeuristics.Satellite

private def I (d : Data) (s : State) : Nat :=
  coverCount d (uncalibratedModes d s) + coverCount d (unpoweredModes d s) + freeSlot d s
private def U (d : Data) (s : State) : Nat := (unmetImages d s).size
private def T (d : Data) (s : State) : Nat := turns d s

def spec (t : Task) : ShapeSpec :=
  let d := compile t
  { cases := #[
      { name := "image"
        holds := fun s s' => U d s' + 1 == U d s && I d s' == I d s && T d s ≤ T d s' },
      { name := "ready"
        holds := fun s s' => U d s' == U d s && I d s ≤ I d s' + 1 && T d s ≤ T d s' },
      { name := "turn"
        holds := fun s s' => U d s' == U d s && I d s' == I d s && T d s ≤ T d s' + 1 }] }

end SatelliteShape

/-! ### Floortile -/

namespace FloortileShape

open ExampleHeuristics.Floortile

private def U (d : Data) (s : State) : Nat := unpainted d s
private def R (d : Data) (s : State) : Nat := recolours d s
private def M (d : Data) (s : State) : Nat := movement d s

def spec (t : Task) : ShapeSpec :=
  let d := compile t
  { cases := #[
      -- the dead-end guard carries the value on its own
      { name := "dead"
        holds := fun s s' => isDead d s || isDead d s' },
      { name := "paint"
        holds := fun s s' => U d s' + 1 == U d s && R d s ≤ R d s' && M d s ≤ M d s' },
      { name := "changeColour"
        holds := fun s s' => U d s' == U d s && R d s ≤ R d s' + 1 && M d s ≤ M d s' },
      { name := "move"
        holds := fun s s' => U d s' == U d s && R d s ≤ R d s' && M d s ≤ M d s' + 1 },
      { name := "other"
        holds := fun s s' => U d s' == U d s && R d s ≤ R d s' && M d s ≤ M d s' }]
    guard := some (isDead d) }

end FloortileShape

/-! ### Sokoban -/

namespace SokobanShape

open ExampleHeuristics.Sokoban

private def P (d : Data) (s : State) : Nat := pushes d s
private def A (d : Data) (s : State) : Nat := approach d s
private def H (d : Data) (s : State) : Nat := hardest d s

def spec (t : Task) : ShapeSpec :=
  let d := compile t
  { cases := #[
      { name := "move"
        holds := fun s s' => P d s' == P d s && A d s ≤ A d s' + 1 && H d s ≤ H d s' + 1 },
      { name := "push"
        holds := fun s s' => P d s ≤ P d s' + 1 && A d s ≤ A d s' && H d s ≤ H d s' + 1 }] }

end SokobanShape

/-- The shape a heuristic name selects, if one is registered. -/
def shapeSpecFor (name : String) (t : Task) : Option ShapeSpec :=
  match name with
  | "spanner-improved" => some (SpannerShape.spec t)
  | "transport-improved" => some (TransportShape.spec t)
  | "satellite-improved" => some (SatelliteShape.spec t)
  | "floortile-improved" => some (FloortileShape.spec t)
  | "sokoban-improved" => some (SokobanShape.spec t)
  | _ => none

end Planner
