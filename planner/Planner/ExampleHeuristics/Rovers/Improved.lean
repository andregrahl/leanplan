/-
Rovers, improved heuristic.

Seven schema families, each bounded on its own and then added, because no action
belongs to two of them.

  * `communicate_*`: one per unmet `communicated_*` goal — each such action
    produces exactly one of those atoms.
  * `sample_soil` / `sample_rock`: one per unmet data goal whose analysis nobody
    holds yet.  The waypoint identifies the action, so these never coincide.
  * `take_image`: one per unmet image goal whose picture nobody holds yet.
  * `calibrate`: `take_image` consumes the calibration it uses, so each of those
    images needs its own `calibrate` beyond the cameras calibrated right now.
  * `drop`: each sample fills the rover's store, so each of those samples needs
    its own empty store beyond the ones empty right now.
  * `navigate`: a rover has to stand on a waypoint to sample it.  Each `navigate`
    moves one rover one step, so the largest distance from a suitably equipped
    rover to a waypoint still to be sampled is a lower bound.

The single largest distance is a weak bound once several waypoints are still to
be sampled, since it sees only the farthest one.  A second `navigate` bound counts
them instead: every waypoint still to be sampled needs a rover standing on it, and
one `navigate` arrives at exactly one waypoint, so the waypoints that no rover
occupies right now each cost at least one.  Sampling cannot cheat it, because
sampling requires the rover to be there already, so the waypoint it removes was
contributing nothing.  Both bounds constrain `navigate`, so they are combined with
`max` rather than added.

The two "consumed resource" terms are what make this more than landmark counting:
they see that a second image needs a second calibration and a second sample needs
the store emptied, which a goal count never notices.  Both survive their
consuming action because it decrements demand and supply together.
-/
import Planner.ExampleHeuristics.Base
import Planner.Distance

namespace Planner.ExampleHeuristics.Rovers

open Planner.Pddl

/-- An unmet `communicated_soil_data` or `communicated_rock_data` goal. -/
structure SampleGoal where
  goalFact : Fact
  /-- The waypoint to sample, as a graph node. -/
  waypoint : Nat
  /-- The facts `have_*_analysis(r, w)` over all rovers. -/
  analysisFacts : Array Fact
  deriving Inhabited

/-- An unmet `communicated_image_data` goal. -/
structure ImageGoal where
  goalFact : Fact
  /-- The facts `have_image(r, o, m)` over all rovers. -/
  haveFacts : Array Fact
  deriving Inhabited

structure Data where
  /-- One traversal distance table per rover; `navigate` follows `can_traverse`. -/
  dist : Array Distances
  /-- For each rover, the facts `at(rover, w)` with the waypoint index. -/
  roverAt : Array (Array (Fact × Nat))
  /-- Rovers equipped for soil and for rock analysis, as rover indices. -/
  soilRovers : Array Nat
  rockRovers : Array Nat
  soilGoals : Array SampleGoal
  rockGoals : Array SampleGoal
  imageGoals : Array ImageGoal
  /-- All `calibrated` facts and all `empty` facts. -/
  calibratedFacts : Array Fact
  emptyFacts : Array Fact
  deriving Inhabited

/-- The traversal graph of one rover.  Not `private`: the consistency proof has
to name it, to read an edge back out of it. -/
def roverGraph (t : Task) (waypoints : Array Name) (r : Name) : Graph :=
  -- Built with the shared `ofEdges`, not by hand: a consistency proof has to read
  -- an edge back out of the graph, and `Proofs/Distance.lean` proves that of
  -- `ofEdges` once for every domain.  `navigate` is applicable exactly when
  -- `can_traverse(r, y, z)` and `visible(y, z)` hold, so those are the edges.
  let visible := t.staticWith "visible"
  Graph.ofEdges waypoints (t.staticAtoms.filterMap fun a =>
    if a.pred == "can_traverse" then
      match a.args with
      | [x, y, z] =>
          if x == r && visible.any (fun b => b.args == [y, z]) then
            some ({ pred := "can_traverse", args := [y, z] } : GroundAtom)
          else none
      | _ => none
    else none)

def compile (t : Task) : Data := Id.run do
  let waypoints := t.objectsOfTypes ["waypoint"]
  let rovers := t.objectsOfTypes ["rover"]
  let wpIndex : Name → Option Nat := fun w => waypoints.findIdx? (· == w)
  let dist := rovers.map fun r => Distances.of (roverGraph t waypoints r)
  let atFacts := t.factsWith "at"
  let roverAt := rovers.map fun r =>
    atFacts.filterMap fun (f, a) =>
      match a.args with
      | [x, w] => if x == r then (wpIndex w).map ((f, ·)) else none
      | _ => none
  let equipped : Name → Array Nat := fun pred =>
    (t.staticWith pred).filterMap fun a =>
      match a.args with
      | [r] => rovers.findIdx? (· == r)
      | _ => none
  let soilFacts := t.factsWith "have_soil_analysis"
  let rockFacts := t.factsWith "have_rock_analysis"
  let imageFacts := t.factsWith "have_image"

  let analysisOf (facts : Array (Fact × GroundAtom)) (w : Name) : Array Fact :=
    facts.filterMap fun (f, a) =>
      match a.args with
      | [_, x] => if x == w then some f else none
      | _ => none

  -- The three goal tables, each a filter of the goal atoms.  Written this way
  -- rather than as one loop with three accumulators so that a proof can say what
  -- an entry is: an imperative fold hides that behind its own induction, and
  -- every reader lemma would have to unfold it first.
  let soilGoals : Array SampleGoal := t.goalAtoms.zipIdx.filterMap fun (a, i) =>
    match a.pred, a.args with
    | "communicated_soil_data", [w] =>
        (wpIndex w).map fun wi =>
          { goalFact := t.goal.getD i 0, waypoint := wi,
            analysisFacts := analysisOf soilFacts w }
    | _, _ => none
  let rockGoals : Array SampleGoal := t.goalAtoms.zipIdx.filterMap fun (a, i) =>
    match a.pred, a.args with
    | "communicated_rock_data", [w] =>
        (wpIndex w).map fun wi =>
          { goalFact := t.goal.getD i 0, waypoint := wi,
            analysisFacts := analysisOf rockFacts w }
    | _, _ => none
  let imageGoals : Array ImageGoal := t.goalAtoms.zipIdx.filterMap fun (a, i) =>
    match a.pred, a.args with
    | "communicated_image_data", [o, m] =>
        some { goalFact := t.goal.getD i 0
               haveFacts := imageFacts.filterMap fun (fi, b) =>
                 match b.args with
                 | [_, x, y] => if x == o && y == m then some fi else none
                 | _ => none }
    | _, _ => none

  return { dist, roverAt
           soilRovers := equipped "equipped_for_soil_analysis"
           rockRovers := equipped "equipped_for_rock_analysis"
           soilGoals, rockGoals, imageGoals
           calibratedFacts := (t.factsWith "calibrated").map (·.1)
           emptyFacts := (t.factsWith "empty").map (·.1) }

/-- The smallest number of `navigate` steps from a suitably equipped rover to `w`. -/
@[inline] def reach (d : Data) (s : State) (crew : Array Nat) (w : Nat) : Nat :=
  let best := crew.foldl (init := none) fun acc r =>
    match (d.roverAt.getD r #[]).find? fun (f, _) => s.test f with
    | some (_, here) =>
        let v := (d.dist.getD r default).get here w
        some (match acc with | none => v | some a => min a v)
    | none => acc
  best.getD 0

@[inline] def unmetSoil (d : Data) (s : State) : Array SampleGoal :=
  d.soilGoals.filter fun g => !s.test g.goalFact
@[inline] def unmetRock (d : Data) (s : State) : Array SampleGoal :=
  d.rockGoals.filter fun g => !s.test g.goalFact
@[inline] def unmetImage (d : Data) (s : State) : Array ImageGoal :=
  d.imageGoals.filter fun g => !s.test g.goalFact

/-- One `communicate` per unachieved goal. -/
@[inline] def communicate (d : Data) (s : State) : Nat :=
  (unmetSoil d s).size + (unmetRock d s).size + (unmetImage d s).size

/-- Nobody holds this analysis yet. -/
@[inline] def needsSample (s : State) (g : SampleGoal) : Bool :=
  !(g.analysisFacts.any fun f => s.test f)

@[inline] def soilToSample (d : Data) (s : State) : Array SampleGoal :=
  (unmetSoil d s).filter fun g => needsSample s g
@[inline] def rockToSample (d : Data) (s : State) : Array SampleGoal :=
  (unmetRock d s).filter fun g => needsSample s g

/-- One `sample_*` per goal whose analysis is missing. -/
@[inline] def samples (d : Data) (s : State) : Nat :=
  (soilToSample d s).size + (rockToSample d s).size

/-- One `take_image` per goal whose picture is missing. -/
@[inline] def images (d : Data) (s : State) : Nat :=
  ((unmetImage d s).filter fun g => !(g.haveFacts.any fun f => s.test f)).size

@[inline] def calibrated (d : Data) (s : State) : Nat := countHolding d.calibratedFacts s
@[inline] def emptyStores (d : Data) (s : State) : Nat := countHolding d.emptyFacts s

/-- Waypoints still to be sampled. -/
@[inline] def requiredWaypoints (d : Data) (s : State) : List Nat :=
  distinct (((soilToSample d s).toList ++ (rockToSample d s).toList).map (·.waypoint))

@[inline] def occupied (d : Data) (s : State) (w : Nat) : Bool :=
  d.roverAt.any fun facts => facts.any fun x => x.2 == w && s.test x.1

/-- One `navigate` per waypoint still to be sampled that no rover stands on. -/
@[inline] def arrivals (d : Data) (s : State) : Nat :=
  ((requiredWaypoints d s).filter fun w => !occupied d s w).length

/-- The distance from the nearest suitably equipped rover to the farthest such waypoint. -/
@[inline] def travel (d : Data) (s : State) : Nat :=
  max ((soilToSample d s).foldl (init := 0) fun acc g =>
         max acc (reach d s d.soilRovers g.waypoint))
      ((rockToSample d s).foldl (init := 0) fun acc g =>
         max acc (reach d s d.rockRovers g.waypoint))

/-- The five counting families, plus the navigation bound. -/
@[inline] def baseCount (d : Data) (s : State) : Nat :=
  communicate d s + samples d s + images d s
    + (images d s - calibrated d s) + (samples d s - emptyStores d s)

/--
Six families that never share an action, bounded separately and added.

Written as named pieces rather than a loop over mutable counters: the pieces are
what the correctness argument talks about, so they are what the proof needs to
name.  It computes exactly what the loop version did.
-/
def value (d : Data) (s : State) : Nat :=
  baseCount d s + max (travel d s) (arrivals d s)

def improved (t : Task) : Heuristic :=
  let d := compile t
  { name := "rovers-improved", eval := value d }

end Planner.ExampleHeuristics.Rovers
