/-
Rovers's improved heuristic, proved end to end in one file.

The order below is the order the argument is built in.  The schema-level proof
comes first: the improved value over the domain's own data, and what each schema
does to the counters.  The rest lifts that value to the parsed domain and
compiles it against the numbered task.

The runtime heuristic and its data stay under `Planner/`.  The simple heuristic
of this domain is proved in `Proofs/Domains/RoversSimple.lean`.
-/
import Planner.ExampleHeuristics.Rovers.Certificate
import Proofs.Heuristic
import Planner.GeneratedDomains.Rovers
import Proofs.Combinators
import Proofs.Certificates
import Proofs.Distance
import Proofs.SchemaSupport
import Proofs.LiftedHeuristic
import Proofs.CompileSupport
import Proofs.Validation
import Proofs.FactTables
import Planner.ExampleHeuristics.Rovers.Improved

/- -------------------------------------------------------------------------- -/
/-
Rovers, improved heuristic: goal awareness and the two quantities.

The consistency half lives in `Schema.lean`, which states what the domain's nine
schemas do to the predicates and derives the base count and the navigation bound
from that.
-/

namespace Planner.ExampleHeuristics.Rovers

open Planner

/-! ### The two quantities -/

/-- The five counting families. -/
abbrev Bc (d : Data) (s : State) : Nat := baseCount d s
/-- The navigation bound. -/
abbrev Rc (d : Data) (s : State) : Nat := max (travel d s) (arrivals d s)

/-! ### Assembly -/

theorem unmet_empty (d : Data) (s : State)
    (h1 : ∀ g ∈ d.soilGoals, s.test g.goalFact = true)
    (h2 : ∀ g ∈ d.rockGoals, s.test g.goalFact = true)
    (h3 : ∀ g ∈ d.imageGoals, s.test g.goalFact = true) :
    unmetSoil d s = #[] ∧ unmetRock d s = #[] ∧ unmetImage d s = #[] := by
  refine ⟨?_, ?_, ?_⟩ <;> [skip; skip; skip] <;>
    · first
        | (unfold unmetSoil; rw [Array.filter_eq_empty_iff]; intro x hx; simp [h1 x hx])
        | (unfold unmetRock; rw [Array.filter_eq_empty_iff]; intro x hx; simp [h2 x hx])
        | (unfold unmetImage; rw [Array.filter_eq_empty_iff]; intro x hx; simp [h3 x hx])

theorem value_eq_zero_of_goal (d : Data) (s : State)
    (h1 : ∀ g ∈ d.soilGoals, s.test g.goalFact = true)
    (h2 : ∀ g ∈ d.rockGoals, s.test g.goalFact = true)
    (h3 : ∀ g ∈ d.imageGoals, s.test g.goalFact = true) : value d s = 0 := by
  obtain ⟨e1, e2, e3⟩ := unmet_empty d s h1 h2 h3
  unfold value baseCount communicate samples images travel arrivals requiredWaypoints
    soilToSample rockToSample
  rw [e1, e2, e3]
  simp [travel, arrivals, distinct]

theorem improved_goalAware (t : Task)
    (c1 : ∀ g ∈ (compile t).soilGoals, g.goalFact ∈ t.goal)
    (c2 : ∀ g ∈ (compile t).rockGoals, g.goalFact ∈ t.goal)
    (c3 : ∀ g ∈ (compile t).imageGoals, g.goalFact ∈ t.goal) :
    t.GoalAware (improved t).eval := by
  refine t.goalAware_of _ fun s _ hgoal => ?_
  exact value_eq_zero_of_goal _ s (fun g hg => hgoal _ (c1 g hg))
    (fun g hg => hgoal _ (c2 g hg)) (fun g hg => hgoal _ (c3 g hg))

end Planner.ExampleHeuristics.Rovers

/- -------------------------------------------------------------------------- -/
/-
Rovers, stated at the schema level.

`Effect` in `Improved.lean` assumes how one action moves the base count and the
navigation bound.  This file assumes only what the domain's schemas do to the
predicates the heuristic reads — which goals hold, which analyses and images are
in hand, which stores are empty, which cameras are calibrated, where each rover
stands — and derives both counters.

Eight of the nine schemas move no rover, so they share one congruence lemma for
the navigation bound; only `navigate` needs the distance argument.
-/

namespace Planner.ExampleHeuristics.Rovers

open Planner

/-! ### The state, read in the domain's vocabulary -/

/-- A sample goal still to communicate. -/
def liveS (s : State) (g : SampleGoal) : Bool := !s.test g.goalFact
/-- An image goal still to communicate. -/
def liveI (s : State) (g : ImageGoal) : Bool := !s.test g.goalFact
/-- Some rover holds this picture. -/
def hasImage (s : State) (g : ImageGoal) : Bool := g.haveFacts.any fun f => s.test f
/-- The `at` fact of a rover that currently holds, exactly as `reach` reads it. -/
def roverFind (d : Data) (s : State) (r : Nat) : Option (Fact × Nat) :=
  (d.roverAt.getD r #[]).find? fun (f, _) => s.test f

theorem reach_congr {d : Data} {s s' : State}
    (h : ∀ r, roverFind d s' r = roverFind d s r) (crew : Array Nat) (w : Nat) :
    reach d s' crew w = reach d s crew w := by
  unfold reach
  unfold roverFind at h
  simp only [h]

/-! ### The counters, as filters over the goal lists -/

theorem soilToSample_toList (d : Data) (s : State) :
    (soilToSample d s).toList = d.soilGoals.toList.filter fun g => needsSample s g && liveS s g := by
  unfold soilToSample unmetSoil liveS
  rw [Array.toList_filter, Array.toList_filter, List.filter_filter]

theorem rockToSample_toList (d : Data) (s : State) :
    (rockToSample d s).toList = d.rockGoals.toList.filter fun g => needsSample s g && liveS s g := by
  unfold rockToSample unmetRock liveS
  rw [Array.toList_filter, Array.toList_filter, List.filter_filter]

theorem images_inner (d : Data) (s : State) :
    List.filter (fun g => !(g.haveFacts.any fun f => s.test f)) (unmetImage d s).toList
      = d.imageGoals.toList.filter fun g =>
          (!(g.haveFacts.any fun f => s.test f)) && liveI s g := by
  unfold unmetImage liveI
  rw [Array.toList_filter, List.filter_filter]

/-! ### Congruence: when nothing the counters read has moved -/

/-- The sampling sets are determined by the goal facts and the analyses in hand. -/
theorem soilToSample_congr {d : Data} {s s' : State}
    (hg : ∀ g ∈ d.soilGoals, s'.test g.goalFact = s.test g.goalFact)
    (ha : ∀ g ∈ d.soilGoals, needsSample s' g = needsSample s g) :
    soilToSample d s' = soilToSample d s :=
  Array.toList_inj.mp (by
    rw [soilToSample_toList, soilToSample_toList]
    refine List.filter_congr ?_
    intro g hgm
    have hm : g ∈ d.soilGoals := by simpa using hgm
    simp [liveS, hg g hm, ha g hm])

theorem rockToSample_congr {d : Data} {s s' : State}
    (hg : ∀ g ∈ d.rockGoals, s'.test g.goalFact = s.test g.goalFact)
    (ha : ∀ g ∈ d.rockGoals, needsSample s' g = needsSample s g) :
    rockToSample d s' = rockToSample d s :=
  Array.toList_inj.mp (by
    rw [rockToSample_toList, rockToSample_toList]
    refine List.filter_congr ?_
    intro g hgm
    have hm : g ∈ d.rockGoals := by simpa using hgm
    simp [liveS, hg g hm, ha g hm])

/-- The navigation bound reads only the sampling sets and where the rovers stand. -/
theorem Rc_congr {d : Data} {s s' : State}
    (hsoil : soilToSample d s' = soilToSample d s)
    (hrock : rockToSample d s' = rockToSample d s)
    (hfind : ∀ r, roverFind d s' r = roverFind d s r)
    (hocc : ∀ w, occupied d s' w = occupied d s w) :
    Rc d s' = Rc d s := by
  have htravel : travel d s' = travel d s := by
    unfold travel
    rw [hsoil, hrock]
    simp only [reach_congr hfind]
  have harr : arrivals d s' = arrivals d s := by
    unfold arrivals requiredWaypoints
    rw [hsoil, hrock]
    congr 1
    exact List.filter_congr fun w _ => by rw [hocc w]
  show max (travel d s') (arrivals d s') = max (travel d s) (arrivals d s)
  rw [htravel, harr]

/--
Sampling soil at an occupied waypoint cannot lower the navigation bound.  A
soil goal may leave the sampling set, but only at that waypoint; its travel
term was zero and it was absent from the unoccupied-waypoint count already.
-/
theorem Rc_le_of_soil_sample {d : Data} {s s' : State} {w : Nat}
    (hsoil : ∀ g ∈ soilToSample d s,
      g ∈ soilToSample d s' ∨ g.waypoint = w)
    (hrock : rockToSample d s' = rockToSample d s)
    (hfind : ∀ r, roverFind d s' r = roverFind d s r)
    (hocc : ∀ u, occupied d s' u = occupied d s u)
    (hhere : occupied d s w = true)
    (hzero : reach d s d.soilRovers w = 0) :
    Rc d s ≤ Rc d s' := by
  have hsmax : (soilToSample d s).toList.foldl
        (fun acc g => max acc (reach d s d.soilRovers g.waypoint)) 0
      ≤ (soilToSample d s').toList.foldl
        (fun acc g => max acc (reach d s' d.soilRovers g.waypoint)) 0 := by
    refine foldl_max_le_bound _ _ _ (fun g hg => ?_) 0 (Nat.zero_le _)
    rcases hsoil g (by simpa using hg) with hg' | hgw
    · have hr := reach_congr hfind d.soilRovers g.waypoint
      rw [← hr]
      exact foldl_max_ge_mem (soilToSample d s').toList
        (fun g => reach d s' d.soilRovers g.waypoint) (by simpa using hg') 0
    · rw [hgw, hzero]
      exact Nat.zero_le _
  have hrmax : (rockToSample d s).toList.foldl
        (fun acc g => max acc (reach d s d.rockRovers g.waypoint)) 0
      ≤ (rockToSample d s').toList.foldl
        (fun acc g => max acc (reach d s' d.rockRovers g.waypoint)) 0 := by
    rw [hrock]
    refine foldl_max_mono _ _ _ (fun g _ => ?_) 0 0 (Nat.le_refl _)
    exact Nat.le_of_eq (reach_congr hfind d.rockRovers g.waypoint).symm
  have htravel : travel d s ≤ travel d s' := by
    unfold travel
    simp only [← Array.foldl_toList]
    omega
  have harr : arrivals d s ≤ arrivals d s' := by
    unfold arrivals requiredWaypoints
    refine length_le_of_subset _ _ ((distinct_nodup _).filter _) ?_
    intro u hu
    rw [List.mem_filter] at hu ⊢
    refine ⟨?_, ?_⟩
    · rw [mem_distinct, List.mem_map] at hu ⊢
      obtain ⟨g, hg, hgu⟩ := hu.1
      rcases List.mem_append.mp hg with hg | hg
      · rcases hsoil g (by simpa using hg) with hg' | hgw
        · exact ⟨g, List.mem_append.mpr (Or.inl (by simpa using hg')), hgu⟩
        · have huw : u = w := hgu.symm.trans hgw
          have hnot : (!occupied d s u) = true := hu.2
          rw [huw, hhere] at hnot
          exact Bool.noConfusion hnot
      · have hg' : g ∈ (rockToSample d s').toList := by
          rw [hrock]
          exact hg
        exact ⟨g, List.mem_append.mpr (Or.inr hg'), hgu⟩
    · rw [hocc u]
      exact hu.2
  show max (travel d s) (arrivals d s) ≤ max (travel d s') (arrivals d s')
  omega

/-- The symmetric navigation fact for a rock sample. -/
theorem Rc_le_of_rock_sample {d : Data} {s s' : State} {w : Nat}
    (hsoil : soilToSample d s' = soilToSample d s)
    (hrock : ∀ g ∈ rockToSample d s,
      g ∈ rockToSample d s' ∨ g.waypoint = w)
    (hfind : ∀ r, roverFind d s' r = roverFind d s r)
    (hocc : ∀ u, occupied d s' u = occupied d s u)
    (hhere : occupied d s w = true)
    (hzero : reach d s d.rockRovers w = 0) :
    Rc d s ≤ Rc d s' := by
  have hsmax : (soilToSample d s).toList.foldl
        (fun acc g => max acc (reach d s d.soilRovers g.waypoint)) 0
      ≤ (soilToSample d s').toList.foldl
        (fun acc g => max acc (reach d s' d.soilRovers g.waypoint)) 0 := by
    rw [hsoil]
    refine foldl_max_mono _ _ _ (fun g _ => ?_) 0 0 (Nat.le_refl _)
    exact Nat.le_of_eq (reach_congr hfind d.soilRovers g.waypoint).symm
  have hrmax : (rockToSample d s).toList.foldl
        (fun acc g => max acc (reach d s d.rockRovers g.waypoint)) 0
      ≤ (rockToSample d s').toList.foldl
        (fun acc g => max acc (reach d s' d.rockRovers g.waypoint)) 0 := by
    refine foldl_max_le_bound _ _ _ (fun g hg => ?_) 0 (Nat.zero_le _)
    rcases hrock g (by simpa using hg) with hg' | hgw
    · have hr := reach_congr hfind d.rockRovers g.waypoint
      rw [← hr]
      exact foldl_max_ge_mem (rockToSample d s').toList
        (fun g => reach d s' d.rockRovers g.waypoint) (by simpa using hg') 0
    · rw [hgw, hzero]
      exact Nat.zero_le _
  have htravel : travel d s ≤ travel d s' := by
    unfold travel
    simp only [← Array.foldl_toList]
    omega
  have harr : arrivals d s ≤ arrivals d s' := by
    unfold arrivals requiredWaypoints
    refine length_le_of_subset _ _ ((distinct_nodup _).filter _) ?_
    intro u hu
    rw [List.mem_filter] at hu ⊢
    refine ⟨?_, ?_⟩
    · rw [mem_distinct, List.mem_map] at hu ⊢
      obtain ⟨g, hg, hgu⟩ := hu.1
      rcases List.mem_append.mp hg with hg | hg
      · have hg' : g ∈ (soilToSample d s').toList := by
          rw [hsoil]
          exact hg
        exact ⟨g, List.mem_append.mpr (Or.inl hg'), hgu⟩
      · rcases hrock g (by simpa using hg) with hg' | hgw
        · exact ⟨g, List.mem_append.mpr (Or.inr (by simpa using hg')), hgu⟩
        · have huw : u = w := hgu.symm.trans hgw
          have hnot : (!occupied d s u) = true := hu.2
          rw [huw, hhere] at hnot
          exact Bool.noConfusion hnot
    · rw [hocc u]
      exact hu.2
  show max (travel d s) (arrivals d s) ≤ max (travel d s') (arrivals d s')
  omega

/-! ### The base count -/

private theorem foldl_count_congr (s s' : State) :
    ∀ (l : List Fact), (∀ f ∈ l, s'.test f = s.test f) → ∀ a : Nat,
      l.foldl (fun acc f => if s'.test f then acc + 1 else acc) a
        = l.foldl (fun acc f => if s.test f then acc + 1 else acc) a := by
  intro l
  induction l with
  | nil => intro _ a; rfl
  | cons f rest ih =>
      intro h a
      simp only [List.foldl_cons, h f (by simp)]
      exact ih (fun g hg => h g (by simp [hg])) _

theorem countHolding_congr (facts : Array Fact) {s s' : State}
    (h : ∀ f ∈ facts, s'.test f = s.test f) :
    countHolding facts s' = countHolding facts s := by
  unfold countHolding
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact foldl_count_congr s s' facts.toList (fun f hf => h f (by simpa using hf)) 0

theorem unmetSoil_congr {d : Data} {s s' : State}
    (hg : ∀ g ∈ d.soilGoals, s'.test g.goalFact = s.test g.goalFact) :
    unmetSoil d s' = unmetSoil d s :=
  array_filter_congr _ _ _ fun g hg' => by simp [hg g hg']

theorem unmetRock_congr {d : Data} {s s' : State}
    (hg : ∀ g ∈ d.rockGoals, s'.test g.goalFact = s.test g.goalFact) :
    unmetRock d s' = unmetRock d s :=
  array_filter_congr _ _ _ fun g hg' => by simp [hg g hg']

theorem unmetImage_congr {d : Data} {s s' : State}
    (hg : ∀ g ∈ d.imageGoals, s'.test g.goalFact = s.test g.goalFact) :
    unmetImage d s' = unmetImage d s :=
  array_filter_congr _ _ _ fun g hg' => by simp [hg g hg']

theorem images_congr {d : Data} {s s' : State}
    (hg : ∀ g ∈ d.imageGoals, s'.test g.goalFact = s.test g.goalFact)
    (hi : ∀ g ∈ d.imageGoals, hasImage s' g = hasImage s g) :
    images d s' = images d s := by
  unfold images
  rw [unmetImage_congr hg]
  congr 1
  refine array_filter_congr _ _ _ ?_
  intro g hgm
  have hm : g ∈ d.imageGoals := by
    simp only [unmetImage, Array.mem_filter] at hgm; exact hgm.1
  simpa [hasImage] using congrArg (! ·) (hi g hm)

/-- Everything the base count reads, unchanged. -/
theorem Bc_congr {d : Data} {s s' : State}
    (hsg : ∀ g ∈ d.soilGoals, s'.test g.goalFact = s.test g.goalFact)
    (hrg : ∀ g ∈ d.rockGoals, s'.test g.goalFact = s.test g.goalFact)
    (hig : ∀ g ∈ d.imageGoals, s'.test g.goalFact = s.test g.goalFact)
    (hsn : ∀ g ∈ d.soilGoals, needsSample s' g = needsSample s g)
    (hrn : ∀ g ∈ d.rockGoals, needsSample s' g = needsSample s g)
    (hi : ∀ g ∈ d.imageGoals, hasImage s' g = hasImage s g)
    (hcal : ∀ f ∈ d.calibratedFacts, s'.test f = s.test f)
    (hemp : ∀ f ∈ d.emptyFacts, s'.test f = s.test f) :
    Bc d s' = Bc d s := by
  have hcomm : communicate d s' = communicate d s := by
    unfold communicate
    rw [unmetSoil_congr hsg, unmetRock_congr hrg, unmetImage_congr hig]
  have hsam : samples d s' = samples d s := by
    unfold samples
    rw [soilToSample_congr hsg hsn, rockToSample_congr hrg hrn]
  show communicate d s' + samples d s' + images d s' + (images d s' - calibrated d s')
      + (samples d s' - emptyStores d s') = _
  rw [hcomm, hsam, images_congr hig hi]
  unfold calibrated emptyStores
  rw [countHolding_congr _ hcal, countHolding_congr _ hemp]
  rfl

/-! ### What each schema does

`Quiet` is the part eight of the nine schemas share: nothing the base count reads
outside the goal facts has moved, and no rover has moved.
-/

/-- Nothing moved but the goal facts. -/
structure Quiet (d : Data) (s s' : State) : Prop where
  needsSoil : ∀ g ∈ d.soilGoals, needsSample s' g = needsSample s g
  needsRock : ∀ g ∈ d.rockGoals, needsSample s' g = needsSample s g
  imageHeld : ∀ g ∈ d.imageGoals, hasImage s' g = hasImage s g
  calib : ∀ f ∈ d.calibratedFacts, s'.test f = s.test f
  emptyF : ∀ f ∈ d.emptyFacts, s'.test f = s.test f
  pos : ∀ r, roverFind d s' r = roverFind d s r
  occ : ∀ w, occupied d s' w = occupied d s w

/-- The goal facts, unchanged. -/
structure GoalsFixed (d : Data) (s s' : State) : Prop where
  soil : ∀ g ∈ d.soilGoals, s'.test g.goalFact = s.test g.goalFact
  rock : ∀ g ∈ d.rockGoals, s'.test g.goalFact = s.test g.goalFact
  image : ∀ g ∈ d.imageGoals, s'.test g.goalFact = s.test g.goalFact

theorem Quiet.soilSame {d : Data} {s s' : State} (h : Quiet d s s')
    (hg : ∀ g ∈ d.soilGoals, s'.test g.goalFact = s.test g.goalFact) :
    soilToSample d s' = soilToSample d s :=
  soilToSample_congr hg h.needsSoil

theorem Quiet.rockSame {d : Data} {s s' : State} (h : Quiet d s s')
    (hg : ∀ g ∈ d.rockGoals, s'.test g.goalFact = s.test g.goalFact) :
    rockToSample d s' = rockToSample d s :=
  rockToSample_congr hg h.needsRock

theorem Quiet.Rc_eq {d : Data} {s s' : State} (h : Quiet d s s')
    (hs : soilToSample d s' = soilToSample d s)
    (hr : rockToSample d s' = rockToSample d s) : Rc d s' = Rc d s :=
  Rc_congr hs hr h.pos h.occ

/-- `communicate_soil_data`: one soil goal is met, and its analysis was in hand. -/
structure CommSoilStep (d : Data) (s s' : State) (q : SampleGoal) : Prop where
  quiet : Quiet d s s'
  memQ : q ∈ d.soilGoals
  unmetQ : s.test q.goalFact = false
  metQ' : s'.test q.goalFact = true
  hasData : needsSample s q = false
  frameSoil : ∀ g ∈ d.soilGoals, g ≠ q → s'.test g.goalFact = s.test g.goalFact
  frameRock : ∀ g ∈ d.rockGoals, s'.test g.goalFact = s.test g.goalFact
  frameImage : ∀ g ∈ d.imageGoals, s'.test g.goalFact = s.test g.goalFact

/-- `communicate_rock_data`. -/
structure CommRockStep (d : Data) (s s' : State) (q : SampleGoal) : Prop where
  quiet : Quiet d s s'
  memQ : q ∈ d.rockGoals
  unmetQ : s.test q.goalFact = false
  metQ' : s'.test q.goalFact = true
  hasData : needsSample s q = false
  frameSoil : ∀ g ∈ d.soilGoals, s'.test g.goalFact = s.test g.goalFact
  frameRock : ∀ g ∈ d.rockGoals, g ≠ q → s'.test g.goalFact = s.test g.goalFact
  frameImage : ∀ g ∈ d.imageGoals, s'.test g.goalFact = s.test g.goalFact

/-- `communicate_image_data`: one image goal is met, and its picture was in hand. -/
structure CommImageStep (d : Data) (s s' : State) (q : ImageGoal) : Prop where
  quiet : Quiet d s s'
  memQ : q ∈ d.imageGoals
  unmetQ : s.test q.goalFact = false
  metQ' : s'.test q.goalFact = true
  hasPicture : hasImage s q = true
  frameSoil : ∀ g ∈ d.soilGoals, s'.test g.goalFact = s.test g.goalFact
  frameRock : ∀ g ∈ d.rockGoals, s'.test g.goalFact = s.test g.goalFact
  frameImage : ∀ g ∈ d.imageGoals, g ≠ q → s'.test g.goalFact = s.test g.goalFact

/--
`sample_soil`, `sample_rock`, `drop`, `calibrate` and `take_image`: the goals do
not move and no rover moves, so the navigation bound is unchanged.  What the base
count may lose is bounded by one, which is all consistency needs.
-/
structure ResourceStep (d : Data) (s s' : State) : Prop where
  goals : GoalsFixed d s s'
  /--
  The navigation bound never falls.

  This was four fields — the two sample sets and the two rover readings, each
  unchanged — and `sample_soil` breaks all of them: it supplies the analysis its
  goal was waiting for, so that goal leaves `soilToSample`.  What stays true, and
  what the consistency argument consumes, is only that `Rc` does not drop.  It
  does not, because the rover doing the sampling stands on the waypoint it
  samples: that waypoint is at distance zero, so it was contributing nothing to
  `travel`, and it is occupied, so it was contributing nothing to `arrivals`.
  -/
  RcLe : Rc d s ≤ Rc d s'
  /-- The base count never falls by more than one. -/
  baseDrop : Bc d s ≤ Bc d s' + 1

/-- `navigate`: one rover moves one edge; nothing else changes. -/
structure NavigateStep (d : Data) (s s' : State) (dest : Nat) : Prop where
  quiet' : ∀ g ∈ d.soilGoals, needsSample s' g = needsSample s g
  quietR : ∀ g ∈ d.rockGoals, needsSample s' g = needsSample s g
  imageHeld : ∀ g ∈ d.imageGoals, hasImage s' g = hasImage s g
  calib : ∀ f ∈ d.calibratedFacts, s'.test f = s.test f
  emptyF : ∀ f ∈ d.emptyFacts, s'.test f = s.test f
  goals : GoalsFixed d s s'
  /-- The only place a rover newly stands is where this one arrived. -/
  occNew : ∀ w, occupied d s' w = true → occupied d s w = true ∨ w = dest
  /-- One edge changes any rover's distance to any waypoint by at most one. -/
  reachStep : ∀ crew w, reach d s crew w ≤ 1 + reach d s' crew w

/-- One action of the domain. -/
inductive SchemaStep (d : Data) (s s' : State) : Prop
  | commSoil (q : SampleGoal) (h : CommSoilStep d s s' q)
  | commRock (q : SampleGoal) (h : CommRockStep d s s' q)
  | commImage (q : ImageGoal) (h : CommImageStep d s s' q)
  | resource (h : ResourceStep d s s')
  | navigate (dest : Nat) (h : NavigateStep d s s' dest)

/-! ### The counters, derived from the shapes -/

namespace CommSoilStep
variable {d : Data} {s s' : State} {q : SampleGoal}

theorem soilSame (h : CommSoilStep d s s' q) : soilToSample d s' = soilToSample d s :=
  Array.toList_inj.mp (by
    rw [soilToSample_toList, soilToSample_toList]
    refine List.filter_congr ?_
    intro g hgm
    have hm : g ∈ d.soilGoals := by simpa using hgm
    by_cases hne : g = q
    · subst hne; simp [h.quiet.needsSoil g hm, h.hasData]
    · simp [liveS, h.frameSoil g hm hne, h.quiet.needsSoil g hm])

theorem rockSame (h : CommSoilStep d s s' q) : rockToSample d s' = rockToSample d s :=
  h.quiet.rockSame h.frameRock

theorem Bc_drop (h : CommSoilStep d s s' q) (hnd : d.soilGoals.toList.Nodup) :
    Bc d s' + 1 = Bc d s := by
  have hcomm : communicate d s' + 1 = communicate d s := by
    unfold communicate
    have h1 : (unmetSoil d s').size + 1 = (unmetSoil d s).size :=
      unmet_size_drop d.soilGoals (·.goalFact) q h.memQ hnd h.unmetQ h.metQ' h.frameSoil
    rw [unmetRock_congr h.frameRock, unmetImage_congr h.frameImage]
    omega
  have hsam : samples d s' = samples d s := by
    unfold samples; rw [h.soilSame, h.rockSame]
  have himg : images d s' = images d s := images_congr h.frameImage h.quiet.imageHeld
  have hcal : calibrated d s' = calibrated d s := countHolding_congr _ h.quiet.calib
  have hemp : emptyStores d s' = emptyStores d s := countHolding_congr _ h.quiet.emptyF
  show communicate d s' + samples d s' + images d s' + (images d s' - calibrated d s')
      + (samples d s' - emptyStores d s') + 1 = _
  rw [hsam, himg, hcal, hemp]
  show _ = communicate d s + samples d s + images d s + (images d s - calibrated d s)
      + (samples d s - emptyStores d s)
  omega

theorem Rc_eq (h : CommSoilStep d s s' q) : Rc d s' = Rc d s :=
  h.quiet.Rc_eq h.soilSame h.rockSame

end CommSoilStep

namespace CommRockStep
variable {d : Data} {s s' : State} {q : SampleGoal}

theorem rockSame (h : CommRockStep d s s' q) : rockToSample d s' = rockToSample d s :=
  Array.toList_inj.mp (by
    rw [rockToSample_toList, rockToSample_toList]
    refine List.filter_congr ?_
    intro g hgm
    have hm : g ∈ d.rockGoals := by simpa using hgm
    by_cases hne : g = q
    · subst hne; simp [h.quiet.needsRock g hm, h.hasData]
    · simp [liveS, h.frameRock g hm hne, h.quiet.needsRock g hm])

theorem soilSame (h : CommRockStep d s s' q) : soilToSample d s' = soilToSample d s :=
  h.quiet.soilSame h.frameSoil

theorem Bc_drop (h : CommRockStep d s s' q) (hnd : d.rockGoals.toList.Nodup) :
    Bc d s' + 1 = Bc d s := by
  have hcomm : communicate d s' + 1 = communicate d s := by
    unfold communicate
    have h1 : (unmetRock d s').size + 1 = (unmetRock d s).size :=
      unmet_size_drop d.rockGoals (·.goalFact) q h.memQ hnd h.unmetQ h.metQ' h.frameRock
    rw [unmetSoil_congr h.frameSoil, unmetImage_congr h.frameImage]
    omega
  have hsam : samples d s' = samples d s := by
    unfold samples; rw [h.soilSame, h.rockSame]
  have himg : images d s' = images d s := images_congr h.frameImage h.quiet.imageHeld
  have hcal : calibrated d s' = calibrated d s := countHolding_congr _ h.quiet.calib
  have hemp : emptyStores d s' = emptyStores d s := countHolding_congr _ h.quiet.emptyF
  show communicate d s' + samples d s' + images d s' + (images d s' - calibrated d s')
      + (samples d s' - emptyStores d s') + 1 = _
  rw [hsam, himg, hcal, hemp]
  show _ = communicate d s + samples d s + images d s + (images d s - calibrated d s)
      + (samples d s - emptyStores d s)
  omega

theorem Rc_eq (h : CommRockStep d s s' q) : Rc d s' = Rc d s :=
  h.quiet.Rc_eq h.soilSame h.rockSame

end CommRockStep

namespace CommImageStep
variable {d : Data} {s s' : State} {q : ImageGoal}

theorem images_eq (h : CommImageStep d s s' q) : images d s' = images d s := by
  unfold images
  rw [size_filter_toList, size_filter_toList, images_inner, images_inner]
  refine length_filter_congr _ _ _ ?_
  intro g hgm
  have hm : g ∈ d.imageGoals := by simpa using hgm
  by_cases hne : g = q
  · subst hne
    have h2 : (g.haveFacts.any fun f => s.test f) = true := by
      simpa [hasImage] using h.hasPicture
    have h1 : (g.haveFacts.any fun f => s'.test f) = true := by
      have hq := h.quiet.imageHeld g hm
      simp only [hasImage] at hq
      rw [hq]; exact h2
    simp [h1, h2]
  · have := h.quiet.imageHeld g hm
    simp only [hasImage] at this
    simp [liveI, this, h.frameImage g hm hne]

theorem Bc_drop (h : CommImageStep d s s' q) (hnd : d.imageGoals.toList.Nodup) :
    Bc d s' + 1 = Bc d s := by
  have hcomm : communicate d s' + 1 = communicate d s := by
    unfold communicate
    have h1 : (unmetImage d s').size + 1 = (unmetImage d s).size :=
      unmet_size_drop d.imageGoals (·.goalFact) q h.memQ hnd h.unmetQ h.metQ' h.frameImage
    rw [unmetSoil_congr h.frameSoil, unmetRock_congr h.frameRock]
    omega
  have hsoil := h.quiet.soilSame h.frameSoil
  have hrock := h.quiet.rockSame h.frameRock
  have hsam : samples d s' = samples d s := by unfold samples; rw [hsoil, hrock]
  have himg := h.images_eq
  have hcal : calibrated d s' = calibrated d s := countHolding_congr _ h.quiet.calib
  have hemp : emptyStores d s' = emptyStores d s := countHolding_congr _ h.quiet.emptyF
  show communicate d s' + samples d s' + images d s' + (images d s' - calibrated d s')
      + (samples d s' - emptyStores d s') + 1 = _
  rw [hsam, himg, hcal, hemp]
  show _ = communicate d s + samples d s + images d s + (images d s - calibrated d s)
      + (samples d s - emptyStores d s)
  omega

theorem Rc_eq (h : CommImageStep d s s' q) : Rc d s' = Rc d s :=
  h.quiet.Rc_eq (h.quiet.soilSame h.frameSoil) (h.quiet.rockSame h.frameRock)

end CommImageStep

namespace NavigateStep
variable {d : Data} {s s' : State} {dest : Nat}

theorem Bc_eq (h : NavigateStep d s s' dest) : Bc d s' = Bc d s :=
  Bc_congr h.goals.soil h.goals.rock h.goals.image h.quiet' h.quietR h.imageHeld
    h.calib h.emptyF

theorem Rc_le (h : NavigateStep d s s' dest) : Rc d s ≤ Rc d s' + 1 := by
  have hsoil : soilToSample d s' = soilToSample d s :=
    soilToSample_congr h.goals.soil h.quiet'
  have hrock : rockToSample d s' = rockToSample d s :=
    rockToSample_congr h.goals.rock h.quietR
  have htravel : travel d s ≤ travel d s' + 1 := by
    unfold travel
    rw [hsoil, hrock]
    have k1 : (soilToSample d s).toList.foldl
          (fun acc g => max acc (reach d s d.soilRovers g.waypoint)) 0
        ≤ 1 + (soilToSample d s).toList.foldl
          (fun acc g => max acc (reach d s' d.soilRovers g.waypoint)) 0 :=
      foldl_max_le_succ _ _ _ (fun g _ => h.reachStep _ _) 0 0 (by omega)
    have k2 : (rockToSample d s).toList.foldl
          (fun acc g => max acc (reach d s d.rockRovers g.waypoint)) 0
        ≤ 1 + (rockToSample d s).toList.foldl
          (fun acc g => max acc (reach d s' d.rockRovers g.waypoint)) 0 :=
      foldl_max_le_succ _ _ _ (fun g _ => h.reachStep _ _) 0 0 (by omega)
    simp only [← Array.foldl_toList]
    omega
  have harr : arrivals d s ≤ arrivals d s' + 1 := by
    unfold arrivals requiredWaypoints
    rw [hsoil, hrock]
    refine length_le_succ_of_subset _ _ dest ((distinct_nodup _).filter _) ?_
    intro x hx
    rw [List.mem_filter] at hx
    obtain ⟨hxm, hxo⟩ := hx
    by_cases hxd : x = dest
    · exact Or.inr hxd
    · refine Or.inl ?_
      rw [List.mem_filter]
      refine ⟨hxm, ?_⟩
      simp only [Bool.not_eq_true'] at hxo ⊢
      by_contra hcon
      have : occupied d s' x = true := by simpa using hcon
      rcases h.occNew x this with hc | hc
      · rw [hc] at hxo; exact Bool.noConfusion hxo
      · exact hxd hc
  show max (travel d s) (arrivals d s) ≤ max (travel d s') (arrivals d s') + 1
  omega

end NavigateStep

/-! ### The consistency step, with nothing about the counters assumed -/

theorem value_step_of_schema (d : Data) (s s' : State)
    (hnds : d.soilGoals.toList.Nodup) (hndr : d.rockGoals.toList.Nodup)
    (hndi : d.imageGoals.toList.Nodup)
    (he : SchemaStep d s s') (cost : Nat) (hcost : 1 ≤ cost) :
    value d s ≤ cost + value d s' := by
  show Bc d s + Rc d s ≤ cost + (Bc d s' + Rc d s')
  cases he with
  | commSoil q h =>
      have h1 := h.Bc_drop hnds
      have h2 := h.Rc_eq
      omega
  | commRock q h =>
      have h1 := h.Bc_drop hndr
      have h2 := h.Rc_eq
      omega
  | commImage q h =>
      have h1 := h.Bc_drop hndi
      have h2 := h.Rc_eq
      omega
  | resource h =>
      have h1 := h.baseDrop
      have h2 := h.RcLe
      omega
  | navigate dest h =>
      have h1 := h.Bc_eq
      have h2 := h.Rc_le
      omega

/-- Zero at every goal state, assuming only what the schemas do. -/
theorem improved_goalAware_of_schema (t : Task)
    (c1 : ∀ g ∈ (compile t).soilGoals, g.goalFact ∈ t.goal)
    (c2 : ∀ g ∈ (compile t).rockGoals, g.goalFact ∈ t.goal)
    (c3 : ∀ g ∈ (compile t).imageGoals, g.goalFact ∈ t.goal) :
    t.GoalAware (improved t).eval := improved_goalAware t c1 c2 c3

/-- And never falls by more than one action costs. -/
theorem improved_consistent_of_schema (t : Task)
    (hnds : (compile t).soilGoals.toList.Nodup) (hndr : (compile t).rockGoals.toList.Nodup)
    (hndi : (compile t).imageGoals.toList.Nodup)
    (hstep : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      SchemaStep (compile t) s (op.apply s))
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost) :
    t.Consistent (improved t).eval :=
  t.consistent_of_ops _ fun op hop s hs happ =>
    value_step_of_schema _ s _ hnds hndr hndi (hstep op hop s hs happ) op.cost (hcost op hop)

/-- Never overestimates, assuming only that every operator is one of the schemas. -/
theorem improved_admissible_of_schema (t : Task)
    (c1 : ∀ g ∈ (compile t).soilGoals, g.goalFact ∈ t.goal)
    (c2 : ∀ g ∈ (compile t).rockGoals, g.goalFact ∈ t.goal)
    (c3 : ∀ g ∈ (compile t).imageGoals, g.goalFact ∈ t.goal)
    (hnds : (compile t).soilGoals.toList.Nodup) (hndr : (compile t).rockGoals.toList.Nodup)
    (hndi : (compile t).imageGoals.toList.Nodup)
    (hstep : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      SchemaStep (compile t) s (op.apply s))
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost) :
    t.Admissible (improved t).eval :=
  t.admissible _ (improved_goalAware_of_schema t c1 c2 c3)
    (improved_consistent_of_schema t hnds hndr hndi hstep hcost)

/-! ### Relative to an invariant

`NavigateStep.reachStep` is not a property of every well-formed state.  Take a
state where a rover has two `at` facts true at once — well formed, but not
reachable — say `at(x, a)` and `at(x, b)`, with `a` listed first in `x`'s table.
Then `roverFind` reports `a`.  A `navigate(x, a, z)` deletes `at(x, a)`, so
afterwards `roverFind` reports `b`, and the step compares the distance from `a`
with the distance from `b`.  Those two can be arbitrarily far apart, so
`reach s ≤ 1 + reach s'` fails.

So the schema obligation can only be discharged where an invariant holds, and
these say so.  Goal awareness needs no invariant and keeps its plain form.
-/

theorem improved_consistentOn_of_schema (t : Task) (Q : State → Prop)
    (hnds : (compile t).soilGoals.toList.Nodup) (hndr : (compile t).rockGoals.toList.Nodup)
    (hndi : (compile t).imageGoals.toList.Nodup)
    (hstep : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → Q s → op.applicable s = true →
      SchemaStep (compile t) s (op.apply s))
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost) :
    t.ConsistentOn Q (improved t).eval :=
  t.consistentOn_of_ops _ _ fun op hop s hs hq happ =>
    value_step_of_schema _ s _ hnds hndr hndi (hstep op hop s hs hq happ) op.cost
      (hcost op hop)

/-- **Never overestimates**, on the states the invariant admits. -/
theorem improved_admissibleOn_of_schema (t : Task) (Q : State → Prop)
    (hQ : ∀ s i s', State.WF t.numFacts s → Q s → t.step s i s' → Q s')
    (c1 : ∀ g ∈ (compile t).soilGoals, g.goalFact ∈ t.goal)
    (c2 : ∀ g ∈ (compile t).rockGoals, g.goalFact ∈ t.goal)
    (c3 : ∀ g ∈ (compile t).imageGoals, g.goalFact ∈ t.goal)
    (hnds : (compile t).soilGoals.toList.Nodup) (hndr : (compile t).rockGoals.toList.Nodup)
    (hndi : (compile t).imageGoals.toList.Nodup)
    (hstep : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → Q s → op.applicable s = true →
      SchemaStep (compile t) s (op.apply s))
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost) :
    t.AdmissibleOn Q (improved t).eval :=
  t.admissibleOn _ _ hQ
    (fun s hs hgoal => improved_goalAware_of_schema t c1 c2 c3 s hs.1 hgoal)
    (improved_consistentOn_of_schema t Q hnds hndr hndi hstep hcost)

end Planner.ExampleHeuristics.Rovers

/- -------------------------------------------------------------------------- -/
/-
Which domain a Rovers task came from.

The equation on `actions` fixes the nine schemas exactly as the parser produces
them from `benchmarks/ipc2023-learning/training/rovers/domain.pddl`.  The rest of
the file exposes what each instance reads, adds and deletes, so that a heuristic
proof can reason about one lifted transition without mentioning grounding or
fact numbers.

Note which predicates move.  `at` moves only under `navigate`; `empty` and
`full` only under the two samplers and `drop`; `calibrated` is added by
`calibrate` and deleted by `take_image`; the three `communicated_*` families are
only ever added.  Everything else — `can_traverse`, `visible`, `visible_from`,
`store_of`, `on_board`, `supports`, `calibration_target`, `at_lander` and the
three `equipped_for_*` — is static.
-/

namespace Planner.Lifted.Rovers

open Planner Planner.Pddl

/-! ### The domain's atoms -/

def at_ (r w : Name) : GroundAtom := { pred := "at", args := [r, w] }
def atSoilSample (w : Name) : GroundAtom := { pred := "at_soil_sample", args := [w] }
def atRockSample (w : Name) : GroundAtom := { pred := "at_rock_sample", args := [w] }
def emptyS (s : Name) : GroundAtom := { pred := "empty", args := [s] }
def fullS (s : Name) : GroundAtom := { pred := "full", args := [s] }
def haveSoil (r w : Name) : GroundAtom := { pred := "have_soil_analysis", args := [r, w] }
def haveRock (r w : Name) : GroundAtom := { pred := "have_rock_analysis", args := [r, w] }
def haveImage (r o m : Name) : GroundAtom := { pred := "have_image", args := [r, o, m] }
def calibrated (c r : Name) : GroundAtom := { pred := "calibrated", args := [c, r] }
def commSoil (w : Name) : GroundAtom := { pred := "communicated_soil_data", args := [w] }
def commRock (w : Name) : GroundAtom := { pred := "communicated_rock_data", args := [w] }
def commImage (o m : Name) : GroundAtom :=
  { pred := "communicated_image_data", args := [o, m] }

/-! ### The schemas, as the parser produces them -/

abbrev roverP (n : Name) : TypedName := { name := n, type := "rover" }
abbrev waypointP (n : Name) : TypedName := { name := n, type := "waypoint" }
abbrev storeP (n : Name) : TypedName := { name := n, type := "store" }
abbrev cameraP (n : Name) : TypedName := { name := n, type := "camera" }
abbrev modeP (n : Name) : TypedName := { name := n, type := "mode" }
abbrev landerP (n : Name) : TypedName := { name := n, type := "lander" }
abbrev objectiveP (n : Name) : TypedName := { name := n, type := "objective" }

abbrev atV (r w : Name) : Atom := { pred := "at", args := [.var r, .var w] }
abbrev atLanderV (l w : Name) : Atom := { pred := "at_lander", args := [.var l, .var w] }
abbrev canTraverseV (r x y : Name) : Atom :=
  { pred := "can_traverse", args := [.var r, .var x, .var y] }
abbrev visibleV (x y : Name) : Atom := { pred := "visible", args := [.var x, .var y] }
abbrev visibleFromV (o w : Name) : Atom :=
  { pred := "visible_from", args := [.var o, .var w] }
abbrev atSoilSampleV (w : Name) : Atom := { pred := "at_soil_sample", args := [.var w] }
abbrev atRockSampleV (w : Name) : Atom := { pred := "at_rock_sample", args := [.var w] }
abbrev emptyV (s : Name) : Atom := { pred := "empty", args := [.var s] }
abbrev fullV (s : Name) : Atom := { pred := "full", args := [.var s] }
abbrev storeOfV (s r : Name) : Atom := { pred := "store_of", args := [.var s, .var r] }
abbrev equipSoilV (r : Name) : Atom :=
  { pred := "equipped_for_soil_analysis", args := [.var r] }
abbrev equipRockV (r : Name) : Atom :=
  { pred := "equipped_for_rock_analysis", args := [.var r] }
abbrev equipImagingV (r : Name) : Atom :=
  { pred := "equipped_for_imaging", args := [.var r] }
abbrev haveSoilV (r w : Name) : Atom :=
  { pred := "have_soil_analysis", args := [.var r, .var w] }
abbrev haveRockV (r w : Name) : Atom :=
  { pred := "have_rock_analysis", args := [.var r, .var w] }
abbrev haveImageV (r o m : Name) : Atom :=
  { pred := "have_image", args := [.var r, .var o, .var m] }
abbrev calibratedV (c r : Name) : Atom := { pred := "calibrated", args := [.var c, .var r] }
abbrev calibTargetV (i o : Name) : Atom :=
  { pred := "calibration_target", args := [.var i, .var o] }
abbrev onBoardV (i r : Name) : Atom := { pred := "on_board", args := [.var i, .var r] }
abbrev supportsV (i m : Name) : Atom := { pred := "supports", args := [.var i, .var m] }
abbrev commSoilV (w : Name) : Atom :=
  { pred := "communicated_soil_data", args := [.var w] }
abbrev commRockV (w : Name) : Atom :=
  { pred := "communicated_rock_data", args := [.var w] }
abbrev commImageV (o m : Name) : Atom :=
  { pred := "communicated_image_data", args := [.var o, .var m] }

abbrev navigateA : Action := Planner.GeneratedDomains.Rovers.action0
abbrev sampleSoilA : Action := Planner.GeneratedDomains.Rovers.action1
abbrev sampleRockA : Action := Planner.GeneratedDomains.Rovers.action2
abbrev dropA : Action := Planner.GeneratedDomains.Rovers.action3
abbrev calibrateA : Action := Planner.GeneratedDomains.Rovers.action4
abbrev takeImageA : Action := Planner.GeneratedDomains.Rovers.action5
abbrev commSoilA : Action := Planner.GeneratedDomains.Rovers.action6
abbrev commRockA : Action := Planner.GeneratedDomains.Rovers.action7
abbrev commImageA : Action := Planner.GeneratedDomains.Rovers.action8

/-- The parsed domain is Rovers. -/
abbrev RoversDomain (d : Domain) : Prop :=
  d.actions = Planner.GeneratedDomains.Rovers.actions

/-! ### Every predicate the value reads is dynamic -/

theorem at_dynamic {d : Domain} (hd : RoversDomain d) :
    (staticPredicates d).contains "at" = false :=
  not_static_of_mem_add (a := navigateA) (by rw [hd]; simp) (y := atV "?x" "?z")
    (by simp [navigateA])

theorem full_dynamic {d : Domain} (hd : RoversDomain d) :
    (staticPredicates d).contains "full" = false :=
  not_static_of_mem_add (a := sampleSoilA) (by rw [hd]; simp) (y := fullV "?s")
    (by simp [sampleSoilA])

theorem empty_dynamic {d : Domain} (hd : RoversDomain d) :
    (staticPredicates d).contains "empty" = false :=
  not_static_of_mem_add (a := dropA) (by rw [hd]; simp) (y := emptyV "?y")
    (by simp [dropA])

theorem haveSoil_dynamic {d : Domain} (hd : RoversDomain d) :
    (staticPredicates d).contains "have_soil_analysis" = false :=
  not_static_of_mem_add (a := sampleSoilA) (by rw [hd]; simp)
    (y := haveSoilV "?x" "?p") (by simp [sampleSoilA])

theorem haveRock_dynamic {d : Domain} (hd : RoversDomain d) :
    (staticPredicates d).contains "have_rock_analysis" = false :=
  not_static_of_mem_add (a := sampleRockA) (by rw [hd]; simp)
    (y := haveRockV "?x" "?p") (by simp [sampleRockA])

theorem haveImage_dynamic {d : Domain} (hd : RoversDomain d) :
    (staticPredicates d).contains "have_image" = false :=
  not_static_of_mem_add (a := takeImageA) (by rw [hd]; simp)
    (y := haveImageV "?r" "?o" "?m") (by simp [takeImageA])

theorem calibrated_dynamic {d : Domain} (hd : RoversDomain d) :
    (staticPredicates d).contains "calibrated" = false :=
  not_static_of_mem_add (a := calibrateA) (by rw [hd]; simp)
    (y := calibratedV "?i" "?r") (by simp [calibrateA])

theorem atSoilSample_dynamic {d : Domain} (hd : RoversDomain d) :
    (staticPredicates d).contains "at_soil_sample" = false :=
  not_static_of_mem_del (a := sampleSoilA) (by rw [hd]; simp)
    (y := atSoilSampleV "?p") (by simp [sampleSoilA])

theorem atRockSample_dynamic {d : Domain} (hd : RoversDomain d) :
    (staticPredicates d).contains "at_rock_sample" = false :=
  not_static_of_mem_del (a := sampleRockA) (by rw [hd]; simp)
    (y := atRockSampleV "?p") (by simp [sampleRockA])

theorem commSoil_dynamic {d : Domain} (hd : RoversDomain d) :
    (staticPredicates d).contains "communicated_soil_data" = false :=
  not_static_of_mem_add (a := commSoilA) (by rw [hd]; simp) (y := commSoilV "?p")
    (by simp [commSoilA])

theorem commRock_dynamic {d : Domain} (hd : RoversDomain d) :
    (staticPredicates d).contains "communicated_rock_data" = false :=
  not_static_of_mem_add (a := commRockA) (by rw [hd]; simp) (y := commRockV "?p")
    (by simp [commRockA])

theorem commImage_dynamic {d : Domain} (hd : RoversDomain d) :
    (staticPredicates d).contains "communicated_image_data" = false :=
  not_static_of_mem_add (a := commImageA) (by rw [hd]; simp)
    (y := commImageV "?o" "?m") (by simp [commImageA])

/-! ### Instances -/

theorem instance_shape {d : Domain} {objects : List TypedName} (hd : RoversDomain d)
    (i : Instance d objects) :
    (∃ x y z, i.schema = navigateA ∧ i.args = [x, y, z]) ∨
    (∃ x s p, i.schema = sampleSoilA ∧ i.args = [x, s, p]) ∨
    (∃ x s p, i.schema = sampleRockA ∧ i.args = [x, s, p]) ∨
    (∃ x y, i.schema = dropA ∧ i.args = [x, y]) ∨
    (∃ r c t w, i.schema = calibrateA ∧ i.args = [r, c, t, w]) ∨
    (∃ r p o c m, i.schema = takeImageA ∧ i.args = [r, p, o, c, m]) ∨
    (∃ r l p x y, i.schema = commSoilA ∧ i.args = [r, l, p, x, y]) ∨
    (∃ r l p x y, i.schema = commRockA ∧ i.args = [r, l, p, x, y]) ∨
    (∃ r l o m x y, i.schema = commImageA ∧ i.args = [r, l, o, m, x, y]) := by
  have hmem : i.schema ∈ [navigateA, sampleSoilA, sampleRockA, dropA, calibrateA,
      takeImageA, commSoilA, commRockA, commImageA] := by
    have hm : i.schema ∈ d.actions := i.mem
    rw [hd] at hm
    exact hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with hs | hs | hs | hs | hs | hs | hs | hs | hs
  · obtain ⟨x, y, z, ha, -, -, -⟩ := i.args_three (by rw [hs])
    exact Or.inl ⟨x, y, z, hs, ha⟩
  · obtain ⟨x, s, p, ha, -, -, -⟩ := i.args_three (by rw [hs])
    exact Or.inr (Or.inl ⟨x, s, p, hs, ha⟩)
  · obtain ⟨x, s, p, ha, -, -, -⟩ := i.args_three (by rw [hs])
    exact Or.inr (Or.inr (Or.inl ⟨x, s, p, hs, ha⟩))
  · obtain ⟨x, y, ha, -, -⟩ := i.args_two (by rw [hs])
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨x, y, hs, ha⟩)))
  · obtain ⟨r, c, t, w, ha, -, -, -, -⟩ := i.args_four (by rw [hs])
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, c, t, w, hs, ha⟩))))
  · obtain ⟨r, p, o, c, m, ha, -, -, -, -, -⟩ := i.args_five (by rw [hs])
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, p, o, c, m, hs, ha⟩)))))
  · obtain ⟨r, l, p, x, y, ha, -, -, -, -, -⟩ := i.args_five (by rw [hs])
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨r, l, p, x, y, hs, ha⟩))))))
  · obtain ⟨r, l, p, x, y, ha, -, -, -, -, -⟩ := i.args_five (by rw [hs])
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨r, l, p, x, y, hs, ha⟩)))))))
  · obtain ⟨r, l, o, m, x, y, ha, -, -, -, -, -, -⟩ := i.args_six (by rw [hs])
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr ⟨r, l, o, m, x, y, hs, ha⟩)))))))

/-! ### What each instance reads, adds and deletes -/

theorem navigate_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {x y z : Name} (hs : i.schema = navigateA) (ha : i.args = [x, y, z]) :
    at_ x y ∈ i.pre ∧ i.add = [at_ x z] ∧ i.del = [at_ x y] := by
  have hp : i.pre = [{ pred := "can_traverse", args := [x, y, z] }, at_ x y,
      { pred := "visible", args := [y, z] }] := by rw [i.pre_eq, hs, ha]; rfl
  have hadd : i.add = [at_ x z] := by rw [i.add_eq, hs, ha]; rfl
  have hdel : i.del = [at_ x y] := by rw [i.del_eq, hs, ha]; rfl
  simp [hp, hadd, hdel]

theorem sampleSoil_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {x s p : Name} (hs : i.schema = sampleSoilA) (ha : i.args = [x, s, p]) :
    at_ x p ∈ i.pre ∧ atSoilSample p ∈ i.pre ∧ emptyS s ∈ i.pre ∧
      i.add = [fullS s, haveSoil x p] ∧ i.del = [emptyS s, atSoilSample p] := by
  have hp : i.pre = [at_ x p, atSoilSample p,
      { pred := "equipped_for_soil_analysis", args := [x] },
      { pred := "store_of", args := [s, x] }, emptyS s] := by
    rw [i.pre_eq, hs, ha]; rfl
  have hadd : i.add = [fullS s, haveSoil x p] := by rw [i.add_eq, hs, ha]; rfl
  have hdel : i.del = [emptyS s, atSoilSample p] := by rw [i.del_eq, hs, ha]; rfl
  simp [hp, hadd, hdel]

theorem sampleRock_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {x s p : Name} (hs : i.schema = sampleRockA) (ha : i.args = [x, s, p]) :
    at_ x p ∈ i.pre ∧ atRockSample p ∈ i.pre ∧ emptyS s ∈ i.pre ∧
      i.add = [fullS s, haveRock x p] ∧ i.del = [emptyS s, atRockSample p] := by
  have hp : i.pre = [at_ x p, atRockSample p,
      { pred := "equipped_for_rock_analysis", args := [x] },
      { pred := "store_of", args := [s, x] }, emptyS s] := by
    rw [i.pre_eq, hs, ha]; rfl
  have hadd : i.add = [fullS s, haveRock x p] := by rw [i.add_eq, hs, ha]; rfl
  have hdel : i.del = [emptyS s, atRockSample p] := by rw [i.del_eq, hs, ha]; rfl
  simp [hp, hadd, hdel]

theorem drop_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {x y : Name} (hs : i.schema = dropA) (ha : i.args = [x, y]) :
    fullS y ∈ i.pre ∧ i.add = [emptyS y] ∧ i.del = [fullS y] := by
  have hp : i.pre = [{ pred := "store_of", args := [y, x] }, fullS y] := by
    rw [i.pre_eq, hs, ha]; rfl
  have hadd : i.add = [emptyS y] := by rw [i.add_eq, hs, ha]; rfl
  have hdel : i.del = [fullS y] := by rw [i.del_eq, hs, ha]; rfl
  simp [hp, hadd, hdel]

theorem calibrate_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {r c t w : Name} (hs : i.schema = calibrateA) (ha : i.args = [r, c, t, w]) :
    at_ r w ∈ i.pre ∧ i.add = [calibrated c r] ∧ i.del = [] := by
  have hp : i.pre = [{ pred := "equipped_for_imaging", args := [r] },
      { pred := "calibration_target", args := [c, t] }, at_ r w,
      { pred := "visible_from", args := [t, w] },
      { pred := "on_board", args := [c, r] }] := by rw [i.pre_eq, hs, ha]; rfl
  have hadd : i.add = [calibrated c r] := by rw [i.add_eq, hs, ha]; rfl
  have hdel : i.del = [] := by rw [i.del_eq, hs, ha]; rfl
  simp [hp, hadd, hdel]

theorem takeImage_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {r p o c m : Name} (hs : i.schema = takeImageA) (ha : i.args = [r, p, o, c, m]) :
    calibrated c r ∈ i.pre ∧ at_ r p ∈ i.pre ∧
      i.add = [haveImage r o m] ∧ i.del = [calibrated c r] := by
  have hp : i.pre = [calibrated c r, { pred := "on_board", args := [c, r] },
      { pred := "equipped_for_imaging", args := [r] },
      { pred := "supports", args := [c, m] },
      { pred := "visible_from", args := [o, p] }, at_ r p] := by
    rw [i.pre_eq, hs, ha]; rfl
  have hadd : i.add = [haveImage r o m] := by rw [i.add_eq, hs, ha]; rfl
  have hdel : i.del = [calibrated c r] := by rw [i.del_eq, hs, ha]; rfl
  simp [hp, hadd, hdel]

theorem commSoil_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {r l p x y : Name} (hs : i.schema = commSoilA) (ha : i.args = [r, l, p, x, y]) :
    at_ r x ∈ i.pre ∧ haveSoil r p ∈ i.pre ∧ i.add = [commSoil p] ∧ i.del = [] := by
  have hp : i.pre = [at_ r x, { pred := "at_lander", args := [l, y] }, haveSoil r p,
      { pred := "visible", args := [x, y] }] := by rw [i.pre_eq, hs, ha]; rfl
  have hadd : i.add = [commSoil p] := by rw [i.add_eq, hs, ha]; rfl
  have hdel : i.del = [] := by rw [i.del_eq, hs, ha]; rfl
  simp [hp, hadd, hdel]

theorem commRock_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {r l p x y : Name} (hs : i.schema = commRockA) (ha : i.args = [r, l, p, x, y]) :
    at_ r x ∈ i.pre ∧ haveRock r p ∈ i.pre ∧ i.add = [commRock p] ∧ i.del = [] := by
  have hp : i.pre = [at_ r x, { pred := "at_lander", args := [l, y] }, haveRock r p,
      { pred := "visible", args := [x, y] }] := by rw [i.pre_eq, hs, ha]; rfl
  have hadd : i.add = [commRock p] := by rw [i.add_eq, hs, ha]; rfl
  have hdel : i.del = [] := by rw [i.del_eq, hs, ha]; rfl
  simp [hp, hadd, hdel]

theorem commImage_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {r l o m x y : Name} (hs : i.schema = commImageA)
    (ha : i.args = [r, l, o, m, x, y]) :
    at_ r x ∈ i.pre ∧ haveImage r o m ∈ i.pre ∧
      i.add = [commImage o m] ∧ i.del = [] := by
  have hp : i.pre = [at_ r x, { pred := "at_lander", args := [l, y] },
      haveImage r o m, { pred := "visible", args := [x, y] }] := by
    rw [i.pre_eq, hs, ha]; rfl
  have hadd : i.add = [commImage o m] := by rw [i.add_eq, hs, ha]; rfl
  have hdel : i.del = [] := by rw [i.del_eq, hs, ha]; rfl
  simp [hp, hadd, hdel]

end Planner.Lifted.Rovers

/- -------------------------------------------------------------------------- -/
/-
What a Rovers task must satisfy, and the parts of the step proof that follow
from the schemas alone.

Rovers is the first domain here with a large static vocabulary: `can_traverse`,
`visible`, `visible_from`, `store_of`, `on_board`, `supports`,
`calibration_target`, `at_lander` and the three `equipped_for_*` never move.  So
`pre_dynamic` is *false* for this domain — unlike Blocks World, where every
predicate is dynamic — and the step proof has to say which preconditions it is
reading, rather than reading them all.
-/

namespace Planner.Lifted.Rovers

open Planner Planner.Pddl

variable {d : Domain} {p : Problem}

/-- The four schemas whose adds a step proof reads: a `navigate`'s new position,
and the goal atom each `communicate` asserts.  The other five never have an add
read. -/
def ReadsAdds (a : Action) : Prop :=
  a = navigateA ∨ a = commSoilA ∨ a = commRockA ∨ a = commImageA

/--
Add-completeness for one operator, restricted to those four schemas.

Unrestricted it is **false** here, in the way sokoban's was.  A `sample_soil` at
a waypoint no goal asks about is still kept — it deletes the store's `empty`,
which is relevant — but nothing reads its `have_soil_analysis`, so that atom is
irrelevant and the analysis trims the add.  On `rovers/easy-p01` five kept
operators lose an add exactly so, and 147 of the 189 shipped tasks have a soil
sample at a waypoint no goal mentions.  The four schemas above are the only ones
whose adds any proof reads, and for those the add does survive.
-/
def AddsFor (d : Domain) (p : Problem) (o : AtomOp) (hf : OpFacts d p o) : Prop :=
  ReadsAdds hf.inst.schema → ∀ y ∈ hf.inst.schema.add,
    instAtom hf.inst.schema.params hf.inst.args y ∉ o.pre →
    instAtom hf.inst.schema.params hf.inst.args y ∈ o.add

/-- The add-completeness the Rovers proofs need, after relevance pruning or
without it.  Proved in `Proofs/Lifted/RoversRelevance.lean`. -/
def AddsKept (d : Domain) (p : Problem) (rel : Bool) : Prop :=
  ∀ o ∈ groundedOps d p rel, ∃ hf : OpFacts d p o, AddsFor d p o hf

/-- The finite check that no rover has two initial `at` facts. -/
def initInvCheck (p : Problem) : Bool :=
  (initPairs p "at").all fun x =>
    (initPairs p "at").all fun y => !(x.1 == y.1) || (x.2 == y.2)

/-- What a Rovers task must satisfy for the proof to apply. -/
structure Pinned (d : Domain) (p : Problem) : Prop where
  /-- The nine schemas are the ones the parser produces. -/
  domain : RoversDomain d
  /-- Every parameter type of the domain is declared. -/
  roverType : "rover" ∈ d.typeNames
  waypointType : "waypoint" ∈ d.typeNames
  storeType : "store" ∈ d.typeNames
  cameraType : "camera" ∈ d.typeNames
  modeType : "mode" ∈ d.typeNames
  landerType : "lander" ∈ d.typeNames
  objectiveType : "objective" ∈ d.typeNames
  /-- Rover and waypoint parameters index exactly these two object tables. -/
  roverTypeExact : ∀ o ∈ allObjects d p,
    d.isSubtype o.type "rover" = true → o.type = "rover"
  waypointTypeExact : ∀ o ∈ allObjects d p,
    d.isSubtype o.type "waypoint" = true → o.type = "waypoint"
  /-- The pair passed the planner's own validators.  `namesNodup` below is read
  off it rather than assumed: validation checks the objects for duplicates, the
  constants for duplicates, and rejects an object that shadows a constant. -/
  validated : Validated d p
  /-- The goal names each atom once. -/
  goalNodup : p.goal.Nodup
  /-- `can_traverse` never moves. -/
  canTraverseStatic : (staticPredicates d).contains "can_traverse" = true
  visibleStatic : (staticPredicates d).contains "visible" = true
  soilEquippedStatic :
    (staticPredicates d).contains "equipped_for_soil_analysis" = true
  rockEquippedStatic :
    (staticPredicates d).contains "equipped_for_rock_analysis" = true
  /-- Goals mention no static predicate, as in the shipped Rovers tasks. -/
  goalDynamic : ∀ a ∈ p.goal, (staticPredicates d).contains a.pred = false
  /-- The initial state has at most one position per rover. -/
  initCheck : initInvCheck p = true
  /--
  Every traversal reverses: if a rover can drive from `y` to `z`, it can drive
  back.

  This is what makes a rover's destination relevant, and so what makes the
  analysis keep the `at` add of a `navigate` it keeps.  An atom is relevant only
  if some operator that writes into the relevant set reads it, and the operator
  that reads `at ?x ?z` is the drive back out of `?z`.

  It holds of every Rovers task in the benchmark set: `can_traverse` and
  `visible` are both emitted symmetrically.
  -/
  traverseReverses : ∀ x y z : Pddl.Name,
    ({ pred := "can_traverse", args := [x, y, z] } : GroundAtom) ∈ p.init →
    ({ pred := "visible", args := [y, z] } : GroundAtom) ∈ p.init →
    ({ pred := "can_traverse", args := [x, z, y] } : GroundAtom) ∈ p.init ∧
      ({ pred := "visible", args := [z, y] } : GroundAtom) ∈ p.init
  /--
  No waypoint is traversable to itself.

  Without this a `navigate` could be a self-loop, adding and deleting the same
  `at` atom.  The grounder handles that correctly — it drops a delete whose atom
  the schema also adds — but `OpFacts` does not expose the fact, so the proof
  cannot see it.
  -/
  noSelfTraverse : ∀ r w : Pddl.Name,
    ({ pred := "can_traverse", args := [r, w, w] } : GroundAtom) ∉ p.init

/-- The object names are distinct — decided by validation, not assumed. -/
theorem Pinned.namesNodup {d : Domain} {p : Problem} (hp : Pinned d p) :
    ((allObjects d p).map (·.name)).Nodup := hp.validated.namesNodup

/-- Every parameter of every Rovers schema has a declared type. -/
theorem params_typed (hp : Pinned d p) {objects : List TypedName}
    (i : Instance d objects) : ∀ pm ∈ i.schema.params, pm.type ∈ d.typeNames := by
  intro pm hpm
  rcases instance_shape hp.domain i with
    ⟨x, y, z, hs, -⟩ | ⟨x, s, q, hs, -⟩ | ⟨x, s, q, hs, -⟩ | ⟨x, y, hs, -⟩ |
      ⟨r, c, t, w, hs, -⟩ | ⟨r, q, o, c, m, hs, -⟩ | ⟨r, l, q, x, y, hs, -⟩ |
      ⟨r, l, q, x, y, hs, -⟩ | ⟨r, l, o, m, x, y, hs, -⟩ <;> rw [hs] at hpm <;>
    simp only [navigateA, sampleSoilA, sampleRockA, dropA, calibrateA, takeImageA,
      commSoilA, commRockA, commImageA, List.mem_cons, List.not_mem_nil,
      or_false] at hpm <;>
    rcases hpm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact hp.roverType | exact hp.waypointType | exact hp.storeType
      | exact hp.cameraType | exact hp.modeType | exact hp.landerType
      | exact hp.objectiveType

/-- **Every Rovers operator costs one.** -/
theorem cost_one (hp : Pinned d p) (rel : Bool) :
    ∀ o ∈ groundedOps d p rel, 1 ≤ o.cost := by
  intro o ho
  obtain ⟨hf⟩ := opFacts_ground d p rel ho
  rw [hf.cost]
  show 1 ≤ hf.inst.schema.cost
  rcases instance_shape hp.domain hf.inst with
    ⟨x, y, z, hs, -⟩ | ⟨x, s, q, hs, -⟩ | ⟨x, s, q, hs, -⟩ | ⟨x, y, hs, -⟩ |
      ⟨r, c, t, w, hs, -⟩ | ⟨r, q, o, c, m, hs, -⟩ | ⟨r, l, q, x, y, hs, -⟩ |
      ⟨r, l, q, x, y, hs, -⟩ | ⟨r, l, o, m, x, y, hs, -⟩ <;>
    rw [hs] <;> exact Nat.le_refl 1

theorem cost_pos (hp : Pinned d p) (rel : Bool) :
    ∀ o ∈ groundedOps d p rel, 0 < o.cost := fun o ho =>
  Nat.lt_of_lt_of_le Nat.zero_lt_one (cost_one hp rel o ho)

/-- And so does every operator of the numbered task. -/
theorem ops_cost (hp : Pinned d p) (rel : Bool) :
    ∀ op ∈ (ground d p rel).ops, 1 ≤ op.cost := by
  intro op hop
  have hops : (ground d p rel).ops
      = (groundedOps d p rel).map
        (numberOp (factIndex (allAtoms (groundedOps d p rel) p.goal.toArray)).1) := rfl
  rw [hops, Array.mem_map] at hop
  obtain ⟨o, ho, rfl⟩ := hop
  exact cost_one hp rel o ho

/-- The object list names each block once, read through the task's table. -/
theorem objectNames_inj (hp : Pinned d p) (rel : Bool) :
    ∀ x y, x < (ground d p rel).objectNames.size →
      y < (ground d p rel).objectNames.size →
      (ground d p rel).objectNames.getD x default
        = (ground d p rel).objectNames.getD y default → x = y := by
  have hnd : (ground d p rel).objectNames.toList.Nodup := by
    show (((allObjects d p).toArray.map (·.name)).toList).Nodup
    simpa using hp.namesNodup
  intro x y hx hy h
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hx, Option.getD_some,
    Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hy, Option.getD_some] at h
  exact (List.Nodup.getElem_inj_iff hnd
    (hi := by simpa using hx) (hj := by simpa using hy)).mp (by simpa using h)

/-- The task's goal names each fact once. -/
theorem goal_nodup (hp : Pinned d p) (rel : Bool) :
    ((ground d p rel).goal).toList.Nodup := by
  show ((p.goal.toArray.map (fun a =>
    (factIndex (allAtoms (groundedOps d p rel) p.goal.toArray)).1.getD a 0)).toList).Nodup
  rw [Array.toList_map]
  refine List.Nodup.map_on (fun a ha b hb h => ?_) (by simpa using hp.goalNodup)
  have hma : a ∈ allAtoms (groundedOps d p rel) p.goal.toArray := by
    unfold allAtoms
    exact Array.mem_append.mpr (Or.inr (by simpa using ha))
  have hmb : b ∈ allAtoms (groundedOps d p rel) p.goal.toArray := by
    unfold allAtoms
    exact Array.mem_append.mpr (Or.inr (by simpa using hb))
  exact factIndex_injective' _ (factIndex_contains _ hma) (factIndex_contains _ hmb) h

/-- **Distinct facts name distinct atoms.**  `factIndex` numbers each atom once,
so reading a name back gives the index it was read from.

(The same proof appears in `Proofs/Lifted/BlocksworldBridge.lean`; both belong in
`Proofs/CompileSupport.lean` once that file is not being edited.) -/
theorem factNames_inj {rel : Bool} {f g : Fact}
    (hf : f < (ground d p rel).factNames.size)
    (hg : g < (ground d p rel).factNames.size)
    (h : (ground d p rel).factNames.getD f default
      = (ground d p rel).factNames.getD g default) : f = g := by
  have hfn : (ground d p rel).factNames
      = (factIndex (allAtoms (groundedOps d p rel) p.goal.toArray)).2 := rfl
  rw [hfn] at hf hg h
  obtain ⟨-, hf'⟩ := factIndex_rev _ f hf
  obtain ⟨-, hg'⟩ := factIndex_rev _ g hg
  rw [← hf', h, hg']

/-! ### Numbering the atoms a schema names

Rovers has static preconditions, so `ground_names_instance` has a real side
condition here: the grounder checked those against `:init`, and that check has to
be turned back into membership.
-/

/-- What the grounder checked against `:init` really is in `:init`. -/
theorem mem_init_of_contains {a : GroundAtom}
    (h : (Std.HashSet.ofList p.init).contains a = true) : a ∈ p.init := by
  rw [Std.HashSet.contains_ofList] at h
  simpa using h

/-- And so an instance's static preconditions hold of the initial state. -/
theorem staticHeld_mem {o : AtomOp} (hf : OpFacts d p o) :
    ∀ y ∈ hf.inst.schema.pre, (staticPredicates d).contains y.pred = true →
      instAtom hf.inst.schema.params hf.inst.args y ∈ p.init :=
  fun y hy hs => mem_init_of_contains (hf.staticHeld y hy hs)

/-- **A dynamic precondition of a Rovers schema is numbered.** -/
theorem names_pre (hp : Pinned d p) {o : AtomOp} (hf : OpFacts d p o) {y : Atom}
    (hy : y ∈ hf.inst.schema.pre)
    (hdyn : (staticPredicates d).contains y.pred = false) :
    ∃ f, f < (ground d p false).numFacts ∧
      (ground d p false).factNames.getD f default
        = instAtom hf.inst.schema.params hf.inst.args y :=
  ground_names_instance d p hf.inst (params_typed hp hf.inst) (staticHeld_mem hf)
    (Or.inl ⟨hy, hdyn⟩)

/-- **A `navigate` never loops.** -/
theorem navigate_ne (hp : Pinned d p) {o : AtomOp} (hf : OpFacts d p o)
    {x y z : Pddl.Name} (hs : hf.inst.schema = navigateA)
    (hargs : hf.inst.args = [x, y, z]) : y ≠ z := by
  intro hyz
  subst hyz
  have hy : canTraverseV "?x" "?y" "?z" ∈ hf.inst.schema.pre := by
    rw [hs]; simp [navigateA]
  have hin := staticHeld_mem hf _ hy hp.canTraverseStatic
  rw [show instAtom hf.inst.schema.params hf.inst.args (canTraverseV "?x" "?y" "?z")
    = { pred := "can_traverse", args := [x, y, y] } from by rw [hs, hargs]; rfl] at hin
  exact hp.noSelfTraverse x y hin

/-- **A `navigate` really puts its rover at the destination.**  The destination
atom is not one of its own preconditions, because the step is not a self-loop, so
the add survives grounding. -/
theorem navigate_adds (hp : Pinned d p) {o : AtomOp} (hfa : OpFactsAdd d p o)
    {x y z : Pddl.Name} (hs : hfa.inst.schema = navigateA)
    (hargs : hfa.inst.args = [x, y, z]) (σ : AtomState) :
    o.applyA σ (at_ x z) = true := by
  have hinst : instAtom hfa.inst.schema.params hfa.inst.args (atV "?x" "?z")
      = at_ x z := by rw [hs, hargs]; rfl
  have hpre : hfa.inst.pre = [{ pred := "can_traverse", args := [x, y, z] }, at_ x y,
      { pred := "visible", args := [y, z] }] := by
    rw [Pddl.Instance.pre_eq, hs, hargs]; rfl
  have hne : y ≠ z := navigate_ne hp hfa.toOpFacts hs hargs
  have hnp : instAtom hfa.inst.schema.params hfa.inst.args (atV "?x" "?z") ∉ o.pre := by
    rw [hinst]
    intro hmem
    have h := hfa.subPre _ hmem
    rw [hpre] at h
    rcases (by simpa using h :
        at_ x z = { pred := "can_traverse", args := [x, y, z] } ∨
        at_ x z = at_ x y ∨
        at_ x z = { pred := "visible", args := [y, z] }) with h' | h' | h'
    · simp [at_] at h'
    · have hzy : z = y := by simpa [at_] using h'
      exact hne hzy.symm
    · simp [at_] at h'
  have hy : atV "?x" "?z" ∈ hfa.inst.schema.add := by rw [hs]; simp [navigateA]
  have h := asserted_of_lists hfa hy hnp σ
  rwa [hinst] at h

/-- **The destination add of a `navigate` survives grounding and pruning.** -/
theorem navigate_add_mem (hp : Pinned d p) {o : AtomOp} (hfa : OpFactsAdd d p o)
    {x y z : Pddl.Name} (hs : hfa.inst.schema = navigateA)
    (hargs : hfa.inst.args = [x, y, z]) : at_ x z ∈ o.add := by
  have hinst : instAtom hfa.inst.schema.params hfa.inst.args (atV "?x" "?z")
      = at_ x z := by rw [hs, hargs]; rfl
  have hpre : hfa.inst.pre = [{ pred := "can_traverse", args := [x, y, z] }, at_ x y,
      { pred := "visible", args := [y, z] }] := by
    rw [Pddl.Instance.pre_eq, hs, hargs]; rfl
  have hne : y ≠ z := navigate_ne hp hfa.toOpFacts hs hargs
  have hnp : at_ x z ∉ o.pre := by
    intro hmem
    have h := hfa.subPre _ hmem
    rw [hpre] at h
    rcases (by simpa using h :
        at_ x z = { pred := "can_traverse", args := [x, y, z] } ∨
        at_ x z = at_ x y ∨
        at_ x z = { pred := "visible", args := [y, z] }) with h' | h' | h'
    · simp [at_] at h'
    · have hzy : z = y := by simpa [at_] using h'
      exact hne hzy.symm
    · simp [at_] at h'
  have hy : atV "?x" "?z" ∈ hfa.inst.schema.add := by rw [hs]; simp [navigateA]
  have hmem := hfa.addComplete _ hy (by rwa [hinst])
  rwa [hinst] at hmem

/-- **An atom a Rovers schema adds is numbered.** -/
theorem names_add (hp : Pinned d p) {o : AtomOp} (hf : OpFacts d p o) {y : Atom}
    (hy : y ∈ hf.inst.schema.add) :
    ∃ f, f < (ground d p false).numFacts ∧
      (ground d p false).factNames.getD f default
        = instAtom hf.inst.schema.params hf.inst.args y :=
  ground_names_instance d p hf.inst (params_typed hp hf.inst) (staticHeld_mem hf)
    (Or.inr (Or.inl hy))

/-! ### Frames

Every field of `Quiet`, `GoalsFixed` and `ResourceStep` says some family of facts
did not move.  All of them reduce to one question: does this schema touch an atom
of that predicate?  `framed_of_pred` turns the answer into the frame, and the
nine lemmas after it answer it for each schema.
-/

/-- An operator that touches no atom of a predicate leaves every such atom. -/
theorem framed_of_pred {o : AtomOp} (hf : OpFacts d p o) {P : Pddl.Name}
    (hadd : ∀ a ∈ hf.inst.add, a.pred ≠ P) (hdel : ∀ a ∈ hf.inst.del, a.pred ≠ P)
    {a : GroundAtom} (ha : a.pred = P) (σ : AtomState) : o.applyA σ a = σ a :=
  applyA_frame σ (fun hm => hadd a (hf.subAdd a hm) ha)
    (fun hm => hdel a (hf.subDel a hm) ha)

/--
**And so the facts of that predicate keep their values.**

This is the shape every `Quiet` and `GoalsFixed` field takes: read the fact's
atom off the table, note its predicate, and check the schema does not touch it.
-/
theorem test_frame_pred {o : AtomOp} (hf : OpFacts d p o) {P : Pddl.Name}
    (hadd : ∀ a ∈ hf.inst.add, a.pred ≠ P) (hdel : ∀ a ∈ hf.inst.del, a.pred ≠ P)
    {t : Task} {s s' : State} {σ : AtomState}
    (habs : Abstracts t s σ) (habs' : Abstracts t s' (o.applyA σ))
    (hn : t.numFacts = t.factNames.size)
    {f : Fact} (hlt : f < t.factNames.size)
    (hp : (t.factNames.getD f default).pred = P) : s'.test f = s.test f := by
  rw [← habs'.numbered f (by rw [hn]; exact hlt),
    ← habs.numbered f (by rw [hn]; exact hlt)]
  exact framed_of_pred hf hadd hdel hp σ

variable {objects : List TypedName}

/-- `navigate` touches only `at`. -/
theorem navigate_touches (i : Instance d objects) {x y z : Pddl.Name}
    (hs : i.schema = navigateA) (ha : i.args = [x, y, z])
    {a : GroundAtom} (h : a ∈ i.add ∨ a ∈ i.del) : a.pred = "at" := by
  obtain ⟨-, hadd, hdel⟩ := navigate_atoms i hs ha
  rcases h with h | h
  · rw [hadd] at h
    obtain rfl : a = at_ x z := by simpa using h
    rfl
  · rw [hdel] at h
    obtain rfl : a = at_ x y := by simpa using h
    rfl

/-- `sample_soil` touches `full`, `have_soil_analysis`, `empty` and
`at_soil_sample`. -/
theorem sampleSoil_touches (i : Instance d objects) {x s q : Pddl.Name}
    (hs : i.schema = sampleSoilA) (ha : i.args = [x, s, q])
    {a : GroundAtom} (h : a ∈ i.add ∨ a ∈ i.del) :
    a.pred = "full" ∨ a.pred = "have_soil_analysis" ∨ a.pred = "empty" ∨
      a.pred = "at_soil_sample" := by
  obtain ⟨-, -, -, hadd, hdel⟩ := sampleSoil_atoms i hs ha
  rcases h with h | h
  · rw [hadd] at h
    rcases (by simpa using h : a = fullS s ∨ a = haveSoil x q) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · rw [hdel] at h
    rcases (by simpa using h : a = emptyS s ∨ a = atSoilSample q) with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

/-- `sample_rock` touches `full`, `have_rock_analysis`, `empty` and
`at_rock_sample`. -/
theorem sampleRock_touches (i : Instance d objects) {x s q : Pddl.Name}
    (hs : i.schema = sampleRockA) (ha : i.args = [x, s, q])
    {a : GroundAtom} (h : a ∈ i.add ∨ a ∈ i.del) :
    a.pred = "full" ∨ a.pred = "have_rock_analysis" ∨ a.pred = "empty" ∨
      a.pred = "at_rock_sample" := by
  obtain ⟨-, -, -, hadd, hdel⟩ := sampleRock_atoms i hs ha
  rcases h with h | h
  · rw [hadd] at h
    rcases (by simpa using h : a = fullS s ∨ a = haveRock x q) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · rw [hdel] at h
    rcases (by simpa using h : a = emptyS s ∨ a = atRockSample q) with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

/-- `drop` touches only the store. -/
theorem drop_touches (i : Instance d objects) {x y : Pddl.Name}
    (hs : i.schema = dropA) (ha : i.args = [x, y])
    {a : GroundAtom} (h : a ∈ i.add ∨ a ∈ i.del) :
    a.pred = "empty" ∨ a.pred = "full" := by
  obtain ⟨-, hadd, hdel⟩ := drop_atoms i hs ha
  rcases h with h | h
  · rw [hadd] at h
    obtain rfl : a = emptyS y := by simpa using h
    exact Or.inl rfl
  · rw [hdel] at h
    obtain rfl : a = fullS y := by simpa using h
    exact Or.inr rfl

/-- `calibrate` touches only `calibrated`. -/
theorem calibrate_touches (i : Instance d objects) {r c t w : Pddl.Name}
    (hs : i.schema = calibrateA) (ha : i.args = [r, c, t, w])
    {a : GroundAtom} (h : a ∈ i.add ∨ a ∈ i.del) : a.pred = "calibrated" := by
  obtain ⟨-, hadd, hdel⟩ := calibrate_atoms i hs ha
  rcases h with h | h
  · rw [hadd] at h
    obtain rfl : a = calibrated c r := by simpa using h
    rfl
  · rw [hdel] at h; simp at h

/-- `take_image` touches `have_image` and `calibrated`. -/
theorem takeImage_touches (i : Instance d objects) {r q o c m : Pddl.Name}
    (hs : i.schema = takeImageA) (ha : i.args = [r, q, o, c, m])
    {a : GroundAtom} (h : a ∈ i.add ∨ a ∈ i.del) :
    a.pred = "have_image" ∨ a.pred = "calibrated" := by
  obtain ⟨-, -, hadd, hdel⟩ := takeImage_atoms i hs ha
  rcases h with h | h
  · rw [hadd] at h
    obtain rfl : a = haveImage r o m := by simpa using h
    exact Or.inl rfl
  · rw [hdel] at h
    obtain rfl : a = calibrated c r := by simpa using h
    exact Or.inr rfl

/-- `communicate_soil_data` touches only its own goal family. -/
theorem commSoil_touches (i : Instance d objects) {r l q x y : Pddl.Name}
    (hs : i.schema = commSoilA) (ha : i.args = [r, l, q, x, y])
    {a : GroundAtom} (h : a ∈ i.add ∨ a ∈ i.del) :
    a.pred = "communicated_soil_data" := by
  obtain ⟨-, -, hadd, hdel⟩ := commSoil_atoms i hs ha
  rcases h with h | h
  · rw [hadd] at h
    obtain rfl : a = commSoil q := by simpa using h
    rfl
  · rw [hdel] at h; simp at h

/-- `communicate_rock_data` likewise. -/
theorem commRock_touches (i : Instance d objects) {r l q x y : Pddl.Name}
    (hs : i.schema = commRockA) (ha : i.args = [r, l, q, x, y])
    {a : GroundAtom} (h : a ∈ i.add ∨ a ∈ i.del) :
    a.pred = "communicated_rock_data" := by
  obtain ⟨-, -, hadd, hdel⟩ := commRock_atoms i hs ha
  rcases h with h | h
  · rw [hadd] at h
    obtain rfl : a = commRock q := by simpa using h
    rfl
  · rw [hdel] at h; simp at h

/-- And `communicate_image_data`. -/
theorem commImage_touches (i : Instance d objects) {r l o m x y : Pddl.Name}
    (hs : i.schema = commImageA) (ha : i.args = [r, l, o, m, x, y])
    {a : GroundAtom} (h : a ∈ i.add ∨ a ∈ i.del) :
    a.pred = "communicated_image_data" := by
  obtain ⟨-, -, hadd, hdel⟩ := commImage_atoms i hs ha
  rcases h with h | h
  · rw [hadd] at h
    obtain rfl : a = commImage o m := by simpa using h
    rfl
  · rw [hdel] at h; simp at h

/-! ### Each rover stands in one place

`roverFind` reads the *first* true `at` fact of a rover's table.  For that to be
the rover's position at all, at most one may be true — and `NavigateStep.reachStep`
is false without it, because a rover with two `at` facts true reports a different
waypoint after the step that deletes the first.

Only `navigate` touches `at`, so only `navigate` has anything to prove: it moves
its rover to the destination and nowhere else.
-/

/-- Each rover stands at one waypoint at most. -/
def OneAt (σ : AtomState) : Prop :=
  ∀ r w w', σ (at_ r w) = true → σ (at_ r w') = true → w = w'

/-- A successful initial-state check supplies the rover-position invariant. -/
theorem initOneAt_of_check {p : Problem} (h : initInvCheck p = true) :
    OneAt (fun a => p.init.toArray.contains a) := by
  simp only [initInvCheck, List.all_eq_true] at h
  intro r w w' hw hw'
  have hm : (r, w) ∈ initPairs p "at" :=
    mem_initPairs.mpr (by simpa [at_] using hw)
  have hm' : (r, w') ∈ initPairs p "at" :=
    mem_initPairs.mpr (by simpa [at_] using hw')
  simpa using h (r, w) hm (r, w') hm'

/-- A step that leaves the `at` atoms alone keeps it. -/
theorem oneAt_of_framed {σ τ : AtomState} (h : ∀ r w, τ (at_ r w) = σ (at_ r w))
    (hinv : OneAt σ) : OneAt τ := fun r w w' h1 h2 =>
  hinv r w w' (by rw [← h]; exact h1) (by rw [← h]; exact h2)

/-- **`navigate` keeps it.**  Afterwards its rover is at the destination and
nowhere else: any other `at` it could have held was the one just deleted. -/
theorem navigate_oneAt {o : AtomOp} (hf : OpFacts d p o) (hd : RoversDomain d)
    {x y z : Pddl.Name}
    (hs : hf.inst.schema = navigateA) (hargs : hf.inst.args = [x, y, z])
    {σ : AtomState} (happ : o.applicableA σ) (hinv : OneAt σ) :
    OneAt (o.applyA σ) := by
  obtain ⟨hpre, hadd, hdel⟩ := navigate_atoms hf.inst hs hargs
  have hpy : σ (at_ x y) = true := pre_holds hf hpre (at_dynamic hd) happ
  -- The moved rover ends up only at the destination.
  have hkey : ∀ w, (o.applyA σ) (at_ x w) = true → w = z := by
    intro w hw
    by_cases hwz : w = z
    · exact hwz
    have hnl : at_ x w ∉ [at_ x z] := by simpa [at_] using hwz
    have hnadd : at_ x w ∉ hf.inst.add := by rw [hadd]; exact hnl
    have hσw : σ (at_ x w) = true := falls_of_lists hf hadd hnl hw
    have hwy : w = y := hinv x w y hσw hpy
    subst hwy
    -- The rover's old `at` is deleted and not added back, so it is false after.
    have hdelo : at_ x w ∈ o.del :=
      del_kept hf (by rw [hdel]; simp) hnadd hpre (at_dynamic hd)
    have hnao : at_ x w ∉ o.add := fun hc => hnadd (hf.subAdd _ hc)
    rw [applyA_del σ hdelo hnao] at hw
    exact absurd hw (by simp)
  intro r w w' h1 h2
  by_cases hrx : r = x
  · subst hrx; rw [hkey w h1, hkey w' h2]
  · -- Every other rover's `at` atoms are framed.
    have hframe : ∀ u, (o.applyA σ) (at_ r u) = σ (at_ r u) := by
      intro u
      refine frame_of_lists hf hadd hdel ?_ ?_ σ
      · simpa [at_] using fun h => absurd h hrx
      · simpa [at_] using fun h => absurd h hrx
    rw [hframe] at h1 h2
    exact hinv r w w' h1 h2

/-- **`OneAt` is a transition invariant of a Rovers task.**  Only `navigate`
touches `at`; the other eight leave every `at` atom where it was. -/
theorem oneAt_closed (hd : RoversDomain d) {o : AtomOp} (hf : OpFacts d p o)
    {σ : AtomState} (happ : o.applicableA σ) (hinv : OneAt σ) :
    OneAt (o.applyA σ) := by
  rcases instance_shape hd hf.inst with
    ⟨x, y, z, hs, ha⟩ | ⟨x, st, q, hs, ha⟩ | ⟨x, st, q, hs, ha⟩ | ⟨x, y, hs, ha⟩ |
      ⟨rr, cc, tt, ww, hs, ha⟩ | ⟨rr, qq, oo, cc, mm, hs, ha⟩ |
      ⟨rr, ll, qq, xx, yy, hs, ha⟩ | ⟨rr, ll, qq, xx, yy, hs, ha⟩ |
      ⟨rr, ll, oo, mm, xx, yy, hs, ha⟩
  · exact navigate_oneAt hf hd hs ha happ hinv
  · exact oneAt_of_framed (fun _ _ => framed_of_pred (P := "at") hf
      (fun a hm => by
        rcases sampleSoil_touches hf.inst hs ha (Or.inl hm) with h|h|h|h <;> rw [h] <;> decide)
      (fun a hm => by
        rcases sampleSoil_touches hf.inst hs ha (Or.inr hm) with h|h|h|h <;> rw [h] <;> decide)
      rfl σ) hinv
  · exact oneAt_of_framed (fun _ _ => framed_of_pred (P := "at") hf
      (fun a hm => by
        rcases sampleRock_touches hf.inst hs ha (Or.inl hm) with h|h|h|h <;> rw [h] <;> decide)
      (fun a hm => by
        rcases sampleRock_touches hf.inst hs ha (Or.inr hm) with h|h|h|h <;> rw [h] <;> decide)
      rfl σ) hinv
  · exact oneAt_of_framed (fun _ _ => framed_of_pred (P := "at") hf
      (fun a hm => by
        rcases drop_touches hf.inst hs ha (Or.inl hm) with h|h <;> rw [h] <;> decide)
      (fun a hm => by
        rcases drop_touches hf.inst hs ha (Or.inr hm) with h|h <;> rw [h] <;> decide)
      rfl σ) hinv
  · exact oneAt_of_framed (fun _ _ => framed_of_pred (P := "at") hf
      (fun a hm => by rw [calibrate_touches hf.inst hs ha (Or.inl hm)]; decide)
      (fun a hm => by rw [calibrate_touches hf.inst hs ha (Or.inr hm)]; decide)
      rfl σ) hinv
  · exact oneAt_of_framed (fun _ _ => framed_of_pred (P := "at") hf
      (fun a hm => by
        rcases takeImage_touches hf.inst hs ha (Or.inl hm) with h|h <;> rw [h] <;> decide)
      (fun a hm => by
        rcases takeImage_touches hf.inst hs ha (Or.inr hm) with h|h <;> rw [h] <;> decide)
      rfl σ) hinv
  · exact oneAt_of_framed (fun _ _ => framed_of_pred (P := "at") hf
      (fun a hm => by rw [commSoil_touches hf.inst hs ha (Or.inl hm)]; decide)
      (fun a hm => by rw [commSoil_touches hf.inst hs ha (Or.inr hm)]; decide)
      rfl σ) hinv
  · exact oneAt_of_framed (fun _ _ => framed_of_pred (P := "at") hf
      (fun a hm => by rw [commRock_touches hf.inst hs ha (Or.inl hm)]; decide)
      (fun a hm => by rw [commRock_touches hf.inst hs ha (Or.inr hm)]; decide)
      rfl σ) hinv
  · exact oneAt_of_framed (fun _ _ => framed_of_pred (P := "at") hf
      (fun a hm => by rw [commImage_touches hf.inst hs ha (Or.inl hm)]; decide)
      (fun a hm => by rw [commImage_touches hf.inst hs ha (Or.inr hm)]; decide)
      rfl σ) hinv

end Planner.Lifted.Rovers

/- -------------------------------------------------------------------------- -/
/-
The adds that pruning must keep, and the ones it need not.

Rovers used to assume the unrestricted fact — that grounding and the relevance
analysis keep every non-precondition add of every retained operator — as a field
of `Pinned`.  It is false.  A `sample_soil` at a waypoint no goal asks about is
kept, because it deletes the store's `empty` and that atom is relevant, but
nothing reads its `have_soil_analysis`, so the analysis trims that add.  Five
kept operators on `rovers/easy-p01` lose an add this way.

What the step proofs actually read is narrower, and true.  A `communicate`
deletes nothing, so an operator the analysis keeps must have kept its one add —
there is nothing else for it to have touched.  And a `navigate`'s new position is
relevant because the drive *back* reads it and adds the position the operator
came from, which is relevant already.
-/

namespace Planner.Lifted.Rovers

open Planner Planner.Pddl

variable {d : Domain} {p : Problem}

/-- The dynamic preconditions of a `navigate`, as the grounder filters them. -/
abbrev navDyn (d : Domain) : List Atom :=
  navigateA.pre.filter fun a => !(staticPredicates d).contains a.pred

/-- **Every traversal of the map is a `navigate` of the unpruned task.** -/
theorem raw_navigate (hp : Pinned d p) {x y z : Name}
    (hwx : WellTyped d (allObjects d p) "rover" x)
    (hwy : WellTyped d (allObjects d p) "waypoint" y)
    (hwz : WellTyped d (allObjects d p) "waypoint" z)
    (hct : ({ pred := "can_traverse", args := [x, y, z] } : GroundAtom) ∈ p.init)
    (hvis : ({ pred := "visible", args := [y, z] } : GroundAtom) ∈ p.init) :
    mkOp navigateA (navDyn d) #[x, y, z] ∈ rawOps d p := by
  rw [← groundedOps_false]
  refine groundedOps_complete d p (a := navigateA) (by rw [hp.domain]; simp) #[x, y, z]
    rfl ?_ ?_ ?_
  · intro pm hpm
    simp only [navigateA, List.mem_cons, List.not_mem_nil, or_false] at hpm
    rcases hpm with rfl | rfl | rfl
    · exact hp.roverType
    · exact hp.waypointType
    · exact hp.waypointType
  · show List.Forall₂ _ navigateA.params [x, y, z]
    exact List.Forall₂.cons hwx (List.Forall₂.cons hwy
      (List.Forall₂.cons hwz List.Forall₂.nil))
  · intro w hw hst
    simp only [navigateA, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact hct
    · rw [show (atV "?x" "?y").pred = "at" from rfl, at_dynamic hp.domain] at hst
      exact absurd hst (by simp)
    · exact hvis

/--
**A rover's origin is relevant once its destination is.**

The drive adds `at ?x ?z`, so if that atom is relevant the analysis keeps the
drive, and then — the set being closed — everything the drive reads is relevant,
`at ?x ?y` among it.
-/
theorem at_relevant (hp : Pinned d p) {r : Std.HashSet GroundAtom}
    (hclosed : Closed (rawOps d p) r) {x y z : Name}
    (hwx : WellTyped d (allObjects d p) "rover" x)
    (hwy : WellTyped d (allObjects d p) "waypoint" y)
    (hwz : WellTyped d (allObjects d p) "waypoint" z)
    (hct : ({ pred := "can_traverse", args := [x, y, z] } : GroundAtom) ∈ p.init)
    (hvis : ({ pred := "visible", args := [y, z] } : GroundAtom) ∈ p.init)
    (h : r.contains (at_ x z) = true) : r.contains (at_ x y) = true := by
  have hne : y ≠ z := by
    rintro rfl
    exact hp.noSelfTraverse x y hct
  set op := mkOp navigateA (navDyn d) #[x, y, z] with hop
  have hmem : op ∈ rawOps d p := raw_navigate hp hwx hwy hwz hct hvis
  have hadd : at_ x z ∈ op.add := by
    have heq : instAtom navigateA.params (#[x, y, z] : Array Name).toList (atV "?x" "?z")
        = at_ x z := rfl
    rw [hop, ← heq]
    refine mem_mkOp_add navigateA (navDyn d) _ (by simp [navigateA]) ?_
    intro w hw
    have hw' : w ∈ navigateA.pre := (List.mem_filter.mp hw).1
    simp only [navigateA, List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl | rfl
    · show ({ pred := "can_traverse", args := [x, y, z] } : GroundAtom) ≠ at_ x z
      simp [at_]
    · show at_ x y ≠ at_ x z
      simpa [at_] using hne
    · show ({ pred := "visible", args := [y, z] } : GroundAtom) ≠ at_ x z
      simp [at_]
  have htouch : op.touches r = true := by
    unfold AtomOp.touches
    rw [array_any_of_mem hadd h]
    rfl
  refine hclosed op hmem htouch (at_ x y) ?_
  have heq : instAtom navigateA.params (#[x, y, z] : Array Name).toList (atV "?x" "?y")
      = at_ x y := rfl
  rw [hop, ← heq]
  refine mem_mkOp_pre navigateA (navDyn d) _ (List.mem_filter.mpr ⟨by simp [navigateA], ?_⟩)
  simp only [Bool.not_eq_true']
  exact at_dynamic hp.domain

/-! ### An operator that deletes nothing kept its one add -/

/--
The three `communicate` schemas delete nothing, so a kept one must have kept its
add: there is nothing else it could have touched the relevant set with.
-/
theorem lone_add_relevant {op : AtomOp} {r : Std.HashSet GroundAtom}
    (hfa : OpFactsAdd d p op) (htouch : op.touches r = true)
    (hdel : hfa.inst.del = []) {a : GroundAtom} (hadd : hfa.inst.add = [a]) :
    r.contains a = true := by
  have hdelFalse : op.del.any r.contains = false := by
    by_contra hc
    rw [Bool.not_eq_false, ← Array.any_toList] at hc
    obtain ⟨w, hw, -⟩ := List.any_eq_true.mp hc
    have hmem := hfa.subDel w (by simpa using hw)
    rw [hdel] at hmem
    simp at hmem
  have hany : op.add.any r.contains = true := by
    unfold AtomOp.touches at htouch
    rw [hdelFalse, Bool.or_false] at htouch
    exact htouch
  rw [← Array.any_toList] at hany
  obtain ⟨w, hw, hrw⟩ := List.any_eq_true.mp hany
  have hmem := hfa.subAdd w (by simpa using hw)
  rw [hadd] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rwa [hmem] at hrw

/-! ### The adds the proofs read are kept -/

/-- With pruning off, grounding keeps every add, so the restriction is free. -/
theorem addsFor_of_raw {o : AtomOp} (hfa : OpFactsAdd d p o) :
    AddsFor d p o hfa.toOpFacts := fun _ y hy hnp => hfa.addComplete y hy hnp

/--
**Rovers keeps the adds its proofs read**, with the relevance analysis on or off.

A `communicate` keeps its add because it deletes nothing.  A `navigate` keeps its
add because the drive back reads the destination and adds the origin, which is
relevant already — that is what `Pinned.traverseReverses` is for.
-/
theorem addsKept (hp : Pinned d p) (rel : Bool) : AddsKept d p rel := by
  cases rel with
  | false =>
      intro o ho
      obtain ⟨hfa⟩ := opFacts_raw_add d p (by rwa [← groundedOps_false])
      exact ⟨hfa.toOpFacts, addsFor_of_raw hfa⟩
  | true =>
      intro o ho
      rcases relevance_cases (rawOps d p) p.goal.toArray with
        ⟨r, hclosed, -, hrdef⟩ | hall
      · obtain ⟨op, hop, hval, hpre, htouch⟩ := pruned_op ho hclosed hrdef
        obtain ⟨hfa⟩ := opFacts_raw_add d p hop
        subst hval
        refine ⟨⟨hfa.inst, ?_, ?_, ?_, ?_, hfa.staticHeld, ?_, hfa.cost⟩, ?_⟩
        · intro a ha; exact hfa.subPre a ha
        · intro a ha; exact hfa.subAdd a (Array.mem_filter.mp ha).1
        · intro a ha; exact hfa.subDel a (Array.mem_filter.mp ha).1
        · intro y hy hdyn; exact hfa.preComplete y hy hdyn
        · intro y hy hn hp2
          exact Array.mem_filter.mpr ⟨hfa.delComplete y hy hn hp2, hpre _ hp2⟩
        · intro hreads y hy hnp
          refine Array.mem_filter.mpr ⟨hfa.addComplete y hy hnp, ?_⟩
          rcases hreads with hs | hs | hs | hs
          · -- `navigate`: the drive back makes the destination relevant
            obtain ⟨x, w, z, ha, hwx, hww, hwz⟩ := hfa.inst.args_three
              (show hfa.inst.schema.params
                = [roverP "?x", waypointP "?y", waypointP "?z"] by rw [hs])
            have hyv : y = atV "?x" "?z" := by
              rw [hs] at hy
              simpa [navigateA] using hy
            have hinst : instAtom hfa.inst.schema.params hfa.inst.args y = at_ x z := by
              rw [hyv, hs, ha]; rfl
            rw [hinst]
            have hct : ({ pred := "can_traverse", args := [x, w, z] } : GroundAtom)
                ∈ p.init := by
              have hmem := staticHeld_mem hfa.toOpFacts (canTraverseV "?x" "?y" "?z")
                (by rw [hs]; simp [navigateA]) hp.canTraverseStatic
              rwa [show instAtom hfa.inst.schema.params hfa.inst.args
                (canTraverseV "?x" "?y" "?z")
                = { pred := "can_traverse", args := [x, w, z] } from by
                  rw [hs, ha]; rfl] at hmem
            have hvis : ({ pred := "visible", args := [w, z] } : GroundAtom) ∈ p.init := by
              have hmem := staticHeld_mem hfa.toOpFacts (visibleV "?y" "?z")
                (by rw [hs]; simp [navigateA]) hp.visibleStatic
              rwa [show instAtom hfa.inst.schema.params hfa.inst.args (visibleV "?y" "?z")
                = { pred := "visible", args := [w, z] } from by rw [hs, ha]; rfl] at hmem
            have hatw : at_ x w ∈ (AtomOp.trim op r).pre := by
              have hmem := hfa.preComplete (atV "?x" "?y") (by rw [hs]; simp [navigateA])
                (by rw [show (atV "?x" "?y").pred = "at" from rfl]
                    exact at_dynamic hp.domain)
              rwa [show instAtom hfa.inst.schema.params hfa.inst.args (atV "?x" "?y")
                = at_ x w from by rw [hs, ha]; rfl] at hmem
            obtain ⟨hct', hvis'⟩ := hp.traverseReverses x w z hct hvis
            exact at_relevant hp hclosed hwx hwz hww hct' hvis' (hpre _ hatw)
          · -- `communicate_soil_data`: it deletes nothing
            obtain ⟨rr, l, q, x, w, ha, -, -, -, -, -⟩ := hfa.inst.args_five
              (show hfa.inst.schema.params = [roverP "?r", landerP "?l", waypointP "?p",
                waypointP "?x", waypointP "?y"] by rw [hs])
            have hyv : y = commSoilV "?p" := by
              rw [hs] at hy
              simpa [commSoilA] using hy
            have hinst : instAtom hfa.inst.schema.params hfa.inst.args y = commSoil q := by
              rw [hyv, hs, ha]; rfl
            rw [hinst]
            exact lone_add_relevant hfa htouch (by rw [Instance.del_eq, hs, ha]; rfl)
              (show hfa.inst.add = [commSoil q] by rw [Instance.add_eq, hs, ha]; rfl)
          · obtain ⟨rr, l, q, x, w, ha, -, -, -, -, -⟩ := hfa.inst.args_five
              (show hfa.inst.schema.params = [roverP "?r", landerP "?l", waypointP "?p",
                waypointP "?x", waypointP "?y"] by rw [hs])
            have hyv : y = commRockV "?p" := by
              rw [hs] at hy
              simpa [commRockA] using hy
            have hinst : instAtom hfa.inst.schema.params hfa.inst.args y = commRock q := by
              rw [hyv, hs, ha]; rfl
            rw [hinst]
            exact lone_add_relevant hfa htouch (by rw [Instance.del_eq, hs, ha]; rfl)
              (show hfa.inst.add = [commRock q] by rw [Instance.add_eq, hs, ha]; rfl)
          · obtain ⟨rr, l, ob, m, x, w, ha, -, -, -, -, -, -⟩ := hfa.inst.args_six
              (show hfa.inst.schema.params = [roverP "?r", landerP "?l", objectiveP "?o",
                modeP "?m", waypointP "?x", waypointP "?y"] by rw [hs])
            have hyv : y = commImageV "?o" "?m" := by
              rw [hs] at hy
              simpa [commImageA] using hy
            have hinst : instAtom hfa.inst.schema.params hfa.inst.args y
                = commImage ob m := by rw [hyv, hs, ha]; rfl
            rw [hinst]
            exact lone_add_relevant hfa htouch (by rw [Instance.del_eq, hs, ha]; rfl)
              (show hfa.inst.add = [commImage ob m] by rw [Instance.add_eq, hs, ha]; rfl)
      · have heq : groundedOps d p true = rawOps d p := by rw [groundedOps_true, hall]
        rw [heq] at ho
        obtain ⟨hfa⟩ := opFacts_raw_add d p ho
        exact ⟨hfa.toOpFacts, addsFor_of_raw hfa⟩

end Planner.Lifted.Rovers

/- -------------------------------------------------------------------------- -/
/-
Reading Rovers' compiled tables.

Every table the heuristic keeps is a filter of `factsWith`, so every entry is a
numbered fact naming an atom of one predicate.  The lemmas here say which atom,
for each of the four dynamic families the counters read: where a rover stands,
which analyses are held, which pictures are held, and the `calibrated` and
`empty` facts the resource count reads.

This is the layer the step proof reads the state through — the Rovers analogue
of `Proofs/Domains/Blocksworld/Step.lean`.
-/

namespace Planner.Lifted.Rovers

open Planner Planner.Pddl

/-- The object a `findIdx?` picks out is the one searched for. -/
theorem name_of_findIdx {xs : Array Pddl.Name} {w : Pddl.Name} {i : Nat}
    (h : xs.findIdx? (· == w) = some i) : xs.getD i default = w := by
  obtain ⟨hlt, hp, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp h
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt, Option.getD_some]
  exact eq_of_beq hp

/-- **Where a rover stands.**  An entry of the `at` table of rover `r` is a
numbered fact naming `at(r, w)`, with `w` the waypoint its index picks out. -/
theorem mem_roverAt_entries {t : Task} {r : Pddl.Name} {f : Fact} {wi : Nat}
    {waypoints : Array Pddl.Name}
    (h : (f, wi) ∈ (t.factsWith "at").filterMap fun x =>
      match x.2.args with
      | [y, w] => if y == r then (waypoints.findIdx? (· == w)).map ((x.1, ·)) else none
      | _ => none) :
    f < t.factNames.size ∧ wi < waypoints.size ∧
      t.factNames.getD f default =
        { pred := "at", args := [r, waypoints.getD wi default] } := by
  obtain ⟨x, -, hval, hlt, hname, hpred⟩ := mem_factsWith_filterMap h
  obtain ⟨g, a⟩ := x
  dsimp only at hval hlt hname hpred
  rcases hargs : a.args with _ | ⟨y, rest⟩
  · rw [hargs] at hval; simp at hval
  rcases rest with _ | ⟨w, rest⟩
  · rw [hargs] at hval; simp at hval
  rcases rest with _ | ⟨u, rest⟩
  case cons.cons.cons => rw [hargs] at hval; simp at hval
  rw [hargs] at hval
  dsimp only at hval
  by_cases hy : y == r
  · rw [if_pos hy] at hval
    rcases hidx : waypoints.findIdx? (· == w) with _ | j
    · rw [hidx] at hval; simp at hval
    · rw [hidx] at hval
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hval
      obtain ⟨rfl, rfl⟩ := hval
      refine ⟨hlt, (Array.findIdx?_eq_some_iff_getElem.mp hidx).1, ?_⟩
      rw [hname, name_of_findIdx hidx]
      show a = { pred := "at", args := [r, w] }
      rw [← hpred, ← eq_of_beq hy, ← hargs]
  · rw [if_neg hy] at hval; simp at hval

/-- **Which analyses are held.**  An entry of a sample goal's analysis table is a
numbered fact naming `pred(_, w)` for the goal's waypoint. -/
theorem mem_analysisOf {t : Task} {pred w : Pddl.Name} {f : Fact}
    (h : f ∈ (t.factsWith pred).filterMap fun x =>
      match x.2.args with
      | [_, y] => if y == w then some x.1 else none
      | _ => none) :
    f < t.factNames.size ∧ (t.factNames.getD f default).pred = pred ∧
      ∃ r, t.factNames.getD f default = { pred := pred, args := [r, w] } := by
  obtain ⟨x, -, hval, hlt, hname, hpred⟩ := mem_factsWith_filterMap h
  obtain ⟨g, a⟩ := x
  dsimp only at hval hlt hname hpred
  rcases hargs : a.args with _ | ⟨r, rest⟩
  · rw [hargs] at hval; simp at hval
  rcases rest with _ | ⟨y, rest⟩
  · rw [hargs] at hval; simp at hval
  rcases rest with _ | ⟨u, rest⟩
  case cons.cons.cons => rw [hargs] at hval; simp at hval
  rw [hargs] at hval
  dsimp only at hval
  by_cases hyw : y == w
  · rw [if_pos hyw] at hval
    obtain rfl : g = f := by simpa using hval
    refine ⟨hlt, by rw [hname]; exact hpred, r, ?_⟩
    rw [hname]
    show a = { pred := pred, args := [r, w] }
    rw [← hpred, ← eq_of_beq hyw, ← hargs]
  · rw [if_neg hyw] at hval; simp at hval

/-- **Which pictures are held.**  An entry of an image goal's table names
`have_image(_, o, m)`. -/
theorem mem_haveFacts {t : Task} {o m : Pddl.Name} {f : Fact}
    (h : f ∈ (t.factsWith "have_image").filterMap fun x =>
      match x.2.args with
      | [_, y, z] => if y == o && z == m then some x.1 else none
      | _ => none) :
    f < t.factNames.size ∧
      ∃ r, t.factNames.getD f default =
        { pred := "have_image", args := [r, o, m] } := by
  obtain ⟨x, -, hval, hlt, hname, hpred⟩ := mem_factsWith_filterMap h
  obtain ⟨g, a⟩ := x
  dsimp only at hval hlt hname hpred
  rcases hargs : a.args with _ | ⟨r, rest⟩
  · rw [hargs] at hval; simp at hval
  rcases rest with _ | ⟨y, rest⟩
  · rw [hargs] at hval; simp at hval
  rcases rest with _ | ⟨z, rest⟩
  · rw [hargs] at hval; simp at hval
  rcases rest with _ | ⟨u, rest⟩
  case cons.cons.cons.cons => rw [hargs] at hval; simp at hval
  rw [hargs] at hval
  dsimp only at hval
  by_cases hyz : (y == o && z == m) = true
  · rw [if_pos hyz] at hval
    obtain rfl : g = f := by simpa using hval
    simp only [Bool.and_eq_true] at hyz
    refine ⟨hlt, r, ?_⟩
    rw [hname]
    show a = { pred := "have_image", args := [r, o, m] }
    rw [← hpred, ← eq_of_beq hyz.1, ← eq_of_beq hyz.2, ← hargs]
  · rw [if_neg hyz] at hval; simp at hval

/-- **The `calibrated` and `empty` facts.**  Both tables are the whole family. -/
theorem mem_factsWith_map {t : Task} {pred : Pddl.Name} {f : Fact}
    (h : f ∈ (t.factsWith pred).map (·.1)) :
    f < t.factNames.size ∧ (t.factNames.getD f default).pred = pred := by
  obtain ⟨x, hx, hval⟩ := Array.mem_map.mp h
  obtain ⟨h1, h2, h3⟩ := mem_factsWith hx
  subst hval
  exact ⟨h1, by rw [h2]; exact h3⟩

/-! ### The three goal tables

Each is a filter of the task's goal atoms, so an entry is a goal fact of the
task.  That is what `improved_admissible_of_schema` asks for in `c1`, `c2` and
`c3`, and until now it was assumed.
-/

open Planner.ExampleHeuristics.Rovers in
/-- The soil goal table, spelled out. -/
theorem compile_soilGoals (t : Task) :
    (compile t).soilGoals = t.goalAtoms.zipIdx.filterMap (fun x =>
      match x.1.pred, x.1.args with
      | "communicated_soil_data", [w] =>
          ((t.objectsOfTypes ["waypoint"]).findIdx? (· == w)).map fun wi =>
            ({ goalFact := t.goal.getD x.2 0, waypoint := wi,
               analysisFacts := (t.factsWith "have_soil_analysis").filterMap fun y =>
                 match y.2.args with
                 | [_, z] => if z == w then some y.1 else none
                 | _ => none } : SampleGoal)
      | _, _ => none) := rfl

open Planner.ExampleHeuristics.Rovers in
/-- The rock goal table, spelled out. -/
theorem compile_rockGoals (t : Task) :
    (compile t).rockGoals = t.goalAtoms.zipIdx.filterMap (fun x =>
      match x.1.pred, x.1.args with
      | "communicated_rock_data", [w] =>
          ((t.objectsOfTypes ["waypoint"]).findIdx? (· == w)).map fun wi =>
            ({ goalFact := t.goal.getD x.2 0, waypoint := wi,
               analysisFacts := (t.factsWith "have_rock_analysis").filterMap fun y =>
                 match y.2.args with
                 | [_, z] => if z == w then some y.1 else none
                 | _ => none } : SampleGoal)
      | _, _ => none) := rfl

open Planner.ExampleHeuristics.Rovers in
/-- The image goal table, spelled out. -/
theorem compile_imageGoals (t : Task) :
    (compile t).imageGoals = t.goalAtoms.zipIdx.filterMap (fun x =>
      match x.1.pred, x.1.args with
      | "communicated_image_data", [o, m] =>
          some ({ goalFact := t.goal.getD x.2 0
                  haveFacts := (t.factsWith "have_image").filterMap fun y =>
                    match y.2.args with
                    | [_, u, v] => if u == o && v == m then some y.1 else none
                    | _ => none } : ImageGoal)
      | _, _ => none) := rfl

/-- A fact read out of the goal array at a goal-atom position is a goal fact. -/
theorem goal_getD_mem {d : Domain} {p : Problem} {rel : Bool} {i : Nat}
    (hi : i < (ground d p rel).goalAtoms.size) :
    (ground d p rel).goal.getD i 0 ∈ (ground d p rel).goal := by
  have hgs : (ground d p rel).goal.size = (ground d p rel).goalAtoms.size := by
    show (p.goal.toArray.map (fun a =>
      (factIndex (allAtoms (groundedOps d p rel) p.goal.toArray)).1.getD a 0)).size
      = (ground d p rel).goalAtoms.size
    rw [Array.size_map, taskOf_goalAtoms]
  have hlt : i < (ground d p rel).goal.size := by rw [hgs]; exact hi
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt, Option.getD_some]
  exact Array.getElem_mem hlt

open Planner.ExampleHeuristics.Rovers in
/-- **Every soil goal the table holds is a goal fact of the task.** -/
theorem soilGoals_mem_goal (d : Domain) (p : Problem) (rel : Bool) :
    ∀ g ∈ (compile (ground d p rel)).soilGoals,
      g.goalFact ∈ (ground d p rel).goal := by
  intro g hg
  rw [compile_soilGoals] at hg
  obtain ⟨x, hx, hval⟩ := Array.mem_filterMap.mp hg
  obtain ⟨-, hlt, -⟩ := Array.mem_zipIdx hx
  simp only [Nat.zero_add] at hlt
  split at hval
  · rename_i w h1 h2
    rcases hidx : ((ground d p rel).objectsOfTypes ["waypoint"]).findIdx? (· == w) with
      _ | wi
    · rw [hidx] at hval; simp at hval
    · rw [hidx] at hval
      simp only [Option.map_some, Option.some.injEq] at hval
      subst hval
      exact goal_getD_mem hlt
  · simp at hval

open Planner.ExampleHeuristics.Rovers in
/-- **And every rock goal.** -/
theorem rockGoals_mem_goal (d : Domain) (p : Problem) (rel : Bool) :
    ∀ g ∈ (compile (ground d p rel)).rockGoals,
      g.goalFact ∈ (ground d p rel).goal := by
  intro g hg
  rw [compile_rockGoals] at hg
  obtain ⟨x, hx, hval⟩ := Array.mem_filterMap.mp hg
  obtain ⟨-, hlt, -⟩ := Array.mem_zipIdx hx
  simp only [Nat.zero_add] at hlt
  split at hval
  · rename_i w h1 h2
    rcases hidx : ((ground d p rel).objectsOfTypes ["waypoint"]).findIdx? (· == w) with
      _ | wi
    · rw [hidx] at hval; simp at hval
    · rw [hidx] at hval
      simp only [Option.map_some, Option.some.injEq] at hval
      subst hval
      exact goal_getD_mem hlt
  · simp at hval

open Planner.ExampleHeuristics.Rovers in
/-- **And every image goal.** -/
theorem imageGoals_mem_goal (d : Domain) (p : Problem) (rel : Bool) :
    ∀ g ∈ (compile (ground d p rel)).imageGoals,
      g.goalFact ∈ (ground d p rel).goal := by
  intro g hg
  rw [compile_imageGoals] at hg
  obtain ⟨x, hx, hval⟩ := Array.mem_filterMap.mp hg
  obtain ⟨-, hlt, -⟩ := Array.mem_zipIdx hx
  simp only [Nat.zero_add] at hlt
  split at hval
  · simp only [Option.some.injEq] at hval
    subst hval
    exact goal_getD_mem hlt
  · simp at hval

open Planner.ExampleHeuristics.Rovers in
/--
**Rovers' improved heuristic is zero at every goal state of the task the grounder
builds**, with nothing assumed.

`improved_goalAware_of_schema` asks that each of the three goal tables hold goal
facts.  All three now follow from the tables being filters of the goal atoms,
which is what the declarative form of `compile` makes visible.
-/
theorem improved_goalAware (d : Domain) (p : Problem) (rel : Bool) :
    (ground d p rel).GoalAware (improved (ground d p rel)).eval :=
  improved_goalAware_of_schema _ (soilGoals_mem_goal d p rel)
    (rockGoals_mem_goal d p rel) (imageGoals_mem_goal d p rel)

/-! ### What predicate each table's facts use

`Quiet` says six families of facts did not move.  Each family is a table, and
each table's facts all use one predicate — so the whole structure follows from
the schema not touching those six predicates.
-/

open Planner.ExampleHeuristics.Rovers in
/-- The `at` table, spelled out. -/
theorem compile_roverAt (t : Task) :
    (compile t).roverAt = (t.objectsOfTypes ["rover"]).map (fun r =>
      (t.factsWith "at").filterMap fun x =>
        match x.2.args with
        | [y, w] =>
            if y == r then
              ((t.objectsOfTypes ["waypoint"]).findIdx? (· == w)).map ((x.1, ·))
            else none
        | _ => none) := rfl

open Planner.ExampleHeuristics.Rovers in
/-- The `calibrated` table, spelled out. -/
theorem compile_calibratedFacts (t : Task) :
    (compile t).calibratedFacts = (t.factsWith "calibrated").map (·.1) := rfl

open Planner.ExampleHeuristics.Rovers in
/-- The `empty` table, spelled out. -/
theorem compile_emptyFacts (t : Task) :
    (compile t).emptyFacts = (t.factsWith "empty").map (·.1) := rfl

open Planner.ExampleHeuristics.Rovers in
/-- Every `at` fact of the rover tables is numbered and uses `at`. -/
theorem roverAt_pred {t : Task} {r : Nat} {y : Fact × Nat}
    (hy : y ∈ (compile t).roverAt.getD r #[]) :
    y.1 < t.factNames.size ∧ (t.factNames.getD y.1 default).pred = "at" := by
  by_cases hr : r < (t.objectsOfTypes ["rover"]).size
  · rw [compile_roverAt, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (by simpa using hr), Option.getD_some,
      Array.getElem_map] at hy
    obtain ⟨h1, -, h3⟩ := mem_roverAt_entries (by simpa using hy)
    exact ⟨h1, by rw [h3]⟩
  · rw [compile_roverAt, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none_iff.2 (by simpa using Nat.le_of_not_lt hr),
      Option.getD_none] at hy
    simp at hy

open Planner.ExampleHeuristics.Rovers in
/-- The same, for a rover table taken from the array rather than by index. -/
theorem roverAt_mem_pred {t : Task} {facts : Array (Fact × Nat)}
    (hfacts : facts ∈ (compile t).roverAt) {y : Fact × Nat} (hy : y ∈ facts) :
    y.1 < t.factNames.size ∧ (t.factNames.getD y.1 default).pred = "at" := by
  rw [compile_roverAt] at hfacts
  obtain ⟨r, -, hval⟩ := Array.mem_map.mp hfacts
  subst hval
  obtain ⟨h1, -, h3⟩ := mem_roverAt_entries (by simpa using hy)
  exact ⟨h1, by rw [h3]⟩

open Planner.ExampleHeuristics.Rovers in
/-- Every `calibrated` fact of the table is numbered and uses `calibrated`. -/
theorem calibratedFacts_pred {t : Task} {f : Fact}
    (hf : f ∈ (compile t).calibratedFacts) :
    f < t.factNames.size ∧ (t.factNames.getD f default).pred = "calibrated" :=
  mem_factsWith_map (by rwa [compile_calibratedFacts] at hf)

open Planner.ExampleHeuristics.Rovers in
/-- Every `empty` fact of the table is numbered and uses `empty`. -/
theorem emptyFacts_pred {t : Task} {f : Fact}
    (hf : f ∈ (compile t).emptyFacts) :
    f < t.factNames.size ∧ (t.factNames.getD f default).pred = "empty" :=
  mem_factsWith_map (by rwa [compile_emptyFacts] at hf)

open Planner.ExampleHeuristics.Rovers in
/-- Every analysis fact of a soil goal is numbered and uses
`have_soil_analysis`. -/
theorem soilGoal_analysis_pred {t : Task} {g : SampleGoal}
    (hg : g ∈ (compile t).soilGoals) {f : Fact} (hf : f ∈ g.analysisFacts) :
    f < t.factNames.size ∧
      (t.factNames.getD f default).pred = "have_soil_analysis" := by
  rw [compile_soilGoals] at hg
  obtain ⟨x, -, hval⟩ := Array.mem_filterMap.mp hg
  obtain ⟨a, i⟩ := x
  dsimp only at hval
  split at hval
  · obtain ⟨wi, -, hval'⟩ := Option.map_eq_some_iff.mp hval
    subst hval'
    obtain ⟨h1, h2, -⟩ := mem_analysisOf (by simpa using hf)
    exact ⟨h1, h2⟩
  · simp at hval

open Planner.ExampleHeuristics.Rovers in
/-- And of a rock goal, `have_rock_analysis`. -/
theorem rockGoal_analysis_pred {t : Task} {g : SampleGoal}
    (hg : g ∈ (compile t).rockGoals) {f : Fact} (hf : f ∈ g.analysisFacts) :
    f < t.factNames.size ∧
      (t.factNames.getD f default).pred = "have_rock_analysis" := by
  rw [compile_rockGoals] at hg
  obtain ⟨x, -, hval⟩ := Array.mem_filterMap.mp hg
  obtain ⟨a, i⟩ := x
  dsimp only at hval
  split at hval
  · obtain ⟨wi, -, hval'⟩ := Option.map_eq_some_iff.mp hval
    subst hval'
    obtain ⟨h1, h2, -⟩ := mem_analysisOf (by simpa using hf)
    exact ⟨h1, h2⟩
  · simp at hval

open Planner.ExampleHeuristics.Rovers in
/-- And every picture fact of an image goal uses `have_image`. -/
theorem imageGoal_have_pred {t : Task} {g : ImageGoal}
    (hg : g ∈ (compile t).imageGoals) {f : Fact} (hf : f ∈ g.haveFacts) :
    f < t.factNames.size ∧ (t.factNames.getD f default).pred = "have_image" := by
  rw [compile_imageGoals] at hg
  obtain ⟨x, -, hval⟩ := Array.mem_filterMap.mp hg
  obtain ⟨a, i⟩ := x
  dsimp only at hval
  split at hval
  · simp only [Option.some.injEq] at hval
    subst hval
    obtain ⟨h1, r, h2⟩ := mem_haveFacts (by simpa using hf)
    exact ⟨h1, by rw [h2]⟩
  · simp at hval

/-! ### `Quiet`, assembled

Eight of the nine schemas leave every family the base count reads.  For the three
`communicate` schemas that is all of them, which is what makes their step a
`CommSoilStep`, `CommRockStep` or `CommImageStep` rather than a `ResourceStep`.
-/

private theorem any_congr {α : Type} (xs : Array α) (P Q : α → Bool)
    (h : ∀ y ∈ xs, P y = Q y) : xs.any P = xs.any Q := by
  rw [Bool.eq_iff_iff]
  simp only [Array.any_eq_true]
  constructor
  · rintro ⟨i, hi, hp⟩; exact ⟨i, hi, by rw [← h _ (Array.getElem_mem hi)]; exact hp⟩
  · rintro ⟨i, hi, hp⟩; exact ⟨i, hi, by rw [h _ (Array.getElem_mem hi)]; exact hp⟩

open Planner.ExampleHeuristics.Rovers in
/--
**A schema that touches none of the six families leaves all of them.**

The six are what `Quiet` names: the two analysis families, the pictures, the
`calibrated` and `empty` facts, and where the rovers stand.
-/
theorem quiet_of_untouched {d : Domain} {p : Problem} {rel : Bool} {o : AtomOp}
    (hf : OpFacts d p o)
    (hunt : ∀ a, (a ∈ hf.inst.add ∨ a ∈ hf.inst.del) →
      a.pred ≠ "have_soil_analysis" ∧ a.pred ≠ "have_rock_analysis" ∧
      a.pred ≠ "have_image" ∧ a.pred ≠ "calibrated" ∧ a.pred ≠ "empty" ∧
      a.pred ≠ "at")
    {s s' : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (habs' : Abstracts (ground d p rel) s' (o.applyA σ))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size) :
    Quiet (compile (ground d p rel)) s s' := by
  have frame : ∀ (P : Pddl.Name), (∀ a, (a ∈ hf.inst.add ∨ a ∈ hf.inst.del) →
      a.pred ≠ P) → ∀ {f : Fact}, f < (ground d p rel).factNames.size →
      ((ground d p rel).factNames.getD f default).pred = P →
      s'.test f = s.test f := by
    intro P hP f hlt hp
    exact test_frame_pred hf (fun a ha => hP a (Or.inl ha))
      (fun a ha => hP a (Or.inr ha)) habs habs' hn hlt hp
  refine
    { needsSoil := ?_, needsRock := ?_, imageHeld := ?_, calib := ?_, emptyF := ?_,
      pos := ?_, occ := ?_ }
  · intro g hg
    unfold needsSample
    rw [any_congr _ _ _ fun y hy => ?_]
    obtain ⟨h1, h2⟩ := soilGoal_analysis_pred hg hy
    exact frame _ (fun a ha => (hunt a ha).1) h1 h2
  · intro g hg
    unfold needsSample
    rw [any_congr _ _ _ fun y hy => ?_]
    obtain ⟨h1, h2⟩ := rockGoal_analysis_pred hg hy
    exact frame _ (fun a ha => (hunt a ha).2.1) h1 h2
  · intro g hg
    unfold hasImage
    rw [any_congr _ _ _ fun y hy => ?_]
    obtain ⟨h1, h2⟩ := imageGoal_have_pred hg hy
    exact frame _ (fun a ha => (hunt a ha).2.2.1) h1 h2
  · intro f hf'
    obtain ⟨h1, h2⟩ := calibratedFacts_pred hf'
    exact frame _ (fun a ha => (hunt a ha).2.2.2.1) h1 h2
  · intro f hf'
    obtain ⟨h1, h2⟩ := emptyFacts_pred hf'
    exact frame _ (fun a ha => (hunt a ha).2.2.2.2.1) h1 h2
  · intro r
    unfold roverFind
    refine array_find?_congr _ _ _ fun y hy => ?_
    obtain ⟨h1, h2⟩ := roverAt_pred hy
    exact frame _ (fun a ha => (hunt a ha).2.2.2.2.2) h1 h2
  · intro w
    unfold occupied
    refine any_congr _ _ _ fun facts hfacts => ?_
    refine any_congr _ _ _ fun y hy => ?_
    obtain ⟨h1, h2⟩ := roverAt_mem_pred hfacts hy
    rw [frame _ (fun a ha => (hunt a ha).2.2.2.2.2) h1 h2]

/-! ### The goal tables name each fact once

`frameSoil` says every soil goal *but* the one just met keeps its value.  That
needs two different entries to carry two different facts — otherwise the entry
"other than `q`" could be `q` under another name, and the frame would be false.
It holds because the problem's goal names each atom once.
-/

open Planner.ExampleHeuristics.Rovers in
/-- **Two soil entries with the same goal fact are the same entry.** -/
theorem soilGoals_goalFact_inj (hp : Pinned d p) (rel : Bool) :
    ∀ g ∈ (compile (ground d p rel)).soilGoals,
      ∀ q ∈ (compile (ground d p rel)).soilGoals, g.goalFact = q.goalFact → g = q := by
  intro g hg q hq heq
  rw [compile_soilGoals] at hg hq
  obtain ⟨x, hx, hval⟩ := Array.mem_filterMap.mp hg
  obtain ⟨z, hz, hval'⟩ := Array.mem_filterMap.mp hq
  obtain ⟨-, hlt, hget⟩ := Array.mem_zipIdx hx
  obtain ⟨-, hlt', hget'⟩ := Array.mem_zipIdx hz
  simp only [Nat.zero_add, Nat.sub_zero] at hlt hget hlt' hget'
  obtain ⟨a, i⟩ := x
  obtain ⟨b, j⟩ := z
  dsimp only at hval hval' hlt hget hlt' hget'
  -- Each entry's goal fact is read at its own goal position.
  have hgf : g.goalFact = (ground d p rel).goal.getD i 0 := by
    split at hval
    · obtain ⟨wi, -, h'⟩ := Option.map_eq_some_iff.mp hval; subst h'; rfl
    · simp at hval
  have hqf : q.goalFact = (ground d p rel).goal.getD j 0 := by
    split at hval'
    · obtain ⟨wi, -, h'⟩ := Option.map_eq_some_iff.mp hval'; subst h'; rfl
    · simp at hval'
  -- Equal facts name equal goal atoms.
  have hatoms : (ground d p rel).goalAtoms[i]'hlt
      = (ground d p rel).goalAtoms[j]'hlt' := by
    obtain ⟨hn1, -⟩ := goal_name_eq d p rel hlt
    obtain ⟨hn2, -⟩ := goal_name_eq d p rel hlt'
    rw [← hn1, ← hn2, ← hgf, ← hqf, heq]
  -- And the problem's goal names each atom once, so the positions agree.
  have hnd : (ground d p rel).goalAtoms.toList.Nodup := by
    rw [taskOf_goalAtoms]; simpa using hp.goalNodup
  have hij : i = j :=
    (List.Nodup.getElem_inj_iff hnd (hi := by simpa using hlt)
      (hj := by simpa using hlt')).mp (by simpa using hatoms)
  subst hij
  have hab : a = b := hget.trans hget'.symm
  subst hab
  rw [hval] at hval'
  simpa using hval'


open Planner.ExampleHeuristics.Rovers in
/-- **Two rock entries with the same goal fact are the same entry.** -/
theorem rockGoals_goalFact_inj (hp : Pinned d p) (rel : Bool) :
    ∀ g ∈ (compile (ground d p rel)).rockGoals,
      ∀ q ∈ (compile (ground d p rel)).rockGoals, g.goalFact = q.goalFact → g = q := by
  intro g hg q hq heq
  rw [compile_rockGoals] at hg hq
  obtain ⟨x, hx, hval⟩ := Array.mem_filterMap.mp hg
  obtain ⟨z, hz, hval'⟩ := Array.mem_filterMap.mp hq
  obtain ⟨-, hlt, hget⟩ := Array.mem_zipIdx hx
  obtain ⟨-, hlt', hget'⟩ := Array.mem_zipIdx hz
  simp only [Nat.zero_add, Nat.sub_zero] at hlt hget hlt' hget'
  obtain ⟨a, i⟩ := x
  obtain ⟨b, j⟩ := z
  dsimp only at hval hval' hlt hget hlt' hget'
  have hgf : g.goalFact = (ground d p rel).goal.getD i 0 := by
    split at hval
    · obtain ⟨wi, -, h'⟩ := Option.map_eq_some_iff.mp hval; subst h'; rfl
    · simp at hval
  have hqf : q.goalFact = (ground d p rel).goal.getD j 0 := by
    split at hval'
    · obtain ⟨wi, -, h'⟩ := Option.map_eq_some_iff.mp hval'; subst h'; rfl
    · simp at hval'
  have hatoms : (ground d p rel).goalAtoms[i]'hlt
      = (ground d p rel).goalAtoms[j]'hlt' := by
    obtain ⟨hn1, -⟩ := goal_name_eq d p rel hlt
    obtain ⟨hn2, -⟩ := goal_name_eq d p rel hlt'
    rw [← hn1, ← hn2, ← hgf, ← hqf, heq]
  have hnd : (ground d p rel).goalAtoms.toList.Nodup := by
    rw [taskOf_goalAtoms]; simpa using hp.goalNodup
  have hij : i = j :=
    (List.Nodup.getElem_inj_iff hnd (hi := by simpa using hlt)
      (hj := by simpa using hlt')).mp (by simpa using hatoms)
  subst hij
  have hab : a = b := hget.trans hget'.symm
  subst hab
  rw [hval] at hval'
  simpa using hval'

open Planner.ExampleHeuristics.Rovers in
/-- **Two image entries with the same goal fact are the same entry.** -/
theorem imageGoals_goalFact_inj (hp : Pinned d p) (rel : Bool) :
    ∀ g ∈ (compile (ground d p rel)).imageGoals,
      ∀ q ∈ (compile (ground d p rel)).imageGoals, g.goalFact = q.goalFact → g = q := by
  intro g hg q hq heq
  rw [compile_imageGoals] at hg hq
  obtain ⟨x, hx, hval⟩ := Array.mem_filterMap.mp hg
  obtain ⟨z, hz, hval'⟩ := Array.mem_filterMap.mp hq
  obtain ⟨-, hlt, hget⟩ := Array.mem_zipIdx hx
  obtain ⟨-, hlt', hget'⟩ := Array.mem_zipIdx hz
  simp only [Nat.zero_add, Nat.sub_zero] at hlt hget hlt' hget'
  obtain ⟨a, i⟩ := x
  obtain ⟨b, j⟩ := z
  dsimp only at hval hval' hlt hget hlt' hget'
  have hgf : g.goalFact = (ground d p rel).goal.getD i 0 := by
    split at hval
    · simp only [Option.some.injEq] at hval; subst hval; rfl
    · simp at hval
  have hqf : q.goalFact = (ground d p rel).goal.getD j 0 := by
    split at hval'
    · simp only [Option.some.injEq] at hval'; subst hval'; rfl
    · simp at hval'
  have hatoms : (ground d p rel).goalAtoms[i]'hlt
      = (ground d p rel).goalAtoms[j]'hlt' := by
    obtain ⟨hn1, -⟩ := goal_name_eq d p rel hlt
    obtain ⟨hn2, -⟩ := goal_name_eq d p rel hlt'
    rw [← hn1, ← hn2, ← hgf, ← hqf, heq]
  have hnd : (ground d p rel).goalAtoms.toList.Nodup := by
    rw [taskOf_goalAtoms]; simpa using hp.goalNodup
  have hij : i = j :=
    (List.Nodup.getElem_inj_iff hnd (hi := by simpa using hlt)
      (hj := by simpa using hlt')).mp (by simpa using hatoms)
  subst hij
  have hab : a = b := hget.trans hget'.symm
  subst hab
  rw [hval] at hval'
  simpa using hval'
open Planner.ExampleHeuristics.Rovers in
/-- **A soil goal's analysis table is the one for its own waypoint.**  This is
what ties the precondition a `communicate` reads to the facts `needsSample`
looks at. -/
theorem soilGoal_analysis_eq (d : Domain) (p : Problem) (rel : Bool) :
    ∀ g ∈ (compile (ground d p rel)).soilGoals, ∀ w : Pddl.Name,
      (ground d p rel).factNames.getD g.goalFact default
        = { pred := "communicated_soil_data", args := [w] } →
      g.analysisFacts = ((ground d p rel).factsWith "have_soil_analysis").filterMap
        fun z => match z.2.args with
                 | [_, u] => if u == w then some z.1 else none
                 | _ => none := by
  intro g hg w hw
  rw [compile_soilGoals] at hg
  obtain ⟨x, hx, hval⟩ := Array.mem_filterMap.mp hg
  obtain ⟨-, hlt, hget⟩ := Array.mem_zipIdx hx
  simp only [Nat.zero_add, Nat.sub_zero] at hlt hget
  obtain ⟨a, i⟩ := x
  dsimp only at hval hlt hget
  split at hval
  · rename_i w' h1 h2
    obtain ⟨wi, -, hval'⟩ := Option.map_eq_some_iff.mp hval
    subst hval'
    -- The entry's atom is `communicated_soil_data(w')`, and `hw` says it is `w`.
    obtain ⟨hname, -⟩ := goal_name_eq d p rel hlt
    have hatom : (ground d p rel).factNames.getD
        ((ground d p rel).goal.getD i 0) default
        = { pred := "communicated_soil_data", args := [w'] } := by
      rw [hname, ← h1, ← h2]
      exact hget.symm
    have : w' = w := by
      have := hatom.symm.trans hw
      simpa using this
    rw [this]
  · simp at hval

open Planner.ExampleHeuristics.Rovers in
/-- A soil goal's stored waypoint is the index of the waypoint named by its goal. -/
theorem soilGoal_waypoint_eq (d : Domain) (p : Problem) (rel : Bool) :
    ∀ g ∈ (compile (ground d p rel)).soilGoals, ∀ w : Pddl.Name,
      (ground d p rel).factNames.getD g.goalFact default
        = { pred := "communicated_soil_data", args := [w] } →
      ((ground d p rel).objectsOfTypes ["waypoint"]).findIdx? (· == w)
        = some g.waypoint := by
  intro g hg w hw
  rw [compile_soilGoals] at hg
  obtain ⟨x, hx, hval⟩ := Array.mem_filterMap.mp hg
  obtain ⟨-, hlt, hget⟩ := Array.mem_zipIdx hx
  simp only [Nat.zero_add, Nat.sub_zero] at hlt hget
  obtain ⟨a, i⟩ := x
  dsimp only at hval hlt hget
  split at hval
  · rename_i w' h1 h2
    obtain ⟨wi, hidx, hval'⟩ := Option.map_eq_some_iff.mp hval
    subst hval'
    obtain ⟨hname, -⟩ := goal_name_eq d p rel hlt
    have hatom : (ground d p rel).factNames.getD
        ((ground d p rel).goal.getD i 0) default
        = { pred := "communicated_soil_data", args := [w'] } := by
      rw [hname, ← h1, ← h2]
      exact hget.symm
    have : w' = w := by
      have := hatom.symm.trans hw
      simpa using this
    simpa [this] using hidx
  · simp at hval

open Planner.ExampleHeuristics.Rovers in
/-- A rock goal's analysis table is the one for its own waypoint. -/
theorem rockGoal_analysis_eq (d : Domain) (p : Problem) (rel : Bool) :
    ∀ g ∈ (compile (ground d p rel)).rockGoals, ∀ w : Pddl.Name,
      (ground d p rel).factNames.getD g.goalFact default
        = { pred := "communicated_rock_data", args := [w] } →
      g.analysisFacts = ((ground d p rel).factsWith "have_rock_analysis").filterMap
        fun z => match z.2.args with
                 | [_, u] => if u == w then some z.1 else none
                 | _ => none := by
  intro g hg w hw
  rw [compile_rockGoals] at hg
  obtain ⟨x, hx, hval⟩ := Array.mem_filterMap.mp hg
  obtain ⟨-, hlt, hget⟩ := Array.mem_zipIdx hx
  simp only [Nat.zero_add, Nat.sub_zero] at hlt hget
  obtain ⟨a, i⟩ := x
  dsimp only at hval hlt hget
  split at hval
  · rename_i w' h1 h2
    obtain ⟨wi, -, hval'⟩ := Option.map_eq_some_iff.mp hval
    subst hval'
    obtain ⟨hname, -⟩ := goal_name_eq d p rel hlt
    have hatom : (ground d p rel).factNames.getD
        ((ground d p rel).goal.getD i 0) default
        = { pred := "communicated_rock_data", args := [w'] } := by
      rw [hname, ← h1, ← h2]
      exact hget.symm
    have : w' = w := by
      have := hatom.symm.trans hw
      simpa using this
    rw [this]
  · simp at hval

open Planner.ExampleHeuristics.Rovers in
/-- A rock goal's stored waypoint is the index of the waypoint named by its goal. -/
theorem rockGoal_waypoint_eq (d : Domain) (p : Problem) (rel : Bool) :
    ∀ g ∈ (compile (ground d p rel)).rockGoals, ∀ w : Pddl.Name,
      (ground d p rel).factNames.getD g.goalFact default
        = { pred := "communicated_rock_data", args := [w] } →
      ((ground d p rel).objectsOfTypes ["waypoint"]).findIdx? (· == w)
        = some g.waypoint := by
  intro g hg w hw
  rw [compile_rockGoals] at hg
  obtain ⟨x, hx, hval⟩ := Array.mem_filterMap.mp hg
  obtain ⟨-, hlt, hget⟩ := Array.mem_zipIdx hx
  simp only [Nat.zero_add, Nat.sub_zero] at hlt hget
  obtain ⟨a, i⟩ := x
  dsimp only at hval hlt hget
  split at hval
  · rename_i w' h1 h2
    obtain ⟨wi, hidx, hval'⟩ := Option.map_eq_some_iff.mp hval
    subst hval'
    obtain ⟨hname, -⟩ := goal_name_eq d p rel hlt
    have hatom : (ground d p rel).factNames.getD
        ((ground d p rel).goal.getD i 0) default
        = { pred := "communicated_rock_data", args := [w'] } := by
      rw [hname, ← h1, ← h2]
      exact hget.symm
    have : w' = w := by
      have := hatom.symm.trans hw
      simpa using this
    simpa [this] using hidx
  · simp at hval

/-- **A numbered `have_image(r, o, m)` fact is in the picture table of `(o, m)`.** -/
theorem mem_haveFacts_of {t : Task} {ob m r : Pddl.Name} {f : Fact}
    (hlt : f < t.factNames.size)
    (hname : t.factNames.getD f default
      = { pred := "have_image", args := [r, ob, m] }) :
    f ∈ (t.factsWith "have_image").filterMap fun x =>
      match x.2.args with
      | [_, u, v] => if u == ob && v == m then some x.1 else none
      | _ => none := by
  refine Array.mem_filterMap.mpr ⟨(f, { pred := "have_image", args := [r, ob, m] }),
    mem_factsWith_of_named hlt hname rfl, ?_⟩
  show (match ({ pred := "have_image", args := [r, ob, m] } : GroundAtom).args with
    | [_, u, v] => if u == ob && v == m then some f else none
    | _ => none) = some f
  simp

open Planner.ExampleHeuristics.Rovers in
/-- And so a held picture makes `hasImage` true. -/
theorem hasImage_true {t : Task} {s : State} {g : ImageGoal} {ob m r : Pddl.Name}
    {f : Fact}
    (hg : g.haveFacts = (t.factsWith "have_image").filterMap fun x =>
      match x.2.args with
      | [_, u, v] => if u == ob && v == m then some x.1 else none
      | _ => none)
    (hlt : f < t.factNames.size)
    (hname : t.factNames.getD f default
      = { pred := "have_image", args := [r, ob, m] })
    (htrue : s.test f = true) : hasImage s g = true := by
  unfold hasImage
  rw [hg]
  simp only [Array.any_eq_true]
  obtain ⟨i, hi, hget⟩ := Array.getElem_of_mem (mem_haveFacts_of hlt hname)
  exact ⟨i, hi, by rw [hget]; exact htrue⟩

open Planner.ExampleHeuristics.Rovers in
/-- An image goal's picture table is the one for its own objective and mode. -/
theorem imageGoal_have_eq (d : Domain) (p : Problem) (rel : Bool) :
    ∀ g ∈ (compile (ground d p rel)).imageGoals, ∀ ob m : Pddl.Name,
      (ground d p rel).factNames.getD g.goalFact default
        = { pred := "communicated_image_data", args := [ob, m] } →
      g.haveFacts = ((ground d p rel).factsWith "have_image").filterMap
        fun z => match z.2.args with
                 | [_, u, v] => if u == ob && v == m then some z.1 else none
                 | _ => none := by
  intro g hg ob m hw
  rw [compile_imageGoals] at hg
  obtain ⟨x, hx, hval⟩ := Array.mem_filterMap.mp hg
  obtain ⟨-, hlt, hget⟩ := Array.mem_zipIdx hx
  simp only [Nat.zero_add, Nat.sub_zero] at hlt hget
  obtain ⟨a, i⟩ := x
  dsimp only at hval hlt hget
  split at hval
  · rename_i ob' m' h1 h2
    simp only [Option.some.injEq] at hval
    subst hval
    obtain ⟨hname, -⟩ := goal_name_eq d p rel hlt
    have hatom : (ground d p rel).factNames.getD
        ((ground d p rel).goal.getD i 0) default
        = { pred := "communicated_image_data", args := [ob', m'] } := by
      rw [hname, ← h1, ← h2]
      exact hget.symm
    obtain ⟨rfl, rfl⟩ : ob' = ob ∧ m' = m := by
      have := hatom.symm.trans hw
      simpa using this
    rfl
  · simp at hval

/-! ### A `communicate` really asserts its atom

On the unpruned task the add survives grounding, because the atom is not already
a precondition — the preconditions are `at`, `at_lander`, the analysis, and
`visible`, none of which is a `communicated_*`.
-/

open Planner.ExampleHeuristics.Rovers in
/-- `communicate_soil_data` asserts its atom. -/
theorem commSoil_adds {d : Domain} {p : Problem} {o : AtomOp}
    (hfa : OpFactsAdd d p o) {r l q x y : Pddl.Name}
    (hs : hfa.inst.schema = commSoilA) (hargs : hfa.inst.args = [r, l, q, x, y])
    (σ : AtomState) : o.applyA σ (commSoil q) = true := by
  have hinst : instAtom hfa.inst.schema.params hfa.inst.args (commSoilV "?p")
      = commSoil q := by rw [hs, hargs]; rfl
  have hpre : hfa.inst.pre = [at_ r x, { pred := "at_lander", args := [l, y] },
      haveSoil r q, { pred := "visible", args := [x, y] }] := by
    rw [Pddl.Instance.pre_eq, hs, hargs]; rfl
  have hnp : instAtom hfa.inst.schema.params hfa.inst.args (commSoilV "?p") ∉ o.pre := by
    rw [hinst]
    intro hmem
    have h := hfa.subPre _ hmem
    rw [hpre] at h
    simp [commSoil, at_, haveSoil] at h
  have h := asserted_of_lists hfa (y := commSoilV "?p")
    (by rw [hs]; simp [commSoilA]) hnp σ
  rwa [hinst] at h

open Planner.ExampleHeuristics.Rovers in
/-- `communicate_rock_data` asserts its atom. -/
theorem commRock_adds {d : Domain} {p : Problem} {o : AtomOp}
    (hfa : OpFactsAdd d p o) {r l q x y : Pddl.Name}
    (hs : hfa.inst.schema = commRockA) (hargs : hfa.inst.args = [r, l, q, x, y])
    (σ : AtomState) : o.applyA σ (commRock q) = true := by
  have hinst : instAtom hfa.inst.schema.params hfa.inst.args (commRockV "?p")
      = commRock q := by rw [hs, hargs]; rfl
  have hpre : hfa.inst.pre = [at_ r x, { pred := "at_lander", args := [l, y] },
      haveRock r q, { pred := "visible", args := [x, y] }] := by
    rw [Pddl.Instance.pre_eq, hs, hargs]; rfl
  have hnp : instAtom hfa.inst.schema.params hfa.inst.args (commRockV "?p") ∉ o.pre := by
    rw [hinst]
    intro hmem
    have h := hfa.subPre _ hmem
    rw [hpre] at h
    simp [commRock, at_, haveRock] at h
  have h := asserted_of_lists hfa (y := commRockV "?p")
    (by rw [hs]; simp [commRockA]) hnp σ
  rwa [hinst] at h

open Planner.ExampleHeuristics.Rovers in
/-- `communicate_image_data` asserts its atom. -/
theorem commImage_adds {d : Domain} {p : Problem} {o : AtomOp}
    (hfa : OpFactsAdd d p o) {r l ob m x y : Pddl.Name}
    (hs : hfa.inst.schema = commImageA) (hargs : hfa.inst.args = [r, l, ob, m, x, y])
    (σ : AtomState) : o.applyA σ (commImage ob m) = true := by
  have hinst : instAtom hfa.inst.schema.params hfa.inst.args (commImageV "?o" "?m")
      = commImage ob m := by rw [hs, hargs]; rfl
  have hpre : hfa.inst.pre = [at_ r x, { pred := "at_lander", args := [l, y] },
      haveImage r ob m, { pred := "visible", args := [x, y] }] := by
    rw [Pddl.Instance.pre_eq, hs, hargs]; rfl
  have hnp : instAtom hfa.inst.schema.params hfa.inst.args (commImageV "?o" "?m")
      ∉ o.pre := by
    rw [hinst]
    intro hmem
    have h := hfa.subPre _ hmem
    rw [hpre] at h
    simp [commImage, at_, haveImage] at h
  have h := asserted_of_lists hfa (y := commImageV "?o" "?m")
    (by rw [hs]; simp [commImageA]) hnp σ
  rwa [hinst] at h

/-! ### What atom each goal fact names

The step proof has to compare the atom a `communicate` adds with the goal facts
the tables hold: that comparison is what decides whether the step meets a goal
the heuristic is counting.
-/

open Planner.ExampleHeuristics.Rovers in
/-- Every soil goal's fact names `communicated_soil_data` of some waypoint. -/
theorem soilGoals_name (d : Domain) (p : Problem) (rel : Bool) :
    ∀ g ∈ (compile (ground d p rel)).soilGoals,
      g.goalFact < (ground d p rel).factNames.size ∧
      ∃ w, (ground d p rel).factNames.getD g.goalFact default
        = { pred := "communicated_soil_data", args := [w] } := by
  intro g hg
  rw [compile_soilGoals] at hg
  obtain ⟨x, hx, hval⟩ := Array.mem_filterMap.mp hg
  obtain ⟨-, hlt, hget⟩ := Array.mem_zipIdx hx
  simp only [Nat.zero_add, Nat.sub_zero] at hlt hget
  obtain ⟨a, i⟩ := x
  dsimp only at hval hlt hget
  split at hval
  · rename_i w h1 h2
    obtain ⟨wi, -, hval'⟩ := Option.map_eq_some_iff.mp hval
    subst hval'
    obtain ⟨hname, hfsz⟩ := goal_name_eq d p rel hlt
    refine ⟨hfsz, w, ?_⟩
    show (ground d p rel).factNames.getD ((ground d p rel).goal.getD i 0) default = _
    rw [hname, ← h1, ← h2]
    exact hget.symm
  · simp at hval

open Planner.ExampleHeuristics.Rovers in
/-- Every rock goal's fact names `communicated_rock_data`. -/
theorem rockGoals_name (d : Domain) (p : Problem) (rel : Bool) :
    ∀ g ∈ (compile (ground d p rel)).rockGoals,
      g.goalFact < (ground d p rel).factNames.size ∧
      ∃ w, (ground d p rel).factNames.getD g.goalFact default
        = { pred := "communicated_rock_data", args := [w] } := by
  intro g hg
  rw [compile_rockGoals] at hg
  obtain ⟨x, hx, hval⟩ := Array.mem_filterMap.mp hg
  obtain ⟨-, hlt, hget⟩ := Array.mem_zipIdx hx
  simp only [Nat.zero_add, Nat.sub_zero] at hlt hget
  obtain ⟨a, i⟩ := x
  dsimp only at hval hlt hget
  split at hval
  · rename_i w h1 h2
    obtain ⟨wi, -, hval'⟩ := Option.map_eq_some_iff.mp hval
    subst hval'
    obtain ⟨hname, hfsz⟩ := goal_name_eq d p rel hlt
    refine ⟨hfsz, w, ?_⟩
    show (ground d p rel).factNames.getD ((ground d p rel).goal.getD i 0) default = _
    rw [hname, ← h1, ← h2]
    exact hget.symm
  · simp at hval

open Planner.ExampleHeuristics.Rovers in
/-- Every image goal's fact names `communicated_image_data`. -/
theorem imageGoals_name (d : Domain) (p : Problem) (rel : Bool) :
    ∀ g ∈ (compile (ground d p rel)).imageGoals,
      g.goalFact < (ground d p rel).factNames.size ∧
      ∃ ob m, (ground d p rel).factNames.getD g.goalFact default
        = { pred := "communicated_image_data", args := [ob, m] } := by
  intro g hg
  rw [compile_imageGoals] at hg
  obtain ⟨x, hx, hval⟩ := Array.mem_filterMap.mp hg
  obtain ⟨-, hlt, hget⟩ := Array.mem_zipIdx hx
  simp only [Nat.zero_add, Nat.sub_zero] at hlt hget
  obtain ⟨a, i⟩ := x
  dsimp only at hval hlt hget
  split at hval
  · rename_i ob m h1 h2
    simp only [Option.some.injEq] at hval
    subst hval
    obtain ⟨hname, hfsz⟩ := goal_name_eq d p rel hlt
    refine ⟨hfsz, ob, m, ?_⟩
    show (ground d p rel).factNames.getD ((ground d p rel).goal.getD i 0) default = _
    rw [hname, ← h1, ← h2]
    exact hget.symm
  · simp at hval

open Planner.ExampleHeuristics.Rovers in
/-- Two soil goals stored at the same waypoint are the same table entry. -/
theorem soilGoals_waypoint_inj (hp : Pinned d p) (rel : Bool) :
    ∀ g ∈ (compile (ground d p rel)).soilGoals,
      ∀ q ∈ (compile (ground d p rel)).soilGoals, g.waypoint = q.waypoint → g = q := by
  intro g hg q hq hwp
  obtain ⟨hglt, w, hgname⟩ := soilGoals_name d p rel g hg
  obtain ⟨hqlt, w', hqname⟩ := soilGoals_name d p rel q hq
  have hgidx := soilGoal_waypoint_eq d p rel g hg w hgname
  have hqidx := soilGoal_waypoint_eq d p rel q hq w' hqname
  rw [← hwp] at hqidx
  obtain ⟨-, hgw⟩ := findIdx_sound hgidx
  obtain ⟨-, hqw⟩ := findIdx_sound hqidx
  have hww : w = w' := hgw.symm.trans hqw
  have hgf : g.goalFact = q.goalFact :=
    factNames_inj hglt hqlt (by rw [hgname, hqname, hww])
  exact soilGoals_goalFact_inj hp rel g hg q hq hgf

open Planner.ExampleHeuristics.Rovers in
/-- Two rock goals stored at the same waypoint are the same table entry. -/
theorem rockGoals_waypoint_inj (hp : Pinned d p) (rel : Bool) :
    ∀ g ∈ (compile (ground d p rel)).rockGoals,
      ∀ q ∈ (compile (ground d p rel)).rockGoals, g.waypoint = q.waypoint → g = q := by
  intro g hg q hq hwp
  obtain ⟨hglt, w, hgname⟩ := rockGoals_name d p rel g hg
  obtain ⟨hqlt, w', hqname⟩ := rockGoals_name d p rel q hq
  have hgidx := rockGoal_waypoint_eq d p rel g hg w hgname
  have hqidx := rockGoal_waypoint_eq d p rel q hq w' hqname
  rw [← hwp] at hqidx
  obtain ⟨-, hgw⟩ := findIdx_sound hgidx
  obtain ⟨-, hqw⟩ := findIdx_sound hqidx
  have hww : w = w' := hgw.symm.trans hqw
  have hgf : g.goalFact = q.goalFact :=
    factNames_inj hglt hqlt (by rw [hgname, hqname, hww])
  exact rockGoals_goalFact_inj hp rel g hg q hq hgf

/-! ### The other direction: the table holds every such fact

`hasData` says the analysis a `communicate` announces is really in hand.  The
precondition gives the atom; this says the goal's table holds its fact, so the
`needsSample` test really does see it.
-/

/-- **A numbered `pred(r, w)` fact is in the analysis table of `w`.** -/
theorem mem_analysisOf_of {t : Task} {pred w r : Pddl.Name} {f : Fact}
    (hlt : f < t.factNames.size)
    (hname : t.factNames.getD f default = { pred := pred, args := [r, w] }) :
    f ∈ (t.factsWith pred).filterMap fun x =>
      match x.2.args with
      | [_, z] => if z == w then some x.1 else none
      | _ => none := by
  refine Array.mem_filterMap.mpr ⟨(f, { pred := pred, args := [r, w] }),
    mem_factsWith_of_named hlt hname rfl, ?_⟩
  show (match ({ pred := pred, args := [r, w] } : GroundAtom).args with
    | [_, z] => if z == w then some f else none
    | _ => none) = some f
  simp

open Planner.ExampleHeuristics.Rovers in
/-- And so a held analysis makes `needsSample` false. -/
theorem needsSample_false {t : Task} {s : State} {g : SampleGoal}
    {pred w r : Pddl.Name} {f : Fact}
    (hg : g.analysisFacts = (t.factsWith pred).filterMap fun x =>
      match x.2.args with
      | [_, z] => if z == w then some x.1 else none
      | _ => none)
    (hlt : f < t.factNames.size)
    (hname : t.factNames.getD f default = { pred := pred, args := [r, w] })
    (htrue : s.test f = true) : needsSample s g = false := by
  unfold needsSample
  simp only [Bool.not_eq_false']
  rw [hg]
  simp only [Array.any_eq_true]
  obtain ⟨i, hi, hget⟩ := Array.getElem_of_mem (mem_analysisOf_of hlt hname)
  exact ⟨i, hi, by rw [hget]; exact htrue⟩

/-! ### A schema that adds one atom

All three `communicate` schemas add exactly one atom and delete nothing.  So
every fact but the one that atom names keeps its value, and the goal tables move
only where the added atom is a goal they hold.
-/

open Planner.ExampleHeuristics.Rovers in
/-- Every fact but the one the added atom names keeps its value. -/
theorem addOne_frame {d : Domain} {p : Problem} {rel : Bool} {o : AtomOp}
    (hf : OpFacts d p o) {A : GroundAtom}
    (hadd : hf.inst.add = [A]) (hdel : hf.inst.del = [])
    {s s' : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (habs' : Abstracts (ground d p rel) s' (o.applyA σ))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    {f : Fact} (hlt : f < (ground d p rel).factNames.size)
    (hne : (ground d p rel).factNames.getD f default ≠ A) :
    s'.test f = s.test f := by
  rw [← habs'.numbered f (by rw [hn]; exact hlt),
    ← habs.numbered f (by rw [hn]; exact hlt)]
  exact frame_of_lists hf hadd hdel (by simpa using hne) (by simp) σ

open Planner.ExampleHeuristics.Rovers in
/-- **And so the goal tables do not move**, when the added atom is none of the
goals they hold. -/
theorem goalsFixed_of_ne {d : Domain} {p : Problem} {rel : Bool} {o : AtomOp}
    (hf : OpFacts d p o) {A : GroundAtom}
    (hadd : hf.inst.add = [A]) (hdel : hf.inst.del = [])
    {s s' : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (habs' : Abstracts (ground d p rel) s' (o.applyA σ))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (h1 : ∀ g ∈ (compile (ground d p rel)).soilGoals,
      (ground d p rel).factNames.getD g.goalFact default ≠ A)
    (h2 : ∀ g ∈ (compile (ground d p rel)).rockGoals,
      (ground d p rel).factNames.getD g.goalFact default ≠ A)
    (h3 : ∀ g ∈ (compile (ground d p rel)).imageGoals,
      (ground d p rel).factNames.getD g.goalFact default ≠ A) :
    GoalsFixed (compile (ground d p rel)) s s' where
  soil g hg :=
    addOne_frame hf hadd hdel habs habs' hn (soilGoals_name d p rel g hg).1 (h1 g hg)
  rock g hg :=
    addOne_frame hf hadd hdel habs habs' hn (rockGoals_name d p rel g hg).1 (h2 g hg)
  image g hg :=
    addOne_frame hf hadd hdel habs habs' hn (imageGoals_name d p rel g hg).1 (h3 g hg)

open Planner.ExampleHeuristics.Rovers in
/--
**A quiet step whose goals do not move is a `ResourceStep`.**

Nothing the base count reads has moved, so it has not moved either — which is
more than `baseDrop` asks for.  This is the case a `communicate` falls into when
the goal it announces is not one the tables are counting.
-/
theorem resourceStep_of_quiet {dd : ExampleHeuristics.Rovers.Data} {s s' : State}
    (hq : Quiet dd s s') (hg : GoalsFixed dd s s') : ResourceStep dd s s' where
  goals := hg
  RcLe := by
    rw [Rc_congr (hq.soilSame hg.soil) (hq.rockSame hg.rock) hq.pos hq.occ]
  baseDrop := by
    rw [Bc_congr hg.soil hg.rock hg.image hq.needsSoil hq.needsRock hq.imageHeld
      hq.calib hq.emptyF]
    omega

open Planner.ExampleHeuristics.Rovers in
/-- A schema that deletes nothing can only make facts truer. -/
theorem addOne_mono {d : Domain} {p : Problem} {rel : Bool} {o : AtomOp}
    (hf : OpFacts d p o) (hdel : hf.inst.del = [])
    {s s' : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (habs' : Abstracts (ground d p rel) s' (o.applyA σ))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    {f : Fact} (hlt : f < (ground d p rel).factNames.size)
    (htrue : s.test f = true) : s'.test f = true := by
  rw [← habs'.numbered f (by rw [hn]; exact hlt)]
  by_cases hmem : (ground d p rel).factNames.getD f default ∈ o.add
  · exact applyA_add σ hmem
  · rw [applyA_frame σ hmem (fun hc => by
      have hin := hf.subDel _ hc
      rw [hdel] at hin
      simp at hin)]
    rw [← habs.numbered f (by rw [hn]; exact hlt)] at htrue
    exact htrue

open Planner.ExampleHeuristics.Rovers in
/--
**The goal tables do not move**, when every goal they hold either is not the
atom the step announces or was already true.

The second case is why this replaces the earlier `goalsFixed_of_ne`: a
`communicate` may re-announce a goal that is already met, and then the fact does
not move either — but its atom *is* the announced one.
-/
theorem goalsFixed_of {d : Domain} {p : Problem} {rel : Bool} {o : AtomOp}
    (hf : OpFacts d p o) {A : GroundAtom}
    (hadd : hf.inst.add = [A]) (hdel : hf.inst.del = [])
    {s s' : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (habs' : Abstracts (ground d p rel) s' (o.applyA σ))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (h1 : ∀ g ∈ (compile (ground d p rel)).soilGoals,
      (ground d p rel).factNames.getD g.goalFact default ≠ A ∨
        s.test g.goalFact = true)
    (h2 : ∀ g ∈ (compile (ground d p rel)).rockGoals,
      (ground d p rel).factNames.getD g.goalFact default ≠ A ∨
        s.test g.goalFact = true)
    (h3 : ∀ g ∈ (compile (ground d p rel)).imageGoals,
      (ground d p rel).factNames.getD g.goalFact default ≠ A ∨
        s.test g.goalFact = true) :
    GoalsFixed (compile (ground d p rel)) s s' := by
  refine { soil := fun g hg => ?_, rock := fun g hg => ?_, image := fun g hg => ?_ }
  · rcases h1 g hg with hne | htr
    · exact addOne_frame hf hadd hdel habs habs' hn (soilGoals_name d p rel g hg).1 hne
    · rw [htr, addOne_mono hf hdel habs habs' hn (soilGoals_name d p rel g hg).1 htr]
  · rcases h2 g hg with hne | htr
    · exact addOne_frame hf hadd hdel habs habs' hn (rockGoals_name d p rel g hg).1 hne
    · rw [htr, addOne_mono hf hdel habs habs' hn (rockGoals_name d p rel g hg).1 htr]
  · rcases h3 g hg with hne | htr
    · exact addOne_frame hf hadd hdel habs habs' hn (imageGoals_name d p rel g hg).1 hne
    · rw [htr, addOne_mono hf hdel habs habs' hn (imageGoals_name d p rel g hg).1 htr]

/-! ### The three `communicate` schemas are quiet

Each adds one atom of its own goal family and deletes nothing, so none of the six
families `Quiet` names can move.
-/

variable {d : Domain} {p : Problem} {rel : Bool} {o : AtomOp}
variable {s s' : State} {σ : AtomState}

open Planner.ExampleHeuristics.Rovers in
/-- `communicate_soil_data` leaves every family `Quiet` names. -/
theorem commSoil_quiet (hf : OpFacts d p o) {r l q x y : Pddl.Name}
    (hs : hf.inst.schema = commSoilA) (hargs : hf.inst.args = [r, l, q, x, y])
    (habs : Abstracts (ground d p rel) s σ)
    (habs' : Abstracts (ground d p rel) s' (o.applyA σ))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size) :
    Quiet (compile (ground d p rel)) s s' :=
  quiet_of_untouched hf (fun a ha => by
    rw [commSoil_touches hf.inst hs hargs ha]
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩)
    habs habs' hn

open Planner.ExampleHeuristics.Rovers in
/-- And `communicate_rock_data`. -/
theorem commRock_quiet (hf : OpFacts d p o) {r l q x y : Pddl.Name}
    (hs : hf.inst.schema = commRockA) (hargs : hf.inst.args = [r, l, q, x, y])
    (habs : Abstracts (ground d p rel) s σ)
    (habs' : Abstracts (ground d p rel) s' (o.applyA σ))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size) :
    Quiet (compile (ground d p rel)) s s' :=
  quiet_of_untouched hf (fun a ha => by
    rw [commRock_touches hf.inst hs hargs ha]
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩)
    habs habs' hn

open Planner.ExampleHeuristics.Rovers in
/-- And `communicate_image_data`. -/
theorem commImage_quiet (hf : OpFacts d p o) {r l ob m x y : Pddl.Name}
    (hs : hf.inst.schema = commImageA) (hargs : hf.inst.args = [r, l, ob, m, x, y])
    (habs : Abstracts (ground d p rel) s σ)
    (habs' : Abstracts (ground d p rel) s' (o.applyA σ))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size) :
    Quiet (compile (ground d p rel)) s s' :=
  quiet_of_untouched hf (fun a ha => by
    rw [commImage_touches hf.inst hs hargs ha]
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩)
    habs habs' hn

/-! ### `CommSoilStep`, assembled

A `communicate_soil_data` that announces a goal the tables hold, and that was not
already met, meets exactly that goal: its fact becomes true, its analysis was in
hand because the schema reads it, and nothing else moves.
-/

open Planner.ExampleHeuristics.Rovers in
/-- **A `communicate_soil_data` meeting a tracked, unmet goal is a
`CommSoilStep`.** -/
theorem commSoilStep_of (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (ho : o ∈ groundedOps d p rel) (hfa : OpFactsAdd d p o)
    {r l q x y : Pddl.Name}
    (hs : hfa.inst.schema = commSoilA) (hargs : hfa.inst.args = [r, l, q, x, y])
    {s s' : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (habs' : Abstracts (ground d p rel) s' (o.applyA σ))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (happ : o.applicableA σ)
    {G : SampleGoal} (hG : G ∈ (compile (ground d p rel)).soilGoals)
    (hGname : (ground d p rel).factNames.getD G.goalFact default = commSoil q)
    (hunmet : s.test G.goalFact = false) :
    CommSoilStep (compile (ground d p rel)) s s' G := by
  obtain ⟨hadd, hdel⟩ : hfa.inst.add = [commSoil q] ∧ hfa.inst.del = [] := by
    obtain ⟨-, -, ha, hd⟩ := commSoil_atoms hfa.inst hs hargs; exact ⟨ha, hd⟩
  have hGlt : G.goalFact < (ground d p rel).factNames.size :=
    (soilGoals_name d p rel G hG).1
  refine
    { quiet := commSoil_quiet hfa.toOpFacts hs hargs habs habs' hn
      memQ := hG
      unmetQ := hunmet
      metQ' := ?_
      hasData := ?_
      frameSoil := ?_
      frameRock := ?_
      frameImage := ?_ }
  · -- The announced atom's fact is true afterwards.
    rw [← habs'.numbered G.goalFact (by rw [hn]; exact hGlt), hGname]
    exact commSoil_adds hfa hs hargs σ
  · -- The analysis is in hand, because the schema reads it.
    have hpre : haveSoil r q ∈ hfa.inst.pre := by
      obtain ⟨-, h, -, -⟩ := commSoil_atoms hfa.inst hs hargs; exact h
    obtain ⟨f, hflt, hfname⟩ := numbered_of_op d p rel ho
      (Or.inl (pre_mem_op hfa.toOpFacts hpre (haveSoil_dynamic hp.domain)))
    have htrue : s.test f = true := by
      rw [← habs.numbered f (by rw [hn]; exact hflt), hfname]
      exact pre_holds hfa.toOpFacts hpre (haveSoil_dynamic hp.domain) happ
    exact needsSample_false (soilGoal_analysis_eq d p rel G hG q hGname)
      hflt hfname htrue
  · -- No other soil goal names the announced atom.
    intro g hg hne
    refine addOne_frame hfa.toOpFacts hadd hdel habs habs' hn
      (soilGoals_name d p rel g hg).1 (fun hbad => hne ?_)
    exact soilGoals_goalFact_inj hp rel g hg G hG
      (factNames_inj (soilGoals_name d p rel g hg).1 hGlt (hbad.trans hGname.symm))
  · -- Rock goals name a different predicate.
    intro g hg
    obtain ⟨hlt, w, hname⟩ := rockGoals_name d p rel g hg
    refine addOne_frame hfa.toOpFacts hadd hdel habs habs' hn hlt ?_
    rw [hname]; simp [commSoil]
  · -- And so do image goals.
    intro g hg
    obtain ⟨hlt, ob, m, hname⟩ := imageGoals_name d p rel g hg
    refine addOne_frame hfa.toOpFacts hadd hdel habs habs' hn hlt ?_
    rw [hname]; simp [commSoil]

open Planner.ExampleHeuristics.Rovers in
/-- **A `communicate_rock_data` meeting a tracked, unmet goal is a
`CommRockStep`.** -/
theorem commRockStep_of (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (ho : o ∈ groundedOps d p rel) (hfa : OpFactsAdd d p o)
    {r l q x y : Pddl.Name}
    (hs : hfa.inst.schema = commRockA) (hargs : hfa.inst.args = [r, l, q, x, y])
    {s s' : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (habs' : Abstracts (ground d p rel) s' (o.applyA σ))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (happ : o.applicableA σ)
    {G : SampleGoal} (hG : G ∈ (compile (ground d p rel)).rockGoals)
    (hGname : (ground d p rel).factNames.getD G.goalFact default = commRock q)
    (hunmet : s.test G.goalFact = false) :
    CommRockStep (compile (ground d p rel)) s s' G := by
  obtain ⟨hadd, hdel⟩ : hfa.inst.add = [commRock q] ∧ hfa.inst.del = [] := by
    obtain ⟨-, -, ha, hd⟩ := commRock_atoms hfa.inst hs hargs; exact ⟨ha, hd⟩
  have hGlt : G.goalFact < (ground d p rel).factNames.size :=
    (rockGoals_name d p rel G hG).1
  refine
    { quiet := commRock_quiet hfa.toOpFacts hs hargs habs habs' hn
      memQ := hG
      unmetQ := hunmet
      metQ' := ?_
      hasData := ?_
      frameSoil := ?_
      frameRock := ?_
      frameImage := ?_ }
  · rw [← habs'.numbered G.goalFact (by rw [hn]; exact hGlt), hGname]
    exact commRock_adds hfa hs hargs σ
  · have hpre : haveRock r q ∈ hfa.inst.pre := by
      obtain ⟨-, h, -, -⟩ := commRock_atoms hfa.inst hs hargs; exact h
    obtain ⟨f, hflt, hfname⟩ := numbered_of_op d p rel ho
      (Or.inl (pre_mem_op hfa.toOpFacts hpre (haveRock_dynamic hp.domain)))
    have htrue : s.test f = true := by
      rw [← habs.numbered f (by rw [hn]; exact hflt), hfname]
      exact pre_holds hfa.toOpFacts hpre (haveRock_dynamic hp.domain) happ
    exact needsSample_false (rockGoal_analysis_eq d p rel G hG q hGname)
      hflt hfname htrue
  · intro g hg
    obtain ⟨hlt, w, hname⟩ := soilGoals_name d p rel g hg
    refine addOne_frame hfa.toOpFacts hadd hdel habs habs' hn hlt ?_
    rw [hname]; simp [commRock]
  · intro g hg hne
    refine addOne_frame hfa.toOpFacts hadd hdel habs habs' hn
      (rockGoals_name d p rel g hg).1 (fun hbad => hne ?_)
    exact rockGoals_goalFact_inj hp rel g hg G hG
      (factNames_inj (rockGoals_name d p rel g hg).1 hGlt (hbad.trans hGname.symm))
  · intro g hg
    obtain ⟨hlt, ob, m, hname⟩ := imageGoals_name d p rel g hg
    refine addOne_frame hfa.toOpFacts hadd hdel habs habs' hn hlt ?_
    rw [hname]; simp [commRock]

open Planner.ExampleHeuristics.Rovers in
/-- **A `communicate_image_data` meeting a tracked, unmet goal is a
`CommImageStep`.** -/
theorem commImageStep_of (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (ho : o ∈ groundedOps d p rel) (hfa : OpFactsAdd d p o)
    {r l ob m x y : Pddl.Name}
    (hs : hfa.inst.schema = commImageA) (hargs : hfa.inst.args = [r, l, ob, m, x, y])
    {s s' : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (habs' : Abstracts (ground d p rel) s' (o.applyA σ))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (happ : o.applicableA σ)
    {G : ImageGoal} (hG : G ∈ (compile (ground d p rel)).imageGoals)
    (hGname : (ground d p rel).factNames.getD G.goalFact default = commImage ob m)
    (hunmet : s.test G.goalFact = false) :
    CommImageStep (compile (ground d p rel)) s s' G := by
  obtain ⟨hadd, hdel⟩ : hfa.inst.add = [commImage ob m] ∧ hfa.inst.del = [] := by
    obtain ⟨-, -, ha, hd⟩ := commImage_atoms hfa.inst hs hargs; exact ⟨ha, hd⟩
  have hGlt : G.goalFact < (ground d p rel).factNames.size :=
    (imageGoals_name d p rel G hG).1
  refine
    { quiet := commImage_quiet hfa.toOpFacts hs hargs habs habs' hn
      memQ := hG
      unmetQ := hunmet
      metQ' := ?_
      hasPicture := ?_
      frameSoil := ?_
      frameRock := ?_
      frameImage := ?_ }
  · rw [← habs'.numbered G.goalFact (by rw [hn]; exact hGlt), hGname]
    exact commImage_adds hfa hs hargs σ
  · have hpre : haveImage r ob m ∈ hfa.inst.pre := by
      obtain ⟨-, h, -, -⟩ := commImage_atoms hfa.inst hs hargs; exact h
    obtain ⟨f, hflt, hfname⟩ := numbered_of_op d p rel ho
      (Or.inl (pre_mem_op hfa.toOpFacts hpre (haveImage_dynamic hp.domain)))
    have htrue : s.test f = true := by
      rw [← habs.numbered f (by rw [hn]; exact hflt), hfname]
      exact pre_holds hfa.toOpFacts hpre (haveImage_dynamic hp.domain) happ
    exact hasImage_true (imageGoal_have_eq d p rel G hG ob m hGname)
      hflt hfname htrue
  · intro g hg
    obtain ⟨hlt, w, hname⟩ := soilGoals_name d p rel g hg
    refine addOne_frame hfa.toOpFacts hadd hdel habs habs' hn hlt ?_
    rw [hname]; simp [commImage]
  · intro g hg
    obtain ⟨hlt, w, hname⟩ := rockGoals_name d p rel g hg
    refine addOne_frame hfa.toOpFacts hadd hdel habs habs' hn hlt ?_
    rw [hname]; simp [commImage]
  · intro g hg hne
    refine addOne_frame hfa.toOpFacts hadd hdel habs habs' hn
      (imageGoals_name d p rel g hg).1 (fun hbad => hne ?_)
    exact imageGoals_goalFact_inj hp rel g hg G hG
      (factNames_inj (imageGoals_name d p rel g hg).1 hGlt (hbad.trans hGname.symm))

/-! ### Where the rovers stand -/

open Planner.ExampleHeuristics.Rovers in
/-- A waypoint is occupied exactly when some rover's table holds a true `at`
fact for it. -/
theorem occupied_iff {dd : ExampleHeuristics.Rovers.Data} {s : State} {w : Nat} :
    occupied dd s w = true ↔
      ∃ facts ∈ dd.roverAt, ∃ e ∈ facts, e.2 = w ∧ s.test e.1 = true := by
  unfold occupied
  simp only [Array.any_eq_true, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨i, hi, j, hj, hw, ht⟩
    exact ⟨_, Array.getElem_mem hi, _, Array.getElem_mem hj, hw, ht⟩
  · rintro ⟨facts, hfacts, e, he, hw, ht⟩
    obtain ⟨i, hi, hgi⟩ := Array.getElem_of_mem hfacts
    obtain ⟨j, hj, hgj⟩ := Array.getElem_of_mem (hgi ▸ he)
    exact ⟨i, hi, j, hj, by rw [hgj]; exact hw, by rw [hgj]; exact ht⟩

open Planner.ExampleHeuristics.Rovers in
/-- And what such a fact names. -/
theorem roverAt_mem_atom {t : Task} {facts : Array (Fact × Nat)}
    (hfacts : facts ∈ (compile t).roverAt) {e : Fact × Nat} (he : e ∈ facts) :
    e.1 < t.factNames.size ∧ e.2 < (t.objectsOfTypes ["waypoint"]).size ∧
      ∃ r, t.factNames.getD e.1 default =
        { pred := "at", args := [r, (t.objectsOfTypes ["waypoint"]).getD e.2 default] } := by
  rw [compile_roverAt] at hfacts
  obtain ⟨r, -, hval⟩ := Array.mem_map.mp hfacts
  subst hval
  obtain ⟨h1, h2, h3⟩ := mem_roverAt_entries (by simpa using he)
  exact ⟨h1, h2, r, h3⟩

/-! ### The rover graphs hold the edges `navigate` walks

`reachStep` is where the traversal graph enters: `Distances.Sound.step` bounds a
distance across one edge, and this says the graph really has the edge a
`navigate` uses.  It is the payoff for building the graph with the shared
`Graph.ofEdges` rather than by hand.
-/

open Planner.ExampleHeuristics.Rovers in
/-- **A `navigate`'s preconditions name an edge of its rover's graph.** -/
theorem navigate_edge {t : Task} {waypoints : Array Pddl.Name}
    {r y z : Pddl.Name} {u v : Nat}
    (hct : ({ pred := "can_traverse", args := [r, y, z] } : GroundAtom)
      ∈ t.staticAtoms)
    (hvis : (t.staticWith "visible").any (fun b => b.args == [y, z]) = true)
    (hu : (roverGraph t waypoints r).find? y = some u)
    (hv : (roverGraph t waypoints r).find? z = some v) :
    v ∈ (roverGraph t waypoints r).adj.getD u #[] := by
  refine Graph.mem_adj_of_mem (pred := "can_traverse") ?_ hu hv
  refine Array.mem_filterMap.mpr ⟨_, hct, ?_⟩
  simp only [beq_self_eq_true, if_pos, hvis, Bool.and_self]

/-! ### Threading a bound through the minimum over a crew

`reach` folds a minimum over the crew, but the accumulator is `Option Nat` — it
is `none` until some rover has a position at all.  The fold lemmas in
`Proofs/Distance.lean` are over `Nat`, so this is the `Option` form.
-/

/-- One accumulator is within one of the other, and they are defined together. -/
def OptLe1 (a b : Option Nat) : Prop :=
  (a = none ↔ b = none) ∧ ∀ u v, a = some u → b = some v → u ≤ 1 + v

theorem optLe1_none : OptLe1 none none := ⟨Iff.rfl, by simp⟩

/-- And so the values it ends with are within one. -/
theorem OptLe1.getD_le {a b : Option Nat} (h : OptLe1 a b) : a.getD 0 ≤ 1 + b.getD 0 := by
  rcases ha : a with _ | u
  · simp
  · rcases hb : b with _ | v
    · exact absurd (h.1.mpr hb) (by rw [ha]; simp)
    · simpa using h.2 u v ha hb

/-- **The bound survives any fold whose step preserves it.** -/
theorem foldl_step_optLe1 {α : Type} (F G : Option Nat → α → Option Nat) :
    ∀ (l : List α), (∀ x ∈ l, ∀ a b, OptLe1 a b → OptLe1 (F a x) (G b x)) →
      ∀ a b, OptLe1 a b → OptLe1 (l.foldl F a) (l.foldl G b) := by
  intro l
  induction l with
  | nil => intro _ a b hab; exact hab
  | cons x rest ih =>
      intro h a b hab
      exact ih (fun y hy => h y (by simp [hy])) _ _ (h x (by simp) a b hab)

open Planner.ExampleHeuristics.Rovers in
/-- The distance one rover contributes to `reach`, if it has a position at all. -/
def roverVal (dd : ExampleHeuristics.Rovers.Data) (s : State) (r w : Nat) :
    Option Nat :=
  ((dd.roverAt.getD r #[]).find? fun x => s.test x.1).map
    fun x => (dd.dist.getD r default).get x.2 w

open Planner.ExampleHeuristics.Rovers in
/-- **A bound on every rover is a bound on `reach`.** -/
theorem reach_le_succ (dd : ExampleHeuristics.Rovers.Data) (s s' : State)
    (crew : Array Nat) (w : Nat)
    (h : ∀ r ∈ crew, OptLe1 (roverVal dd s r w) (roverVal dd s' r w)) :
    reach dd s crew w ≤ 1 + reach dd s' crew w := by
  simp only [reach]
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  refine OptLe1.getD_le (foldl_step_optLe1 _ _ crew.toList ?_ none none optLe1_none)
  intro r hr a b hab
  obtain ⟨h1, h2⟩ := h r (by simpa using hr)
  obtain ⟨hab1, hab2⟩ := hab
  rcases hf : (dd.roverAt.getD r #[]).find? (fun x => s.test x.1) with _ | e
  · rcases hg : (dd.roverAt.getD r #[]).find? (fun x => s'.test x.1) with _ | e'
    · simp only [hf, hg]; exact ⟨hab1, hab2⟩
    · exact absurd (h1.mp (by unfold roverVal; rw [hf]; rfl))
        (by unfold roverVal; rw [hg]; simp)
  · rcases hg : (dd.roverAt.getD r #[]).find? (fun x => s'.test x.1) with _ | e'
    · exact absurd (h1.mpr (by unfold roverVal; rw [hg]; rfl))
        (by unfold roverVal; rw [hf]; simp)
    · have hv : (dd.dist.getD r default).get e.2 w
          ≤ 1 + (dd.dist.getD r default).get e'.2 w :=
        h2 _ _ (by unfold roverVal; rw [hf]; rfl) (by unfold roverVal; rw [hg]; rfl)
      simp only [hf, hg]
      by_cases han : a = none
      · rw [han, hab1.mp han]
        exact ⟨by simp, by
          intro u u' k1 k2
          simp only [Option.some.injEq] at k1 k2
          subst k1; subst k2; omega⟩
      · obtain ⟨m, ham⟩ := Option.ne_none_iff_exists'.mp han
        obtain ⟨m', hbm⟩ := Option.ne_none_iff_exists'.mp
          (fun hc => han (hab1.mpr hc))
        have hmm : m ≤ 1 + m' := hab2 m m' ham hbm
        rw [ham, hbm]
        exact ⟨by simp, by
          intro u u' k1 k2
          simp only [Option.some.injEq] at k1 k2
          subst k1; subst k2; omega⟩

/-- A rover that did not move contributes the same. -/
theorem optLe1_refl (a : Option Nat) : OptLe1 a a := by
  refine ⟨Iff.rfl, ?_⟩
  intro u v h1 h2
  rw [h1] at h2
  simp only [Option.some.injEq] at h2
  omega

open Planner.ExampleHeuristics.Rovers in
/-- And a rover whose `at` facts did not move has the same contribution. -/
theorem roverVal_congr (dd : ExampleHeuristics.Rovers.Data) (s s' : State)
    (r w : Nat) (h : ∀ e ∈ dd.roverAt.getD r #[], s'.test e.1 = s.test e.1) :
    roverVal dd s' r w = roverVal dd s r w := by
  unfold roverVal
  rw [array_find?_congr _ _ _ h]

open Planner.ExampleHeuristics.Rovers in
/--
**The mover's contribution moves by at most one across the edge it walks.**

This is `Distances.Sound.step` read through `roverVal`: the rover's distance to
any target from where it was is within one of its distance from where it went.
-/
theorem roverVal_le_of_edge {dd : ExampleHeuristics.Rovers.Data} {s s' : State}
    {r w u v : Nat} {g : Graph}
    (hs : roverVal dd s r w = some ((dd.dist.getD r default).get u w))
    (hs' : roverVal dd s' r w = some ((dd.dist.getD r default).get v w))
    (hsound : Distances.Sound g (dd.dist.getD r default))
    (hu : u < g.size) (hw : w < g.size) (hedge : v ∈ g.adj.getD u #[]) :
    OptLe1 (roverVal dd s r w) (roverVal dd s' r w) := by
  refine ⟨by rw [hs, hs']; simp, ?_⟩
  intro a b h1 h2
  rw [hs] at h1
  rw [hs'] at h2
  simp only [Option.some.injEq] at h1 h2
  subst h1; subst h2
  exact hsound.step u v w hu hw hedge

open Planner.ExampleHeuristics.Rovers in
/--
**When a rover has one `at` fact true, that is the one `roverFind` reports.**

`roverFind` takes the *first* true entry, so on its own it says nothing about
where the rover is.  Under the invariant there is only one, and then the first is
the only one.
-/
theorem roverVal_eq_of_unique {dd : ExampleHeuristics.Rovers.Data} {s : State}
    {r w : Nat} {e : Fact × Nat}
    (he : e ∈ dd.roverAt.getD r #[]) (htrue : s.test e.1 = true)
    (huniq : ∀ e' ∈ dd.roverAt.getD r #[], s.test e'.1 = true → e' = e) :
    roverVal dd s r w = some ((dd.dist.getD r default).get e.2 w) := by
  unfold roverVal
  rcases hf : (dd.roverAt.getD r #[]).find? (fun x => s.test x.1) with _ | e'
  · exact absurd (Array.find?_eq_none.mp hf e he) (by simp [htrue])
  · rw [hf, huniq e' (Array.mem_of_find?_eq_some hf)
      (by simpa using Array.find?_some hf)]
    rfl

open Planner.ExampleHeuristics.Rovers in
/-- What an entry of rover `r`'s table names, with the rover read off the index. -/
theorem roverAt_getD_atom {t : Task} {r : Nat}
    (hr : r < (t.objectsOfTypes ["rover"]).size) {e : Fact × Nat}
    (he : e ∈ (compile t).roverAt.getD r #[]) :
    e.1 < t.factNames.size ∧ e.2 < (t.objectsOfTypes ["waypoint"]).size ∧
      t.factNames.getD e.1 default =
        { pred := "at", args := [(t.objectsOfTypes ["rover"]).getD r default,
                                 (t.objectsOfTypes ["waypoint"]).getD e.2 default] } := by
  rw [compile_roverAt, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem (by simpa using hr), Option.getD_some,
    Array.getElem_map] at he
  have hrn : (t.objectsOfTypes ["rover"]).getD r default
      = (t.objectsOfTypes ["rover"])[r] := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hr, Option.getD_some]
  obtain ⟨h1, h2, h3⟩ := mem_roverAt_entries (by simpa using he)
  exact ⟨h1, h2, by rw [h3, hrn]⟩

open Planner.ExampleHeuristics.Rovers in
/-- **Under the invariant, a rover's table has at most one true entry.** -/
theorem roverAt_unique {d : Domain} {p : Problem} {rel : Bool} {s : State}
    {σ : AtomState} (habs : Abstracts (ground d p rel) s σ)
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (hwnd : ((ground d p rel).objectsOfTypes ["waypoint"]).toList.Nodup)
    (hone : OneAt σ) {r : Nat}
    (hr : r < ((ground d p rel).objectsOfTypes ["rover"]).size)
    {e e' : Fact × Nat}
    (he : e ∈ (compile (ground d p rel)).roverAt.getD r #[])
    (he' : e' ∈ (compile (ground d p rel)).roverAt.getD r #[])
    (ht : s.test e.1 = true) (ht' : s.test e'.1 = true) : e = e' := by
  obtain ⟨hlt, hwlt, hname⟩ := roverAt_getD_atom hr he
  obtain ⟨hlt', hwlt', hname'⟩ := roverAt_getD_atom hr he'
  -- Both name an `at` of the same rover, so the invariant equates the waypoints.
  have hσ : σ ((ground d p rel).factNames.getD e.1 default) = true := by
    rw [habs.numbered e.1 (by rw [hn]; exact hlt)]; exact ht
  have hσ' : σ ((ground d p rel).factNames.getD e'.1 default) = true := by
    rw [habs.numbered e'.1 (by rw [hn]; exact hlt')]; exact ht'
  rw [hname] at hσ
  rw [hname'] at hσ'
  have hw : ((ground d p rel).objectsOfTypes ["waypoint"]).getD e.2 default
      = ((ground d p rel).objectsOfTypes ["waypoint"]).getD e'.2 default :=
    hone _ _ _ hσ hσ'
  have h2 : e.2 = e'.2 := by
    refine (List.Nodup.getElem_inj_iff hwnd (hi := by simpa using hwlt)
      (hj := by simpa using hwlt')).mp ?_
    have k1 : ((ground d p rel).objectsOfTypes ["waypoint"])[e.2]'hwlt
        = ((ground d p rel).objectsOfTypes ["waypoint"]).getD e.2 default := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hwlt, Option.getD_some]
    have k2 : ((ground d p rel).objectsOfTypes ["waypoint"])[e'.2]'hwlt'
        = ((ground d p rel).objectsOfTypes ["waypoint"]).getD e'.2 default := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hwlt', Option.getD_some]
    simpa using (k1.trans hw).trans k2.symm
  have h1 : e.1 = e'.1 :=
    factNames_inj hlt hlt' (by rw [hname, hname', h2])
  exact Prod.ext h1 h2

open Planner.ExampleHeuristics.Rovers in
/-- **The other direction: a numbered `at(rov, wp)` fact is in `rov`'s table.** -/
theorem mem_roverAt_of {t : Task} {r : Nat}
    (hr : r < (t.objectsOfTypes ["rover"]).size) {wp : Pddl.Name} {wi : Nat} {f : Fact}
    (hwi : (t.objectsOfTypes ["waypoint"]).findIdx? (· == wp) = some wi)
    (hlt : f < t.factNames.size)
    (hname : t.factNames.getD f default =
      { pred := "at", args := [(t.objectsOfTypes ["rover"]).getD r default, wp] }) :
    (f, wi) ∈ (compile t).roverAt.getD r #[] := by
  have hrn : (t.objectsOfTypes ["rover"]).getD r default
      = (t.objectsOfTypes ["rover"])[r] := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hr, Option.getD_some]
  rw [compile_roverAt, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem (by simpa using hr), Option.getD_some, Array.getElem_map]
  refine Array.mem_filterMap.mpr
    ⟨(f, { pred := "at",
           args := [(t.objectsOfTypes ["rover"]).getD r default, wp] }),
     mem_factsWith_of_named hlt hname rfl, ?_⟩
  show (match ([(t.objectsOfTypes ["rover"]).getD r default, wp] : List Pddl.Name) with
    | [y, w] =>
        if y == (t.objectsOfTypes ["rover"])[r] then
          ((t.objectsOfTypes ["waypoint"]).findIdx? (· == w)).map ((f, ·)) else none
    | _ => none) = some (f, wi)
  rw [hrn]
  simp [hwi]

open Planner.ExampleHeuristics.Rovers in
/--
**Where a rover is, read off one true `at` fact.**

Both halves of `reachStep` are this lemma: before the step with the origin, after
it with the destination.
-/
theorem roverVal_at {d : Domain} {p : Problem} {rel : Bool} {s : State}
    {σ : AtomState} (habs : Abstracts (ground d p rel) s σ)
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (hwnd : ((ground d p rel).objectsOfTypes ["waypoint"]).toList.Nodup)
    (hone : OneAt σ) {ri : Nat}
    (hr : ri < ((ground d p rel).objectsOfTypes ["rover"]).size)
    {x wp : Pddl.Name}
    (hrn : ((ground d p rel).objectsOfTypes ["rover"]).getD ri default = x)
    {wi : Nat} {f : Fact}
    (hwi : ((ground d p rel).objectsOfTypes ["waypoint"]).findIdx? (· == wp) = some wi)
    (hlt : f < (ground d p rel).factNames.size)
    (hname : (ground d p rel).factNames.getD f default = at_ x wp)
    (htrue : s.test f = true) (w : Nat) :
    roverVal (compile (ground d p rel)) s ri w
      = some (((compile (ground d p rel)).dist.getD ri default).get wi w) := by
  have hmem : (f, wi) ∈ (compile (ground d p rel)).roverAt.getD ri #[] :=
    mem_roverAt_of hr hwi hlt (by rw [hrn]; exact hname)
  refine roverVal_eq_of_unique hmem htrue ?_
  intro e' he' ht'
  exact roverAt_unique habs hn hwnd hone hr he' hmem ht' htrue

open Planner.ExampleHeuristics.Rovers in
/-- The distance table of one rover is the distances of that rover's graph. -/
theorem compile_dist_getD {t : Task} {ri : Nat}
    (hr : ri < (t.objectsOfTypes ["rover"]).size) :
    (compile t).dist.getD ri default
      = Distances.of (roverGraph t (t.objectsOfTypes ["waypoint"])
          ((t.objectsOfTypes ["rover"]).getD ri default)) := by
  show ((t.objectsOfTypes ["rover"]).map (fun r =>
    Distances.of (roverGraph t (t.objectsOfTypes ["waypoint"]) r))).getD ri default = _
  rw [Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem (by simpa using hr), Option.getD_some, Array.getElem_map,
    Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hr, Option.getD_some]

open Planner.ExampleHeuristics.Rovers in
/--
**`reach` moves by at most one when one rover walks one edge.**

The rover that moved is bounded by `Distances.Sound.step` across the edge it
walked; every other rover contributes exactly what it did before.
-/
theorem reach_le_of_move {dd : ExampleHeuristics.Rovers.Data} {s s' : State}
    {crew : Array Nat} {w ri u v : Nat} {g : Graph}
    (hbefore : roverVal dd s ri w = some ((dd.dist.getD ri default).get u w))
    (hafter : roverVal dd s' ri w = some ((dd.dist.getD ri default).get v w))
    (hsound : Distances.Sound g (dd.dist.getD ri default))
    (hu : u < g.size) (hw : w < g.size) (hedge : v ∈ g.adj.getD u #[])
    (hother : ∀ r ∈ crew, r ≠ ri → roverVal dd s' r w = roverVal dd s r w) :
    reach dd s crew w ≤ 1 + reach dd s' crew w := by
  refine reach_le_succ dd s s' crew w (fun r hr => ?_)
  by_cases hrri : r = ri
  · subst hrri
    exact roverVal_le_of_edge hbefore hafter hsound hu hw hedge
  · rw [hother r hr hrri]
    exact optLe1_refl _

/-! ### The base count, spelled out

`ResourceStep.baseDrop` is the one place a Rovers counter genuinely falls rather
than staying put, so its proof is arithmetic over the five families rather than a
frame.  Spelling `Bc` out is what lets each schema state which family moved and
leave the rest to `omega`.
-/

open Planner.ExampleHeuristics.Rovers in
theorem baseCount_eq (dd : ExampleHeuristics.Rovers.Data) (s : State) :
    Bc dd s = communicate dd s + samples dd s + images dd s
      + (images dd s - ExampleHeuristics.Rovers.calibrated dd s) + (samples dd s - emptyStores dd s) := rfl

open Planner.ExampleHeuristics.Rovers in
/--
**The base count falls by at most one**, given a drop named for each of its five
terms and the drops summing to one.

Stated this way rather than term by term because the terms interact.
`take_image` supplies a picture *and* spends the calibration, so `images` falls
by one while `images - calibrated` does not move at all — its drop is zero, not
one, and a term-by-term bound would double-count it.
-/
theorem baseCount_le_succ {dd : ExampleHeuristics.Rovers.Data} {s s' : State}
    {dc ds di dp de : Nat}
    (hc : communicate dd s ≤ communicate dd s' + dc)
    (hsam : samples dd s ≤ samples dd s' + ds)
    (himg : images dd s ≤ images dd s' + di)
    (hpair : images dd s - ExampleHeuristics.Rovers.calibrated dd s
      ≤ images dd s' - ExampleHeuristics.Rovers.calibrated dd s' + dp)
    (hstore : samples dd s - emptyStores dd s
      ≤ samples dd s' - emptyStores dd s' + de)
    (hsum : dc + ds + di + dp + de ≤ 1) :
    Bc dd s ≤ Bc dd s' + 1 := by
  rw [baseCount_eq, baseCount_eq]
  omega

open Planner.ExampleHeuristics.Rovers in
/-- **A rover standing on a waypoint occupies it.**  This is half of why the two
samplers do not lower the navigation bound: they sample where they stand, and
`arrivals` never counts an occupied waypoint. -/
theorem occupied_of {dd : ExampleHeuristics.Rovers.Data} {s : State} {r w : Nat}
    (hr : r < dd.roverAt.size) {e : Fact × Nat}
    (he : e ∈ dd.roverAt.getD r #[]) (hw : e.2 = w) (ht : s.test e.1 = true) :
    occupied dd s w = true := by
  refine occupied_iff.mpr ⟨dd.roverAt.getD r #[], ?_, e, he, hw, ht⟩
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hr, Option.getD_some]
  exact Array.getElem_mem hr

open Planner.ExampleHeuristics.Rovers in
/--
**The mover's contribution, for any target at all.**

`reachStep` quantifies over every `w`, including ones past the last column of the
distance table.  There both readings are the cap, so the bound is immediate;
inside the table it is `Sound.step` across the edge.
-/
theorem roverVal_le_of_edge' {dd : ExampleHeuristics.Rovers.Data} {s s' : State}
    {r w u v : Nat} {g : Graph}
    (hs : roverVal dd s r w = some ((dd.dist.getD r default).get u w))
    (hs' : roverVal dd s' r w = some ((dd.dist.getD r default).get v w))
    (hsound : Distances.Sound g (dd.dist.getD r default))
    (hu : u < g.size) (hedge : v ∈ g.adj.getD u #[]) :
    OptLe1 (roverVal dd s r w) (roverVal dd s' r w) := by
  by_cases hw : w < g.size
  · exact roverVal_le_of_edge hs hs' hsound hu hw hedge
  · refine ⟨by rw [hs, hs']; simp, ?_⟩
    intro a b h1 h2
    rw [hs] at h1
    rw [hs'] at h2
    simp only [Option.some.injEq] at h1 h2
    subst h1; subst h2
    rw [Distances.get_of_col_ge hsound u (by omega),
      Distances.get_of_col_ge hsound v (by omega)]
    omega

open Planner.ExampleHeuristics.Rovers in
/-- **And so `reach` moves by at most one, for every target.** -/
theorem reach_le_of_move' {dd : ExampleHeuristics.Rovers.Data} {s s' : State}
    {crew : Array Nat} {w ri u v : Nat} {g : Graph}
    (hbefore : roverVal dd s ri w = some ((dd.dist.getD ri default).get u w))
    (hafter : roverVal dd s' ri w = some ((dd.dist.getD ri default).get v w))
    (hsound : Distances.Sound g (dd.dist.getD ri default))
    (hu : u < g.size) (hedge : v ∈ g.adj.getD u #[])
    (hother : ∀ r ∈ crew, r ≠ ri → roverVal dd s' r w = roverVal dd s r w) :
    reach dd s crew w ≤ 1 + reach dd s' crew w := by
  refine reach_le_succ dd s s' crew w (fun r hr => ?_)
  by_cases hrri : r = ri
  · subst hrri
    exact roverVal_le_of_edge' hbefore hafter hsound hu hedge
  · rw [hother r hr hrri]
    exact optLe1_refl _

/-! ### One changed fact moves a pool count by at most one

`Proofs/SchemaSupport.lean` has `countHolding_succ` for the exact case — one fact
becomes true and nothing else moves — and `countHolding_congr'` for none moving.
Each resource schema sits between: it changes at most one fact of the pool, and
`baseDrop` only needs the bound, not the exact count.
-/

open Planner.ExampleHeuristics.Rovers in
/-- **A pool count moves by at most one when at most one of its facts does.** -/
theorem countHolding_le_one (facts : Array Fact) {s s' : State} (x : Fact)
    (hnd : facts.toList.Nodup)
    (hrest : ∀ f ∈ facts, f ≠ x → s'.test f = s.test f) :
    countHolding facts s' ≤ countHolding facts s + 1 ∧
      countHolding facts s ≤ countHolding facts s' + 1 := by
  rw [countHolding_eq, countHolding_eq, size_filter_toList, size_filter_toList]
  exact ⟨length_filter_le_succ _ _ _ x hnd
      (fun y hy hne => hrest y (by simpa using hy) hne),
    length_filter_le_succ _ _ _ x hnd
      (fun y hy hne => (hrest y (by simpa using hy) hne).symm)⟩

open Planner.ExampleHeuristics.Rovers in
/--
**A schema that leaves the goals, analyses, pictures and rover positions alone is
a `ResourceStep`**, provided its two pool counts move by at most one between them.

This covers all four resource schemas at once.  Each names its own pool — `empty`
for the two samplers and `drop`, `calibrated` for `calibrate` and `take_image` —
and everything else is a frame.
-/
theorem resourceStep_of_frames {dd : ExampleHeuristics.Rovers.Data} {s s' : State}
    {dcal demp : Nat}
    (hgoal : GoalsFixed dd s s')
    (hsoil : ∀ g ∈ dd.soilGoals, needsSample s' g = needsSample s g)
    (hrock : ∀ g ∈ dd.rockGoals, needsSample s' g = needsSample s g)
    (himg : ∀ g ∈ dd.imageGoals, hasImage s' g = hasImage s g)
    (hpos : ∀ r, roverFind dd s' r = roverFind dd s r)
    (hocc : ∀ w, occupied dd s' w = occupied dd s w)
    (hcal : ExampleHeuristics.Rovers.calibrated dd s'
      ≤ ExampleHeuristics.Rovers.calibrated dd s + dcal)
    (hemp : emptyStores dd s' ≤ emptyStores dd s + demp)
    (hsum : dcal + demp ≤ 1) :
    ResourceStep dd s s' := by
  have hs : soilToSample dd s' = soilToSample dd s :=
    soilToSample_congr hgoal.soil hsoil
  have hr : rockToSample dd s' = rockToSample dd s :=
    rockToSample_congr hgoal.rock hrock
  have hsam : samples dd s' = samples dd s := by unfold samples; rw [hs, hr]
  have hi : images dd s' = images dd s := images_congr hgoal.image himg
  have hc : communicate dd s' = communicate dd s := by
    unfold communicate
    rw [unmetSoil_congr hgoal.soil, unmetRock_congr hgoal.rock,
      unmetImage_congr hgoal.image]
  refine { goals := hgoal, RcLe := ?_, baseDrop := ?_ }
  · rw [Rc_congr hs hr hpos hocc]
  · refine baseCount_le_succ (dc := 0) (ds := 0) (di := 0) (dp := dcal) (de := demp)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

open Planner.ExampleHeuristics.Rovers in
/--
**A pool whose only touched atom is `A` moves by at most one.**

Which fact is the exception does not have to be named: if the table holds one for
`A` it is that one, and distinct facts name distinct atoms; if it holds none,
every fact is framed and the counts agree.
-/
theorem pool_le_one {d : Domain} {p : Problem} {rel : Bool} {o : AtomOp}
    (hf : OpFacts d p o) {A : GroundAtom} {P : Pddl.Name}
    (htouch : ∀ a, (a ∈ hf.inst.add ∨ a ∈ hf.inst.del) → a = A ∨ a.pred ≠ P)
    (facts : Array Fact) (hnd : facts.toList.Nodup)
    (hlt : ∀ f ∈ facts, f < (ground d p rel).factNames.size)
    (hpred : ∀ f ∈ facts, ((ground d p rel).factNames.getD f default).pred = P)
    {s s' : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (habs' : Abstracts (ground d p rel) s' (o.applyA σ))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size) :
    countHolding facts s' ≤ countHolding facts s + 1 ∧
      countHolding facts s ≤ countHolding facts s' + 1 := by
  have frame : ∀ f ∈ facts, (ground d p rel).factNames.getD f default ≠ A →
      s'.test f = s.test f := by
    intro f hf' hne
    have hne' : ∀ a, (a ∈ hf.inst.add ∨ a ∈ hf.inst.del) →
        (ground d p rel).factNames.getD f default ≠ a := by
      intro a ha hbad
      rcases htouch a ha with rfl | hp
      · exact hne hbad
      · exact hp (by rw [← hbad]; exact hpred f hf')
    rw [← habs'.numbered f (by rw [hn]; exact hlt f hf'),
      ← habs.numbered f (by rw [hn]; exact hlt f hf')]
    exact applyA_frame σ (fun hc => hne' _ (Or.inl (hf.subAdd _ hc)) rfl)
      (fun hc => hne' _ (Or.inr (hf.subDel _ hc)) rfl)
  by_cases hex : ∃ f0 ∈ facts, (ground d p rel).factNames.getD f0 default = A
  · obtain ⟨f0, hf0, hn0⟩ := hex
    exact countHolding_le_one facts f0 hnd fun f hf' hne =>
      frame f hf' fun hbad =>
        hne (factNames_inj (hlt f hf') (hlt f0 hf0) (hbad.trans hn0.symm))
  · simp only [not_exists, not_and] at hex
    exact countHolding_le_one facts 0 hnd fun f hf' _ => frame f hf' (hex f hf')

open Planner.ExampleHeuristics.Rovers in
/--
**A schema that touches neither the analyses, the pictures, nor the rover
positions leaves all five families `resourceStep_of_frames` reads.**

Weaker than `quiet_of_untouched`, which also asks for the two pools — and the
resource schemas each move one of those, so they need this instead.
-/
theorem frames_of_untouched {d : Domain} {p : Problem} {rel : Bool} {o : AtomOp}
    (hf : OpFacts d p o)
    (hunt : ∀ a, (a ∈ hf.inst.add ∨ a ∈ hf.inst.del) →
      a.pred ≠ "have_soil_analysis" ∧ a.pred ≠ "have_rock_analysis" ∧
      a.pred ≠ "have_image" ∧ a.pred ≠ "at")
    {s s' : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (habs' : Abstracts (ground d p rel) s' (o.applyA σ))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size) :
    (∀ g ∈ (compile (ground d p rel)).soilGoals,
        needsSample s' g = needsSample s g) ∧
      (∀ g ∈ (compile (ground d p rel)).rockGoals,
        needsSample s' g = needsSample s g) ∧
      (∀ g ∈ (compile (ground d p rel)).imageGoals, hasImage s' g = hasImage s g) ∧
      (∀ r, roverFind (compile (ground d p rel)) s' r
        = roverFind (compile (ground d p rel)) s r) ∧
      (∀ w, occupied (compile (ground d p rel)) s' w
        = occupied (compile (ground d p rel)) s w) := by
  have frame : ∀ (P : Pddl.Name), (∀ a, (a ∈ hf.inst.add ∨ a ∈ hf.inst.del) →
      a.pred ≠ P) → ∀ {f : Fact}, f < (ground d p rel).factNames.size →
      ((ground d p rel).factNames.getD f default).pred = P →
      s'.test f = s.test f := by
    intro P hP f hlt hp
    exact test_frame_pred hf (fun a ha => hP a (Or.inl ha))
      (fun a ha => hP a (Or.inr ha)) habs habs' hn hlt hp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    unfold needsSample
    rw [any_congr _ _ _ fun w hw => ?_]
    obtain ⟨h1, h2⟩ := soilGoal_analysis_pred hg hw
    exact frame _ (fun a ha => (hunt a ha).1) h1 h2
  · intro g hg
    unfold needsSample
    rw [any_congr _ _ _ fun w hw => ?_]
    obtain ⟨h1, h2⟩ := rockGoal_analysis_pred hg hw
    exact frame _ (fun a ha => (hunt a ha).2.1) h1 h2
  · intro g hg
    unfold hasImage
    rw [any_congr _ _ _ fun w hw => ?_]
    obtain ⟨h1, h2⟩ := imageGoal_have_pred hg hw
    exact frame _ (fun a ha => (hunt a ha).2.2.1) h1 h2
  · intro r
    unfold roverFind
    refine array_find?_congr _ _ _ fun y hy => ?_
    obtain ⟨h1, h2⟩ := roverAt_pred hy
    exact frame _ (fun a ha => (hunt a ha).2.2.2) h1 h2
  · intro w
    unfold occupied
    refine any_congr _ _ _ fun facts hfacts => ?_
    refine any_congr _ _ _ fun y hy => ?_
    obtain ⟨h1, h2⟩ := roverAt_mem_pred hfacts hy
    rw [frame _ (fun a ha => (hunt a ha).2.2.2) h1 h2]

open Planner.ExampleHeuristics.Rovers in
/-- **A numbered `calibrated` fact is in the pool.** -/
theorem mem_calibratedFacts_of {t : Task} {f : Fact} {a : GroundAtom}
    (hlt : f < t.factNames.size) (hname : t.factNames.getD f default = a)
    (hpred : a.pred = "calibrated") : f ∈ (compile t).calibratedFacts := by
  rw [compile_calibratedFacts]
  exact Array.mem_map.mpr ⟨(f, a), mem_factsWith_of_named hlt hname hpred, rfl⟩

open Planner.ExampleHeuristics.Rovers in
/-- **And a numbered `empty` fact.** -/
theorem mem_emptyFacts_of {t : Task} {f : Fact} {a : GroundAtom}
    (hlt : f < t.factNames.size) (hname : t.factNames.getD f default = a)
    (hpred : a.pred = "empty") : f ∈ (compile t).emptyFacts := by
  rw [compile_emptyFacts]
  exact Array.mem_map.mpr ⟨(f, a), mem_factsWith_of_named hlt hname hpred, rfl⟩

open Planner.ExampleHeuristics.Rovers in
/-- **A pool loses exactly one when one fact falls and no other fact moves.** -/
theorem pool_drop_one (facts : Array Fact) (hnd : facts.toList.Nodup)
    {s s' : State} (f : Fact) (hf : f ∈ facts)
    (hs : s.test f = true) (hs' : s'.test f = false)
    (hrest : ∀ g ∈ facts, g ≠ f → s.test g = s'.test g) :
    countHolding facts s = countHolding facts s' + 1 :=
  countHolding_succ facts f hf hnd hs' hs (fun g hg hgf => hrest g hg hgf)

open Planner.ExampleHeuristics.Rovers in
/-- Removing only goals at one waypoint shortens a sample-goal array by at most one. -/
theorem sample_size_le_succ {old new : Array SampleGoal} {w : Nat}
    (hnd : old.toList.Nodup)
    (hmove : ∀ g ∈ old, g ∈ new ∨ g.waypoint = w)
    (hinj : ∀ g ∈ old, ∀ G ∈ old, g.waypoint = G.waypoint → g = G) :
    old.size ≤ new.size + 1 := by
  classical
  by_cases hex : ∃ G ∈ old, G.waypoint = w
  · obtain ⟨G, hG, hGwp⟩ := hex
    have hsub : ∀ g ∈ old.toList, g ∈ G :: new.toList := by
      intro g hg
      rcases hmove g (by simpa using hg) with hg' | hgwp
      · exact List.mem_cons.mpr (Or.inr (by simpa using hg'))
      · exact List.mem_cons.mpr (Or.inl
          (hinj g (by simpa using hg) G hG (hgwp.trans hGwp.symm)))
    simpa using length_le_of_subset' _ _ hnd hsub
  · simp only [not_exists, not_and] at hex
    have hsub : ∀ g ∈ old.toList, g ∈ new.toList := by
      intro g hg
      rcases hmove g (by simpa using hg) with hg' | hgwp
      · simpa using hg'
      · exact absurd hgwp (hex g (by simpa using hg))
    have hle := length_le_of_subset' _ _ hnd hsub
    simpa using Nat.le_trans hle (Nat.le_succ _)

open Planner.ExampleHeuristics.Rovers in
/-- **A `sample_soil` is a `ResourceStep`.**  The new analysis can remove only
the goal at the sampled waypoint.  That waypoint was already occupied and at
distance zero, while the consumed empty store compensates the sample count. -/
theorem sampleSoil_schemaStep (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (ho : o ∈ groundedOps d p rel) (hf : OpFacts d p o)
    {x st q : Pddl.Name}
    (hs : hf.inst.schema = sampleSoilA) (hargs : hf.inst.args = [x, st, q])
    {s s' : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (habs' : Abstracts (ground d p rel) s' (o.applyA σ))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (happ : o.applicableA σ)
    (hnd : (compile (ground d p rel)).soilGoals.toList.Nodup)
    {wi : Nat}
    (hwi : ((ground d p rel).objectsOfTypes ["waypoint"]).findIdx? (· == q) = some wi)
    (hhere : occupied (compile (ground d p rel)) s wi = true)
    (hzero : reach (compile (ground d p rel)) s
      (compile (ground d p rel)).soilRovers wi = 0) :
    SchemaStep (compile (ground d p rel)) s s' := by
  classical
  let dd := compile (ground d p rel)
  change SchemaStep dd s s'
  obtain ⟨hat, -, hemp, hadd, hdel⟩ := sampleSoil_atoms hf.inst hs hargs
  have frame : ∀ (P : Pddl.Name), P ≠ "full" → P ≠ "have_soil_analysis" →
      P ≠ "empty" → P ≠ "at_soil_sample" → ∀ {f : Fact},
      f < (ground d p rel).factNames.size →
      ((ground d p rel).factNames.getD f default).pred = P →
      s'.test f = s.test f := by
    intro P hfull hsoil hemp' hatSample f hlt hpred
    refine test_frame_pred hf ?_ ?_ habs habs' hn hlt hpred <;> intro a hm hbad
    · rcases sampleSoil_touches hf.inst hs hargs (Or.inl hm) with h | h | h | h <;>
        rw [h] at hbad
      · exact hfull hbad.symm
      · exact hsoil hbad.symm
      · exact hemp' hbad.symm
      · exact hatSample hbad.symm
    · rcases sampleSoil_touches hf.inst hs hargs (Or.inr hm) with h | h | h | h <;>
        rw [h] at hbad
      · exact hfull hbad.symm
      · exact hsoil hbad.symm
      · exact hemp' hbad.symm
      · exact hatSample hbad.symm
  have hgoal : GoalsFixed dd s s' := by
    refine { soil := fun g hg => ?_, rock := fun g hg => ?_, image := fun g hg => ?_ }
    · obtain ⟨hlt, w, hname⟩ := soilGoals_name d p rel g hg
      exact frame "communicated_soil_data" (by decide) (by decide) (by decide)
        (by decide) hlt (by rw [hname])
    · obtain ⟨hlt, w, hname⟩ := rockGoals_name d p rel g hg
      exact frame "communicated_rock_data" (by decide) (by decide) (by decide)
        (by decide) hlt (by rw [hname])
    · obtain ⟨hlt, ob, m, hname⟩ := imageGoals_name d p rel g hg
      exact frame "communicated_image_data" (by decide) (by decide) (by decide)
        (by decide) hlt (by rw [hname])
  have hrockNeeds : ∀ g ∈ dd.rockGoals, needsSample s' g = needsSample s g := by
    intro g hg
    unfold needsSample
    rw [any_congr _ _ _ fun f hfg => ?_]
    obtain ⟨hlt, hpred⟩ := rockGoal_analysis_pred hg hfg
    exact frame "have_rock_analysis" (by decide) (by decide) (by decide)
      (by decide) hlt hpred
  have himage : ∀ g ∈ dd.imageGoals, hasImage s' g = hasImage s g := by
    intro g hg
    unfold hasImage
    rw [any_congr _ _ _ fun f hfg => ?_]
    obtain ⟨hlt, hpred⟩ := imageGoal_have_pred hg hfg
    exact frame "have_image" (by decide) (by decide) (by decide) (by decide) hlt hpred
  have hfind : ∀ r, roverFind dd s' r = roverFind dd s r := by
    intro r
    unfold roverFind
    refine array_find?_congr _ _ _ fun e he => ?_
    obtain ⟨hlt, hpred⟩ := roverAt_pred he
    exact frame "at" (by decide) (by decide) (by decide) (by decide) hlt hpred
  have hocc : ∀ w, occupied dd s' w = occupied dd s w := by
    intro w
    unfold occupied
    refine any_congr _ _ _ fun facts hfacts => ?_
    refine any_congr _ _ _ fun e he => ?_
    obtain ⟨hlt, hpred⟩ := roverAt_mem_pred hfacts he
    rw [frame "at" (by decide) (by decide) (by decide) (by decide) hlt hpred]
  have hcal : ExampleHeuristics.Rovers.calibrated dd s' =
      ExampleHeuristics.Rovers.calibrated dd s := by
    unfold ExampleHeuristics.Rovers.calibrated
    refine countHolding_congr _ fun f hfm => ?_
    obtain ⟨hlt, hpred⟩ := calibratedFacts_pred hfm
    exact frame "calibrated" (by decide) (by decide) (by decide) (by decide) hlt hpred
  have hsoil : ∀ g ∈ soilToSample dd s,
      g ∈ soilToSample dd s' ∨ g.waypoint = wi := by
    intro g hg
    by_cases hgwi : g.waypoint = wi
    · exact Or.inr hgwi
    left
    have hold : g ∈ dd.soilGoals.toList.filter
        (fun z => needsSample s z && liveS s z) := by
      rw [← soilToSample_toList]
      simpa using hg
    have hgbase : g ∈ dd.soilGoals := by
      simpa using (List.mem_filter.mp hold).1
    obtain ⟨-, w, hname⟩ := soilGoals_name d p rel g hgbase
    have hgidx := soilGoal_waypoint_eq d p rel g hgbase w hname
    have hwq : w ≠ q := by
      intro hwq
      subst hwq
      have : some g.waypoint = some wi := hgidx.symm.trans hwi
      exact hgwi (Option.some.inj this)
    have hanalysis : g.analysisFacts =
        ((ground d p rel).factsWith "have_soil_analysis").filterMap fun z =>
          match z.2.args with
          | [_, u] => if u == w then some z.1 else none
          | _ => none := soilGoal_analysis_eq d p rel g hgbase w hname
    have hneeds : needsSample s' g = needsSample s g := by
      unfold needsSample
      rw [any_congr _ _ _ fun f hfg => ?_]
      obtain ⟨hlt, -, r, hfname⟩ := mem_analysisOf (by rw [← hanalysis]; exact hfg)
      rw [← habs'.numbered f (by rw [hn]; exact hlt),
        ← habs.numbered f (by rw [hn]; exact hlt)]
      refine frame_of_lists hf hadd hdel ?_ ?_ σ
      · rw [hfname]
        simp [haveSoil, fullS, hwq]
      · rw [hfname]
        simp [emptyS, atSoilSample]
    have hnew : g ∈ (soilToSample dd s').toList := by
      rw [soilToSample_toList]
      refine List.mem_filter.mpr ⟨by simpa using hgbase, ?_⟩
      have holdp := (List.mem_filter.mp hold).2
      simpa [liveS, hneeds, hgoal.soil g hgbase] using holdp
    simpa using hnew
  have hrock : rockToSample dd s' = rockToSample dd s :=
    rockToSample_congr hgoal.rock hrockNeeds
  have hsoilSize : (soilToSample dd s).size ≤ (soilToSample dd s').size + 1 := by
    have holdnd : (soilToSample dd s).toList.Nodup := by
      rw [soilToSample_toList]
      exact hnd.filter _
    refine sample_size_le_succ holdnd hsoil ?_
    intro g hg G hG hwp
    have hgbase : g ∈ dd.soilGoals := by
      have hgl : g ∈ (soilToSample dd s).toList := by simpa using hg
      rw [soilToSample_toList] at hgl
      simpa using (List.mem_filter.mp hgl).1
    have hGbase : G ∈ dd.soilGoals := by
      have hGl : G ∈ (soilToSample dd s).toList := by simpa using hG
      rw [soilToSample_toList] at hGl
      simpa using (List.mem_filter.mp hGl).1
    exact soilGoals_waypoint_inj hp rel g hgbase G hGbase hwp
  have hsamples : samples dd s ≤ samples dd s' + 1 := by
    unfold samples
    rw [hrock]
    omega
  obtain ⟨fe, felt, fename⟩ := numbered_of_op d p rel ho
    (Or.inl (pre_mem_op hf hemp (empty_dynamic hp.domain)))
  have fetrue : s.test fe = true := by
    rw [← habs.numbered fe (by rw [hn]; exact felt), fename]
    exact pre_holds hf hemp (empty_dynamic hp.domain) happ
  have fedel : emptyS st ∈ o.del := by
    refine del_kept hf (by rw [hdel]; simp) ?_ hemp (empty_dynamic hp.domain)
    rw [hadd]
    simp [emptyS, fullS, haveSoil]
  have fenadd : emptyS st ∉ o.add := fun hmem => by
    have hmem' := hf.subAdd _ hmem
    rw [hadd] at hmem'
    simp [emptyS, fullS, haveSoil] at hmem'
  have fefalse : s'.test fe = false := by
    rw [← habs'.numbered fe (by rw [hn]; exact felt), fename]
    exact applyA_del σ fedel fenadd
  have femem : fe ∈ dd.emptyFacts := mem_emptyFacts_of felt fename rfl
  have hempDrop : emptyStores dd s = emptyStores dd s' + 1 := by
    unfold emptyStores
    refine pool_drop_one dd.emptyFacts ?_ fe femem fetrue fefalse ?_
    · rw [compile_emptyFacts]
      exact factsWith_nodup _ _
    · intro f hfm hne
      obtain ⟨hlt, hpred⟩ := emptyFacts_pred hfm
      apply Eq.symm
      rw [← habs'.numbered f (by rw [hn]; exact hlt),
        ← habs.numbered f (by rw [hn]; exact hlt)]
      refine frame_of_lists hf hadd hdel ?_ ?_ σ
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        constructor <;> intro hname <;> rw [hname] at hpred <;>
          simp [fullS, haveSoil] at hpred
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        constructor
        · intro hname
          exact hne (factNames_inj hlt felt (hname.trans fename.symm))
        · intro hname
          rw [hname] at hpred
          simp [atSoilSample] at hpred
  refine .resource
    { goals := hgoal
      RcLe := Rc_le_of_soil_sample hsoil hrock hfind hocc hhere hzero
      baseDrop := ?_ }
  have hcomm : communicate dd s' = communicate dd s := by
    unfold communicate
    rw [unmetSoil_congr hgoal.soil, unmetRock_congr hgoal.rock,
      unmetImage_congr hgoal.image]
  have himages : images dd s' = images dd s := images_congr hgoal.image himage
  refine baseCount_le_succ (dc := 0) (ds := 1) (di := 0) (dp := 0) (de := 0)
    (by omega) hsamples (by omega) (by omega) ?_ (by omega)
  omega

open Planner.ExampleHeuristics.Rovers in
/-- **A `sample_rock` is a `ResourceStep`.**  This is the rock-analysis
counterpart of `sampleSoil_schemaStep`. -/
theorem sampleRock_schemaStep (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (ho : o ∈ groundedOps d p rel) (hf : OpFacts d p o)
    {x st q : Pddl.Name}
    (hs : hf.inst.schema = sampleRockA) (hargs : hf.inst.args = [x, st, q])
    {s s' : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (habs' : Abstracts (ground d p rel) s' (o.applyA σ))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (happ : o.applicableA σ)
    (hnd : (compile (ground d p rel)).rockGoals.toList.Nodup)
    {wi : Nat}
    (hwi : ((ground d p rel).objectsOfTypes ["waypoint"]).findIdx? (· == q) = some wi)
    (hhere : occupied (compile (ground d p rel)) s wi = true)
    (hzero : reach (compile (ground d p rel)) s
      (compile (ground d p rel)).rockRovers wi = 0) :
    SchemaStep (compile (ground d p rel)) s s' := by
  classical
  let dd := compile (ground d p rel)
  change SchemaStep dd s s'
  obtain ⟨hat, -, hemp, hadd, hdel⟩ := sampleRock_atoms hf.inst hs hargs
  have frame : ∀ (P : Pddl.Name), P ≠ "full" → P ≠ "have_rock_analysis" →
      P ≠ "empty" → P ≠ "at_rock_sample" → ∀ {f : Fact},
      f < (ground d p rel).factNames.size →
      ((ground d p rel).factNames.getD f default).pred = P →
      s'.test f = s.test f := by
    intro P hfull hrock hemp' hatSample f hlt hpred
    refine test_frame_pred hf ?_ ?_ habs habs' hn hlt hpred <;> intro a hm hbad
    · rcases sampleRock_touches hf.inst hs hargs (Or.inl hm) with h | h | h | h <;>
        rw [h] at hbad
      · exact hfull hbad.symm
      · exact hrock hbad.symm
      · exact hemp' hbad.symm
      · exact hatSample hbad.symm
    · rcases sampleRock_touches hf.inst hs hargs (Or.inr hm) with h | h | h | h <;>
        rw [h] at hbad
      · exact hfull hbad.symm
      · exact hrock hbad.symm
      · exact hemp' hbad.symm
      · exact hatSample hbad.symm
  have hgoal : GoalsFixed dd s s' := by
    refine { soil := fun g hg => ?_, rock := fun g hg => ?_, image := fun g hg => ?_ }
    · obtain ⟨hlt, w, hname⟩ := soilGoals_name d p rel g hg
      exact frame "communicated_soil_data" (by decide) (by decide) (by decide)
        (by decide) hlt (by rw [hname])
    · obtain ⟨hlt, w, hname⟩ := rockGoals_name d p rel g hg
      exact frame "communicated_rock_data" (by decide) (by decide) (by decide)
        (by decide) hlt (by rw [hname])
    · obtain ⟨hlt, ob, m, hname⟩ := imageGoals_name d p rel g hg
      exact frame "communicated_image_data" (by decide) (by decide) (by decide)
        (by decide) hlt (by rw [hname])
  have hsoilNeeds : ∀ g ∈ dd.soilGoals, needsSample s' g = needsSample s g := by
    intro g hg
    unfold needsSample
    rw [any_congr _ _ _ fun f hfg => ?_]
    obtain ⟨hlt, hpred⟩ := soilGoal_analysis_pred hg hfg
    exact frame "have_soil_analysis" (by decide) (by decide) (by decide)
      (by decide) hlt hpred
  have himage : ∀ g ∈ dd.imageGoals, hasImage s' g = hasImage s g := by
    intro g hg
    unfold hasImage
    rw [any_congr _ _ _ fun f hfg => ?_]
    obtain ⟨hlt, hpred⟩ := imageGoal_have_pred hg hfg
    exact frame "have_image" (by decide) (by decide) (by decide) (by decide) hlt hpred
  have hfind : ∀ r, roverFind dd s' r = roverFind dd s r := by
    intro r
    unfold roverFind
    refine array_find?_congr _ _ _ fun e he => ?_
    obtain ⟨hlt, hpred⟩ := roverAt_pred he
    exact frame "at" (by decide) (by decide) (by decide) (by decide) hlt hpred
  have hocc : ∀ w, occupied dd s' w = occupied dd s w := by
    intro w
    unfold occupied
    refine any_congr _ _ _ fun facts hfacts => ?_
    refine any_congr _ _ _ fun e he => ?_
    obtain ⟨hlt, hpred⟩ := roverAt_mem_pred hfacts he
    rw [frame "at" (by decide) (by decide) (by decide) (by decide) hlt hpred]
  have hcal : ExampleHeuristics.Rovers.calibrated dd s' =
      ExampleHeuristics.Rovers.calibrated dd s := by
    unfold ExampleHeuristics.Rovers.calibrated
    refine countHolding_congr _ fun f hfm => ?_
    obtain ⟨hlt, hpred⟩ := calibratedFacts_pred hfm
    exact frame "calibrated" (by decide) (by decide) (by decide) (by decide) hlt hpred
  have hrock : ∀ g ∈ rockToSample dd s,
      g ∈ rockToSample dd s' ∨ g.waypoint = wi := by
    intro g hg
    by_cases hgwi : g.waypoint = wi
    · exact Or.inr hgwi
    left
    have hold : g ∈ dd.rockGoals.toList.filter
        (fun z => needsSample s z && liveS s z) := by
      rw [← rockToSample_toList]
      simpa using hg
    have hgbase : g ∈ dd.rockGoals := by
      simpa using (List.mem_filter.mp hold).1
    obtain ⟨-, w, hname⟩ := rockGoals_name d p rel g hgbase
    have hgidx := rockGoal_waypoint_eq d p rel g hgbase w hname
    have hwq : w ≠ q := by
      intro hwq
      subst hwq
      have : some g.waypoint = some wi := hgidx.symm.trans hwi
      exact hgwi (Option.some.inj this)
    have hanalysis : g.analysisFacts =
        ((ground d p rel).factsWith "have_rock_analysis").filterMap fun z =>
          match z.2.args with
          | [_, u] => if u == w then some z.1 else none
          | _ => none := rockGoal_analysis_eq d p rel g hgbase w hname
    have hneeds : needsSample s' g = needsSample s g := by
      unfold needsSample
      rw [any_congr _ _ _ fun f hfg => ?_]
      obtain ⟨hlt, -, r, hfname⟩ := mem_analysisOf (by rw [← hanalysis]; exact hfg)
      rw [← habs'.numbered f (by rw [hn]; exact hlt),
        ← habs.numbered f (by rw [hn]; exact hlt)]
      refine frame_of_lists hf hadd hdel ?_ ?_ σ
      · rw [hfname]
        simp [haveRock, fullS, hwq]
      · rw [hfname]
        simp [emptyS, atRockSample]
    have hnew : g ∈ (rockToSample dd s').toList := by
      rw [rockToSample_toList]
      refine List.mem_filter.mpr ⟨by simpa using hgbase, ?_⟩
      have holdp := (List.mem_filter.mp hold).2
      simpa [liveS, hneeds, hgoal.rock g hgbase] using holdp
    simpa using hnew
  have hsoil : soilToSample dd s' = soilToSample dd s :=
    soilToSample_congr hgoal.soil hsoilNeeds
  have hrockSize : (rockToSample dd s).size ≤ (rockToSample dd s').size + 1 := by
    have holdnd : (rockToSample dd s).toList.Nodup := by
      rw [rockToSample_toList]
      exact hnd.filter _
    refine sample_size_le_succ holdnd hrock ?_
    intro g hg G hG hwp
    have hgbase : g ∈ dd.rockGoals := by
      have hgl : g ∈ (rockToSample dd s).toList := by simpa using hg
      rw [rockToSample_toList] at hgl
      simpa using (List.mem_filter.mp hgl).1
    have hGbase : G ∈ dd.rockGoals := by
      have hGl : G ∈ (rockToSample dd s).toList := by simpa using hG
      rw [rockToSample_toList] at hGl
      simpa using (List.mem_filter.mp hGl).1
    exact rockGoals_waypoint_inj hp rel g hgbase G hGbase hwp
  have hsamples : samples dd s ≤ samples dd s' + 1 := by
    unfold samples
    rw [hsoil]
    omega
  obtain ⟨fe, felt, fename⟩ := numbered_of_op d p rel ho
    (Or.inl (pre_mem_op hf hemp (empty_dynamic hp.domain)))
  have fetrue : s.test fe = true := by
    rw [← habs.numbered fe (by rw [hn]; exact felt), fename]
    exact pre_holds hf hemp (empty_dynamic hp.domain) happ
  have fedel : emptyS st ∈ o.del := by
    refine del_kept hf (by rw [hdel]; simp) ?_ hemp (empty_dynamic hp.domain)
    rw [hadd]
    simp [emptyS, fullS, haveRock]
  have fenadd : emptyS st ∉ o.add := fun hmem => by
    have hmem' := hf.subAdd _ hmem
    rw [hadd] at hmem'
    simp [emptyS, fullS, haveRock] at hmem'
  have fefalse : s'.test fe = false := by
    rw [← habs'.numbered fe (by rw [hn]; exact felt), fename]
    exact applyA_del σ fedel fenadd
  have femem : fe ∈ dd.emptyFacts := mem_emptyFacts_of felt fename rfl
  have hempDrop : emptyStores dd s = emptyStores dd s' + 1 := by
    unfold emptyStores
    refine pool_drop_one dd.emptyFacts ?_ fe femem fetrue fefalse ?_
    · rw [compile_emptyFacts]
      exact factsWith_nodup _ _
    · intro f hfm hne
      obtain ⟨hlt, hpred⟩ := emptyFacts_pred hfm
      apply Eq.symm
      rw [← habs'.numbered f (by rw [hn]; exact hlt),
        ← habs.numbered f (by rw [hn]; exact hlt)]
      refine frame_of_lists hf hadd hdel ?_ ?_ σ
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        constructor <;> intro hname <;> rw [hname] at hpred <;>
          simp [fullS, haveRock] at hpred
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        constructor
        · intro hname
          exact hne (factNames_inj hlt felt (hname.trans fename.symm))
        · intro hname
          rw [hname] at hpred
          simp [atRockSample] at hpred
  refine .resource
    { goals := hgoal
      RcLe := Rc_le_of_rock_sample hsoil hrock hfind hocc hhere hzero
      baseDrop := ?_ }
  have hcomm : communicate dd s' = communicate dd s := by
    unfold communicate
    rw [unmetSoil_congr hgoal.soil, unmetRock_congr hgoal.rock,
      unmetImage_congr hgoal.image]
  have himages : images dd s' = images dd s := images_congr hgoal.image himage
  refine baseCount_le_succ (dc := 0) (ds := 1) (di := 0) (dp := 0) (de := 0)
    (by omega) hsamples (by omega) (by omega) ?_ (by omega)
  omega

open Planner.ExampleHeuristics.Rovers in
/-- **A `take_image` is a `ResourceStep`.**  At most one tracked image becomes
held, and the calibration spent by the action compensates that change in the
paired image-minus-calibration term. -/
theorem takeImage_schemaStep (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (ho : o ∈ groundedOps d p rel) (hf : OpFacts d p o)
    {r q ob c m : Pddl.Name}
    (hs : hf.inst.schema = takeImageA) (hargs : hf.inst.args = [r, q, ob, c, m])
    {s s' : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (habs' : Abstracts (ground d p rel) s' (o.applyA σ))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (happ : o.applicableA σ)
    (hnd : (compile (ground d p rel)).imageGoals.toList.Nodup) :
    SchemaStep (compile (ground d p rel)) s s' := by
  classical
  let dd := compile (ground d p rel)
  change SchemaStep dd s s'
  obtain ⟨hpreCal, -, hadd, hdel⟩ := takeImage_atoms hf.inst hs hargs
  have frame : ∀ (P : Pddl.Name), P ≠ "have_image" → P ≠ "calibrated" →
      ∀ {f : Fact}, f < (ground d p rel).factNames.size →
      ((ground d p rel).factNames.getD f default).pred = P →
      s'.test f = s.test f := by
    intro P himg hcal f hlt hpred
    refine test_frame_pred hf ?_ ?_ habs habs' hn hlt hpred <;> intro a hm hbad
    · rcases takeImage_touches hf.inst hs hargs (Or.inl hm) with h | h <;> rw [h] at hbad
      · exact himg hbad.symm
      · exact hcal hbad.symm
    · rcases takeImage_touches hf.inst hs hargs (Or.inr hm) with h | h <;> rw [h] at hbad
      · exact himg hbad.symm
      · exact hcal hbad.symm
  have hgoal : GoalsFixed dd s s' := by
    refine { soil := fun g hg => ?_, rock := fun g hg => ?_, image := fun g hg => ?_ }
    · obtain ⟨hlt, w, hname⟩ := soilGoals_name d p rel g hg
      exact frame "communicated_soil_data" (by decide) (by decide) hlt (by rw [hname])
    · obtain ⟨hlt, w, hname⟩ := rockGoals_name d p rel g hg
      exact frame "communicated_rock_data" (by decide) (by decide) hlt (by rw [hname])
    · obtain ⟨hlt, ob', m', hname⟩ := imageGoals_name d p rel g hg
      exact frame "communicated_image_data" (by decide) (by decide) hlt (by rw [hname])
  have hsoilNeeds : ∀ g ∈ dd.soilGoals, needsSample s' g = needsSample s g := by
    intro g hg
    unfold needsSample
    rw [any_congr _ _ _ fun f hfg => ?_]
    obtain ⟨hlt, hpred⟩ := soilGoal_analysis_pred hg hfg
    exact frame "have_soil_analysis" (by decide) (by decide) hlt hpred
  have hrockNeeds : ∀ g ∈ dd.rockGoals, needsSample s' g = needsSample s g := by
    intro g hg
    unfold needsSample
    rw [any_congr _ _ _ fun f hfg => ?_]
    obtain ⟨hlt, hpred⟩ := rockGoal_analysis_pred hg hfg
    exact frame "have_rock_analysis" (by decide) (by decide) hlt hpred
  have hfind : ∀ ri, roverFind dd s' ri = roverFind dd s ri := by
    intro ri
    unfold roverFind
    refine array_find?_congr _ _ _ fun e he => ?_
    obtain ⟨hlt, hpred⟩ := roverAt_pred he
    exact frame "at" (by decide) (by decide) hlt hpred
  have hocc : ∀ w, occupied dd s' w = occupied dd s w := by
    intro w
    unfold occupied
    refine any_congr _ _ _ fun facts hfacts => ?_
    refine any_congr _ _ _ fun e he => ?_
    obtain ⟨hlt, hpred⟩ := roverAt_mem_pred hfacts he
    rw [frame "at" (by decide) (by decide) hlt hpred]
  have hempty : emptyStores dd s' = emptyStores dd s := by
    unfold emptyStores
    refine countHolding_congr _ fun f hfm => ?_
    obtain ⟨hlt, hpred⟩ := emptyFacts_pred hfm
    exact frame "empty" (by decide) (by decide) hlt hpred
  have himageOther : ∀ g ∈ dd.imageGoals,
      (ground d p rel).factNames.getD g.goalFact default ≠ commImage ob m →
      hasImage s' g = hasImage s g := by
    intro g hg hgoalName
    obtain ⟨-, ob', m', hname⟩ := imageGoals_name d p rel g hg
    have hkeys : ¬ (ob' = ob ∧ m' = m) := by
      rintro ⟨rfl, rfl⟩
      exact hgoalName hname
    have hhave := imageGoal_have_eq d p rel g hg ob' m' hname
    unfold hasImage
    rw [any_congr _ _ _ fun f hfg => ?_]
    obtain ⟨hlt, r', hfname⟩ := mem_haveFacts (by rw [← hhave]; exact hfg)
    rw [← habs'.numbered f (by rw [hn]; exact hlt),
      ← habs.numbered f (by rw [hn]; exact hlt)]
    refine frame_of_lists hf hadd hdel ?_ ?_ σ
    · rw [hfname]
      intro hmem
      have hEq : ({ pred := "have_image", args := [r', ob', m'] } : GroundAtom) =
          haveImage r ob m := by simpa using hmem
      have ha := congrArg GroundAtom.args hEq
      simp [haveImage] at ha
      exact hkeys ⟨ha.2.1, ha.2.2⟩
    · rw [hfname]
      simp [calibrated]
  have himages : images dd s ≤ images dd s' + 1 := by
    unfold images
    rw [size_filter_toList, size_filter_toList, images_inner, images_inner]
    by_cases hex : ∃ G ∈ dd.imageGoals,
        (ground d p rel).factNames.getD G.goalFact default = commImage ob m
    · obtain ⟨G, hG, hGname⟩ := hex
      refine length_filter_le_succ _ _ _ G hnd fun g hg hne => ?_
      have hgmem : g ∈ dd.imageGoals := by simpa using hg
      have hname : (ground d p rel).factNames.getD g.goalFact default ≠
          commImage ob m := by
        intro hbad
        apply hne
        exact imageGoals_goalFact_inj hp rel g hgmem G hG
          (factNames_inj (imageGoals_name d p rel g hgmem).1
            (imageGoals_name d p rel G hG).1 (hbad.trans hGname.symm))
      have hi := himageOther g hgmem hname
      unfold hasImage at hi
      simp only [liveI]
      rw [hi, hgoal.image g hgmem]
    · simp only [not_exists, not_and] at hex
      have heq : (dd.imageGoals.toList.filter fun g =>
          (!g.haveFacts.any fun f => s.test f) && liveI s g) =
          (dd.imageGoals.toList.filter fun g =>
            (!g.haveFacts.any fun f => s'.test f) && liveI s' g) := by
        refine List.filter_congr fun g hg => ?_
        have hgmem : g ∈ dd.imageGoals := by simpa using hg
        have hi := himageOther g hgmem (hex g hgmem)
        unfold hasImage at hi
        simp only [liveI]
        rw [hi, hgoal.image g hgmem]
      rw [heq]
      exact Nat.le_succ _
  have hsoil : soilToSample dd s' = soilToSample dd s :=
    soilToSample_congr hgoal.soil hsoilNeeds
  have hrock : rockToSample dd s' = rockToSample dd s :=
    rockToSample_congr hgoal.rock hrockNeeds
  have hsamples : samples dd s' = samples dd s := by
    unfold samples
    rw [hsoil, hrock]
  obtain ⟨fc, fclt, fcname⟩ := numbered_of_op d p rel ho
    (Or.inl (pre_mem_op hf hpreCal (calibrated_dynamic hp.domain)))
  have fctrue : s.test fc = true := by
    rw [← habs.numbered fc (by rw [hn]; exact fclt), fcname]
    exact pre_holds hf hpreCal (calibrated_dynamic hp.domain) happ
  have fcdel : calibrated c r ∈ o.del := by
    refine del_kept hf (by rw [hdel]; simp) ?_ hpreCal (calibrated_dynamic hp.domain)
    rw [hadd]
    simp [calibrated, haveImage]
  have fcnadd : calibrated c r ∉ o.add := fun hmem => by
    have hmem' := hf.subAdd _ hmem
    rw [hadd] at hmem'
    simp [calibrated, haveImage] at hmem'
  have fcfalse : s'.test fc = false := by
    rw [← habs'.numbered fc (by rw [hn]; exact fclt), fcname]
    exact applyA_del σ fcdel fcnadd
  have fcmem : fc ∈ dd.calibratedFacts := mem_calibratedFacts_of fclt fcname rfl
  have hcalDrop : ExampleHeuristics.Rovers.calibrated dd s =
      ExampleHeuristics.Rovers.calibrated dd s' + 1 := by
    unfold ExampleHeuristics.Rovers.calibrated
    refine pool_drop_one dd.calibratedFacts ?_ fc fcmem fctrue fcfalse ?_
    · rw [compile_calibratedFacts]
      exact factsWith_nodup _ _
    · intro f hfm hne
      obtain ⟨hlt, hpred⟩ := calibratedFacts_pred hfm
      apply Eq.symm
      rw [← habs'.numbered f (by rw [hn]; exact hlt),
        ← habs.numbered f (by rw [hn]; exact hlt)]
      refine frame_of_lists hf hadd hdel ?_ ?_ σ
      · intro hmem
        have hname : (ground d p rel).factNames.getD f default = haveImage r ob m := by
          simpa using hmem
        rw [hname] at hpred
        simp [haveImage] at hpred
      · intro hmem
        have hname : (ground d p rel).factNames.getD f default = calibrated c r := by
          simpa using hmem
        exact hne (factNames_inj hlt fclt (hname.trans fcname.symm))
  refine .resource
    { goals := hgoal
      RcLe := Nat.le_of_eq (Rc_congr hsoil hrock hfind hocc).symm
      baseDrop := ?_ }
  have hcomm : communicate dd s' = communicate dd s := by
    unfold communicate
    rw [unmetSoil_congr hgoal.soil, unmetRock_congr hgoal.rock,
      unmetImage_congr hgoal.image]
  refine baseCount_le_succ (dc := 0) (ds := 0) (di := 1) (dp := 0) (de := 0)
    (by omega) (by omega) himages (by omega) (by omega) (by omega)

open Planner.ExampleHeuristics.Rovers in
/-- **A `calibrate` is a `ResourceStep`.**  It touches only `calibrated`, so
every family but that pool is framed, and the pool moves by one at most. -/
theorem calibrate_schemaStep {o : AtomOp} (hf : OpFacts d p o)
    {r c tt w : Pddl.Name}
    (hs : hf.inst.schema = calibrateA) (hargs : hf.inst.args = [r, c, tt, w])
    {s s' : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (habs' : Abstracts (ground d p rel) s' (o.applyA σ))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size) :
    SchemaStep (compile (ground d p rel)) s s' := by
  obtain ⟨-, hadd, hdel⟩ := calibrate_atoms hf.inst hs hargs
  -- Nothing but `calibrated` moves.
  have frame : ∀ (P : Pddl.Name), P ≠ "calibrated" → ∀ {f : Fact},
      f < (ground d p rel).factNames.size →
      ((ground d p rel).factNames.getD f default).pred = P →
      s'.test f = s.test f := by
    intro P hP f hlt hpred
    refine test_frame_pred hf ?_ ?_ habs habs' hn hlt hpred <;> intro a hm hbad
    · rw [calibrate_touches hf.inst hs hargs (Or.inl hm)] at hbad; exact hP hbad.symm
    · rw [calibrate_touches hf.inst hs hargs (Or.inr hm)] at hbad; exact hP hbad.symm
  obtain ⟨h1, h2, h3, h4, h5⟩ := frames_of_untouched hf (fun a ha => by
    rw [calibrate_touches hf.inst hs hargs ha]
    exact ⟨by decide, by decide, by decide, by decide⟩) habs habs' hn
  have hgoal : GoalsFixed (compile (ground d p rel)) s s' := by
    refine { soil := fun g hg => ?_, rock := fun g hg => ?_, image := fun g hg => ?_ }
    · obtain ⟨hlt, ww, hname⟩ := soilGoals_name d p rel g hg
      exact frame "communicated_soil_data" (by decide) hlt (by rw [hname])
    · obtain ⟨hlt, ww, hname⟩ := rockGoals_name d p rel g hg
      exact frame "communicated_rock_data" (by decide) hlt (by rw [hname])
    · obtain ⟨hlt, ob, m, hname⟩ := imageGoals_name d p rel g hg
      exact frame "communicated_image_data" (by decide) hlt (by rw [hname])
  refine .resource (resourceStep_of_frames (dcal := 1) (demp := 0)
    hgoal h1 h2 h3 h4 h5 ?_ ?_ (by omega))
  · have htouch : ∀ a, (a ∈ hf.inst.add ∨ a ∈ hf.inst.del) →
        a = calibrated c r ∨ a.pred ≠ "calibrated" := by
      intro a ha
      rcases ha with ha | ha
      · rw [hadd] at ha; exact Or.inl (by simpa using ha)
      · rw [hdel] at ha; simp at ha
    exact (pool_le_one hf htouch _
      (by rw [compile_calibratedFacts]; exact factsWith_nodup _ _)
      (fun f hf' => (calibratedFacts_pred hf').1)
      (fun f hf' => (calibratedFacts_pred hf').2) habs habs' hn).1
  · refine Nat.le_of_eq (countHolding_congr' _ fun f hf' => ?_)
    obtain ⟨hlt, hpred⟩ := emptyFacts_pred hf'
    exact frame "empty" (by decide) hlt hpred

open Planner.ExampleHeuristics.Rovers in
/-- **A `drop` is a `ResourceStep`.**  It touches only the store, restoring an
`empty` and spending a `full`; every family the base count reads is framed but
the `empty` pool, which gains one at most. -/
theorem drop_schemaStep {o : AtomOp} (hf : OpFacts d p o) {x y : Pddl.Name}
    (hs : hf.inst.schema = dropA) (hargs : hf.inst.args = [x, y])
    {s s' : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (habs' : Abstracts (ground d p rel) s' (o.applyA σ))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size) :
    SchemaStep (compile (ground d p rel)) s s' := by
  obtain ⟨-, hadd, hdel⟩ := drop_atoms hf.inst hs hargs
  have frame : ∀ (P : Pddl.Name), P ≠ "empty" → P ≠ "full" → ∀ {f : Fact},
      f < (ground d p rel).factNames.size →
      ((ground d p rel).factNames.getD f default).pred = P →
      s'.test f = s.test f := by
    intro P hP hP' f hlt hpred
    refine test_frame_pred hf ?_ ?_ habs habs' hn hlt hpred <;> intro a hm hbad
    · rcases drop_touches hf.inst hs hargs (Or.inl hm) with h | h <;> rw [h] at hbad
      · exact hP hbad.symm
      · exact hP' hbad.symm
    · rcases drop_touches hf.inst hs hargs (Or.inr hm) with h | h <;> rw [h] at hbad
      · exact hP hbad.symm
      · exact hP' hbad.symm
  obtain ⟨h1, h2, h3, h4, h5⟩ := frames_of_untouched hf (fun a ha => by
    rcases drop_touches hf.inst hs hargs ha with h | h <;> rw [h] <;>
      exact ⟨by decide, by decide, by decide, by decide⟩) habs habs' hn
  have hgoal : GoalsFixed (compile (ground d p rel)) s s' := by
    refine { soil := fun g hg => ?_, rock := fun g hg => ?_, image := fun g hg => ?_ }
    · obtain ⟨hlt, ww, hname⟩ := soilGoals_name d p rel g hg
      exact frame "communicated_soil_data" (by decide) (by decide) hlt (by rw [hname])
    · obtain ⟨hlt, ww, hname⟩ := rockGoals_name d p rel g hg
      exact frame "communicated_rock_data" (by decide) (by decide) hlt (by rw [hname])
    · obtain ⟨hlt, ob, m, hname⟩ := imageGoals_name d p rel g hg
      exact frame "communicated_image_data" (by decide) (by decide) hlt (by rw [hname])
  refine .resource (resourceStep_of_frames (dcal := 0) (demp := 1)
    hgoal h1 h2 h3 h4 h5 ?_ ?_ (by omega))
  · refine Nat.le_of_eq (countHolding_congr' _ fun f hf' => ?_)
    obtain ⟨hlt, hpred⟩ := calibratedFacts_pred hf'
    exact frame "calibrated" (by decide) (by decide) hlt hpred
  · have htouch : ∀ a, (a ∈ hf.inst.add ∨ a ∈ hf.inst.del) →
        a = emptyS y ∨ a.pred ≠ "empty" := by
      intro a ha
      rcases ha with ha | ha
      · rw [hadd] at ha; exact Or.inl (by simpa using ha)
      · rw [hdel] at ha
        obtain rfl : a = fullS y := by simpa using ha
        exact Or.inr (by simp [fullS])
    exact (pool_le_one hf htouch _
      (by rw [compile_emptyFacts]; exact factsWith_nodup _ _)
      (fun f hf' => (emptyFacts_pred hf').1)
      (fun f hf' => (emptyFacts_pred hf').2) habs habs' hn).1

/-! ### `NavigateStep`

`navigate` touches only `at`, so every family the base count reads is framed and
the goals do not move.  What is left of the shape is the two facts about
movement: where a rover can newly stand, and how far one edge can change a
distance.  Those are the step's own content and are taken as hypotheses here,
the way Floortile and Transport take `Distances.Sound`.
-/

open Planner.ExampleHeuristics.Rovers in
/-- **Everything but the movement of a `navigate` step.** -/
theorem navigateStep_of_bounds (rel : Bool)
    {o : AtomOp} (hf : OpFacts d p o)
    {x y z : Pddl.Name}
    (hs : hf.inst.schema = navigateA) (hargs : hf.inst.args = [x, y, z])
    {s s' : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (habs' : Abstracts (ground d p rel) s' (o.applyA σ))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    {dest : Nat}
    (hocc : ∀ w, occupied (compile (ground d p rel)) s' w = true →
      occupied (compile (ground d p rel)) s w = true ∨ w = dest)
    (hreach : ∀ crew w, reach (compile (ground d p rel)) s crew w
      ≤ 1 + reach (compile (ground d p rel)) s' crew w) :
    NavigateStep (compile (ground d p rel)) s s' dest := by
  -- `navigate` moves no atom whose predicate is not `at`.
  have frame : ∀ (P : Pddl.Name), P ≠ "at" → ∀ {f : Fact},
      f < (ground d p rel).factNames.size →
      ((ground d p rel).factNames.getD f default).pred = P →
      s'.test f = s.test f := by
    intro P hP f hlt hpred
    refine test_frame_pred hf ?_ ?_ habs habs' hn hlt hpred
    · intro a ha hbad
      rw [navigate_touches hf.inst hs hargs (Or.inl ha)] at hbad
      exact hP hbad.symm
    · intro a ha hbad
      rw [navigate_touches hf.inst hs hargs (Or.inr ha)] at hbad
      exact hP hbad.symm
  refine
    { quiet' := ?_, quietR := ?_, imageHeld := ?_, calib := ?_, emptyF := ?_,
      goals := ?_, occNew := hocc, reachStep := hreach }
  · intro g hg
    unfold needsSample
    rw [any_congr _ _ _ fun w hw => ?_]
    obtain ⟨h1, h2⟩ := soilGoal_analysis_pred hg hw
    exact frame _ (by decide) h1 h2
  · intro g hg
    unfold needsSample
    rw [any_congr _ _ _ fun w hw => ?_]
    obtain ⟨h1, h2⟩ := rockGoal_analysis_pred hg hw
    exact frame _ (by decide) h1 h2
  · intro g hg
    unfold hasImage
    rw [any_congr _ _ _ fun w hw => ?_]
    obtain ⟨h1, h2⟩ := imageGoal_have_pred hg hw
    exact frame _ (by decide) h1 h2
  · intro f hf'
    obtain ⟨h1, h2⟩ := calibratedFacts_pred hf'
    exact frame _ (by decide) h1 h2
  · intro f hf'
    obtain ⟨h1, h2⟩ := emptyFacts_pred hf'
    exact frame _ (by decide) h1 h2
  · exact
      { soil := fun g hg => by
          obtain ⟨h1, w, h2⟩ := soilGoals_name d p rel g hg
          exact frame "communicated_soil_data" (by decide) h1 (by rw [h2])
        rock := fun g hg => by
          obtain ⟨h1, w, h2⟩ := rockGoals_name d p rel g hg
          exact frame "communicated_rock_data" (by decide) h1 (by rw [h2])
        image := fun g hg => by
          obtain ⟨h1, ob, m, h2⟩ := imageGoals_name d p rel g hg
          exact frame "communicated_image_data" (by decide) h1 (by rw [h2]) }

open Planner.ExampleHeuristics.Rovers in
/--
**A `navigate` puts a rover only where it arrived.**

A waypoint newly occupied must hold a fact that turned true, and the only fact a
`navigate` turns true is the `at` of its destination.  The waypoint list names
each waypoint once, so that fixes the index.
-/
theorem navigate_occNew (hp : Pinned d p) (rel : Bool)
    {o : AtomOp} (hf : OpFacts d p o)
    {x y z : Pddl.Name}
    (hs : hf.inst.schema = navigateA) (hargs : hf.inst.args = [x, y, z])
    {s s' : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (habs' : Abstracts (ground d p rel) s' (o.applyA σ))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    {dest : Nat}
    (hdest : ((ground d p rel).objectsOfTypes ["waypoint"]).findIdx? (· == z)
      = some dest) :
    ∀ w, occupied (compile (ground d p rel)) s' w = true →
      occupied (compile (ground d p rel)) s w = true ∨ w = dest := by
  obtain ⟨-, hadd, -⟩ := navigate_atoms hf.inst hs hargs
  intro w hw
  obtain ⟨facts, hfacts, e, he, hew, hte⟩ := occupied_iff.mp hw
  by_cases hprev : s.test e.1 = true
  · exact Or.inl (occupied_iff.mpr ⟨facts, hfacts, e, he, hew, hprev⟩)
  right
  obtain ⟨hlt, hwlt, r, hname⟩ := roverAt_mem_atom hfacts he
  -- The fact turned true, so its atom is the one `navigate` adds.
  have hσ' : (o.applyA σ) ((ground d p rel).factNames.getD e.1 default) = true := by
    rw [habs'.numbered e.1 (by rw [hn]; exact hlt)]; exact hte
  have hσ : σ ((ground d p rel).factNames.getD e.1 default) = false := by
    rcases hc : σ ((ground d p rel).factNames.getD e.1 default) with _ | _
    · rfl
    · exact absurd (by rw [← habs.numbered e.1 (by rw [hn]; exact hlt)]; exact hc) hprev
  have hmem : (ground d p rel).factNames.getD e.1 default ∈ [at_ x z] := by
    by_contra hc
    rw [falls_of_lists hf hadd hc hσ'] at hσ
    exact Bool.noConfusion hσ
  have hatom : (ground d p rel).factNames.getD e.1 default = at_ x z := by
    simpa using hmem
  -- So the waypoint it names is the destination.
  have hz : ((ground d p rel).objectsOfTypes ["waypoint"]).getD e.2 default = z := by
    rw [hname] at hatom
    exact (by simpa [at_] using hatom : _ ∧ _).2
  obtain ⟨hdlt, hdz⟩ := findIdx_sound hdest
  have hnd : ((ground d p rel).objectsOfTypes ["waypoint"]).toList.Nodup :=
    objsOf_nodup hp.namesNodup
  have : e.2 = dest := by
    refine (List.Nodup.getElem_inj_iff hnd (hi := by simpa using hwlt)
      (hj := by simpa using hdlt)).mp ?_
    have h1 : ((ground d p rel).objectsOfTypes ["waypoint"])[e.2]'hwlt = z := by
      rw [← hz, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hwlt,
        Option.getD_some]
    have h2 : ((ground d p rel).objectsOfTypes ["waypoint"])[dest]'hdlt = z := by
      rw [← hdz, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hdlt,
        Option.getD_some]
    simpa using h1.trans h2.symm
  rw [← hew, this]

/-! ### A `communicate` is a step, either way

Three cases: the announced goal is one the tables hold and is unmet — the count
drops, and the step is a `Comm*Step`; it is held but already met, or it is not
held at all — nothing the heuristic counts moves, and the step is a
`ResourceStep`.
-/

open Planner.ExampleHeuristics.Rovers in
/-- **Every `communicate_soil_data` is one of the two shapes.** -/
theorem commSoil_schemaStep (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (ho : o ∈ groundedOps d p rel) (hfa : OpFactsAdd d p o)
    {r l q x y : Pddl.Name}
    (hs : hfa.inst.schema = commSoilA) (hargs : hfa.inst.args = [r, l, q, x, y])
    {s s' : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (habs' : Abstracts (ground d p rel) s' (o.applyA σ))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (happ : o.applicableA σ) :
    SchemaStep (compile (ground d p rel)) s s' := by
  obtain ⟨hadd, hdel⟩ : hfa.inst.add = [commSoil q] ∧ hfa.inst.del = [] := by
    obtain ⟨-, -, ha, hd⟩ := commSoil_atoms hfa.inst hs hargs; exact ⟨ha, hd⟩
  by_cases hex : ∃ G ∈ (compile (ground d p rel)).soilGoals,
      (ground d p rel).factNames.getD G.goalFact default = commSoil q ∧
        s.test G.goalFact = false
  · obtain ⟨G, hG, hGname, hunmet⟩ := hex
    exact .commSoil G
      (commSoilStep_of hp rel ho hfa hs hargs habs habs' hn happ hG hGname hunmet)
  · refine .resource (resourceStep_of_quiet
      (commSoil_quiet hfa.toOpFacts hs hargs habs habs' hn)
      (goalsFixed_of hfa.toOpFacts hadd hdel habs habs' hn ?_ ?_ ?_))
    · intro g hg
      by_cases hname : (ground d p rel).factNames.getD g.goalFact default
          = commSoil q
      · refine Or.inr ?_
        by_contra hc
        exact hex ⟨g, hg, hname, by simpa using hc⟩
      · exact Or.inl hname
    · intro g hg
      obtain ⟨-, w, hname⟩ := rockGoals_name d p rel g hg
      exact Or.inl (by rw [hname]; simp [commSoil])
    · intro g hg
      obtain ⟨-, ob, m, hname⟩ := imageGoals_name d p rel g hg
      exact Or.inl (by rw [hname]; simp [commSoil])

open Planner.ExampleHeuristics.Rovers in
/-- **Every `communicate_rock_data` is one of the two shapes.** -/
theorem commRock_schemaStep (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (ho : o ∈ groundedOps d p rel) (hfa : OpFactsAdd d p o)
    {r l q x y : Pddl.Name}
    (hs : hfa.inst.schema = commRockA) (hargs : hfa.inst.args = [r, l, q, x, y])
    {s s' : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (habs' : Abstracts (ground d p rel) s' (o.applyA σ))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (happ : o.applicableA σ) :
    SchemaStep (compile (ground d p rel)) s s' := by
  obtain ⟨hadd, hdel⟩ : hfa.inst.add = [commRock q] ∧ hfa.inst.del = [] := by
    obtain ⟨-, -, ha, hd⟩ := commRock_atoms hfa.inst hs hargs; exact ⟨ha, hd⟩
  by_cases hex : ∃ G ∈ (compile (ground d p rel)).rockGoals,
      (ground d p rel).factNames.getD G.goalFact default = commRock q ∧
        s.test G.goalFact = false
  · obtain ⟨G, hG, hGname, hunmet⟩ := hex
    exact .commRock G
      (commRockStep_of hp rel ho hfa hs hargs habs habs' hn happ hG hGname hunmet)
  · refine .resource (resourceStep_of_quiet
      (commRock_quiet hfa.toOpFacts hs hargs habs habs' hn)
      (goalsFixed_of hfa.toOpFacts hadd hdel habs habs' hn ?_ ?_ ?_))
    · intro g hg
      obtain ⟨-, w, hname⟩ := soilGoals_name d p rel g hg
      exact Or.inl (by rw [hname]; simp [commRock])
    · intro g hg
      by_cases hname : (ground d p rel).factNames.getD g.goalFact default
          = commRock q
      · refine Or.inr ?_
        by_contra hc
        exact hex ⟨g, hg, hname, by simpa using hc⟩
      · exact Or.inl hname
    · intro g hg
      obtain ⟨-, ob, m, hname⟩ := imageGoals_name d p rel g hg
      exact Or.inl (by rw [hname]; simp [commRock])

open Planner.ExampleHeuristics.Rovers in
/-- **Every `communicate_image_data` is one of the two shapes.** -/
theorem commImage_schemaStep (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (ho : o ∈ groundedOps d p rel) (hfa : OpFactsAdd d p o)
    {r l ob m x y : Pddl.Name}
    (hs : hfa.inst.schema = commImageA)
    (hargs : hfa.inst.args = [r, l, ob, m, x, y])
    {s s' : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (habs' : Abstracts (ground d p rel) s' (o.applyA σ))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (happ : o.applicableA σ) :
    SchemaStep (compile (ground d p rel)) s s' := by
  obtain ⟨hadd, hdel⟩ : hfa.inst.add = [commImage ob m] ∧ hfa.inst.del = [] := by
    obtain ⟨-, -, ha, hd⟩ := commImage_atoms hfa.inst hs hargs; exact ⟨ha, hd⟩
  by_cases hex : ∃ G ∈ (compile (ground d p rel)).imageGoals,
      (ground d p rel).factNames.getD G.goalFact default = commImage ob m ∧
        s.test G.goalFact = false
  · obtain ⟨G, hG, hGname, hunmet⟩ := hex
    exact .commImage G
      (commImageStep_of hp rel ho hfa hs hargs habs habs' hn happ hG hGname hunmet)
  · refine .resource (resourceStep_of_quiet
      (commImage_quiet hfa.toOpFacts hs hargs habs habs' hn)
      (goalsFixed_of hfa.toOpFacts hadd hdel habs habs' hn ?_ ?_ ?_))
    · intro g hg
      obtain ⟨-, w, hname⟩ := soilGoals_name d p rel g hg
      exact Or.inl (by rw [hname]; simp [commImage])
    · intro g hg
      obtain ⟨-, w, hname⟩ := rockGoals_name d p rel g hg
      exact Or.inl (by rw [hname]; simp [commImage])
    · intro g hg
      by_cases hname : (ground d p rel).factNames.getD g.goalFact default
          = commImage ob m
      · refine Or.inr ?_
        by_contra hc
        exact hex ⟨g, hg, hname, by simpa using hc⟩
      · exact Or.inl hname

open Planner.ExampleHeuristics.Rovers in
/--
**A `navigate` is a `SchemaStep`.**

Everything but the movement is framed; the movement itself is one edge of the
rover's own graph, and `Distances.Sound` bounds a distance across one edge.  The
soundness of the graph is a hypothesis, checked at runtime, exactly as Floortile
and Transport take it.
-/
theorem navigate_schemaStep (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (ho : o ∈ groundedOps d p rel) (hfa : OpFactsAdd d p o)
    {x y z : Pddl.Name}
    (hs : hfa.inst.schema = navigateA) (hargs : hfa.inst.args = [x, y, z])
    {s s' : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (habs' : Abstracts (ground d p rel) s' (o.applyA σ))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (happ : o.applicableA σ) (hone : OneAt σ) (hone' : OneAt (o.applyA σ))
    (hwnd : ((ground d p rel).objectsOfTypes ["waypoint"]).toList.Nodup)
    {ri yi zi : Nat}
    (hr : ri < ((ground d p rel).objectsOfTypes ["rover"]).size)
    (hrn : ((ground d p rel).objectsOfTypes ["rover"]).getD ri default = x)
    (hyi : ((ground d p rel).objectsOfTypes ["waypoint"]).findIdx? (· == y) = some yi)
    (hzi : ((ground d p rel).objectsOfTypes ["waypoint"]).findIdx? (· == z) = some zi)
    (hsound : Distances.Sound
      (roverGraph (ground d p rel)
        ((ground d p rel).objectsOfTypes ["waypoint"]) x)
      ((compile (ground d p rel)).dist.getD ri default))
    (hylt : yi < (roverGraph (ground d p rel)
      ((ground d p rel).objectsOfTypes ["waypoint"]) x).size)
    (hedge : zi ∈ (roverGraph (ground d p rel)
      ((ground d p rel).objectsOfTypes ["waypoint"]) x).adj.getD yi #[])
    (hother : ∀ r, r ≠ ri → ∀ e ∈ (compile (ground d p rel)).roverAt.getD r #[],
      s'.test e.1 = s.test e.1) :
    SchemaStep (compile (ground d p rel)) s s' := by
  -- The origin fact, from the precondition.
  have hpre : at_ x y ∈ hfa.inst.pre := by
    obtain ⟨h, -, -⟩ := navigate_atoms hfa.inst hs hargs; exact h
  obtain ⟨fy, hfylt, hfyn⟩ := numbered_of_op d p rel ho
    (Or.inl (pre_mem_op hfa.toOpFacts hpre (at_dynamic hp.domain)))
  have hytrue : s.test fy = true := by
    rw [← habs.numbered fy (by rw [hn]; exact hfylt), hfyn]
    exact pre_holds hfa.toOpFacts hpre (at_dynamic hp.domain) happ
  -- The destination fact, from the add.
  have hzadd : at_ x z ∈ o.add := navigate_add_mem hp hfa hs hargs
  obtain ⟨fz, hfzlt, hfzn⟩ := numbered_of_op d p rel ho (Or.inr (Or.inl hzadd))
  have hztrue : s'.test fz = true := by
    rw [← habs'.numbered fz (by rw [hn]; exact hfzlt), hfzn]
    exact navigate_adds hp hfa hs hargs σ
  refine .navigate zi (navigateStep_of_bounds rel hfa.toOpFacts hs hargs habs habs' hn
    (navigate_occNew hp rel hfa.toOpFacts hs hargs habs habs' hn hzi) (fun crew w => ?_))
  refine reach_le_of_move' ?_ ?_ hsound hylt hedge (fun r _ hrri => ?_)
  · exact roverVal_at habs hn hwnd hone hr hrn hyi hfylt hfyn
      hytrue w
  · exact roverVal_at habs' hn hwnd hone' hr hrn hzi hfzlt hfzn
      hztrue w
  · exact roverVal_congr _ s s' r w (hother r hrri)

/-! ### Closing the lifted task proof -/

/-- A static precondition of an applicable grounded schema occurs in the
compiled task's static table. -/
theorem static_of_pre (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (hf : OpFacts d p o) {a : GroundAtom} (hmem : a ∈ hf.inst.pre)
    (hstatic : (staticPredicates d).contains a.pred = true) :
    a ∈ (ground d p rel).staticWith a.pred := by
  have hmem' : a ∈ hf.inst.schema.pre.map
      (instAtom hf.inst.schema.params hf.inst.args) := hmem
  obtain ⟨y, hy, hval⟩ := List.mem_map.mp hmem'
  have hinit : a ∈ p.init := by
    have hpred : y.pred = a.pred := by rw [← hval]; rfl
    have h := hf.staticHeld y hy (by rw [hpred]; exact hstatic)
    rw [hval] at h
    exact mem_init_of_contains h
  have hnot : a ∉ allAtoms (groundedOps d p rel) p.goal.toArray := by
    intro hc
    have hfalse := hp.goalDynamic a (mem_goal_of_static d p rel hc hstatic)
    rw [hstatic] at hfalse
    exact Bool.noConfusion hfalse
  exact mem_staticWith d p rel hinit hnot rfl

/-- A typed rover argument has an index in the rover table. -/
theorem rover_index (hp : Pinned d p) (rel : Bool) {r : Pddl.Name}
    (hw : WellTyped d (allObjects d p) "rover" r) :
    ∃ ri, ((ground d p rel).objectsOfTypes ["rover"]).findIdx? (· == r) = some ri :=
  findIdx_total (mem_objsOf_of_wellTyped hp.roverTypeExact hw)

/-- A typed waypoint argument has an index in the waypoint table. -/
theorem waypoint_index (hp : Pinned d p) (rel : Bool) {w : Pddl.Name}
    (hw : WellTyped d (allObjects d p) "waypoint" w) :
    ∃ wi, ((ground d p rel).objectsOfTypes ["waypoint"]).findIdx? (· == w) = some wi :=
  findIdx_total (mem_objsOf_of_wellTyped hp.waypointTypeExact hw)

open Planner.ExampleHeuristics.Rovers in
/-- `roverGraph` and the waypoint table assign the same index when waypoint
names are distinct. -/
theorem roverGraph_find_of_findIdx {t : Task} {r w : Pddl.Name} {wi : Nat}
    (hnd : (t.objectsOfTypes ["waypoint"]).toList.Nodup)
    (hwi : (t.objectsOfTypes ["waypoint"]).findIdx? (· == w) = some wi) :
    (roverGraph t (t.objectsOfTypes ["waypoint"]) r).find? w = some wi := by
  obtain ⟨hwilt, hwin⟩ := findIdx_sound hwi
  have hwmem : w ∈ t.objectsOfTypes ["waypoint"] := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hwilt,
      Option.getD_some] at hwin
    rw [← hwin]
    exact Array.getElem_mem hwilt
  have his : ((roverGraph t (t.objectsOfTypes ["waypoint"]) r).find? w).isSome := by
    simpa [roverGraph] using
      (Graph.find?_isSome' (nodes := t.objectsOfTypes ["waypoint"])
        (edges := t.staticAtoms.filterMap fun a =>
          if a.pred == "can_traverse" then
            match a.args with
            | [x, y, z] =>
                if x == r && (t.staticWith "visible").any (fun b => b.args == [y, z])
                then some ({ pred := "can_traverse", args := [y, z] } : GroundAtom)
                else none
            | _ => none
          else none) hwmem)
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp his
  have hjlt := Graph.find?_lt' hj
  have hjn := Graph.find?_node hj
  have hji : j = wi := by
    refine (List.Nodup.getElem_inj_iff hnd (hi := by simpa [roverGraph, Graph.size] using hjlt)
      (hj := by simpa using hwilt)).mp ?_
    have h1 : (t.objectsOfTypes ["waypoint"])[j]'(by
        simpa [roverGraph, Graph.size] using hjlt) = w := by
      have h1d : (t.objectsOfTypes ["waypoint"]).getD j "" = w := by
        simpa [roverGraph, Graph.ofEdges] using hjn
      rw [Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem (by simpa [roverGraph, Graph.size] using hjlt),
        Option.getD_some] at h1d
      exact h1d
    have h2 : (t.objectsOfTypes ["waypoint"])[wi]'hwilt = w := by
      rw [← hwin, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hwilt,
        Option.getD_some]
    simpa using h1.trans h2.symm
  rwa [hji] at hj

open Planner.ExampleHeuristics.Rovers in
/-- A rover named by a static equipment fact occurs in the compiled crew. -/
theorem mem_equipped_of {t : Task} {pred r : Pddl.Name} {ri : Nat}
    (heq : ({ pred := pred, args := [r] } : GroundAtom) ∈ t.staticWith pred)
    (hri : (t.objectsOfTypes ["rover"]).findIdx? (· == r) = some ri) :
    ri ∈ (t.staticWith pred).filterMap fun a =>
      match a.args with
      | [x] => (t.objectsOfTypes ["rover"]).findIdx? (· == x)
      | _ => none := by
  refine Array.mem_filterMap.mpr ⟨_, heq, ?_⟩
  simp [hri]

open Planner.ExampleHeuristics.Rovers in
/-- An equipped rover whose current position is the target makes `reach` zero. -/
theorem reach_eq_zero_of_mem {dd : ExampleHeuristics.Rovers.Data} {s : State}
    {crew : Array Nat} {r w : Nat} (hr : r ∈ crew)
    (hv : roverVal dd s r w = some 0) : reach dd s crew w = 0 := by
  let F : Option Nat → Nat → Option Nat := fun acc i =>
    match (dd.roverAt.getD i #[]).find? fun x => s.test x.1 with
    | some (_, here) =>
        let v := (dd.dist.getD i default).get here w
        some (match acc with | none => v | some a => min a v)
    | none => acc
  have habsorb : ∀ l : List Nat, l.foldl F (some 0) = some 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons i rest ih =>
        rw [List.foldl_cons]
        have hstep : F (some 0) i = some 0 := by
          unfold F
          split <;> simp
        rw [hstep]
        exact ih
  have hhit : ∀ (l : List Nat) (acc : Option Nat), r ∈ l →
      l.foldl F acc = some 0 := by
    intro l
    induction l with
    | nil => simp
    | cons i rest ih =>
        intro acc hmem
        rw [List.foldl_cons]
        rcases List.mem_cons.mp hmem with rfl | hrest
        · have hstep : F acc r = some 0 := by
            have hFval : F acc r =
                match roverVal dd s r w with
                | some v => some (match acc with | none => v | some a => min a v)
                | none => acc := by
              unfold F
              rcases hfind : (dd.roverAt.getD r #[]).find? (fun x => s.test x.1) with _ | e
              · rw [hfind]
                unfold roverVal
                rw [hfind]
                rfl
              · rw [hfind]
                unfold roverVal
                rw [hfind]
                rfl
            rw [hFval, hv]
            rcases acc with _ | a <;> simp
          rw [hstep]
          exact habsorb rest
        · exact ih _ hrest
  unfold reach
  change (crew.foldl F none).getD 0 = 0
  rw [← Array.foldl_toList]
  rw [hhit crew.toList none (by simpa using hr)]
  rfl

open Planner.ExampleHeuristics.Rovers in
/-- The position and equipment preconditions of a sampler make its navigation
term zero at the sampled waypoint. -/
theorem sample_ready (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (ho : o ∈ groundedOps d p rel) (hf : OpFacts d p o)
    {x st q equipPred : Pddl.Name} {crew : Array Nat}
    (hs : hf.inst.schema.params = [roverP "?x", storeP "?s", waypointP "?p"])
    (hargs : hf.inst.args = [x, st, q])
    (hat : at_ x q ∈ hf.inst.pre)
    (hequip : ({ pred := equipPred, args := [x] } : GroundAtom) ∈ hf.inst.pre)
    (hstatic : (staticPredicates d).contains equipPred = true)
    (hcrew : crew = ((ground d p rel).staticWith equipPred).filterMap fun a =>
      match a.args with
      | [r] => ((ground d p rel).objectsOfTypes ["rover"]).findIdx? (· == r)
      | _ => none)
    {s : State} {sigma : AtomState}
    (habs : Abstracts (ground d p rel) s sigma)
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (hone : OneAt sigma) (happ : o.applicableA sigma)
    (hsound : ∀ ri, ri < ((ground d p rel).objectsOfTypes ["rover"]).size →
      Distances.Sound
        (roverGraph (ground d p rel)
          ((ground d p rel).objectsOfTypes ["waypoint"])
          (((ground d p rel).objectsOfTypes ["rover"]).getD ri default))
        ((compile (ground d p rel)).dist.getD ri default)) :
    ∃ wi,
      ((ground d p rel).objectsOfTypes ["waypoint"]).findIdx? (· == q) = some wi ∧
      occupied (compile (ground d p rel)) s wi = true ∧
      reach (compile (ground d p rel)) s crew wi = 0 := by
  obtain ⟨a1, a2, a3, ha, hwx, -, hwq⟩ := hf.inst.args_three hs
  rw [hargs] at ha
  obtain ⟨rfl, rfl, rfl⟩ : x = a1 ∧ st = a2 ∧ q = a3 := by simpa using ha
  obtain ⟨ri, hri⟩ := rover_index hp rel hwx
  obtain ⟨wi, hwi⟩ := waypoint_index hp rel hwq
  obtain ⟨hrilt, hrin⟩ := findIdx_sound hri
  obtain ⟨hwilt, -⟩ := findIdx_sound hwi
  obtain ⟨f, hflt, hfname⟩ := numbered_of_op d p rel ho
    (Or.inl (pre_mem_op hf hat (at_dynamic hp.domain)))
  have hftrue : s.test f = true := by
    rw [← habs.numbered f (by rw [hn]; exact hflt), hfname]
    exact pre_holds hf hat (at_dynamic hp.domain) happ
  have hfmem : (f, wi) ∈ (compile (ground d p rel)).roverAt.getD ri #[] :=
    mem_roverAt_of hrilt hwi hflt (by simpa [hrin] using hfname)
  have hroverSize : ri < (compile (ground d p rel)).roverAt.size := by
    rw [compile_roverAt, Array.size_map]
    exact hrilt
  have hoccupied : occupied (compile (ground d p rel)) s wi = true :=
    occupied_of hroverSize hfmem rfl hftrue
  have hwnd : ((ground d p rel).objectsOfTypes ["waypoint"]).toList.Nodup :=
    objsOf_nodup hp.namesNodup
  have hgraph : (roverGraph (ground d p rel)
      ((ground d p rel).objectsOfTypes ["waypoint"])
      (((ground d p rel).objectsOfTypes ["rover"]).getD ri default)).find? q = some wi :=
    roverGraph_find_of_findIdx hwnd hwi
  have hval := roverVal_at habs hn hwnd hone hrilt hrin hwi hflt hfname hftrue wi
  have hval0 : roverVal (compile (ground d p rel)) s ri wi = some 0 := by
    rw [(hsound ri hrilt).self wi (Graph.find?_lt' hgraph)] at hval
    exact hval
  have hequipStatic := static_of_pre hp rel hf hequip hstatic
  have hrcrew : ri ∈ crew := by
    rw [hcrew]
    exact mem_equipped_of hequipStatic hri
  exact ⟨wi, hwi, hoccupied, reach_eq_zero_of_mem hrcrew hval0⟩

open Planner.ExampleHeuristics.Rovers in
/-- A `navigate` frames every rover table except the mover's table. -/
theorem navigate_other_frames (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (hf : OpFacts d p o) {x y z : Pddl.Name}
    (hs : hf.inst.schema = navigateA) (hargs : hf.inst.args = [x, y, z])
    {s s' : State} {sigma : AtomState}
    (habs : Abstracts (ground d p rel) s sigma)
    (habs' : Abstracts (ground d p rel) s' (o.applyA sigma))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    {ri : Nat}
    (hrilt : ri < ((ground d p rel).objectsOfTypes ["rover"]).size)
    (hrin : ((ground d p rel).objectsOfTypes ["rover"]).getD ri default = x) :
    ∀ r, r ≠ ri → ∀ e ∈ (compile (ground d p rel)).roverAt.getD r #[],
      s'.test e.1 = s.test e.1 := by
  obtain ⟨-, hadd, hdel⟩ := navigate_atoms hf.inst hs hargs
  have hrnd : ((ground d p rel).objectsOfTypes ["rover"]).toList.Nodup :=
    objsOf_nodup hp.namesNodup
  intro r hne e he
  by_cases hr : r < ((ground d p rel).objectsOfTypes ["rover"]).size
  · obtain ⟨helt, -, hename⟩ := roverAt_getD_atom hr he
    have hrx : ((ground d p rel).objectsOfTypes ["rover"]).getD r default ≠ x := by
      intro heq
      have hri : r = ri := by
        refine (List.Nodup.getElem_inj_iff hrnd (hi := by simpa using hr)
          (hj := by simpa using hrilt)).mp ?_
        have h1 : ((ground d p rel).objectsOfTypes ["rover"])[r]'hr = x := by
          rw [← heq, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hr,
            Option.getD_some]
        have h2 : ((ground d p rel).objectsOfTypes ["rover"])[ri]'hrilt = x := by
          rw [← hrin, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hrilt,
            Option.getD_some]
        simpa using h1.trans h2.symm
      exact hne hri
    rw [← habs'.numbered e.1 (by rw [hn]; exact helt),
      ← habs.numbered e.1 (by rw [hn]; exact helt)]
    have hnot : ∀ w : Pddl.Name,
        (ground d p rel).factNames.getD e.1 default ∉ [at_ x w] := by
      intro w hmem
      have heq : (ground d p rel).factNames.getD e.1 default = at_ x w := by
        simpa only [List.mem_cons, List.not_mem_nil, or_false] using hmem
      have hargEq := congrArg GroundAtom.args (hename.symm.trans heq)
      apply hrx
      exact (by simpa only [at_, List.cons.injEq, true_and] using hargEq :
        ((ground d p rel).objectsOfTypes ["rover"]).getD r default = x ∧
          ((ground d p rel).objectsOfTypes ["waypoint"]).getD e.2 default = w ∧ True).1
    refine frame_of_lists hf hadd hdel ?_ ?_ sigma
    · exact hnot z
    · exact hnot y
  · rw [compile_roverAt, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none_iff.2 (by
        simpa [Array.size_map] using Nat.le_of_not_lt hr), Option.getD_none] at he
    simp at he

open Planner.ExampleHeuristics.Rovers in
/-- The typed and static preconditions of a `navigate` produce the indices and
graph edge required by `navigate_schemaStep`. -/
theorem navigate_ready (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (hf : OpFacts d p o) {x y z : Pddl.Name}
    (hs : hf.inst.schema = navigateA) (hargs : hf.inst.args = [x, y, z])
    {s s' : State} {sigma : AtomState}
    (habs : Abstracts (ground d p rel) s sigma)
    (habs' : Abstracts (ground d p rel) s' (o.applyA sigma))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size) :
    ∃ ri yi zi,
      ri < ((ground d p rel).objectsOfTypes ["rover"]).size ∧
      ((ground d p rel).objectsOfTypes ["rover"]).getD ri default = x ∧
      ((ground d p rel).objectsOfTypes ["waypoint"]).findIdx? (· == y) = some yi ∧
      ((ground d p rel).objectsOfTypes ["waypoint"]).findIdx? (· == z) = some zi ∧
      yi < (roverGraph (ground d p rel)
        ((ground d p rel).objectsOfTypes ["waypoint"]) x).size ∧
      zi ∈ (roverGraph (ground d p rel)
        ((ground d p rel).objectsOfTypes ["waypoint"]) x).adj.getD yi #[] ∧
      (∀ r, r ≠ ri → ∀ e ∈ (compile (ground d p rel)).roverAt.getD r #[],
        s'.test e.1 = s.test e.1) := by
  obtain ⟨a1, a2, a3, ha, hwx, hwy, hwz⟩ := hf.inst.args_three
    (show hf.inst.schema.params = [roverP "?x", waypointP "?y", waypointP "?z"] by
      rw [hs])
  rw [hargs] at ha
  obtain ⟨rfl, rfl, rfl⟩ : x = a1 ∧ y = a2 ∧ z = a3 := by simpa using ha
  obtain ⟨ri, hri⟩ := rover_index hp rel hwx
  obtain ⟨yi, hyi⟩ := waypoint_index hp rel hwy
  obtain ⟨zi, hzi⟩ := waypoint_index hp rel hwz
  obtain ⟨hrilt, hrin⟩ := findIdx_sound hri
  have hwnd : ((ground d p rel).objectsOfTypes ["waypoint"]).toList.Nodup :=
    objsOf_nodup hp.namesNodup
  have hgy : (roverGraph (ground d p rel)
      ((ground d p rel).objectsOfTypes ["waypoint"]) x).find? y = some yi :=
    roverGraph_find_of_findIdx hwnd hyi
  have hgz : (roverGraph (ground d p rel)
      ((ground d p rel).objectsOfTypes ["waypoint"]) x).find? z = some zi :=
    roverGraph_find_of_findIdx hwnd hzi
  have hctPre : ({ pred := "can_traverse", args := [x, y, z] } : GroundAtom)
      ∈ hf.inst.pre := by
    have hpre : hf.inst.pre =
        [{ pred := "can_traverse", args := [x, y, z] }, at_ x y,
          { pred := "visible", args := [y, z] }] := by
      rw [Pddl.Instance.pre_eq, hs, hargs]
      rfl
    rw [hpre]
    simp
  have hvisPre : ({ pred := "visible", args := [y, z] } : GroundAtom)
      ∈ hf.inst.pre := by
    have hpre : hf.inst.pre =
        [{ pred := "can_traverse", args := [x, y, z] }, at_ x y,
          { pred := "visible", args := [y, z] }] := by
      rw [Pddl.Instance.pre_eq, hs, hargs]
      rfl
    rw [hpre]
    simp
  have hctStatic := static_of_pre hp rel hf hctPre hp.canTraverseStatic
  have hvisStatic := static_of_pre hp rel hf hvisPre hp.visibleStatic
  have hctAtoms : ({ pred := "can_traverse", args := [x, y, z] } : GroundAtom)
      ∈ (ground d p rel).staticAtoms := (Array.mem_filter.mp hctStatic).1
  have hvis : ((ground d p rel).staticWith "visible").any
      (fun b => b.args == [y, z]) = true :=
    Array.any_eq_true'.mpr ⟨_, hvisStatic, by simp⟩
  have hedge := navigate_edge hctAtoms hvis hgy hgz
  exact ⟨ri, yi, zi, hrilt, hrin, hyi, hzi, Graph.find?_lt' hgy, hedge,
    navigate_other_frames hp rel hf hs hargs habs habs' hn hrilt hrin⟩

/-! ### The goal tables have no duplicate entries

Each table walks the goal atoms with their indices and stores `t.goal.getD i 0`
in every entry it keeps.  Numbering is injective on the goal, so two entries
carry the same fact only if they came from the same goal atom, and
`Pinned.goalNodup` says the goal names each atom once.
-/

open Planner.ExampleHeuristics.Rovers in
theorem soilGoals_nodup (hp : Pinned d p) (rel : Bool) :
    (compile (ground d p rel)).soilGoals.toList.Nodup := by
  refine goalTable_nodup_fact d p rel hp.goalNodup _ (·.goalFact) ?_
  intro x hx b hb
  split at hb
  · split at hb
    · obtain ⟨wi, -, hval⟩ := Option.map_eq_some_iff.mp hb
      rw [← hval]
      rfl
    · simp at hb

open Planner.ExampleHeuristics.Rovers in
theorem rockGoals_nodup (hp : Pinned d p) (rel : Bool) :
    (compile (ground d p rel)).rockGoals.toList.Nodup := by
  refine goalTable_nodup_fact d p rel hp.goalNodup _ (·.goalFact) ?_
  intro x hx b hb
  split at hb
  · split at hb
    · obtain ⟨wi, -, hval⟩ := Option.map_eq_some_iff.mp hb
      rw [← hval]
      rfl
    · simp at hb

open Planner.ExampleHeuristics.Rovers in
theorem imageGoals_nodup (hp : Pinned d p) (rel : Bool) :
    (compile (ground d p rel)).imageGoals.toList.Nodup := by
  refine goalTable_nodup_fact d p rel hp.goalNodup _ (·.goalFact) ?_
  intro x hx b hb
  split at hb
  · split at hb
    · simp only [Option.some.injEq] at hb
      rw [← hb]
      rfl
    · simp at hb


open Planner.ExampleHeuristics.Rovers in
/-- Every applicable grounded Rovers operator satisfies one of the nine
counter-step shapes. -/
theorem schemaStep_of_op (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (ho : o ∈ groundedOps d p rel) (hf : OpFacts d p o) (hadd : AddsFor d p o hf)
    {s s' : State} {sigma : AtomState}
    (habs : Abstracts (ground d p rel) s sigma)
    (habs' : Abstracts (ground d p rel) s' (o.applyA sigma))
    (happ : o.applicableA sigma) (hone : OneAt sigma) :
    SchemaStep (compile (ground d p rel)) s s' := by
  have hsound : ∀ ri, ri < ((ground d p rel).objectsOfTypes ["rover"]).size →
      Distances.Sound
        (roverGraph (ground d p rel)
          ((ground d p rel).objectsOfTypes ["waypoint"])
          (((ground d p rel).objectsOfTypes ["rover"]).getD ri default))
        ((compile (ground d p rel)).dist.getD ri default) :=
    fun ri hri => by
      rw [compile_dist_getD hri]
      exact Distances.sound_of _
  rcases instance_shape hp.domain hf.inst with
    ⟨x, y, z, hs, ha⟩ | ⟨x, st, q, hs, ha⟩ | ⟨x, st, q, hs, ha⟩ |
      ⟨x, st, hs, ha⟩ | ⟨r, c, tt, w, hs, ha⟩ |
      ⟨r, q, ob, c, m, hs, ha⟩ | ⟨r, l, q, x, y, hs, ha⟩ |
      ⟨r, l, q, x, y, hs, ha⟩ | ⟨r, l, ob, m, x, y, hs, ha⟩
  · obtain ⟨ri, yi, zi, hr, hrn, hyi, hzi, hylt, hedge, hother⟩ :=
      navigate_ready hp rel hf hs ha habs habs' rfl
    have hsnd := hsound ri hr
    rw [hrn] at hsnd
    exact navigate_schemaStep hp rel ho
      ⟨hf, fun y hy hnp => hadd (Or.inl hs) y hy hnp⟩ hs ha habs habs' rfl happ hone
      (oneAt_closed hp.domain hf happ hone)
      (objsOf_nodup hp.namesNodup) hr hrn hyi hzi hsnd hylt hedge hother
  · obtain ⟨hat, -, -, -, -⟩ := sampleSoil_atoms hf.inst hs ha
    have hequip : ({ pred := "equipped_for_soil_analysis", args := [x] } : GroundAtom)
        ∈ hf.inst.pre := by
      have hpre : hf.inst.pre = [at_ x q, atSoilSample q,
          { pred := "equipped_for_soil_analysis", args := [x] },
          { pred := "store_of", args := [st, x] }, emptyS st] := by
        rw [Pddl.Instance.pre_eq, hs, ha]
        rfl
      rw [hpre]
      simp
    obtain ⟨wi, hwi, hhere, hzero⟩ := sample_ready hp rel ho hf
      (by rw [hs]) ha hat hequip hp.soilEquippedStatic
      (show (compile (ground d p rel)).soilRovers =
        ((ground d p rel).staticWith "equipped_for_soil_analysis").filterMap fun a =>
          match a.args with
          | [r] => ((ground d p rel).objectsOfTypes ["rover"]).findIdx? (· == r)
          | _ => none from rfl)
      habs rfl hone happ hsound
    exact sampleSoil_schemaStep hp rel ho hf hs ha habs habs' rfl happ
      (soilGoals_nodup hp rel) hwi hhere hzero
  · obtain ⟨hat, -, -, -, -⟩ := sampleRock_atoms hf.inst hs ha
    have hequip : ({ pred := "equipped_for_rock_analysis", args := [x] } : GroundAtom)
        ∈ hf.inst.pre := by
      have hpre : hf.inst.pre = [at_ x q, atRockSample q,
          { pred := "equipped_for_rock_analysis", args := [x] },
          { pred := "store_of", args := [st, x] }, emptyS st] := by
        rw [Pddl.Instance.pre_eq, hs, ha]
        rfl
      rw [hpre]
      simp
    obtain ⟨wi, hwi, hhere, hzero⟩ := sample_ready hp rel ho hf
      (by rw [hs]) ha hat hequip hp.rockEquippedStatic
      (show (compile (ground d p rel)).rockRovers =
        ((ground d p rel).staticWith "equipped_for_rock_analysis").filterMap fun a =>
          match a.args with
          | [r] => ((ground d p rel).objectsOfTypes ["rover"]).findIdx? (· == r)
          | _ => none from rfl)
      habs rfl hone happ hsound
    exact sampleRock_schemaStep hp rel ho hf hs ha habs habs' rfl happ
      (rockGoals_nodup hp rel) hwi hhere hzero
  · exact drop_schemaStep hf hs ha habs habs' rfl
  · exact calibrate_schemaStep hf hs ha habs habs' rfl
  · exact takeImage_schemaStep hp rel ho hf hs ha habs habs' rfl happ
      (imageGoals_nodup hp rel)
  · exact commSoil_schemaStep hp rel ho
      ⟨hf, fun y hy hnp => hadd (Or.inr (Or.inl hs)) y hy hnp⟩ hs ha habs habs' rfl happ
  · exact commRock_schemaStep hp rel ho
      ⟨hf, fun y hy hnp => hadd (Or.inr (Or.inr (Or.inl hs))) y hy hnp⟩ hs ha habs habs'
      rfl happ
  · exact commImage_schemaStep hp rel ho
      ⟨hf, fun y hy hnp => hadd (Or.inr (Or.inr (Or.inr hs))) y hy hnp⟩ hs ha habs habs'
      rfl happ

/-- The single-position invariant holds at every reachable numbered state. -/
theorem reach_oneAt (hp : Pinned d p) (rel : Bool)
    (hwf : Task.WF (ground d p rel)) {s : State}
    (hreach : Reachable (ground d p rel) s) :
    ∃ sigma, Abstracts (ground d p rel) s sigma ∧ OneAt sigma := by
  exact reachable_abstracts_inv d p rel hwf (cost_pos hp rel) OneAt
    (initOneAt_of_check hp.initCheck)
    (fun o ho sigma hone happ => by
      obtain ⟨hf⟩ := opFacts_ground d p rel ho
      exact oneAt_closed hp.domain hf happ hone) hreach

open Planner.ExampleHeuristics.Rovers in
/-- Every numbered operator applicable at a reachable state has a Rovers
`SchemaStep`. -/
theorem schemaStep_of_reach (hp : Pinned d p) (rel : Bool)
    (hwf : Task.WF (ground d p rel)) {s : State}
    (hreach : Reachable (ground d p rel) s) {op : Op}
    (hop : op ∈ (ground d p rel).ops) (happ : op.applicable s = true) :
    SchemaStep (compile (ground d p rel)) s (op.apply s) := by
  obtain ⟨sigma, habs, hone⟩ := reach_oneAt hp rel hwf hreach
  have hops : (ground d p rel).ops = (groundedOps d p rel).map
      (numberOp (factIndex (allAtoms (groundedOps d p rel) p.goal.toArray)).1) := rfl
  rw [hops, Array.mem_map] at hop
  obtain ⟨o, ho, hnum⟩ := hop
  have happA : o.applicableA sigma :=
    (assemble_applicable (groundedOps d p rel) p.goal.toArray p.init.toArray
      (allObjects d p).toArray d.name ho habs).mp (by rw [hnum]; exact happ)
  have habs' : Abstracts (ground d p rel) (op.apply s) (o.applyA sigma) := by
    rw [← hnum]
    exact assemble_apply (groundedOps d p rel) p.goal.toArray p.init.toArray
      (allObjects d p).toArray d.name ho (cost_pos hp rel o ho)
      (hreach.wf hwf) habs
  obtain ⟨hf, hadd⟩ := addsKept hp rel o ho
  exact schemaStep_of_op hp rel ho hf hadd habs habs' happA hone

open Planner.ExampleHeuristics.Rovers in
/-- Rovers' shipped improved heuristic never overestimates on any reachable
state, with relevance pruning enabled or disabled. -/
theorem improved_admissible_of_pinned (hp : Pinned d p) (rel : Bool) :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel))
      (improved (ground d p rel)).eval := by
  have hwf : Task.WF (ground d p rel) := ground_wf d p rel (cost_pos hp rel)
  refine improved_admissibleOn_of_schema _ _ ?_ (soilGoals_mem_goal d p rel)
    (rockGoals_mem_goal d p rel) (imageGoals_mem_goal d p rel)
    (soilGoals_nodup hp rel) (rockGoals_nodup hp rel) (imageGoals_nodup hp rel) ?_
    (ops_cost hp rel)
  · exact fun s i s' _ hr hstep => Reachable.step hr i hstep
  · exact fun op hop s _ hr happ => schemaStep_of_reach hp rel hwf hr hop happ

open Planner.ExampleHeuristics.Rovers in
/-- Rovers' shipped improved heuristic is zero at every reachable goal. -/
theorem improved_goalAware_of_pinned (hp : Pinned d p) (rel : Bool) :
    (ground d p rel).GoalAwareOn (Reachable (ground d p rel))
      (improved (ground d p rel)).eval := by
  intro s hs hgoal
  exact improved_goalAware_of_schema _ (soilGoals_mem_goal d p rel)
    (rockGoals_mem_goal d p rel) (imageGoals_mem_goal d p rel) s hs.1 hgoal

open Planner.ExampleHeuristics.Rovers in
/-- And is consistent on reachable states. -/
theorem improved_consistent_of_pinned (hp : Pinned d p) (rel : Bool) :
    (ground d p rel).ConsistentOn (Reachable (ground d p rel))
      (improved (ground d p rel)).eval := by
  have hwf : Task.WF (ground d p rel) := ground_wf d p rel (cost_pos hp rel)
  exact improved_consistentOn_of_schema _ _ (soilGoals_nodup hp rel)
    (rockGoals_nodup hp rel) (imageGoals_nodup hp rel)
    (fun op hop s _ hr happ => schemaStep_of_reach hp rel hwf hr hop happ)
    (ops_cost hp rel)

/-! ### The executable certificate

The record above is what the proof needs.  The certificate is what the loader
can check.  Everything the record quantifies over an arbitrary name is decided
here over `p.init`, `p.goal`, or the problem's objects.
-/

theorem certificate_sound {d : Domain} {p : Problem}
    (hv : Validated d p)
    (h : ExampleHeuristics.Rovers.Certificate.certified d p = true) :
    Pinned d p := by
  simp only [ExampleHeuristics.Rovers.Certificate.certified,
    ExampleHeuristics.Rovers.Certificate.conditions, Certificate.passes,
    List.all_cons, List.all_nil, Bool.and_eq_true] at h
  rcases h with
    ⟨hactions, hrover, hwaypoint, hstore, hcamera, hmode, hlander, hobjective,
      hroverExact, hwaypointExact, hgoalNodup, hcanTraverse, hvisible, hsoil, hrock,
      hgoalDynamic, hinit, hnoSelf, hreverses, -⟩
  have hpairs : ∀ pred : Pddl.Name,
      Planner.Certificate.initPairs p pred = initPairs p pred := fun _ => rfl
  have htriples : ∀ pred : Pddl.Name,
      Planner.Certificate.initTriples p pred = initTriples p pred := fun _ => rfl
  refine
    { domain := by simpa using hactions
      roverType := by simpa using hrover
      waypointType := by simpa using hwaypoint
      storeType := by simpa using hstore
      cameraType := by simpa using hcamera
      modeType := by simpa using hmode
      landerType := by simpa using hlander
      objectiveType := by simpa using hobjective
      roverTypeExact := Certificate.exactType_sound hroverExact
      waypointTypeExact := Certificate.exactType_sound hwaypointExact
      validated := hv
      goalNodup := of_decide_eq_true hgoalNodup
      canTraverseStatic := by simpa using hcanTraverse
      visibleStatic := by simpa using hvisible
      soilEquippedStatic := by simpa using hsoil
      rockEquippedStatic := by simpa using hrock
      goalDynamic := ?_
      initCheck := ?_
      traverseReverses := ?_
      noSelfTraverse := ?_ }
  · rw [List.all_eq_true] at hgoalDynamic
    intro a ha
    simpa using hgoalDynamic a ha
  · rw [ExampleHeuristics.Rovers.Certificate.initInvCheck] at hinit
    simpa [hpairs, initInvCheck] using hinit
  · intro x y z hct hvis
    rw [ExampleHeuristics.Rovers.Certificate.traverseReverses] at hreverses
    simp only [htriples, hpairs, List.all_eq_true] at hreverses
    have hb := hreverses _ (mem_initTriples.mpr hct)
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true,
      List.contains_eq_mem, decide_eq_true_eq, decide_eq_false_iff_not] at hb
    rcases hb with hb | ⟨hb1, hb2⟩
    · exact absurd (mem_initPairs.mpr hvis) hb
    · exact ⟨mem_initTriples.mp hb1, mem_initPairs.mp hb2⟩
  · intro r w hmem
    rw [ExampleHeuristics.Rovers.Certificate.noSelfTraverse] at hnoSelf
    simp only [htriples, List.all_eq_true] at hnoSelf
    have hb := hnoSelf _ (mem_initTriples.mpr hmem)
    simp at hb

open Planner.ExampleHeuristics.Rovers in
theorem improved_goalAware_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool)
    (h : ExampleHeuristics.Rovers.Certificate.certified d p = true) :
    (ground d p rel).GoalAwareOn (Reachable (ground d p rel))
      (improved (ground d p rel)).eval :=
  improved_goalAware_of_pinned (certificate_sound hv h) rel

open Planner.ExampleHeuristics.Rovers in
theorem improved_consistent_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool)
    (h : ExampleHeuristics.Rovers.Certificate.certified d p = true) :
    (ground d p rel).ConsistentOn (Reachable (ground d p rel))
      (improved (ground d p rel)).eval :=
  improved_consistent_of_pinned (certificate_sound hv h) rel

open Planner.ExampleHeuristics.Rovers in
theorem improved_proof_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool) :
    ImprovedProof d p rel
      (Certificate.certified d p)
      (improved (ground d p rel)) :=
  { goalAware := improved_goalAware_of_certificate hv rel
    consistent := improved_consistent_of_certificate hv rel }

open Planner.ExampleHeuristics.Rovers in
theorem improved_admissible_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool)
    (h : ExampleHeuristics.Rovers.Certificate.certified d p = true) :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel))
      (improved (ground d p rel)).eval :=
  (improved_proof_of_certificate hv rel).admissible h

end Planner.Lifted.Rovers
