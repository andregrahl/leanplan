/-
Transport's improved heuristic, proved end to end in one file.

The order below is the order the argument is built in.  The schema-level proof
comes first: the improved value over the domain's own data, and what each schema
does to the counters.  The rest lifts that value to the parsed domain and
compiles it against the numbered task.

The runtime heuristic and its data stay under `Planner/`.  The simple heuristic
of this domain is proved in `Proofs/Domains/TransportSimple.lean`.
-/
import Planner.ExampleHeuristics.Transport.Certificate
import Proofs.Heuristic
import Planner.GeneratedDomains.Transport
import Proofs.Combinators
import Proofs.Certificates
import Proofs.Distance
import Proofs.SchemaSupport
import Proofs.LiftedHeuristic
import Proofs.FactTables
import Proofs.CompileSupport
import Proofs.Validation
import Planner.ExampleHeuristics.Transport.Improved

/- -------------------------------------------------------------------------- -/
/-
Transport, improved heuristic: goal awareness and the pieces the schema-level
proof builds on.

The consistency half lives in `Schema.lean`, which states what the domain's
schemas do to the predicates and derives the three counters from that.  What
stays here is goal awareness and the two set lemmas the derivation uses.
-/

namespace Planner.ExampleHeuristics.Transport

open Planner

/-! ### The three quantities -/

/-- Load and unload actions still owed. -/
abbrev Hc (d : Data) (s : State) : Nat := handling d s
/-- The driving bound. -/
abbrev Dc (d : Data) (s : State) : Nat := driving d s
/-- Locations a vehicle must still reach. -/
abbrev Rc (d : Data) (s : State) : Nat := (requiredLocs d s).length

/-! ### Assembly -/

theorem unmet_empty (d : Data) (s : State)
    (hall : ∀ pk ∈ d.packages, s.test pk.goalFact = true) : unmet d s = #[] := by
  unfold unmet
  rw [Array.filter_eq_empty_iff]
  intro x hx
  simp [hall x hx]

theorem value_eq_zero_of_goal (d : Data) (s : State)
    (hall : ∀ pk ∈ d.packages, s.test pk.goalFact = true) : value d s = 0 := by
  unfold value handling driving requiredLocs
  rw [unmet_empty d s hall]
  rfl

theorem improved_goalAware (t : Task)
    (hcompiled : ∀ pk ∈ (compile t).packages, pk.goalFact ∈ t.goal) :
    t.GoalAware (improved t).eval := by
  refine t.goalAware_of _ fun s _ hgoal => ?_
  exact value_eq_zero_of_goal _ s fun pk hpk => hgoal _ (hcompiled pk hpk)

/-! ### Discharging the locations a vehicle must still reach

`pick-up` and `drop` happen where a vehicle already stands, and such locations are never counted, so the set never shrinks; a `drive` frees one location and occupies another, so it gains at most one.  Both follow from how the length of a deduplicated list moves, so the
obligation reduces to a membership statement about the underlying collection.
-/

theorem set_mono (d : Data) (s s' : State) {l l' : List Nat}
    (hl : requiredLocs d s = distinct l) (hl' : requiredLocs d s' = distinct l')
    (h : ∀ x ∈ l, x ∈ l') : Rc d s ≤ Rc d s' := by
  show (requiredLocs d s).length ≤ (requiredLocs d s').length
  rw [hl, hl']
  exact length_distinct_mono l l' h

theorem set_le_succ (d : Data) (s s' : State) {l l' : List Nat} (a : Nat)
    (hl : requiredLocs d s = distinct l) (hl' : requiredLocs d s' = distinct l')
    (h : ∀ x ∈ l, x ∈ l' ∨ x = a) : Rc d s ≤ Rc d s' + 1 := by
  show (requiredLocs d s).length ≤ (requiredLocs d s').length + 1
  rw [hl, hl']
  exact length_distinct_le_succ l l' a h

end Planner.ExampleHeuristics.Transport

/- -------------------------------------------------------------------------- -/
/-
Transport, stated at the schema level.

`Effect` in `Improved.lean` assumes how one action moves the heuristic's three
counters.  This file assumes only what the domain's schemas do to the predicates —
where each vehicle stands, where a package sits, which vehicle carries it — and
derives the counters.

Trying to prove `Effect` rather than assume it exposed a defect in it.  Its
`pickup` and `drop` constructors both assert that the handling count *falls* by
one.  Neither is true in general: dropping a package short of its destination
takes it from carried (worth one) to on the ground (worth two), and picking up a
package that already sits at its destination puts it back into the unmet set.
Both raise the count.  No constructor of `Effect` covers either, so that
assumption is not satisfiable for a real transport task.  The value is still
consistent — a rise in `H` is harmless — and the shape below carries the weaker,
true bound `H ≤ H' + 1`, which covers all four cases at once.
-/

namespace Planner.ExampleHeuristics.Transport

open Planner

/-! ### The counters, over the whole package list -/

/-- Still to deliver. -/
def live (s : State) (pk : PackageInfo) : Bool := !s.test pk.goalFact

theorem handling_eq (d : Data) (s : State) :
    Hc d s = (d.packages.toList.map fun pk =>
      if live s pk then handlingCost s pk else 0).sum := by
  show handling d s = _
  unfold handling unmet live
  rw [← Array.foldl_toList, foldl_add_eq_sum, Array.toList_filter, ← sum_filter_eq_ite]
  simp

theorem driving_eq (d : Data) (s : State) :
    Dc d s = d.packages.toList.foldl (fun acc pk =>
      max acc (if live s pk then drivingOf d s (vehicleLocations d s) pk else 0)) 0 := by
  show driving d s = _
  unfold driving unmet live
  rw [← Array.foldl_toList, Array.toList_filter, foldl_max_filter]

theorem required_eq (d : Data) (s : State) :
    requiredLocs d s = distinct (((d.packages.toList.filter
      (fun pk => !s.test pk.goalFact)).flatMap fun pk =>
      pk.goalLoc :: (match groundLoc s pk with | some l => [l] | none => [])).filter
      fun l => !(vehicleLocations d s).contains l) := by
  unfold requiredLocs unmet
  rw [Array.toList_filter]
  rfl

/-! ### What each schema does -/

/--
`pick-up` and `drop`.  A vehicle stands at `l`; the package `q` is at `l` or in
that vehicle, before and after.  One structure covers all four cases — picking up
a package that was still to deliver or one already delivered, dropping at the
destination or short of it — because the bounds they need are the same.
-/
structure LoadStep (g : Graph) (d : Data) (s s' : State) (v l : Nat) (q : PackageInfo) :
    Prop where
  memQ : q ∈ d.packages
  lLt : l < g.size
  vehMem : l ∈ vehicleLocations d s
  vehOcc : (vehicleLocations d s).contains l = true
  vehLoc : (vehicleLocations d s).getD v d.dist.bound = l
  atQ : groundLoc s q = some l ∨ (groundLoc s q = none ∧ carrier s q = some v)
  atQ' : groundLoc s' q = some l ∨ (groundLoc s' q = none ∧ carrier s' q = some v)
  /-- The only way `q` becomes delivered here is a drop at its own destination. -/
  served' : s'.test q.goalFact = true →
    q.goalLoc = l ∧ groundLoc s q = none ∧ carrier s q = some v
  frameVeh : vehicleLocations d s' = vehicleLocations d s
  frameGround : ∀ pk ∈ d.packages, pk ≠ q → groundLoc s' pk = groundLoc s pk
  frameCarrier : ∀ pk ∈ d.packages, pk ≠ q → carrier s' pk = carrier s pk
  frameServed : ∀ pk ∈ d.packages, pk ≠ q → s'.test pk.goalFact = s.test pk.goalFact

/-- `drive`: one vehicle leaves `l1` for the adjacent `l2`; no package moves. -/
structure DriveStep (g : Graph) (d : Data) (s s' : State) (l1 l2 : Nat) : Prop where
  l1Lt : l1 < g.size
  adj : l2 ∈ g.adj.getD l1 #[]
  /-- Each vehicle either stays put or is the one that drove. -/
  vehEntry : ∀ i, (vehicleLocations d s').getD i d.dist.bound
      = (vehicleLocations d s).getD i d.dist.bound
    ∨ ((vehicleLocations d s).getD i d.dist.bound = l1
       ∧ (vehicleLocations d s').getD i d.dist.bound = l2)
  /-- Every place a vehicle stands afterwards is one it stood on before, or `l2`. -/
  occNew : ∀ x, (vehicleLocations d s').contains x = true →
    (vehicleLocations d s).contains x = true ∨ x = l2
  /-- The only new vehicle position is `l2`, reached from `l1`. -/
  vehNew : ∀ w ∈ vehicleLocations d s', w ∈ vehicleLocations d s ∨ w = l2
  l1Mem : l1 ∈ vehicleLocations d s
  frameGround : ∀ pk ∈ d.packages, groundLoc s' pk = groundLoc s pk
  frameCarrier : ∀ pk ∈ d.packages, carrier s' pk = carrier s pk
  frameServed : ∀ pk ∈ d.packages, s'.test pk.goalFact = s.test pk.goalFact

/-- One action of the domain. -/
inductive SchemaStep (g : Graph) (d : Data) (s s' : State) : Prop
  | load (v l : Nat) (q : PackageInfo) (h : LoadStep g d s s' v l q)
  | drive (l1 l2 : Nat) (h : DriveStep g d s s' l1 l2)

/-! ### The counters, derived from the shapes -/

namespace LoadStep

variable {g : Graph} {d : Data} {s s' : State} {v l : Nat} {q : PackageInfo}

theorem minFrom_zero (h : LoadStep g d s s' v l q) (hsound : Distances.Sound g d.dist) :
    d.dist.minFrom (vehicleLocations d s) l = 0 := by
  have := minFrom_le_of_mem d.dist h.vehMem l
  rw [hsound.self l h.lLt] at this
  omega

theorem drivingOf_q (h : LoadStep g d s s' v l q) (hsound : Distances.Sound g d.dist) :
    drivingOf d s (vehicleLocations d s) q = d.dist.get l q.goalLoc := by
  rcases h.atQ with hg | ⟨hg, hc⟩
  · simp [drivingOf, hg, h.minFrom_zero hsound]
  · simp [drivingOf, hg, hc, h.vehLoc]

theorem drivingOf_q' (h : LoadStep g d s s' v l q) (hsound : Distances.Sound g d.dist) :
    drivingOf d s' (vehicleLocations d s') q = d.dist.get l q.goalLoc := by
  rw [h.frameVeh]
  rcases h.atQ' with hg | ⟨hg, hc⟩
  · simp [drivingOf, hg, h.minFrom_zero hsound]
  · simp [drivingOf, hg, hc, h.vehLoc]

theorem handlingCost_q_le (h : LoadStep g d s s' v l q) : handlingCost s q ≤ 2 := by
  rcases h.atQ with hg | ⟨hg, hc⟩
  · simp [handlingCost, hg]
  · simp [handlingCost, hg, hc]

theorem handlingCost_q'_ge (h : LoadStep g d s s' v l q) : 1 ≤ handlingCost s' q := by
  rcases h.atQ' with hg | ⟨hg, hc⟩
  · simp [handlingCost, hg]
  · simp [handlingCost, hg, hc]

theorem handlingCost_q_of_served (h : LoadStep g d s s' v l q)
    (hs : s'.test q.goalFact = true) : handlingCost s q = 1 := by
  obtain ⟨-, hg, hc⟩ := h.served' hs
  simp [handlingCost, hg, hc]

theorem frame_handling (h : LoadStep g d s s' v l q) {pk : PackageInfo}
    (hpk : pk ∈ d.packages) (hne : pk ≠ q) : handlingCost s' pk = handlingCost s pk := by
  simp [handlingCost, h.frameGround pk hpk hne, h.frameCarrier pk hpk hne]

theorem frame_driving (h : LoadStep g d s s' v l q) {pk : PackageInfo}
    (hpk : pk ∈ d.packages) (hne : pk ≠ q) :
    drivingOf d s' (vehicleLocations d s') pk = drivingOf d s (vehicleLocations d s) pk := by
  simp [drivingOf, h.frameVeh, h.frameGround pk hpk hne, h.frameCarrier pk hpk hne]

theorem Hc_le (h : LoadStep g d s s' v l q) (hnd : d.packages.toList.Nodup) :
    Hc d s ≤ Hc d s' + 1 := by
  rw [handling_eq, handling_eq]
  refine sum_map_le_succ _ _ _ q hnd ?_ ?_
  · by_cases h1 : live s q
    · by_cases h2 : live s' q
      · have := h.handlingCost_q_le
        have := h.handlingCost_q'_ge
        simp only [h1, h2, if_true]
        omega
      · have hs : s'.test q.goalFact = true := by
          simpa [live] using h2
        simp only [h1, h2, if_true, if_false, h.handlingCost_q_of_served hs]
        omega
    · simp [h1]
  · intro y hy hne
    have hm : y ∈ d.packages := by simpa using hy
    simp [live, h.frameServed y hm hne, h.frame_handling hm hne]

theorem Dc_le (h : LoadStep g d s s' v l q) (hsound : Distances.Sound g d.dist) :
    Dc d s ≤ Dc d s' := by
  rw [driving_eq, driving_eq]
  refine foldl_max_mono _ _ _ ?_ 0 0 (Nat.le_refl _)
  intro y hy
  have hm : y ∈ d.packages := by simpa using hy
  by_cases hne : y = q
  · subst hne
    by_cases h1 : live s y
    · by_cases h2 : live s' y
      · simp only [h1, h2, if_true, h.drivingOf_q hsound, h.drivingOf_q' hsound,
          Nat.le_refl]
      · have hs : s'.test y.goalFact = true := by simpa [live] using h2
        obtain ⟨hgoal, -, -⟩ := h.served' hs
        simp only [h1, h2, if_true, if_false, h.drivingOf_q hsound, hgoal,
          hsound.self l h.lLt]
        omega
    · simp [h1]
  · simp [live, h.frameServed y hm hne, h.frame_driving hm hne]

theorem Rc_le (h : LoadStep g d s s' v l q) (hsound : Distances.Sound g d.dist) :
    Rc d s ≤ Rc d s' := by
  refine set_mono d s s' (required_eq d s) (required_eq d s') ?_
  intro x hx
  rw [List.mem_filter] at hx ⊢
  obtain ⟨hxm, hxocc⟩ := hx
  rw [List.mem_flatMap] at hxm ⊢
  obtain ⟨pk, hpk, hxp⟩ := hxm
  rw [List.mem_filter] at hpk
  have hm : pk ∈ d.packages := by simpa using hpk.1
  have hnotOcc : (vehicleLocations d s).contains x = false := by simpa using hxocc
  refine ⟨?_, ?_⟩
  · by_cases hne : pk = q
    · subst hne
      have hxgoal : x = pk.goalLoc := by
        rcases List.mem_cons.mp hxp with h1 | h1
        · exact h1
        · exfalso
          rcases h.atQ with hga | ⟨hga, -⟩
          · rw [hga] at h1
            simp only [List.mem_singleton] at h1
            subst h1
            rw [h.vehOcc] at hnotOcc
            exact Bool.noConfusion hnotOcc
          · rw [hga] at h1; simp at h1
      refine ⟨pk, ?_, ?_⟩
      · rw [List.mem_filter]
        refine ⟨hpk.1, ?_⟩
        by_contra hcon
        have hs : s'.test pk.goalFact = true := by simpa [live] using hcon
        obtain ⟨hgoal, -, -⟩ := h.served' hs
        rw [hxgoal, hgoal, h.vehOcc] at hnotOcc
        exact Bool.noConfusion hnotOcc
      · rw [hxgoal]; simp
    · refine ⟨pk, ?_, ?_⟩
      · rw [List.mem_filter]
        exact ⟨hpk.1, by simpa [live, h.frameServed pk hm hne] using hpk.2⟩
      · rwa [h.frameGround pk hm hne]
  · simpa [h.frameVeh] using hxocc

end LoadStep

namespace DriveStep

variable {g : Graph} {d : Data} {s s' : State} {l1 l2 : Nat}

theorem vehStep (h : DriveStep g d s s' l1 l2) (hsound : Distances.Sound g d.dist)
    {x : Nat} (hx : x < g.size) :
    ∀ w ∈ vehicleLocations d s', ∃ u ∈ vehicleLocations d s,
      d.dist.get u x ≤ 1 + d.dist.get w x := by
  intro w hw
  rcases h.vehNew w hw with hmem | rfl
  · exact ⟨w, hmem, by omega⟩
  · exact ⟨l1, h.l1Mem, hsound.step l1 w x h.l1Lt hx h.adj⟩

theorem Hc_eq (h : DriveStep g d s s' l1 l2) : Hc d s' = Hc d s := by
  rw [handling_eq, handling_eq]
  congr 1
  refine List.map_congr_left ?_
  intro y hy
  have hm : y ∈ d.packages := by simpa using hy
  simp [live, handlingCost, h.frameServed y hm, h.frameGround y hm, h.frameCarrier y hm]

theorem drivingOf_le_succ (h : DriveStep g d s s' l1 l2) (hsound : Distances.Sound g d.dist)
    {pk : PackageInfo} (hpk : pk ∈ d.packages) (hgoalLt : pk.goalLoc < g.size)
    (hgroundLt : ∀ lp, groundLoc s pk = some lp → lp < g.size) :
    drivingOf d s (vehicleLocations d s) pk
      ≤ 1 + drivingOf d s' (vehicleLocations d s') pk := by
  rcases hg : groundLoc s pk with _ | lp
  · rcases hc : carrier s pk with _ | v'
    · simp [drivingOf, hg, hc, h.frameGround pk hpk, h.frameCarrier pk hpk]
    · simp only [drivingOf, hg, hc, h.frameGround pk hpk, h.frameCarrier pk hpk]
      rcases h.vehEntry v' with heq | ⟨he1, he2⟩
      · rw [heq]; omega
      · rw [he1, he2]
        exact hsound.step l1 l2 pk.goalLoc h.l1Lt hgoalLt h.adj
  · have hkey := minFrom_le_succ d.dist (vehicleLocations d s) (vehicleLocations d s') lp
      (h.vehStep hsound (hgroundLt lp hg))
    simp only [drivingOf, hg, h.frameGround pk hpk]
    omega

theorem Dc_le_succ (h : DriveStep g d s s' l1 l2) (hsound : Distances.Sound g d.dist)
    (hnodes : ∀ pk ∈ d.packages, pk.goalLoc < g.size ∧
      ∀ lp, groundLoc s pk = some lp → lp < g.size) :
    Dc d s ≤ Dc d s' + 1 := by
  rw [driving_eq, driving_eq]
  have hterm : ∀ y ∈ d.packages.toList,
      (if live s y then drivingOf d s (vehicleLocations d s) y else 0)
        ≤ 1 + (if live s' y then drivingOf d s' (vehicleLocations d s') y else 0) := by
    intro y hy
    have hm : y ∈ d.packages := by simpa using hy
    obtain ⟨hg1, hg2⟩ := hnodes y hm
    by_cases h1 : live s y
    · have h2 : live s' y = true := by simpa [live, h.frameServed y hm] using h1
      simp only [h1, h2, if_true]
      exact h.drivingOf_le_succ hsound hm hg1 hg2
    · have h2 : ¬ live s' y = true := by simpa [live, h.frameServed y hm] using h1
      simp [h1, h2]
  have key := foldl_max_le_succ d.packages.toList _ _ hterm 0 0 (by omega)
  omega

theorem Rc_le_succ (h : DriveStep g d s s' l1 l2) : Rc d s ≤ Rc d s' + 1 := by
  refine set_le_succ d s s' l2 (required_eq d s) (required_eq d s') ?_
  intro x hx
  rw [List.mem_filter] at hx
  obtain ⟨hxm, hxocc⟩ := hx
  rw [List.mem_flatMap] at hxm
  obtain ⟨pk, hpk, hxp⟩ := hxm
  rw [List.mem_filter] at hpk
  have hm : pk ∈ d.packages := by simpa using hpk.1
  have hnotOcc : (vehicleLocations d s).contains x = false := by simpa using hxocc
  by_cases hxl2 : x = l2
  · exact Or.inr hxl2
  · refine Or.inl ?_
    rw [List.mem_filter, List.mem_flatMap]
    refine ⟨⟨pk, ?_, ?_⟩, ?_⟩
    · rw [List.mem_filter]
      exact ⟨hpk.1, by simpa [live, h.frameServed pk hm] using hpk.2⟩
    · rwa [h.frameGround pk hm]
    · simp only [Bool.not_eq_true']
      by_contra hcon
      have hcon' : (vehicleLocations d s').contains x = true := by
        simpa using hcon
      rcases h.occNew x hcon' with hc | hc
      · rw [hc] at hnotOcc; exact Bool.noConfusion hnotOcc
      · exact hxl2 hc

end DriveStep

/-! ### The consistency step, with nothing about the counters assumed -/

theorem value_step_of_schema (g : Graph) (d : Data) (s s' : State)
    (hnd : d.packages.toList.Nodup) (hsound : Distances.Sound g d.dist)
    (hnodes : ∀ pk ∈ d.packages, pk.goalLoc < g.size ∧
      ∀ lp, groundLoc s pk = some lp → lp < g.size)
    (he : SchemaStep g d s s') (cost : Nat) (hcost : 1 ≤ cost) :
    value d s ≤ cost + value d s' := by
  show Hc d s + max (Dc d s) (Rc d s) ≤ cost + (Hc d s' + max (Dc d s') (Rc d s'))
  cases he with
  | load v l q h =>
      have h1 := h.Hc_le hnd
      have h2 := h.Dc_le hsound
      have h3 := h.Rc_le hsound
      omega
  | drive l1 l2 h =>
      have h1 := h.Hc_eq
      have h2 := h.Dc_le_succ hsound hnodes
      have h3 := h.Rc_le_succ
      omega

/-- Zero at every goal state, assuming only what the schemas do. -/
theorem improved_goalAware_of_schema (t : Task)
    (hcompiled : ∀ pk ∈ (compile t).packages, pk.goalFact ∈ t.goal) :
    t.GoalAware (improved t).eval := improved_goalAware t hcompiled

/-- And never falls by more than one action costs. -/
theorem improved_consistent_of_schema (t : Task) (g : Graph)
    (hnd : (compile t).packages.toList.Nodup)
    (hsound : Distances.Sound g (compile t).dist)
    (hnodes : ∀ s, ∀ pk ∈ (compile t).packages, pk.goalLoc < g.size ∧
      ∀ lp, groundLoc s pk = some lp → lp < g.size)
    (hstep : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      SchemaStep g (compile t) s (op.apply s))
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost) :
    t.Consistent (improved t).eval :=
  t.consistent_of_ops _ fun op hop s hs happ =>
    value_step_of_schema g _ s _ hnd hsound (hnodes s) (hstep op hop s hs happ)
      op.cost (hcost op hop)

/-- Never overestimates, assuming only that every operator is one of the schemas. -/
theorem improved_admissible_of_schema (t : Task) (g : Graph)
    (hcompiled : ∀ pk ∈ (compile t).packages, pk.goalFact ∈ t.goal)
    (hnd : (compile t).packages.toList.Nodup)
    (hsound : Distances.Sound g (compile t).dist)
    (hnodes : ∀ s, ∀ pk ∈ (compile t).packages, pk.goalLoc < g.size ∧
      ∀ lp, groundLoc s pk = some lp → lp < g.size)
    (hstep : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      SchemaStep g (compile t) s (op.apply s))
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost) :
    t.Admissible (improved t).eval :=
  t.admissible _ (improved_goalAware_of_schema t hcompiled)
    (improved_consistent_of_schema t g hnd hsound hnodes hstep hcost)

end Planner.ExampleHeuristics.Transport

/- -------------------------------------------------------------------------- -/
/-
Which domain a Transport task came from.

The equation on `actions` fixes the three schemas exactly as the parser produces
them.  The remaining lemmas expose their instantiated atoms, which lets the
heuristic proof reason about one lifted transition without mentioning grounding
or fact numbers.
-/

namespace Planner.Lifted.Transport

open Planner Planner.Pddl

/-! ### The domain's atoms -/

def atAtom (x l : Name) : GroundAtom := { pred := "at", args := [x, l] }
def inAtom (q v : Name) : GroundAtom := { pred := "in", args := [q, v] }
def road (l₁ l₂ : Name) : GroundAtom := { pred := "road", args := [l₁, l₂] }
def capacity (v s : Name) : GroundAtom := { pred := "capacity", args := [v, s] }
def capPred (s₁ s₂ : Name) : GroundAtom :=
  { pred := "capacity-predecessor", args := [s₁, s₂] }

/-! ### The schemas, as the parser produces them -/

abbrev locP (n : Name) : TypedName := { name := n, type := "location" }
abbrev sizeP (n : Name) : TypedName := { name := n, type := "size" }
abbrev vehP : TypedName := { name := "?v", type := "vehicle" }
abbrev pkgP : TypedName := { name := "?p", type := "package" }

abbrev atV (x l : Name) : Atom := { pred := "at", args := [.var x, .var l] }
abbrev inV (q v : Name) : Atom := { pred := "in", args := [.var q, .var v] }
abbrev roadV (l₁ l₂ : Name) : Atom := { pred := "road", args := [.var l₁, .var l₂] }
abbrev capacityV (v s : Name) : Atom := { pred := "capacity", args := [.var v, .var s] }
abbrev capPredV (s₁ s₂ : Name) : Atom :=
  { pred := "capacity-predecessor", args := [.var s₁, .var s₂] }

abbrev driveA : Action := Planner.GeneratedDomains.Transport.action0
abbrev pickupA : Action := Planner.GeneratedDomains.Transport.action1
abbrev dropA : Action := Planner.GeneratedDomains.Transport.action2

/-- The parsed domain is Transport. -/
abbrev TransportDomain (d : Domain) : Prop :=
  d.actions = Planner.GeneratedDomains.Transport.actions

theorem at_dynamic {d : Domain} (hd : TransportDomain d) :
    (staticPredicates d).contains "at" = false :=
  not_static_of_mem_del (a := driveA) (by rw [hd]; simp) (y := atV "?v" "?l1")
    (by simp [driveA])

theorem in_dynamic {d : Domain} (hd : TransportDomain d) :
    (staticPredicates d).contains "in" = false :=
  not_static_of_mem_add (a := pickupA) (by rw [hd]; simp) (y := inV "?p" "?v")
    (by simp [pickupA])

theorem capacity_dynamic {d : Domain} (hd : TransportDomain d) :
    (staticPredicates d).contains "capacity" = false :=
  not_static_of_mem_add (a := pickupA) (by rw [hd]; simp) (y := capacityV "?v" "?s1")
    (by simp [pickupA])

/-! ### Instances -/

theorem instance_shape {d : Domain} {objects : List TypedName} (hd : TransportDomain d)
    (i : Instance d objects) :
    (∃ v l₁ l₂, i.schema = driveA ∧ i.args = [v, l₁, l₂]) ∨
    (∃ v l q s₁ s₂, i.schema = pickupA ∧ i.args = [v, l, q, s₁, s₂]) ∨
    (∃ v l q s₁ s₂, i.schema = dropA ∧ i.args = [v, l, q, s₁, s₂]) := by
  have hmem : i.schema ∈ [driveA, pickupA, dropA] := by
    have hm : i.schema ∈ d.actions := i.mem
    rw [hd] at hm
    exact hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with hs | hs | hs
  · obtain ⟨v, l₁, l₂, ha, -, -, -⟩ := i.args_three (by rw [hs])
    exact Or.inl ⟨v, l₁, l₂, hs, ha⟩
  · obtain ⟨v, l, q, s₁, s₂, ha, -, -, -, -, -⟩ := i.args_five (by rw [hs])
    exact Or.inr (Or.inl ⟨v, l, q, s₁, s₂, hs, ha⟩)
  · obtain ⟨v, l, q, s₁, s₂, ha, -, -, -, -, -⟩ := i.args_five (by rw [hs])
    exact Or.inr (Or.inr ⟨v, l, q, s₁, s₂, hs, ha⟩)

theorem drive_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {v l₁ l₂ : Name} (hs : i.schema = driveA) (ha : i.args = [v, l₁, l₂]) :
    atAtom v l₁ ∈ i.pre ∧ road l₁ l₂ ∈ i.pre ∧
    i.add = [atAtom v l₂] ∧ i.del = [atAtom v l₁] := by
  have hp : i.pre = [atAtom v l₁, road l₁ l₂] := by rw [i.pre_eq, hs, ha]; rfl
  have hadd : i.add = [atAtom v l₂] := by rw [i.add_eq, hs, ha]; rfl
  have hdel : i.del = [atAtom v l₁] := by rw [i.del_eq, hs, ha]; rfl
  simp [hp, hadd, hdel]

theorem pickup_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {v l q s₁ s₂ : Name} (hs : i.schema = pickupA) (ha : i.args = [v, l, q, s₁, s₂]) :
    atAtom v l ∈ i.pre ∧ atAtom q l ∈ i.pre ∧
    i.add = [inAtom q v, capacity v s₁] ∧ i.del = [atAtom q l, capacity v s₂] := by
  have hp : i.pre = [atAtom v l, atAtom q l, capPred s₁ s₂, capacity v s₂] := by
    rw [i.pre_eq, hs, ha]; rfl
  have hadd : i.add = [inAtom q v, capacity v s₁] := by rw [i.add_eq, hs, ha]; rfl
  have hdel : i.del = [atAtom q l, capacity v s₂] := by rw [i.del_eq, hs, ha]; rfl
  simp [hp, hadd, hdel]

theorem drop_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {v l q s₁ s₂ : Name} (hs : i.schema = dropA) (ha : i.args = [v, l, q, s₁, s₂]) :
    atAtom v l ∈ i.pre ∧ inAtom q v ∈ i.pre ∧
    i.add = [atAtom q l, capacity v s₂] ∧ i.del = [inAtom q v, capacity v s₁] := by
  have hp : i.pre = [atAtom v l, inAtom q v, capPred s₁ s₂, capacity v s₁] := by
    rw [i.pre_eq, hs, ha]; rfl
  have hadd : i.add = [atAtom q l, capacity v s₂] := by rw [i.add_eq, hs, ha]; rfl
  have hdel : i.del = [inAtom q v, capacity v s₁] := by rw [i.del_eq, hs, ha]; rfl
  simp [hp, hadd, hdel]

end Planner.Lifted.Transport

/- -------------------------------------------------------------------------- -/
/-
Transport's improved heuristic over ground atoms.

The data has the same shape as the compiled heuristic, but its tables contain
atoms instead of fact numbers.  This keeps the value close to the executable one
while making the consistency argument independent of grounding.
-/

namespace Planner.Lifted.Transport

open Planner Planner.Pddl

/-- What the heuristic needs to know about one package with an unmet goal. -/
structure PackageInfo where
  /-- The atom `at(package, destination)`. -/
  goalAtom : GroundAtom
  /-- The destination, as a node of the road graph. -/
  goalLoc : Nat
  /-- The atoms `at(package, l)`, with `l`. -/
  atAtoms : Array (GroundAtom × Nat)
  /-- The atoms `in(package, v)`, with the vehicle's index. -/
  inAtoms : Array (GroundAtom × Nat)
  deriving Inhabited, DecidableEq

structure Cfg where
  dist : Distances
  /-- For each vehicle, the atoms `at(vehicle, l)` with `l`. -/
  vehAt : Array (Array (GroundAtom × Nat))
  packages : Array PackageInfo
  deriving Inhabited

@[inline] def vehicleLocations (c : Cfg) (σ : AtomState) : Array Nat :=
  c.vehAt.map fun atoms =>
    match atoms.find? fun x => σ x.1 with
    | some (_, l) => l
    | none => c.dist.bound

@[inline] def unmet (c : Cfg) (σ : AtomState) : Array PackageInfo :=
  c.packages.filter fun pk => !σ pk.goalAtom

@[inline] def groundLoc (σ : AtomState) (pk : PackageInfo) : Option Nat :=
  (pk.atAtoms.find? fun x => σ x.1).map (·.2)

@[inline] def carrier (σ : AtomState) (pk : PackageInfo) : Option Nat :=
  (pk.inAtoms.find? fun x => σ x.1).map (·.2)

@[inline] def handlingCost (σ : AtomState) (pk : PackageInfo) : Nat :=
  match groundLoc σ pk with
  | some _ => 2
  | none => match carrier σ pk with
            | some _ => 1
            | none => 0

@[inline] def handling (c : Cfg) (σ : AtomState) : Nat :=
  (unmet c σ).foldl (init := 0) fun acc pk => acc + handlingCost σ pk

@[inline] def drivingOf (c : Cfg) (σ : AtomState) (veh : Array Nat)
    (pk : PackageInfo) : Nat :=
  match groundLoc σ pk with
  | some l => c.dist.minFrom veh l + c.dist.get l pk.goalLoc
  | none => match carrier σ pk with
            | some v => c.dist.get (veh.getD v c.dist.bound) pk.goalLoc
            | none => 0

@[inline] def driving (c : Cfg) (σ : AtomState) : Nat :=
  (unmet c σ).foldl (init := 0) fun acc pk =>
    max acc (drivingOf c σ (vehicleLocations c σ) pk)

@[inline] def requiredLocs (c : Cfg) (σ : AtomState) : List Nat :=
  distinct (((unmet c σ).toList.flatMap fun pk =>
      pk.goalLoc :: (match groundLoc σ pk with
                     | some l => [l]
                     | none => [])).filter
      fun l => !(vehicleLocations c σ).contains l)

def value (c : Cfg) (σ : AtomState) : Nat :=
  handling c σ + max (driving c σ) (requiredLocs c σ).length

/-! ### The three quantities -/

/-- Load and unload actions still owed. -/
abbrev Hc (c : Cfg) (σ : AtomState) : Nat := handling c σ
/-- The driving bound. -/
abbrev Dc (c : Cfg) (σ : AtomState) : Nat := driving c σ
/-- Locations a vehicle must still reach. -/
abbrev Rc (c : Cfg) (σ : AtomState) : Nat := (requiredLocs c σ).length

/-! ### Goal awareness -/

theorem unmet_empty (c : Cfg) (σ : AtomState)
    (hall : ∀ pk ∈ c.packages, σ pk.goalAtom = true) : unmet c σ = #[] := by
  unfold unmet
  rw [Array.filter_eq_empty_iff]
  intro x hx
  simp [hall x hx]

theorem value_eq_zero (c : Cfg) (σ : AtomState)
    (hall : ∀ pk ∈ c.packages, σ pk.goalAtom = true) : value c σ = 0 := by
  unfold value handling driving requiredLocs
  rw [unmet_empty c σ hall]
  rfl

theorem liftedGoalAware (p : Problem) (c : Cfg)
    (hsub : ∀ pk ∈ c.packages, pk.goalAtom ∈ p.goal) : LiftedGoalAware p (value c) := by
  intro σ hgoal
  exact value_eq_zero c σ fun pk hpk => hgoal pk.goalAtom (by simpa using hsub pk hpk)

/-! ### The counters, over the whole package list -/

/-- Still to deliver. -/
def live (σ : AtomState) (pk : PackageInfo) : Bool := !σ pk.goalAtom

theorem handling_eq (c : Cfg) (σ : AtomState) :
    Hc c σ = (c.packages.toList.map fun pk =>
      if live σ pk then handlingCost σ pk else 0).sum := by
  show handling c σ = _
  unfold handling unmet live
  rw [← Array.foldl_toList, foldl_add_eq_sum, Array.toList_filter, ← sum_filter_eq_ite]
  simp

theorem driving_eq (c : Cfg) (σ : AtomState) :
    Dc c σ = c.packages.toList.foldl (fun acc pk =>
      max acc (if live σ pk then drivingOf c σ (vehicleLocations c σ) pk else 0)) 0 := by
  show driving c σ = _
  unfold driving unmet live
  rw [← Array.foldl_toList, Array.toList_filter, foldl_max_filter]

theorem required_eq (c : Cfg) (σ : AtomState) :
    requiredLocs c σ = distinct (((c.packages.toList.filter
      (fun pk => !σ pk.goalAtom)).flatMap fun pk =>
      pk.goalLoc :: (match groundLoc σ pk with | some l => [l] | none => [])).filter
      fun l => !(vehicleLocations c σ).contains l) := by
  unfold requiredLocs unmet
  rw [Array.toList_filter]

theorem set_mono (c : Cfg) (σ τ : AtomState) {l l' : List Nat}
    (hl : requiredLocs c σ = distinct l) (hl' : requiredLocs c τ = distinct l')
    (h : ∀ x ∈ l, x ∈ l') : Rc c σ ≤ Rc c τ := by
  show (requiredLocs c σ).length ≤ (requiredLocs c τ).length
  rw [hl, hl']
  exact length_distinct_mono l l' h

theorem set_le_succ (c : Cfg) (σ τ : AtomState) {l l' : List Nat} (a : Nat)
    (hl : requiredLocs c σ = distinct l) (hl' : requiredLocs c τ = distinct l')
    (h : ∀ x ∈ l, x ∈ l' ∨ x = a) : Rc c σ ≤ Rc c τ + 1 := by
  show (requiredLocs c σ).length ≤ (requiredLocs c τ).length + 1
  rw [hl, hl']
  exact length_distinct_le_succ l l' a h

end Planner.Lifted.Transport

/- -------------------------------------------------------------------------- -/
/-
Transport, stated over ground atoms at the schema level.

The file says what the domain's schemas do to the predicates — where each vehicle
stands, where a package sits, which vehicle carries it — and derives the three
counters from that.  Nothing about the counters themselves is assumed.

The counters do not all fall.  `pick-up` and `drop` can each *raise* the handling
count: dropping a package short of its destination takes it from carried (worth
one) to on the ground (worth two), and picking up a package that already sits at
its destination puts it back into the unmet set.  Both are harmless, and the
shapes below carry the weaker, true bound `H ≤ H' + 1`, which covers all four
cases at once.
-/

namespace Planner.Lifted.Transport

open Planner Planner.Pddl

/-! ### What each schema does -/

/--
`pick-up` and `drop`.  A vehicle stands at `l`; the package `q` is at `l` or in
that vehicle, before and after.  One structure covers all four cases — picking up
a package that was still to deliver or one already delivered, dropping at the
destination or short of it — because the bounds they need are the same.
-/
structure LoadStep (g : Graph) (c : Cfg) (σ τ : AtomState) (v l : Nat)
    (q : PackageInfo) : Prop where
  memQ : q ∈ c.packages
  lLt : l < g.size
  vehMem : l ∈ vehicleLocations c σ
  vehOcc : (vehicleLocations c σ).contains l = true
  vehLoc : (vehicleLocations c σ).getD v c.dist.bound = l
  atQ : groundLoc σ q = some l ∨ (groundLoc σ q = none ∧ carrier σ q = some v)
  atQ' : groundLoc τ q = some l ∨ (groundLoc τ q = none ∧ carrier τ q = some v)
  /--
  The only way `q` becomes *newly* delivered here is a drop at its own
  destination.  Stated for a goal that did not already hold: a `pick-up` of a
  package already standing where the goal wants it leaves the goal true without
  any of these holding, and a shape that asked for them unconditionally would not
  be satisfiable.
  -/
  served' : σ q.goalAtom = false → τ q.goalAtom = true →
    q.goalLoc = l ∧ groundLoc σ q = none ∧ carrier σ q = some v
  frameVeh : vehicleLocations c τ = vehicleLocations c σ
  frameGround : ∀ pk ∈ c.packages, pk ≠ q → groundLoc τ pk = groundLoc σ pk
  frameCarrier : ∀ pk ∈ c.packages, pk ≠ q → carrier τ pk = carrier σ pk
  frameServed : ∀ pk ∈ c.packages, pk ≠ q → τ pk.goalAtom = σ pk.goalAtom

/-- `drive`: one vehicle leaves `l1` for the adjacent `l2`; no package moves. -/
structure DriveStep (g : Graph) (c : Cfg) (σ τ : AtomState) (l1 l2 : Nat) : Prop where
  l1Lt : l1 < g.size
  adj : l2 ∈ g.adj.getD l1 #[]
  /--
  Each vehicle stays put, is the one that drove, or has no position at all.

  The third case is not idle.  Relevance pruning can drop the `at` an operator
  adds while keeping the one it deletes, and then the vehicle the operator moves
  reads as nowhere afterwards.  Every term the value takes from a vehicle only
  grows when that happens, so the bound survives; a shape that ruled it out would
  not be satisfiable on the pruned task.
  -/
  vehEntry : ∀ i, (vehicleLocations c τ).getD i c.dist.bound
      = (vehicleLocations c σ).getD i c.dist.bound
    ∨ ((vehicleLocations c σ).getD i c.dist.bound = l1
       ∧ (vehicleLocations c τ).getD i c.dist.bound = l2)
    ∨ (vehicleLocations c τ).getD i c.dist.bound = c.dist.bound
  /-- Every place a vehicle stands afterwards is one it stood on before, or `l2`. -/
  occNew : ∀ x, (vehicleLocations c τ).contains x = true →
    (vehicleLocations c σ).contains x = true ∨ x = l2 ∨ x = c.dist.bound
  /-- The only new vehicle position is `l2`, reached from `l1`. -/
  vehNew : ∀ w ∈ vehicleLocations c τ,
    w ∈ vehicleLocations c σ ∨ w = l2 ∨ w = c.dist.bound
  l1Mem : l1 ∈ vehicleLocations c σ
  frameGround : ∀ pk ∈ c.packages, groundLoc τ pk = groundLoc σ pk
  frameCarrier : ∀ pk ∈ c.packages, carrier τ pk = carrier σ pk
  frameServed : ∀ pk ∈ c.packages, τ pk.goalAtom = σ pk.goalAtom

/--
A step that touches nothing the value reads.

`pick-up` and `drop` of a package the goal never mentions have this shape: the
package is in no entry of `c.packages`, so no ground position, no carrier and no
goal fact moves, and no vehicle moves either.  Such an action is neither a
`LoadStep`, which names the entry it moves, nor a `DriveStep`, which names the
road it drives.  Every transport task in the benchmark set gives each package a
goal, so the case is never taken there, but a task without one is a transport
task all the same.
-/
structure StallStep (c : Cfg) (σ τ : AtomState) : Prop where
  frameVeh : vehicleLocations c τ = vehicleLocations c σ
  frameGround : ∀ pk ∈ c.packages, groundLoc τ pk = groundLoc σ pk
  frameCarrier : ∀ pk ∈ c.packages, carrier τ pk = carrier σ pk
  frameServed : ∀ pk ∈ c.packages, τ pk.goalAtom = σ pk.goalAtom

/-- One action of the domain. -/
inductive SchemaStep (g : Graph) (c : Cfg) (σ τ : AtomState) : Prop
  | load (v l : Nat) (q : PackageInfo) (h : LoadStep g c σ τ v l q)
  | drive (l1 l2 : Nat) (h : DriveStep g c σ τ l1 l2)
  | stall (h : StallStep c σ τ)

/-! ### The counters, derived from the shapes -/

namespace LoadStep

variable {g : Graph} {c : Cfg} {σ τ : AtomState} {v l : Nat} {q : PackageInfo}

theorem minFrom_zero (h : LoadStep g c σ τ v l q) (hsound : Distances.Sound g c.dist) :
    c.dist.minFrom (vehicleLocations c σ) l = 0 := by
  have := minFrom_le_of_mem c.dist h.vehMem l
  rw [hsound.self l h.lLt] at this
  omega

theorem drivingOf_q (h : LoadStep g c σ τ v l q) (hsound : Distances.Sound g c.dist) :
    drivingOf c σ (vehicleLocations c σ) q = c.dist.get l q.goalLoc := by
  rcases h.atQ with hg | ⟨hg, hc⟩
  · simp [drivingOf, hg, h.minFrom_zero hsound]
  · simp [drivingOf, hg, hc, h.vehLoc]

theorem drivingOf_q' (h : LoadStep g c σ τ v l q) (hsound : Distances.Sound g c.dist) :
    drivingOf c τ (vehicleLocations c τ) q = c.dist.get l q.goalLoc := by
  rw [h.frameVeh]
  rcases h.atQ' with hg | ⟨hg, hc⟩
  · simp [drivingOf, hg, h.minFrom_zero hsound]
  · simp [drivingOf, hg, hc, h.vehLoc]

theorem handlingCost_q_le (h : LoadStep g c σ τ v l q) : handlingCost σ q ≤ 2 := by
  rcases h.atQ with hg | ⟨hg, hc⟩
  · simp [handlingCost, hg]
  · simp [handlingCost, hg, hc]

theorem handlingCost_q'_ge (h : LoadStep g c σ τ v l q) : 1 ≤ handlingCost τ q := by
  rcases h.atQ' with hg | ⟨hg, hc⟩
  · simp [handlingCost, hg]
  · simp [handlingCost, hg, hc]

theorem handlingCost_q_of_served (h : LoadStep g c σ τ v l q)
    (hs0 : σ q.goalAtom = false) (hs : τ q.goalAtom = true) :
    handlingCost σ q = 1 := by
  obtain ⟨-, hg, hc⟩ := h.served' hs0 hs
  simp [handlingCost, hg, hc]

theorem frame_handling (h : LoadStep g c σ τ v l q) {pk : PackageInfo}
    (hpk : pk ∈ c.packages) (hne : pk ≠ q) : handlingCost τ pk = handlingCost σ pk := by
  simp [handlingCost, h.frameGround pk hpk hne, h.frameCarrier pk hpk hne]

theorem frame_driving (h : LoadStep g c σ τ v l q) {pk : PackageInfo}
    (hpk : pk ∈ c.packages) (hne : pk ≠ q) :
    drivingOf c τ (vehicleLocations c τ) pk = drivingOf c σ (vehicleLocations c σ) pk := by
  simp [drivingOf, h.frameVeh, h.frameGround pk hpk hne, h.frameCarrier pk hpk hne]

theorem Hc_le (h : LoadStep g c σ τ v l q) (hnd : c.packages.toList.Nodup) :
    Hc c σ ≤ Hc c τ + 1 := by
  rw [handling_eq, handling_eq]
  refine sum_map_le_succ _ _ _ q hnd ?_ ?_
  · by_cases h1 : live σ q
    · by_cases h2 : live τ q
      · have := h.handlingCost_q_le
        have := h.handlingCost_q'_ge
        simp only [h1, h2, if_true]
        omega
      · have hs : τ q.goalAtom = true := by
          simpa [live] using h2
        simp only [h1, h2, if_true, if_false,
          h.handlingCost_q_of_served (by simpa [live] using h1) hs]
        omega
    · simp [h1]
  · intro y hy hne
    have hm : y ∈ c.packages := by simpa using hy
    simp [live, h.frameServed y hm hne, h.frame_handling hm hne]

theorem Dc_le (h : LoadStep g c σ τ v l q) (hsound : Distances.Sound g c.dist) :
    Dc c σ ≤ Dc c τ := by
  rw [driving_eq, driving_eq]
  refine foldl_max_mono _ _ _ ?_ 0 0 (Nat.le_refl _)
  intro y hy
  have hm : y ∈ c.packages := by simpa using hy
  by_cases hne : y = q
  · subst hne
    by_cases h1 : live σ y
    · by_cases h2 : live τ y
      · simp only [h1, h2, if_true, h.drivingOf_q hsound, h.drivingOf_q' hsound,
          Nat.le_refl]
      · have hs : τ y.goalAtom = true := by simpa [live] using h2
        obtain ⟨hgoal, -, -⟩ := h.served' (by simpa [live] using h1) hs
        simp only [h1, h2, if_true, if_false, h.drivingOf_q hsound, hgoal,
          hsound.self l h.lLt]
        omega
    · simp [h1]
  · simp [live, h.frameServed y hm hne, h.frame_driving hm hne]

theorem Rc_le (h : LoadStep g c σ τ v l q) (hsound : Distances.Sound g c.dist) :
    Rc c σ ≤ Rc c τ := by
  refine set_mono c σ τ (required_eq c σ) (required_eq c τ) ?_
  intro x hx
  rw [List.mem_filter] at hx ⊢
  obtain ⟨hxm, hxocc⟩ := hx
  rw [List.mem_flatMap] at hxm ⊢
  obtain ⟨pk, hpk, hxp⟩ := hxm
  rw [List.mem_filter] at hpk
  have hm : pk ∈ c.packages := by simpa using hpk.1
  have hnotOcc : (vehicleLocations c σ).contains x = false := by simpa using hxocc
  refine ⟨?_, ?_⟩
  · by_cases hne : pk = q
    · subst hne
      have hxgoal : x = pk.goalLoc := by
        rcases List.mem_cons.mp hxp with h1 | h1
        · exact h1
        · exfalso
          rcases h.atQ with hga | ⟨hga, -⟩
          · rw [hga] at h1
            simp only [List.mem_singleton] at h1
            subst h1
            rw [h.vehOcc] at hnotOcc
            exact Bool.noConfusion hnotOcc
          · rw [hga] at h1; simp at h1
      refine ⟨pk, ?_, ?_⟩
      · rw [List.mem_filter]
        refine ⟨hpk.1, ?_⟩
        by_contra hcon
        have hs : τ pk.goalAtom = true := by simpa [live] using hcon
        obtain ⟨hgoal, -, -⟩ := h.served' (by simpa [live] using hpk.2) hs
        rw [hxgoal, hgoal, h.vehOcc] at hnotOcc
        exact Bool.noConfusion hnotOcc
      · rw [hxgoal]; simp
    · refine ⟨pk, ?_, ?_⟩
      · rw [List.mem_filter]
        exact ⟨hpk.1, by simpa [live, h.frameServed pk hm hne] using hpk.2⟩
      · rwa [h.frameGround pk hm hne]
  · simpa [h.frameVeh] using hxocc

end LoadStep

namespace DriveStep

variable {g : Graph} {c : Cfg} {σ τ : AtomState} {l1 l2 : Nat}

theorem vehStep (h : DriveStep g c σ τ l1 l2) (hsound : Distances.Sound g c.dist)
    {x : Nat} (hx : x < g.size) :
    ∀ w ∈ vehicleLocations c τ, ∃ u ∈ vehicleLocations c σ,
      c.dist.get u x ≤ 1 + c.dist.get w x := by
  intro w hw
  rcases h.vehNew w hw with hmem | rfl | hb
  · exact ⟨w, hmem, by omega⟩
  · exact ⟨l1, h.l1Mem, hsound.step l1 w x h.l1Lt hx h.adj⟩
  · refine ⟨l1, h.l1Mem, ?_⟩
    rw [hb, Distances.get_of_ge hsound hsound.boundGe x]
    have := hsound.le_bound l1 x
    omega

theorem Hc_eq (h : DriveStep g c σ τ l1 l2) : Hc c τ = Hc c σ := by
  rw [handling_eq, handling_eq]
  congr 1
  refine List.map_congr_left ?_
  intro y hy
  have hm : y ∈ c.packages := by simpa using hy
  simp [live, handlingCost, h.frameServed y hm, h.frameGround y hm, h.frameCarrier y hm]

theorem drivingOf_le_succ (h : DriveStep g c σ τ l1 l2) (hsound : Distances.Sound g c.dist)
    {pk : PackageInfo} (hpk : pk ∈ c.packages) (hgoalLt : pk.goalLoc < g.size)
    (hgroundLt : ∀ lp, groundLoc σ pk = some lp → lp < g.size) :
    drivingOf c σ (vehicleLocations c σ) pk
      ≤ 1 + drivingOf c τ (vehicleLocations c τ) pk := by
  rcases hg : groundLoc σ pk with _ | lp
  · rcases hc : carrier σ pk with _ | v'
    · simp [drivingOf, hg, hc, h.frameGround pk hpk, h.frameCarrier pk hpk]
    · simp only [drivingOf, hg, hc, h.frameGround pk hpk, h.frameCarrier pk hpk]
      rcases h.vehEntry v' with heq | ⟨he1, he2⟩ | hb
      · rw [heq]; omega
      · rw [he1, he2]
        exact hsound.step l1 l2 pk.goalLoc h.l1Lt hgoalLt h.adj
      · rw [hb, Distances.get_of_ge hsound hsound.boundGe pk.goalLoc]
        have := hsound.le_bound ((vehicleLocations c σ).getD v' c.dist.bound) pk.goalLoc
        omega
  · have hkey := minFrom_le_succ c.dist (vehicleLocations c σ) (vehicleLocations c τ) lp
      (h.vehStep hsound (hgroundLt lp hg))
    simp only [drivingOf, hg, h.frameGround pk hpk]
    omega

theorem Dc_le_succ (h : DriveStep g c σ τ l1 l2) (hsound : Distances.Sound g c.dist)
    (hnodes : ∀ pk ∈ c.packages, pk.goalLoc < g.size ∧
      ∀ lp, groundLoc σ pk = some lp → lp < g.size) :
    Dc c σ ≤ Dc c τ + 1 := by
  rw [driving_eq, driving_eq]
  have hterm : ∀ y ∈ c.packages.toList,
      (if live σ y then drivingOf c σ (vehicleLocations c σ) y else 0)
        ≤ 1 + (if live τ y then drivingOf c τ (vehicleLocations c τ) y else 0) := by
    intro y hy
    have hm : y ∈ c.packages := by simpa using hy
    obtain ⟨hg1, hg2⟩ := hnodes y hm
    by_cases h1 : live σ y
    · have h2 : live τ y = true := by simpa [live, h.frameServed y hm] using h1
      simp only [h1, h2, if_true]
      exact h.drivingOf_le_succ hsound hm hg1 hg2
    · have h2 : ¬ live τ y = true := by simpa [live, h.frameServed y hm] using h1
      simp [h1, h2]
  have key := foldl_max_le_succ c.packages.toList _ _ hterm 0 0 (by omega)
  omega

theorem Rc_le_succ (h : DriveStep g c σ τ l1 l2) (hsound : Distances.Sound g c.dist)
    (hnodes : ∀ pk ∈ c.packages, pk.goalLoc < g.size ∧
      ∀ lp, groundLoc σ pk = some lp → lp < g.size) :
    Rc c σ ≤ Rc c τ + 1 := by
  refine set_le_succ c σ τ l2 (required_eq c σ) (required_eq c τ) ?_
  intro x hx
  rw [List.mem_filter] at hx
  obtain ⟨hxm, hxocc⟩ := hx
  rw [List.mem_flatMap] at hxm
  obtain ⟨pk, hpk, hxp⟩ := hxm
  rw [List.mem_filter] at hpk
  have hm : pk ∈ c.packages := by simpa using hpk.1
  have hnotOcc : (vehicleLocations c σ).contains x = false := by simpa using hxocc
  have hxlt : x < g.size := by
    obtain ⟨hg1, hg2⟩ := hnodes pk hm
    rcases List.mem_cons.mp hxp with rfl | h1
    · exact hg1
    · rcases hgl : groundLoc σ pk with _ | lp
      · rw [hgl] at h1; simp at h1
      · rw [hgl] at h1
        simp only [List.mem_singleton] at h1
        subst h1
        exact hg2 x hgl
  by_cases hxl2 : x = l2
  · exact Or.inr hxl2
  · refine Or.inl ?_
    rw [List.mem_filter, List.mem_flatMap]
    refine ⟨⟨pk, ?_, ?_⟩, ?_⟩
    · rw [List.mem_filter]
      exact ⟨hpk.1, by simpa [live, h.frameServed pk hm] using hpk.2⟩
    · rwa [h.frameGround pk hm]
    · simp only [Bool.not_eq_true']
      by_contra hcon
      have hcon' : (vehicleLocations c τ).contains x = true := by
        simpa using hcon
      rcases h.occNew x hcon' with hc | hc | hc
      · rw [hc] at hnotOcc; exact Bool.noConfusion hnotOcc
      · exact hxl2 hc
      · have := hsound.boundGe
        omega

end DriveStep

namespace StallStep

variable {c : Cfg} {σ τ : AtomState}

theorem Hc_eq (h : StallStep c σ τ) : Hc c τ = Hc c σ := by
  rw [handling_eq, handling_eq]
  congr 1
  refine List.map_congr_left ?_
  intro y hy
  have hm : y ∈ c.packages := by simpa using hy
  simp [live, handlingCost, h.frameServed y hm, h.frameGround y hm, h.frameCarrier y hm]

theorem Dc_eq (h : StallStep c σ τ) : Dc c τ = Dc c σ := by
  rw [driving_eq, driving_eq]
  refine foldl_congr_mem _ ?_ 0
  intro y hy acc
  have hm : y ∈ c.packages := by simpa using hy
  simp [live, drivingOf, h.frameVeh, h.frameServed y hm, h.frameGround y hm,
    h.frameCarrier y hm]

theorem Rc_eq (h : StallStep c σ τ) : Rc c τ = Rc c σ := by
  have hu : unmet c τ = unmet c σ :=
    array_filter_congr _ _ _ fun y hy => by rw [h.frameServed y hy]
  show (requiredLocs c τ).length = (requiredLocs c σ).length
  unfold requiredLocs
  rw [hu, h.frameVeh]
  congr 3
  refine flatMap_congr_mem _ ?_
  intro y hy
  have hm : y ∈ c.packages := by
    have := (Array.mem_filter.mp (by simpa using hy : y ∈ unmet c σ)).1
    exact this
  rw [h.frameGround y hm]

end StallStep

/-! ### The consistency step, with nothing about the counters assumed -/

theorem value_step_of_schema (g : Graph) (c : Cfg) (σ τ : AtomState)
    (hnd : c.packages.toList.Nodup) (hsound : Distances.Sound g c.dist)
    (hnodes : ∀ pk ∈ c.packages, pk.goalLoc < g.size ∧
      ∀ lp, groundLoc σ pk = some lp → lp < g.size)
    (he : SchemaStep g c σ τ) (cost : Nat) (hcost : 1 ≤ cost) :
    value c σ ≤ cost + value c τ := by
  show Hc c σ + max (Dc c σ) (Rc c σ) ≤ cost + (Hc c τ + max (Dc c τ) (Rc c τ))
  cases he with
  | load v l q h =>
      have h1 := h.Hc_le hnd
      have h2 := h.Dc_le hsound
      have h3 := h.Rc_le hsound
      omega
  | drive l1 l2 h =>
      have h1 := h.Hc_eq
      have h2 := h.Dc_le_succ hsound hnodes
      have h3 := h.Rc_le_succ hsound hnodes
      omega
  | stall h =>
      have h1 := h.Hc_eq
      have h2 := h.Dc_eq
      have h3 := h.Rc_eq
      omega

theorem liftedConsistent {d : Domain} {p : Problem} (rel : Bool) (g : Graph) (c : Cfg)
    (Inv : AtomState → Prop)
    (hnd : c.packages.toList.Nodup) (hsound : Distances.Sound g c.dist)
    (hnodes : ∀ σ, ∀ pk ∈ c.packages, pk.goalLoc < g.size ∧
      ∀ lp, groundLoc σ pk = some lp → lp < g.size)
    (hshape : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ → o.applicableA σ →
      SchemaStep g c σ (o.applyA σ))
    (hcost : ∀ o ∈ groundedOps d p rel, 0 < o.cost) :
    LiftedConsistentOn d p rel Inv (value c) := by
  intro o ho σ hinv happ
  exact value_step_of_schema g c σ (o.applyA σ) hnd hsound (hnodes σ)
    (hshape o ho σ hinv happ) o.cost (hcost o ho)

/-! ### The compiled boundary -/

theorem improved_goalAwareOn (d : Domain) (p : Problem) (rel : Bool) (c : Cfg)
    (Inv : AtomState → Prop)
    (hwf : Task.WF (ground d p rel))
    (hcost : ∀ o ∈ groundedOps d p rel, 0 < o.cost)
    (hsub : ∀ pk ∈ c.packages, pk.goalAtom ∈ p.goal)
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hpres : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ →
      o.applicableA σ → Inv (o.applyA σ))
    (hv : State → Nat) (hcomp : ComputesOn (ground d p rel) Inv hv (value c)) :
    (ground d p rel).GoalAwareOn (Reachable (ground d p rel)) hv :=
  goalAwareOn_of_lifted d p rel hwf hcost hv (value c) Inv hcomp hinit hpres
    (liftedGoalAware p c hsub)

theorem improved_consistentOn (d : Domain) (p : Problem) (rel : Bool) (g : Graph)
    (c : Cfg) (Inv : AtomState → Prop)
    (hwf : Task.WF (ground d p rel))
    (hcost : ∀ o ∈ groundedOps d p rel, 0 < o.cost)
    (hnd : c.packages.toList.Nodup) (hsound : Distances.Sound g c.dist)
    (hnodes : ∀ σ, ∀ pk ∈ c.packages, pk.goalLoc < g.size ∧
      ∀ lp, groundLoc σ pk = some lp → lp < g.size)
    (hshape : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ → o.applicableA σ →
      SchemaStep g c σ (o.applyA σ))
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hpres : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ →
      o.applicableA σ → Inv (o.applyA σ))
    (hv : State → Nat) (hcomp : ComputesOn (ground d p rel) Inv hv (value c)) :
    (ground d p rel).ConsistentOn (Reachable (ground d p rel)) hv :=
  consistentOn_of_lifted d p rel hwf hcost hv (value c) Inv hcomp hinit hpres
    (liftedConsistent rel g c Inv hnd hsound hnodes hshape hcost)

theorem improved_admissibleOn (d : Domain) (p : Problem) (rel : Bool) (g : Graph)
    (c : Cfg) (Inv : AtomState → Prop)
    (hwf : Task.WF (ground d p rel))
    (hcost : ∀ o ∈ groundedOps d p rel, 0 < o.cost)
    (hsub : ∀ pk ∈ c.packages, pk.goalAtom ∈ p.goal)
    (hnd : c.packages.toList.Nodup) (hsound : Distances.Sound g c.dist)
    (hnodes : ∀ σ, ∀ pk ∈ c.packages, pk.goalLoc < g.size ∧
      ∀ lp, groundLoc σ pk = some lp → lp < g.size)
    (hshape : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ → o.applicableA σ →
      SchemaStep g c σ (o.applyA σ))
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hpres : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ →
      o.applicableA σ → Inv (o.applyA σ))
    (hv : State → Nat) (hcomp : ComputesOn (ground d p rel) Inv hv (value c)) :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel)) hv :=
  admissibleOn_of_lifted d p rel hwf hcost hv (value c) Inv hcomp hinit hpres
    (liftedGoalAware p c hsub)
    (liftedConsistent rel g c Inv hnd hsound hnodes hshape hcost)

end Planner.Lifted.Transport

/- -------------------------------------------------------------------------- -/
/-
The compiled Transport tables and their atom-level meaning.

Each relation below says that a fact number names the atom in the corresponding
lifted entry.  The value theorem then follows structurally: paired searches find
the same location, paired filters retain the same packages, and both sides fold
the same distance table.
-/

namespace Planner.Lifted.Transport

open Planner Planner.Pddl

abbrev CData := ExampleHeuristics.Transport.Data
abbrev CPackage := ExampleHeuristics.Transport.PackageInfo

structure FactMatch (t : Task) (f : Fact) (a : GroundAtom) : Prop where
  name : t.factNames.getD f default = a
  range : f < t.factNames.size

structure PairMatch (t : Task) (x : Fact × Nat) (y : GroundAtom × Nat) : Prop where
  fact : FactMatch t x.1 y.1
  index : x.2 = y.2

structure PackageMatch (t : Task) (x : CPackage) (y : PackageInfo) : Prop where
  goal : FactMatch t x.goalFact y.goalAtom
  dest : x.goalLoc = y.goalLoc
  positions : List.Forall₂ (PairMatch t) x.atFacts.toList y.atAtoms.toList
  carried : List.Forall₂ (PairMatch t) x.inFacts.toList y.inAtoms.toList

structure DataMatches (t : Task) (c : Cfg) (dd : CData) : Prop where
  dist : dd.dist = c.dist
  veh : List.Forall₂ (fun xs ys =>
    List.Forall₂ (PairMatch t) xs.toList ys.toList) dd.vehAt.toList c.vehAt.toList
  packages : List.Forall₂ (PackageMatch t) dd.packages.toList c.packages.toList

theorem test_eq {t : Task} {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) {f : Fact} {a : GroundAtom}
    (h : FactMatch t f a) : s.test f = σ a := by
  rw [← h.name]
  exact (habs.numbered f (by rw [hn]; exact h.range)).symm

private theorem findLoc_eq {t : Task} {xs : List (Fact × Nat)}
    {ys : List (GroundAtom × Nat)} (hm : List.Forall₂ (PairMatch t) xs ys)
    {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) :
    (xs.find? fun x => s.test x.1).map (fun x => x.2) =
      (ys.find? fun y => σ y.1).map (fun y => y.2) := by
  induction hm with
  | nil => rfl
  | @cons x y xs ys hxy _ ih =>
      have ht := test_eq habs hn hxy.fact
      simp only [List.find?_cons, ht]
      by_cases hp : σ y.1
      · simp [hp, hxy.index]
      · simp [hp, ih]

private theorem findLocA_eq {t : Task} {xs : Array (Fact × Nat)}
    {ys : Array (GroundAtom × Nat)}
    (hm : List.Forall₂ (PairMatch t) xs.toList ys.toList)
    {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) :
    (xs.find? fun x => s.test x.1).map (fun x => x.2) =
      (ys.find? fun y => σ y.1).map (fun y => y.2) := by
  rw [← Array.find?_toList, ← Array.find?_toList]
  exact findLoc_eq hm habs hn

/-! ### Where the vehicles stand -/

private theorem vehList_eq {t : Task} {b : Nat}
    {xss : List (Array (Fact × Nat))} {yss : List (Array (GroundAtom × Nat))}
    (hm : List.Forall₂ (fun xs ys =>
      List.Forall₂ (PairMatch t) xs.toList ys.toList) xss yss)
    {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) :
    xss.map (fun xs => match xs.find? fun x => s.test x.1 with
                       | some (_, l) => l | none => b) =
      yss.map (fun ys => match ys.find? fun y => σ y.1 with
                         | some (_, l) => l | none => b) := by
  induction hm with
  | nil => rfl
  | @cons xs ys xss yss hxy _ ih =>
      have hloc := findLocA_eq hxy habs hn
      simp only [List.map_cons, ih]
      congr 1
      rcases hf : xs.find? (fun x => s.test x.1) with _ | ⟨f, l⟩
      · rw [hf] at hloc
        simp only [Option.map_none] at hloc
        rcases hg : ys.find? (fun y => σ y.1) with _ | ⟨a, k⟩
        · simp [hf, hg]
        · rw [hg] at hloc; simp at hloc
      · rw [hf] at hloc
        simp only [Option.map_some] at hloc
        rcases hg : ys.find? (fun y => σ y.1) with _ | ⟨a, k⟩
        · rw [hg] at hloc; simp at hloc
        · rw [hg] at hloc
          simp only [Option.map_some, Option.some.injEq] at hloc
          simp [hf, hg, hloc]

theorem vehicleLocations_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Transport.vehicleLocations dd s = vehicleLocations c σ := by
  apply Array.toList_inj.mp
  simpa [ExampleHeuristics.Transport.vehicleLocations, vehicleLocations,
    Array.toList_map, hm.dist] using vehList_eq (b := c.dist.bound) hm.veh habs hn

/-! ### One package at a time -/

theorem groundLoc_eq {t : Task} {x : CPackage} {y : PackageInfo}
    (hm : PackageMatch t x y) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Transport.groundLoc s x = groundLoc σ y :=
  findLocA_eq hm.positions habs hn

theorem carrier_eq {t : Task} {x : CPackage} {y : PackageInfo}
    (hm : PackageMatch t x y) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Transport.carrier s x = carrier σ y :=
  findLocA_eq hm.carried habs hn

theorem handlingCost_eq {t : Task} {x : CPackage} {y : PackageInfo}
    (hm : PackageMatch t x y) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Transport.handlingCost s x = handlingCost σ y := by
  unfold ExampleHeuristics.Transport.handlingCost handlingCost
  rw [groundLoc_eq hm habs hn, carrier_eq hm habs hn]
  rfl

theorem drivingOf_eq {t : Task} {c : Cfg} {dd : CData} (hd : dd.dist = c.dist)
    {x : CPackage} {y : PackageInfo} (hm : PackageMatch t x y) (veh : Array Nat)
    {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Transport.drivingOf dd s veh x = drivingOf c σ veh y := by
  unfold ExampleHeuristics.Transport.drivingOf drivingOf
  rw [groundLoc_eq hm habs hn, carrier_eq hm habs hn, hd, hm.dest]
  rfl

/-! ### The packages still to deliver -/

private theorem filterPackages {t : Task} {xs : List CPackage} {ys : List PackageInfo}
    (hm : List.Forall₂ (PackageMatch t) xs ys)
    {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) :
    List.Forall₂ (PackageMatch t)
      (xs.filter fun x => !s.test x.goalFact) (ys.filter fun y => !σ y.goalAtom) := by
  induction hm with
  | nil => exact .nil
  | @cons x y xs ys hxy _ ih =>
      have ht := test_eq habs hn hxy.goal
      simp only [List.filter_cons, ht]
      by_cases hp : σ y.goalAtom
      · simp [hp, ih]
      · simp [hp, ih, hxy]

theorem unmet_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    List.Forall₂ (PackageMatch t)
      (ExampleHeuristics.Transport.unmet dd s).toList (unmet c σ).toList := by
  simpa [ExampleHeuristics.Transport.unmet, unmet, Array.toList_filter]
    using filterPackages hm.packages habs hn

/-! ### The three quantities -/

private theorem foldSum_eq {t : Task} {xs : List CPackage} {ys : List PackageInfo}
    (hm : List.Forall₂ (PackageMatch t) xs ys)
    {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) (acc : Nat) :
    xs.foldl (fun acc x => acc + ExampleHeuristics.Transport.handlingCost s x) acc =
      ys.foldl (fun acc y => acc + handlingCost σ y) acc := by
  induction hm generalizing acc with
  | nil => rfl
  | @cons x y xs ys hxy _ ih =>
      simp only [List.foldl_cons, handlingCost_eq hxy habs hn]
      exact ih _

theorem handling_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Transport.handling dd s = handling c σ := by
  unfold ExampleHeuristics.Transport.handling handling
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact foldSum_eq (unmet_matches hm habs hn) habs hn 0

private theorem foldMax_eq {t : Task} {c : Cfg} {dd : CData} (hd : dd.dist = c.dist)
    {xs : List CPackage} {ys : List PackageInfo}
    (hm : List.Forall₂ (PackageMatch t) xs ys) (veh : Array Nat)
    {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) (acc : Nat) :
    xs.foldl (fun acc x =>
        max acc (ExampleHeuristics.Transport.drivingOf dd s veh x)) acc =
      ys.foldl (fun acc y => max acc (drivingOf c σ veh y)) acc := by
  induction hm generalizing acc with
  | nil => rfl
  | @cons x y xs ys hxy _ ih =>
      simp only [List.foldl_cons, drivingOf_eq hd hxy veh habs hn]
      exact ih _

theorem driving_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Transport.driving dd s = driving c σ := by
  have hveh := vehicleLocations_matches hm habs hn
  unfold ExampleHeuristics.Transport.driving driving
  rw [← Array.foldl_toList, ← Array.foldl_toList, hveh]
  exact foldMax_eq hm.dist (unmet_matches hm habs hn) _ habs hn 0

private theorem flatMap_eq {t : Task} {xs : List CPackage} {ys : List PackageInfo}
    (hm : List.Forall₂ (PackageMatch t) xs ys)
    {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) :
    (xs.flatMap fun x => x.goalLoc ::
        (match ExampleHeuristics.Transport.groundLoc s x with
         | some l => [l] | none => [])) =
      ys.flatMap fun y => y.goalLoc ::
        (match groundLoc σ y with | some l => [l] | none => []) := by
  induction hm with
  | nil => rfl
  | @cons x y xs ys hxy _ ih =>
      simp only [List.flatMap_cons, ih, hxy.dest, groundLoc_eq hxy habs hn]

theorem requiredLocs_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Transport.requiredLocs dd s = requiredLocs c σ := by
  have hveh := vehicleLocations_matches hm habs hn
  unfold ExampleHeuristics.Transport.requiredLocs requiredLocs
  rw [hveh]
  exact congrArg distinct (congrArg (List.filter _)
    (flatMap_eq (unmet_matches hm habs hn) habs hn))

/-- The executable Transport value computes the atom-level value. -/
theorem computes {t : Task} {c : Cfg} {dd : CData} (hm : DataMatches t c dd)
    (hn : t.numFacts = t.factNames.size) :
    Computes t (ExampleHeuristics.Transport.value dd) (value c) := by
  intro s σ habs _
  unfold ExampleHeuristics.Transport.value value
  rw [handling_matches hm habs hn, driving_matches hm habs hn,
    requiredLocs_matches hm habs hn]

theorem computesOn_of_matches {t : Task} {c : Cfg} {dd : CData}
    (Inv : AtomState → Prop) (hm : DataMatches t c dd)
    (hn : t.numFacts = t.factNames.size) :
    ComputesOn t Inv (ExampleHeuristics.Transport.value dd) (value c) := by
  intro s σ habs _
  exact computes hm hn s σ habs trivial

/-! ### The executable boundary -/

set_option maxHeartbeats 1000000 in
/-- Goal awareness for the compiled value, after its tables have been matched. -/
theorem compiled_goalAwareOn (d : Domain) (p : Problem) (rel : Bool) (c : Cfg)
    (Inv : AtomState → Prop)
    (hm : DataMatches (ground d p rel) c
      (ExampleHeuristics.Transport.compile (ground d p rel)))
    (hwf : Task.WF (ground d p rel))
    (hcost : ∀ o ∈ groundedOps d p rel, 0 < o.cost)
    (hsub : ∀ pk ∈ c.packages, pk.goalAtom ∈ p.goal)
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hpres : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ →
      o.applicableA σ → Inv (o.applyA σ)) :
    (ground d p rel).GoalAwareOn (Reachable (ground d p rel))
      (ExampleHeuristics.Transport.improved (ground d p rel)).eval :=
  improved_goalAwareOn d p rel c (Inv := Inv) hwf hcost hsub hinit hpres _
    (computesOn_of_matches Inv hm rfl)

set_option maxHeartbeats 1000000 in
/-- Consistency for the compiled value, after its tables have been matched. -/
theorem compiled_consistentOn (d : Domain) (p : Problem) (rel : Bool) (g : Graph)
    (c : Cfg) (Inv : AtomState → Prop)
    (hm : DataMatches (ground d p rel) c
      (ExampleHeuristics.Transport.compile (ground d p rel)))
    (hwf : Task.WF (ground d p rel))
    (hcost : ∀ o ∈ groundedOps d p rel, 0 < o.cost)
    (hnd : c.packages.toList.Nodup) (hsound : Distances.Sound g c.dist)
    (hnodes : ∀ σ, ∀ pk ∈ c.packages, pk.goalLoc < g.size ∧
      ∀ lp, groundLoc σ pk = some lp → lp < g.size)
    (hshape : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ → o.applicableA σ →
      SchemaStep g c σ (o.applyA σ))
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hpres : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ →
      o.applicableA σ → Inv (o.applyA σ)) :
    (ground d p rel).ConsistentOn (Reachable (ground d p rel))
      (ExampleHeuristics.Transport.improved (ground d p rel)).eval :=
  improved_consistentOn d p rel g c (Inv := Inv) hwf hcost hnd hsound hnodes hshape
    hinit hpres _ (computesOn_of_matches Inv hm rfl)

set_option maxHeartbeats 1000000 in
/-- Admissibility follows from the two executable properties. -/
theorem compiled_admissibleOn (d : Domain) (p : Problem) (rel : Bool) (g : Graph)
    (c : Cfg) (Inv : AtomState → Prop)
    (hm : DataMatches (ground d p rel) c
      (ExampleHeuristics.Transport.compile (ground d p rel)))
    (hwf : Task.WF (ground d p rel))
    (hcost : ∀ o ∈ groundedOps d p rel, 0 < o.cost)
    (hsub : ∀ pk ∈ c.packages, pk.goalAtom ∈ p.goal)
    (hnd : c.packages.toList.Nodup) (hsound : Distances.Sound g c.dist)
    (hnodes : ∀ σ, ∀ pk ∈ c.packages, pk.goalLoc < g.size ∧
      ∀ lp, groundLoc σ pk = some lp → lp < g.size)
    (hshape : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ → o.applicableA σ →
      SchemaStep g c σ (o.applyA σ))
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hpres : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ →
      o.applicableA σ → Inv (o.applyA σ)) :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel))
      (ExampleHeuristics.Transport.improved (ground d p rel)).eval :=
  improved_admissibleOn d p rel g c (Inv := Inv) hwf hcost hsub hnd hsound hnodes
    hshape hinit hpres _ (computesOn_of_matches Inv hm rfl)

end Planner.Lifted.Transport

/- -------------------------------------------------------------------------- -/
/-
The bridge from `compile` to the lifted `Cfg`.

`Proofs/Lifted/TransportComputes.lean` says what it takes for the compiled tables
and a lifted `Cfg` to agree: each fact number names the atom in the corresponding
lifted entry.  This file supplies such a `Cfg` — the one that reads every fact of
`compile` through the task's own names — and discharges the agreement outright.

What is left after this file is the shape of one transition, `SchemaStep`, which
is about the domain's schemas rather than about the tables.
-/

namespace Planner.Lifted.Transport

open Planner Planner.Pddl

/-! ### The `Cfg` a task describes -/

/-- The atom a fact number names. -/
abbrev atomOf (t : Task) (f : Fact) : GroundAtom := t.factNames.getD f default

/-- One compiled package record, read through the task's names. -/
def packageOf (t : Task) (x : CPackage) : PackageInfo where
  goalAtom := atomOf t x.goalFact
  goalLoc := x.goalLoc
  atAtoms := x.atFacts.map fun y => (atomOf t y.1, y.2)
  inAtoms := x.inFacts.map fun y => (atomOf t y.1, y.2)

/-- The configuration a transport task describes. -/
def cfgOf (t : Task) : Cfg where
  dist := (ExampleHeuristics.Transport.compile t).dist
  vehAt := (ExampleHeuristics.Transport.compile t).vehAt.map fun xs =>
    xs.map fun y => (atomOf t y.1, y.2)
  packages := (ExampleHeuristics.Transport.compile t).packages.map (packageOf t)

/-! ### Every fact the tables hold is numbered -/

theorem atOf_range (t : Task) (g : Graph) (who : Name) :
    ∀ y ∈ ExampleHeuristics.Transport.atOf (t.factsWith "at") g who,
      y.1 < t.factNames.size := by
  intro y hy
  obtain ⟨z, hz, hval⟩ := Array.mem_filterMap.mp hy
  have hzr : z.1 < t.factNames.size := factsWith_ok z hz
  revert hval
  rcases hargs : z.2.args with _ | ⟨x, rest⟩
  · simp
  · cases rest with
    | nil => simp
    | cons l rest' =>
        cases rest' with
        | cons _ _ => simp
        | nil =>
            simp only []
            by_cases hx : (x == who) = true
            · simp only [hx, if_true]
              rcases hf : g.find? l with _ | i
              · simp
              · simp only [Option.map_some, Option.some.injEq]
                intro h; rw [← h]; exact hzr
            · simp only [Bool.not_eq_true] at hx
              simp [hx]

theorem inOf_range (t : Task) (vehicles : Array Name) (who : Name) :
    ∀ y ∈ ExampleHeuristics.Transport.inOf (t.factsWith "in") vehicles who,
      y.1 < t.factNames.size := by
  intro y hy
  obtain ⟨z, hz, hval⟩ := Array.mem_filterMap.mp hy
  have hzr : z.1 < t.factNames.size := factsWith_ok z hz
  revert hval
  rcases hargs : z.2.args with _ | ⟨x, rest⟩
  · simp
  · cases rest with
    | nil => simp
    | cons v rest' =>
        cases rest' with
        | cons _ _ => simp
        | nil =>
            simp only []
            by_cases hx : (x == who) = true
            · simp only [hx, if_true]
              rcases hf : vehicles.findIdx? (· == v) with _ | i
              · simp
              · simp only [Option.map_some, Option.some.injEq]
                intro h; rw [← h]; exact hzr
            · simp only [Bool.not_eq_true] at hx
              simp [hx]

theorem packageEntry_range {t : Task} (hwf : Task.WF t)
    (hn : t.numFacts = t.factNames.size) (hsize : t.goalAtoms.size ≤ t.goal.size)
    {g : Graph} {vehicles : Array Name} {x : GroundAtom × Nat}
    (hx : x ∈ t.goalAtoms.zipIdx) {y : CPackage}
    (h : ExampleHeuristics.Transport.packageEntry t g
      (ExampleHeuristics.Transport.atOf (t.factsWith "at") g)
      (ExampleHeuristics.Transport.inOf (t.factsWith "in") vehicles) x = some y) :
    y.goalFact < t.factNames.size ∧
      (∀ z ∈ y.atFacts, z.1 < t.factNames.size) ∧
      (∀ z ∈ y.inFacts, z.1 < t.factNames.size) := by
  have hlt : x.2 < t.goal.size := by
    obtain ⟨-, h2, -⟩ := Array.mem_zipIdx hx
    omega
  have hmem : t.goal.getD x.2 0 ∈ t.goal := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]
    simpa using Array.getElem_mem hlt
  have hgoal : t.goal.getD x.2 0 < t.factNames.size := by
    rw [← hn]; exact hwf.goal _ hmem
  unfold ExampleHeuristics.Transport.packageEntry at h
  by_cases hpred : (x.1.pred == "at") = true
  · rcases hargs : x.1.args with _ | ⟨q, rest⟩
    · simp only [hpred, hargs] at h; simp at h
    · cases rest with
      | nil => simp only [hpred, hargs] at h; simp at h
      | cons gname rest' =>
          cases rest' with
          | cons _ _ => simp only [hpred, hargs] at h; simp at h
          | nil =>
              simp only [hpred, hargs] at h
              rcases hf : g.find? gname with _ | gl
              · rw [hf] at h; simp at h
              · rw [hf] at h
                simp only [Option.map_some, Option.some.injEq] at h
                rw [← h]
                exact ⟨hgoal, atOf_range t g q, inOf_range t vehicles q⟩
  · simp only [Bool.not_eq_true] at hpred
    simp only [hpred] at h
    simp at h

/-! ### The tables and the `Cfg` agree -/

private theorem pairMatch_of_range {t : Task} {y : Fact × Nat}
    (h : y.1 < t.factNames.size) : PairMatch t y (atomOf t y.1, y.2) :=
  ⟨⟨rfl, h⟩, rfl⟩

/-- **The compiled tables say of the task exactly what the lifted `Cfg` says.** -/
theorem dataMatches (t : Task) (hwf : Task.WF t) (hn : t.numFacts = t.factNames.size)
    (hsize : t.goalAtoms.size ≤ t.goal.size) :
    DataMatches t (cfgOf t) (ExampleHeuristics.Transport.compile t) := by
  refine ⟨rfl, ?_, ?_⟩
  · show List.Forall₂ _ _ (((ExampleHeuristics.Transport.compile t).vehAt.map _).toList)
    rw [Array.toList_map]
    refine forall₂_map_right _ ?_
    intro xs hxs
    show List.Forall₂ (PairMatch t) xs.toList ((xs.map _).toList)
    rw [Array.toList_map]
    refine forall₂_map_right _ ?_
    intro y hy
    refine pairMatch_of_range ?_
    have hxs' : xs ∈ (t.objectsOfTypes ["vehicle"]).map
        (ExampleHeuristics.Transport.atOf (t.factsWith "at")
          (Graph.ofStatic t "road" (t.objectsOfTypes ["location"]))) := by
      simpa [ExampleHeuristics.Transport.compile] using hxs
    obtain ⟨who, -, hval⟩ := Array.mem_map.mp hxs'
    rw [← hval] at hy
    exact atOf_range t _ who y (by simpa using hy)
  · show List.Forall₂ _ _ (((ExampleHeuristics.Transport.compile t).packages.map _).toList)
    rw [Array.toList_map]
    refine forall₂_map_right _ ?_
    intro x hx
    have hx' : x ∈ (ExampleHeuristics.Transport.compile t).packages := by simpa using hx
    obtain ⟨z, hz, hval⟩ := Array.mem_filterMap.mp hx'
    obtain ⟨hg, ha, hi⟩ := packageEntry_range hwf hn hsize hz hval
    refine ⟨⟨rfl, hg⟩, rfl, ?_, ?_⟩
    · show List.Forall₂ (PairMatch t) x.atFacts.toList ((x.atFacts.map _).toList)
      rw [Array.toList_map]
      refine forall₂_map_right _ ?_
      intro y hy
      exact pairMatch_of_range (ha y (by simpa using hy))
    · show List.Forall₂ (PairMatch t) x.inFacts.toList ((x.inFacts.map _).toList)
      rw [Array.toList_map]
      refine forall₂_map_right _ ?_
      intro y hy
      exact pairMatch_of_range (hi y (by simpa using hy))

/-! ### On the task the planner grounds -/

theorem goal_size (d : Domain) (p : Problem) (rel : Bool) :
    (ground d p rel).goalAtoms.size ≤ (ground d p rel).goal.size := by
  show p.goal.toArray.size ≤ (p.goal.toArray.map _).size
  rw [Array.size_map]

/-- **The tables agree on the task the planner searches.** -/
theorem dataMatches_ground (d : Domain) (p : Problem) (rel : Bool)
    (hwf : Task.WF (ground d p rel)) :
    DataMatches (ground d p rel) (cfgOf (ground d p rel))
      (ExampleHeuristics.Transport.compile (ground d p rel)) :=
  dataMatches _ hwf rfl (goal_size d p rel)

/-! ### The road graph, and the locations the tables name

`hnodes` and distance soundness are the two things the driving bound needs of
the graph.  Every index the tables hold came out of `Graph.find?`, and the
distance constructor is sound for the graph by construction.
-/

/-- The graph the heuristic builds. -/
abbrev graphOf (t : Task) : Graph :=
  Graph.ofStatic t "road" (t.objectsOfTypes ["location"])

theorem cfg_dist (t : Task) : (cfgOf t).dist = Distances.of (graphOf t) := rfl

theorem atOf_nodes (t : Task) (who : Name) :
    ∀ y ∈ ExampleHeuristics.Transport.atOf (t.factsWith "at") (graphOf t) who,
      y.2 < (graphOf t).size := by
  intro y hy
  obtain ⟨z, hz, hval⟩ := Array.mem_filterMap.mp hy
  revert hval
  rcases hargs : z.2.args with _ | ⟨x, rest⟩
  · simp
  · cases rest with
    | nil => simp
    | cons l rest' =>
        cases rest' with
        | cons _ _ => simp
        | nil =>
            simp only []
            by_cases hx : (x == who) = true
            · simp only [hx, if_true]
              rcases hf : (graphOf t).find? l with _ | i
              · simp
              · simp only [Option.map_some, Option.some.injEq]
                intro h; rw [← h]
                exact Graph.find?_lt hf
            · simp only [Bool.not_eq_true] at hx
              simp [hx]

theorem packageEntry_nodes {t : Task} {x : GroundAtom × Nat} {y : CPackage}
    (h : ExampleHeuristics.Transport.packageEntry t (graphOf t)
      (ExampleHeuristics.Transport.atOf (t.factsWith "at") (graphOf t))
      (ExampleHeuristics.Transport.inOf (t.factsWith "in") (t.objectsOfTypes ["vehicle"]))
      x = some y) :
    y.goalLoc < (graphOf t).size ∧ ∀ z ∈ y.atFacts, z.2 < (graphOf t).size := by
  unfold ExampleHeuristics.Transport.packageEntry at h
  by_cases hpred : (x.1.pred == "at") = true
  · rcases hargs : x.1.args with _ | ⟨q, rest⟩
    · simp only [hpred, hargs] at h; simp at h
    · cases rest with
      | nil => simp only [hpred, hargs] at h; simp at h
      | cons gname rest' =>
          cases rest' with
          | cons _ _ => simp only [hpred, hargs] at h; simp at h
          | nil =>
              simp only [hpred, hargs] at h
              rcases hf : (graphOf t).find? gname with _ | gl
              · rw [hf] at h; simp at h
              · rw [hf] at h
                simp only [Option.map_some, Option.some.injEq] at h
                rw [← h]
                exact ⟨Graph.find?_lt hf, atOf_nodes t q⟩
  · simp only [Bool.not_eq_true] at hpred
    simp only [hpred] at h
    simp at h

/-- **Every location the tables name is a node of the road graph.** -/
theorem nodes_ok (t : Task) : ∀ σ, ∀ pk ∈ (cfgOf t).packages,
    pk.goalLoc < (graphOf t).size ∧
      ∀ lp, groundLoc σ pk = some lp → lp < (graphOf t).size := by
  intro σ pk hpk
  have hpk' : pk ∈ (ExampleHeuristics.Transport.compile t).packages.map (packageOf t) := hpk
  obtain ⟨x, hx, hval⟩ := Array.mem_map.mp hpk'
  have hx' : x ∈ (ExampleHeuristics.Transport.compile t).packages := hx
  obtain ⟨z, -, hz⟩ := Array.mem_filterMap.mp hx'
  obtain ⟨hg, ha⟩ := packageEntry_nodes hz
  subst hval
  refine ⟨hg, ?_⟩
  intro lp hlp
  obtain ⟨w, hw, hwval⟩ := Option.map_eq_some_iff.mp hlp
  have hw' : w ∈ x.atFacts.map (fun y => (atomOf t y.1, y.2)) :=
    Array.mem_of_find?_eq_some hw
  obtain ⟨u, hu, huval⟩ := Array.mem_map.mp hw'
  rw [← hwval, ← huval]
  exact ha u hu

/-! ### The goal atoms the package table names -/

/-- **Every package entry names a goal atom of the problem.** -/
theorem goalAtom_mem (d : Domain) (p : Problem) (rel : Bool) :
    ∀ pk ∈ (cfgOf (ground d p rel)).packages, pk.goalAtom ∈ p.goal := by
  intro pk hpk
  have hpk' : pk ∈ (ExampleHeuristics.Transport.compile (ground d p rel)).packages.map
      (packageOf (ground d p rel)) := hpk
  obtain ⟨x, hx, hval⟩ := Array.mem_map.mp hpk'
  obtain ⟨z, hz, hzval⟩ := Array.mem_filterMap.mp (hx :
    x ∈ (ExampleHeuristics.Transport.compile (ground d p rel)).packages)
  obtain ⟨-, hlt, -⟩ := Array.mem_zipIdx hz
  have hgoal : x.goalFact = (ground d p rel).goal.getD z.2 0 := by
    unfold ExampleHeuristics.Transport.packageEntry at hzval
    by_cases hpred : (z.1.pred == "at") = true
    · rcases hargs : z.1.args with _ | ⟨q, rest⟩
      · simp only [hpred, hargs] at hzval; simp at hzval
      · cases rest with
        | nil => simp only [hpred, hargs] at hzval; simp at hzval
        | cons gname rest' =>
            cases rest' with
            | cons _ _ => simp only [hpred, hargs] at hzval; simp at hzval
            | nil =>
                simp only [hpred, hargs] at hzval
                rcases hf : (graphOf (ground d p rel)).find? gname with _ | gl
                · rw [hf] at hzval; simp at hzval
                · rw [hf] at hzval
                  simp only [Option.map_some, Option.some.injEq] at hzval
                  rw [← hzval]
    · simp only [Bool.not_eq_true] at hpred
      simp only [hpred] at hzval
      simp at hzval
  have hi : z.2 < (ground d p rel).goalAtoms.size := by simpa using hlt
  obtain ⟨hname0, -⟩ := goal_name_eq d p rel hi
  have hname : atomOf (ground d p rel) ((ground d p rel).goal.getD z.2 0)
      = (ground d p rel).goalAtoms[z.2]'hi := hname0
  subst hval
  show atomOf (ground d p rel) x.goalFact ∈ p.goal
  rw [hgoal, hname]
  have : (ground d p rel).goalAtoms[z.2]'hi ∈ (ground d p rel).goalAtoms :=
    Array.getElem_mem hi
  simpa [taskOf_goalAtoms] using this


/--
**Transport's improved heuristic is admissible on the task the planner searches**,
with nothing about its tables assumed.

Three of the old hypotheses are gone: the package entries name goal atoms of the
problem, and every location they name is a node of the road graph, are theorems
now.  What is left is the shape of one transition, the invariant the shape needs,
that the goal names each package once, and the decidable check that the distance
table is sound.
-/
theorem improved_admissible_of_shape (d : Domain) (p : Problem) (rel : Bool)
    (Inv : AtomState → Prop)
    (hwf : Task.WF (ground d p rel))
    (hcost : ∀ o ∈ groundedOps d p rel, 0 < o.cost)
    (hnd : (cfgOf (ground d p rel)).packages.toList.Nodup)
    (hsound : Distances.Sound (graphOf (ground d p rel)) (cfgOf (ground d p rel)).dist)
    (hshape : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ → o.applicableA σ →
      SchemaStep (graphOf (ground d p rel)) (cfgOf (ground d p rel)) σ (o.applyA σ))
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hpres : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ →
      o.applicableA σ → Inv (o.applyA σ)) :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel))
      (ExampleHeuristics.Transport.improved (ground d p rel)).eval :=
  compiled_admissibleOn d p rel _ _ Inv (dataMatches_ground d p rel hwf) hwf hcost
    (goalAtom_mem d p rel) hnd hsound (nodes_ok (ground d p rel)) hshape hinit hpres

/-- Goal awareness for the shipped value, from the same shape obligations. -/
theorem improved_goalAware_of_shape (d : Domain) (p : Problem) (rel : Bool)
    (Inv : AtomState → Prop)
    (hwf : Task.WF (ground d p rel))
    (hcost : ∀ o ∈ groundedOps d p rel, 0 < o.cost)
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hpres : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ →
      o.applicableA σ → Inv (o.applyA σ)) :
    (ground d p rel).GoalAwareOn (Reachable (ground d p rel))
      (ExampleHeuristics.Transport.improved (ground d p rel)).eval :=
  compiled_goalAwareOn d p rel _ Inv (dataMatches_ground d p rel hwf) hwf hcost
    (goalAtom_mem d p rel) hinit hpres

/-- And consistency. -/
theorem improved_consistent_of_shape (d : Domain) (p : Problem) (rel : Bool)
    (Inv : AtomState → Prop)
    (hwf : Task.WF (ground d p rel))
    (hcost : ∀ o ∈ groundedOps d p rel, 0 < o.cost)
    (hnd : (cfgOf (ground d p rel)).packages.toList.Nodup)
    (hsound : Distances.Sound (graphOf (ground d p rel)) (cfgOf (ground d p rel)).dist)
    (hshape : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ → o.applicableA σ →
      SchemaStep (graphOf (ground d p rel)) (cfgOf (ground d p rel)) σ (o.applyA σ))
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hpres : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ →
      o.applicableA σ → Inv (o.applyA σ)) :
    (ground d p rel).ConsistentOn (Reachable (ground d p rel))
      (ExampleHeuristics.Transport.improved (ground d p rel)).eval :=
  compiled_consistentOn d p rel _ _ Inv (dataMatches_ground d p rel hwf) hwf hcost hnd
    hsound (nodes_ok (ground d p rel)) hshape hinit hpres

end Planner.Lifted.Transport

/- -------------------------------------------------------------------------- -/
/-
Transport's invariant, and its preservation.

Each object stands in at most one place, each package rides in at most one
vehicle, and a package on the ground is in none.  All three are true of a
transport `:init` and survive every action, and they are what the transition
shapes need: they are why a vehicle's position is the one entry of its table that
holds, and why picking a package up cannot leave it in two vehicles at once.
-/

namespace Planner.Lifted.Transport

open Planner Planner.Pddl

/-! ### Atoms of different predicates are different -/

@[simp] theorem atAtom_ne_inAtom (x l q v : Name) : atAtom x l ≠ inAtom q v := by
  simp [atAtom, inAtom]
@[simp] theorem atAtom_ne_capacity (x l v s : Name) : atAtom x l ≠ capacity v s := by
  simp [atAtom, capacity]
@[simp] theorem inAtom_ne_atAtom (q v x l : Name) : inAtom q v ≠ atAtom x l := by
  simp [inAtom, atAtom]
@[simp] theorem inAtom_ne_capacity (q v w s : Name) : inAtom q v ≠ capacity w s := by
  simp [inAtom, capacity]
@[simp] theorem atAtom_eq (x l x' l' : Name) : atAtom x l = atAtom x' l' ↔ x = x' ∧ l = l' := by
  simp [atAtom]
@[simp] theorem inAtom_eq (q v q' v' : Name) : inAtom q v = inAtom q' v' ↔ q = q' ∧ v = v' := by
  simp [inAtom]

/-! ### Reading one operator through its instance -/

variable {d : Domain} {p : Problem} {o : AtomOp}

private theorem frameOf (hf : OpFacts d p o) {a : GroundAtom}
    (ha : a ∉ hf.inst.add) (hdl : a ∉ hf.inst.del) (σ : AtomState) :
    o.applyA σ a = σ a :=
  applyA_frame σ (fun hmem => ha (hf.subAdd a hmem)) (fun hmem => hdl (hf.subDel a hmem))

private theorem fallsOf (hf : OpFacts d p o) {a : GroundAtom}
    (ha : a ∉ hf.inst.add) {σ : AtomState} (h : o.applyA σ a = true) : σ a = true := by
  have hna : a ∉ o.add := fun hmem => ha (hf.subAdd a hmem)
  by_cases hdl : a ∈ o.del
  · rw [applyA_del σ hdl hna] at h; exact absurd h (by simp)
  · rwa [applyA_frame σ hna hdl] at h

private theorem delOf (hf : OpFacts d p o) {a : GroundAtom}
    (hdel : a ∈ o.del) (ha : a ∉ hf.inst.add) (σ : AtomState) :
    o.applyA σ a = false :=
  applyA_del σ hdel (fun hmem => ha (hf.subAdd a hmem))

/-! ### The invariant -/

structure Inv (σ : AtomState) : Prop where
  /-- Nothing stands in two places. -/
  oneAt : ∀ x l l', σ (atAtom x l) = true → σ (atAtom x l') = true → l = l'
  /-- No package rides in two vehicles. -/
  oneIn : ∀ q v v', σ (inAtom q v) = true → σ (inAtom q v') = true → v = v'
  /-- A package on the ground rides in none. -/
  atNotIn : ∀ q l v, σ (atAtom q l) = true → σ (inAtom q v) = true → False

/-! ### It survives every action -/

theorem inv_preserved (hd : TransportDomain d) (hf : OpFacts d p o) {σ : AtomState}
    (hinv : Inv σ) (happ : o.applicableA σ) : Inv (o.applyA σ) := by
  have hatDyn : (staticPredicates d).contains (atAtom "" "").pred = false := by
    simpa [atAtom] using at_dynamic hd
  have hinDyn : (staticPredicates d).contains (inAtom "" "").pred = false := by
    simpa [inAtom] using in_dynamic hd
  rcases instance_shape hd hf.inst with
    ⟨v, l1, l2, hs, ha⟩ | ⟨v, l, q, s1, s2, hs, ha⟩ | ⟨v, l, q, s1, s2, hs, ha⟩
  · -- drive: only the vehicle's place moves
    obtain ⟨hpre, hroad, hadd, hdel⟩ := drive_atoms hf.inst hs ha
    have hv1 : σ (atAtom v l1) = true := pre_holds hf hpre hatDyn happ
    have hin : ∀ x w, o.applyA σ (inAtom x w) = σ (inAtom x w) := by
      intro x w
      exact frameOf hf (by rw [hadd]; simp) (by rw [hdel]; simp) σ
    have hkey : ∀ n, o.applyA σ (atAtom v n) = true → n = l2 := by
      intro n hn
      by_cases hn2 : n = l2
      · exact hn2
      · exfalso
        have hnadd : atAtom v n ∉ hf.inst.add := by
          rw [hadd]; simp [hn2]
        by_cases hn1 : n = l1
        · subst hn1
          have hmemdel : atAtom v n ∈ hf.inst.del := by rw [hdel]; simp
          have hnd : atAtom v n ∈ o.del := del_kept hf hmemdel hnadd hpre hatDyn
          rw [delOf hf hnd hnadd σ] at hn
          exact Bool.noConfusion hn
        · have hfr : o.applyA σ (atAtom v n) = σ (atAtom v n) :=
            frameOf hf hnadd (by rw [hdel]; simp [hn1]) σ
          rw [hfr] at hn
          exact hn1 (hinv.oneAt v n l1 hn hv1)
    have hoff : ∀ x n, x ≠ v → o.applyA σ (atAtom x n) = σ (atAtom x n) := by
      intro x n hxv
      exact frameOf hf (by rw [hadd]; simp [hxv]) (by rw [hdel]; simp [hxv]) σ
    refine ⟨?_, ?_, ?_⟩
    · intro x m m' h1 h2
      by_cases hxv : x = v
      · subst hxv
        rw [hkey m h1, hkey m' h2]
      · rw [hoff x m hxv] at h1
        rw [hoff x m' hxv] at h2
        exact hinv.oneAt x m m' h1 h2
    · intro x w w' h1 h2
      rw [hin] at h1 h2
      exact hinv.oneIn x w w' h1 h2
    · intro x m w h1 h2
      rw [hin] at h2
      by_cases hxv : x = v
      · subst hxv
        exact hinv.atNotIn x l1 w hv1 h2
      · rw [hoff x m hxv] at h1
        exact hinv.atNotIn x m w h1 h2
  · -- pick-up: the package leaves the ground and enters the vehicle
    obtain ⟨hpreV, hpreQ, hadd, hdel⟩ := pickup_atoms hf.inst hs ha
    have hq : σ (atAtom q l) = true := pre_holds hf hpreQ hatDyn happ
    have hnadd : ∀ x m, atAtom x m ∉ hf.inst.add := by
      intro x m; rw [hadd]; simp
    have hatFall : ∀ x m, o.applyA σ (atAtom x m) = true → σ (atAtom x m) = true :=
      fun x m h => fallsOf hf (hnadd x m) h
    have hmemdel : atAtom q l ∈ hf.inst.del := by rw [hdel]; simp
    have hqGone : o.applyA σ (atAtom q l) = false :=
      delOf hf (del_kept hf hmemdel (hnadd q l) hpreQ hatDyn) (hnadd q l) σ
    have hinOther : ∀ x w, x ≠ q → o.applyA σ (inAtom x w) = σ (inAtom x w) := by
      intro x w hne
      exact frameOf hf (by rw [hadd]; simp [hne]) (by rw [hdel]; simp) σ
    have hinQ : ∀ w, o.applyA σ (inAtom q w) = true → w = v := by
      intro w hw
      by_cases hwv : w = v
      · exact hwv
      · exfalso
        have hbefore : σ (inAtom q w) = true := by
          refine fallsOf hf ?_ hw
          rw [hadd]; simp [hwv]
        exact hinv.atNotIn q l w hq hbefore
    refine ⟨?_, ?_, ?_⟩
    · intro x m m' h1 h2
      exact hinv.oneAt x m m' (hatFall x m h1) (hatFall x m' h2)
    · intro x w w' h1 h2
      by_cases hxq : x = q
      · subst hxq
        rw [hinQ w h1, hinQ w' h2]
      · rw [hinOther x w hxq] at h1
        rw [hinOther x w' hxq] at h2
        exact hinv.oneIn x w w' h1 h2
    · intro x m w h1 h2
      have hbefore := hatFall x m h1
      by_cases hxq : x = q
      · subst hxq
        have hml : m = l := hinv.oneAt x m l hbefore hq
        subst hml
        rw [hqGone] at h1
        exact Bool.noConfusion h1
      · rw [hinOther x w hxq] at h2
        exact hinv.atNotIn x m w hbefore h2
  · -- drop: the package leaves the vehicle and lands
    obtain ⟨hpreV, hpreQ, hadd, hdel⟩ := drop_atoms hf.inst hs ha
    have hq : σ (inAtom q v) = true := pre_holds hf hpreQ hinDyn happ
    have hnadd : ∀ x w, inAtom x w ∉ hf.inst.add := by
      intro x w; rw [hadd]; simp
    have hinFall : ∀ x w, o.applyA σ (inAtom x w) = true → σ (inAtom x w) = true :=
      fun x w h => fallsOf hf (hnadd x w) h
    have hmemdel : inAtom q v ∈ hf.inst.del := by rw [hdel]; simp
    have hqGone : o.applyA σ (inAtom q v) = false :=
      delOf hf (del_kept hf hmemdel (hnadd q v) hpreQ hinDyn) (hnadd q v) σ
    have hatOther : ∀ x m, x ≠ q → o.applyA σ (atAtom x m) = σ (atAtom x m) := by
      intro x m hne
      exact frameOf hf (by rw [hadd]; simp [hne]) (by rw [hdel]; simp) σ
    have hatQ : ∀ m, o.applyA σ (atAtom q m) = true → m = l := by
      intro m hm
      by_cases hml : m = l
      · exact hml
      · exfalso
        have hbefore : σ (atAtom q m) = true := by
          refine fallsOf hf ?_ hm
          rw [hadd]; simp [hml]
        exact hinv.atNotIn q m v hbefore hq
    refine ⟨?_, ?_, ?_⟩
    · intro x m m' h1 h2
      by_cases hxq : x = q
      · subst hxq
        rw [hatQ m h1, hatQ m' h2]
      · rw [hatOther x m hxq] at h1
        rw [hatOther x m' hxq] at h2
        exact hinv.oneAt x m m' h1 h2
    · intro x w w' h1 h2
      exact hinv.oneIn x w w' (hinFall x w h1) (hinFall x w' h2)
    · intro x m w h1 h2
      have hbefore := hinFall x w h2
      by_cases hxq : x = q
      · subst hxq
        have hwv : w = v := hinv.oneIn x w v hbefore hq
        subst hwv
        rw [hqGone] at h2
        exact Bool.noConfusion h2
      · rw [hatOther x m hxq] at h1
        exact hinv.atNotIn x m w h1 hbefore

/-! ### `:init` satisfies it, and the planner can check that

Every field is a statement about the two-argument atoms of `:init`, so a single
pass over the initial state decides all three.
-/

/-- The `(object, place)` pairs of `:init`. -/
def atPairs (p : Problem) : List (Name × Name) :=
  p.init.filterMap fun a =>
    match a.pred == "at", a.args with
    | true, [x, l] => some (x, l)
    | _, _ => none

/-- The `(package, vehicle)` pairs of `:init`. -/
def inPairs (p : Problem) : List (Name × Name) :=
  p.init.filterMap fun a =>
    match a.pred == "in", a.args with
    | true, [x, v] => some (x, v)
    | _, _ => none

theorem mem_atPairs {p : Problem} {x l : Name} : (x, l) ∈ atPairs p ↔ atAtom x l ∈ p.init := by
  constructor
  · intro h
    obtain ⟨a, ha, hval⟩ := List.mem_filterMap.mp h
    by_cases hp : (a.pred == "at") = true
    · rcases hargs : a.args with _ | ⟨y, rest⟩
      · rw [hargs] at hval; simp only [hp] at hval; simp at hval
      · cases rest with
        | nil => rw [hargs] at hval; simp only [hp] at hval; simp at hval
        | cons z t =>
            cases t with
            | cons _ _ => rw [hargs] at hval; simp only [hp] at hval; simp at hval
            | nil =>
                rw [hargs] at hval
                simp only [hp, Option.some.injEq, Prod.mk.injEq] at hval
                obtain ⟨rfl, rfl⟩ := hval
                have hpred : a.pred = "at" := by simpa using hp
                have heq : atAtom y z = a := by
                  unfold atAtom; rw [← hpred, ← hargs]
                rw [heq]; exact ha
    · simp only [Bool.not_eq_true] at hp
      rw [hp] at hval; simp at hval
  · intro h
    refine List.mem_filterMap.mpr ⟨atAtom x l, h, ?_⟩
    simp [atAtom]

theorem mem_inPairs {p : Problem} {x v : Name} : (x, v) ∈ inPairs p ↔ inAtom x v ∈ p.init := by
  constructor
  · intro h
    obtain ⟨a, ha, hval⟩ := List.mem_filterMap.mp h
    by_cases hp : (a.pred == "in") = true
    · rcases hargs : a.args with _ | ⟨y, rest⟩
      · rw [hargs] at hval; simp only [hp] at hval; simp at hval
      · cases rest with
        | nil => rw [hargs] at hval; simp only [hp] at hval; simp at hval
        | cons z t =>
            cases t with
            | cons _ _ => rw [hargs] at hval; simp only [hp] at hval; simp at hval
            | nil =>
                rw [hargs] at hval
                simp only [hp, Option.some.injEq, Prod.mk.injEq] at hval
                obtain ⟨rfl, rfl⟩ := hval
                have hpred : a.pred = "in" := by simpa using hp
                have heq : inAtom y z = a := by
                  unfold inAtom; rw [← hpred, ← hargs]
                rw [heq]; exact ha
    · simp only [Bool.not_eq_true] at hp
      rw [hp] at hval; simp at hval
  · intro h
    refine List.mem_filterMap.mpr ⟨inAtom x v, h, ?_⟩
    simp [inAtom]

/-- One pass over `:init` decides the invariant. -/
def initInvCheck (p : Problem) : Bool :=
  (atPairs p).all (fun x => (atPairs p).all fun y => !(x.1 == y.1) || (x.2 == y.2)) &&
  (inPairs p).all (fun x => (inPairs p).all fun y => !(x.1 == y.1) || (x.2 == y.2)) &&
  (atPairs p).all fun x => (inPairs p).all fun y => !(x.1 == y.1)

theorem initInv_of_check {p : Problem} (h : initInvCheck p = true) :
    Inv (fun a => p.init.toArray.contains a) := by
  simp only [initInvCheck, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro x l l' hl hl'
    have m1 : (x, l) ∈ atPairs p := mem_atPairs.mpr (by simpa using hl)
    have m2 : (x, l') ∈ atPairs p := mem_atPairs.mpr (by simpa using hl')
    have := h1 (x, l) m1 (x, l') m2
    simpa using this
  · intro q v v' hv hv'
    have m1 : (q, v) ∈ inPairs p := mem_inPairs.mpr (by simpa using hv)
    have m2 : (q, v') ∈ inPairs p := mem_inPairs.mpr (by simpa using hv')
    have := h2 (q, v) m1 (q, v') m2
    simpa using this
  · intro q l v hl hv
    have m1 : (q, l) ∈ atPairs p := mem_atPairs.mpr (by simpa using hl)
    have m2 : (q, v) ∈ inPairs p := mem_inPairs.mpr (by simpa using hv)
    have := h3 (q, l) m1 (q, v) m2
    simp at this


end Planner.Lifted.Transport

/- -------------------------------------------------------------------------- -/
/-
What the compiled transport tables hold, read as atoms.

`Proofs/Lifted/TransportCompile.lean` says the tables and the lifted `Cfg` agree.
This file says what the entries *are*: the `k`th vehicle list holds the atoms
`at(vₖ, l)` with the node index of `l`, and a package entry holds the atoms
`at(q, l)` and `in(q, w)` for its own object.  That is what turns a statement
about the domain's schemas into a statement about `vehicleLocations`,
`groundLoc` and `carrier`.
-/

namespace Planner.Lifted.Transport

open Planner Planner.Pddl

/-- The objects the vehicle table is indexed by. -/
abbrev vehicles (t : Task) : Array Name := t.objectsOfTypes ["vehicle"]

/-- The `k`th vehicle. -/
abbrev vehName (t : Task) (k : Nat) : Name := (vehicles t).getD k ""

/-! ### One `at` table -/

theorem mem_atOf (t : Task) (who : Name) {y : Fact × Nat}
    (hy : y ∈ ExampleHeuristics.Transport.atOf (t.factsWith "at") (graphOf t) who) :
    ∃ l, atomOf t y.1 = atAtom who l ∧ (graphOf t).find? l = some y.2 := by
  obtain ⟨z, hz, hval⟩ := Array.mem_filterMap.mp hy
  obtain ⟨-, hname, hpred⟩ := mem_factsWith hz
  revert hval
  rcases hargs : z.2.args with _ | ⟨x, rest⟩
  · simp
  · cases rest with
    | nil => simp
    | cons l rest' =>
        cases rest' with
        | cons _ _ => simp
        | nil =>
            simp only []
            by_cases hx : (x == who) = true
            · simp only [hx, if_true]
              rcases hf : (graphOf t).find? l with _ | i
              · simp
              · simp only [Option.map_some, Option.some.injEq]
                intro h
                refine ⟨l, ?_, ?_⟩
                · rw [← h]
                  show t.factNames.getD z.1 default = atAtom who l
                  rw [hname]
                  unfold atAtom
                  rw [← hpred, show who = x from (by simpa using hx : x = who).symm,
                    ← hargs]
                · rw [← h]; exact hf
            · simp only [Bool.not_eq_true] at hx
              simp [hx]

theorem mem_atOf_total (t : Task) (who l : Name) {f : Fact} {i : Nat}
    (hf : f < t.factNames.size) (hname : atomOf t f = atAtom who l)
    (hi : (graphOf t).find? l = some i) :
    (f, i) ∈ ExampleHeuristics.Transport.atOf (t.factsWith "at") (graphOf t) who := by
  refine Array.mem_filterMap.mpr ⟨(f, atAtom who l), ?_, ?_⟩
  · exact mem_factsWith_of_named hf hname rfl
  · simp only [atAtom, hi]
    simp

/-! ### The vehicle table -/

private theorem getD_map {α β : Type} (xs : Array α) (f : α → β) (k : Nat) (a : α)
    (b : β) (hd : f a = b) : (xs.map f).getD k b = f (xs.getD k a) := by
  by_cases hk : k < xs.size
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hk),
      Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk]
    simp
  · rw [Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none (by simpa using Nat.le_of_not_lt hk),
      Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt hk)]
    simpa using hd.symm

theorem vehAt_getD (t : Task) {k : Nat} (hk : k < (vehicles t).size) :
    (cfgOf t).vehAt.getD k #[] =
      (ExampleHeuristics.Transport.atOf (t.factsWith "at") (graphOf t)
        (vehName t k)).map (fun y => (atomOf t y.1, y.2)) := by
  have h1 : (cfgOf t).vehAt.getD k #[]
      = ((ExampleHeuristics.Transport.compile t).vehAt.getD k #[]).map
        (fun y => (atomOf t y.1, y.2)) := getD_map _ _ k #[] #[] (by simp)
  have h2 : (ExampleHeuristics.Transport.compile t).vehAt.getD k #[]
      = ExampleHeuristics.Transport.atOf (t.factsWith "at") (graphOf t) (vehName t k) := by
    show ((vehicles t).map
      (ExampleHeuristics.Transport.atOf (t.factsWith "at") (graphOf t))).getD k #[] = _
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hk)]
    simp only [Option.getD_some, Array.getElem_map]
    congr 1
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk]
  rw [h1, h2]

theorem vehAt_size (t : Task) : (cfgOf t).vehAt.size = (vehicles t).size := by
  show (((vehicles t).map _).map _).size = _
  simp

/-- Every entry of the `k`th vehicle list is an `at` atom of the `k`th vehicle. -/
theorem mem_vehAt (t : Task) {k : Nat} (hk : k < (vehicles t).size)
    {y : GroundAtom × Nat} (hy : y ∈ (cfgOf t).vehAt.getD k #[]) :
    ∃ l, y.1 = atAtom (vehName t k) l ∧ (graphOf t).find? l = some y.2 := by
  rw [vehAt_getD t hk] at hy
  obtain ⟨z, hz, hval⟩ := Array.mem_map.mp hy
  obtain ⟨l, hatom, hidx⟩ := mem_atOf t (vehName t k) hz
  exact ⟨l, by rw [← hval]; exact hatom, by rw [← hval]; exact hidx⟩

/-- And the atom of any numbered `at` for that vehicle is one of them. -/
theorem mem_vehAt_total (t : Task) {k : Nat} (hk : k < (vehicles t).size)
    {l : Name} {f : Fact} {i : Nat} (hf : f < t.factNames.size)
    (hname : atomOf t f = atAtom (vehName t k) l)
    (hi : (graphOf t).find? l = some i) :
    (atAtom (vehName t k) l, i) ∈ (cfgOf t).vehAt.getD k #[] := by
  rw [vehAt_getD t hk]
  refine Array.mem_map.mpr ⟨(f, i), mem_atOf_total t _ l hf hname hi, ?_⟩
  simp only [Prod.mk.injEq]
  exact ⟨hname, trivial⟩

theorem vehName_mem (t : Task) {i : Nat} (hi : i < (vehicles t).size) :
    vehName t i ∈ vehicles t := by
  show (vehicles t).getD i "" ∈ vehicles t
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
  simpa using Array.getElem_mem hi

/-- Every atom anywhere in the vehicle table is an `at` of some vehicle. -/
theorem mem_vehAt_any (t : Task) {xs : Array (GroundAtom × Nat)}
    (hxs : xs ∈ (cfgOf t).vehAt) {y : GroundAtom × Nat} (hy : y ∈ xs) :
    ∃ w l, y.1 = atAtom w l ∧ w ∈ vehicles t := by
  obtain ⟨i, hi, hival⟩ := Array.getElem_of_mem hxs
  have hilt : i < (vehicles t).size := by rw [← vehAt_size]; exact hi
  have hxs' : (cfgOf t).vehAt.getD i #[] = xs := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
    simpa using hival
  rw [← hxs'] at hy
  obtain ⟨l, hatom, -⟩ := mem_vehAt t hilt hy
  exact ⟨vehName t i, l, hatom, vehName_mem t hilt⟩


/-! ### Where a vehicle stands -/

theorem vehLoc_def (t : Task) (σ : AtomState) (k : Nat) :
    (vehicleLocations (cfgOf t) σ).getD k (cfgOf t).dist.bound =
      (match ((cfgOf t).vehAt.getD k #[]).find? (fun x => σ x.1) with
       | some (_, l) => l
       | none => (cfgOf t).dist.bound) :=
  getD_map _ _ k #[] _ (by simp)

/-- With one `at` of the vehicle holding, that is where the table says it stands. -/
theorem vehLoc_eq (t : Task) {σ : AtomState} (hinv : Inv σ) {k : Nat}
    (hk : k < (vehicles t).size) {l : Name} {i : Nat}
    (hmem : (atAtom (vehName t k) l, i) ∈ (cfgOf t).vehAt.getD k #[])
    (hσ : σ (atAtom (vehName t k) l) = true) :
    (vehicleLocations (cfgOf t) σ).getD k (cfgOf t).dist.bound = i := by
  rw [vehLoc_def]
  rcases hfind : ((cfgOf t).vehAt.getD k #[]).find? (fun x => σ x.1) with _ | z
  · exfalso
    rw [Array.find?_eq_none] at hfind
    have := hfind _ hmem
    simp only [Bool.not_eq_true] at this
    rw [hσ] at this
    exact Bool.noConfusion this
  · have hzmem : z ∈ (cfgOf t).vehAt.getD k #[] := Array.mem_of_find?_eq_some hfind
    have hzσ : σ z.1 = true := by
      have := Array.find?_some hfind
      simpa using this
    obtain ⟨l', hatom, hidx⟩ := mem_vehAt t hk hzmem
    rw [hatom] at hzσ
    have hll : l' = l := hinv.oneAt _ l' l hzσ hσ
    subst hll
    obtain ⟨l'', hatom2, hidx2⟩ := mem_vehAt t hk hmem
    have : l'' = l' := by
      have := hatom2
      simp only [atAtom_eq] at this
      exact this.2.symm
    subst this
    have h2 : z.2 = i := Option.some.inj (hidx.symm.trans hidx2)
    rw [hfind]
    show z.2 = i
    exact h2

/-- A vehicle's position is one of the positions the value reads. -/
theorem vehLoc_mem (t : Task) (σ : AtomState) {k : Nat} (hk : k < (vehicles t).size) :
    (vehicleLocations (cfgOf t) σ).getD k (cfgOf t).dist.bound
      ∈ vehicleLocations (cfgOf t) σ := by
  have hsize : (vehicleLocations (cfgOf t) σ).size = (vehicles t).size := by
    unfold vehicleLocations
    rw [Array.size_map, vehAt_size]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [hsize]; exact hk)]
  simpa using Array.getElem_mem (by rw [hsize]; exact hk : k < _)

/-! ### The package table -/

theorem mem_inOf (t : Task) (who : Name) {y : Fact × Nat}
    (hy : y ∈ ExampleHeuristics.Transport.inOf (t.factsWith "in") (vehicles t) who) :
    ∃ w, atomOf t y.1 = inAtom who w := by
  obtain ⟨z, hz, hval⟩ := Array.mem_filterMap.mp hy
  obtain ⟨-, hname, hpred⟩ := mem_factsWith hz
  revert hval
  rcases hargs : z.2.args with _ | ⟨x, rest⟩
  · simp
  · cases rest with
    | nil => simp
    | cons w rest' =>
        cases rest' with
        | cons _ _ => simp
        | nil =>
            simp only []
            by_cases hx : (x == who) = true
            · simp only [hx, if_true]
              rcases hf : (vehicles t).findIdx? (· == w) with _ | i
              · simp
              · simp only [Option.map_some, Option.some.injEq]
                intro h
                refine ⟨w, ?_⟩
                rw [← h]
                show t.factNames.getD z.1 default = inAtom who w
                rw [hname]
                unfold inAtom
                rw [← hpred, show who = x from (by simpa using hx : x = who).symm,
                  ← hargs]
            · simp only [Bool.not_eq_true] at hx
              simp [hx]

/-- Every entry of a package's tables is an atom about that package's own object. -/
theorem pkg_exists (t : Task) : ∀ pk ∈ (cfgOf t).packages,
    ∃ (q g : Name) (i : Nat) (x : CPackage),
    i < t.goalAtoms.size ∧ t.goalAtoms.getD i default = atAtom q g ∧
    ExampleHeuristics.Transport.packageEntry t (graphOf t)
      (ExampleHeuristics.Transport.atOf (t.factsWith "at") (graphOf t))
      (ExampleHeuristics.Transport.inOf (t.factsWith "in") (vehicles t))
      (atAtom q g, i) = some x ∧
    pk = packageOf t x ∧
    pk.goalAtom = atomOf t (t.goal.getD i 0) ∧
    (graphOf t).find? g = some pk.goalLoc ∧
    pk.atAtoms = (ExampleHeuristics.Transport.atOf (t.factsWith "at") (graphOf t) q).map
      (fun u => (atomOf t u.1, u.2)) ∧
    pk.inAtoms = (ExampleHeuristics.Transport.inOf (t.factsWith "in") (vehicles t) q).map
      (fun u => (atomOf t u.1, u.2)) ∧
    (∀ y ∈ pk.atAtoms, ∃ l, y.1 = atAtom q l ∧ (graphOf t).find? l = some y.2) ∧
    (∀ y ∈ pk.inAtoms, ∃ w, y.1 = inAtom q w) := by
  intro pk hpk
  have hpk' : pk ∈ (ExampleHeuristics.Transport.compile t).packages.map (packageOf t) := hpk
  obtain ⟨x, hx, hval⟩ := Array.mem_map.mp hpk'
  obtain ⟨z, hzmem, hzval⟩ := Array.mem_filterMap.mp
    (hx : x ∈ (ExampleHeuristics.Transport.compile t).packages)
  have hzorig := hzval
  obtain ⟨-, hlt, hget⟩ := Array.mem_zipIdx hzmem
  simp only [Nat.zero_add, Nat.sub_zero] at hlt hget
  have hzgoal : z.1 ∈ t.goalAtoms := by
    rw [hget]; exact Array.getElem_mem hlt
  unfold ExampleHeuristics.Transport.packageEntry at hzval
  by_cases hpred : (z.1.pred == "at") = true
  · rcases hargs : z.1.args with _ | ⟨q, rest⟩
    · simp only [hpred, hargs] at hzval; simp at hzval
    · cases rest with
      | nil => simp only [hpred, hargs] at hzval; simp at hzval
      | cons gname rest' =>
          cases rest' with
          | cons _ _ => simp only [hpred, hargs] at hzval; simp at hzval
          | nil =>
              simp only [hpred, hargs] at hzval
              rcases hf : (graphOf t).find? gname with _ | gl
              · rw [hf] at hzval; simp at hzval
              · rw [hf] at hzval
                simp only [Option.map_some, Option.some.injEq] at hzval
                have hpred' : z.1.pred = "at" := by simpa using hpred
                have hz1 : z.1 = atAtom q gname := by
                  unfold atAtom
                  rw [← hpred', ← hargs]
                have hatEq : pk.atAtoms
                    = (ExampleHeuristics.Transport.atOf (t.factsWith "at") (graphOf t) q).map
                      (fun u => (atomOf t u.1, u.2)) := by
                  rw [← hval, ← hzval]; rfl
                have hinEq : pk.inAtoms
                    = (ExampleHeuristics.Transport.inOf (t.factsWith "in") (vehicles t) q).map
                      (fun u => (atomOf t u.1, u.2)) := by
                  rw [← hval, ← hzval]; rfl
                have hlocEq : (graphOf t).find? gname = some pk.goalLoc := by
                  rw [← hval, ← hzval]
                  show (graphOf t).find? gname = some gl
                  exact hf
                refine ⟨q, gname, z.2, x, hlt, ?_, ?_, hval.symm, ?_, hlocEq, hatEq, hinEq,
                  ?_, ?_⟩
                · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]
                  simpa using hget.symm.trans hz1
                · rw [← hz1]
                  exact hzorig
                · rw [← hval, ← hzval]
                  rfl
                · intro y hy
                  rw [← hval] at hy
                  have hy' : y ∈ x.atFacts.map (fun u => (atomOf t u.1, u.2)) := hy
                  obtain ⟨u, hu, huval⟩ := Array.mem_map.mp hy'
                  rw [← hzval] at hu
                  obtain ⟨l, hatom, hidx⟩ := mem_atOf t q hu
                  exact ⟨l, by rw [← huval]; exact hatom, by rw [← huval]; exact hidx⟩
                · intro y hy
                  rw [← hval] at hy
                  have hy' : y ∈ x.inFacts.map (fun u => (atomOf t u.1, u.2)) := hy
                  obtain ⟨u, hu, huval⟩ := Array.mem_map.mp hy'
                  rw [← hzval] at hu
                  obtain ⟨w, hatom⟩ := mem_inOf t q hu
                  exact ⟨w, by rw [← huval]; exact hatom⟩
  · simp only [Bool.not_eq_true] at hpred
    simp only [hpred] at hzval
    simp at hzval


/-! ### Where a package stands, and what carries it -/

theorem mem_pkgAt_total (t : Task) {pk : PackageInfo} {q : Name}
    (hats : pk.atAtoms = (ExampleHeuristics.Transport.atOf (t.factsWith "at")
      (graphOf t) q).map (fun u => (atomOf t u.1, u.2)))
    {l : Name} {f : Fact} {i : Nat} (hf : f < t.factNames.size)
    (hname : atomOf t f = atAtom q l) (hi : (graphOf t).find? l = some i) :
    (atAtom q l, i) ∈ pk.atAtoms := by
  rw [hats]
  refine Array.mem_map.mpr ⟨(f, i), mem_atOf_total t q l hf hname hi, ?_⟩
  simp only [Prod.mk.injEq]
  exact ⟨hname, trivial⟩

/-- With one `at` of the package holding, that is where the table says it sits. -/
theorem groundLoc_of_holds (t : Task) {σ : AtomState} (hinv : Inv σ) {pk : PackageInfo} {q : Name}
    (hats : ∀ y ∈ pk.atAtoms, ∃ l, y.1 = atAtom q l ∧ (graphOf t).find? l = some y.2)
    {l : Name} {i : Nat} (hmem : (atAtom q l, i) ∈ pk.atAtoms)
    (hσ : σ (atAtom q l) = true) : groundLoc σ pk = some i := by
  unfold groundLoc
  rcases hfind : pk.atAtoms.find? (fun x => σ x.1) with _ | z
  · exfalso
    rw [Array.find?_eq_none] at hfind
    have := hfind _ hmem
    simp only [Bool.not_eq_true] at this
    rw [hσ] at this
    exact Bool.noConfusion this
  · rw [hfind]
    have hzmem : z ∈ pk.atAtoms := Array.mem_of_find?_eq_some hfind
    have hzσ : σ z.1 = true := by simpa using Array.find?_some hfind
    obtain ⟨l', hatom, hidx⟩ := hats z hzmem
    rw [hatom] at hzσ
    have hll : l' = l := hinv.oneAt q l' l hzσ hσ
    subst hll
    obtain ⟨l'', hatom2, hidx2⟩ := hats _ hmem
    have hl2 : l'' = l' := by
      have := hatom2
      simp only [atAtom_eq] at this
      exact this.2.symm
    subst hl2
    have h2 : z.2 = i := Option.some.inj (hidx.symm.trans hidx2)
    show some z.2 = some i
    rw [h2]

/-- And with no `at` holding, the table says it sits nowhere. -/
theorem groundLoc_none {σ : AtomState} {pk : PackageInfo}
    (h : ∀ y ∈ pk.atAtoms, σ y.1 = false) : groundLoc σ pk = none := by
  unfold groundLoc
  rcases hfind : pk.atAtoms.find? (fun x => σ x.1) with _ | z
  · rw [hfind]; rfl
  · exfalso
    have hzσ : σ z.1 = true := by simpa using Array.find?_some hfind
    rw [h z (Array.mem_of_find?_eq_some hfind)] at hzσ
    exact Bool.noConfusion hzσ

theorem mem_pkgIn_total (t : Task) {pk : PackageInfo} {q : Name}
    (hins : pk.inAtoms = (ExampleHeuristics.Transport.inOf (t.factsWith "in")
      (vehicles t) q).map (fun u => (atomOf t u.1, u.2)))
    {w : Name} {f : Fact} {i : Nat} (hf : f < t.factNames.size)
    (hname : atomOf t f = inAtom q w)
    (hi : (vehicles t).findIdx? (· == w) = some i) :
    (inAtom q w, i) ∈ pk.inAtoms := by
  rw [hins]
  refine Array.mem_map.mpr ⟨(f, i), ?_, ?_⟩
  · refine Array.mem_filterMap.mpr ⟨(f, inAtom q w), mem_factsWith_of_named hf hname rfl, ?_⟩
    simp only [inAtom, hi]
    simp
  · simp only [Prod.mk.injEq]
    exact ⟨hname, trivial⟩

/-- With one `in` of the package holding, that is what the table says carries it. -/
theorem carrier_of_holds (t : Task) {σ : AtomState} (hinv : Inv σ) {pk : PackageInfo} {q : Name}
    (hins : ∀ y ∈ pk.inAtoms, ∃ w, y.1 = inAtom q w)
    (hidx : ∀ y ∈ pk.inAtoms, ∀ w, y.1 = inAtom q w → (vehicles t).findIdx? (· == w) = some y.2)
    {w : Name} {i : Nat} (hmem : (inAtom q w, i) ∈ pk.inAtoms)
    (hσ : σ (inAtom q w) = true) : carrier σ pk = some i := by
  unfold carrier
  rcases hfind : pk.inAtoms.find? (fun x => σ x.1) with _ | z
  · exfalso
    rw [Array.find?_eq_none] at hfind
    have := hfind _ hmem
    simp only [Bool.not_eq_true] at this
    rw [hσ] at this
    exact Bool.noConfusion this
  · rw [hfind]
    have hzmem : z ∈ pk.inAtoms := Array.mem_of_find?_eq_some hfind
    have hzσ : σ z.1 = true := by simpa using Array.find?_some hfind
    obtain ⟨w', hatom⟩ := hins z hzmem
    rw [hatom] at hzσ
    have hww : w' = w := hinv.oneIn q w' w hzσ hσ
    have e1 := hidx z hzmem w' hatom
    rw [hww] at e1
    have e2 := hidx _ hmem w rfl
    have h2 : z.2 = i := Option.some.inj (e1.symm.trans e2)
    show some z.2 = some i
    rw [h2]

theorem carrier_none {σ : AtomState} {pk : PackageInfo}
    (h : ∀ y ∈ pk.inAtoms, σ y.1 = false) : carrier σ pk = none := by
  unfold carrier
  rcases hfind : pk.inAtoms.find? (fun x => σ x.1) with _ | z
  · rw [hfind]; rfl
  · exfalso
    have hzσ : σ z.1 = true := by simpa using Array.find?_some hfind
    rw [h z (Array.mem_of_find?_eq_some hfind)] at hzσ
    exact Bool.noConfusion hzσ

/-- The vehicle index an `in` entry carries is the one the name has. -/
theorem inOf_index (t : Task) (q : Name) {y : Fact × Nat}
    (hy : y ∈ ExampleHeuristics.Transport.inOf (t.factsWith "in") (vehicles t) q)
    (w : Name) (hw : atomOf t y.1 = inAtom q w) :
    (vehicles t).findIdx? (· == w) = some y.2 := by
  obtain ⟨z, hz, hval⟩ := Array.mem_filterMap.mp hy
  obtain ⟨-, hname, hpred⟩ := mem_factsWith hz
  revert hval
  rcases hargs : z.2.args with _ | ⟨x, rest⟩
  · simp
  · cases rest with
    | nil => simp
    | cons w' rest' =>
        cases rest' with
        | cons _ _ => simp
        | nil =>
            simp only []
            by_cases hx : (x == q) = true
            · simp only [hx, if_true]
              rcases hf : (vehicles t).findIdx? (· == w') with _ | i
              · simp
              · simp only [Option.map_some, Option.some.injEq]
                intro h
                have hy1 : y.1 = z.1 := by rw [← h]
                have hy2 : y.2 = i := by rw [← h]
                have : atomOf t z.1 = inAtom q w' := by
                  show t.factNames.getD z.1 default = inAtom q w'
                  rw [hname]
                  unfold inAtom
                  rw [← hpred, show q = x from (by simpa using hx : x = q).symm, ← hargs]
                rw [hy1, this] at hw
                simp only [inAtom, GroundAtom.mk.injEq, List.cons.injEq] at hw
                rw [hy2, ← hw.2.2.1]
                exact hf
            · simp only [Bool.not_eq_true] at hx
              simp [hx]


/-! ### Frames -/

theorem groundLoc_congr {pk : PackageInfo} {σ τ : AtomState}
    (h : ∀ y ∈ pk.atAtoms, τ y.1 = σ y.1) : groundLoc τ pk = groundLoc σ pk := by
  unfold groundLoc
  rw [array_find?_congr _ _ _ (fun y hy => h y hy)]

theorem carrier_congr {pk : PackageInfo} {σ τ : AtomState}
    (h : ∀ y ∈ pk.inAtoms, τ y.1 = σ y.1) : carrier τ pk = carrier σ pk := by
  unfold carrier
  rw [array_find?_congr _ _ _ (fun y hy => h y hy)]

theorem vehAt_congr {t : Task} {σ τ : AtomState}
    (h : ∀ xs ∈ (cfgOf t).vehAt, ∀ y ∈ xs, τ y.1 = σ y.1) :
    vehicleLocations (cfgOf t) τ = vehicleLocations (cfgOf t) σ := by
  unfold vehicleLocations
  apply Array.toList_inj.mp
  rw [Array.toList_map, Array.toList_map]
  refine List.map_congr_left ?_
  intro xs hxs
  rw [array_find?_congr _ _ _ (fun y hy => h xs (by simpa using hxs) y hy)]


end Planner.Lifted.Transport

/- -------------------------------------------------------------------------- -/
/-
Every grounded transport operator has one of the three shapes.

This is the last thing `improved_admissible_of_shape` assumes about the domain.
The argument is the same for all three schemas: read the operator's instance,
turn its atoms into statements about the tables of `Proofs/Lifted/TransportTables.lean`,
and hand the shape the frames it asks for.
-/

namespace Planner.Lifted.Transport

open Planner Planner.Pddl

/-! ### What a transport task must satisfy -/

/-- Every field is decidable on a parsed domain and problem. -/
structure Pinned (d : Domain) (p : Problem) : Prop where
  domain : TransportDomain d
  /-- The pair passed the planner's own validators.  `namesNodup` below is read
  off it rather than assumed: validation checks the objects for duplicates, the
  constants for duplicates, and rejects an object that shadows a constant. -/
  validated : Validated d p
  /-- No object's type is a proper subtype of `location`. -/
  locType : ∀ o ∈ allObjects d p, d.isSubtype o.type "location" = true → o.type = "location"
  /-- Nor of `vehicle`. -/
  vehType : ∀ o ∈ allObjects d p, d.isSubtype o.type "vehicle" = true → o.type = "vehicle"
  /-- No `at` goal names a vehicle: the value tracks packages, not the fleet. -/
  goalNotVeh : ∀ a ∈ p.goal, a.pred = "at" →
    ∀ o ∈ allObjects d p, o.name = a.args.headD "" → o.type ≠ "vehicle"
  /-- `road` never changes, and is never asked for. -/
  roadStatic : (staticPredicates d).contains "road" = true
  goalNotRoad : ∀ a ∈ p.goal, a.pred ≠ "road"
  /-- The goal names each object at most once.  Two destinations for one package
  are unreachable together, and the value would count both. -/
  goalObjUnique : ∀ a ∈ p.goal, ∀ b ∈ p.goal, a.pred = "at" → b.pred = "at" →
    a.args.headD "" = b.args.headD "" → a = b
  goalNodup : p.goal.Nodup
  /-- A vehicle is not a package. -/
  vehNotPkg : ∀ o ∈ allObjects d p, o.type = "vehicle" →
    d.isSubtype o.type "package" = false
  /-- `:init` satisfies the invariant. -/
  initCheck : initInvCheck p = true
  /-- The loading schemas' parameter types are declared. -/
  loadTypes : ∀ pm ∈ dropA.params, pm.type ∈ d.typeNames
  /-- `capacity-predecessor` never changes. -/
  capPredStatic : (staticPredicates d).contains "capacity-predecessor" = true

/-- The object names are distinct — decided by validation, not assumed. -/
theorem Pinned.namesNodup {d : Domain} {p : Problem} (hp : Pinned d p) :
    ((allObjects d p).map (·.name)).Nodup := hp.validated.namesNodup

/-! ### Operator-level frames -/

variable {d : Domain} {p : Problem} {o : AtomOp}

theorem fallsOp {a : GroundAtom} (hna : a ∉ o.add) {σ : AtomState}
    (h : o.applyA σ a = true) : σ a = true := by
  by_cases hdl : a ∈ o.del
  · rw [applyA_del σ hdl hna] at h; exact absurd h (by simp)
  · rwa [applyA_frame σ hna hdl] at h

/-! ### Names and nodes -/

theorem mem_locs {hp : Pinned d p} {rel : Bool} {l : Name}
    (hw : WellTyped d (allObjects d p) "location" l) :
    l ∈ (ground d p rel).objectsOfTypes ["location"] :=
  mem_objsOf_of_wellTyped hp.locType hw

theorem mem_vehs {hp : Pinned d p} {rel : Bool} {v : Name}
    (hw : WellTyped d (allObjects d p) "vehicle" v) : v ∈ vehicles (ground d p rel) :=
  mem_objsOf_of_wellTyped hp.vehType hw

/-- Distinct positions in the vehicle list carry distinct names. -/
theorem vehName_inj {hp : Pinned d p} {rel : Bool} {i k : Nat}
    (hi : i < (vehicles (ground d p rel)).size) (hk : k < (vehicles (ground d p rel)).size)
    (hne : i ≠ k) : vehName (ground d p rel) i ≠ vehName (ground d p rel) k := by
  have hnd : (vehicles (ground d p rel)).toList.Nodup := objsOf_nodup hp.namesNodup
  intro hc
  refine hne ?_
  have h1 : (vehicles (ground d p rel)).toList[i]'(by simpa using hi)
      = (vehicles (ground d p rel)).toList[k]'(by simpa using hk) := by
    show (vehicles (ground d p rel))[i] = (vehicles (ground d p rel))[k]
    have e1 : vehName (ground d p rel) i = (vehicles (ground d p rel))[i] := by
      show (vehicles (ground d p rel)).getD i "" = _
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]; rfl
    have e2 : vehName (ground d p rel) k = (vehicles (ground d p rel))[k] := by
      show (vehicles (ground d p rel)).getD k "" = _
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk]; rfl
    rw [← e1, ← e2]; exact hc
  exact (List.Nodup.getElem_inj_iff hnd).mp h1

/-- A package entry's object is never a vehicle. -/
theorem pkg_not_vehicle {hp : Pinned d p} {rel : Bool} {q g : Name}
    (hg : atAtom q g ∈ (ground d p rel).goalAtoms) : q ∉ vehicles (ground d p rel) := by
  intro hmem
  obtain ⟨ob, hob, hname, hty⟩ := mem_objectsOfTypes hmem
  have hob' : ob ∈ allObjects d p := by
    have h2 : ob ∈ (allObjects d p).toArray := hob
    simpa using h2
  refine hp.goalNotVeh (atAtom q g) (by simpa [taskOf_goalAtoms] using hg) rfl ob hob'
    (by rw [hname]; rfl) ?_
  simpa using hty

/-! ### The road the driver used is an edge of the graph -/

theorem road_edge (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (ho : o ∈ groundedOps d p rel) (hf : OpFacts d p o) {l1 l2 : Name}
    (hroad : road l1 l2 ∈ hf.inst.pre) {i1 i2 : Nat}
    (h1 : (graphOf (ground d p rel)).find? l1 = some i1)
    (h2 : (graphOf (ground d p rel)).find? l2 = some i2) :
    i2 ∈ (graphOf (ground d p rel)).adj.getD i1 #[] := by
  have hmem' : road l1 l2 ∈
      hf.inst.schema.pre.map (instAtom hf.inst.schema.params hf.inst.args) := hroad
  obtain ⟨y, hy, hval⟩ := List.mem_map.mp hmem'
  have hy2 : y.pred = (road l1 l2).pred := by rw [← hval]; rfl
  have hypred : y.pred = "road" := by rw [hy2]; rfl
  have hinit : road l1 l2 ∈ p.init := by
    have := hf.staticHeld y hy (by rw [hypred]; exact hp.roadStatic)
    rw [hval] at this
    simpa using this
  have hnot : road l1 l2 ∉ allAtoms (groundedOps d p rel) p.goal.toArray := by
    intro hc
    exact hp.goalNotRoad _ (mem_goal_of_static d p rel hc hp.roadStatic) rfl
  refine Graph.mem_adj_of_static ?_ h1 h2
  exact mem_staticAtoms d p rel hinit hnot


/-- A package object is never one of the vehicles. -/
theorem not_mem_vehicles (hp : Pinned d p) (rel : Bool) {q : Name}
    (hw : WellTyped d (allObjects d p) "package" q) : q ∉ vehicles (ground d p rel) :=
  not_mem_objsOf_of_wellTyped hp.namesNodup hp.vehNotPkg hw

/-! ### One package entry per object -/

/-- The whole of what a package entry is, on the task the planner grounds. -/
theorem pkg_data (rel : Bool) : ∀ pk ∈ (cfgOf (ground d p rel)).packages,
    ∃ (q g : Name) (i : Nat) (x : CPackage),
    i < (ground d p rel).goalAtoms.size ∧
    (ground d p rel).goalAtoms.getD i default = atAtom q g ∧
    ExampleHeuristics.Transport.packageEntry (ground d p rel) (graphOf (ground d p rel))
      (ExampleHeuristics.Transport.atOf ((ground d p rel).factsWith "at")
        (graphOf (ground d p rel)))
      (ExampleHeuristics.Transport.inOf ((ground d p rel).factsWith "in")
        (vehicles (ground d p rel)))
      (atAtom q g, i) = some x ∧
    pk = packageOf (ground d p rel) x ∧
    pk.goalAtom = atAtom q g ∧
    (graphOf (ground d p rel)).find? g = some pk.goalLoc ∧
    pk.atAtoms = (ExampleHeuristics.Transport.atOf ((ground d p rel).factsWith "at")
      (graphOf (ground d p rel)) q).map (fun u => (atomOf (ground d p rel) u.1, u.2)) ∧
    pk.inAtoms = (ExampleHeuristics.Transport.inOf ((ground d p rel).factsWith "in")
      (vehicles (ground d p rel)) q).map (fun u => (atomOf (ground d p rel) u.1, u.2)) ∧
    (∀ y ∈ pk.atAtoms, ∃ l, y.1 = atAtom q l ∧
      (graphOf (ground d p rel)).find? l = some y.2) ∧
    (∀ y ∈ pk.inAtoms, ∃ w, y.1 = inAtom q w) := by
  intro pk hpk
  obtain ⟨q, g, i, x, hilt, hga, hentry, hxe, hgoal, hloc, hatE, hinE, hats, hins⟩ :=
    pkg_exists (ground d p rel) pk hpk
  refine ⟨q, g, i, x, hilt, hga, hentry, hxe, ?_, hloc, hatE, hinE, hats, hins⟩
  obtain ⟨hn, -⟩ := goal_name_eq d p rel hilt
  have hn' : atomOf (ground d p rel) ((ground d p rel).goal.getD i 0)
      = (ground d p rel).goalAtoms[i]'hilt := hn
  rw [hgoal, hn']
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hilt] at hga
  simpa using hga

/-- Two entries about the same object are the same entry. -/
theorem pkg_unique (hp : Pinned d p) (rel : Bool) {pk pk' : PackageInfo}
    (h : pk ∈ (cfgOf (ground d p rel)).packages)
    (h' : pk' ∈ (cfgOf (ground d p rel)).packages) {q g g' : Name}
    (hg : pk.goalAtom = atAtom q g) (hg' : pk'.goalAtom = atAtom q g') : pk = pk' := by
  obtain ⟨q1, g1, i, x, hilt, hga, hentry, hxe, hgoal, -, -, -, -, -⟩ := pkg_data rel pk h
  obtain ⟨q2, g2, j, y, hjlt, hgb, hentry', hye, hgoal', -, -, -, -, -⟩ := pkg_data rel pk' h'
  rw [hgoal] at hg
  rw [hgoal'] at hg'
  simp only [atAtom_eq] at hg hg'
  rw [hg.1, hg.2] at hga hentry
  rw [hg'.1, hg'.2] at hgb hentry'
  -- both goal atoms are `at(q, ·)`, so they are the same atom
  have hmem1 : atAtom q g ∈ p.goal := by
    rw [← hga]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hilt]
    simpa [taskOf_goalAtoms] using Array.getElem_mem hilt
  have hmem2 : atAtom q g' ∈ p.goal := by
    rw [← hgb]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hjlt]
    simpa [taskOf_goalAtoms] using Array.getElem_mem hjlt
  have hgg : g = g' := by
    have := hp.goalObjUnique (atAtom q g) hmem1 (atAtom q g') hmem2 rfl rfl rfl
    simpa using this
  subst hgg
  -- and the goal has no repeats, so the same position
  have hnd : (ground d p rel).goalAtoms.toList.Nodup := by
    simpa [taskOf_goalAtoms] using hp.goalNodup
  have he1 : (ground d p rel).goalAtoms.toList[i]'(by simpa using hilt)
      = (ground d p rel).goalAtoms.toList[j]'(by simpa using hjlt) := by
    show (ground d p rel).goalAtoms[i] = (ground d p rel).goalAtoms[j]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hilt] at hga
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hjlt] at hgb
    simp only [Option.getD_some] at hga hgb
    rw [hga, hgb]
  have hij : i = j := (List.Nodup.getElem_inj_iff hnd).mp he1
  subst hij
  rw [hentry] at hentry'
  rw [hxe, hye, Option.some.inj hentry']


/-! ### `drive` -/

set_option maxHeartbeats 1000000 in
theorem drive_step (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (ho : o ∈ groundedOps d p rel) (hf : OpFacts d p o)
    {v l1 l2 : Name} (hs : hf.inst.schema = driveA) (hargs : hf.inst.args = [v, l1, l2])
    {σ : AtomState} (hinv : Inv σ) (happ : o.applicableA σ) :
    SchemaStep (graphOf (ground d p rel)) (cfgOf (ground d p rel)) σ (o.applyA σ) := by
  have hatDyn : (staticPredicates d).contains (atAtom "" "").pred = false := by
    simpa [atAtom] using at_dynamic hp.domain
  obtain ⟨hpre, hroad, hadd, hdel⟩ := drive_atoms hf.inst hs hargs
  have hv1 : σ (atAtom v l1) = true := pre_holds hf hpre hatDyn happ
  have hinv' : Inv (o.applyA σ) := inv_preserved hp.domain hf hinv happ
  -- the three arguments are typed
  obtain ⟨a1, a2, a3, hargs3, hw1, hw2, hw3⟩ :=
    hf.inst.args_three (show hf.inst.schema.params = [vehP, locP "?l1", locP "?l2"] by
      rw [hs])
  rw [hargs] at hargs3
  obtain ⟨rfl, rfl, rfl⟩ : v = a1 ∧ l1 = a2 ∧ l2 = a3 := by simpa using hargs3
  have hwv : WellTyped d (allObjects d p) "vehicle" v := hw1
  have hwl1 : WellTyped d (allObjects d p) "location" l1 := hw2
  have hwl2 : WellTyped d (allObjects d p) "location" l2 := hw3
  -- both ends of the road are nodes
  obtain ⟨i1, hi1⟩ := Option.isSome_iff_exists.mp
    (Graph.find?_isSome (t := ground d p rel) (pred := "road") (mem_locs (hp := hp) (rel := rel) hwl1))
  obtain ⟨i2, hi2⟩ := Option.isSome_iff_exists.mp
    (Graph.find?_isSome (t := ground d p rel) (pred := "road") (mem_locs (hp := hp) (rel := rel) hwl2))
  -- the vehicle's slot in the table
  obtain ⟨k, hk⟩ := findIdx_total (mem_vehs (hp := hp) (rel := rel) hwv)
  obtain ⟨hklt, hkname⟩ := findIdx_sound hk
  have hvk : vehName (ground d p rel) k = v := hkname
  -- its `at` atom before the step is numbered, so the table holds it
  obtain ⟨f1, hf1lt, hf1name⟩ :=
    numbered_of_op d p rel ho (Or.inl (pre_mem_op hf hpre hatDyn))
  have hmem1 : (atAtom v l1, i1) ∈ (cfgOf (ground d p rel)).vehAt.getD k #[] := by
    have := mem_vehAt_total (ground d p rel) hklt hf1lt (by rw [hvk]; exact hf1name) hi1
    rwa [hvk] at this
  have hbefore : (vehicleLocations (cfgOf (ground d p rel)) σ).getD k
      (cfgOf (ground d p rel)).dist.bound = i1 :=
    vehLoc_eq (ground d p rel) hinv hklt (by rw [hvk]; exact hmem1) (by rw [hvk]; exact hv1)
  -- every other slot is untouched
  have hother : ∀ i, i ≠ k →
      (vehicleLocations (cfgOf (ground d p rel)) (o.applyA σ)).getD i
        (cfgOf (ground d p rel)).dist.bound
      = (vehicleLocations (cfgOf (ground d p rel)) σ).getD i
        (cfgOf (ground d p rel)).dist.bound := by
    intro i hik
    rw [vehLoc_def, vehLoc_def]
    by_cases hilt : i < (vehicles (ground d p rel)).size
    · have hne : vehName (ground d p rel) i ≠ v := by
        rw [← hvk]; exact vehName_inj (hp := hp) hilt hklt hik
      rw [array_find?_congr _ _ _ ?_]
      intro y hy
      obtain ⟨l, hatom, -⟩ := mem_vehAt (ground d p rel) hilt hy
      have : o.applyA σ y.1 = σ y.1 := by
        rw [hatom]
        revert hne
        generalize vehName (ground d p rel) i = w
        intro hne
        exact frame_of_lists hf hadd hdel (by simp [hne]) (by simp [hne]) σ
      simp [this]
    · have hnone : ∀ (τ : AtomState),
          ((cfgOf (ground d p rel)).vehAt.getD i #[]).find? (fun x => τ x.1) = none := by
        intro τ
        have : (cfgOf (ground d p rel)).vehAt.getD i #[] = #[] := by
          rw [Array.getD_eq_getD_getElem?,
            Array.getElem?_eq_none (by rw [vehAt_size]; omega)]
          rfl
        rw [this]; rfl
      rw [hnone, hnone]
  -- what the vehicle's own slot can read afterwards
  have hval : ∀ y ∈ (cfgOf (ground d p rel)).vehAt.getD k #[],
      (o.applyA σ) y.1 = true → y.2 = i2 ∨ y.2 = i1 := by
    intro y hy hyt
    obtain ⟨l, hatom, hidx⟩ := mem_vehAt (ground d p rel) hklt hy
    rw [hvk] at hatom
    by_cases hin : y.1 ∈ o.add
    · have hmem := hf.subAdd _ hin
      rw [hadd] at hmem
      simp only [List.mem_singleton] at hmem
      rw [hatom] at hmem
      simp only [atAtom_eq] at hmem
      have hl2 : l = l2 := hmem.2
      subst hl2
      rw [hi2] at hidx
      exact Or.inl (Option.some.inj hidx).symm
    · have hbef : σ y.1 = true := fallsOp hin hyt
      rw [hatom] at hbef
      have hl1 : l = l1 := hinv.oneAt v l l1 hbef hv1
      subst hl1
      rw [hi1] at hidx
      exact Or.inr (Option.some.inj hidx).symm
  have hafterK :
      (vehicleLocations (cfgOf (ground d p rel)) (o.applyA σ)).getD k
        (cfgOf (ground d p rel)).dist.bound = i2 ∨
      (vehicleLocations (cfgOf (ground d p rel)) (o.applyA σ)).getD k
        (cfgOf (ground d p rel)).dist.bound = i1 ∨
      (vehicleLocations (cfgOf (ground d p rel)) (o.applyA σ)).getD k
        (cfgOf (ground d p rel)).dist.bound = (cfgOf (ground d p rel)).dist.bound := by
    rw [vehLoc_def]
    rcases hfind : ((cfgOf (ground d p rel)).vehAt.getD k #[]).find?
        (fun x => (o.applyA σ) x.1) with _ | z
    · rw [hfind]; exact Or.inr (Or.inr rfl)
    · rw [hfind]
      have hz := Array.mem_of_find?_eq_some hfind
      have hzt : (o.applyA σ) z.1 = true := by simpa using Array.find?_some hfind
      rcases hval z hz hzt with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  have hentry : ∀ i, (vehicleLocations (cfgOf (ground d p rel)) (o.applyA σ)).getD i
        (cfgOf (ground d p rel)).dist.bound
      = (vehicleLocations (cfgOf (ground d p rel)) σ).getD i
        (cfgOf (ground d p rel)).dist.bound
    ∨ ((vehicleLocations (cfgOf (ground d p rel)) σ).getD i
        (cfgOf (ground d p rel)).dist.bound = i1
       ∧ (vehicleLocations (cfgOf (ground d p rel)) (o.applyA σ)).getD i
        (cfgOf (ground d p rel)).dist.bound = i2)
    ∨ (vehicleLocations (cfgOf (ground d p rel)) (o.applyA σ)).getD i
        (cfgOf (ground d p rel)).dist.bound = (cfgOf (ground d p rel)).dist.bound := by
    intro i
    by_cases hik : i = k
    · subst hik
      rcases hafterK with h | h | h
      · exact Or.inr (Or.inl ⟨hbefore, h⟩)
      · exact Or.inl (by rw [h, hbefore])
      · exact Or.inr (Or.inr h)
    · exact Or.inl (hother i hik)
  have hsizeV : (vehicleLocations (cfgOf (ground d p rel)) (o.applyA σ)).size
      = (vehicles (ground d p rel)).size := by
    unfold vehicleLocations
    rw [Array.size_map, vehAt_size]
  have hnew : ∀ w ∈ vehicleLocations (cfgOf (ground d p rel)) (o.applyA σ),
      w ∈ vehicleLocations (cfgOf (ground d p rel)) σ ∨ w = i2 ∨
      w = (cfgOf (ground d p rel)).dist.bound := by
    intro w hw
    obtain ⟨i, hi, hival⟩ := Array.getElem_of_mem hw
    have hilt : i < (vehicles (ground d p rel)).size := by rw [← hsizeV]; exact hi
    have hw' : (vehicleLocations (cfgOf (ground d p rel)) (o.applyA σ)).getD i
        (cfgOf (ground d p rel)).dist.bound = w := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
      simpa using hival
    rcases hentry i with h | ⟨-, h⟩ | h
    · rw [hw'] at h
      exact Or.inl (h ▸ vehLoc_mem (ground d p rel) σ hilt)
    · exact Or.inr (Or.inl (by rw [← hw', h]))
    · exact Or.inr (Or.inr (by rw [← hw', h]))
  -- a package entry never names the vehicle that drove
  have hvmem : v ∈ vehicles (ground d p rel) := mem_vehs (hp := hp) (rel := rel) hwv
  have hpkg : ∀ pk ∈ (cfgOf (ground d p rel)).packages,
      (∀ y ∈ pk.atAtoms, (o.applyA σ) y.1 = σ y.1) ∧
      (∀ y ∈ pk.inAtoms, (o.applyA σ) y.1 = σ y.1) ∧
      (o.applyA σ) pk.goalAtom = σ pk.goalAtom := by
    intro pk hpk
    obtain ⟨q, g, idx, xx, hidxlt, hga, -, -, hgoal, -, -, -, hats, hins⟩ :=
      pkg_data rel pk hpk
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hidxlt] at hga
    simp only [Option.getD_some] at hga
    have hgmem : atAtom q g ∈ (ground d p rel).goalAtoms := by
      rw [← hga]; exact Array.getElem_mem hidxlt
    have hqv : q ≠ v := by
      intro hc
      exact pkg_not_vehicle (hp := hp) hgmem (hc ▸ hvmem)
    have hframeAt : ∀ x : Name, (o.applyA σ) (atAtom q x) = σ (atAtom q x) := by
      intro x
      exact frame_of_lists hf hadd hdel (by simp [hqv]) (by simp [hqv]) σ
    refine ⟨?_, ?_, ?_⟩
    · intro y hy
      obtain ⟨l, hatom, -⟩ := hats y hy
      rw [hatom]; exact hframeAt l
    · intro y hy
      obtain ⟨w, hatom⟩ := hins y hy
      rw [hatom]
      exact frame_of_lists hf hadd hdel (by simp) (by simp) σ
    · rw [hgoal]; exact hframeAt g
  refine SchemaStep.drive i1 i2 ⟨Graph.find?_lt hi1,
    road_edge hp rel ho hf hroad hi1 hi2, hentry, ?_, hnew, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hmem : x ∈ vehicleLocations (cfgOf (ground d p rel)) (o.applyA σ) := by
      simpa using hx
    rcases hnew x hmem with h | h | h
    · exact Or.inl (by simpa using h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rw [← hbefore]
    exact vehLoc_mem (ground d p rel) σ hklt
  · intro pk hpk
    exact groundLoc_congr (fun y hy => (hpkg pk hpk).1 y hy)
  · intro pk hpk
    exact carrier_congr (fun y hy => (hpkg pk hpk).2.1 y hy)
  · intro pk hpk
    exact (hpkg pk hpk).2.2




/-! ### `pick-up` -/

set_option maxHeartbeats 4000000 in
theorem pickup_step (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (ho : o ∈ groundedOps d p rel) (hf : OpFacts d p o)
    {v l q0 s1 s2 : Name} (hinAdd : inAtom q0 v ∈ o.add)
    (hs : hf.inst.schema = pickupA)
    (hargs : hf.inst.args = [v, l, q0, s1, s2])
    {σ : AtomState} (hinv : Inv σ) (happ : o.applicableA σ) :
    SchemaStep (graphOf (ground d p rel)) (cfgOf (ground d p rel)) σ (o.applyA σ) := by
  have hatDyn : (staticPredicates d).contains (atAtom "" "").pred = false := by
    simpa [atAtom] using at_dynamic hp.domain
  have hinDyn : (staticPredicates d).contains (inAtom "" "").pred = false := by
    simpa [inAtom] using in_dynamic hp.domain
  obtain ⟨hpreV, hpreQ, hadd, hdel⟩ := pickup_atoms hf.inst hs hargs
  have hvl : σ (atAtom v l) = true := pre_holds hf hpreV hatDyn happ
  have hql : σ (atAtom q0 l) = true := pre_holds hf hpreQ hatDyn happ
  have hinv' : Inv (o.applyA σ) := inv_preserved hp.domain hf hinv happ
  -- typing
  obtain ⟨a1, a2, a3, a4, a5, hargs5, hw1, hw2, hw3, hw4, hw5⟩ :=
    hf.inst.args_five (show hf.inst.schema.params
      = [vehP, locP "?l", pkgP, sizeP "?s1", sizeP "?s2"] by rw [hs])
  rw [hargs] at hargs5
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ :
      v = a1 ∧ l = a2 ∧ q0 = a3 ∧ s1 = a4 ∧ s2 = a5 := by simpa using hargs5
  have hwv : WellTyped d (allObjects d p) "vehicle" v := hw1
  have hwl : WellTyped d (allObjects d p) "location" l := hw2
  have hwq : WellTyped d (allObjects d p) "package" q0 := hw3
  have hq0nv : q0 ∉ vehicles (ground d p rel) := not_mem_vehicles hp rel hwq
  -- the vehicle table does not move
  have hframeVeh : vehicleLocations (cfgOf (ground d p rel)) (o.applyA σ)
      = vehicleLocations (cfgOf (ground d p rel)) σ := by
    refine vehAt_congr ?_
    intro xs hxs y hy
    obtain ⟨w, lw, hatom, hwmem⟩ := mem_vehAt_any (ground d p rel) hxs hy
    have hne : w ≠ q0 := by intro hc; exact hq0nv (hc ▸ hwmem)
    rw [hatom]
    exact frame_of_lists hf hadd hdel (by simp) (by simp [hne]) σ
  -- the location and the vehicle slot
  obtain ⟨li, hli⟩ := Option.isSome_iff_exists.mp
    (Graph.find?_isSome (t := ground d p rel) (pred := "road")
      (mem_locs (hp := hp) (rel := rel) hwl))
  obtain ⟨k, hk⟩ := findIdx_total (mem_vehs (hp := hp) (rel := rel) hwv)
  obtain ⟨hklt, hkname⟩ := findIdx_sound hk
  have hvk : vehName (ground d p rel) k = v := hkname
  obtain ⟨fv, hfvlt, hfvname⟩ :=
    numbered_of_op d p rel ho (Or.inl (pre_mem_op hf hpreV hatDyn))
  have hmemV : (atAtom v l, li) ∈ (cfgOf (ground d p rel)).vehAt.getD k #[] := by
    have := mem_vehAt_total (ground d p rel) hklt hfvlt (by rw [hvk]; exact hfvname) hli
    rwa [hvk] at this
  have hvehLoc : (vehicleLocations (cfgOf (ground d p rel)) σ).getD k
      (cfgOf (ground d p rel)).dist.bound = li :=
    vehLoc_eq (ground d p rel) hinv hklt (by rw [hvk]; exact hmemV) (by rw [hvk]; exact hvl)
  have hvehMem : li ∈ vehicleLocations (cfgOf (ground d p rel)) σ := by
    rw [← hvehLoc]; exact vehLoc_mem (ground d p rel) σ hklt
  -- the package's own atoms
  have hatQdel : atAtom q0 l ∈ o.del := by
    refine del_kept hf (by rw [hdel]; simp) ?_ hpreQ hatDyn
    rw [hadd]; simp
  have hatQnadd : ∀ x : Name, atAtom q0 x ∉ o.add := by
    intro x hc
    have hm := hf.subAdd _ hc
    rw [hadd] at hm
    simp at hm
  have hgoneAt : ∀ x : Name, (o.applyA σ) (atAtom q0 x) = false := by
    intro x
    by_cases hx : x = l
    · rw [hx]; exact applyA_del σ hatQdel (hatQnadd l)
    · rcases hb : (o.applyA σ) (atAtom q0 x) with _ | _
      · rfl
      · exfalso
        have := fallsOp (hatQnadd x) hb
        exact hx (hinv.oneAt q0 x l this hql)
  have hinTrue : (o.applyA σ) (inAtom q0 v) = true := applyA_add σ hinAdd
  obtain ⟨fi, hfilt, hfiname⟩ := numbered_of_op d p rel ho (Or.inr (Or.inl hinAdd))
  by_cases hex : ∃ pk ∈ (cfgOf (ground d p rel)).packages, ∃ g, pk.goalAtom = atAtom q0 g
  · obtain ⟨pk, hpk, gname, hgname⟩ := hex
    obtain ⟨q1, g1, idx, xx, hidxlt, hga, -, -, hgoal, hloc, hatE, hinE, hats, hins⟩ :=
      pkg_data rel pk hpk
    have hq1 : q1 = q0 := by
      rw [hgoal] at hgname
      simpa using (by simpa using hgname : q1 = q0 ∧ g1 = gname).1
    subst hq1
    -- where it stands now
    obtain ⟨fq, hfqlt, hfqname⟩ :=
      numbered_of_op d p rel ho (Or.inl (pre_mem_op hf hpreQ hatDyn))
    have hmemQ : (atAtom q1 l, li) ∈ pk.atAtoms :=
      mem_pkgAt_total (ground d p rel) hatE hfqlt hfqname hli
    have hgroundσ : groundLoc σ pk = some li :=
      groundLoc_of_holds (ground d p rel) hinv hats hmemQ hql
    -- and where it is afterwards
    have hgroundτ : groundLoc (o.applyA σ) pk = none := by
      refine groundLoc_none ?_
      intro y hy
      obtain ⟨lx, hatom, -⟩ := hats y hy
      rw [hatom]; exact hgoneAt lx
    have hidxIn : ∀ y ∈ pk.inAtoms, ∀ w, y.1 = inAtom q1 w →
        (vehicles (ground d p rel)).findIdx? (· == w) = some y.2 := by
      intro y hy w hyw
      rw [hinE] at hy
      obtain ⟨u, hu, huval⟩ := Array.mem_map.mp hy
      have h2 : y.2 = u.2 := by rw [← huval]
      rw [h2]
      refine inOf_index (ground d p rel) q1 hu w ?_
      rw [← huval] at hyw
      simpa using hyw
    have hmemIn : (inAtom q1 v, k) ∈ pk.inAtoms :=
      mem_pkgIn_total (ground d p rel) hinE hfilt hfiname hk
    have hcarrierτ : carrier (o.applyA σ) pk = some k :=
      carrier_of_holds (ground d p rel) hinv' hins hidxIn hmemIn hinTrue
    -- entries other than this one do not move
    have hframeOther : ∀ pk' ∈ (cfgOf (ground d p rel)).packages, pk' ≠ pk →
        (∀ y ∈ pk'.atAtoms, (o.applyA σ) y.1 = σ y.1) ∧
        (∀ y ∈ pk'.inAtoms, (o.applyA σ) y.1 = σ y.1) ∧
        (o.applyA σ) pk'.goalAtom = σ pk'.goalAtom := by
      intro pk' hpk' hne
      obtain ⟨q', g', idx', xx', -, -, -, -, hgoal', -, -, -, hats', hins'⟩ :=
        pkg_data rel pk' hpk'
      have hqq : q' ≠ q1 := by
        intro hc
        exact hne (pkg_unique hp rel hpk' hpk (by rw [hgoal', hc]) hgoal)
      have hframeAt : ∀ x : Name, (o.applyA σ) (atAtom q' x) = σ (atAtom q' x) := by
        intro x
        exact frame_of_lists hf hadd hdel (by simp) (by simp [hqq]) σ
      refine ⟨?_, ?_, ?_⟩
      · intro y hy
        obtain ⟨lx, hatom, -⟩ := hats' y hy
        rw [hatom]; exact hframeAt lx
      · intro y hy
        obtain ⟨wx, hatom⟩ := hins' y hy
        rw [hatom]
        exact frame_of_lists hf hadd hdel (by simp [hqq]) (by simp) σ
      · rw [hgoal']; exact hframeAt g'
    refine SchemaStep.load k li pk ⟨hpk, Graph.find?_lt hli, hvehMem, by simpa using hvehMem,
      hvehLoc, Or.inl hgroundσ, Or.inr ⟨hgroundτ, hcarrierτ⟩, ?_, hframeVeh, ?_, ?_, ?_⟩
    · intro h0 h1
      exfalso
      rw [hgoal] at h0 h1
      rw [hgoneAt g1] at h1
      exact Bool.noConfusion h1
    · intro pk' hpk' hne
      exact groundLoc_congr (fun y hy => (hframeOther pk' hpk' hne).1 y hy)
    · intro pk' hpk' hne
      exact carrier_congr (fun y hy => (hframeOther pk' hpk' hne).2.1 y hy)
    · intro pk' hpk' hne
      exact (hframeOther pk' hpk' hne).2.2
  · -- no entry names this package, so nothing the value reads moves
    have hpkgFrame : ∀ pk ∈ (cfgOf (ground d p rel)).packages,
        (∀ y ∈ pk.atAtoms, (o.applyA σ) y.1 = σ y.1) ∧
        (∀ y ∈ pk.inAtoms, (o.applyA σ) y.1 = σ y.1) ∧
        (o.applyA σ) pk.goalAtom = σ pk.goalAtom := by
      intro pk hpk
      obtain ⟨q', g', idx', xx', -, -, -, -, hgoal', -, -, -, hats', hins'⟩ :=
        pkg_data rel pk hpk
      have hqq : q' ≠ q0 := fun hc => hex ⟨pk, hpk, g', by rw [hgoal', hc]⟩
      have hframeAt : ∀ x : Name, (o.applyA σ) (atAtom q' x) = σ (atAtom q' x) := by
        intro x
        exact frame_of_lists hf hadd hdel (by simp) (by simp [hqq]) σ
      have hframeIn : ∀ w : Name, (o.applyA σ) (inAtom q' w) = σ (inAtom q' w) := by
        intro w
        exact frame_of_lists hf hadd hdel (by simp [hqq]) (by simp) σ
      refine ⟨?_, ?_, ?_⟩
      · intro y hy
        obtain ⟨lx, hatom, -⟩ := hats' y hy
        rw [hatom]; exact hframeAt lx
      · intro y hy
        obtain ⟨wx, hatom⟩ := hins' y hy
        rw [hatom]; exact hframeIn wx
      · rw [hgoal']; exact hframeAt g'
    exact SchemaStep.stall ⟨hframeVeh,
      fun pk hpk => groundLoc_congr (fun y hy => (hpkgFrame pk hpk).1 y hy),
      fun pk hpk => carrier_congr (fun y hy => (hpkgFrame pk hpk).2.1 y hy),
      fun pk hpk => (hpkgFrame pk hpk).2.2⟩

/-! ### `drop` -/

set_option maxHeartbeats 4000000 in
theorem drop_step (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (ho : o ∈ groundedOps d p rel) (hf : OpFacts d p o)
    {v l q0 s1 s2 : Name} (hatAdd : atAtom q0 l ∈ o.add)
    (hs : hf.inst.schema = dropA)
    (hargs : hf.inst.args = [v, l, q0, s1, s2])
    {σ : AtomState} (hinv : Inv σ) (happ : o.applicableA σ) :
    SchemaStep (graphOf (ground d p rel)) (cfgOf (ground d p rel)) σ (o.applyA σ) := by
  have hatDyn : (staticPredicates d).contains (atAtom "" "").pred = false := by
    simpa [atAtom] using at_dynamic hp.domain
  have hinDyn : (staticPredicates d).contains (inAtom "" "").pred = false := by
    simpa [inAtom] using in_dynamic hp.domain
  obtain ⟨hpreV, hpreQ, hadd, hdel⟩ := drop_atoms hf.inst hs hargs
  have hvl : σ (atAtom v l) = true := pre_holds hf hpreV hatDyn happ
  have hqin : σ (inAtom q0 v) = true := pre_holds hf hpreQ hinDyn happ
  have hinv' : Inv (o.applyA σ) := inv_preserved hp.domain hf hinv happ
  obtain ⟨a1, a2, a3, a4, a5, hargs5, hw1, hw2, hw3, hw4, hw5⟩ :=
    hf.inst.args_five (show hf.inst.schema.params
      = [vehP, locP "?l", pkgP, sizeP "?s1", sizeP "?s2"] by rw [hs])
  rw [hargs] at hargs5
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ :
      v = a1 ∧ l = a2 ∧ q0 = a3 ∧ s1 = a4 ∧ s2 = a5 := by simpa using hargs5
  have hwv : WellTyped d (allObjects d p) "vehicle" v := hw1
  have hwl : WellTyped d (allObjects d p) "location" l := hw2
  have hwq : WellTyped d (allObjects d p) "package" q0 := hw3
  have hq0nv : q0 ∉ vehicles (ground d p rel) := not_mem_vehicles hp rel hwq
  have hvmem : v ∈ vehicles (ground d p rel) := mem_vehs (hp := hp) (rel := rel) hwv
  have hqv : q0 ≠ v := fun hc => hq0nv (hc ▸ hvmem)
  -- the vehicle table does not move
  have hframeVeh : vehicleLocations (cfgOf (ground d p rel)) (o.applyA σ)
      = vehicleLocations (cfgOf (ground d p rel)) σ := by
    refine vehAt_congr ?_
    intro xs hxs y hy
    obtain ⟨w, lw, hatom, hwmem⟩ := mem_vehAt_any (ground d p rel) hxs hy
    have hne : w ≠ q0 := by intro hc; exact hq0nv (hc ▸ hwmem)
    rw [hatom]
    exact frame_of_lists hf hadd hdel (by simp [hne]) (by simp) σ
  obtain ⟨li, hli⟩ := Option.isSome_iff_exists.mp
    (Graph.find?_isSome (t := ground d p rel) (pred := "road")
      (mem_locs (hp := hp) (rel := rel) hwl))
  obtain ⟨k, hk⟩ := findIdx_total (mem_vehs (hp := hp) (rel := rel) hwv)
  obtain ⟨hklt, hkname⟩ := findIdx_sound hk
  have hvk : vehName (ground d p rel) k = v := hkname
  obtain ⟨fv, hfvlt, hfvname⟩ :=
    numbered_of_op d p rel ho (Or.inl (pre_mem_op hf hpreV hatDyn))
  have hmemV : (atAtom v l, li) ∈ (cfgOf (ground d p rel)).vehAt.getD k #[] := by
    have := mem_vehAt_total (ground d p rel) hklt hfvlt (by rw [hvk]; exact hfvname) hli
    rwa [hvk] at this
  have hvehLoc : (vehicleLocations (cfgOf (ground d p rel)) σ).getD k
      (cfgOf (ground d p rel)).dist.bound = li :=
    vehLoc_eq (ground d p rel) hinv hklt (by rw [hvk]; exact hmemV) (by rw [hvk]; exact hvl)
  have hvehMem : li ∈ vehicleLocations (cfgOf (ground d p rel)) σ := by
    rw [← hvehLoc]; exact vehLoc_mem (ground d p rel) σ hklt
  -- the package leaves the vehicle and lands
  have hatTrue : (o.applyA σ) (atAtom q0 l) = true := applyA_add σ hatAdd
  have hinDelOp : inAtom q0 v ∈ o.del := by
    refine del_kept hf (by rw [hdel]; simp) ?_ hpreQ hinDyn
    rw [hadd]; simp
  have hinNadd : ∀ w : Name, inAtom q0 w ∉ o.add := by
    intro w hc
    have hm := hf.subAdd _ hc
    rw [hadd] at hm
    simp at hm
  have hgoneIn : ∀ w : Name, (o.applyA σ) (inAtom q0 w) = false := by
    intro w
    by_cases hw : w = v
    · rw [hw]; exact applyA_del σ hinDelOp (hinNadd v)
    · rcases hb : (o.applyA σ) (inAtom q0 w) with _ | _
      · rfl
      · exfalso
        have := fallsOp (hinNadd w) hb
        exact hw (hinv.oneIn q0 w v this hqin)
  have hgroundNone : ∀ x : Name, σ (atAtom q0 x) = false := by
    intro x
    rcases hb : σ (atAtom q0 x) with _ | _
    · rfl
    · exact absurd (hinv.atNotIn q0 x v hb hqin) (by simp)
  obtain ⟨fq, hfqlt, hfqname⟩ := numbered_of_op d p rel ho (Or.inr (Or.inl hatAdd))
  obtain ⟨fi, hfilt, hfiname⟩ :=
    numbered_of_op d p rel ho (Or.inl (pre_mem_op hf hpreQ hinDyn))
  by_cases hex : ∃ pk ∈ (cfgOf (ground d p rel)).packages, ∃ g, pk.goalAtom = atAtom q0 g
  · obtain ⟨pk, hpk, gname, hgname⟩ := hex
    obtain ⟨q1, g1, idx, xx, hidxlt, hga, -, -, hgoal, hloc, hatE, hinE, hats, hins⟩ :=
      pkg_data rel pk hpk
    have hq1 : q1 = q0 := by
      rw [hgoal] at hgname
      simpa using (by simpa using hgname : q1 = q0 ∧ g1 = gname).1
    subst hq1
    have hidxIn : ∀ y ∈ pk.inAtoms, ∀ w, y.1 = inAtom q1 w →
        (vehicles (ground d p rel)).findIdx? (· == w) = some y.2 := by
      intro y hy w hyw
      rw [hinE] at hy
      obtain ⟨u, hu, huval⟩ := Array.mem_map.mp hy
      have h2 : y.2 = u.2 := by rw [← huval]
      rw [h2]
      refine inOf_index (ground d p rel) q1 hu w ?_
      rw [← huval] at hyw
      simpa using hyw
    have hmemIn : (inAtom q1 v, k) ∈ pk.inAtoms :=
      mem_pkgIn_total (ground d p rel) hinE hfilt hfiname hk
    have hcarrierσ : carrier σ pk = some k :=
      carrier_of_holds (ground d p rel) hinv hins hidxIn hmemIn hqin
    have hgroundσ : groundLoc σ pk = none := by
      refine groundLoc_none ?_
      intro y hy
      obtain ⟨lx, hatom, -⟩ := hats y hy
      rw [hatom]; exact hgroundNone lx
    have hmemAt : (atAtom q1 l, li) ∈ pk.atAtoms :=
      mem_pkgAt_total (ground d p rel) hatE hfqlt hfqname hli
    have hgroundτ : groundLoc (o.applyA σ) pk = some li :=
      groundLoc_of_holds (ground d p rel) hinv' hats hmemAt hatTrue
    have hframeOther : ∀ pk' ∈ (cfgOf (ground d p rel)).packages, pk' ≠ pk →
        (∀ y ∈ pk'.atAtoms, (o.applyA σ) y.1 = σ y.1) ∧
        (∀ y ∈ pk'.inAtoms, (o.applyA σ) y.1 = σ y.1) ∧
        (o.applyA σ) pk'.goalAtom = σ pk'.goalAtom := by
      intro pk' hpk' hne
      obtain ⟨q', g', idx', xx', -, -, -, -, hgoal', -, -, -, hats', hins'⟩ :=
        pkg_data rel pk' hpk'
      have hqq : q' ≠ q1 := by
        intro hc
        exact hne (pkg_unique hp rel hpk' hpk (by rw [hgoal', hc]) hgoal)
      have hframeAt : ∀ x : Name, (o.applyA σ) (atAtom q' x) = σ (atAtom q' x) := by
        intro x
        exact frame_of_lists hf hadd hdel (by simp [hqq]) (by simp) σ
      have hframeIn : ∀ w : Name, (o.applyA σ) (inAtom q' w) = σ (inAtom q' w) := by
        intro w
        exact frame_of_lists hf hadd hdel (by simp) (by simp [hqq]) σ
      refine ⟨?_, ?_, ?_⟩
      · intro y hy
        obtain ⟨lx, hatom, -⟩ := hats' y hy
        rw [hatom]; exact hframeAt lx
      · intro y hy
        obtain ⟨wx, hatom⟩ := hins' y hy
        rw [hatom]; exact hframeIn wx
      · rw [hgoal']; exact hframeAt g'
    refine SchemaStep.load k li pk ⟨hpk, Graph.find?_lt hli, hvehMem, by simpa using hvehMem,
      hvehLoc, Or.inr ⟨hgroundσ, hcarrierσ⟩, Or.inl hgroundτ, ?_, hframeVeh, ?_, ?_, ?_⟩
    · intro h0 h1
      refine ⟨?_, hgroundσ, hcarrierσ⟩
      rw [hgoal] at h0 h1
      by_cases hgl : g1 = l
      · subst hgl
        rw [hli] at hloc
        exact (Option.some.inj hloc).symm
      · exfalso
        have hfr : (o.applyA σ) (atAtom q1 g1) = σ (atAtom q1 g1) := by
          exact frame_of_lists hf hadd hdel (by simp [hgl]) (by simp) σ
        rw [hfr, h0] at h1
        exact Bool.noConfusion h1
    · intro pk' hpk' hne
      exact groundLoc_congr (fun y hy => (hframeOther pk' hpk' hne).1 y hy)
    · intro pk' hpk' hne
      exact carrier_congr (fun y hy => (hframeOther pk' hpk' hne).2.1 y hy)
    · intro pk' hpk' hne
      exact (hframeOther pk' hpk' hne).2.2
  · have hpkgFrame : ∀ pk ∈ (cfgOf (ground d p rel)).packages,
        (∀ y ∈ pk.atAtoms, (o.applyA σ) y.1 = σ y.1) ∧
        (∀ y ∈ pk.inAtoms, (o.applyA σ) y.1 = σ y.1) ∧
        (o.applyA σ) pk.goalAtom = σ pk.goalAtom := by
      intro pk hpk
      obtain ⟨q', g', idx', xx', -, -, -, -, hgoal', -, -, -, hats', hins'⟩ :=
        pkg_data rel pk hpk
      have hqq : q' ≠ q0 := fun hc => hex ⟨pk, hpk, g', by rw [hgoal', hc]⟩
      have hframeAt : ∀ x : Name, (o.applyA σ) (atAtom q' x) = σ (atAtom q' x) := by
        intro x
        exact frame_of_lists hf hadd hdel (by simp [hqq]) (by simp) σ
      have hframeIn : ∀ w : Name, (o.applyA σ) (inAtom q' w) = σ (inAtom q' w) := by
        intro w
        exact frame_of_lists hf hadd hdel (by simp) (by simp [hqq]) σ
      refine ⟨?_, ?_, ?_⟩
      · intro y hy
        obtain ⟨lx, hatom, -⟩ := hats' y hy
        rw [hatom]; exact hframeAt lx
      · intro y hy
        obtain ⟨wx, hatom⟩ := hins' y hy
        rw [hatom]; exact hframeIn wx
      · rw [hgoal']; exact hframeAt g'
    exact SchemaStep.stall ⟨hframeVeh,
      fun pk hpk => groundLoc_congr (fun y hy => (hpkgFrame pk hpk).1 y hy),
      fun pk hpk => carrier_congr (fun y hy => (hpkgFrame pk hpk).2.1 y hy),
      fun pk hpk => (hpkgFrame pk hpk).2.2⟩


/-! ### Assembling the shape -/

/-- Every operator costs something. -/
theorem cost_pos (hp : Pinned d p) (rel : Bool) :
    ∀ o ∈ groundedOps d p rel, 0 < o.cost := by
  intro o ho
  obtain ⟨hf⟩ := opFacts_ground d p rel ho
  rw [hf.cost]
  show 0 < hf.inst.schema.cost
  rcases instance_shape hp.domain hf.inst with ⟨-, -, -, hs, -⟩ |
    ⟨-, -, -, -, -, hs, -⟩ | ⟨-, -, -, -, -, hs, -⟩ <;> rw [hs] <;> decide

/--
The adds the two loading schemas need.

With pruning off the grounder keeps them; with pruning on they survive only
because the operator that meets the goal reads them, which is the relevance
argument.  Either way the step proof takes them as given.
-/
def AddsKept (d : Domain) (p : Problem) (rel : Bool) : Prop :=
  ∀ o ∈ groundedOps d p rel, ∃ hf : OpFacts d p o,
    (∀ v l q0 s1 s2 : Name, hf.inst.schema = pickupA →
      hf.inst.args = [v, l, q0, s1, s2] → inAtom q0 v ∈ o.add) ∧
    (∀ v l q0 s1 s2 : Name, hf.inst.schema = dropA →
      hf.inst.args = [v, l, q0, s1, s2] → atAtom q0 l ∈ o.add)

/-- **Every operator the grounder builds is one of the three shapes.** -/
theorem schemaStep_of_ops (hp : Pinned d p) (rel : Bool) (hadds : AddsKept d p rel) :
    ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ → o.applicableA σ →
      SchemaStep (graphOf (ground d p rel)) (cfgOf (ground d p rel)) σ
        (o.applyA σ) := by
  intro o ho σ hinv happ
  obtain ⟨hf, hpick, hdrop⟩ := hadds o ho
  rcases instance_shape hp.domain hf.inst with
    ⟨v, l1, l2, hs, ha⟩ | ⟨v, l, q, s1, s2, hs, ha⟩ | ⟨v, l, q, s1, s2, hs, ha⟩
  · exact drive_step hp rel ho hf hs ha hinv happ
  · exact pickup_step hp rel ho hf (hpick v l q s1 s2 hs ha) hs ha hinv happ
  · exact drop_step hp rel ho hf (hdrop v l q s1 s2 hs ha) hs ha hinv happ

/-- With pruning off, the grounder keeps every add the schema names. -/
theorem adds_of_raw (hp : Pinned d p) : AddsKept d p false := by
  intro o ho
  obtain ⟨hfa⟩ := opFacts_raw_add d p (by rwa [groundedOps_false] at ho)
  refine ⟨hfa.toOpFacts, ?_, ?_⟩
  · intro v l q0 s1 s2 hs ha
    have heq : instAtom hfa.inst.schema.params hfa.inst.args (inV "?p" "?v")
        = inAtom q0 v := by rw [hs, ha]; rfl
    rw [← heq]
    refine hfa.addComplete (inV "?p" "?v") (by
      rw [hs]
      show inV "?p" "?v" ∈ [inV "?p" "?v", capacityV "?v" "?s1"]
      simp) ?_
    rw [heq]
    intro hc
    have hm : inAtom q0 v ∈ hfa.inst.pre := hfa.toOpFacts.subPre _ hc
    have hmem' : inAtom q0 v ∈
        hfa.inst.schema.pre.map (instAtom hfa.inst.schema.params hfa.inst.args) := hm
    have hlist : hfa.inst.schema.pre.map (instAtom hfa.inst.schema.params hfa.inst.args)
        = [atAtom v l, atAtom q0 l, capPred s1 s2, capacity v s2] := by
      rw [hs, ha]; rfl
    rw [hlist] at hmem'
    simp [inAtom, atAtom, capPred, capacity] at hmem'
  · intro v l q0 s1 s2 hs ha
    obtain ⟨a1, a2, a3, a4, a5, ha5, hw1, hw2, hw3, hw4, hw5⟩ :=
      hfa.inst.args_five (show hfa.inst.schema.params
        = [vehP, locP "?l", pkgP, sizeP "?s1", sizeP "?s2"] by rw [hs])
    rw [ha] at ha5
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ :
        v = a1 ∧ l = a2 ∧ q0 = a3 ∧ s1 = a4 ∧ s2 = a5 := by simpa using ha5
    have hqv : q0 ≠ v := fun hc =>
      (not_mem_vehicles hp false hw3) (hc ▸ mem_vehs (hp := hp) (rel := false) hw1)
    have heq : instAtom hfa.inst.schema.params hfa.inst.args (atV "?p" "?l")
        = atAtom q0 l := by rw [hs, ha]; rfl
    rw [← heq]
    refine hfa.addComplete (atV "?p" "?l") (by
      rw [hs]
      show atV "?p" "?l" ∈ [atV "?p" "?l", capacityV "?v" "?s2"]
      simp) ?_
    rw [heq]
    intro hc
    have hm : atAtom q0 l ∈ hfa.inst.pre := hfa.toOpFacts.subPre _ hc
    have hmem' : atAtom q0 l ∈
        hfa.inst.schema.pre.map (instAtom hfa.inst.schema.params hfa.inst.args) := hm
    have hlist : hfa.inst.schema.pre.map (instAtom hfa.inst.schema.params hfa.inst.args)
        = [atAtom v l, inAtom q0 v, capPred s1 s2, capacity v s1] := by
      rw [hs, ha]; rfl
    rw [hlist] at hmem'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem'
    rcases hmem' with h1 | h1 | h1 | h1
    · simp only [atAtom_eq] at h1
      exact hqv h1.1
    · simp [atAtom, inAtom] at h1
    · simp [atAtom, capPred] at h1
    · simp [atAtom, capacity] at h1


/-! ### The adds the relevance analysis keeps

A `pick-up` needs its `in` atom, and the `drop` that meets the goal reads that
atom, so closure puts it in the relevant set.  A `drop` needs its `at` atom, and
the `pick-up` that consumes it reads that one.  Each argument builds the other
schema's raw operator on the same arguments, which is legitimate because the two
schemas have the same parameters and the same static precondition.
-/

private theorem raw_load (hp : Pinned d p) (a : Action) (ha : a ∈ d.actions)
    (hparams : a.params = dropA.params)
    (hstatic : ∀ y ∈ a.pre, (staticPredicates d).contains y.pred = true →
      y = capPredV "?s1" "?s2")
    {v l q0 s1 s2 : Name}
    (hwt : List.Forall₂ (fun (pm : TypedName) (o : Name) =>
      WellTyped d (allObjects d p) pm.type o) dropA.params [v, l, q0, s1, s2])
    (hcap : capPred s1 s2 ∈ p.init) :
    mkOp a (a.pre.filter fun x => !(staticPredicates d).contains x.pred)
      #[v, l, q0, s1, s2] ∈ rawOps d p := by
  rw [← groundedOps_false]
  refine groundedOps_complete d p ha _ (by rw [hparams]; rfl)
    (by rw [hparams]; exact hp.loadTypes) (by rw [hparams]; exact hwt) ?_
  intro y hy hst
  have hy2 := hstatic y hy hst
  subst hy2
  show instAtom a.params (#[v, l, q0, s1, s2] : Array Name).toList
    (capPredV "?s1" "?s2") ∈ p.init
  rw [hparams]
  exact hcap

theorem adds_of_pruned (hp : Pinned d p) : AddsKept d p true := by
  intro o ho
  rcases relevance_cases (rawOps d p) p.goal.toArray with ⟨r, hclosed, hgoal, hrdef⟩ | hall
  · obtain ⟨hf, hpre, hkept⟩ := opFacts_pruned_add d p ho hclosed hrdef
    have hatDyn : (staticPredicates d).contains (atAtom "" "").pred = false := by
      simpa [atAtom] using at_dynamic hp.domain
    have hinDyn : (staticPredicates d).contains (inAtom "" "").pred = false := by
      simpa [inAtom] using in_dynamic hp.domain
    have hcapDyn : (staticPredicates d).contains (capacity "" "").pred = false := by
      simpa [capacity] using capacity_dynamic hp.domain
    refine ⟨hf, ?_, ?_⟩
    · -- `pick-up`: the `drop` that meets the goal reads the `in` atom
      intro v l q0 s1 s2 hs ha
      obtain ⟨hpreV, hpreQ, hadd, hdel⟩ := pickup_atoms hf.inst hs ha
      obtain ⟨a1, a2, a3, a4, a5, ha5, hw1, hw2, hw3, hw4, hw5⟩ :=
        hf.inst.args_five (show hf.inst.schema.params
          = [vehP, locP "?l", pkgP, sizeP "?s1", sizeP "?s2"] by rw [hs])
      rw [ha] at ha5
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ :
          v = a1 ∧ l = a2 ∧ q0 = a3 ∧ s1 = a4 ∧ s2 = a5 := by simpa using ha5
      have hqv : q0 ≠ v := fun hc =>
        (not_mem_vehicles hp true hw3) (hc ▸ mem_vehs (hp := hp) (rel := true) hw1)
      have hatRel : r.contains (atAtom q0 l) = true :=
        hpre _ (pre_mem_op hf hpreQ hatDyn)
      have hcap : capPred s1 s2 ∈ p.init := by
        have := hf.staticHeld (capPredV "?s1" "?s2") (by rw [hs]; simp [pickupA])
          hp.capPredStatic
        have heq : instAtom hf.inst.schema.params hf.inst.args (capPredV "?s1" "?s2")
            = capPred s1 s2 := by rw [hs, ha]; rfl
        rw [heq] at this
        simpa using this
      have hraw : mkOp dropA (dropA.pre.filter fun x =>
          !(staticPredicates d).contains x.pred) #[v, l, q0, s1, s2] ∈ rawOps d p := by
        refine raw_load hp dropA (by rw [hp.domain]; simp) rfl ?_ ?_ hcap
        · intro y hy hst
          rcases (by simpa [dropA] using hy :
            y = atV "?v" "?l" ∨ y = inV "?p" "?v" ∨ y = capPredV "?s1" "?s2"
              ∨ y = capacityV "?v" "?s1") with rfl | rfl | rfl | rfl
          · rw [show (atV "?v" "?l").pred = (atAtom "" "").pred from rfl, hatDyn] at hst
            exact absurd hst (by simp)
          · rw [show (inV "?p" "?v").pred = (inAtom "" "").pred from rfl, hinDyn] at hst
            exact absurd hst (by simp)
          · rfl
          · rw [show (capacityV "?v" "?s1").pred = (capacity "" "").pred from rfl,
              hcapDyn] at hst
            exact absurd hst (by simp)
        · have : hf.inst.schema.params = dropA.params := by rw [hs]
          rw [← this, ← ha]
          exact hf.inst.typed
      have hAddAt : atAtom q0 l ∈ (mkOp dropA (dropA.pre.filter fun x =>
          !(staticPredicates d).contains x.pred) #[v, l, q0, s1, s2]).add := by
        have heq : instAtom dropA.params (#[v, l, q0, s1, s2] : Array Name).toList
            (atV "?p" "?l") = atAtom q0 l := rfl
        rw [← heq]
        refine mem_mkOp_add dropA _ _ (by simp [dropA]) ?_
        intro z hz
        rcases (by simpa [dropA] using (List.mem_filter.mp hz).1 :
          z = atV "?v" "?l" ∨ z = inV "?p" "?v" ∨ z = capPredV "?s1" "?s2"
            ∨ z = capacityV "?v" "?s1") with rfl | rfl | rfl | rfl
        · show atAtom v l ≠ atAtom q0 l
          simp only [ne_eq, atAtom_eq, not_and]
          intro hc
          exact absurd hc (Ne.symm hqv)
        · show inAtom q0 v ≠ atAtom q0 l
          simp
        · show capPred s1 s2 ≠ atAtom q0 l
          simp [capPred, atAtom]
        · show capacity v s1 ≠ atAtom q0 l
          simp [capacity, atAtom]
      have htouch : (mkOp dropA (dropA.pre.filter fun x =>
          !(staticPredicates d).contains x.pred) #[v, l, q0, s1, s2]).touches r = true := by
        unfold AtomOp.touches
        have : (mkOp dropA (dropA.pre.filter fun x =>
            !(staticPredicates d).contains x.pred) #[v, l, q0, s1, s2]).add.any
            r.contains = true := by
          rw [← Array.any_toList]
          exact List.any_eq_true.mpr ⟨atAtom q0 l, by simpa using hAddAt, hatRel⟩
        rw [this]; rfl
      have hinRel : r.contains (inAtom q0 v) = true := by
        refine hclosed _ hraw htouch _ ?_
        have heq : instAtom dropA.params (#[v, l, q0, s1, s2] : Array Name).toList
            (inV "?p" "?v") = inAtom q0 v := rfl
        rw [← heq]
        refine mem_mkOp_pre dropA (dropA.pre.filter fun x =>
          !(staticPredicates d).contains x.pred) #[v, l, q0, s1, s2]
          (List.mem_filter.mpr ⟨by simp [dropA], ?_⟩)
        simp only [Bool.not_eq_true']
        exact hinDyn
      have heq2 : instAtom hf.inst.schema.params hf.inst.args (inV "?p" "?v")
          = inAtom q0 v := by rw [hs, ha]; rfl
      rw [← heq2]
      refine hkept (inV "?p" "?v") (by rw [hs]; simp [pickupA]) ?_ (by rw [heq2]; exact hinRel)
      rw [heq2]
      intro hc
      have hm : inAtom q0 v ∈ hf.inst.pre := hf.subPre _ hc
      have hmem' : inAtom q0 v ∈
          hf.inst.schema.pre.map (instAtom hf.inst.schema.params hf.inst.args) := hm
      have hlist : hf.inst.schema.pre.map (instAtom hf.inst.schema.params hf.inst.args)
          = [atAtom v l, atAtom q0 l, capPred s1 s2, capacity v s2] := by
        rw [hs, ha]; rfl
      rw [hlist] at hmem'
      simp [inAtom, atAtom, capPred, capacity] at hmem'
    · -- `drop`: the `pick-up` that consumes the package reads the `at` atom
      intro v l q0 s1 s2 hs ha
      obtain ⟨hpreV, hpreQ, hadd, hdel⟩ := drop_atoms hf.inst hs ha
      obtain ⟨a1, a2, a3, a4, a5, ha5, hw1, hw2, hw3, hw4, hw5⟩ :=
        hf.inst.args_five (show hf.inst.schema.params
          = [vehP, locP "?l", pkgP, sizeP "?s1", sizeP "?s2"] by rw [hs])
      rw [ha] at ha5
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ :
          v = a1 ∧ l = a2 ∧ q0 = a3 ∧ s1 = a4 ∧ s2 = a5 := by simpa using ha5
      have hqv : q0 ≠ v := fun hc =>
        (not_mem_vehicles hp true hw3) (hc ▸ mem_vehs (hp := hp) (rel := true) hw1)
      have hinRel : r.contains (inAtom q0 v) = true :=
        hpre _ (pre_mem_op hf hpreQ hinDyn)
      have hcap : capPred s1 s2 ∈ p.init := by
        have := hf.staticHeld (capPredV "?s1" "?s2") (by rw [hs]; simp [dropA])
          hp.capPredStatic
        have heq : instAtom hf.inst.schema.params hf.inst.args (capPredV "?s1" "?s2")
            = capPred s1 s2 := by rw [hs, ha]; rfl
        rw [heq] at this
        simpa using this
      have hraw : mkOp pickupA (pickupA.pre.filter fun x =>
          !(staticPredicates d).contains x.pred) #[v, l, q0, s1, s2] ∈ rawOps d p := by
        refine raw_load hp pickupA (by rw [hp.domain]; simp) rfl ?_ ?_ hcap
        · intro y hy hst
          rcases (by simpa [pickupA] using hy :
            y = atV "?v" "?l" ∨ y = atV "?p" "?l" ∨ y = capPredV "?s1" "?s2"
              ∨ y = capacityV "?v" "?s2") with rfl | rfl | rfl | rfl
          · rw [show (atV "?v" "?l").pred = (atAtom "" "").pred from rfl, hatDyn] at hst
            exact absurd hst (by simp)
          · rw [show (atV "?p" "?l").pred = (atAtom "" "").pred from rfl, hatDyn] at hst
            exact absurd hst (by simp)
          · rfl
          · rw [show (capacityV "?v" "?s2").pred = (capacity "" "").pred from rfl,
              hcapDyn] at hst
            exact absurd hst (by simp)
        · have hpar : hf.inst.schema.params = dropA.params := by rw [hs]
          rw [← hpar, ← ha]
          exact hf.inst.typed
      have hAddIn : inAtom q0 v ∈ (mkOp pickupA (pickupA.pre.filter fun x =>
          !(staticPredicates d).contains x.pred) #[v, l, q0, s1, s2]).add := by
        have heq : instAtom pickupA.params (#[v, l, q0, s1, s2] : Array Name).toList
            (inV "?p" "?v") = inAtom q0 v := rfl
        rw [← heq]
        refine mem_mkOp_add pickupA _ _ (by simp [pickupA]) ?_
        intro z hz
        rcases (by simpa [pickupA] using (List.mem_filter.mp hz).1 :
          z = atV "?v" "?l" ∨ z = atV "?p" "?l" ∨ z = capPredV "?s1" "?s2"
            ∨ z = capacityV "?v" "?s2") with rfl | rfl | rfl | rfl
        · show atAtom v l ≠ inAtom q0 v
          simp
        · show atAtom q0 l ≠ inAtom q0 v
          simp
        · show capPred s1 s2 ≠ inAtom q0 v
          simp [capPred, inAtom]
        · show capacity v s2 ≠ inAtom q0 v
          simp [capacity, inAtom]
      have htouch : (mkOp pickupA (pickupA.pre.filter fun x =>
          !(staticPredicates d).contains x.pred) #[v, l, q0, s1, s2]).touches r = true := by
        unfold AtomOp.touches
        have : (mkOp pickupA (pickupA.pre.filter fun x =>
            !(staticPredicates d).contains x.pred) #[v, l, q0, s1, s2]).add.any
            r.contains = true := by
          rw [← Array.any_toList]
          exact List.any_eq_true.mpr ⟨inAtom q0 v, by simpa using hAddIn, hinRel⟩
        rw [this]; rfl
      have hatRel : r.contains (atAtom q0 l) = true := by
        refine hclosed _ hraw htouch _ ?_
        have heq : instAtom pickupA.params (#[v, l, q0, s1, s2] : Array Name).toList
            (atV "?p" "?l") = atAtom q0 l := rfl
        rw [← heq]
        refine mem_mkOp_pre pickupA (pickupA.pre.filter fun x =>
          !(staticPredicates d).contains x.pred) #[v, l, q0, s1, s2]
          (List.mem_filter.mpr ⟨by simp [pickupA], ?_⟩)
        simp only [Bool.not_eq_true']
        exact hatDyn
      have heq2 : instAtom hf.inst.schema.params hf.inst.args (atV "?p" "?l")
          = atAtom q0 l := by rw [hs, ha]; rfl
      rw [← heq2]
      refine hkept (atV "?p" "?l") (by rw [hs]; simp [dropA]) ?_ (by rw [heq2]; exact hatRel)
      rw [heq2]
      intro hc
      have hm : atAtom q0 l ∈ hf.inst.pre := hf.subPre _ hc
      have hmem' : atAtom q0 l ∈
          hf.inst.schema.pre.map (instAtom hf.inst.schema.params hf.inst.args) := hm
      have hlist : hf.inst.schema.pre.map (instAtom hf.inst.schema.params hf.inst.args)
          = [atAtom v l, inAtom q0 v, capPred s1 s2, capacity v s1] := by
        rw [hs, ha]; rfl
      rw [hlist] at hmem'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem'
      rcases hmem' with h1 | h1 | h1 | h1
      · simp only [atAtom_eq] at h1
        exact hqv h1.1
      · simp [atAtom, inAtom] at h1
      · simp [atAtom, capPred] at h1
      · simp [atAtom, capacity] at h1
  · refine adds_of_raw hp o ?_
    rw [groundedOps_true, hall] at ho
    rwa [groundedOps_false]


/-! ### Assembling the shape -/

/-- Every operator costs something. -/
theorem cost_pos' (hp : Pinned d p) (rel : Bool) :
    ∀ o ∈ groundedOps d p rel, 0 < o.cost := cost_pos hp rel

/--
**Transport's improved heuristic is admissible on the task the grounder builds**,
with nothing about the heuristic assumed.

`AddsKept` is the one thing the relevance analysis can take away: a `pick-up`
whose `in` atom were dropped would leave the package neither on the ground nor
carried, and the handling count would fall by two across one action.
-/
theorem improved_admissible (hp : Pinned d p) (rel : Bool)
    (hadds : AddsKept d p rel)
    (hnd : (cfgOf (ground d p rel)).packages.toList.Nodup) :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel))
      (ExampleHeuristics.Transport.improved (ground d p rel)).eval :=
  improved_admissible_of_shape d p rel Inv
    (ground_wf d p rel (cost_pos hp rel)) (cost_pos hp rel) hnd
    (by rw [cfg_dist]; exact Distances.sound_of _)
    (schemaStep_of_ops hp rel hadds) (initInv_of_check hp.initCheck)
    (fun o ho σ hinv happ => by
      obtain ⟨hf⟩ := opFacts_ground d p rel ho
      exact inv_preserved hp.domain hf hinv happ)

/-- And `AddsKept` holds either way, so the domain is closed for both. -/
theorem addsKept (hp : Pinned d p) (rel : Bool) : AddsKept d p rel := by
  cases rel with
  | false => exact adds_of_raw hp
  | true => exact adds_of_pruned hp

/--
**The package table has no duplicate entry.**

Each entry stores the fact of the goal atom it came from, and the problem's goal
names each atom once, so two entries agree only if they came from the same goal
atom.  `Pinned.goalNodup` is what supplies that.
-/
theorem packages_nodup (hp : Pinned d p) (rel : Bool) :
    (cfgOf (ground d p rel)).packages.toList.Nodup := by
  show ((ExampleHeuristics.Transport.compile (ground d p rel)).packages.map
    (packageOf (ground d p rel))).toList.Nodup
  have hpk : (ExampleHeuristics.Transport.compile (ground d p rel)).packages
      = ((ground d p rel).goalAtoms.zipIdx).filterMap
        (ExampleHeuristics.Transport.packageEntry (ground d p rel)
          (graphOf (ground d p rel))
          (ExampleHeuristics.Transport.atOf ((ground d p rel).factsWith "at")
            (graphOf (ground d p rel)))
          (ExampleHeuristics.Transport.inOf ((ground d p rel).factsWith "in")
            (vehicles (ground d p rel)))) := rfl
  rw [hpk, Array.map_filterMap]
  refine goalTable_nodup d p rel hp.goalNodup _ (·.goalAtom) ?_
  intro x hx b hb
  obtain ⟨hlt, -⟩ := List.mem_zipIdx' hx
  have hi : x.2 < (taskOf d p rel).goalAtoms.size := by simpa using hlt
  obtain ⟨y, hy, hval⟩ := Option.map_eq_some_iff.mp hb
  have hgoal : y.goalFact = (ground d p rel).goal.getD x.2 0 := by
    unfold ExampleHeuristics.Transport.packageEntry at hy
    by_cases hpred : (x.1.pred == "at") = true
    · rcases hargs : x.1.args with _ | ⟨q, rest⟩
      · simp only [hpred, hargs] at hy; simp at hy
      · cases rest with
        | nil => simp only [hpred, hargs] at hy; simp at hy
        | cons g rest' =>
            cases rest' with
            | cons _ _ => simp only [hpred, hargs] at hy; simp at hy
            | nil =>
                simp only [hpred, hargs] at hy
                rcases hf : (graphOf (ground d p rel)).find? g with _ | gl
                · rw [hf] at hy; simp at hy
                · rw [hf] at hy
                  simp only [Option.map_some, Option.some.injEq] at hy
                  rw [← hy]
    · simp only [Bool.not_eq_true] at hpred
      simp only [hpred] at hy
      simp at hy
  rw [← hval]
  show atomOf (ground d p rel) y.goalFact = _
  rw [hgoal]
  exact atomOf_goal_getD d p rel hi

theorem improved_admissible' (hp : Pinned d p) (rel : Bool) :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel))
      (ExampleHeuristics.Transport.improved (ground d p rel)).eval :=
  improved_admissible hp rel (addsKept hp rel) (packages_nodup hp rel)

/-- Goal awareness for the shipped heuristic, from the record alone. -/
theorem improved_goalAware_of_pinned (hp : Pinned d p) (rel : Bool) :
    (ground d p rel).GoalAwareOn (Reachable (ground d p rel))
      (ExampleHeuristics.Transport.improved (ground d p rel)).eval :=
  improved_goalAware_of_shape d p rel Inv
    (ground_wf d p rel (cost_pos hp rel)) (cost_pos hp rel)
    (initInv_of_check hp.initCheck)
    (fun o ho σ hinv happ => by
      obtain ⟨hf⟩ := opFacts_ground d p rel ho
      exact inv_preserved hp.domain hf hinv happ)

/-- And consistency. -/
theorem improved_consistent_of_pinned (hp : Pinned d p) (rel : Bool) :
    (ground d p rel).ConsistentOn (Reachable (ground d p rel))
      (ExampleHeuristics.Transport.improved (ground d p rel)).eval :=
  improved_consistent_of_shape d p rel Inv
    (ground_wf d p rel (cost_pos hp rel)) (cost_pos hp rel) (packages_nodup hp rel)
    (by rw [cfg_dist]; exact Distances.sound_of _)
    (schemaStep_of_ops hp rel (addsKept hp rel))
    (initInv_of_check hp.initCheck)
    (fun o ho σ hinv happ => by
      obtain ⟨hf⟩ := opFacts_ground d p rel ho
      exact inv_preserved hp.domain hf hinv happ)

/-! ### The executable certificate -/

theorem certificate_sound {d : Domain} {p : Problem}
    (hv : Validated d p)
    (h : ExampleHeuristics.Transport.Certificate.certified d p = true) :
    Pinned d p := by
  simp only [ExampleHeuristics.Transport.Certificate.certified,
    ExampleHeuristics.Transport.Certificate.conditions, Certificate.passes,
    List.all_cons, List.all_nil, Bool.and_eq_true] at h
  rcases h with
    ⟨hactions, hloc, hveh, hgoalVeh, hroad, hgoalRoad, hgoalUnique, hgoalNodup,
      hvehPkg, hinit, hloadTypes, hcapPred, -⟩
  have hpairs : ∀ pred : Pddl.Name,
      Planner.Certificate.initPairs p pred = initPairs p pred := fun _ => rfl
  refine
    { domain := by simpa using hactions
      validated := hv
      locType := Certificate.exactType_sound hloc
      vehType := Certificate.exactType_sound hveh
      goalNotVeh := ?_
      roadStatic := by simpa using hroad
      goalNotRoad := ?_
      goalObjUnique := ?_
      goalNodup := of_decide_eq_true hgoalNodup
      vehNotPkg := ?_
      initCheck := ?_
      loadTypes := ?_
      capPredStatic := by simpa using hcapPred }
  · rw [ExampleHeuristics.Transport.Certificate.goalNotVehicle,
      List.all_eq_true] at hgoalVeh
    intro a ha hpred o ho hname
    have hb := hgoalVeh a ha
    simp only [hpred, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at hb
    rcases hb with hb | hb
    · exact absurd trivial hb
    · have := hb o ho
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at this
      rcases this with h1 | h1
      · exact absurd hname h1
      · exact h1
  · rw [List.all_eq_true] at hgoalRoad
    intro a ha
    simpa using hgoalRoad a ha
  · rw [ExampleHeuristics.Transport.Certificate.goalObjUnique,
      List.all_eq_true] at hgoalUnique
    intro a ha b hb hpa hpb hargs
    have h1 := hgoalUnique a ha
    rw [List.all_eq_true] at h1
    have h2 := h1 b hb
    simp only [hpa, hpb, hargs, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true,
      beq_iff_eq, beq_self_eq_true, and_self, Bool.true_and] at h2
    simpa using h2
  · rw [ExampleHeuristics.Transport.Certificate.vehNotPackage,
      List.all_eq_true] at hvehPkg
    intro o ho hty
    have hb := hvehPkg o ho
    simp only [hty, Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at hb
    rcases hb with hb | hb
    · exact absurd trivial hb
    · rw [hty]; exact hb
  · rw [ExampleHeuristics.Transport.Certificate.initInvCheck] at hinit
    simpa [hpairs, initInvCheck, atPairs, inPairs, initPairs] using hinit
  · simpa using hloadTypes

theorem improved_goalAware_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool)
    (h : ExampleHeuristics.Transport.Certificate.certified d p = true) :
    (ground d p rel).GoalAwareOn (Reachable (ground d p rel))
      (ExampleHeuristics.Transport.improved (ground d p rel)).eval :=
  improved_goalAware_of_pinned (certificate_sound hv h) rel

theorem improved_consistent_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool)
    (h : ExampleHeuristics.Transport.Certificate.certified d p = true) :
    (ground d p rel).ConsistentOn (Reachable (ground d p rel))
      (ExampleHeuristics.Transport.improved (ground d p rel)).eval :=
  improved_consistent_of_pinned (certificate_sound hv h) rel

theorem improved_proof_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool) :
    ImprovedProof d p rel
      (ExampleHeuristics.Transport.Certificate.certified d p)
      (ExampleHeuristics.Transport.improved (ground d p rel)) :=
  { goalAware := improved_goalAware_of_certificate hv rel
    consistent := improved_consistent_of_certificate hv rel }

theorem improved_admissible_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool)
    (h : ExampleHeuristics.Transport.Certificate.certified d p = true) :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel))
      (ExampleHeuristics.Transport.improved (ground d p rel)).eval :=
  (improved_proof_of_certificate hv rel).admissible h

end Planner.Lifted.Transport
