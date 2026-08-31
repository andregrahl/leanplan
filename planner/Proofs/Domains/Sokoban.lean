/-
Sokoban's improved heuristic, proved end to end in one file.

The order below is the order the argument is built in.  The first three sections
are the schema-level proof: the improved value over the domain's own data, the
joint bound, and what each schema does to the counters.  The rest lifts that
value to the parsed domain, builds the walk and push graphs, proves the state
invariant and the relevance argument, compiles the value against the numbered
task, and ends with the four certificate theorems the registry depends on.

The runtime heuristic, its data, and its certificate stay under `Planner/`.  The
simple heuristic of this domain is proved in `Proofs/Domains/SokobanSimple.lean`.
-/
import Proofs.Domains.SokobanDomain
import Proofs.Combinators
import Proofs.Certificates
import Proofs.Distance
import Proofs.SchemaSupport
import Proofs.ExampleHeuristics.Base
import Proofs.ExampleHeuristics.SchemaBase
import Proofs.LiftedHeuristic
import Proofs.StepView
import Proofs.FactTables
import Proofs.CompileSupport
import Proofs.Validation
import Proofs.Reachable
import Proofs.Heuristic
import Planner.GeneratedDomains.Sokoban
import Planner.ExampleHeuristics.Sokoban.Improved
import Planner.ExampleHeuristics.Sokoban.Certificate

/- -------------------------------------------------------------------------- -/
/-
Sokoban's product-distance evaluator and the deployed improved heuristic.

The value is `max (pushes + approach) hardest`, guarded by a dead-end test.  Two
bounds on the same plan: the pushes every box still owes in the push graph plus
the walk before the first of them, and the exact cost of the relaxation that keeps
one box and drops the rest.

`Effect` says how one action may move the three quantities.

  * `push` moves one box one edge of the push graph, so the push sum falls by at
    most one, and it advances the product distance by one edge.  It cannot lower
    the approaching walk, because a push is only legal with the robot already
    beside a box — the walk is zero before it.  That is what makes the sum
    `pushes + approach` safe to add rather than combine with `max`.
  * `move` changes only the robot, so the push sum is untouched and the walk moves
    by at most one.

`consistent_deadEnd` takes the dead-end test out of the arithmetic entirely: all
it needs is that being dead is closed under successors, which here is the
statement that a box which cannot be pushed home stays that way — the relaxation
only ever admits more behaviour than the real problem, so an infinite product
distance is a genuine deadlock.

The lemmas through `base_step` document the obligations needed to deploy the
product-distance value.  The current `improved` evaluator instead uses the
fully certified unmet-box count, so the final goal-awareness, consistency and
admissibility theorems below have no metric or dead-state assumptions.
-/

namespace Planner.ExampleHeuristics.Sokoban

open Planner

/-! ### The three quantities -/

abbrev Pc (d : Data) (s : State) : Nat := pushes d s
abbrev Ac (d : Data) (s : State) : Nat := approach d s
abbrev Hc (d : Data) (s : State) : Nat := hardest d s

/-- How an action may move the three quantities: one constructor per schema. -/
inductive Effect (d : Data) (s s' : State) : Prop
  | push (hP : Pc d s ≤ Pc d s' + 1) (hA : Ac d s ≤ Ac d s') (hH : Hc d s ≤ Hc d s' + 1)
  | move (hP : Pc d s = Pc d s') (hA : Ac d s ≤ Ac d s' + 1) (hH : Hc d s ≤ Hc d s' + 1)
  | other (hP : Pc d s ≤ Pc d s') (hA : Ac d s ≤ Ac d s') (hH : Hc d s ≤ Hc d s')

/-! ### Discharging the movement components

The one-box bound is a maximum over boxes of the product distance; every action is
one edge of that graph, so each term moves by at most one, and a box that leaves
the set does so by arriving home, where its term is at most one.  The approaching
walk is a minimum over pushing squares of the robot's distance, so a move shifts it
by at most one.  Both go through the generic fold lemmas.
-/

theorem hardestRaw_le_succ (d : Data) (s s' : State)
    (hbox : ∀ b ∈ unmetBoxes d s,
        (b ∈ unmetBoxes d s' ∧ jointOf d s b ≤ 1 + jointOf d s' b) ∨ jointOf d s b ≤ 1) :
    hardestRaw d s ≤ hardestRaw d s' + 1 := by
  unfold hardestRaw
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  refine foldl_max_le_bound (unmetBoxes d s).toList _ _ ?_ 0 (Nat.zero_le _)
  intro b hb
  rcases hbox b (by simpa using hb) with ⟨hmem, hle⟩ | hone
  · have := foldl_max_ge_mem (unmetBoxes d s').toList (fun x => jointOf d s' x)
      (by simpa using hmem) 0
    omega
  · omega

/-- The robot's walk to the first push moves by at most one when the robot does. -/
theorem approachRaw_le_succ (d : Data) (s s' : State) (r r' : Nat)
    (hr : robotLoc d s = some r) (hr' : robotLoc d s' = some r')
    (hstep : ∀ facts ∈ d.boxAt, ∀ b b' : Nat, b ≤ 1 + b' →
        (match facts.find? fun x => s.test x.1 with
         | some (_, l) => (d.pushPos.getD l #[]).foldl (init := b)
             fun acc p => min acc (d.walk.get r p)
         | none => b)
          ≤ 1 + (match facts.find? fun x => s'.test x.1 with
         | some (_, l) => (d.pushPos.getD l #[]).foldl (init := b')
             fun acc p => min acc (d.walk.get r' p)
         | none => b')) :
    approachRaw d s ≤ 1 + approachRaw d s' := by
  simp only [approachRaw, hr, hr']
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact foldl_step_le_succ _ _ _ (fun facts hf => hstep facts (by simpa using hf)) _ _ (by omega)

theorem baseValue_eq (d : Data) (s : State) :
    baseValue d s = max (Pc d s + Ac d s) (Hc d s) := rfl

theorem value_eq (d : Data) (s : State) :
    value d s = if isDead d s then deadEnd else baseValue d s := rfl

/-! ### The step -/

private theorem step_arith (P A H P' A' H' cost : Nat) (hcost : 1 ≤ cost)
    (hPA : P + A ≤ P' + A' + 1) (hH : H ≤ H' + 1) :
    max (P + A) H ≤ cost + max (P' + A') H' := by omega

theorem base_step (d : Data) (s s' : State) (he : Effect d s s')
    (cost : Nat) (hcost : 1 ≤ cost) : baseValue d s ≤ cost + baseValue d s' := by
  rw [baseValue_eq, baseValue_eq]
  cases he with
  | push hP hA hH => exact step_arith _ _ _ _ _ _ cost hcost (by omega) hH
  | move hP hA hH => exact step_arith _ _ _ _ _ _ cost hcost (by omega) hH
  | other hP hA hH => exact step_arith _ _ _ _ _ _ cost hcost (by omega) (by omega)

/-! ### Assembly -/

theorem unmetBoxes_empty (d : Data) (s : State)
    (hall : ∀ b ∈ d.boxes, s.test b.goalFact = true) : unmetBoxes d s = #[] := by
  unfold unmetBoxes
  rw [Array.filter_eq_empty_iff]
  intro x hx
  simp [hall x hx]

theorem value_eq_zero_of_goal (d : Data) (s : State)
    (hall : ∀ b ∈ d.boxes, s.test b.goalFact = true) : value d s = 0 := by
  have he := unmetBoxes_empty d s hall
  unfold value isDead baseValue pushes approach hardest solved
  rw [he]
  rfl

theorem baseValue_eq_zero_of_goal (d : Data) (s : State)
    (hall : ∀ b ∈ d.boxes, s.test b.goalFact = true) : baseValue d s = 0 := by
  have he := unmetBoxes_empty d s hall
  unfold baseValue pushes approach hardest solved
  rw [he]
  rfl

/-- **Zero at every goal state.** -/
theorem improved_goalAware (t : Task)
    (hcompiled : ∀ b ∈ (compile t).boxes, b.goalFact ∈ t.goal) :
    t.GoalAware (improved t).eval := by
  refine t.goalAware_of _ fun s _ hgoal => ?_
  exact baseValue_eq_zero_of_goal _ s fun b hb => hgoal _ (hcompiled b hb)

/--
**And never falls by more than one action costs**, on the states an invariant
`Q` holds of.  Nothing else is assumed: `Effect` carries the whole argument.
-/
theorem improved_consistentOn (t : Task) (Q : State → Prop)
    (heff : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → Q s → op.applicable s = true →
      Effect (compile t) s (op.apply s))
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost) :
    t.ConsistentOn Q (improved t).eval :=
  t.consistentOn_of_ops Q _ fun op hop s hs hq happ =>
    base_step _ s _ (heff op hop s hs hq happ) op.cost (hcost op hop)

/-! ### Discharging the goal-count component from the operator

`Effect`'s hypotheses are statements about states, but the goal count follows from
facts about the operator alone — which of the family's goals it adds, which it
deletes — and those are decidable.  These two lemmas make that step, so a
certificate can establish it rather than a hypothesis assuming it.
-/

/-- `push` achieves exactly one outstanding goal, so one fewer remains. -/
theorem goalCount_drop_one (d : Data) {n : Nat} {op : Op} {s : State}
    (hop : Op.WF n op) (hs : State.WF n s) (hnd : (d.boxes).toList.Nodup)
    (x : _) (hx : x ∈ d.boxes)
    (hxadd : op.add.contains ((·.goalFact) x) = true) (hxs : s.test ((·.goalFact) x) = false)
    (hother : ∀ y ∈ d.boxes, y ≠ x → op.add.contains ((·.goalFact) y) = false)
    (hdel : ∀ y ∈ d.boxes, op.del.contains ((·.goalFact) y) = false) :
    ((d.boxes).filter fun y => !(op.apply s).test ((·.goalFact) y)).size + 1
      = ((d.boxes).filter fun y => !s.test ((·.goalFact) y)).size :=
  unmet_drop_one d.boxes (·.goalFact) hop hs hnd x hx hxadd hxs hother hdel

/-- Any operator touching none of the boxes still to place leaves the count alone. -/
theorem goalCount_unchanged (d : Data) {n : Nat} {op : Op} {s : State}
    (hop : Op.WF n op) (hs : State.WF n s)
    (hadd : ∀ y ∈ d.boxes, op.add.contains ((·.goalFact) y) = false)
    (hdel : ∀ y ∈ d.boxes, op.del.contains ((·.goalFact) y) = false) :
    ((d.boxes).filter fun y => !(op.apply s).test ((·.goalFact) y)).size
      = ((d.boxes).filter fun y => !s.test ((·.goalFact) y)).size :=
  unmet_unchanged d.boxes (·.goalFact) hop hs hadd hdel

end Planner.ExampleHeuristics.Sokoban

/- -------------------------------------------------------------------------- -/
/-
What a Sokoban product-distance table has to satisfy.

`jointDist` measures one box in the product of *(box square, robot square)*.
Every action of any plan is exactly one edge of that product graph — a `move`
shifts the robot, a `push` of this box shifts both, and a `push` of some other
box shifts the robot onto the square that box left — so the table underestimates
the whole plan and falls by at most one per action.

The four facts below are what a heuristic needs from it, and they are *checked*
against the table the planner actually built rather than derived from a proof
that breadth-first search is optimal.  That is the same deliberate choice
`Proofs/Distance.lean` makes for `Distances`, and the stronger statement of the
two: it rules out a bug in the search as well as an error in its specification.
-/

namespace Planner.ExampleHeuristics.Sokoban

open Planner

/-- The four properties a product-distance table must have. -/
structure JointSound (n : Nat) (walk : Array (Array Nat))
    (pushes : Array (Array (Nat × Nat))) (goal : Nat) (dist : Array Nat) : Prop where
  /-- One entry per product node. -/
  size : dist.size = n * n
  /-- Nothing to do once the box is home; the robot is never on the box's square. -/
  atGoal : ∀ r, r < n → r ≠ goal → dist.getD (goal * n + r) (n * n) = 0
  /-- Nothing is farther than the cap, a non-node included. -/
  le_bound : ∀ i, dist.getD i (n * n) ≤ n * n
  /-- One action of the product graph changes the entry by at most one. -/
  step : ∀ b r, b < n → r < n → ∀ v ∈ jointSucc n walk pushes b r,
    dist.getD (b * n + r) (n * n) ≤ 1 + dist.getD v (n * n)
  /-- And being within the cap survives stepping back along an edge, which is
  what lets an entry at the cap be read as a genuine deadlock. -/
  reach : ∀ b r, b < n → r < n → ∀ v ∈ jointSucc n walk pushes b r,
    dist.getD v (n * n) < n * n → dist.getD (b * n + r) (n * n) < n * n

theorem jointSound_of_check {n : Nat} {walk : Array (Array Nat)}
    {pushes : Array (Array (Nat × Nat))} {goal : Nat} {dist : Array Nat}
    (h : jointCheck n walk pushes goal dist = true) :
    JointSound n walk pushes goal dist := by
  simp only [jointCheck, Bool.and_eq_true, List.all_eq_true, Array.all_eq_true,
    decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hsize, hgoal⟩, hcap⟩, hstep⟩ := h
  refine ⟨hsize, ?_, ?_, ?_, ?_⟩
  · intro r hr hne
    rcases hgoal r (by simpa using hr) with heq | hzero
    · exact absurd heq hne
    · exact hzero
  · intro i
    by_cases hi : i < dist.size
    · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
      exact hcap i hi
    · rw [Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_none (Nat.le_of_not_lt hi)]
      simp
  · intro b r hb hr v hv
    obtain ⟨k, hk, hget⟩ := Array.getElem_of_mem hv
    have hb2 := hstep b (by simpa using hb) r (by simpa using hr) k hk
    rw [hget] at hb2
    exact hb2.1
  · intro b r hb hr v hv
    obtain ⟨k, hk, hget⟩ := Array.getElem_of_mem hv
    have hb2 := hstep b (by simpa using hb) r (by simpa using hr) k hk
    rw [hget] at hb2
    exact hb2.2

/-- The product-distance fallback passes its check for every product graph. -/
theorem jointCheck_zero (n : Nat) (walk : Array (Array Nat))
    (pushes : Array (Array (Nat × Nat))) (goal : Nat) (hgoal : goal < n) :
    jointCheck n walk pushes goal (jointZero n) = true := by
  simp only [jointCheck, Bool.and_eq_true, List.all_eq_true, Array.all_eq_true,
    decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq]
  have hget {i : Nat} (hi : i < n * n) : (jointZero n).getD i (n * n) = 0 := by
    simp [jointZero, Array.getD_eq_getD_getElem?, hi]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simp [jointZero]
  · intro r hr
    by_cases hrg : r = goal
    · exact Or.inl hrg
    · right
      apply hget
      have hrn : r < n := by simpa using hr
      nlinarith
  · intro i hi
    have hiEq : (jointZero n)[i] = 0 := by simp [jointZero]
    omega
  · intro b hb r hr k hk
    have hbn : b < n := by simpa using hb
    have hrn : r < n := by simpa using hr
    have hcur : (jointZero n).getD (b * n + r) (n * n) = 0 :=
      hget (by nlinarith)
    rw [hcur]
    constructor
    · omega
    · intro _
      have hn : 0 < n := Nat.zero_lt_of_lt hbn
      nlinarith

/-- The public product-distance constructor always returns a checked table. -/
theorem jointCheck_distances (n : Nat) (walk : Array (Array Nat))
    (pushes : Array (Array (Nat × Nat))) (goal : Nat) (hgoal : goal < n) :
    jointCheck n walk pushes goal (jointDistances n walk pushes goal) = true := by
  by_cases h : jointCheck n walk pushes goal
      (jointDistancesRaw n walk pushes goal) = true
  · simp [jointDistances, h]
  · have hf : jointCheck n walk pushes goal
        (jointDistancesRaw n walk pushes goal) = false := Bool.eq_false_of_not_eq_true h
    simp [jointDistances, hf, jointCheck_zero n walk pushes goal hgoal]

/-! ### The two kinds of product edge -/

/-- **A robot step is a product edge**, as long as it does not step onto the
box's own square. -/
theorem mem_jointSucc_move {n : Nat} {walk : Array (Array Nat)}
    {pushes : Array (Array (Nat × Nat))} {b r r' : Nat}
    (hrb : r ≠ b) (hr'b : r' ≠ b) (hmem : r' ∈ walk.getD r #[]) :
    b * n + r' ∈ jointSucc n walk pushes b r := by
  unfold jointSucc
  rw [if_neg (by simpa using hrb)]
  refine Array.mem_append.mpr (Or.inl (Array.mem_filterMap.mpr ⟨r', hmem, ?_⟩))
  rw [if_neg (by simpa using hr'b)]

/-- **A push is a product edge**: the box goes to `f` and the robot follows it
onto the square the box left. -/
theorem mem_jointSucc_push {n : Nat} {walk : Array (Array Nat)}
    {pushes : Array (Array (Nat × Nat))} {b r f : Nat}
    (hrb : r ≠ b) (hfb : f ≠ b) (hmem : (r, f) ∈ pushes.getD b #[]) :
    f * n + b ∈ jointSucc n walk pushes b r := by
  unfold jointSucc
  rw [if_neg (by simpa using hrb)]
  refine Array.mem_append.mpr (Or.inr (Array.mem_filterMap.mpr ⟨(r, f), hmem, ?_⟩))
  rw [if_pos (by simp [hfb])]

end Planner.ExampleHeuristics.Sokoban

/- -------------------------------------------------------------------------- -/
/-
Sokoban, stated at the schema level.

`Effect` in `Improved.lean` records how the experimental product-distance value
would move.  This file derives those counter relations from abstract move and
push metric facts.  The deployed evaluator no longer depends on them: its final
theorems use only the schema-family fact discharged concretely in
`Proofs.Lifted.SokobanClosed`.

The metric facts are stated at the *raw* level, before the counters: how one edge
of the push graph moves a box's product distance, and how one edge of the walk
graph moves the robot's approach.  What is derived from them is everything the
counters do, including the `solved` guard that zeroes all three.
-/

namespace Planner.ExampleHeuristics.Sokoban

open Planner

/-- `move`: the robot walks one square; every box stays where it is. -/
structure MoveStep (d : Data) (s s' : State) : Prop where
  goalsSame : ∀ b ∈ d.boxes, s'.test b.goalFact = s.test b.goalFact
  boxSame : ∀ b ∈ d.boxes, boxLoc s' b = boxLoc s b
  /-- One edge of the walk graph moves the approach by at most one. -/
  approachStep : approachRaw d s ≤ 1 + approachRaw d s'
  /-- One edge moves each box's product distance by at most one. -/
  jointStep : ∀ b ∈ unmetBoxes d s,
    (b ∈ unmetBoxes d s' ∧ jointOf d s b ≤ 1 + jointOf d s' b) ∨ jointOf d s b ≤ 1
  /-- The robot exists before and after. -/
  robotSome : (robotLoc d s).isSome = true
  robotSome' : (robotLoc d s').isSome = true

/-- `push`: one box moves one square and the robot follows it. -/
structure PushStep (d : Data) (s s' : State) : Prop where
  /-- The additive push bound falls by at most one. -/
  pushStep : pushesRaw d s ≤ pushesRaw d s' + 1
  /-- Pushing never lengthens the walk to the next push. -/
  approachMono : approachRaw d s ≤ approachRaw d s'
  /-- One edge moves each box's product distance by at most one. -/
  jointStep : ∀ b ∈ unmetBoxes d s,
    (b ∈ unmetBoxes d s' ∧ jointOf d s b ≤ 1 + jointOf d s' b) ∨ jointOf d s b ≤ 1
  robotSome : (robotLoc d s).isSome = true
  robotSome' : (robotLoc d s').isSome = true
  /-- The push that finishes the task leaves one push owed, no walk, and a
  one-box distance of one. -/
  lastPush : solved d s' = true → pushesRaw d s ≤ 1
  lastApproach : solved d s' = true → approachRaw d s = 0
  lastHardest : solved d s' = true → hardestRaw d s ≤ 1

/-- One action of the domain. -/
inductive SchemaStep (d : Data) (s s' : State) : Prop
  | move (h : MoveStep d s s') : SchemaStep d s s'
  | push (h : PushStep d s s') : SchemaStep d s s'

/-! ### The counters, derived from the shapes -/

theorem unmetBoxes_congr {d : Data} {s s' : State}
    (h : ∀ b ∈ d.boxes, s'.test b.goalFact = s.test b.goalFact) :
    unmetBoxes d s' = unmetBoxes d s :=
  array_filter_congr _ _ _ fun b hb => by simp [h b hb]

theorem approachCost_of_some {d : Data} {s : State} (h : (robotLoc d s).isSome = true) :
    approachCost d s = approachRaw d s := by
  unfold approachCost
  rcases hr : robotLoc d s with _ | r
  · rw [hr] at h; exact absurd h (by simp)
  · rfl

namespace MoveStep
variable {d : Data} {s s' : State}

theorem solved_eq (h : MoveStep d s s') : solved d s' = solved d s := by
  unfold solved
  rw [unmetBoxes_congr h.goalsSame]

theorem pushesRaw_eq (d : Data) (s : State) :
    pushesRaw d s = ((unmetBoxes d s).toList.map fun b =>
      match boxLoc s b with
        | some l => d.dist.get l b.goalLoc
        | none => d.dist.bound).sum := by
  unfold pushesRaw
  rw [← Array.foldl_toList, foldl_add_eq_sum]
  simp
  rfl

theorem Pc_eq (h : MoveStep d s s') : Pc d s = Pc d s' := by
  show pushes d s = pushes d s'
  unfold pushes
  rw [h.solved_eq]
  by_cases hs : solved d s
  · simp [hs]
  · simp only [hs, if_false, Bool.false_eq_true]
    rw [pushesRaw_eq, pushesRaw_eq, unmetBoxes_congr h.goalsSame]
    congr 1
    refine List.map_congr_left ?_
    intro b hb
    have hm : b ∈ d.boxes := by
      simp only [unmetBoxes, Array.toList_filter, List.mem_filter] at hb
      simpa using hb.1
    rw [h.boxSame b hm]

theorem Ac_le (h : MoveStep d s s') : Ac d s ≤ Ac d s' + 1 := by
  show approach d s ≤ approach d s' + 1
  unfold approach
  rw [h.solved_eq]
  by_cases hs : solved d s
  · simp [hs]
  · simp only [hs, if_false, Bool.false_eq_true,
      approachCost_of_some h.robotSome, approachCost_of_some h.robotSome']
    have := h.approachStep
    omega

theorem Hc_le (h : MoveStep d s s') : Hc d s ≤ Hc d s' + 1 := by
  show hardest d s ≤ hardest d s' + 1
  unfold hardest
  rw [h.solved_eq]
  by_cases hs : solved d s
  · simp [hs]
  · simp only [hs, if_false, Bool.false_eq_true]
    have := hardestRaw_le_succ d s s' h.jointStep
    omega

end MoveStep

namespace PushStep
variable {d : Data} {s s' : State}

/-
`PushStep` used to carry a field `goalsMono`, saying a box may reach its goal but
never leave it, and a lemma `solved_mono` derived from it.  A `push` can shove a
box straight off its goal square, so the field is false, and nothing consumed the
lemma: `Pc_le`, `Ac_le` and `Hc_le` all go through the `last*` fields instead.
Both are gone.
-/

theorem Pc_le (h : PushStep d s s') : Pc d s ≤ Pc d s' + 1 := by
  show pushes d s ≤ pushes d s' + 1
  unfold pushes
  by_cases hs : solved d s
  · simp [hs]
  · by_cases hs' : solved d s'
    · simp only [hs, hs', if_false, if_true, Bool.false_eq_true]
      have := h.lastPush hs'
      omega
    · simp only [hs, hs', if_false, Bool.false_eq_true]
      have := h.pushStep
      omega

theorem Ac_le (h : PushStep d s s') : Ac d s ≤ Ac d s' := by
  show approach d s ≤ approach d s'
  unfold approach
  by_cases hs : solved d s
  · simp [hs]
  · by_cases hs' : solved d s'
    · simp only [hs, hs', if_false, if_true, Bool.false_eq_true,
        approachCost_of_some h.robotSome]
      have := h.lastApproach hs'
      omega
    · simp only [hs, hs', if_false, Bool.false_eq_true,
        approachCost_of_some h.robotSome, approachCost_of_some h.robotSome']
      exact h.approachMono

theorem Hc_le (h : PushStep d s s') : Hc d s ≤ Hc d s' + 1 := by
  show hardest d s ≤ hardest d s' + 1
  unfold hardest
  by_cases hs : solved d s
  · simp [hs]
  · by_cases hs' : solved d s'
    · simp only [hs, hs', if_false, if_true, Bool.false_eq_true]
      have := h.lastHardest hs'
      omega
    · simp only [hs, hs', if_false, Bool.false_eq_true]
      have := hardestRaw_le_succ d s s' h.jointStep
      omega

end PushStep

theorem effect_of_schema (d : Data) (s s' : State) (he : SchemaStep d s s') :
    Effect d s s' := by
  cases he with
  | move h => exact .move h.Pc_eq h.Ac_le h.Hc_le
  | push h => exact .push h.Pc_le h.Ac_le h.Hc_le

/-- Zero at every goal state. -/
theorem improved_goalAware_of_schema (t : Task)
    (hcompiled : ∀ b ∈ (compile t).boxes, b.goalFact ∈ t.goal) :
    t.GoalAware (improved t).eval := improved_goalAware t hcompiled

/-- And never falls by more than one action costs, on the states `Q` holds of. -/
theorem improved_consistentOn_of_schema (t : Task) (Q : State → Prop)
    (hstep : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → Q s → op.applicable s = true →
      SchemaStep (compile t) s (op.apply s))
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost) :
    t.ConsistentOn Q (improved t).eval :=
  improved_consistentOn t Q
    (fun op hop s hs hq happ => effect_of_schema _ s _ (hstep op hop s hs hq happ)) hcost

/-- **Never overestimates**, on every state a closed invariant `Q` holds of. -/
theorem improved_admissibleOn_of_schema (t : Task) (Q : State → Prop)
    (hQ : ∀ s i s', State.WF t.numFacts s → Q s → t.step s i s' → Q s')
    (hcompiled : ∀ b ∈ (compile t).boxes, b.goalFact ∈ t.goal)
    (hstep : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → Q s → op.applicable s = true →
      SchemaStep (compile t) s (op.apply s))
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost) :
    t.AdmissibleOn Q (improved t).eval :=
  t.admissibleOn _ _ hQ
    (fun s hs hgoal => improved_goalAware_of_schema t hcompiled s hs.1 hgoal)
    (improved_consistentOn_of_schema t Q hstep hcost)

end Planner.ExampleHeuristics.Sokoban

/- -------------------------------------------------------------------------- -/
/-
Reading Sokoban's box table.

`compile` builds the experimental product-distance table by filtering the
task's goal atoms, so every entry carries a goal fact of the task.  These reader
lemmas remain useful for proving that stronger evaluator when its metric
obligations are discharged.

The table was until recently built by a loop with an accumulator, which a proof
cannot read: an imperative fold hides what an entry is behind its own induction.
Written as a filter, the spelling below is `rfl`.
-/

namespace Planner.Lifted.Sokoban

open Planner Planner.Pddl

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

open Planner.ExampleHeuristics.Sokoban in
/--
**Every box the table holds carries a goal fact of the task.**

Whatever the location index does, the entry's `goalFact` is read out of
`t.goal` at the position of the goal atom that produced it.
-/
theorem boxes_mem_goal (d : Domain) (p : Problem) (rel : Bool) :
    ∀ b ∈ (compile (ground d p rel)).boxes,
      b.goalFact ∈ (ground d p rel).goal := by
  intro b hb
  obtain ⟨x, hx, hval⟩ := Array.mem_filterMap.mp hb
  obtain ⟨-, hlt, -⟩ := Array.mem_zipIdx hx
  simp only [Nat.zero_add] at hlt
  obtain ⟨a, i⟩ := x
  dsimp only at hval hlt
  by_cases hp : (a.pred == "at") = true
  · rw [if_pos hp] at hval
    split at hval
    · obtain ⟨gl, -, hval'⟩ := Option.map_eq_some_iff.mp hval
      subst hval'
      exact goal_getD_mem hlt
    · simp at hval
  · rw [if_neg hp] at hval; simp at hval

/-! ### What the box table holds

A box entry's goal fact names an `at` atom, and its position table holds `at`
facts of that box.  `move` touches only `at-robot`, so both are framed across a
walk — which is `MoveStep.goalsSame` and `MoveStep.boxSame`.
-/

open Planner.ExampleHeuristics.Sokoban in
/-- **Every box's goal fact names an `at` atom.** -/
theorem boxes_name (d : Domain) (p : Problem) (rel : Bool) :
    ∀ bx ∈ (compile (ground d p rel)).boxes,
      bx.goalFact < (ground d p rel).factNames.size ∧
      ∃ b g, (ground d p rel).factNames.getD bx.goalFact default
        = { pred := "at", args := [b, g] } := by
  intro bx hb
  obtain ⟨x, hx, hval⟩ := Array.mem_filterMap.mp hb
  obtain ⟨-, hlt, hget⟩ := Array.mem_zipIdx hx
  simp only [Nat.zero_add, Nat.sub_zero] at hlt hget
  obtain ⟨a, i⟩ := x
  dsimp only at hval hlt hget
  by_cases hp : (a.pred == "at") = true
  · rw [if_pos hp] at hval
    split at hval
    · rename_i b g h1
      obtain ⟨gl, -, hval'⟩ := Option.map_eq_some_iff.mp hval
      subst hval'
      obtain ⟨hname, hfsz⟩ := goal_name_eq d p rel hlt
      refine ⟨hfsz, b, g, ?_⟩
      show (ground d p rel).factNames.getD ((ground d p rel).goal.getD i 0) default = _
      rw [hname, ← eq_of_beq hp, ← h1]
      exact hget.symm
    · simp at hval
  · rw [if_neg hp] at hval; simp at hval

open Planner.ExampleHeuristics.Sokoban in
/-- **And every fact in its position table is an `at` fact.** -/
theorem boxes_atFacts_pred {t : Task} {bx : BoxInfo}
    (hb : bx ∈ (compile t).boxes) {e : Fact × Nat} (he : e ∈ bx.atFacts) :
    e.1 < t.factNames.size ∧ (t.factNames.getD e.1 default).pred = "at" := by
  obtain ⟨x, hx, hval⟩ := Array.mem_filterMap.mp hb
  obtain ⟨a, i⟩ := x
  dsimp only at hval
  by_cases hp : (a.pred == "at") = true
  · rw [if_pos hp] at hval
    split at hval
    · rename_i b g h1
      obtain ⟨gl, -, hval'⟩ := Option.map_eq_some_iff.mp hval
      subst hval'
      obtain ⟨y, -, hyval, hlt, hname, hpred⟩ := mem_factsWith_filterMap he
      obtain ⟨g', c⟩ := y
      dsimp only at hyval hlt hname hpred
      rcases hargs : c.args with _ | ⟨u, rest⟩
      · rw [hargs] at hyval; simp at hyval
      rcases rest with _ | ⟨l, rest⟩
      · rw [hargs] at hyval; simp at hyval
      rcases rest with _ | ⟨q, rest⟩
      case cons.cons.cons => rw [hargs] at hyval; simp at hyval
      rw [hargs] at hyval
      dsimp only at hyval
      by_cases hu : u == b
      · rw [if_pos hu] at hyval
        obtain ⟨li, -, hli⟩ := Option.map_eq_some_iff.mp hyval
        subst hli
        exact ⟨hlt, by rw [hname]; exact hpred⟩
      · rw [if_neg hu] at hyval; simp at hyval
    · simp at hval
  · rw [if_neg hp] at hval; simp at hval

/-! ### `move` frames the boxes

`move` touches only `at-robot`, so neither a box's goal nor its position moves.
Those are `MoveStep.goalsSame` and `MoveStep.boxSame`.
-/

variable {d : Domain} {p : Problem} {rel : Bool}

open Planner.ExampleHeuristics.Sokoban in
/-- **`MoveStep.goalsSame`.** -/
theorem move_goalsSame {o : AtomOp} (hf : OpFacts d p o) {f t dir : Pddl.Name}
    (hs : hf.inst.schema = moveA) (ha : hf.inst.args = [f, t, dir])
    {s s' : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (habs' : Abstracts (ground d p rel) s' (o.applyA σ))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size) :
    ∀ b ∈ (compile (ground d p rel)).boxes,
      s'.test b.goalFact = s.test b.goalFact := by
  intro b hb
  obtain ⟨hlt, bx, g, hname⟩ := boxes_name d p rel b hb
  refine test_frame_pred (P := "at") hf ?_ ?_ habs habs' hn hlt (by rw [hname]) <;>
    intro a hm hbad
  · rw [move_touches hf.inst hs ha (Or.inl hm)] at hbad; exact absurd hbad (by decide)
  · rw [move_touches hf.inst hs ha (Or.inr hm)] at hbad; exact absurd hbad (by decide)

open Planner.ExampleHeuristics.Sokoban in
/-- **`MoveStep.boxSame`.** -/
theorem move_boxSame {o : AtomOp} (hf : OpFacts d p o) {f t dir : Pddl.Name}
    (hs : hf.inst.schema = moveA) (ha : hf.inst.args = [f, t, dir])
    {s s' : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (habs' : Abstracts (ground d p rel) s' (o.applyA σ))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size) :
    ∀ b ∈ (compile (ground d p rel)).boxes, boxLoc s' b = boxLoc s b := by
  intro b hb
  unfold boxLoc
  refine congrArg _ (array_find?_congr _ _ _ fun y hy => ?_)
  obtain ⟨hlt, hpred⟩ := boxes_atFacts_pred hb hy
  refine test_frame_pred (P := "at") hf ?_ ?_ habs habs' hn hlt hpred <;>
    intro a hm hbad
  · rw [move_touches hf.inst hs ha (Or.inl hm)] at hbad; exact absurd hbad (by decide)
  · rw [move_touches hf.inst hs ha (Or.inr hm)] at hbad; exact absurd hbad (by decide)

end Planner.Lifted.Sokoban

/- -------------------------------------------------------------------------- -/
/-
Reading Sokoban's two graphs.

`compile` builds three tables out of the `adjacent` facts: where the robot may
walk, where a box may be pushed from and to, and the two distance tables over
those.  All three were written as loops over mutable arrays, which a proof
cannot read — an imperative fold hides what an entry is behind its own
induction.  They are now `filterMap`s and `flatMap`s over the static facts, and
this file says what they hold.

What the step proof needs from them is one direction only: a schema whose static
preconditions name an `adjacent` fact puts an edge in the graph.  That is what
lets the distance table's triangle inequality apply to the square the robot or
the box just left.
-/

namespace Planner.Lifted.Sokoban

open Planner Planner.Pddl Planner.ExampleHeuristics.Sokoban

/-! ### The location table and its index -/

/-- The squares, in the order the compiled tables index them. -/
abbrev locsA (t : Task) : Array Name := t.objectsOfTypes ["location"]

/-- The index the compiled tables give a square. -/
abbrev locIx (t : Task) (l : Name) : Option Nat := (Graph.nodeIndex (locsA t))[l]?

theorem locIx_lt {t : Task} {l : Name} {i : Nat} (h : locIx t l = some i) :
    i < (locsA t).size := Graph.nodeIndex_lt h

theorem locIx_get {t : Task} {l : Name} {i : Nat} (h : locIx t l = some i) :
    (locsA t).getD i "" = l := Graph.nodeIndex_get h

/-- An index determines its square, so two names at one index are one name. -/
theorem locIx_inj {t : Task} {l l' : Name} {i : Nat}
    (h : locIx t l = some i) (h' : locIx t l' = some i) : l = l' := by
  rw [← locIx_get h, ← locIx_get h']

theorem locIx_isSome {t : Task} {l : Name} (h : l ∈ locsA t) :
    (locIx t l).isSome := Graph.nodeIndex_isSome h

theorem locIx_total {t : Task} {l : Name} (h : l ∈ locsA t) :
    ∃ i, locIx t l = some i := by
  have hs := locIx_isSome (t := t) h
  rcases hv : locIx t l with _ | i
  · rw [hv] at hs; exact absurd hs (by simp)
  · exact ⟨i, rfl⟩

/-! ### Reading a table built over `Array.range` -/

theorem range_map_getD {α : Type} (n : Nat) (f : Nat → α) {k : Nat} (hk : k < n)
    (dflt : α) : ((Array.range n).map f).getD k dflt = f k := by
  rw [Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem (by simpa using hk)]
  simp

/-! ### The robot's steps -/

/-- **An `adjacent` fact is a robot step.** -/
theorem mem_robotStepsAt {t : Task} {index : Std.HashMap Name Nat}
    {x y dd : Name} {u v : Nat}
    (ha : adjacent x y dd ∈ t.staticWith "adjacent")
    (hx : index[x]? = some u) (hy : index[y]? = some v) :
    v ∈ robotStepsAt t index u := by
  refine Array.mem_filterMap.mpr ⟨adjacent x y dd, ha, ?_⟩
  show (match ([x, y, dd] : List Name) with
    | [x, y, _] => if index[x]? == some u then index[y]? else none
    | _ => none) = some v
  simp [hx, hy]

theorem robotSteps_getD {t : Task} {index : Std.HashMap Name Nat} {n u : Nat}
    (hu : u < n) : (robotSteps t index n).getD u #[] = robotStepsAt t index u :=
  range_map_getD n _ hu #[]

/-! ### The pushes -/

/-- **Two `adjacent` facts in line are a push.**  The robot stands on `r` behind
a box on `b`, and the box goes to `f`. -/
theorem mem_pushStepsAt {t : Task} {index : Std.HashMap Name Nat}
    {r b f dd : Name} {ub ur uf : Nat}
    (h1 : adjacent r b dd ∈ t.staticWith "adjacent")
    (h2 : adjacent b f dd ∈ t.staticWith "adjacent")
    (hb : index[b]? = some ub) (hr : index[r]? = some ur) (hf : index[f]? = some uf) :
    (ur, uf) ∈ pushStepsAt t index ub := by
  refine Array.mem_flatMap.mpr ⟨adjacent r b dd, h1, ?_⟩
  show (ur, uf) ∈ (match ([r, b, dd] : List Name) with
    | [r, b, d] => if index[b]? == some ub then pushStepsOf t index r b d else #[]
    | _ => #[])
  simp only [hb]
  rw [if_pos (by simp)]
  refine Array.mem_filterMap.mpr ⟨adjacent b f dd, h2, ?_⟩
  show (match ([b, f, dd] : List Name) with
    | [x, fl, e] =>
        if x == b && e == dd then
          match index[r]?, index[fl]? with
          | some ur, some uf => some (ur, uf)
          | _, _ => none
        else none
    | _ => none) = some (ur, uf)
  simp [hr, hf]

theorem pushSteps_getD {t : Task} {index : Std.HashMap Name Nat} {n u : Nat}
    (hu : u < n) : (pushSteps t index n).getD u #[] = pushStepsAt t index u :=
  range_map_getD n _ hu #[]

/-! ### The robot's walk graph, symmetrised -/

theorem mem_walkAdjAt_of {walk : Array (Array Nat)} {u v : Nat}
    (hu : u < walk.size) (h : v ∈ walk.getD u #[]) : v ∈ walkAdjAt walk u := by
  refine Array.mem_flatMap.mpr ⟨(walk.getD u #[], u), ?_, ?_⟩
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hu]
    simpa using Array.mem_zipIdx_iff_getElem?.mpr (by simp [Array.getElem?_eq_getElem hu])
  · refine Array.mem_flatMap.mpr ⟨v, h, ?_⟩
    simp

/-- The walk graph is symmetric by construction, which is what makes the
approach distance move by at most one per robot step in either direction. -/
theorem mem_walkAdjAt_symm {walk : Array (Array Nat)} {u v : Nat}
    (hu : u < walk.size) (h : v ∈ walk.getD u #[]) : u ∈ walkAdjAt walk v := by
  refine Array.mem_flatMap.mpr ⟨(walk.getD u #[], u), ?_, ?_⟩
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hu]
    simpa using Array.mem_zipIdx_iff_getElem?.mpr (by simp [Array.getElem?_eq_getElem hu])
  · refine Array.mem_flatMap.mpr ⟨v, h, ?_⟩
    simp

theorem walkGraph_adj_getD {locations : Array Name} {index : Std.HashMap Name Nat}
    {walk : Array (Array Nat)} {k : Nat} (hk : k < locations.size) :
    (walkGraph locations index walk).adj.getD k #[] = walkAdjAt walk k :=
  range_map_getD locations.size _ hk #[]

theorem walkGraph_size {locations : Array Name} {index : Std.HashMap Name Nat}
    {walk : Array (Array Nat)} :
    (walkGraph locations index walk).size = locations.size := rfl

/-! ### The push graph -/

theorem pushGraph_adj_getD {locations : Array Name} {index : Std.HashMap Name Nat}
    {pushes : Array (Array (Nat × Nat))} {k : Nat} :
    (pushGraph locations index pushes).adj.getD k #[] = (pushes.getD k #[]).map (·.2) := by
  show ((pushes.map fun ps => ps.map (·.2)).getD k #[]) = _
  by_cases hk : k < pushes.size
  · rw [Array.getD_eq_getD_getElem? (xs := pushes.map _),
      Array.getElem?_eq_getElem (by simpa using hk),
      Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk]
    simp
  · rw [Array.getD_eq_getD_getElem? (xs := pushes.map _),
      Array.getElem?_eq_none (by simpa using Nat.le_of_not_lt hk),
      Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt hk)]
    simp

theorem pushGraph_size {locations : Array Name} {index : Std.HashMap Name Nat}
    {pushes : Array (Array (Nat × Nat))} :
    (pushGraph locations index pushes).size = locations.size := rfl

/-! ### The tables `compile` actually builds -/

/-- The robot's steps, over the squares the compiled tables index. -/
abbrev walkTable (t : Task) : Array (Array Nat) :=
  robotSteps t (Graph.nodeIndex (locsA t)) (locsA t).size

/-- The pushes, likewise. -/
abbrev pushTable (t : Task) : Array (Array (Nat × Nat)) :=
  pushSteps t (Graph.nodeIndex (locsA t)) (locsA t).size

theorem walkTable_size (t : Task) : (walkTable t).size = (locsA t).size := by
  simp [walkTable, robotSteps]

theorem pushTable_size (t : Task) : (pushTable t).size = (locsA t).size := by
  simp [pushTable, pushSteps]

theorem compile_n (t : Task) : (compile t).n = (locsA t).size := rfl

theorem compile_walk (t : Task) :
    (compile t).walk =
      Distances.of (walkGraph (locsA t) (Graph.nodeIndex (locsA t)) (walkTable t)) := rfl

theorem compile_dist (t : Task) :
    (compile t).dist =
      Distances.of (pushGraph (locsA t) (Graph.nodeIndex (locsA t)) (pushTable t)) := rfl

theorem compile_pushPos (t : Task) :
    (compile t).pushPos = (pushTable t).map fun ps => ps.map (·.1) := rfl

/-- Reading a bucket of a table built by mapping over buckets. -/
theorem map_getD_empty {α β : Type} (xs : Array (Array α)) (f : Array α → Array β)
    (hf : f #[] = #[]) (k : Nat) : (xs.map f).getD k #[] = f (xs.getD k #[]) := by
  by_cases hk : k < xs.size
  · rw [Array.getD_eq_getD_getElem? (xs := xs.map f),
      Array.getElem?_eq_getElem (by simpa using hk),
      Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk]
    simp
  · rw [Array.getD_eq_getD_getElem? (xs := xs.map f),
      Array.getElem?_eq_none (by simpa using Nat.le_of_not_lt hk),
      Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt hk)]
    simp [hf]


/-- **Both ends of a push are squares the tables index.** -/
theorem pushStepsAt_data {t : Task} {ub : Nat} {y : Nat × Nat}
    (hy : y ∈ pushStepsAt t (Graph.nodeIndex (locsA t)) ub) :
    y.1 < (locsA t).size ∧ y.2 < (locsA t).size := by
  obtain ⟨a, -, hya⟩ := Array.mem_flatMap.mp hy
  rcases hargs : a.args with _ | ⟨r, rest⟩
  · rw [hargs] at hya; simp at hya
  rcases rest with _ | ⟨bb, rest⟩
  · rw [hargs] at hya; simp at hya
  rcases rest with _ | ⟨dd, rest⟩
  · rw [hargs] at hya; simp at hya
  rcases rest with _ | ⟨q, rest⟩
  case cons.cons.cons.cons => rw [hargs] at hya; simp at hya
  rw [hargs] at hya
  dsimp only at hya
  split at hya
  · obtain ⟨c, -, hc⟩ := Array.mem_filterMap.mp hya
    rcases hcargs : c.args with _ | ⟨x, crest⟩
    · rw [hcargs] at hc; simp at hc
    rcases crest with _ | ⟨f, crest⟩
    · rw [hcargs] at hc; simp at hc
    rcases crest with _ | ⟨e, crest⟩
    · rw [hcargs] at hc; simp at hc
    rcases crest with _ | ⟨q', crest⟩
    case cons.cons.cons.cons => rw [hcargs] at hc; simp at hc
    rw [hcargs] at hc
    dsimp only at hc
    split at hc
    · rcases h1 : (Graph.nodeIndex (locsA t))[r]? with _ | ur
      · rw [h1] at hc; simp at hc
      rcases h2 : (Graph.nodeIndex (locsA t))[f]? with _ | uf
      · rw [h1, h2] at hc; simp at hc
      rw [h1, h2] at hc
      have hyy : (ur, uf) = y := by simpa using hc
      rw [← hyy]
      exact ⟨Graph.nodeIndex_lt h1, Graph.nodeIndex_lt h2⟩
    · simp at hc
  · simp at hya

/-- And so is every square a box can be pushed from. -/
theorem pushPos_lt (t : Task) {l q : Nat}
    (hq : q ∈ (compile t).pushPos.getD l #[]) : q < (locsA t).size := by
  rw [compile_pushPos, map_getD_empty _ _ (by simp)] at hq
  obtain ⟨y, hy, hval⟩ := Array.mem_map.mp hq
  by_cases hl : l < (locsA t).size
  · rw [pushSteps_getD hl] at hy
    rw [← hval]
    exact (pushStepsAt_data hy).1
  · have hsz : ¬ l < (pushTable t).size := by rw [pushTable_size]; exact hl
    rw [Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none (Nat.le_of_not_lt hsz)] at hy
    simp at hy

/-! ### An `adjacent` fact is an edge of both graphs -/

theorem mem_walkTable (t : Task) {x y dd : Name} {u v : Nat}
    (ha : adjacent x y dd ∈ t.staticWith "adjacent")
    (hx : locIx t x = some u) (hy : locIx t y = some v) :
    v ∈ (walkTable t).getD u #[] := by
  rw [walkTable, robotSteps_getD (locIx_lt hx)]
  exact mem_robotStepsAt ha hx hy

/-- **A robot step is an edge of the walk graph, in both directions.**  The graph
is symmetrised on purpose: the approach distance has to move by at most one
whichever way the robot walks. -/
theorem walk_edge (t : Task) {x y dd : Name} {u v : Nat}
    (ha : adjacent x y dd ∈ t.staticWith "adjacent")
    (hx : locIx t x = some u) (hy : locIx t y = some v) :
    v ∈ (walkGraph (locsA t) (Graph.nodeIndex (locsA t)) (walkTable t)).adj.getD u #[] ∧
      u ∈ (walkGraph (locsA t) (Graph.nodeIndex (locsA t)) (walkTable t)).adj.getD v #[] := by
  have hmem := mem_walkTable t ha hx hy
  have hsz : u < (walkTable t).size := by rw [walkTable_size]; exact locIx_lt hx
  constructor
  · rw [walkGraph_adj_getD (locIx_lt hx)]
    exact mem_walkAdjAt_of hsz hmem
  · rw [walkGraph_adj_getD (locIx_lt hy)]
    exact mem_walkAdjAt_symm hsz hmem

/-- **A push is an edge of the push graph**, and the square the robot pushed from
is one of the squares that box square can be pushed from. -/
theorem push_edge (t : Task) {r b f dd : Name} {ub ur uf : Nat}
    (h1 : adjacent r b dd ∈ t.staticWith "adjacent")
    (h2 : adjacent b f dd ∈ t.staticWith "adjacent")
    (hb : locIx t b = some ub) (hr : locIx t r = some ur) (hf : locIx t f = some uf) :
    uf ∈ (pushGraph (locsA t) (Graph.nodeIndex (locsA t)) (pushTable t)).adj.getD ub #[] ∧
      ur ∈ (compile t).pushPos.getD ub #[] := by
  have hmem : (ur, uf) ∈ (pushTable t).getD ub #[] := by
    rw [pushTable, pushSteps_getD (locIx_lt hb)]
    exact mem_pushStepsAt h1 h2 hb hr hf
  constructor
  · rw [pushGraph_adj_getD]
    exact Array.mem_map.mpr ⟨(ur, uf), hmem, rfl⟩
  · rw [compile_pushPos, map_getD_empty _ _ (by simp)]
    exact Array.mem_map.mpr ⟨(ur, uf), hmem, rfl⟩

/-! ### A static precondition is a static fact of the task -/

variable {d : Domain} {p : Problem}

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
    rw [Std.HashSet.contains_ofList] at h
    simpa using h
  have hnot : a ∉ allAtoms (groundedOps d p rel) p.goal.toArray := by
    intro hc
    have hfalse := hp.goalDynamic a (mem_goal_of_static d p rel hc hstatic)
    rw [hstatic] at hfalse
    exact Bool.noConfusion hfalse
  exact mem_staticWith d p rel hinit hnot rfl

/-- **`move`'s `adjacent` precondition is a fact of the map.** -/
theorem move_adjacent (hp : Pinned d p) (rel : Bool) {o : AtomOp} (hf : OpFacts d p o)
    {frm dest dir : Name} (hs : hf.inst.schema = moveA)
    (ha : hf.inst.args = [frm, dest, dir]) :
    adjacent frm dest dir ∈ (ground d p rel).staticWith "adjacent" := by
  have hpre : hf.inst.pre = [clearL dest, atRobot frm, adjacent frm dest dir] := by
    rw [hf.inst.pre_eq, hs, ha]; rfl
  exact static_of_pre hp rel hf (a := adjacent frm dest dir) (by rw [hpre]; simp)
    hp.adjacentStatic

/-- **`push`'s two `adjacent` preconditions are facts of the map.** -/
theorem push_adjacent (hp : Pinned d p) (rel : Bool) {o : AtomOp} (hf : OpFacts d p o)
    {rl bl fl dir b : Name} (hs : hf.inst.schema = pushA)
    (ha : hf.inst.args = [rl, bl, fl, dir, b]) :
    adjacent rl bl dir ∈ (ground d p rel).staticWith "adjacent" ∧
      adjacent bl fl dir ∈ (ground d p rel).staticWith "adjacent" := by
  have hpre : hf.inst.pre = [atRobot rl, atBox b bl, clearL fl, adjacent rl bl dir,
      adjacent bl fl dir] := by rw [hf.inst.pre_eq, hs, ha]; rfl
  exact ⟨static_of_pre hp rel hf (a := adjacent rl bl dir) (by rw [hpre]; simp)
      hp.adjacentStatic,
    static_of_pre hp rel hf (a := adjacent bl fl dir) (by rw [hpre]; simp)
      hp.adjacentStatic⟩

end Planner.Lifted.Sokoban

/- -------------------------------------------------------------------------- -/
/-
Where the robot and the boxes stand.

The product-distance value reads three positions off a state — the robot's
square, each box's square, and whether a square is clear — with `find?`, so each
is only well defined because one atom of its family holds at a time.  That fact
is not free: it has to hold of `:init` and survive both schemas.

Five facts are needed, and each is needed by name.  The robot stands in exactly
one place, or `robotLoc` reads the wrong square.  Each box stands in exactly one
place, and no two boxes share a square, or `boxLoc` does.  And the robot's square
is clear while no box's square is, which is what says the robot is never on a
box — the side condition every edge of the product graph carries.
-/

namespace Planner.Lifted.Sokoban

open Planner Planner.Pddl

variable {d : Domain} {p : Problem}

/--
Grounding keeps the `at-robot` and `clear` adds of every retained operator.

Not the `at` adds: neither `at-robot` nor `clear` appears in a Sokoban goal, but
both are preconditions of both schemas, so the relevance analysis keeps every
fact of theirs.  A box position it may well drop — on the shipped tasks it drops
eight of twenty-nine — and the value is written to survive that.
-/
def FrameAddsKept (d : Domain) (p : Problem) (rel : Bool) : Prop :=
  ∀ o ∈ groundedOps d p rel, ∀ hf : OpFacts d p o,
    (∀ frm dest dir : Name, hf.inst.schema = moveA →
      hf.inst.args = [frm, dest, dir] → atRobot dest ∈ o.add) ∧
    (∀ rl bl fl dir b : Name, hf.inst.schema = pushA →
      hf.inst.args = [rl, bl, fl, dir, b] → atRobot bl ∈ o.add ∧ clearL bl ∈ o.add)

/-! ### The invariant -/

/-- The positions the value reads, each single-valued, and the robot off the
boxes. -/
structure Inv (σ : AtomState) : Prop where
  /-- The robot stands somewhere, and in one place only. -/
  robot : RobotAt σ
  /-- A box stands in one place. -/
  boxOne : ∀ b l l', σ (atBox b l) = true → σ (atBox b l') = true → l = l'
  /-- And a square holds one box. -/
  squareOne : ∀ b b' l, σ (atBox b l) = true → σ (atBox b' l) = true → b = b'
  /-- The robot's square is clear. -/
  robotClear : ∀ l, σ (atRobot l) = true → σ (clearL l) = true
  /-- A box's square is not. -/
  boxNotClear : ∀ b l, σ (atBox b l) = true → σ (clearL l) = false

/-- The robot is never on a box's square, which is the side condition every
product-graph edge carries. -/
theorem Inv.robot_ne_box {σ : AtomState} (h : Inv σ) {b l r : Name}
    (hb : σ (atBox b l) = true) (hr : σ (atRobot r) = true) : r ≠ l := by
  intro heq
  subst heq
  have h1 := h.robotClear r hr
  have h2 := h.boxNotClear b r hb
  rw [h1] at h2
  exact Bool.noConfusion h2

/-! ### The initial check -/

/-- The finite check on `:init` that supplies the invariant there. -/
def initInvCheck (p : Problem) : Bool :=
  !(initOnes p "at-robot").isEmpty &&
  ((initOnes p "at-robot").all fun l => (initOnes p "at-robot").all fun l' => l == l') &&
  ((initPairs p "at").all fun x => (initPairs p "at").all fun y =>
      (!(x.1 == y.1) || (x.2 == y.2)) && (!(x.2 == y.2) || (x.1 == y.1))) &&
  ((initOnes p "at-robot").all fun l => (initOnes p "clear").contains l) &&
  ((initPairs p "at").all fun x => !((initOnes p "clear").contains x.2))

theorem init_inv (h : initInvCheck p = true) :
    Inv (fun a => p.init.toArray.contains a) := by
  simp only [initInvCheck, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hne, hrobotOne⟩, hboxes⟩, hrclear⟩, hbclear⟩ := h
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rcases hlist : initOnes p "at-robot" with _ | ⟨l, ls⟩
    · rw [hlist] at hne; simp at hne
    · exact ⟨l, by simpa using mem_initOnes.mp (by rw [hlist]; simp)⟩
  · intro l l' h1 h2
    exact hrobotOne l (mem_initOnes.mpr (by simpa using h1)) l'
      (mem_initOnes.mpr (by simpa using h2))
  · intro b l l' h1 h2
    have m1 : (b, l) ∈ initPairs p "at" := mem_initPairs.mpr (by simpa [atBox] using h1)
    have m2 : (b, l') ∈ initPairs p "at" := mem_initPairs.mpr (by simpa [atBox] using h2)
    rcases (hboxes _ m1 _ m2).1 with hc | hc
    · simp at hc
    · simpa using hc
  · intro b b' l h1 h2
    have m1 : (b, l) ∈ initPairs p "at" := mem_initPairs.mpr (by simpa [atBox] using h1)
    have m2 : (b', l) ∈ initPairs p "at" := mem_initPairs.mpr (by simpa [atBox] using h2)
    rcases (hboxes _ m1 _ m2).2 with hc | hc
    · simp at hc
    · simpa using hc
  · intro l h1
    have hm : l ∈ initOnes p "at-robot" := mem_initOnes.mpr (by simpa [atRobot] using h1)
    have := hrclear l hm
    have hmem : l ∈ initOnes p "clear" := by simpa using this
    simpa [clearL] using mem_initOnes.mp hmem
  · intro b l h1
    have hm : (b, l) ∈ initPairs p "at" := mem_initPairs.mpr (by simpa [atBox] using h1)
    have hnot : l ∉ initOnes p "clear" := by
      intro hc
      have := hbclear _ hm
      rw [show ((initOnes p "clear").contains l) = true from by simpa using hc] at this
      exact Bool.noConfusion this
    simp only [Bool.eq_false_iff, ne_eq]
    intro hc
    exact hnot (mem_initOnes.mpr (by simpa [clearL] using hc))

/-! ### Both schemas keep it -/

/-- Its two ends differ, so a `move` is never a self-loop. -/
theorem adjacent_ne (hp : Pinned d p) (rel : Bool) {o : AtomOp} (hf : OpFacts d p o)
    {x y dd : Name} (hmem : adjacent x y dd ∈ hf.inst.pre) : x ≠ y := by
  intro heq
  subst heq
  have hstat : adjacent x x dd ∈ (ground d p rel).staticWith "adjacent" :=
    static_of_pre hp rel hf (a := adjacent x x dd) hmem hp.adjacentStatic
  exact hp.noSelfAdjacent x dd (staticWith_sub d p rel hstat).1

/-- **`move` puts the robot on its destination.** -/
theorem move_robot_add {o : AtomOp} (ho : o ∈ groundedOps d p rel)
    (hfk : FrameAddsKept d p rel) (hf : OpFacts d p o) {frm dest dir : Name}
    (hs : hf.inst.schema = moveA) (ha : hf.inst.args = [frm, dest, dir]) :
    atRobot dest ∈ o.add := (hfk o ho hf).1 frm dest dir hs ha

/-- The robot really is at the destination afterwards. -/
theorem move_robot_after {o : AtomOp} (ho : o ∈ groundedOps d p rel)
    (hfk : FrameAddsKept d p rel) (hf : OpFacts d p o) {frm dest dir : Name}
    (hs : hf.inst.schema = moveA) (ha : hf.inst.args = [frm, dest, dir])
    (σ : AtomState) : o.applyA σ (atRobot dest) = true :=
  applyA_add σ (move_robot_add ho hfk hf hs ha)

/-- **`move` keeps the invariant.**  It touches only `at-robot`, and its
destination was clear. -/
theorem move_inv (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (ho : o ∈ groundedOps d p rel) (hfk : FrameAddsKept d p rel)
    (hfa : OpFacts d p o)
    {frm dest dir : Name} (hs : hfa.inst.schema = moveA)
    (ha : hfa.inst.args = [frm, dest, dir])
    {σ : AtomState} (hinv : Inv σ) (happ : o.applicableA σ) : Inv (o.applyA σ) := by
  obtain ⟨hpre, hadd, hdel⟩ := move_atoms hfa.inst hs ha
  have hpreEq : hfa.inst.pre = [clearL dest, atRobot frm, adjacent frm dest dir] := by
    rw [hfa.inst.pre_eq, hs, ha]; rfl
  have hne : frm ≠ dest :=
    adjacent_ne hp rel hfa (x := frm) (y := dest) (dd := dir)
      (by rw [hpreEq]; simp)
  have hframe : ∀ a : GroundAtom, a.pred ≠ "at-robot" → o.applyA σ a = σ a := by
    intro a hnp
    refine applyA_frame σ (fun hm => hnp ?_) (fun hm => hnp ?_)
    · exact move_touches hfa.inst hs ha (Or.inl (hfa.subAdd _ hm))
    · exact move_touches hfa.inst hs ha (Or.inr (hfa.subDel _ hm))
  have hbox : ∀ b l, o.applyA σ (atBox b l) = σ (atBox b l) :=
    fun b l => hframe _ (by simp [atBox])
  have hclear : ∀ l, o.applyA σ (clearL l) = σ (clearL l) :=
    fun l => hframe _ (by simp [clearL])
  have hnew : o.applyA σ (atRobot dest) = true := move_robot_after ho hfk hfa hs ha σ
  have hrobot := robotAt_step hfa hp.domain hpre (by rw [hdel]; simp) hnew
    (by intro a hm _; rw [hadd] at hm; simpa using hm) happ hinv.robot
  refine ⟨hrobot, ?_, ?_, ?_, ?_⟩
  · intro b l l' h1 h2
    exact hinv.boxOne b l l' (by rw [← hbox]; exact h1) (by rw [← hbox]; exact h2)
  · intro b b' l h1 h2
    exact hinv.squareOne b b' l (by rw [← hbox]; exact h1) (by rw [← hbox]; exact h2)
  · intro l hl
    have hld : l = dest := hrobot.2 l dest hl hnew
    rw [hld, hclear]
    exact pre_holds hfa (a := clearL dest) (by rw [hpreEq]; simp)
      (clear_dynamic hp.domain) happ
  · intro b l h1
    rw [hclear]
    exact hinv.boxNotClear b l (by rw [← hbox]; exact h1)

/-- **`push` asserts the two adds the relevance analysis always keeps.** -/
theorem push_frame_adds {o : AtomOp} (ho : o ∈ groundedOps d p rel)
    (hfk : FrameAddsKept d p rel) (hf : OpFacts d p o) {rl bl fl dir b : Name}
    (hs : hf.inst.schema = pushA) (ha : hf.inst.args = [rl, bl, fl, dir, b]) :
    atRobot bl ∈ o.add ∧ clearL bl ∈ o.add := (hfk o ho hf).2 rl bl fl dir b hs ha

/-- **The box a `push` moves ends up on the square ahead, and nowhere else.** -/
theorem push_box_key (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (hfa : OpFacts d p o) {rl bl fl dir b : Name}
    (hs : hfa.inst.schema = pushA) (ha : hfa.inst.args = [rl, bl, fl, dir, b])
    {σ : AtomState} (hinv : Inv σ) (happ : o.applicableA σ) :
    ∀ l, o.applyA σ (atBox b l) = true → l = fl := by
  obtain ⟨hpreR, hpreB, hpreC, hadd, hdel⟩ := push_atoms hfa.inst hs ha
  have hpreEq : hfa.inst.pre = [atRobot rl, atBox b bl, clearL fl,
      adjacent rl bl dir, adjacent bl fl dir] := by
    rw [hfa.inst.pre_eq, hs, ha]; rfl
  have hbf : bl ≠ fl :=
    adjacent_ne hp rel hfa (x := bl) (y := fl) (dd := dir)
      (by rw [hpreEq]; simp)
  have hboxBefore : σ (atBox b bl) = true :=
    pre_holds hfa hpreB (atBox_dynamic hp.domain) happ
  have hgoneB : o.applyA σ (atBox b bl) = false :=
    falsified_of_lists hfa hadd hdel
      (by simp [atBox, atRobot, clearL, hbf]) (by simp) hpreB
      (atBox_dynamic hp.domain) σ
  intro l hl
  by_cases hlf : l = fl
  · exact hlf
  have hnotAdd : atBox b l ∉ [atRobot bl, atBox b fl, clearL bl] := by
    simp [atBox, atRobot, clearL, hlf]
  have hbefore : σ (atBox b l) = true := falls_of_lists hfa hadd hnotAdd hl
  have hlbl : l = bl := hinv.boxOne b l bl hbefore hboxBefore
  rw [hlbl, hgoneB] at hl
  exact absurd hl (by simp)

/-- And the two really hold afterwards. -/
theorem push_adds {o : AtomOp} (ho : o ∈ groundedOps d p rel)
    (hfk : FrameAddsKept d p rel) (hf : OpFacts d p o) {rl bl fl dir b : Name}
    (hs : hf.inst.schema = pushA) (ha : hf.inst.args = [rl, bl, fl, dir, b])
    (σ : AtomState) :
    o.applyA σ (atRobot bl) = true ∧ o.applyA σ (clearL bl) = true := by
  obtain ⟨h1, h2⟩ := push_frame_adds ho hfk hf hs ha
  exact ⟨applyA_add σ h1, applyA_add σ h2⟩

/-- **`push` keeps it.**  The box moves onto a clear square and leaves a clear
one behind, and the robot follows it onto the square it left. -/
theorem push_inv (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (ho : o ∈ groundedOps d p rel) (hfk : FrameAddsKept d p rel)
    (hfa : OpFacts d p o)
    {rl bl fl dir b : Name} (hs : hfa.inst.schema = pushA)
    (ha : hfa.inst.args = [rl, bl, fl, dir, b])
    {σ : AtomState} (hinv : Inv σ) (happ : o.applicableA σ) : Inv (o.applyA σ) := by
  obtain ⟨hpreR, hpreB, hpreC, hadd, hdel⟩ := push_atoms hfa.inst hs ha
  have hpreEq : hfa.inst.pre = [atRobot rl, atBox b bl, clearL fl,
      adjacent rl bl dir, adjacent bl fl dir] := by
    rw [hfa.inst.pre_eq, hs, ha]; rfl
  have hrb : rl ≠ bl :=
    adjacent_ne hp rel hfa (x := rl) (y := bl) (dd := dir)
      (by rw [hpreEq]; simp)
  have hbf : bl ≠ fl :=
    adjacent_ne hp rel hfa (x := bl) (y := fl) (dd := dir)
      (by rw [hpreEq]; simp)
  -- what holds before
  have hrobotBefore : σ (atRobot rl) = true :=
    pre_holds hfa hpreR (atRobot_dynamic hp.domain) happ
  have hboxBefore : σ (atBox b bl) = true :=
    pre_holds hfa hpreB (atBox_dynamic hp.domain) happ
  have hclearBefore : σ (clearL fl) = true :=
    pre_holds hfa hpreC (clear_dynamic hp.domain) happ
  -- the three adds really hold afterwards
  obtain ⟨hnewR, hnewC⟩ := push_adds ho hfk hfa hs ha σ
  -- and the two deletes that matter
  have hgoneB : o.applyA σ (atBox b bl) = false :=
    falsified_of_lists hfa hadd hdel
      (by simp [atBox, atRobot, clearL, hbf]) (by simp) hpreB
      (atBox_dynamic hp.domain) σ
  have hgoneC : o.applyA σ (clearL fl) = false :=
    falsified_of_lists hfa hadd hdel
      (by simp [clearL, atRobot, atBox, Ne.symm hbf]) (by simp) hpreC
      (clear_dynamic hp.domain) σ
  -- the box that moved ends up only on `fl`
  have hkeyB : ∀ l, o.applyA σ (atBox b l) = true → l = fl :=
    push_box_key hp rel hfa hs ha hinv happ
  -- every other box stands still
  have hother : ∀ b' l, b' ≠ b → o.applyA σ (atBox b' l) = σ (atBox b' l) := by
    intro b' l hb'
    exact frame_of_lists hfa hadd hdel
      (by simp [atBox, atRobot, clearL, hb']) (by simp [atBox, atRobot, clearL, hb']) σ
  -- and the squares away from the two the push touches keep their `clear`
  have hclearOther : ∀ l, l ≠ bl → l ≠ fl → o.applyA σ (clearL l) = σ (clearL l) := by
    intro l h1 h2
    exact frame_of_lists hfa hadd hdel
      (by simp [clearL, atRobot, atBox, h1]) (by simp [clearL, atRobot, atBox, h2]) σ
  have hrobot := robotAt_step hfa hp.domain hpreR (by rw [hdel]; simp) hnewR
    (by
      intro a hm hpred
      rw [hadd] at hm
      rcases (by simpa using hm : a = atRobot bl ∨ a = atBox b fl ∨ a = clearL bl)
        with rfl | rfl | rfl
      · rfl
      · exact absurd hpred (by simp [atBox])
      · exact absurd hpred (by simp [clearL])) happ hinv.robot
  refine ⟨hrobot, ?_, ?_, ?_, ?_⟩
  · intro b' l l' h1 h2
    by_cases hb' : b' = b
    · subst hb'
      rw [hkeyB l h1, hkeyB l' h2]
    · exact hinv.boxOne b' l l' (by rw [← hother b' l hb']; exact h1)
        (by rw [← hother b' l' hb']; exact h2)
  · intro b1 b2 l h1 h2
    by_cases hb1 : b1 = b
    · subst hb1
      by_cases hb2 : b2 = b1
      · exact hb2.symm
      · have hlf : l = fl := hkeyB l h1
        rw [hlf, hother b2 fl hb2] at h2
        rw [hinv.boxNotClear b2 fl h2] at hclearBefore
        exact absurd hclearBefore (by simp)
    · by_cases hb2 : b2 = b
      · subst hb2
        have hlf : l = fl := hkeyB l h2
        rw [hlf, hother b1 fl hb1] at h1
        rw [hinv.boxNotClear b1 fl h1] at hclearBefore
        exact absurd hclearBefore (by simp)
      · exact hinv.squareOne b1 b2 l (by rw [← hother b1 l hb1]; exact h1)
          (by rw [← hother b2 l hb2]; exact h2)
  · intro l hl
    have hlb : l = bl := hrobot.2 l bl hl hnewR
    rw [hlb]
    exact hnewC
  · intro b' l h1
    by_cases hb' : b' = b
    · subst hb'
      have hlf : l = fl := hkeyB l h1
      rw [hlf]
      exact hgoneC
    · have hbefore : σ (atBox b' l) = true := by rw [← hother b' l hb']; exact h1
      have hlbl : l ≠ bl := by
        intro hc
        rw [hc] at hbefore
        exact hb' (hinv.squareOne b' b bl hbefore hboxBefore)
      have hlfl : l ≠ fl := by
        intro hc
        rw [hc] at hbefore
        rw [hinv.boxNotClear b' fl hbefore] at hclearBefore
        exact absurd hclearBefore (by simp)
      rw [hclearOther l hlbl hlfl]
      exact hinv.boxNotClear b' l hbefore

/-- **Every Sokoban operator keeps it.** -/
theorem inv_step (hp : Pinned d p) (rel : Bool) (hfk : FrameAddsKept d p rel) :
    ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ → o.applicableA σ → Inv (o.applyA σ) := by
  intro o ho σ hinv happ
  obtain ⟨hfa⟩ := opFacts_ground d p rel ho
  rcases instance_shape hp.domain hfa.inst with
    ⟨f, t, dir, hs, ha⟩ | ⟨rl, bl, fl, dir, b, hs, ha⟩
  · exact move_inv hp rel ho hfk hfa hs ha hinv happ
  · exact push_inv hp rel ho hfk hfa hs ha hinv happ

end Planner.Lifted.Sokoban

/- -------------------------------------------------------------------------- -/
/-
Reading the robot's square and a box's square off a state.

Both are `(tbl.find? fun x => s.test x.1).map (·.2)` over a table of facts paired
with a square index, so `Proofs/FactTables.lean` does the state half.  What is
left is the table half — every entry is the fact of an `at-robot` or `at` atom,
indexed by the square that atom names — and the uniqueness half: `find?` returns
the *first* true entry, so it is the position only because one atom of the family
holds at a time, which is what `Inv` says.
-/

namespace Planner.Lifted.Sokoban

open Planner Planner.Pddl Planner.ExampleHeuristics.Sokoban

/-! ### The robot's table -/

theorem robotAt_eq (t : Task) :
    (compile t).robotAt = (t.factsWith "at-robot").filterMap fun x =>
      match x.2.args with
      | [l] => (locIx t l).map ((x.1, ·))
      | _ => none := rfl

/-- **Every entry names an `at-robot` atom, indexed by the square it names.** -/
theorem robotAt_data {t : Task} {e : Fact × Nat} (he : e ∈ (compile t).robotAt) :
    e.1 < t.factNames.size ∧ ∃ l, t.factNames.getD e.1 default = atRobot l ∧
      locIx t l = some e.2 := by
  rw [robotAt_eq] at he
  obtain ⟨x, -, hval, hlt, hname, hpred⟩ := mem_factsWith_filterMap he
  obtain ⟨f, a⟩ := x
  dsimp only at hval hlt hname hpred
  rcases hargs : a.args with _ | ⟨l, rest⟩
  · rw [hargs] at hval; simp at hval
  rcases rest with _ | ⟨q, rest⟩
  · rw [hargs] at hval
    dsimp only at hval
    obtain ⟨i, hi, hval'⟩ := Option.map_eq_some_iff.mp hval
    subst hval'
    refine ⟨hlt, l, ?_, hi⟩
    rw [hname]
    show a = atRobot l
    unfold atRobot
    rw [← hpred, ← hargs]
  · rw [hargs] at hval; simp at hval

/-- **And the atom of every `at-robot` fact has an entry**, as long as its square
is one of the squares the tables index. -/
theorem robotAt_mem {t : Task} {f : Fact} {l : Name} {i : Nat}
    (hf : (f, atRobot l) ∈ t.factsWith "at-robot") (hi : locIx t l = some i) :
    (f, i) ∈ (compile t).robotAt := by
  rw [robotAt_eq]
  refine Array.mem_filterMap.mpr ⟨(f, atRobot l), hf, ?_⟩
  show (match ([l] : List Name) with
    | [l] => (locIx t l).map ((f, ·))
    | _ => none) = some (f, i)
  simp [hi]

/-! ### The box tables -/

theorem boxAt_pred {t : Task} {facts : Array (Fact × Nat)}
    (hfacts : facts ∈ (compile t).boxAt) {e : Fact × Nat} (he : e ∈ facts) :
    e.1 < t.factNames.size ∧ ∃ b l, t.factNames.getD e.1 default = atBox b l ∧
      locIx t l = some e.2 := by
  obtain ⟨bn, -, hval⟩ := Array.mem_map.mp hfacts
  subst hval
  obtain ⟨x, -, hyval, hlt, hname, hpred⟩ := mem_factsWith_filterMap he
  obtain ⟨g, c⟩ := x
  dsimp only at hyval hlt hname hpred
  rcases hargs : c.args with _ | ⟨u, rest⟩
  · rw [hargs] at hyval; simp at hyval
  rcases rest with _ | ⟨l, rest⟩
  · rw [hargs] at hyval; simp at hyval
  rcases rest with _ | ⟨q, rest⟩
  case cons.cons.cons => rw [hargs] at hyval; simp at hyval
  rw [hargs] at hyval
  dsimp only at hyval
  by_cases hu : u == bn
  · rw [if_pos hu] at hyval
    obtain ⟨li, hli, hval'⟩ := Option.map_eq_some_iff.mp hyval
    subst hval'
    refine ⟨hlt, u, l, ?_, hli⟩
    rw [hname]
    show c = atBox u l
    unfold atBox
    rw [← hpred, ← hargs]
  · rw [if_neg hu] at hyval; simp at hyval

/-! ### Reading a position, given the invariant -/

variable {d : Domain} {p : Problem} {rel : Bool}

/-- **The robot's square is the one the table reports.**  The table holds an
entry for every numbered `at-robot` fact, and `Inv` says only one of them is
true. -/
theorem robotLoc_eq {s : State} {σ : AtomState} {l : Name} {i : Nat}
    (habs : Abstracts (ground d p rel) s σ)
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (hinv : Inv σ) (htrue : σ (atRobot l) = true)
    (hf : ∃ f, (f, atRobot l) ∈ (ground d p rel).factsWith "at-robot")
    (hi : locIx (ground d p rel) l = some i) :
    robotLoc (compile (ground d p rel)) s = some i := by
  obtain ⟨f, hfmem⟩ := hf
  have hentry : (f, i) ∈ (compile (ground d p rel)).robotAt := robotAt_mem hfmem hi
  have hok : ∀ y ∈ (compile (ground d p rel)).robotAt,
      y.1 < (ground d p rel).factNames.size := fun y hy => (robotAt_data hy).1
  rcases hfind : ((compile (ground d p rel)).robotAt).find?
      (fun y => s.test y.1) with _ | x
  · obtain ⟨-, hnameF, -⟩ := mem_factsWith hfmem
    have hfalse : σ ((ground d p rel).factNames.getD f default) = false :=
      find?_none_holds habs hn hok hfind (f, i) hentry
    rw [hnameF, htrue] at hfalse
    exact Bool.noConfusion hfalse
  · obtain ⟨hxmem, hxtrue⟩ := find?_holds habs hn hok hfind
    obtain ⟨-, l', hname, hi'⟩ := robotAt_data hxmem
    rw [hname] at hxtrue
    have hll : l' = l := hinv.robot.2 l' l hxtrue htrue
    rw [hll, hi] at hi'
    have hx2 : x.2 = i := by simpa using hi'.symm
    unfold robotLoc
    rw [hfind]
    simp [hx2]

/-! ### One box's tables -/

/-- **Everything a box entry holds**, in the terms the value's readers use: its
goal fact names `at(bn, g)`, its goal square is the index of `g`, its position
table is the `at` facts of `bn`, and its product table is the search over the
two graphs from `g`. -/
theorem boxes_data {bx : BoxInfo} (hb : bx ∈ (compile (ground d p rel)).boxes) :
    bx.goalFact < (ground d p rel).factNames.size ∧ ∃ bn g,
      (ground d p rel).factNames.getD bx.goalFact default = atBox bn g ∧
      locIx (ground d p rel) g = some bx.goalLoc ∧
      bx.atFacts = ((ground d p rel).factsWith "at").filterMap (fun x =>
        match x.2.args with
        | [y, l] => if y == bn then (locIx (ground d p rel) l).map ((x.1, ·)) else none
        | _ => none) ∧
      bx.jointDist = jointDistances (locsA (ground d p rel)).size
        (walkTable (ground d p rel)) (pushTable (ground d p rel)) bx.goalLoc := by
  obtain ⟨x, hx, hval⟩ := Array.mem_filterMap.mp hb
  obtain ⟨-, hlt, hget⟩ := Array.mem_zipIdx hx
  simp only [Nat.zero_add, Nat.sub_zero] at hlt hget
  obtain ⟨a, i⟩ := x
  dsimp only at hval hlt hget
  by_cases hp : (a.pred == "at") = true
  · rw [if_pos hp] at hval
    split at hval
    · rename_i bn g h1
      obtain ⟨gl, hgl, hval'⟩ := Option.map_eq_some_iff.mp hval
      subst hval'
      obtain ⟨hname, hfsz⟩ := goal_name_eq d p rel hlt
      refine ⟨hfsz, bn, g, ?_, hgl, rfl, rfl⟩
      show (ground d p rel).factNames.getD ((ground d p rel).goal.getD i 0) default = _
      rw [hname]
      show (ground d p rel).goalAtoms[i]'hlt = atBox bn g
      unfold atBox
      rw [← hget, ← eq_of_beq hp, ← h1]
    · simp at hval
  · rw [if_neg hp] at hval; simp at hval

/-- **Every entry of a box's position table is an `at` fact of that box**,
indexed by the square it names. -/
theorem boxes_atFacts_data {facts : Array (Fact × Nat)} {bn : Name}
    (hfacts : facts = ((ground d p rel).factsWith "at").filterMap (fun x =>
      match x.2.args with
      | [y, l] => if y == bn then (locIx (ground d p rel) l).map ((x.1, ·)) else none
      | _ => none))
    {e : Fact × Nat} (he : e ∈ facts) :
    e.1 < (ground d p rel).factNames.size ∧ ∃ l,
      (ground d p rel).factNames.getD e.1 default = atBox bn l ∧
      locIx (ground d p rel) l = some e.2 := by
  rw [hfacts] at he
  obtain ⟨y, -, hyval, hlt, hname, hpred⟩ := mem_factsWith_filterMap he
  obtain ⟨f, c⟩ := y
  dsimp only at hyval hlt hname hpred
  rcases hargs : c.args with _ | ⟨u, rest⟩
  · rw [hargs] at hyval; simp at hyval
  rcases rest with _ | ⟨l, rest⟩
  · rw [hargs] at hyval; simp at hyval
  rcases rest with _ | ⟨q, rest⟩
  case cons.cons.cons => rw [hargs] at hyval; simp at hyval
  rw [hargs] at hyval
  dsimp only at hyval
  by_cases hu : u == bn
  · rw [if_pos hu] at hyval
    obtain ⟨li, hli, hval'⟩ := Option.map_eq_some_iff.mp hyval
    subst hval'
    refine ⟨hlt, l, ?_, hli⟩
    rw [hname]
    show c = atBox bn l
    unfold atBox
    rw [← eq_of_beq hu, ← hpred, ← hargs]
  · rw [if_neg hu] at hyval; simp at hyval

/-- **And every `at` fact of that box has an entry.** -/
theorem boxes_atFacts_mem {facts : Array (Fact × Nat)} {bn l : Name} {f i : Nat}
    (hfacts : facts = ((ground d p rel).factsWith "at").filterMap (fun x =>
      match x.2.args with
      | [y, l] => if y == bn then (locIx (ground d p rel) l).map ((x.1, ·)) else none
      | _ => none))
    (hf : (f, atBox bn l) ∈ (ground d p rel).factsWith "at")
    (hi : locIx (ground d p rel) l = some i) : (f, i) ∈ facts := by
  rw [hfacts]
  refine Array.mem_filterMap.mpr ⟨(f, atBox bn l), hf, ?_⟩
  show (match ([bn, l] : List Name) with
    | [y, l] => if y == bn then (locIx (ground d p rel) l).map ((f, ·)) else none
    | _ => none) = some (f, i)
  simp [hi]

/-- **A box's square is the one its table reports.**  Stated over the raw table,
so that the `boxAt` bucket of a box object reads the same way a `boxes` entry
does. -/
theorem atFacts_find_eq {s : State} {σ : AtomState} {facts : Array (Fact × Nat)}
    {bn l : Name} {i : Nat}
    (habs : Abstracts (ground d p rel) s σ)
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (hinv : Inv σ)
    (hfacts : facts = ((ground d p rel).factsWith "at").filterMap (fun x =>
      match x.2.args with
      | [y, l] => if y == bn then (locIx (ground d p rel) l).map ((x.1, ·)) else none
      | _ => none))
    (htrue : σ (atBox bn l) = true)
    (hf : ∃ f, (f, atBox bn l) ∈ (ground d p rel).factsWith "at")
    (hi : locIx (ground d p rel) l = some i) :
    ∃ y, facts.find? (fun x => s.test x.1) = some y ∧ y.2 = i := by
  obtain ⟨f, hfmem⟩ := hf
  have hentry : (f, i) ∈ facts := boxes_atFacts_mem hfacts hfmem hi
  have hok : ∀ y ∈ facts, y.1 < (ground d p rel).factNames.size :=
    fun y hy => (boxes_atFacts_data hfacts hy).1
  rcases hfind : facts.find? (fun y => s.test y.1) with _ | x
  · obtain ⟨-, hnameF, -⟩ := mem_factsWith hfmem
    have hfalse : σ ((ground d p rel).factNames.getD f default) = false :=
      find?_none_holds habs hn hok hfind (f, i) hentry
    rw [hnameF, htrue] at hfalse
    exact Bool.noConfusion hfalse
  · obtain ⟨hxmem, hxtrue⟩ := find?_holds habs hn hok hfind
    obtain ⟨-, l', hname, hi'⟩ := boxes_atFacts_data hfacts hxmem
    rw [hname] at hxtrue
    have hll : l' = l := hinv.boxOne bn l' l hxtrue htrue
    rw [hll, hi] at hi'
    exact ⟨x, hfind, by simpa using hi'.symm⟩

/-- The `boxes` entry form. -/
theorem boxLoc_eq {s : State} {σ : AtomState} {bx : BoxInfo} {bn l : Name} {i : Nat}
    (habs : Abstracts (ground d p rel) s σ)
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (hinv : Inv σ)
    (hfacts : bx.atFacts = ((ground d p rel).factsWith "at").filterMap (fun x =>
      match x.2.args with
      | [y, l] => if y == bn then (locIx (ground d p rel) l).map ((x.1, ·)) else none
      | _ => none))
    (htrue : σ (atBox bn l) = true)
    (hf : ∃ f, (f, atBox bn l) ∈ (ground d p rel).factsWith "at")
    (hi : locIx (ground d p rel) l = some i) : boxLoc s bx = some i := by
  obtain ⟨y, hy, hy2⟩ := atFacts_find_eq habs hn hinv hfacts htrue hf hi
  unfold boxLoc
  rw [hy]
  simp [hy2]

end Planner.Lifted.Sokoban

/- -------------------------------------------------------------------------- -/
/-
The frame adds that pruning must keep.

`move` writes one atom, `at-robot ?to`, and the invariant needs it: an operator
that deleted the robot's old square without adding the new one would leave the
state with no robot at all.  `push` writes two the same way — the square the
robot steps into and the square the box leaves.

Grounding keeps all three, because neither schema reads what it adds.  The
relevance analysis is the question.  It keeps an add only of a *relevant* atom,
and an atom is relevant only when some operator that writes into the relevant set
reads it.  For `at-robot ?to` that operator is the move back out of `?to`: it
adds `at-robot ?from`, which is relevant because the operator we started from
reads it, and everything a kept operator reads is relevant.  That is the whole
argument, and it needs the map to step back, which `Pinned.adjReverses` says.

`clear ?bloc` then comes for free from the forward move, whose `at-robot ?bloc`
add the first half has just shown relevant.
-/

namespace Planner.Lifted.Sokoban

open Planner Planner.Pddl

variable {d : Domain} {p : Problem}

theorem array_any_of_mem {α : Type} {xs : Array α} {P : α → Bool} {x : α}
    (hx : x ∈ xs) (h : P x = true) : xs.any P = true := by
  rw [← Array.any_toList]
  exact List.any_eq_true.mpr ⟨x, by simpa using hx, h⟩

/-! ### A step of the map is an operator of the task -/

/-- The dynamic preconditions of a `move`, as the grounder filters them. -/
abbrev moveDyn (d : Domain) : List Atom :=
  moveA.pre.filter fun x => !(staticPredicates d).contains x.pred

/-- **Every edge of the map is a `move` of the unpruned task.** -/
theorem raw_move (hp : Pinned d p) {l1 l2 dd : Name}
    (hw1 : WellTyped d (allObjects d p) "location" l1)
    (hw2 : WellTyped d (allObjects d p) "location" l2)
    (hwd : WellTyped d (allObjects d p) "direction" dd)
    (hadj : adjacent l1 l2 dd ∈ p.init) :
    mkOp moveA (moveDyn d) #[l1, l2, dd] ∈ rawOps d p := by
  rw [← groundedOps_false]
  refine groundedOps_complete d p (a := moveA) (by rw [hp.domain]; simp) #[l1, l2, dd]
    rfl ?_ ?_ ?_
  · intro pm hpm
    simp only [moveA, List.mem_cons, List.not_mem_nil, or_false] at hpm
    rcases hpm with rfl | rfl | rfl
    · exact hp.locationType
    · exact hp.locationType
    · exact hp.directionType
  · show List.Forall₂ _ moveA.params [l1, l2, dd]
    exact List.Forall₂.cons hw1 (List.Forall₂.cons hw2
      (List.Forall₂.cons hwd List.Forall₂.nil))
  · intro y hy hst
    simp only [moveA, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl
    · rw [show (clearV "?to").pred = "clear" from rfl, clear_dynamic hp.domain] at hst
      exact absurd hst (by simp)
    · rw [show (atRobotV "?from").pred = "at-robot" from rfl,
        atRobot_dynamic hp.domain] at hst
      exact absurd hst (by simp)
    · exact hadj

/-! ### What a kept move makes relevant -/

/--
**Both ends of an edge are relevant once the far one is.**

The move adds `at-robot l2`, so if that atom is relevant the analysis keeps the
move, and then — the set being closed — everything the move reads is relevant:
the square the robot stands on and the square it steps onto.
-/
theorem move_reads_relevant (hp : Pinned d p) {r : Std.HashSet GroundAtom}
    (hclosed : Closed (rawOps d p) r) {l1 l2 dd : Name}
    (hw1 : WellTyped d (allObjects d p) "location" l1)
    (hw2 : WellTyped d (allObjects d p) "location" l2)
    (hwd : WellTyped d (allObjects d p) "direction" dd)
    (hadj : adjacent l1 l2 dd ∈ p.init)
    (h : r.contains (atRobot l2) = true) :
    r.contains (atRobot l1) = true ∧ r.contains (clearL l2) = true := by
  have hne : l1 ≠ l2 := by
    rintro rfl
    exact hp.noSelfAdjacent l1 dd hadj
  set op := mkOp moveA (moveDyn d) #[l1, l2, dd] with hop
  have hmem : op ∈ rawOps d p := raw_move hp hw1 hw2 hwd hadj
  have hadd : atRobot l2 ∈ op.add := by
    have heq : instAtom moveA.params (#[l1, l2, dd] : Array Name).toList
        (atRobotV "?to") = atRobot l2 := rfl
    rw [hop, ← heq]
    refine mem_mkOp_add moveA (moveDyn d) _ (by simp [moveA]) ?_
    intro z hz
    have hz' : z ∈ moveA.pre := (List.mem_filter.mp hz).1
    simp only [moveA, List.mem_cons, List.not_mem_nil, or_false] at hz'
    rcases hz' with rfl | rfl | rfl
    · show clearL l2 ≠ atRobot l2
      simp
    · show atRobot l1 ≠ atRobot l2
      simpa using hne
    · show adjacent l1 l2 dd ≠ atRobot l2
      simp [adjacent, atRobot]
  have htouch : op.touches r = true := by
    unfold AtomOp.touches
    rw [array_any_of_mem hadd h]
    rfl
  refine ⟨hclosed op hmem htouch (atRobot l1) ?_, hclosed op hmem htouch (clearL l2) ?_⟩
  · have heq : instAtom moveA.params (#[l1, l2, dd] : Array Name).toList
        (atRobotV "?from") = atRobot l1 := rfl
    rw [hop, ← heq]
    refine mem_mkOp_pre moveA (moveDyn d) _ (List.mem_filter.mpr ⟨by simp [moveA], ?_⟩)
    simp only [Bool.not_eq_true']
    exact atRobot_dynamic hp.domain
  · have heq : instAtom moveA.params (#[l1, l2, dd] : Array Name).toList
        (clearV "?to") = clearL l2 := rfl
    rw [hop, ← heq]
    refine mem_mkOp_pre moveA (moveDyn d) _ (List.mem_filter.mpr ⟨by simp [moveA], ?_⟩)
    simp only [Bool.not_eq_true']
    exact clear_dynamic hp.domain

/-! ### Reading an operator off any `OpFacts` for it -/

/-- A `move`'s static precondition is a fact of the map. -/
theorem move_adj_init (hp : Pinned d p) {o : AtomOp} (hf : OpFacts d p o)
    {frm dest dir : Name} (hs : hf.inst.schema = moveA)
    (ha : hf.inst.args = [frm, dest, dir]) : adjacent frm dest dir ∈ p.init := by
  have h := hf.staticHeld (adjacentV "?from" "?to" "?dir") (by rw [hs]; simp [moveA])
    (by rw [show (adjacentV "?from" "?to" "?dir").pred = "adjacent" from rfl]
        exact hp.adjacentStatic)
  rw [show instAtom hf.inst.schema.params hf.inst.args (adjacentV "?from" "?to" "?dir")
      = adjacent frm dest dir from by rw [hs, ha]; rfl] at h
  rw [Std.HashSet.contains_ofList] at h
  simpa using h

/-- A `push`'s two static preconditions are facts of the map. -/
theorem push_adj_init (hp : Pinned d p) {o : AtomOp} (hf : OpFacts d p o)
    {rl bl fl dir b : Name} (hs : hf.inst.schema = pushA)
    (ha : hf.inst.args = [rl, bl, fl, dir, b]) :
    adjacent rl bl dir ∈ p.init ∧ adjacent bl fl dir ∈ p.init := by
  constructor
  · have h := hf.staticHeld (adjacentV "?rloc" "?bloc" "?dir") (by rw [hs]; simp [pushA])
      (by rw [show (adjacentV "?rloc" "?bloc" "?dir").pred = "adjacent" from rfl]
          exact hp.adjacentStatic)
    rw [show instAtom hf.inst.schema.params hf.inst.args (adjacentV "?rloc" "?bloc" "?dir")
        = adjacent rl bl dir from by rw [hs, ha]; rfl] at h
    rw [Std.HashSet.contains_ofList] at h
    simpa using h
  · have h := hf.staticHeld (adjacentV "?bloc" "?floc" "?dir") (by rw [hs]; simp [pushA])
      (by rw [show (adjacentV "?bloc" "?floc" "?dir").pred = "adjacent" from rfl]
          exact hp.adjacentStatic)
    rw [show instAtom hf.inst.schema.params hf.inst.args (adjacentV "?bloc" "?floc" "?dir")
        = adjacent bl fl dir from by rw [hs, ha]; rfl] at h
    rw [Std.HashSet.contains_ofList] at h
    simpa using h

/-- A `move`'s arguments are objects of the declared types. -/
theorem move_wellTyped {o : AtomOp} (hf : OpFacts d p o) {frm dest dir : Name}
    (hs : hf.inst.schema = moveA) (ha : hf.inst.args = [frm, dest, dir]) :
    WellTyped d (allObjects d p) "location" frm ∧
    WellTyped d (allObjects d p) "location" dest ∧
    WellTyped d (allObjects d p) "direction" dir := by
  obtain ⟨o1, o2, o3, hargs, hw1, hw2, hw3⟩ := hf.inst.args_three
    (show hf.inst.schema.params = [locP "?from", locP "?to", dirP "?dir"] by rw [hs])
  rw [ha] at hargs
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨e1, e2, e3⟩ := hargs
  rw [← e1] at hw1
  rw [← e2] at hw2
  rw [← e3] at hw3
  exact ⟨hw1, hw2, hw3⟩

/-- And so are a `push`'s. -/
theorem push_wellTyped {o : AtomOp} (hf : OpFacts d p o) {rl bl fl dir b : Name}
    (hs : hf.inst.schema = pushA) (ha : hf.inst.args = [rl, bl, fl, dir, b]) :
    WellTyped d (allObjects d p) "location" rl ∧
    WellTyped d (allObjects d p) "location" bl ∧
    WellTyped d (allObjects d p) "direction" dir := by
  obtain ⟨o1, o2, o3, o4, o5, hargs, hw1, hw2, -, hw4, -⟩ := hf.inst.args_five
    (show hf.inst.schema.params
      = [locP "?rloc", locP "?bloc", locP "?floc", dirP "?dir", boxP "?b"] by rw [hs])
  rw [ha] at hargs
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨e1, e2, -, e4, -⟩ := hargs
  rw [← e1] at hw1
  rw [← e2] at hw2
  rw [← e4] at hw4
  exact ⟨hw1, hw2, hw4⟩

/-! ### The adds the grounder keeps -/

/--
**A `move` keeps its `at-robot` add through grounding.**

The schema does not read what it adds — the square the robot steps onto is not
the one it stands on — so the grounder emits the add.  Stated for an arbitrary
reading of the operator, because the invariant proof brings one of its own; two
readings of the same operator agree on the squares, since each one's dynamic
preconditions are the other's.
-/
theorem move_add_raw (hp : Pinned d p) {op o : AtomOp} (hop : op ∈ rawOps d p)
    (hpre : o.pre = op.pre) (hf : OpFacts d p o) {frm dest dir : Name}
    (hs : hf.inst.schema = moveA) (ha : hf.inst.args = [frm, dest, dir]) :
    atRobot dest ∈ op.add := by
  have hfpre : hf.inst.pre = [clearL dest, atRobot frm, adjacent frm dest dir] := by
    rw [hf.inst.pre_eq, hs, ha]; rfl
  have hsub : ∀ a ∈ op.pre, a ∈ hf.inst.pre := by
    intro a haa
    exact hf.subPre a (by rw [hpre]; exact haa)
  have hne : frm ≠ dest := by
    rintro rfl
    exact hp.noSelfAdjacent frm dir (move_adj_init hp hf hs ha)
  obtain ⟨hfa⟩ := opFacts_raw_add d p hop
  rcases instance_shape hp.domain hfa.inst with
    ⟨f', t', dd', hs', ha'⟩ | ⟨rl', bl', fl', dd', b', hs', ha'⟩
  · have hclEq : instAtom hfa.inst.schema.params hfa.inst.args (clearV "?to")
        = clearL t' := by rw [hs', ha']; rfl
    have hatEq : instAtom hfa.inst.schema.params hfa.inst.args (atRobotV "?to")
        = atRobot t' := by rw [hs', ha']; rfl
    have hcl : clearL t' ∈ op.pre := by
      have h := hfa.preComplete (clearV "?to") (by rw [hs']; simp [moveA])
        (by rw [show (clearV "?to").pred = "clear" from rfl]
            exact clear_dynamic hp.domain)
      rwa [hclEq] at h
    have htd : t' = dest := by
      have h := hsub _ hcl
      rw [hfpre] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h
      · simpa using h
      · exact absurd h (by simp [clearL, atRobot])
      · exact absurd h (by simp [clearL, adjacent])
    have hnp : instAtom hfa.inst.schema.params hfa.inst.args (atRobotV "?to") ∉ op.pre := by
      rw [hatEq, htd]
      intro hc
      have h := hsub _ hc
      rw [hfpre] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h
      · exact absurd h (by simp [clearL, atRobot])
      · have hdf : dest = frm := by simpa using h
        exact hne hdf.symm
      · exact absurd h (by simp [atRobot, adjacent])
    have h := hfa.addComplete (atRobotV "?to") (by rw [hs']; simp [moveA]) hnp
    rwa [hatEq, htd] at h
  · exfalso
    have hboxEq : instAtom hfa.inst.schema.params hfa.inst.args (atBoxV "?b" "?bloc")
        = atBox b' bl' := by rw [hs', ha']; rfl
    have hbox : atBox b' bl' ∈ op.pre := by
      have h := hfa.preComplete (atBoxV "?b" "?bloc") (by rw [hs']; simp [pushA])
        (by rw [show (atBoxV "?b" "?bloc").pred = "at" from rfl]
            exact atBox_dynamic hp.domain)
      rwa [hboxEq] at h
    have h := hsub _ hbox
    rw [hfpre] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h
    · exact absurd h (by simp [atBox, clearL])
    · exact absurd h (by simp [atBox, atRobot])
    · exact absurd h (by simp [atBox, adjacent])

/-- **A `push` keeps both of its frame adds** — the square the robot steps into
and the square the box leaves — for the same reason. -/
theorem push_add_raw (hp : Pinned d p) {op o : AtomOp} (hop : op ∈ rawOps d p)
    (hpre : o.pre = op.pre) (hf : OpFacts d p o) {rl bl fl dir b : Name}
    (hs : hf.inst.schema = pushA) (ha : hf.inst.args = [rl, bl, fl, dir, b]) :
    atRobot bl ∈ op.add ∧ clearL bl ∈ op.add := by
  have hfpre : hf.inst.pre = [atRobot rl, atBox b bl, clearL fl,
      adjacent rl bl dir, adjacent bl fl dir] := by
    rw [hf.inst.pre_eq, hs, ha]; rfl
  have hsub : ∀ a ∈ op.pre, a ∈ hf.inst.pre := by
    intro a haa
    exact hf.subPre a (by rw [hpre]; exact haa)
  obtain ⟨hadj1, hadj2⟩ := push_adj_init hp hf hs ha
  have hne1 : bl ≠ rl := by
    rintro rfl
    exact hp.noSelfAdjacent bl dir hadj1
  have hne2 : bl ≠ fl := by
    rintro rfl
    exact hp.noSelfAdjacent bl dir hadj2
  obtain ⟨hfa⟩ := opFacts_raw_add d p hop
  rcases instance_shape hp.domain hfa.inst with
    ⟨f', t', dd', hs', ha'⟩ | ⟨rl', bl', fl', dd', b', hs', ha'⟩
  · exfalso
    have hboxEq : instAtom hf.inst.schema.params hf.inst.args (atBoxV "?b" "?bloc")
        = atBox b bl := by rw [hs, ha]; rfl
    have hbox : atBox b bl ∈ op.pre := by
      have h := hf.preComplete (atBoxV "?b" "?bloc") (by rw [hs]; simp [pushA])
        (by rw [show (atBoxV "?b" "?bloc").pred = "at" from rfl]
            exact atBox_dynamic hp.domain)
      rw [hboxEq] at h
      rwa [hpre] at h
    have hfapre : hfa.inst.pre = [clearL t', atRobot f', adjacent f' t' dd'] := by
      rw [hfa.inst.pre_eq, hs', ha']; rfl
    have h := hfa.subPre _ hbox
    rw [hfapre] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h
    · exact absurd h (by simp [atBox, clearL])
    · exact absurd h (by simp [atBox, atRobot])
    · exact absurd h (by simp [atBox, adjacent])
  · have hboxEq : instAtom hfa.inst.schema.params hfa.inst.args (atBoxV "?b" "?bloc")
        = atBox b' bl' := by rw [hs', ha']; rfl
    have hatEq : instAtom hfa.inst.schema.params hfa.inst.args (atRobotV "?bloc")
        = atRobot bl' := by rw [hs', ha']; rfl
    have hclEq : instAtom hfa.inst.schema.params hfa.inst.args (clearV "?bloc")
        = clearL bl' := by rw [hs', ha']; rfl
    have hbox : atBox b' bl' ∈ op.pre := by
      have h := hfa.preComplete (atBoxV "?b" "?bloc") (by rw [hs']; simp [pushA])
        (by rw [show (atBoxV "?b" "?bloc").pred = "at" from rfl]
            exact atBox_dynamic hp.domain)
      rwa [hboxEq] at h
    have hbl : bl' = bl := by
      have h := hsub _ hbox
      rw [hfpre] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h | h
      · exact absurd h (by simp [atBox, atRobot])
      · have hbb : b' = b ∧ bl' = bl := by simpa using h
        exact hbb.2
      · exact absurd h (by simp [atBox, clearL])
      · exact absurd h (by simp [atBox, adjacent])
      · exact absurd h (by simp [atBox, adjacent])
    constructor
    · have hnp : instAtom hfa.inst.schema.params hfa.inst.args (atRobotV "?bloc")
          ∉ op.pre := by
        rw [hatEq, hbl]
        intro hc
        have h := hsub _ hc
        rw [hfpre] at h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h | h | h | h
        · have hbr : bl = rl := by simpa using h
          exact hne1 hbr
        · exact absurd h (by simp [atRobot, atBox])
        · exact absurd h (by simp [atRobot, clearL])
        · exact absurd h (by simp [atRobot, adjacent])
        · exact absurd h (by simp [atRobot, adjacent])
      have h := hfa.addComplete (atRobotV "?bloc") (by rw [hs']; simp [pushA]) hnp
      rwa [hatEq, hbl] at h
    · have hnp : instAtom hfa.inst.schema.params hfa.inst.args (clearV "?bloc")
          ∉ op.pre := by
        rw [hclEq, hbl]
        intro hc
        have h := hsub _ hc
        rw [hfpre] at h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h | h | h | h
        · exact absurd h (by simp [clearL, atRobot])
        · exact absurd h (by simp [clearL, atBox])
        · have hbf : bl = fl := by simpa using h
          exact hne2 hbf
        · exact absurd h (by simp [clearL, adjacent])
        · exact absurd h (by simp [clearL, adjacent])
      have h := hfa.addComplete (clearV "?bloc") (by rw [hs']; simp [pushA]) hnp
      rwa [hclEq, hbl] at h

/-! ### The frame adds survive the relevance analysis -/

/--
**Sokoban's frame adds are kept, with pruning on or off.**

With pruning off there is nothing beyond grounding to show.  With pruning on, the
square the operator reads is relevant, because a kept operator reads only
relevant atoms; the move back carries that to the square the operator writes; and
the move forward then carries it to the square itself.
-/
theorem frameAddsKept (hp : Pinned d p) (rel : Bool) : FrameAddsKept d p rel := by
  cases rel with
  | false =>
      intro o ho hf
      have hop : o ∈ rawOps d p := by rwa [← groundedOps_false]
      exact ⟨fun frm dest dir hs ha => move_add_raw hp hop rfl hf hs ha,
        fun rl bl fl dir b hs ha => push_add_raw hp hop rfl hf hs ha⟩
  | true =>
      intro o ho hf
      rcases relevance_cases (rawOps d p) p.goal.toArray with
        ⟨r, hclosed, hgoal, hrdef⟩ | hall
      · obtain ⟨op, hop, hval, hrel, -⟩ := pruned_op ho hclosed hrdef
        subst hval
        have hpre : (op.trim r).pre = op.pre := rfl
        constructor
        · intro frm dest dir hs ha
          have hraw : atRobot dest ∈ op.add := move_add_raw hp hop hpre hf hs ha
          have hatEq : instAtom hf.inst.schema.params hf.inst.args (atRobotV "?from")
              = atRobot frm := by rw [hs, ha]; rfl
          have hfrm : atRobot frm ∈ op.pre := by
            have h := hf.preComplete (atRobotV "?from") (by rw [hs]; simp [moveA])
              (by rw [show (atRobotV "?from").pred = "at-robot" from rfl]
                  exact atRobot_dynamic hp.domain)
            rw [hatEq] at h
            rwa [hpre] at h
          have hrfrm : r.contains (atRobot frm) = true := hrel _ hfrm
          obtain ⟨hw1, hw2, -⟩ := move_wellTyped hf hs ha
          obtain ⟨dd', hwd', hadj'⟩ :=
            hp.adjReverses frm dest dir (move_adj_init hp hf hs ha)
          have hrdest : r.contains (atRobot dest) = true :=
            (move_reads_relevant hp hclosed hw2 hw1 hwd' hadj' hrfrm).1
          show atRobot dest ∈ op.add.filter r.contains
          exact Array.mem_filter.mpr ⟨hraw, hrdest⟩
        · intro rl bl fl dir b hs ha
          obtain ⟨hraw1, hraw2⟩ := push_add_raw hp hop hpre hf hs ha
          have hatEq : instAtom hf.inst.schema.params hf.inst.args (atRobotV "?rloc")
              = atRobot rl := by rw [hs, ha]; rfl
          have hrl : atRobot rl ∈ op.pre := by
            have h := hf.preComplete (atRobotV "?rloc") (by rw [hs]; simp [pushA])
              (by rw [show (atRobotV "?rloc").pred = "at-robot" from rfl]
                  exact atRobot_dynamic hp.domain)
            rw [hatEq] at h
            rwa [hpre] at h
          have hrrl : r.contains (atRobot rl) = true := hrel _ hrl
          obtain ⟨hw1, hw2, hwd⟩ := push_wellTyped hf hs ha
          obtain ⟨hadj1, -⟩ := push_adj_init hp hf hs ha
          obtain ⟨dd', hwd', hadj'⟩ := hp.adjReverses rl bl dir hadj1
          have hrbl : r.contains (atRobot bl) = true :=
            (move_reads_relevant hp hclosed hw2 hw1 hwd' hadj' hrrl).1
          have hrcl : r.contains (clearL bl) = true :=
            (move_reads_relevant hp hclosed hw1 hw2 hwd hadj1 hrbl).2
          refine ⟨?_, ?_⟩
          · show atRobot bl ∈ op.add.filter r.contains
            exact Array.mem_filter.mpr ⟨hraw1, hrbl⟩
          · show clearL bl ∈ op.add.filter r.contains
            exact Array.mem_filter.mpr ⟨hraw2, hrcl⟩
      · have heq : groundedOps d p true = rawOps d p := by rw [groundedOps_true, hall]
        rw [heq] at ho
        exact ⟨fun frm dest dir hs ha => move_add_raw hp ho rfl hf hs ha,
          fun rl bl fl dir b hs ha => push_add_raw hp ho rfl hf hs ha⟩

end Planner.Lifted.Sokoban

/- -------------------------------------------------------------------------- -/
/-
One box's product distance, across one action.

`jointOf` reads the *(box square, robot square)* table at the two positions the
state reports.  A `move` shifts the robot alone, a `push` of this box shifts both,
and a `push` of some other box shifts the robot onto the square that box left —
and each of those is one edge of the product graph `jointSucc` names.  So the
entry falls by at most one, which is `MoveStep.jointStep` and `PushStep.jointStep`.

The table is trusted through `jointCheck`, not through a proof that the search
that built it is optimal; `JointChecked` is that check on every box of the task.
-/

namespace Planner.Lifted.Sokoban

open Planner Planner.Pddl Planner.ExampleHeuristics.Sokoban

variable {d : Domain} {p : Problem} {rel : Bool}

/-! ### The compiled sizes -/

theorem compile_unreachable (t : Task) :
    (compile t).unreachable = (locsA t).size * (locsA t).size := rfl

/-- Every box's product table passes its check. -/
def JointChecked (d : Domain) (p : Problem) (rel : Bool) : Prop :=
  ∀ bx ∈ (compile (ground d p rel)).boxes,
    jointCheck (locsA (ground d p rel)).size (walkTable (ground d p rel))
      (pushTable (ground d p rel)) bx.goalLoc bx.jointDist = true

/-- Every compiled product table passes its check by construction. -/
theorem jointChecked (d : Domain) (p : Problem) (rel : Bool) : JointChecked d p rel := by
  intro bx hbx
  obtain ⟨-, bn, g, -, hg, -, hjoint⟩ := boxes_data hbx
  rw [hjoint]
  exact jointCheck_distances _ _ _ _ (locIx_lt hg)

/-! ### Reading a position back to a name -/

theorem robotLoc_some {s : State} {σ : AtomState} {r : Nat}
    (habs : Abstracts (ground d p rel) s σ)
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (h : robotLoc (compile (ground d p rel)) s = some r) :
    ∃ l f, σ (atRobot l) = true ∧ locIx (ground d p rel) l = some r ∧
      (f, atRobot l) ∈ (ground d p rel).factsWith "at-robot" := by
  have hok : ∀ y ∈ (compile (ground d p rel)).robotAt,
      y.1 < (ground d p rel).factNames.size := fun y hy => (robotAt_data hy).1
  unfold robotLoc at h
  rcases hfind : ((compile (ground d p rel)).robotAt).find?
      (fun y => s.test y.1) with _ | x
  · rw [hfind] at h; simp at h
  · rw [hfind] at h
    obtain ⟨hxmem, hxtrue⟩ := find?_holds habs hn hok hfind
    obtain ⟨hxlt, l, hname, hi⟩ := robotAt_data hxmem
    rw [hname] at hxtrue
    have hxr : x.2 = r := by simpa using h
    exact ⟨l, x.1, hxtrue, by rw [hi, hxr], mem_factsWith_of_named hxlt hname rfl⟩

theorem boxLoc_some {s : State} {σ : AtomState} {bx : BoxInfo} {bn : Name} {li : Nat}
    (habs : Abstracts (ground d p rel) s σ)
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (hfacts : bx.atFacts = ((ground d p rel).factsWith "at").filterMap (fun x =>
      match x.2.args with
      | [y, l] => if y == bn then (locIx (ground d p rel) l).map ((x.1, ·)) else none
      | _ => none))
    (h : boxLoc s bx = some li) :
    ∃ l f, σ (atBox bn l) = true ∧ locIx (ground d p rel) l = some li ∧
      (f, atBox bn l) ∈ (ground d p rel).factsWith "at" := by
  have hok : ∀ y ∈ bx.atFacts, y.1 < (ground d p rel).factNames.size :=
    fun y hy => (boxes_atFacts_data hfacts hy).1
  unfold boxLoc at h
  rcases hfind : (bx.atFacts).find? (fun y => s.test y.1) with _ | x
  · rw [hfind] at h; simp at h
  · rw [hfind] at h
    obtain ⟨hxmem, hxtrue⟩ := find?_holds habs hn hok hfind
    obtain ⟨hxlt, l, hname, hi⟩ := boxes_atFacts_data hfacts hxmem
    rw [hname] at hxtrue
    have hxr : x.2 = li := by simpa using h
    exact ⟨l, x.1, hxtrue, by rw [hi, hxr], mem_factsWith_of_named hxlt hname rfl⟩

/-! ### The value at a state whose two positions are known -/

theorem jointOf_some {t : Task} {s : State} {bx : BoxInfo} {li ri : Nat}
    (hb : boxLoc s bx = some li) (hr : robotLoc (compile t) s = some ri) :
    jointOf (compile t) s bx
      = bx.jointDist.getD (li * (locsA t).size + ri)
        ((locsA t).size * (locsA t).size) := by
  unfold jointOf
  rw [hr, hb]
  rfl

/-- With the robot's square missing the value is zero, which underestimates
anything. -/
theorem jointOf_robot_none {t : Task} {s : State} {bx : BoxInfo}
    (h : robotLoc (compile t) s = none) : jointOf (compile t) s bx = 0 := by
  unfold jointOf
  rw [h]

/--
With the box's square missing the value is the cap.

The state records no position for the box, so no `push` of it is applicable —
every push reads an `at` fact of its own box — and its goal is out of reach for
good.  The cap is a lower bound on that, and reading zero there would let the
value fall by the whole table in one step.
-/
theorem jointOf_box_none {t : Task} {s : State} {bx : BoxInfo} {ri : Nat}
    (hr : robotLoc (compile t) s = some ri) (h : boxLoc s bx = none) :
    jointOf (compile t) s bx = (locsA t).size * (locsA t).size := by
  unfold jointOf
  rw [hr, h]
  rfl

/-- And never more than the cap. -/
theorem jointOf_le_bound {t : Task} {s : State} {bx : BoxInfo}
    (hjs : JointSound (locsA t).size (walkTable t) (pushTable t) bx.goalLoc bx.jointDist) :
    jointOf (compile t) s bx ≤ (locsA t).size * (locsA t).size := by
  unfold jointOf
  rcases hr : robotLoc (compile t) s with _ | ri
  · exact Nat.zero_le _
  · rcases hb : boxLoc s bx with _ | li
    · exact Nat.le_refl _
    · exact hjs.le_bound _

/-! ### The two argument-index lemmas -/

theorem move_arg_indices (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (hf : OpFacts d p o) {frm dest dir : Name}
    (hs : hf.inst.schema = moveA) (ha : hf.inst.args = [frm, dest, dir]) :
    ∃ ui vi, locIx (ground d p rel) frm = some ui ∧
      locIx (ground d p rel) dest = some vi := by
  obtain ⟨a1, a2, a3, ha', hw1, hw2, -⟩ :=
    hf.inst.args_three (show hf.inst.schema.params
      = [locP "?from", locP "?to", dirP "?dir"] by rw [hs])
  rw [ha] at ha'
  obtain ⟨rfl, rfl, rfl⟩ : frm = a1 ∧ dest = a2 ∧ dir = a3 := by simpa using ha'
  obtain ⟨ui, hlrIx⟩ :=
    locIx_total (t := ground d p rel) (mem_objsOf_of_wellTyped hp.locTypeExact hw1)
  obtain ⟨vi, hvi⟩ :=
    locIx_total (t := ground d p rel) (mem_objsOf_of_wellTyped hp.locTypeExact hw2)
  exact ⟨ui, vi, hlrIx, hvi⟩

theorem push_arg_indices (hp : Pinned d p) (rel : Bool) {o : AtomOp}
    (hf : OpFacts d p o) {rl bl fl dir b : Name}
    (hs : hf.inst.schema = pushA) (ha : hf.inst.args = [rl, bl, fl, dir, b]) :
    ∃ ri bi fi, locIx (ground d p rel) rl = some ri ∧
      locIx (ground d p rel) bl = some bi ∧ locIx (ground d p rel) fl = some fi := by
  obtain ⟨a1, a2, a3, a4, a5, ha', hw1, hw2, hw3, -, -⟩ :=
    hf.inst.args_five (show hf.inst.schema.params
      = [locP "?rloc", locP "?bloc", locP "?floc", dirP "?dir", boxP "?b"]
      by rw [hs])
  rw [ha] at ha'
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ :
      rl = a1 ∧ bl = a2 ∧ fl = a3 ∧ dir = a4 ∧ b = a5 := by simpa using ha'
  obtain ⟨ri, hri⟩ :=
    locIx_total (t := ground d p rel) (mem_objsOf_of_wellTyped hp.locTypeExact hw1)
  obtain ⟨bi, hbi⟩ :=
    locIx_total (t := ground d p rel) (mem_objsOf_of_wellTyped hp.locTypeExact hw2)
  obtain ⟨fi, hfi⟩ :=
    locIx_total (t := ground d p rel) (mem_objsOf_of_wellTyped hp.locTypeExact hw3)
  exact ⟨ri, bi, fi, hri, hbi, hfi⟩

/-! ### Numbering an atom an operator mentions -/

theorem factsWith_of_op {o : AtomOp} (ho : o ∈ groundedOps d p rel) {a : GroundAtom}
    (ha : a ∈ o.pre ∨ a ∈ o.add ∨ a ∈ o.del) {pred : Name} (hpred : a.pred = pred) :
    ∃ f, (f, a) ∈ (ground d p rel).factsWith pred := by
  obtain ⟨f, hlt, hname⟩ := numbered_of_op d p rel ho ha
  exact ⟨f, mem_factsWith_of_named hlt hname hpred⟩

/-! ### `move` -/

set_option maxHeartbeats 1000000 in
/-- **`MoveStep.jointStep`.**  A robot step onto a square no box stands on is an
edge of every box's product graph, so every box's entry falls by at most one. -/
theorem move_jointStep (hp : Pinned d p) (hjc : JointChecked d p rel)
    (hfk : FrameAddsKept d p rel) {o : AtomOp}
    (ho : o ∈ groundedOps d p rel) (hfa : OpFacts d p o) {frm dest dir : Name}
    (hs : hfa.inst.schema = moveA) (ha : hfa.inst.args = [frm, dest, dir])
    {s s' : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (habs' : Abstracts (ground d p rel) s' (o.applyA σ))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (hinv : Inv σ) (happ : o.applicableA σ) :
    ∀ bx ∈ unmetBoxes (compile (ground d p rel)) s,
      (bx ∈ unmetBoxes (compile (ground d p rel)) s' ∧
        jointOf (compile (ground d p rel)) s bx ≤
          1 + jointOf (compile (ground d p rel)) s' bx) ∨
      jointOf (compile (ground d p rel)) s bx ≤ 1 := by
  intro bx hbx
  have hbxmem : bx ∈ (compile (ground d p rel)).boxes := (Array.mem_filter.mp hbx).1
  have hunmet' : unmetBoxes (compile (ground d p rel)) s'
      = unmetBoxes (compile (ground d p rel)) s :=
    unmetBoxes_congr (move_goalsSame hfa hs ha habs habs' hn)
  left
  refine ⟨by rw [hunmet']; exact hbx, ?_⟩
  rcases hrl : robotLoc (compile (ground d p rel)) s with _ | ri
  · rw [jointOf_robot_none hrl]; omega
  rcases hbl : boxLoc s bx with _ | li
  · -- the box has no square, and a walk cannot give it one
    have hbl' : boxLoc s' bx = none := by
      rw [move_boxSame hfa hs ha habs habs' hn bx hbxmem]; exact hbl
    have hinv0 : Inv (o.applyA σ) := move_inv hp rel ho hfk hfa hs ha hinv happ
    obtain ⟨-, vi0, -, hvi0⟩ := move_arg_indices hp rel hfa hs ha
    have hrl0 : robotLoc (compile (ground d p rel)) s' = some vi0 :=
      robotLoc_eq habs' hn hinv0 (move_robot_after ho hfk hfa hs ha σ)
        (factsWith_of_op ho (Or.inr (Or.inl (move_robot_add ho hfk hfa hs ha))) rfl) hvi0
    rw [jointOf_box_none hrl hbl, jointOf_box_none hrl0 hbl']
    omega
  -- names for the two positions
  obtain ⟨-, bn, g, -, -, hfacts, -⟩ := boxes_data hbxmem
  obtain ⟨lb, -, hlbTrue, hlbIx, -⟩ := boxLoc_some habs hn hfacts hbl
  obtain ⟨lr, -, hlrTrue, hlrIx, -⟩ := robotLoc_some habs hn hrl
  obtain ⟨hpreR, hadd, hdel⟩ := move_atoms hfa.inst hs ha
  have hpreEq : hfa.inst.pre = [clearL dest, atRobot frm, adjacent frm dest dir] := by
    rw [hfa.inst.pre_eq, hs, ha]; rfl
  have hrobotBefore : σ (atRobot frm) = true :=
    pre_holds hfa hpreR (atRobot_dynamic hp.domain) happ
  have hclearDest : σ (clearL dest) = true :=
    pre_holds hfa (a := clearL dest) (by rw [hpreEq]; simp)
      (clear_dynamic hp.domain) happ
  have hlrfrm : lr = frm := hinv.robot.2 lr frm hlrTrue hrobotBefore
  rw [hlrfrm] at hlrIx
  obtain ⟨-, vi, -, hvi⟩ := move_arg_indices hp rel hfa hs ha
  -- the two positions afterwards
  have hbl' : boxLoc s' bx = some li := by
    rw [move_boxSame hfa hs ha habs habs' hn bx hbxmem]; exact hbl
  have hinv' : Inv (o.applyA σ) := move_inv hp rel ho hfk hfa hs ha hinv happ
  have hrl' : robotLoc (compile (ground d p rel)) s' = some vi := by
    refine robotLoc_eq habs' hn hinv' (move_robot_after ho hfk hfa hs ha σ) ?_ hvi
    exact factsWith_of_op ho (Or.inr (Or.inl (move_robot_add ho hfk hfa hs ha))) rfl
  rw [jointOf_some hbl hrl, jointOf_some hbl' hrl']
  -- the product edge
  have hlbNe : frm ≠ lb := hinv.robot_ne_box hlbTrue hrobotBefore
  have hriNe : ri ≠ li := by
    intro hc
    exact hlbNe (locIx_inj (t := ground d p rel) hlrIx (by rw [← hc] at hlbIx; exact hlbIx))
  have hdestNe : dest ≠ lb := by
    intro hc
    rw [hc] at hclearDest
    rw [hinv.boxNotClear bn lb hlbTrue] at hclearDest
    exact Bool.noConfusion hclearDest
  have hviNe : vi ≠ li := by
    intro hc
    exact hdestNe (locIx_inj (t := ground d p rel) hvi (by rw [← hc] at hlbIx; exact hlbIx))
  have hstep : vi ∈ (walkTable (ground d p rel)).getD ri #[] :=
    mem_walkTable _ (move_adjacent hp rel hfa hs ha) hlrIx hvi
  have hedge : li * (locsA (ground d p rel)).size + vi
      ∈ jointSucc (locsA (ground d p rel)).size (walkTable (ground d p rel))
        (pushTable (ground d p rel)) li ri :=
    mem_jointSucc_move hriNe hviNe hstep
  exact (jointSound_of_check (hjc bx hbxmem)).step li ri (locIx_lt hlbIx)
    (locIx_lt hlrIx) _ hedge

/-! ### What a push leaves alone -/

/-- A box the push does not move keeps its goal and its square. -/
theorem push_frames_other (hp : Pinned d p) {o : AtomOp} (hfa : OpFacts d p o)
    {rl bl fl dir b : Name} (hs : hfa.inst.schema = pushA)
    (ha : hfa.inst.args = [rl, bl, fl, dir, b])
    {s s' : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (habs' : Abstracts (ground d p rel) s' (o.applyA σ))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    {bx : BoxInfo} {bn g : Name}
    (hgoalLt : bx.goalFact < (ground d p rel).factNames.size)
    (hgname : (ground d p rel).factNames.getD bx.goalFact default = atBox bn g)
    (hfacts : bx.atFacts = ((ground d p rel).factsWith "at").filterMap (fun x =>
      match x.2.args with
      | [y, l] => if y == bn then (locIx (ground d p rel) l).map ((x.1, ·)) else none
      | _ => none))
    (hne : bn ≠ b) :
    s'.test bx.goalFact = s.test bx.goalFact ∧ boxLoc s' bx = boxLoc s bx := by
  obtain ⟨-, -, -, hadd, hdel⟩ := push_atoms hfa.inst hs ha
  have hframe : ∀ l : Name, o.applyA σ (atBox bn l) = σ (atBox bn l) := fun l =>
    frame_of_lists hfa hadd hdel
      (by simp [atBox, atRobot, clearL, hne]) (by simp [atBox, atRobot, clearL, hne]) σ
  constructor
  · rw [← habs'.numbered bx.goalFact (by rw [hn]; exact hgoalLt),
      ← habs.numbered bx.goalFact (by rw [hn]; exact hgoalLt), hgname, hframe]
  · unfold boxLoc
    refine congrArg _ (array_find?_congr _ _ _ fun y hy => ?_)
    obtain ⟨hlt, l, hname, -⟩ := boxes_atFacts_data hfacts hy
    rw [← habs'.numbered y.1 (by rw [hn]; exact hlt),
      ← habs.numbered y.1 (by rw [hn]; exact hlt), hname, hframe]

/-! ### `push` -/

set_option maxHeartbeats 1000000 in
/-- **`PushStep.jointStep`.**  For the box being pushed the product edge is the
push itself; for every other box it is the robot step onto the square the pushed
box left.  And a push that puts a box home leaves that box's entry at one, which
is what the second disjunct records. -/
theorem push_jointStep (hp : Pinned d p) (hjc : JointChecked d p rel)
    (hfk : FrameAddsKept d p rel) {o : AtomOp}
    (ho : o ∈ groundedOps d p rel) (hfa : OpFacts d p o) {rl bl fl dir b : Name}
    (hs : hfa.inst.schema = pushA) (ha : hfa.inst.args = [rl, bl, fl, dir, b])
    {s s' : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (habs' : Abstracts (ground d p rel) s' (o.applyA σ))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (hinv : Inv σ) (happ : o.applicableA σ) :
    ∀ bx ∈ unmetBoxes (compile (ground d p rel)) s,
      (bx ∈ unmetBoxes (compile (ground d p rel)) s' ∧
        jointOf (compile (ground d p rel)) s bx ≤
          1 + jointOf (compile (ground d p rel)) s' bx) ∨
      jointOf (compile (ground d p rel)) s bx ≤ 1 := by
  intro bx hbx
  have hbxmem : bx ∈ (compile (ground d p rel)).boxes := (Array.mem_filter.mp hbx).1
  have hbxUnmet : s.test bx.goalFact = false := by
    have := (Array.mem_filter.mp hbx).2
    simpa using this
  obtain ⟨hgoalLt, bn, g, hgname, hgIx, hfacts, -⟩ := boxes_data hbxmem
  obtain ⟨hpreR, hpreB, hpreC, hadd, hdel⟩ := push_atoms hfa.inst hs ha
  have hpreEq : hfa.inst.pre = [atRobot rl, atBox b bl, clearL fl,
      adjacent rl bl dir, adjacent bl fl dir] := by
    rw [hfa.inst.pre_eq, hs, ha]; rfl
  have hrb : rl ≠ bl :=
    adjacent_ne hp rel hfa (x := rl) (y := bl) (dd := dir)
      (by rw [hpreEq]; simp)
  have hbf : bl ≠ fl :=
    adjacent_ne hp rel hfa (x := bl) (y := fl) (dd := dir)
      (by rw [hpreEq]; simp)
  have hrobotBefore : σ (atRobot rl) = true :=
    pre_holds hfa hpreR (atRobot_dynamic hp.domain) happ
  have hboxBefore : σ (atBox b bl) = true :=
    pre_holds hfa hpreB (atBox_dynamic hp.domain) happ
  have hdelR : atRobot rl ∈ o.del :=
    del_kept hfa (by rw [hdel]; simp)
      (by rw [hadd]; simp [atRobot, atBox, clearL, hrb]) hpreR
      (atRobot_dynamic hp.domain)
  have hdelB : atBox b bl ∈ o.del :=
    del_kept hfa (by rw [hdel]; simp)
      (by rw [hadd]; simp [atRobot, atBox, clearL, hbf]) hpreB
      (atBox_dynamic hp.domain)
  obtain ⟨hadjRB, hadjBF⟩ := push_adjacent hp rel hfa hs ha
  obtain ⟨ri, bi, fi, hri, hbi, hfi⟩ := push_arg_indices hp rel hfa hs ha
  have hinv' : Inv (o.applyA σ) := push_inv hp rel ho hfk hfa hs ha hinv happ
  obtain ⟨haddR, haddC⟩ := push_frame_adds ho hfk hfa hs ha
  have hrl' : robotLoc (compile (ground d p rel)) s' = some bi :=
    robotLoc_eq habs' hn hinv' (applyA_add σ haddR)
      (factsWith_of_op ho (Or.inr (Or.inl haddR)) rfl) hbi
  have hrl : robotLoc (compile (ground d p rel)) s = some ri :=
    robotLoc_eq habs hn hinv hrobotBefore
      (factsWith_of_op ho (Or.inr (Or.inr hdelR)) rfl) hri
  rcases hbl : boxLoc s bx with _ | li
  · by_cases hbn : bn = b
    · subst bn
      have hknown : boxLoc s bx = some bi :=
        boxLoc_eq habs hn hinv hfacts hboxBefore
          (factsWith_of_op ho (Or.inr (Or.inr hdelB)) rfl) hbi
      rw [hbl] at hknown
      simp at hknown
    · obtain ⟨hgoalFrame, hboxFrame⟩ :=
        push_frames_other hp hfa hs ha habs habs' hn hgoalLt hgname hfacts hbn
      left
      refine ⟨Array.mem_filter.mpr ⟨hbxmem, ?_⟩, ?_⟩
      · simp [hgoalFrame, hbxUnmet]
      · have hbl' : boxLoc s' bx = none := by rw [hboxFrame, hbl]
        rw [jointOf_box_none hrl hbl, jointOf_box_none hrl' hbl']
        omega
  obtain ⟨lb, fb, hlbTrue, hlbIx, hlbFact⟩ := boxLoc_some habs hn hfacts hbl
  obtain ⟨lr, -, hlrTrue, hlrIx, -⟩ := robotLoc_some habs hn hrl
  have hlrrl : lr = rl := hinv.robot.2 lr rl hlrTrue hrobotBefore
  rw [hlrrl] at hlrIx
  have hbiNe : ri ≠ bi := by
    intro hc
    exact hrb (locIx_inj (t := ground d p rel) hlrIx (by rw [hc]; exact hbi))
  by_cases hbn : bn = b
  · -- the box being pushed
    subst hbn
    have hlbbl : lb = bl := hinv.boxOne bn lb bl hlbTrue hboxBefore
    rw [hlbbl, hbi] at hlbIx
    have hliBi : li = bi := by simpa using hlbIx.symm
    rcases hbl0 : boxLoc s' bx with _ | li'
    · -- relevance dropped the `at` fact of the square ahead, so the box has no
      -- square afterwards, and its entry is the cap
      left
      refine ⟨Array.mem_filter.mpr ⟨hbxmem, ?_⟩, ?_⟩
      · rcases hv : s'.test bx.goalFact with _ | _
        · simp
        · exfalso
          have hatom : o.applyA σ (atBox bn g) = true := by
            rw [← hgname]
            rw [← habs'.numbered bx.goalFact (by rw [hn]; exact hgoalLt)] at hv
            exact hv
          have hsome := boxLoc_eq habs' hn hinv' hfacts hatom
            ⟨bx.goalFact, mem_factsWith_of_named hgoalLt hgname rfl⟩ hgIx
          rw [hbl0] at hsome
          exact absurd hsome (by simp)
      · rw [jointOf_some hbl hrl, jointOf_box_none hrl' hbl0]
        have := (jointSound_of_check (hjc bx hbxmem)).le_bound
          (li * (locsA (ground d p rel)).size + ri)
        omega
    have hbl' : boxLoc s' bx = some fi := by
      obtain ⟨l', -, hl'True, hl'Ix, -⟩ := boxLoc_some habs' hn hfacts hbl0
      have hlfl := push_box_key hp rel hfa hs ha hinv happ l' hl'True
      rw [hlfl, hfi] at hl'Ix
      rw [hbl0, (by simpa using hl'Ix.symm : li' = fi)]
    have hfiNe : fi ≠ bi := by
      intro hc
      exact hbf (locIx_inj (t := ground d p rel) hfi (by rw [hc]; exact hbi)).symm
    have hpush : (ri, fi) ∈ (pushTable (ground d p rel)).getD bi #[] := by
      rw [pushTable, pushSteps_getD (locIx_lt hbi)]
      exact mem_pushStepsAt hadjRB hadjBF hbi hlrIx hfi
    have hedge : fi * (locsA (ground d p rel)).size + bi
        ∈ jointSucc (locsA (ground d p rel)).size (walkTable (ground d p rel))
          (pushTable (ground d p rel)) bi ri :=
      mem_jointSucc_push hbiNe hfiNe hpush
    have hjs := jointSound_of_check (hjc bx hbxmem)
    have hstep := hjs.step bi ri (locIx_lt hbi) (locIx_lt hlrIx) _ hedge
    rw [jointOf_some hbl hrl, jointOf_some hbl' hrl', hliBi]
    by_cases hmet : bx ∈ unmetBoxes (compile (ground d p rel)) s'
    · exact Or.inl ⟨hmet, hstep⟩
    · -- the push put this box home, so its entry afterwards is zero
      right
      have hgoalTrue : s'.test bx.goalFact = true := by
        rcases hv : s'.test bx.goalFact with _ | _
        · exact absurd (Array.mem_filter.mpr ⟨hbxmem, by simp [hv]⟩) hmet
        · rfl
      have hatom : o.applyA σ (atBox bn g) = true := by
        rw [← hgname]
        rw [← habs'.numbered bx.goalFact (by rw [hn]; exact hgoalLt)] at hgoalTrue
        exact hgoalTrue
      have hgfl : g = fl := push_box_key hp rel hfa hs ha hinv happ g hatom
      rw [hgfl, hfi] at hgIx
      have hgoalLoc : bx.goalLoc = fi := by simpa using hgIx.symm
      have hzero : bx.jointDist.getD (fi * (locsA (ground d p rel)).size + bi)
          ((locsA (ground d p rel)).size * (locsA (ground d p rel)).size) = 0 := by
        rw [← hgoalLoc]
        exact hjs.atGoal bi (locIx_lt hbi) (by rw [hgoalLoc]; exact fun hc => hfiNe hc.symm)
      omega
  · -- every other box stands still while the robot walks onto `bl`
    have hboxFrame : o.applyA σ (atBox bn lb) = σ (atBox bn lb) :=
      frame_of_lists hfa hadd hdel
        (by simp [atBox, atRobot, clearL, hbn]) (by simp [atBox, atRobot, clearL, hbn]) σ
    have hbl' : boxLoc s' bx = some li :=
      boxLoc_eq habs' hn hinv' hfacts (by rw [hboxFrame]; exact hlbTrue)
        ⟨fb, hlbFact⟩ hlbIx
    have hunmet' : bx ∈ unmetBoxes (compile (ground d p rel)) s' := by
      refine Array.mem_filter.mpr ⟨hbxmem, ?_⟩
      have hgoalFrame : o.applyA σ (atBox bn g) = σ (atBox bn g) :=
        frame_of_lists hfa hadd hdel
          (by simp [atBox, atRobot, clearL, hbn]) (by simp [atBox, atRobot, clearL, hbn]) σ
      have h1 : s'.test bx.goalFact = s.test bx.goalFact := by
        rw [← habs'.numbered bx.goalFact (by rw [hn]; exact hgoalLt),
          ← habs.numbered bx.goalFact (by rw [hn]; exact hgoalLt), hgname, hgoalFrame]
      simp [h1, hbxUnmet]
    left
    refine ⟨hunmet', ?_⟩
    have hlbNeBl : lb ≠ bl := by
      intro hc
      rw [hc] at hlbTrue
      exact hbn (hinv.squareOne bn b bl hlbTrue hboxBefore)
    have hliNe : bi ≠ li := by
      intro hc
      have h2 : locIx (ground d p rel) bl = some li := by rw [hbi, hc]
      exact hlbNeBl (locIx_inj (t := ground d p rel) hlbIx h2)
    have hriNe : ri ≠ li := by
      intro hc
      have h2 : locIx (ground d p rel) lb = some ri := by rw [hlbIx, hc]
      exact (hinv.robot_ne_box hlbTrue hrobotBefore)
        (locIx_inj (t := ground d p rel) hlrIx h2)
    have hwalk : bi ∈ (walkTable (ground d p rel)).getD ri #[] :=
      mem_walkTable _ hadjRB hlrIx hbi
    have hedge : li * (locsA (ground d p rel)).size + bi
        ∈ jointSucc (locsA (ground d p rel)).size (walkTable (ground d p rel))
          (pushTable (ground d p rel)) li ri :=
      mem_jointSucc_move hriNe hliNe hwalk
    rw [jointOf_some hbl hrl, jointOf_some hbl' hrl']
    exact (jointSound_of_check (hjc bx hbxmem)).step li ri (locIx_lt hlbIx)
      (locIx_lt hlrIx) _ hedge

end Planner.Lifted.Sokoban

/- -------------------------------------------------------------------------- -/
/-
The walk to the first push.

`approachRaw` is the shortest walk from the robot to any square some box can be
pushed from.  It is what makes the additive bound safe: a `push` is only legal
with the robot already standing on such a square, so the walk is *zero* whenever
a push is available, and the push takes one off the push count without taking
anything off the walk.  A `move` leaves the push count alone and shifts the walk
by at most one, because the walk graph is symmetrised and the table is checked to
change by at most one along every edge.

Those are `PushStep.approachMono` and `MoveStep.approachStep`.
-/

namespace Planner.Lifted.Sokoban

open Planner Planner.Pddl Planner.ExampleHeuristics.Sokoban

variable {d : Domain} {p : Problem} {rel : Bool}

/-! ### A running minimum -/

/-- A running minimum is under every term it saw. -/
theorem foldl_min_le_mem {α : Type} (f : α → Nat) :
    ∀ (l : List α) (b : Nat) {x : α}, x ∈ l →
      l.foldl (fun acc y => min acc (f y)) b ≤ f x := by
  intro l
  induction l with
  | nil => intro b x hx; simp at hx
  | cons y rest ih =>
      intro b x hx
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact Nat.le_trans (foldl_min_le_init' _ rest _) (Nat.min_le_right _ _)
      · exact ih _ hmem

/-! ### The value, with the robot's square named -/

theorem approachRaw_some (dd : Data) (s : State) {r : Nat}
    (h : robotLoc dd s = some r) :
    approachRaw dd s = dd.boxAt.foldl (init := dd.walk.bound) fun best facts =>
      match facts.find? fun x => s.test x.1 with
      | some (_, l) =>
          (dd.pushPos.getD l #[]).foldl (init := best) fun acc q =>
            min acc (dd.walk.get r q)
      | none => best := by
  unfold approachRaw
  rw [h]
  rfl

/-- Each bucket only ever lowers the running walk. -/
theorem approach_step_mono (dd : Data) (s : State) (r : Nat) :
    ∀ (b : Nat) (facts : Array (Fact × Nat)),
      (match facts.find? fun x => s.test x.1 with
        | some (_, l) =>
            (dd.pushPos.getD l #[]).foldl (init := b) fun acc q =>
              min acc (dd.walk.get r q)
        | none => b) ≤ b := by
  intro b facts
  split
  · rw [← Array.foldl_toList]
    exact foldl_min_le_init' _ _ _
  · exact Nat.le_refl _

/-! ### The walk table, checked -/

/-- The walk table falls by at most one along every robot step. -/
def WalkSound (d : Domain) (p : Problem) (rel : Bool) : Prop :=
  Distances.Sound (walkGraph (locsA (ground d p rel))
      (Graph.nodeIndex (locsA (ground d p rel))) (walkTable (ground d p rel)))
    (compile (ground d p rel)).walk

/-- The compiled walk table is sound by construction. -/
theorem walkSound (d : Domain) (p : Problem) (rel : Bool) : WalkSound d p rel := by
  unfold WalkSound
  rw [compile_walk]
  exact Distances.sound_of _

/-! ### `move` -/

set_option maxHeartbeats 1000000 in
/-- **`MoveStep.approachStep`.**  The boxes do not move, so the walk changes only
in where it starts, and one edge of the walk graph moves the table by one. -/
theorem move_approachStep (hp : Pinned d p) (hws : WalkSound d p rel)
    (hfk : FrameAddsKept d p rel) {o : AtomOp}
    (ho : o ∈ groundedOps d p rel) (hfa : OpFacts d p o) {frm dest dir : Name}
    (hs : hfa.inst.schema = moveA) (ha : hfa.inst.args = [frm, dest, dir])
    {s s' : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (habs' : Abstracts (ground d p rel) s' (o.applyA σ))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (hinv : Inv σ) (happ : o.applicableA σ) :
    approachRaw (compile (ground d p rel)) s
      ≤ 1 + approachRaw (compile (ground d p rel)) s' := by
  obtain ⟨hpreR, hadd, hdel⟩ := move_atoms hfa.inst hs ha
  have hrobotBefore : σ (atRobot frm) = true :=
    pre_holds hfa hpreR (atRobot_dynamic hp.domain) happ
  obtain ⟨ui, vi, hui, hvi⟩ := move_arg_indices hp rel hfa hs ha
  -- the two positions
  have hpreEq : hfa.inst.pre = [clearL dest, atRobot frm, adjacent frm dest dir] := by
    rw [hfa.inst.pre_eq, hs, ha]; rfl
  have hne : frm ≠ dest :=
    adjacent_ne hp rel hfa (x := frm) (y := dest) (dd := dir)
      (by rw [hpreEq]; simp)
  have hdelR : atRobot frm ∈ o.del :=
    del_kept hfa (by rw [hdel]; simp)
      (by rw [hadd]; simp [atRobot, hne]) hpreR (atRobot_dynamic hp.domain)
  have hrl : robotLoc (compile (ground d p rel)) s = some ui :=
    robotLoc_eq habs hn hinv hrobotBefore
      (factsWith_of_op ho (Or.inr (Or.inr hdelR)) rfl) hui
  have hinv' : Inv (o.applyA σ) := move_inv hp rel ho hfk hfa hs ha hinv happ
  have hrl' : robotLoc (compile (ground d p rel)) s' = some vi :=
    robotLoc_eq habs' hn hinv' (move_robot_after ho hfk hfa hs ha σ)
      (factsWith_of_op ho (Or.inr (Or.inl (move_robot_add ho hfk hfa hs ha))) rfl) hvi
  -- the buckets read the same before and after
  have hbuckets : ∀ facts ∈ (compile (ground d p rel)).boxAt,
      facts.find? (fun x => s'.test x.1) = facts.find? (fun x => s.test x.1) := by
    intro facts hfacts
    refine array_find?_congr _ _ _ fun y hy => ?_
    obtain ⟨hlt, bnm, lnm, hname, -⟩ := boxAt_pred hfacts hy
    refine test_frame_pred (P := "at") hfa ?_ ?_ habs habs' hn hlt
      (by rw [hname]) <;> intro a hm hbad
    · rw [move_touches hfa.inst hs ha (Or.inl hm)] at hbad; exact absurd hbad (by decide)
    · rw [move_touches hfa.inst hs ha (Or.inr hm)] at hbad; exact absurd hbad (by decide)
  -- the walk edge
  have hedge := (walk_edge (ground d p rel)
    (move_adjacent hp rel hfa hs ha) hui hvi).1
  rw [approachRaw_some _ s hrl, approachRaw_some _ s' hrl', ← Array.foldl_toList,
    ← Array.foldl_toList]
  refine foldl_step_le_succ _ _ _ ?_ _ _ (Nat.le_add_left _ _)
  intro facts hfacts b b' hb
  have hfacts' : facts ∈ (compile (ground d p rel)).boxAt := by simpa using hfacts
  rw [hbuckets facts hfacts']
  split
  · rename_i y l hfind
    rw [← Array.foldl_toList, ← Array.foldl_toList]
    refine foldl_min_le_succ _ _ _ (fun q hq => ?_) _ _ hb
    have hq' : q ∈ (compile (ground d p rel)).pushPos.getD l #[] := by simpa using hq
    exact hws.step ui vi q (locIx_lt hui) (pushPos_lt _ hq') hedge
  · exact hb

/-! ### `push` -/

set_option maxHeartbeats 1000000 in
/-- **`PushStep.approachMono`.**  A push is legal only with the robot already on
a square its box can be pushed from, so the walk to the first push is zero and
cannot fall. -/
theorem push_approach_zero (hp : Pinned d p) (hws : WalkSound d p rel) {o : AtomOp}
    (ho : o ∈ groundedOps d p rel) (hfa : OpFacts d p o) {rl bl fl dir b : Name}
    (hs : hfa.inst.schema = pushA) (ha : hfa.inst.args = [rl, bl, fl, dir, b])
    {s : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (hinv : Inv σ) (happ : o.applicableA σ) :
    approachRaw (compile (ground d p rel)) s = 0 := by
  obtain ⟨hpreR, hpreB, hpreC, hadd, hdel⟩ := push_atoms hfa.inst hs ha
  have hpreEq : hfa.inst.pre = [atRobot rl, atBox b bl, clearL fl,
      adjacent rl bl dir, adjacent bl fl dir] := by
    rw [hfa.inst.pre_eq, hs, ha]; rfl
  have hrb : rl ≠ bl :=
    adjacent_ne hp rel hfa (x := rl) (y := bl) (dd := dir)
      (by rw [hpreEq]; simp)
  have hbf : bl ≠ fl :=
    adjacent_ne hp rel hfa (x := bl) (y := fl) (dd := dir)
      (by rw [hpreEq]; simp)
  have hrobotBefore : σ (atRobot rl) = true :=
    pre_holds hfa hpreR (atRobot_dynamic hp.domain) happ
  have hboxBefore : σ (atBox b bl) = true :=
    pre_holds hfa hpreB (atBox_dynamic hp.domain) happ
  obtain ⟨hadjRB, hadjBF⟩ := push_adjacent hp rel hfa hs ha
  obtain ⟨ri, bi, fi, hri, hbi, hfi⟩ := push_arg_indices hp rel hfa hs ha
  -- the robot's square
  have hdelR : atRobot rl ∈ o.del :=
    del_kept hfa (by rw [hdel]; simp)
      (by rw [hadd]; simp [atRobot, atBox, clearL, hrb]) hpreR
      (atRobot_dynamic hp.domain)
  have hrl : robotLoc (compile (ground d p rel)) s = some ri :=
    robotLoc_eq habs hn hinv hrobotBefore
      (factsWith_of_op ho (Or.inr (Or.inr hdelR)) rfl) hri
  -- the pushed box's bucket
  obtain ⟨a1, a2, a3, a4, a5, ha', -, -, -, -, hw5⟩ :=
    hfa.inst.args_five (show hfa.inst.schema.params
      = [locP "?rloc", locP "?bloc", locP "?floc", dirP "?dir", boxP "?b"]
      by rw [hs])
  rw [ha] at ha'
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ :
      rl = a1 ∧ bl = a2 ∧ fl = a3 ∧ dir = a4 ∧ b = a5 := by simpa using ha'
  have hbmem : b ∈ (ground d p rel).objectsOfTypes ["box"] :=
    mem_objsOf_of_wellTyped hp.boxTypeExact hw5
  have hbucket : ((ground d p rel).factsWith "at").filterMap (fun x =>
      match x.2.args with
      | [y, l] => if y == b then (locIx (ground d p rel) l).map ((x.1, ·)) else none
      | _ => none) ∈ (compile (ground d p rel)).boxAt :=
    Array.mem_map.mpr ⟨b, hbmem, rfl⟩
  have hdelB : atBox b bl ∈ o.del :=
    del_kept hfa (by rw [hdel]; simp)
      (by rw [hadd]; simp [atRobot, atBox, clearL, hbf]) hpreB
      (atBox_dynamic hp.domain)
  obtain ⟨y, hy, hy2⟩ := atFacts_find_eq habs hn hinv rfl hboxBefore
    (factsWith_of_op ho (Or.inr (Or.inr hdelB)) rfl) hbi
  -- the robot stands on a square that box can be pushed from
  have hpushPos : ri ∈ (compile (ground d p rel)).pushPos.getD bi #[] :=
    (push_edge (ground d p rel) hadjRB hadjBF hbi hri hfi).2
  have hself : (compile (ground d p rel)).walk.get ri ri = 0 :=
    hws.self ri (locIx_lt hri)
  rw [approachRaw_some _ s hrl, ← Array.foldl_toList]
  refine foldl_eq_zero_of_mem _ (approach_step_mono _ s ri)
    hbucket.val (fun bb => ?_) _
  split
  · rename_i f' l' hfind
    have heq : y = (f', l') := Option.some.inj (hy.symm.trans hfind)
    have hl' : l' = bi := by rw [← hy2, heq]
    refine Nat.le_antisymm ?_ (Nat.zero_le _)
    rw [← Array.foldl_toList, ← hself, hl']
    exact foldl_min_le_mem _ _ _ (by simpa using hpushPos)
  · rename_i hfind
    exact absurd (hy.symm.trans hfind) (by simp)

end Planner.Lifted.Sokoban

/- -------------------------------------------------------------------------- -/
/-
Assembling the schema shapes for the grounded Sokoban operators.

`MoveStep` is complete: a walk frames the boxes, moves the robot along one edge
of the walk graph, and is one edge of every box's product graph.
-/

namespace Planner.Lifted.Sokoban

open Planner Planner.Pddl Planner.ExampleHeuristics.Sokoban

variable {d : Domain} {p : Problem} {rel : Bool}

/-- **`move` is a `MoveStep`.** -/
theorem move_schemaStep (hp : Pinned d p) (hws : WalkSound d p rel)
    (hjc : JointChecked d p rel) (hfk : FrameAddsKept d p rel) {o : AtomOp}
    (ho : o ∈ groundedOps d p rel) (hfa : OpFacts d p o) {frm dest dir : Name}
    (hs : hfa.inst.schema = moveA) (ha : hfa.inst.args = [frm, dest, dir])
    {s s' : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (habs' : Abstracts (ground d p rel) s' (o.applyA σ))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (hinv : Inv σ) (happ : o.applicableA σ) :
    MoveStep (compile (ground d p rel)) s s' := by
  obtain ⟨hpreR, hadd, hdel⟩ := move_atoms hfa.inst hs ha
  have hpreEq : hfa.inst.pre = [clearL dest, atRobot frm, adjacent frm dest dir] := by
    rw [hfa.inst.pre_eq, hs, ha]; rfl
  have hne : frm ≠ dest :=
    adjacent_ne hp rel hfa (x := frm) (y := dest) (dd := dir)
      (by rw [hpreEq]; simp)
  have hrobotBefore : σ (atRobot frm) = true :=
    pre_holds hfa hpreR (atRobot_dynamic hp.domain) happ
  obtain ⟨ui, vi, hui, hvi⟩ := move_arg_indices hp rel hfa hs ha
  have hdelR : atRobot frm ∈ o.del :=
    del_kept hfa (by rw [hdel]; simp)
      (by rw [hadd]; simp [atRobot, hne]) hpreR (atRobot_dynamic hp.domain)
  have hrl : robotLoc (compile (ground d p rel)) s = some ui :=
    robotLoc_eq habs hn hinv hrobotBefore
      (factsWith_of_op ho (Or.inr (Or.inr hdelR)) rfl) hui
  have hinv' : Inv (o.applyA σ) := move_inv hp rel ho hfk hfa hs ha hinv happ
  have hrl' : robotLoc (compile (ground d p rel)) s' = some vi :=
    robotLoc_eq habs' hn hinv' (move_robot_after ho hfk hfa hs ha σ)
      (factsWith_of_op ho (Or.inr (Or.inl (move_robot_add ho hfk hfa hs ha))) rfl) hvi
  exact
    { goalsSame := move_goalsSame hfa hs ha habs habs' hn
      boxSame := move_boxSame hfa hs ha habs habs' hn
      approachStep := move_approachStep hp hws hfk ho hfa hs ha habs habs' hn hinv happ
      jointStep := move_jointStep hp hjc hfk ho hfa hs ha habs habs' hn hinv happ
      robotSome := by rw [hrl]; rfl
      robotSome' := by rw [hrl']; rfl }

end Planner.Lifted.Sokoban

/- -------------------------------------------------------------------------- -/
/-
The additive push count, across one push.

`pushesRaw` sums, over the boxes still to place, the distance from where the box
stands to its goal square in the *push graph* — the graph whose edges are the
squares a box can actually be pushed between, so that walls and corners are
visible where plain adjacency sees nothing.

A push moves one box one edge of that graph and leaves every other box alone, so
the sum falls by at most one.  Two facts about the last push are needed as well,
and both come out of the same decomposition: when the push finishes the task,
the only box still owing anything was the one it moved.
-/

namespace Planner.Lifted.Sokoban

open Planner Planner.Pddl Planner.ExampleHeuristics.Sokoban

variable {d : Domain} {p : Problem} {rel : Bool}

/-! ### The largest one-box distance, bounded -/

theorem hardestRaw_le_of (dd : Data) (s : State) (M : Nat)
    (h : ∀ b ∈ unmetBoxes dd s, jointOf dd s b ≤ M) : hardestRaw dd s ≤ M := by
  unfold hardestRaw
  rw [← Array.foldl_toList]
  exact foldl_max_le_bound _ _ _ (fun b hb => h b (by simpa using hb)) 0 (Nat.zero_le _)

/-! ### The push table, checked -/

/-- The push table falls by at most one along every push edge. -/
def PushSound (d : Domain) (p : Problem) (rel : Bool) : Prop :=
  Distances.Sound (pushGraph (locsA (ground d p rel))
      (Graph.nodeIndex (locsA (ground d p rel))) (pushTable (ground d p rel)))
    (compile (ground d p rel)).dist

/-- The compiled push table is sound by construction. -/
theorem pushSound (d : Domain) (p : Problem) (rel : Bool) : PushSound d p rel := by
  unfold PushSound
  rw [compile_dist]
  exact Distances.sound_of _

/--
**The box table has no duplicate entry.**

Each entry stores the fact of the goal atom it came from, and the problem's goal
names each atom once.  `Pinned.goalNodup` is what supplies that.
-/
theorem boxes_nodup (hp : Pinned d p) (rel : Bool) :
    (compile (ground d p rel)).boxes.toList.Nodup := by
  refine goalTable_nodup_fact d p rel hp.goalNodup _ (·.goalFact) ?_
  intro x hx b hb
  split at hb
  · split at hb
    · split at hb
      · obtain ⟨gl, -, hval⟩ := Option.map_eq_some_iff.mp hb
        rw [← hval]
        rfl
      · simp at hb
    · simp at hb

/--
One `at` goal per box, so a push moves one term of the sum.

Duplicate-freedom of the table is `boxes_nodup`; what stays here is the part that
is genuinely about the task's goal — that no two entries name the *same* box.
A goal asking one box to be in two places would break it, and nothing in the
domain rules that out.
-/
def BoxesOne (d : Domain) (p : Problem) (rel : Bool) : Prop :=
  ∀ bx ∈ (compile (ground d p rel)).boxes, ∀ bx' ∈ (compile (ground d p rel)).boxes,
    ∀ bn l l', (ground d p rel).factNames.getD bx.goalFact default = atBox bn l →
      (ground d p rel).factNames.getD bx'.goalFact default = atBox bn l' → bx = bx'

/-- A finite uniqueness condition on the PDDL goal supplies `BoxesOne` for
either relevance setting. -/
theorem boxesOne_of_goal
    (hgoal : ∀ b l l', atBox b l ∈ p.goal → atBox b l' ∈ p.goal → l = l')
    (rel : Bool) : BoxesOne d p rel := by
  intro bx hbx bx' hbx' bn l l' hname hname'
  have hgoal1 : atBox bn l ∈ p.goal := by
    have hm := atomOf_mem_goal d p rel (boxes_mem_goal d p rel bx hbx)
    rwa [hname] at hm
  have hgoal2 : atBox bn l' ∈ p.goal := by
    have hm := atomOf_mem_goal d p rel (boxes_mem_goal d p rel bx' hbx')
    rwa [hname'] at hm
  have hll : l = l' := hgoal bn l l' hgoal1 hgoal2
  subst l'
  obtain ⟨hlt, b, g, hbg, hgix, hfacts, hjoint⟩ := boxes_data hbx
  obtain ⟨hlt', b', g', hbg', hgix', hfacts', hjoint'⟩ := boxes_data hbx'
  have hargs : b = bn ∧ g = l := by
    rw [hbg] at hname
    simpa using hname
  have hargs' : b' = bn ∧ g' = l := by
    rw [hbg'] at hname'
    simpa using hname'
  obtain ⟨rfl, rfl⟩ := hargs
  obtain ⟨rfl, rfl⟩ := hargs'
  have hgoalFact : bx.goalFact = bx'.goalFact :=
    Planner.factNames_inj d p rel hlt hlt' (by rw [hname, hname'])
  have hgoalLoc : bx.goalLoc = bx'.goalLoc :=
    Option.some.inj (hgix.symm.trans hgix')
  have hatFacts : bx.atFacts = bx'.atFacts := hfacts.trans hfacts'.symm
  have hjointDist : bx.jointDist = bx'.jointDist := by
    rw [hjoint, hjoint', hgoalLoc]
  cases bx
  cases bx'
  simp_all

/-! ### The push count -/

theorem pushesRaw_filter (dd : Data) (s : State) :
    pushesRaw dd s = ((dd.boxes.toList.filter fun bxx => !s.test bxx.goalFact).map
      fun bxx => match boxLoc s bxx with
        | some l => dd.dist.get l bxx.goalLoc
        | none => dd.dist.bound).sum := by
  rw [MoveStep.pushesRaw_eq]
  congr 1
  congr 1
  show (Array.filter (fun bxx => !s.test bxx.goalFact) dd.boxes).toList = _
  rw [Array.toList_filter]

theorem pushesRaw_zero_of_solved (dd : Data) (s : State) (h : solved dd s = true) :
    pushesRaw dd s = 0 := by
  have hempty : unmetBoxes dd s = #[] := by
    have := h
    unfold solved at this
    rwa [Array.isEmpty_iff] at this
  rw [MoveStep.pushesRaw_eq, hempty]
  rfl

set_option maxHeartbeats 1000000 in
/-- **`PushStep.pushStep`.**  Only the box the push moves changes a term of the
sum, and it moves one edge of the push graph. -/
theorem push_pushStep (hp : Pinned d p) (hps : PushSound d p rel)
    (hbo : BoxesOne d p rel) (hfk : FrameAddsKept d p rel) {o : AtomOp}
    (ho : o ∈ groundedOps d p rel) (hfa : OpFacts d p o) {rl bl fl dir b : Name}
    (hs : hfa.inst.schema = pushA) (ha : hfa.inst.args = [rl, bl, fl, dir, b])
    {s s' : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (habs' : Abstracts (ground d p rel) s' (o.applyA σ))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (hinv : Inv σ) (happ : o.applicableA σ) :
    pushesRaw (compile (ground d p rel)) s
      ≤ pushesRaw (compile (ground d p rel)) s' + 1 := by
  obtain ⟨hpreR, hpreB, hpreC, hadd, hdel⟩ := push_atoms hfa.inst hs ha
  have hpreEq : hfa.inst.pre = [atRobot rl, atBox b bl, clearL fl,
      adjacent rl bl dir, adjacent bl fl dir] := by
    rw [hfa.inst.pre_eq, hs, ha]; rfl
  have hbf : bl ≠ fl :=
    adjacent_ne hp rel hfa (x := bl) (y := fl) (dd := dir)
      (by rw [hpreEq]; simp)
  have hboxBefore : σ (atBox b bl) = true :=
    pre_holds hfa hpreB (atBox_dynamic hp.domain) happ
  obtain ⟨hadjRB, hadjBF⟩ := push_adjacent hp rel hfa hs ha
  obtain ⟨ri, bi, fi, hri, hbi, hfi⟩ := push_arg_indices hp rel hfa hs ha
  have hinv' : Inv (o.applyA σ) := push_inv hp rel ho hfk hfa hs ha hinv happ
  obtain ⟨haddR, haddC⟩ := push_frame_adds ho hfk hfa hs ha
  have hdelB : atBox b bl ∈ o.del :=
    del_kept hfa (by rw [hdel]; simp)
      (by rw [hadd]; simp [atRobot, atBox, clearL, hbf]) hpreB
      (atBox_dynamic hp.domain)
  rw [pushesRaw_filter, pushesRaw_filter]
  by_cases hex : ∃ bx0 ∈ (compile (ground d p rel)).boxes,
      ∃ l, (ground d p rel).factNames.getD bx0.goalFact default = atBox b l
  · obtain ⟨bx0, hbx0, l0, hname0⟩ := hex
    obtain ⟨hgoalLt0, bn0, g0, hgname0, hgIx0, hfacts0, -⟩ := boxes_data hbx0
    have hb0 : bn0 = b ∧ g0 = l0 := by
      rw [hgname0] at hname0
      simpa [atBox] using hname0
    rw [hb0.1] at hgname0 hfacts0
    rw [hb0.2] at hgname0 hgIx0
    refine sum_filter_exchange _ _ _ _ bx0 _ (boxes_nodup hp rel) (fun y hy hyx => ?_) ?_
    · -- every other entry is a different box, and a push frames it
      have hymem : y ∈ (compile (ground d p rel)).boxes := by simpa using hy
      obtain ⟨hgoalLtY, bnY, gY, hgnameY, -, hfactsY, -⟩ := boxes_data hymem
      have hneY : bnY ≠ b := by
        intro hc
        rw [hc] at hgnameY
        exact hyx (hbo y hymem bx0 hbx0 b gY l0 hgnameY hgname0)
      obtain ⟨h1, h2⟩ := push_frames_other hp hfa hs ha habs habs' hn hgoalLtY
        hgnameY hfactsY hneY
      exact ⟨by rw [h1], by rw [h2]⟩
    · -- the box the push moves
      by_cases hmet : s.test bx0.goalFact = true
      · rw [if_neg (by simp [hmet])]
        omega
      · have hunmet : s.test bx0.goalFact = false := by
          simpa using hmet
        rw [if_pos (by simp [hunmet])]
        have hbl0 : boxLoc s bx0 = some bi :=
          boxLoc_eq habs hn hinv hfacts0 hboxBefore
            (factsWith_of_op ho (Or.inr (Or.inr hdelB)) rfl) hbi
        rw [hbl0]
        by_cases hmet' : s'.test bx0.goalFact = true
        · -- the push put this box home
          rw [if_neg (by simp [hmet'])]
          have hatom : o.applyA σ (atBox b l0) = true := by
            rw [← hgname0]
            rw [← habs'.numbered bx0.goalFact (by rw [hn]; exact hgoalLt0)] at hmet'
            exact hmet'
          have hgfl : l0 = fl := push_box_key hp rel hfa hs ha hinv happ l0 hatom
          rw [hgfl, hfi] at hgIx0
          have hgoalLoc : bx0.goalLoc = fi := by simpa using hgIx0.symm
          show (compile (ground d p rel)).dist.get bi bx0.goalLoc ≤ 0 + 1
          rw [hgoalLoc]
          have hself : (compile (ground d p rel)).dist.get fi fi = 0 :=
            hps.self fi (locIx_lt hfi)
          have hstep := hps.step bi fi fi (locIx_lt hbi) (locIx_lt hfi)
            (push_edge (ground d p rel) hadjRB hadjBF hbi hri hfi).1
          omega
        · have hunmet' : s'.test bx0.goalFact = false := by simpa using hmet'
          rw [if_pos (by simp [hunmet'])]
          rcases hbl0' : boxLoc s' bx0 with _ | li'
          · -- relevance dropped the `at` fact of the square ahead
            show (compile (ground d p rel)).dist.get bi bx0.goalLoc ≤
              (compile (ground d p rel)).dist.bound + 1
            have := hps.le_bound bi bx0.goalLoc
            omega
          · have hli' : li' = fi := by
              obtain ⟨l', -, hl'True, hl'Ix, -⟩ := boxLoc_some habs' hn hfacts0 hbl0'
              have hlfl := push_box_key hp rel hfa hs ha hinv happ l' hl'True
              rw [hlfl, hfi] at hl'Ix
              simpa using hl'Ix.symm
            rw [hli']
            show (compile (ground d p rel)).dist.get bi bx0.goalLoc ≤
              (compile (ground d p rel)).dist.get fi bx0.goalLoc + 1
            have := hps.step bi fi bx0.goalLoc (locIx_lt hbi) (locIx_lt hgIx0)
              (push_edge (ground d p rel) hadjRB hadjBF hbi hri hfi).1
            omega
  · -- no goal names the box the push moves
    refine Nat.le_trans (Nat.le_of_eq (sum_filter_congr _ _ _ _ _ fun y hy => ?_))
      (Nat.le_add_right _ _)
    have hymem : y ∈ (compile (ground d p rel)).boxes := by simpa using hy
    obtain ⟨hgoalLtY, bnY, gY, hgnameY, -, hfactsY, -⟩ := boxes_data hymem
    have hneY : bnY ≠ b := by
      intro hc
      rw [hc] at hgnameY
      exact hex ⟨y, hymem, gY, hgnameY⟩
    obtain ⟨h1, h2⟩ := push_frames_other hp hfa hs ha habs habs' hn hgoalLtY
      hgnameY hfactsY hneY
    exact ⟨by rw [h1], by rw [h2]⟩

/-! ### The push shape, and the schema bridge -/

set_option maxHeartbeats 1000000 in
/-- **`push` is a `PushStep`.** -/
theorem push_schemaStep (hp : Pinned d p) (hws : WalkSound d p rel)
    (hps : PushSound d p rel) (hjc : JointChecked d p rel) (hbo : BoxesOne d p rel)
    (hfk : FrameAddsKept d p rel)
    {o : AtomOp} (ho : o ∈ groundedOps d p rel) (hfa : OpFacts d p o)
    {rl bl fl dir b : Name}
    (hs : hfa.inst.schema = pushA) (ha : hfa.inst.args = [rl, bl, fl, dir, b])
    {s s' : State} {σ : AtomState}
    (habs : Abstracts (ground d p rel) s σ)
    (habs' : Abstracts (ground d p rel) s' (o.applyA σ))
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size)
    (hinv : Inv σ) (happ : o.applicableA σ) :
    PushStep (compile (ground d p rel)) s s' := by
  obtain ⟨hpreR, hpreB, hpreC, hadd, hdel⟩ := push_atoms hfa.inst hs ha
  have hpreEq : hfa.inst.pre = [atRobot rl, atBox b bl, clearL fl,
      adjacent rl bl dir, adjacent bl fl dir] := by
    rw [hfa.inst.pre_eq, hs, ha]; rfl
  have hrb : rl ≠ bl :=
    adjacent_ne hp rel hfa (x := rl) (y := bl) (dd := dir)
      (by rw [hpreEq]; simp)
  have hrobotBefore : σ (atRobot rl) = true :=
    pre_holds hfa hpreR (atRobot_dynamic hp.domain) happ
  obtain ⟨ri, bi, fi, hri, hbi, hfi⟩ := push_arg_indices hp rel hfa hs ha
  have hinv' : Inv (o.applyA σ) := push_inv hp rel ho hfk hfa hs ha hinv happ
  obtain ⟨haddR, haddC⟩ := push_frame_adds ho hfk hfa hs ha
  have hdelR : atRobot rl ∈ o.del :=
    del_kept hfa (by rw [hdel]; simp)
      (by rw [hadd]; simp [atRobot, atBox, clearL, hrb]) hpreR
      (atRobot_dynamic hp.domain)
  have hrl : robotLoc (compile (ground d p rel)) s = some ri :=
    robotLoc_eq habs hn hinv hrobotBefore
      (factsWith_of_op ho (Or.inr (Or.inr hdelR)) rfl) hri
  have hrl' : robotLoc (compile (ground d p rel)) s' = some bi :=
    robotLoc_eq habs' hn hinv' (applyA_add σ haddR)
      (factsWith_of_op ho (Or.inr (Or.inl haddR)) rfl) hbi
  have hzero : approachRaw (compile (ground d p rel)) s = 0 :=
    push_approach_zero hp hws ho hfa hs ha habs hn hinv happ
  have hjoint := push_jointStep hp hjc hfk ho hfa hs ha habs habs' hn hinv happ
  exact
    { pushStep := push_pushStep hp hps hbo hfk ho hfa hs ha habs habs' hn hinv happ
      approachMono := by rw [hzero]; exact Nat.zero_le _
      jointStep := hjoint
      robotSome := by rw [hrl]; rfl
      robotSome' := by rw [hrl']; rfl
      lastPush := by
        intro hsolved
        have h1 := push_pushStep hp hps hbo hfk ho hfa hs ha habs habs' hn hinv happ
        rw [pushesRaw_zero_of_solved _ s' hsolved] at h1
        omega
      lastApproach := fun _ => hzero
      lastHardest := by
        intro hsolved
        have hempty : unmetBoxes (compile (ground d p rel)) s' = #[] := by
          have := hsolved
          unfold solved at this
          rwa [Array.isEmpty_iff] at this
        refine hardestRaw_le_of _ s 1 fun bx hbx => ?_
        rcases hjoint bx hbx with ⟨hmem, -⟩ | hone
        · rw [hempty] at hmem
          simp at hmem
        · exact hone }

/-- **Every grounded Sokoban operator has a proved schema shape.** -/
theorem schemaStep_of_ops (hp : Pinned d p) (hws : WalkSound d p rel)
    (hps : PushSound d p rel) (hjc : JointChecked d p rel) (hbo : BoxesOne d p rel)
    (hfk : FrameAddsKept d p rel)
    (hn : (ground d p rel).numFacts = (ground d p rel).factNames.size) :
    ∀ o ∈ groundedOps d p rel, ∀ (s s' : State) (σ : AtomState),
      Abstracts (ground d p rel) s σ →
      Abstracts (ground d p rel) s' (o.applyA σ) →
      Inv σ → o.applicableA σ → SchemaStep (compile (ground d p rel)) s s' := by
  intro o ho s s' σ habs habs' hinv happ
  obtain ⟨hfa⟩ := opFacts_ground d p rel ho
  rcases instance_shape hp.domain hfa.inst with
    ⟨f, t, dir, hsc, hac⟩ | ⟨rl, bl, fl, dir, b, hsc, hac⟩
  · exact .move (move_schemaStep hp hws hjc hfk ho hfa hsc hac habs habs' hn hinv happ)
  · exact .push (push_schemaStep hp hws hps hjc hbo hfk ho hfa hsc hac habs habs' hn hinv happ)

end Planner.Lifted.Sokoban

/- -------------------------------------------------------------------------- -/
/-
Sokoban's shipped improved heuristic, admissible on every reachable state.

Everything before this file is stated of one grounded operator and one atom-level
state.  This file lifts that to the numbered task the planner runs: it walks the
reachability relation, carries the position invariant along it, and hands each
numbered operator to the schema bridge.

The remaining finite task-specific facts concern the initial state and the
uniqueness of boxes in the goal.  The frame adds the invariant needs are no
longer among them: `Proofs/Lifted/SokobanRelevance.lean` proves that grounding
and the relevance analysis both keep them.  Distance-table soundness is proved
once for the constructors used by the compiler.
-/

namespace Planner.Lifted.Sokoban

open Planner Planner.Pddl Planner.ExampleHeuristics.Sokoban

variable {d : Domain} {p : Problem}

/-- The decidable facts about one Sokoban task that the proof still checks. -/
structure Certified (d : Domain) (p : Problem) extends Pinned d p where
  /-- No box has two `at` facts in `:init`, the robot stands in one clear place,
  and no box's square is clear. -/
  initCheck : initInvCheck p = true
  /-- The goal names each box once. -/
  boxesOne : ∀ rel : Bool, BoxesOne d p rel

/-- The position invariant holds at every reachable numbered state. -/
theorem reach_inv (hc : Certified d p) (rel : Bool)
    (hwf : Task.WF (ground d p rel)) {s : State}
    (hreach : Reachable (ground d p rel) s) :
    ∃ σ, Abstracts (ground d p rel) s σ ∧ Inv σ :=
  reachable_abstracts_inv d p rel hwf (cost_pos hc.toPinned rel) Inv
    (init_inv hc.initCheck) (inv_step hc.toPinned rel (frameAddsKept hc.toPinned rel))
    hreach

open Planner.ExampleHeuristics.Sokoban in
/-- **Every numbered operator applicable at a reachable state has a shape.** -/
theorem schemaStep_of_reach (hc : Certified d p) (rel : Bool)
    (hwf : Task.WF (ground d p rel)) {s : State}
    (hreach : Reachable (ground d p rel) s) {op : Op}
    (hop : op ∈ (ground d p rel).ops) (happ : op.applicable s = true) :
    SchemaStep (compile (ground d p rel)) s (op.apply s) := by
  have hp := hc.toPinned
  obtain ⟨σ, habs, hinv⟩ := reach_inv hc rel hwf hreach
  have hops : (ground d p rel).ops = (groundedOps d p rel).map
      (numberOp (factIndex (allAtoms (groundedOps d p rel) p.goal.toArray)).1) := rfl
  rw [hops, Array.mem_map] at hop
  obtain ⟨o, ho, hnum⟩ := hop
  have happA : o.applicableA σ :=
    (assemble_applicable (groundedOps d p rel) p.goal.toArray p.init.toArray
      (allObjects d p).toArray d.name ho habs).mp (by rw [hnum]; exact happ)
  have habs' : Abstracts (ground d p rel) (op.apply s) (o.applyA σ) := by
    rw [← hnum]
    exact assemble_apply (groundedOps d p rel) p.goal.toArray p.init.toArray
      (allObjects d p).toArray d.name ho (cost_pos hp rel o ho)
      (hreach.wf hwf) habs
  exact schemaStep_of_ops hp (walkSound d p rel) (pushSound d p rel) (jointChecked d p rel)
    (hc.boxesOne rel) (frameAddsKept hp rel)
    (ground_numFacts d p rel) o ho s (op.apply s) σ
    habs habs' hinv happA

open Planner.ExampleHeuristics.Sokoban in
/-- **Sokoban's shipped improved heuristic is zero at every reachable goal.** -/
theorem improved_goalAware_of_certified (hc : Certified d p) (rel : Bool) :
    (ground d p rel).GoalAwareOn (Reachable (ground d p rel))
      (improved (ground d p rel)).eval := by
  intro s hs hgoal
  exact improved_goalAware_of_schema _ (boxes_mem_goal d p rel) s hs.1 hgoal

open Planner.ExampleHeuristics.Sokoban in
/-- **Sokoban's shipped improved heuristic is consistent on reachable states.** -/
theorem improved_consistent_of_certified (hc : Certified d p) (rel : Bool) :
    (ground d p rel).ConsistentOn (Reachable (ground d p rel))
      (improved (ground d p rel)).eval := by
  have hp := hc.toPinned
  have hwf : Task.WF (ground d p rel) := ground_wf d p rel (cost_pos hp rel)
  exact improved_consistentOn_of_schema _ _
    (fun op hop s _ hr happ => schemaStep_of_reach hc rel hwf hr hop happ)
    (ops_cost hp rel)

open Planner.ExampleHeuristics.Sokoban in
/-- **Sokoban's shipped improved heuristic never overestimates** on any reachable
state, with relevance pruning on or off. -/
theorem improved_admissible_of_certified (hc : Certified d p) (rel : Bool) :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel))
      (improved (ground d p rel)).eval := by
  have hp := hc.toPinned
  have hwf : Task.WF (ground d p rel) := ground_wf d p rel (cost_pos hp rel)
  refine improved_admissibleOn_of_schema _ _ ?_ (boxes_mem_goal d p rel) ?_
    (ops_cost hp rel)
  · exact fun s i s' _ hr hstep => Reachable.step hr i hstep
  · exact fun op hop s _ hr happ => schemaStep_of_reach hc rel hwf hr hop happ

end Planner.Lifted.Sokoban

/- -------------------------------------------------------------------------- -/
/-
Soundness of the executable certificate for the improved Sokoban heuristic.
-/

namespace Planner.Lifted.Sokoban

open Planner Planner.Pddl

private theorem mem_adjacentTriples {p : Problem} {x y dd : Name} :
    (x, y, dd) ∈ ExampleHeuristics.Sokoban.Certificate.adjacentTriples p ↔
      adjacent x y dd ∈ p.init := by
  constructor
  · intro h
    obtain ⟨a, ha, hval⟩ := List.mem_filterMap.mp h
    by_cases hp : (a.pred == "adjacent") = true
    · rcases hargs : a.args with _ | ⟨u, rest⟩
      · rw [hargs] at hval; simp only [hp] at hval; simp at hval
      · cases rest with
        | nil => rw [hargs] at hval; simp only [hp] at hval; simp at hval
        | cons v rest =>
            cases rest with
            | nil => rw [hargs] at hval; simp only [hp] at hval; simp at hval
            | cons w rest =>
                cases rest with
                | cons _ _ => rw [hargs] at hval; simp only [hp] at hval; simp at hval
                | nil =>
                    rw [hargs] at hval
                    simp only [hp, Option.some.injEq, Prod.mk.injEq] at hval
                    obtain ⟨rfl, rfl, rfl⟩ := hval
                    have hpred : a.pred = "adjacent" := by simpa using hp
                    have heq : adjacent u v w = a := by
                      cases a
                      simp_all [adjacent]
                    rw [heq]
                    exact ha
    · simp only [Bool.not_eq_true] at hp
      rw [hp] at hval
      simp at hval
  · intro h
    refine List.mem_filterMap.mpr ⟨_, h, ?_⟩
    simp

private theorem mem_goalPairs {p : Problem} {b l : Name} :
    (b, l) ∈ ExampleHeuristics.Sokoban.Certificate.goalPairs p ↔
      atBox b l ∈ p.goal := by
  constructor
  · intro h
    obtain ⟨a, ha, hval⟩ := List.mem_filterMap.mp h
    by_cases hp : (a.pred == "at") = true
    · rcases hargs : a.args with _ | ⟨u, rest⟩
      · rw [hargs] at hval; simp only [hp] at hval; simp at hval
      · cases rest with
        | nil => rw [hargs] at hval; simp only [hp] at hval; simp at hval
        | cons v rest =>
            cases rest with
            | cons _ _ => rw [hargs] at hval; simp only [hp] at hval; simp at hval
            | nil =>
                rw [hargs] at hval
                simp only [hp, Option.some.injEq, Prod.mk.injEq] at hval
                obtain ⟨rfl, rfl⟩ := hval
                have hpred : a.pred = "at" := by simpa using hp
                have heq : atBox u v = a := by
                  cases a
                  simp_all [atBox]
                rw [heq]
                exact ha
    · simp only [Bool.not_eq_true] at hp
      rw [hp] at hval
      simp at hval
  · intro h
    refine List.mem_filterMap.mpr ⟨_, h, ?_⟩
    simp

theorem certificate_sound {d : Domain} {p : Problem}
    (hv : Validated d p)
    (h : ExampleHeuristics.Sokoban.Certificate.certified d p = true) :
    Certified d p := by
  simp only [ExampleHeuristics.Sokoban.Certificate.certified,
    ExampleHeuristics.Sokoban.Certificate.conditions, Certificate.passes,
    List.all_cons, List.all_nil, Bool.and_eq_true] at h
  rcases h with
    ⟨hactions, hlocType, hdirType, hboxType, hlocExact, hboxExact,
      hgoalNodup, hadjStatic, hgoalDynamic, hnoSelf, hreverses, hinit, hboxes⟩
  refine
    { domain := by simpa using hactions
      locationType := by simpa using hlocType
      directionType := by simpa using hdirType
      boxType := by simpa using hboxType
      locTypeExact := Certificate.exactType_sound hlocExact
      boxTypeExact := Certificate.exactType_sound hboxExact
      validated := hv
      goalNodup := of_decide_eq_true hgoalNodup
      adjacentStatic := by simpa using hadjStatic
      goalDynamic := ?_
      noSelfAdjacent := ?_
      adjReverses := ?_
      initCheck := ?_
      boxesOne := ?_ }
  · rw [List.all_eq_true] at hgoalDynamic
    intro a ha
    have hdyn := hgoalDynamic a ha
    simpa using hdyn
  · rw [ExampleHeuristics.Sokoban.Certificate.noSelfAdjacent,
      List.all_eq_true] at hnoSelf
    intro l dd hmem
    have hn := hnoSelf (l, l, dd) (mem_adjacentTriples.mpr hmem)
    simp at hn
  · rw [ExampleHeuristics.Sokoban.Certificate.adjacentReverses,
      List.all_eq_true] at hreverses
    intro l1 l2 dd hmem
    have hr := hreverses (l1, l2, dd) (mem_adjacentTriples.mpr hmem)
    rw [List.any_eq_true] at hr
    obtain ⟨⟨r1, r2, rdd⟩, hrmem, hcheck⟩ := hr
    simp only [Bool.and_eq_true, beq_iff_eq] at hcheck
    obtain ⟨⟨hr1, hr2⟩, hrtyped⟩ := hcheck
    subst r1
    subst r2
    obtain ⟨o, ho, honame, hotype⟩ := Certificate.objectNamedWithType_sound hrtyped
    refine ⟨rdd, ?_, mem_adjacentTriples.mp hrmem⟩
    rw [← honame]
    exact wellTyped_of_type ho hotype
  · simpa [ExampleHeuristics.Sokoban.Certificate.initInvCheck,
      Certificate.initPairs, Certificate.initOnes, initInvCheck,
      initPairs, initOnes] using hinit
  · have hgoal : ∀ b l l', atBox b l ∈ p.goal → atBox b l' ∈ p.goal → l = l' := by
      have hboxes' := hboxes.1
      rw [ExampleHeuristics.Sokoban.Certificate.goalBoxesOne,
        List.all_eq_true] at hboxes'
      intro b l l' h1 h2
      have hb := hboxes' (b, l) (mem_goalPairs.mpr h1)
      rw [List.all_eq_true] at hb
      have hsame := hb (b, l') (mem_goalPairs.mpr h2)
      simpa using hsame
    exact fun rel => boxesOne_of_goal hgoal rel

theorem improved_goalAware_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool)
    (h : ExampleHeuristics.Sokoban.Certificate.certified d p = true) :
    (ground d p rel).GoalAwareOn (Reachable (ground d p rel))
      (ExampleHeuristics.Sokoban.improved (ground d p rel)).eval :=
  improved_goalAware_of_certified (certificate_sound hv h) rel

theorem improved_consistent_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool)
    (h : ExampleHeuristics.Sokoban.Certificate.certified d p = true) :
    (ground d p rel).ConsistentOn (Reachable (ground d p rel))
      (ExampleHeuristics.Sokoban.improved (ground d p rel)).eval :=
  improved_consistent_of_certified (certificate_sound hv h) rel

theorem improved_proof_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool) :
    ImprovedProof d p rel
      (ExampleHeuristics.Sokoban.Certificate.certified d p)
      (ExampleHeuristics.Sokoban.improved (ground d p rel)) :=
  { goalAware := improved_goalAware_of_certificate hv rel
    consistent := improved_consistent_of_certificate hv rel }

theorem improved_admissible_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool)
    (h : ExampleHeuristics.Sokoban.Certificate.certified d p = true) :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel))
      (ExampleHeuristics.Sokoban.improved (ground d p rel)).eval :=
  (improved_proof_of_certificate hv rel).admissible h

end Planner.Lifted.Sokoban
