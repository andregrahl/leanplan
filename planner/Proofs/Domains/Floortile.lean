/-
Floortile's improved heuristic, proved end to end in one file.

The order below is the order the argument is built in.  The schema-level proof
comes first: the improved value over the domain's own data, and what each schema
does to the counters.  The rest lifts that value to the parsed domain and
compiles it against the numbered task.

The runtime heuristic and its data stay under `Planner/`.  The simple heuristic
of this domain is proved in `Proofs/Domains/FloortileSimple.lean`.
-/
import Planner.ExampleHeuristics.Floortile.Certificate
import Proofs.Heuristic
import Proofs.Combinators
import Proofs.Certificates
import Proofs.Distance
import Proofs.SchemaSupport
import Proofs.LiftedHeuristic
import Proofs.FactTables
import Proofs.CompileSupport
import Proofs.Reach
import Planner.ExampleHeuristics.Floortile.Improved

/- -------------------------------------------------------------------------- -/
/-
Floortile, improved heuristic: goal-aware, consistent, admissible.

The value is paints plus colour changes plus a movement bound, guarded by the
dead-end test that made this domain solvable at all.

`Effect` says how one action may move the three quantities.

  * `paint_*` discharges one tile.  It cannot also lower the colour count,
    because painting with a colour requires a robot to be holding it, so that
    colour was never counted as missing.
  * `change_color` lowers the colour count by at most one.
  * the four move schemas leave paints and colours alone and move the movement
    bound by at most one — that bound is itself a `max` of three lower bounds on
    the same family, so it moves by at most one when each of them does.

`consistent_deadEnd` keeps the dead-end test out of the arithmetic.  All it needs
is closure under successors, and that is the reason the test is sound in the
first place: the only schema adding `clear` is a robot leaving a square it already
occupied, so a painted tile is never clear again, the region a robot can walk in
only shrinks, and a forced square that is unreachable stays unreachable.

What is assumed rather than checked: that each grounded operator induces one of
the four effects, that dead-endedness is closed, and that the task is small
enough for the numeric part to stay below the dead-end constant.  All three are
decidable from the compiled data.
-/

namespace Planner.ExampleHeuristics.Floortile

open Planner

/-! ### The three quantities -/

abbrev Uc (d : Data) (s : State) : Nat := unpainted d s
abbrev Rc (d : Data) (s : State) : Nat := recolours d s
abbrev Mc (d : Data) (s : State) : Nat := movement d s

/-- How an action may move the three quantities: one constructor per schema family. -/
inductive Effect (d : Data) (s s' : State) : Prop
  | paint (hU : Uc d s' + 1 = Uc d s) (hR : Rc d s ≤ Rc d s') (hM : Mc d s ≤ Mc d s')
  | changeColour (hU : Uc d s' = Uc d s) (hR : Rc d s ≤ Rc d s' + 1) (hM : Mc d s ≤ Mc d s')
  | move (hU : Uc d s' = Uc d s) (hR : Rc d s ≤ Rc d s') (hM : Mc d s ≤ Mc d s' + 1)
  | other (hU : Uc d s' = Uc d s) (hR : Rc d s ≤ Rc d s') (hM : Mc d s ≤ Mc d s')

/-! ### Discharging the travel component

The travel bound is a maximum over unpainted tiles of the distance from the
nearest robot to a square that tile can be painted from — a maximum of minima.  A
move takes a robot one edge, which moves every one of those distances by at most
one, so the maximum does too.  Both folds go through the generic step lemmas.
-/

theorem travel_le_succ (d : Data) (s s' : State)
    (hunpainted : unpaintedTiles d s' = unpaintedTiles d s)
    (hstep : ∀ x, ∀ w ∈ robotPos d s', ∃ u ∈ robotPos d s,
        d.dist.get u x ≤ 1 + d.dist.get w x) :
    travel d s ≤ travel d s' + 1 := by
  unfold travel
  rw [hunpainted, ← Array.foldl_toList, ← Array.foldl_toList]
  have inner : ∀ tile : TileGoal,
      tile.paintFrom.foldl (init := d.dist.bound)
          (fun a x => min a (d.dist.minFrom (robotPos d s) x))
        ≤ 1 + tile.paintFrom.foldl (init := d.dist.bound)
          (fun a x => min a (d.dist.minFrom (robotPos d s') x)) := by
    intro tile
    rw [← Array.foldl_toList, ← Array.foldl_toList]
    refine foldl_min_le_succ _ _ _ (fun x _ => minFrom_le_succ d.dist _ _ x (hstep x)) _ _ ?_
    omega
  have := foldl_max_le_succ (unpaintedTiles d s).toList _ _ (fun tile _ => inner tile) 0 0 (by omega)
  simpa [Nat.add_comm] using this

theorem value_eq (d : Data) (s : State) :
    value d s = if isDead d s then deadEnd else baseValue d s := rfl

/-! ### The step -/

private theorem step_arith (U R M U' R' M' cost : Nat) (hcost : 1 ≤ cost)
    (h : (U' + 1 = U ∧ R ≤ R' ∧ M ≤ M') ∨
         (U' = U ∧ R ≤ R' + 1 ∧ M ≤ M') ∨
         (U' = U ∧ R ≤ R' ∧ M ≤ M' + 1)) :
    U + R + M ≤ cost + (U' + R' + M') := by
  rcases h with ⟨h1,h2,h3⟩|⟨h1,h2,h3⟩|⟨h1,h2,h3⟩ <;> omega

theorem base_step (d : Data) (s s' : State) (he : Effect d s s')
    (cost : Nat) (hcost : 1 ≤ cost) : baseValue d s ≤ cost + baseValue d s' := by
  show Uc d s + Rc d s + Mc d s ≤ cost + (Uc d s' + Rc d s' + Mc d s')
  refine step_arith _ _ _ _ _ _ cost hcost ?_
  cases he with
  | paint hU hR hM => exact Or.inl ⟨hU, hR, hM⟩
  | changeColour hU hR hM => exact Or.inr (Or.inl ⟨hU, hR, hM⟩)
  | move hU hR hM => exact Or.inr (Or.inr ⟨hU, hR, hM⟩)
  | other hU hR hM => exact Or.inr (Or.inr ⟨hU, hR, by omega⟩)

/-! ### Assembly -/

theorem unpaintedTiles_empty (d : Data) (s : State)
    (hall : ∀ t ∈ d.tiles, s.test t.goalFact = true) : unpaintedTiles d s = #[] := by
  unfold unpaintedTiles
  rw [Array.filter_eq_empty_iff]
  intro x hx
  simp [hall x hx]

theorem value_eq_zero_of_goal (d : Data) (s : State)
    (hall : ∀ t ∈ d.tiles, s.test t.goalFact = true) : value d s = 0 := by
  have he := unpaintedTiles_empty d s hall
  unfold value isDead baseValue unpainted recolours movement travel unattended
    forcedSquares coloursNeeded
  rw [he]
  simp [distinct]

theorem improved_goalAware (t : Task)
    (hcompiled : ∀ x ∈ (compile t).tiles, x.goalFact ∈ t.goal) :
    t.GoalAware (improved t).eval := by
  refine t.goalAware_of _ fun s _ hgoal => ?_
  exact value_eq_zero_of_goal _ s fun x hx => hgoal _ (hcompiled x hx)

/--
Consistency, given that each operator acts as one of the schemas does, that a
dead state stays dead, and that the numeric part stays below the dead-end
constant.  All three are decidable from the compiled data.
-/
theorem improved_consistent (t : Task)
    (heff : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      Effect (compile t) s (op.apply s))
    (hclosed : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      isDead (compile t) s = true → isDead (compile t) (op.apply s) = true)
    (hbound : ∀ s, baseValue (compile t) s ≤ deadEnd)
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost) :
    t.Consistent (improved t).eval := by
  have hval : (improved t).eval = fun s =>
      if isDead (compile t) s then deadEnd else baseValue (compile t) s := by
    funext s; exact value_eq _ _
  rw [hval]
  exact consistent_deadEnd _ _ hclosed hbound
    (fun op hop s hs happ _ _ => base_step _ s _ (heff op hop s hs happ) op.cost (hcost op hop))

/-- Never overestimates the cost of reaching the goal. -/
theorem improved_admissible (t : Task)
    (hcompiled : ∀ x ∈ (compile t).tiles, x.goalFact ∈ t.goal)
    (heff : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      Effect (compile t) s (op.apply s))
    (hclosed : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      isDead (compile t) s = true → isDead (compile t) (op.apply s) = true)
    (hbound : ∀ s, baseValue (compile t) s ≤ deadEnd)
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost) :
    t.Admissible (improved t).eval :=
  t.admissible _ (improved_goalAware t hcompiled) (improved_consistent t heff hclosed hbound hcost)


/-! ### Discharging the goal-count component from the operator

`Effect`'s hypotheses are statements about states, but the goal count follows from
facts about the operator alone — which of the family's goals it adds, which it
deletes — and those are decidable.  These two lemmas make that step, so a
certificate can establish it rather than a hypothesis assuming it.
-/

/-- `paint` achieves exactly one outstanding goal, so one fewer remains. -/
theorem goalCount_drop_one (d : Data) {n : Nat} {op : Op} {s : State}
    (hop : Op.WF n op) (hs : State.WF n s) (hnd : (d.tiles).toList.Nodup)
    (x : _) (hx : x ∈ d.tiles)
    (hxadd : op.add.contains ((·.goalFact) x) = true) (hxs : s.test ((·.goalFact) x) = false)
    (hother : ∀ y ∈ d.tiles, y ≠ x → op.add.contains ((·.goalFact) y) = false)
    (hdel : ∀ y ∈ d.tiles, op.del.contains ((·.goalFact) y) = false) :
    ((d.tiles).filter fun y => !(op.apply s).test ((·.goalFact) y)).size + 1
      = ((d.tiles).filter fun y => !s.test ((·.goalFact) y)).size :=
  unmet_drop_one d.tiles (·.goalFact) hop hs hnd x hx hxadd hxs hother hdel

/-- Any operator touching none of the unpainted goal tiles leaves the count alone. -/
theorem goalCount_unchanged (d : Data) {n : Nat} {op : Op} {s : State}
    (hop : Op.WF n op) (hs : State.WF n s)
    (hadd : ∀ y ∈ d.tiles, op.add.contains ((·.goalFact) y) = false)
    (hdel : ∀ y ∈ d.tiles, op.del.contains ((·.goalFact) y) = false) :
    ((d.tiles).filter fun y => !(op.apply s).test ((·.goalFact) y)).size
      = ((d.tiles).filter fun y => !s.test ((·.goalFact) y)).size :=
  unmet_unchanged d.tiles (·.goalFact) hop hs hadd hdel

end Planner.ExampleHeuristics.Floortile

/- -------------------------------------------------------------------------- -/
/-
Floortile, stated at the schema level.

`Effect` in `Improved.lean` assumes how one action moves the three counters.  This
file assumes only what the domain's schemas do to the predicates the heuristic
reads — which tiles are painted, which colour each robot holds, where the robots
stand — and derives the counters.

The `paint` case is where the argument lives.  Painting removes a tile from every
one of the three movement bounds, and none of them may fall: the robot painting it
was standing on a square that tile can be painted from, so that tile counted zero
towards the travel bound, was not unattended, and did not contribute a forced
square.  The colour it was painted with was in a robot's hand, so it was not a
colour still to be fetched either.
-/

namespace Planner.ExampleHeuristics.Floortile

open Planner

/-! ### The counters, over the whole tile list -/

/-- Still to paint. -/
def liveT (s : State) (t : TileGoal) : Bool := !s.test t.goalFact

/-- No robot stands on a square this tile can be painted from. -/
def unattendedP (d : Data) (s : State) (t : TileGoal) : Bool :=
  !t.paintFrom.any (robotPos d s).contains

theorem unpaintedTiles_toList (d : Data) (s : State) :
    (unpaintedTiles d s).toList = d.tiles.toList.filter (liveT s) := by
  unfold unpaintedTiles liveT
  rw [Array.toList_filter]

theorem unattended_eq (d : Data) (s : State) :
    unattended d s = (d.tiles.toList.filter fun t => unattendedP d s t && liveT s t).length := by
  unfold unattended
  rw [size_filter_toList, unpaintedTiles_toList, List.filter_filter]
  rfl

theorem travel_eq (d : Data) (s : State) :
    travel d s = d.tiles.toList.foldl (fun acc t =>
      max acc (if liveT s t then
        t.paintFrom.foldl (init := d.dist.bound) (fun a x =>
          min a (d.dist.minFrom (robotPos d s) x)) else 0)) 0 := by
  unfold travel
  rw [← Array.foldl_toList, unpaintedTiles_toList, foldl_max_filter]

theorem colours_eq (d : Data) (s : State) :
    coloursNeeded d s = distinct ((d.tiles.toList.filter (liveT s)).map (·.colour)) := by
  unfold coloursNeeded
  rw [unpaintedTiles_toList]

/-! ### What each schema does -/

/-- `paint_up` and `paint_down`: one tile is painted by a robot standing ready. -/
structure PaintStep (g : Graph) (d : Data) (s s' : State) (q : TileGoal) : Prop where
  memQ : q ∈ d.tiles
  unmetQ : s.test q.goalFact = false
  metQ' : s'.test q.goalFact = true
  frameTiles : ∀ t ∈ d.tiles, t ≠ q → s'.test t.goalFact = s.test t.goalFact
  robotSame : robotPos d s' = robotPos d s
  colourSame : ∀ c, ((d.hasColour.getD c #[]).any fun f => s'.test f)
    = ((d.hasColour.getD c #[]).any fun f => s.test f)
  /-- The robot painting stood on a square this tile can be painted from. -/
  attendedQ : ∃ p ∈ q.paintFrom, p ∈ robotPos d s ∧ p < g.size
  /-- Its forced square, if it has one, is where that robot stood. -/
  forcedOcc : ∀ p, q.forcedFrom = some p → (robotPos d s).contains p = true
  /-- The colour it was painted with was in a robot's hand. -/
  colourHeld : ((d.hasColour.getD q.colour #[]).any fun f => s.test f) = true

/-- `change_color`: only the colour in one robot's hand moves. -/
structure ColourStep (d : Data) (s s' : State) (acquired : Nat) : Prop where
  tilesSame : ∀ t ∈ d.tiles, s'.test t.goalFact = s.test t.goalFact
  robotSame : robotPos d s' = robotPos d s
  /-- The only colour that can newly appear in a hand is the one taken up. -/
  colourNew : ∀ c, ((d.hasColour.getD c #[]).any fun f => s.test f) = false →
    ((d.hasColour.getD c #[]).any fun f => s'.test f) = false ∨ c = acquired

/-- `up`, `down`, `left`, `right`: one robot moves one square. -/
structure MoveStep (d : Data) (s s' : State) (dest : Nat) : Prop where
  tilesSame : ∀ t ∈ d.tiles, s'.test t.goalFact = s.test t.goalFact
  colourSame : ∀ c, ((d.hasColour.getD c #[]).any fun f => s'.test f)
    = ((d.hasColour.getD c #[]).any fun f => s.test f)
  /-- One square changes each robot's distance to any square by at most one. -/
  stepBound : ∀ x, ∀ w ∈ robotPos d s', ∃ u ∈ robotPos d s,
    d.dist.get u x ≤ 1 + d.dist.get w x
  /-- The only square newly occupied is the one moved to. -/
  occNew : ∀ p, (robotPos d s').contains p = true →
    (robotPos d s).contains p = true ∨ p = dest
  /-- A square serves at most two tiles, so vacating one leaves at most two
  tiles unattended that were attended before. -/
  unattendedStep : unattended d s ≤ unattended d s' + 2

/-- One action of the domain. -/
inductive SchemaStep (g : Graph) (d : Data) (s s' : State) : Prop
  | paint (q : TileGoal) (h : PaintStep g d s s' q)
  | colour (acquired : Nat) (h : ColourStep d s s' acquired)
  | move (dest : Nat) (h : MoveStep d s s' dest)

/-! ### The counters, derived from the shapes -/

theorem unpainted_congr {d : Data} {s s' : State}
    (h : ∀ t ∈ d.tiles, s'.test t.goalFact = s.test t.goalFact) :
    unpaintedTiles d s' = unpaintedTiles d s :=
  array_filter_congr _ _ _ fun t ht => by simp [h t ht]

namespace PaintStep
variable {g : Graph} {d : Data} {s s' : State} {q : TileGoal}

theorem Uc_drop (h : PaintStep g d s s' q) (hnd : d.tiles.toList.Nodup) :
    Uc d s' + 1 = Uc d s :=
  unmet_size_drop d.tiles (·.goalFact) q h.memQ hnd h.unmetQ h.metQ' h.frameTiles

theorem Rc_le (h : PaintStep g d s s' q) : Rc d s ≤ Rc d s' := by
  show recolours d s ≤ recolours d s'
  unfold recolours
  refine length_le_of_subset _ _ ((distinct_nodup _).filter _) ?_
  intro c hc
  rw [List.mem_filter] at hc ⊢
  obtain ⟨hcm, hcp⟩ := hc
  have hnob : ((d.hasColour.getD c #[]).any fun f => s.test f) = false := by simpa using hcp
  have hcq : c ≠ q.colour := by
    rintro rfl; rw [h.colourHeld] at hnob; exact Bool.noConfusion hnob
  refine ⟨?_, by rw [h.colourSame c]; exact hcp⟩
  rw [colours_eq] at hcm ⊢
  rw [mem_distinct, List.mem_map] at hcm ⊢
  obtain ⟨t, ht, htc⟩ := hcm
  rw [List.mem_filter] at ht
  have hm : t ∈ d.tiles := by simpa using ht.1
  have htq : t ≠ q := by rintro rfl; exact hcq htc.symm
  exact ⟨t, by
    rw [List.mem_filter]
    exact ⟨ht.1, by simpa [liveT, h.frameTiles t hm htq] using ht.2⟩, htc⟩

theorem travel_le (h : PaintStep g d s s' q) (hsound : Distances.Sound g d.dist) :
    travel d s ≤ travel d s' := by
  rw [travel_eq, travel_eq]
  refine foldl_max_mono _ _ _ ?_ 0 0 (Nat.le_refl _)
  intro t ht
  have hm : t ∈ d.tiles := by simpa using ht
  by_cases htq : t = q
  · subst htq
    obtain ⟨p, hp, hpr, hplt⟩ := h.attendedQ
    have hz : d.dist.minFrom (robotPos d s) p = 0 := by
      have := minFrom_le_of_mem d.dist hpr p
      rw [hsound.self p hplt] at this
      omega
    have hzero : t.paintFrom.foldl (init := d.dist.bound)
        (fun a x => min a (d.dist.minFrom (robotPos d s) x)) = 0 := by
      rw [← Array.foldl_toList]
      have := foldl_min_le_mem t.paintFrom.toList
        (fun x => d.dist.minFrom (robotPos d s) x) (by simpa using hp) d.dist.bound
      rw [hz] at this
      omega
    simp [liveT, h.unmetQ, h.metQ', hzero]
  · simp [liveT, h.frameTiles t hm htq, h.robotSame]

theorem unattended_eq' (h : PaintStep g d s s' q) : unattended d s = unattended d s' := by
  rw [unattended_eq, unattended_eq]
  refine length_filter_congr _ _ _ ?_
  intro t ht
  have hm : t ∈ d.tiles := by simpa using ht
  by_cases htq : t = q
  · subst htq
    obtain ⟨p, hp, hpr, -⟩ := h.attendedQ
    have hany : t.paintFrom.any (robotPos d s).contains = true := by
      have hcontains : (robotPos d s).contains p = true := by simpa using hpr
      obtain ⟨i, hi, hival⟩ := Array.getElem_of_mem hp
      rw [Array.any_eq_true]
      exact ⟨i, hi, by rw [hival]; exact hcontains⟩
    have hatt : unattendedP d s t = false := by unfold unattendedP; rw [hany]; rfl
    simp [liveT, hatt, h.metQ']
  · simp [liveT, h.frameTiles t hm htq, unattendedP, h.robotSame]

theorem forced_le (h : PaintStep g d s s' q) :
    (forcedSquares d s).length ≤ (forcedSquares d s').length := by
  unfold forcedSquares
  refine length_le_of_subset _ _ (distinct_nodup _) ?_
  intro x hx
  rw [mem_distinct, List.mem_filterMap] at hx ⊢
  obtain ⟨t, ht, hval⟩ := hx
  have hmem : t ∈ d.tiles ∧ s.test t.goalFact = false := by
    simp only [unpaintedTiles, Array.toList_filter, List.mem_filter] at ht
    exact ⟨by simpa using ht.1, by simpa using ht.2⟩
  have htq : t ≠ q := by
    rintro rfl
    rcases hf : t.forcedFrom with _ | p
    · rw [hf] at hval; simp at hval
    · rw [hf] at hval
      have hocc := h.forcedOcc p hf
      simp only [hocc] at hval
      simp at hval
  refine ⟨t, ?_, ?_⟩
  · simp only [unpaintedTiles, Array.toList_filter, List.mem_filter]
    refine ⟨by simpa using hmem.1, ?_⟩
    simp [h.frameTiles t hmem.1 htq, hmem.2]
  · rw [h.robotSame]; exact hval

theorem Mc_le (h : PaintStep g d s s' q) (hsound : Distances.Sound g d.dist) :
    Mc d s ≤ Mc d s' := by
  have h1 := h.travel_le hsound
  have h2 := h.unattended_eq'
  have h3 := h.forced_le
  show max (max (travel d s) ((unattended d s + 1) / 2)) (forcedSquares d s).length
    ≤ max (max (travel d s') ((unattended d s' + 1) / 2)) (forcedSquares d s').length
  omega

end PaintStep

namespace ColourStep
variable {d : Data} {s s' : State} {acquired : Nat}

theorem Uc_eq (h : ColourStep d s s' acquired) : Uc d s' = Uc d s := by
  show (unpaintedTiles d s').size = (unpaintedTiles d s).size
  rw [unpainted_congr h.tilesSame]

theorem Rc_le (h : ColourStep d s s' acquired) : Rc d s ≤ Rc d s' + 1 := by
  show recolours d s ≤ recolours d s' + 1
  unfold recolours
  have hcol : coloursNeeded d s' = coloursNeeded d s := by
    unfold coloursNeeded
    rw [unpainted_congr h.tilesSame]
  rw [hcol]
  refine length_le_succ_of_subset _ _ acquired ((distinct_nodup _).filter _) ?_
  intro c hc
  rw [List.mem_filter] at hc
  obtain ⟨hcm, hcp⟩ := hc
  have hnob : ((d.hasColour.getD c #[]).any fun f => s.test f) = false := by simpa using hcp
  rcases h.colourNew c hnob with hnew | hacq
  · exact Or.inl (by rw [List.mem_filter]; exact ⟨hcm, by simp only [hnew, Bool.not_false]⟩)
  · exact Or.inr hacq

theorem Mc_eq (h : ColourStep d s s' acquired) : Mc d s' = Mc d s := by
  have hu : unpaintedTiles d s' = unpaintedTiles d s := unpainted_congr h.tilesSame
  have ht : travel d s' = travel d s := by unfold travel; rw [hu, h.robotSame]
  have hun : unattended d s' = unattended d s := by unfold unattended; rw [hu, h.robotSame]
  have hf : forcedSquares d s' = forcedSquares d s := by
    unfold forcedSquares; rw [hu, h.robotSame]
  show max (max (travel d s') ((unattended d s' + 1) / 2)) (forcedSquares d s').length
    = max (max (travel d s) ((unattended d s + 1) / 2)) (forcedSquares d s).length
  rw [ht, hun, hf]

end ColourStep

namespace MoveStep
variable {d : Data} {s s' : State} {dest : Nat}

theorem Uc_eq (h : MoveStep d s s' dest) : Uc d s' = Uc d s := by
  show (unpaintedTiles d s').size = (unpaintedTiles d s).size
  rw [unpainted_congr h.tilesSame]

theorem Rc_eq (h : MoveStep d s s' dest) : Rc d s' = Rc d s := by
  show recolours d s' = recolours d s
  unfold recolours
  have hcol : coloursNeeded d s' = coloursNeeded d s := by
    unfold coloursNeeded
    rw [unpainted_congr h.tilesSame]
  rw [hcol]
  congr 1
  exact List.filter_congr fun c _ => by rw [h.colourSame c]

theorem forced_le (h : MoveStep d s s' dest) :
    (forcedSquares d s).length ≤ (forcedSquares d s').length + 1 := by
  unfold forcedSquares
  refine length_le_succ_of_subset _ _ dest (distinct_nodup _) ?_
  intro x hx
  rw [mem_distinct, List.mem_filterMap] at hx
  obtain ⟨t, ht, hval⟩ := hx
  have hmem : t ∈ d.tiles ∧ s.test t.goalFact = false := by
    simp only [unpaintedTiles, Array.toList_filter, List.mem_filter] at ht
    exact ⟨by simpa using ht.1, by simpa using ht.2⟩
  rcases hf : t.forcedFrom with _ | p
  · rw [hf] at hval; simp at hval
  · rw [hf] at hval
    by_cases hocc : (robotPos d s).contains p = true
    · simp only [hocc] at hval; simp at hval
    · have hoccf : (robotPos d s).contains p = false := by simpa using hocc
      simp only [hoccf] at hval
      simp only [Bool.not_false, if_true, Option.some.injEq] at hval
      subst hval
      by_cases hxd : p = dest
      · exact Or.inr hxd
      · refine Or.inl ?_
        rw [mem_distinct, List.mem_filterMap]
        refine ⟨t, ?_, ?_⟩
        · simp only [unpaintedTiles, Array.toList_filter, List.mem_filter]
          refine ⟨by simpa using hmem.1, ?_⟩
          simp [h.tilesSame t hmem.1, hmem.2]
        · have hocc' : (robotPos d s').contains p = false := by
            by_contra hcon
            have hc2 : (robotPos d s').contains p = true := by simpa using hcon
            rcases h.occNew p hc2 with hc | hc
            · rw [hc] at hoccf; exact Bool.noConfusion hoccf
            · exact hxd hc
          rw [hf]
          simp only [hocc', Bool.not_false, if_true]

theorem Mc_le (h : MoveStep d s s' dest) : Mc d s ≤ Mc d s' + 1 := by
  have h1 : travel d s ≤ travel d s' + 1 :=
    travel_le_succ d s s' (unpainted_congr h.tilesSame) h.stepBound
  have h2 := h.unattendedStep
  have h3 := h.forced_le
  show max (max (travel d s) ((unattended d s + 1) / 2)) (forcedSquares d s).length
    ≤ max (max (travel d s') ((unattended d s' + 1) / 2)) (forcedSquares d s').length + 1
  omega

end MoveStep

/-! ### The consistency step, with nothing about the counters assumed -/

theorem effect_of_schema (g : Graph) (d : Data) (s s' : State)
    (hnd : d.tiles.toList.Nodup) (hsound : Distances.Sound g d.dist)
    (he : SchemaStep g d s s') : Effect d s s' := by
  cases he with
  | paint q h => exact .paint (h.Uc_drop hnd) h.Rc_le (h.Mc_le hsound)
  | colour a h => exact .changeColour h.Uc_eq h.Rc_le (Nat.le_of_eq h.Mc_eq.symm)
  | move dest h => exact .move h.Uc_eq (Nat.le_of_eq h.Rc_eq.symm) h.Mc_le

/-- Zero at every goal state, assuming only what the schemas do. -/
theorem improved_goalAware_of_schema (t : Task)
    (hcompiled : ∀ x ∈ (compile t).tiles, x.goalFact ∈ t.goal) :
    t.GoalAware (improved t).eval := improved_goalAware t hcompiled

/-- And never falls by more than one action costs. -/
theorem improved_consistent_of_schema (t : Task) (g : Graph)
    (hnd : (compile t).tiles.toList.Nodup)
    (hsound : Distances.Sound g (compile t).dist)
    (hstep : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      SchemaStep g (compile t) s (op.apply s))
    (hclosed : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      isDead (compile t) s = true → isDead (compile t) (op.apply s) = true)
    (hbound : ∀ s, baseValue (compile t) s ≤ deadEnd)
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost) :
    t.Consistent (improved t).eval :=
  improved_consistent t
    (fun op hop s hs happ => effect_of_schema g _ s _ hnd hsound (hstep op hop s hs happ))
    hclosed hbound hcost

/-- Never overestimates, assuming only that every operator is one of the schemas. -/
theorem improved_admissible_of_schema (t : Task) (g : Graph)
    (hcompiled : ∀ x ∈ (compile t).tiles, x.goalFact ∈ t.goal)
    (hnd : (compile t).tiles.toList.Nodup)
    (hsound : Distances.Sound g (compile t).dist)
    (hstep : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      SchemaStep g (compile t) s (op.apply s))
    (hclosed : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      isDead (compile t) s = true → isDead (compile t) (op.apply s) = true)
    (hbound : ∀ s, baseValue (compile t) s ≤ deadEnd)
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost) :
    t.Admissible (improved t).eval :=
  t.admissible _ (improved_goalAware_of_schema t hcompiled)
    (improved_consistent_of_schema t g hnd hsound hstep hclosed hbound hcost)

end Planner.ExampleHeuristics.Floortile

/- -------------------------------------------------------------------------- -/
/-
Which domain a Floortile task came from.

The equation on `actions` fixes the seven schemas exactly as the parser produces
them.  The four moves differ only in which of the four map relations they read,
so they share one shape.
-/

namespace Planner.Lifted.Floortile

open Planner Planner.Pddl

/-! ### The domain's atoms -/

def robotAt (r x : Name) : GroundAtom := { pred := "robot-at", args := [r, x] }
def robotHas (r c : Name) : GroundAtom := { pred := "robot-has", args := [r, c] }
def clearT (x : Name) : GroundAtom := { pred := "clear", args := [x] }
def painted (y c : Name) : GroundAtom := { pred := "painted", args := [y, c] }
def availableColor (c : Name) : GroundAtom := { pred := "available-color", args := [c] }
def upA (y x : Name) : GroundAtom := { pred := "up", args := [y, x] }
def downA (y x : Name) : GroundAtom := { pred := "down", args := [y, x] }
def rightA (y x : Name) : GroundAtom := { pred := "right", args := [y, x] }
def leftA (y x : Name) : GroundAtom := { pred := "left", args := [y, x] }

/-! ### The schemas, as the parser produces them -/

def robotP : TypedName := { name := "?r", type := "robot" }
def colorP (n : Name) : TypedName := { name := n, type := "color" }
def tileP (n : Name) : TypedName := { name := n, type := "tile" }

def robotAtV (r x : Name) : Atom := { pred := "robot-at", args := [.var r, .var x] }
def robotHasV (r c : Name) : Atom := { pred := "robot-has", args := [.var r, .var c] }
def clearV (x : Name) : Atom := { pred := "clear", args := [.var x] }
def paintedV (y c : Name) : Atom := { pred := "painted", args := [.var y, .var c] }
def availableV (c : Name) : Atom := { pred := "available-color", args := [.var c] }
def dirV (pred y x : Name) : Atom := { pred := pred, args := [.var y, .var x] }

def changeA : Action :=
  { name := "change_color", params := [robotP, colorP "?c", colorP "?c2"],
    pre := [robotHasV "?r" "?c", availableV "?c2"],
    add := [robotHasV "?r" "?c2"], del := [robotHasV "?r" "?c"], cost := 1 }

/-- `paint_up` and `paint_down` differ only in the map relation they read. -/
def paintA (name pred : Name) : Action :=
  { name := name, params := [robotP, tileP "?y", tileP "?x", colorP "?c"],
    pre := [robotHasV "?r" "?c", robotAtV "?r" "?x", dirV pred "?y" "?x", clearV "?y"],
    add := [paintedV "?y" "?c"], del := [clearV "?y"], cost := 1 }

/-- The four moves differ only in the map relation they read. -/
def moveA (name pred : Name) : Action :=
  { name := name, params := [robotP, tileP "?x", tileP "?y"],
    pre := [robotAtV "?r" "?x", dirV pred "?y" "?x", clearV "?y"],
    add := [robotAtV "?r" "?y", clearV "?x"],
    del := [robotAtV "?r" "?x", clearV "?y"], cost := 1 }

/-- The parsed domain is Floortile. -/
abbrev FloortileDomain (d : Domain) : Prop :=
  d.actions = [changeA, paintA "paint_up" "up", paintA "paint_down" "down",
    moveA "move_up" "up", moveA "move_down" "down",
    moveA "move_right" "right", moveA "move_left" "left"]

theorem robotHas_dynamic {d : Domain} (hd : FloortileDomain d) :
    (staticPredicates d).contains "robot-has" = false :=
  not_static_of_mem_add (a := changeA) (by rw [hd]; simp) (y := robotHasV "?r" "?c2")
    (by simp [changeA])

theorem robotAt_dynamic {d : Domain} (hd : FloortileDomain d) :
    (staticPredicates d).contains "robot-at" = false :=
  not_static_of_mem_add (a := moveA "move_up" "up") (by rw [hd]; simp)
    (y := robotAtV "?r" "?y") (by simp [moveA])

theorem clear_dynamic {d : Domain} (hd : FloortileDomain d) :
    (staticPredicates d).contains "clear" = false :=
  not_static_of_mem_del (a := paintA "paint_up" "up") (by rw [hd]; simp)
    (y := clearV "?y") (by simp [paintA])

theorem painted_dynamic {d : Domain} (hd : FloortileDomain d) :
    (staticPredicates d).contains "painted" = false :=
  not_static_of_mem_add (a := paintA "paint_up" "up") (by rw [hd]; simp)
    (y := paintedV "?y" "?c") (by simp [paintA])

/-! ### Instances -/

theorem instance_shape {d : Domain} {objects : List TypedName} (hd : FloortileDomain d)
    (i : Instance d objects) :
    (∃ r c c2, i.schema = changeA ∧ i.args = [r, c, c2]) ∨
    (∃ nm pr r y x c, i.schema = paintA nm pr ∧ i.args = [r, y, x, c] ∧
      (nm = "paint_up" ∧ pr = "up" ∨ nm = "paint_down" ∧ pr = "down")) ∨
    (∃ nm pr r x y, i.schema = moveA nm pr ∧ i.args = [r, x, y] ∧
      (nm = "move_up" ∧ pr = "up" ∨ nm = "move_down" ∧ pr = "down" ∨
       nm = "move_right" ∧ pr = "right" ∨ nm = "move_left" ∧ pr = "left")) := by
  have hmem : i.schema ∈ [changeA, paintA "paint_up" "up", paintA "paint_down" "down",
      moveA "move_up" "up", moveA "move_down" "down",
      moveA "move_right" "right", moveA "move_left" "left"] := hd ▸ i.mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with hs | hs | hs | hs | hs | hs | hs
  · obtain ⟨r, c, c2, ha, -, -, -⟩ := i.args_three (by rw [hs]; rfl)
    exact Or.inl ⟨r, c, c2, hs, ha⟩
  · obtain ⟨r, y, x, c, ha, -, -, -, -⟩ := i.args_four (by rw [hs]; rfl)
    exact Or.inr (Or.inl ⟨_, _, r, y, x, c, hs, ha, Or.inl ⟨rfl, rfl⟩⟩)
  · obtain ⟨r, y, x, c, ha, -, -, -, -⟩ := i.args_four (by rw [hs]; rfl)
    exact Or.inr (Or.inl ⟨_, _, r, y, x, c, hs, ha, Or.inr ⟨rfl, rfl⟩⟩)
  · obtain ⟨r, x, y, ha, -, -, -⟩ := i.args_three (by rw [hs]; rfl)
    exact Or.inr (Or.inr ⟨_, _, r, x, y, hs, ha, Or.inl ⟨rfl, rfl⟩⟩)
  · obtain ⟨r, x, y, ha, -, -, -⟩ := i.args_three (by rw [hs]; rfl)
    exact Or.inr (Or.inr ⟨_, _, r, x, y, hs, ha, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩)
  · obtain ⟨r, x, y, ha, -, -, -⟩ := i.args_three (by rw [hs]; rfl)
    exact Or.inr (Or.inr ⟨_, _, r, x, y, hs, ha, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩)
  · obtain ⟨r, x, y, ha, -, -, -⟩ := i.args_three (by rw [hs]; rfl)
    exact Or.inr (Or.inr ⟨_, _, r, x, y, hs, ha, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩)

theorem change_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {r c c2 : Name} (hs : i.schema = changeA) (ha : i.args = [r, c, c2]) :
    robotHas r c ∈ i.pre ∧ i.add = [robotHas r c2] ∧ i.del = [robotHas r c] := by
  have hp : i.pre = [robotHas r c, availableColor c2] := by rw [i.pre_eq, hs, ha]; rfl
  have hadd : i.add = [robotHas r c2] := by rw [i.add_eq, hs, ha]; rfl
  have hdel : i.del = [robotHas r c] := by rw [i.del_eq, hs, ha]; rfl
  simp [hp, hadd, hdel]

theorem paint_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {nm pr r y x c : Name} (hs : i.schema = paintA nm pr) (ha : i.args = [r, y, x, c]) :
    robotHas r c ∈ i.pre ∧ robotAt r x ∈ i.pre ∧ clearT y ∈ i.pre ∧
      ({ pred := pr, args := [y, x] } : GroundAtom) ∈ i.pre ∧
      i.add = [painted y c] ∧ i.del = [clearT y] := by
  have hp : i.pre = [robotHas r c, robotAt r x,
      { pred := pr, args := [y, x] }, clearT y] := by rw [i.pre_eq, hs, ha]; rfl
  have hadd : i.add = [painted y c] := by rw [i.add_eq, hs, ha]; rfl
  have hdel : i.del = [clearT y] := by rw [i.del_eq, hs, ha]; rfl
  simp [hp, hadd, hdel]

theorem move_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {nm pr r x y : Name} (hs : i.schema = moveA nm pr) (ha : i.args = [r, x, y]) :
    robotAt r x ∈ i.pre ∧ clearT y ∈ i.pre ∧
      ({ pred := pr, args := [y, x] } : GroundAtom) ∈ i.pre ∧
      i.add = [robotAt r y, clearT x] ∧ i.del = [robotAt r x, clearT y] := by
  have hp : i.pre = [robotAt r x, { pred := pr, args := [y, x] }, clearT y] := by
    rw [i.pre_eq, hs, ha]; rfl
  have hadd : i.add = [robotAt r y, clearT x] := by rw [i.add_eq, hs, ha]; rfl
  have hdel : i.del = [robotAt r x, clearT y] := by rw [i.del_eq, hs, ha]; rfl
  simp [hp, hadd, hdel]

end Planner.Lifted.Floortile

/- -------------------------------------------------------------------------- -/
/-
Floortile's improved heuristic over ground atoms.

The data has the same shape as the compiled heuristic, but its tables contain
atoms instead of fact numbers.  The walk over the still-clear region is the same
function on both sides, so the two agree as soon as their inputs do.
-/

namespace Planner.Lifted.Floortile

open Planner Planner.Pddl

/-- One unpainted goal tile. -/
structure TileGoal where
  goalAtom : GroundAtom
  colour : Nat
  paintFrom : Array Nat
  forcedFrom : Option Nat
  deriving Inhabited, DecidableEq

structure Cfg where
  dist : Distances
  adj : Array (Array Nat)
  clearAtoms : Array (Option GroundAtom)
  robotAt : Array (Array (GroundAtom × Nat))
  hasColour : Array (Array GroundAtom)
  tiles : Array TileGoal
  deriving Inhabited

@[inline] def robotPos (c : Cfg) (σ : AtomState) : Array Nat :=
  c.robotAt.filterMap fun atoms => (atoms.find? fun x => σ x.1).map (·.2)

def reachable (c : Cfg) (σ : AtomState) : Array Bool :=
  let robots := robotPos c σ
  reachFrom c.adj robots fun x =>
    robots.contains x ||
      (match c.clearAtoms.getD x none with
       | some a => σ a
       | none => false)

@[inline] def unpaintedTiles (c : Cfg) (σ : AtomState) : Array TileGoal :=
  c.tiles.filter fun t => !σ t.goalAtom

def isDead (c : Cfg) (σ : AtomState) : Bool :=
  let seen := reachable c σ
  (unpaintedTiles c σ).any fun tile =>
    match tile.forcedFrom with
    | some p => !seen.getD p false
    | none => !tile.paintFrom.any fun p => seen.getD p false

@[inline] def unpainted (c : Cfg) (σ : AtomState) : Nat := (unpaintedTiles c σ).size

@[inline] def coloursNeeded (c : Cfg) (σ : AtomState) : List Nat :=
  distinct ((unpaintedTiles c σ).toList.map (·.colour))

@[inline] def recolours (c : Cfg) (σ : AtomState) : Nat :=
  ((coloursNeeded c σ).filter fun col =>
      !(c.hasColour.getD col #[]).any σ).length

@[inline] def travel (c : Cfg) (σ : AtomState) : Nat :=
  (unpaintedTiles c σ).foldl (init := 0) fun acc tile =>
    max acc (tile.paintFrom.foldl (init := c.dist.bound) fun a x =>
      min a (c.dist.minFrom (robotPos c σ) x))

@[inline] def unattended (c : Cfg) (σ : AtomState) : Nat :=
  ((unpaintedTiles c σ).filter fun tile =>
      !tile.paintFrom.any (robotPos c σ).contains).size

@[inline] def forcedSquares (c : Cfg) (σ : AtomState) : List Nat :=
  distinct ((unpaintedTiles c σ).toList.filterMap fun tile =>
    match tile.forcedFrom with
    | some p => if !(robotPos c σ).contains p then some p else none
    | none => none)

@[inline] def movement (c : Cfg) (σ : AtomState) : Nat :=
  max (max (travel c σ) ((unattended c σ + 1) / 2)) (forcedSquares c σ).length

@[inline] def baseValue (c : Cfg) (σ : AtomState) : Nat :=
  unpainted c σ + recolours c σ + movement c σ

def value (c : Cfg) (σ : AtomState) : Nat :=
  if isDead c σ then deadEnd else baseValue c σ

/-! ### Goal awareness -/

theorem unpainted_empty (c : Cfg) (σ : AtomState)
    (hall : ∀ t ∈ c.tiles, σ t.goalAtom = true) : unpaintedTiles c σ = #[] := by
  unfold unpaintedTiles
  rw [Array.filter_eq_empty_iff]
  intro x hx
  simp [hall x hx]

theorem value_eq_zero (c : Cfg) (σ : AtomState)
    (hall : ∀ t ∈ c.tiles, σ t.goalAtom = true) : value c σ = 0 := by
  have he := unpainted_empty c σ hall
  unfold value isDead
  rw [he]
  simp only [Array.any_empty, Bool.false_eq_true, if_false]
  unfold baseValue unpainted recolours coloursNeeded
  unfold movement travel unattended forcedSquares
  rw [he]
  simp [distinct]

theorem liftedGoalAware (p : Problem) (c : Cfg)
    (hsub : ∀ t ∈ c.tiles, t.goalAtom ∈ p.goal) : LiftedGoalAware p (value c) := by
  intro σ hgoal
  exact value_eq_zero c σ fun t ht => hgoal t.goalAtom (by simpa using hsub t ht)

end Planner.Lifted.Floortile

/- -------------------------------------------------------------------------- -/
/-
Floortile, stated over ground atoms at the schema level.

The three shapes say only what the seven schemas do to the predicates — which
tile is painted, which colour is in which hand, where the robots stand — and the
four counters are derived.  One field is not about the predicates: a square
serves at most two tiles, so vacating one leaves at most two tiles unattended
that were attended before.  That is a property of the compiled tables and it is
checked, not derived.
-/

namespace Planner.Lifted.Floortile

open Planner Planner.Pddl

/-! ### The counters -/

abbrev Uc (cfg : Cfg) (σ : AtomState) : Nat := unpainted cfg σ
abbrev Rc (cfg : Cfg) (σ : AtomState) : Nat := recolours cfg σ
abbrev Mc (cfg : Cfg) (σ : AtomState) : Nat := movement cfg σ

/-- How an action may move the three quantities: one constructor per schema family. -/
inductive Effect (cfg : Cfg) (σ τ : AtomState) : Prop
  | paint (hU : Uc cfg τ + 1 = Uc cfg σ) (hR : Rc cfg σ ≤ Rc cfg τ) (hM : Mc cfg σ ≤ Mc cfg τ)
  | changeColour (hU : Uc cfg τ = Uc cfg σ) (hR : Rc cfg σ ≤ Rc cfg τ + 1) (hM : Mc cfg σ ≤ Mc cfg τ)
  | move (hU : Uc cfg τ = Uc cfg σ) (hR : Rc cfg σ ≤ Rc cfg τ) (hM : Mc cfg σ ≤ Mc cfg τ + 1)
  | other (hU : Uc cfg τ = Uc cfg σ) (hR : Rc cfg σ ≤ Rc cfg τ) (hM : Mc cfg σ ≤ Mc cfg τ)


/-! ### The counters, over the whole tile list -/

/-- Still to paint. -/
def liveT (σ : AtomState) (t : TileGoal) : Bool := !σ t.goalAtom

/-- No robot stands on a square this tile can be painted from. -/
def unattendedP (cfg : Cfg) (σ : AtomState) (t : TileGoal) : Bool :=
  !t.paintFrom.any (robotPos cfg σ).contains

theorem unpaintedTiles_toList (cfg : Cfg) (σ : AtomState) :
    (unpaintedTiles cfg σ).toList = cfg.tiles.toList.filter (liveT σ) := by
  unfold unpaintedTiles liveT
  rw [Array.toList_filter]

theorem unattended_eq (cfg : Cfg) (σ : AtomState) :
    unattended cfg σ = (cfg.tiles.toList.filter fun t => unattendedP cfg σ t && liveT σ t).length := by
  unfold unattended
  rw [size_filter_toList, unpaintedTiles_toList, List.filter_filter]
  rfl

theorem travel_eq (cfg : Cfg) (σ : AtomState) :
    travel cfg σ = cfg.tiles.toList.foldl (fun acc t =>
      max acc (if liveT σ t then
        t.paintFrom.foldl (init := cfg.dist.bound) (fun a x =>
          min a (cfg.dist.minFrom (robotPos cfg σ) x)) else 0)) 0 := by
  unfold travel
  rw [← Array.foldl_toList, unpaintedTiles_toList, foldl_max_filter]

theorem colours_eq (cfg : Cfg) (σ : AtomState) :
    coloursNeeded cfg σ = distinct ((cfg.tiles.toList.filter (liveT σ)).map (·.colour)) := by
  unfold coloursNeeded
  rw [unpaintedTiles_toList]

theorem travel_le_succ (cfg : Cfg) (σ τ : AtomState)
    (hunpainted : unpaintedTiles cfg τ = unpaintedTiles cfg σ)
    (hstep : ∀ x, ∀ w ∈ robotPos cfg τ, ∃ u ∈ robotPos cfg σ,
        cfg.dist.get u x ≤ 1 + cfg.dist.get w x) :
    travel cfg σ ≤ travel cfg τ + 1 := by
  unfold travel
  rw [hunpainted, ← Array.foldl_toList, ← Array.foldl_toList]
  have inner : ∀ tile : TileGoal,
      tile.paintFrom.foldl (init := cfg.dist.bound)
          (fun a x => min a (cfg.dist.minFrom (robotPos cfg σ) x))
        ≤ 1 + tile.paintFrom.foldl (init := cfg.dist.bound)
          (fun a x => min a (cfg.dist.minFrom (robotPos cfg τ) x)) := by
    intro tile
    rw [← Array.foldl_toList, ← Array.foldl_toList]
    refine foldl_min_le_succ _ _ _ (fun x _ => minFrom_le_succ cfg.dist _ _ x (hstep x)) _ _ ?_
    omega
  have := foldl_max_le_succ (unpaintedTiles cfg σ).toList _ _ (fun tile _ => inner tile) 0 0 (by omega)
  simpa [Nat.add_comm] using this


/-! ### What each schema does -/

/-- `paint_up` and `paint_down`: one tile is painted by a robot standing ready. -/
structure PaintStep (g : Graph) (cfg : Cfg) (σ τ : AtomState) (q : TileGoal) : Prop where
  memQ : q ∈ cfg.tiles
  unmetQ : σ q.goalAtom = false
  metQ' : τ q.goalAtom = true
  frameTiles : ∀ t ∈ cfg.tiles, t ≠ q → τ t.goalAtom = σ t.goalAtom
  robotSame : robotPos cfg τ = robotPos cfg σ
  colourSame : ∀ c, ((cfg.hasColour.getD c #[]).any fun f => τ f)
    = ((cfg.hasColour.getD c #[]).any fun f => σ f)
  /-- The robot painting stood on a square this tile can be painted from. -/
  attendedQ : ∃ p ∈ q.paintFrom, p ∈ robotPos cfg σ ∧ p < g.size
  /-- Its forced square, if it has one, is where that robot stood. -/
  forcedOcc : ∀ p, q.forcedFrom = some p → (robotPos cfg σ).contains p = true
  /-- The colour it was painted with was in a robot'σ hand. -/
  colourHeld : ((cfg.hasColour.getD q.colour #[]).any fun f => σ f) = true

/-- `change_color`: only the colour in one robot'σ hand moves. -/
structure ColourStep (cfg : Cfg) (σ τ : AtomState) (acquired : Nat) : Prop where
  tilesSame : ∀ t ∈ cfg.tiles, τ t.goalAtom = σ t.goalAtom
  robotSame : robotPos cfg τ = robotPos cfg σ
  /-- The only colour that can newly appear in a hand is the one taken up. -/
  colourNew : ∀ c, ((cfg.hasColour.getD c #[]).any fun f => σ f) = false →
    ((cfg.hasColour.getD c #[]).any fun f => τ f) = false ∨ c = acquired

/-- `up`, `down`, `left`, `right`: one robot moves one square. -/
structure MoveStep (cfg : Cfg) (σ τ : AtomState) (dest : Nat) : Prop where
  tilesSame : ∀ t ∈ cfg.tiles, τ t.goalAtom = σ t.goalAtom
  colourSame : ∀ c, ((cfg.hasColour.getD c #[]).any fun f => τ f)
    = ((cfg.hasColour.getD c #[]).any fun f => σ f)
  /-- One square changes each robot'σ distance to any square by at most one. -/
  stepBound : ∀ x, ∀ w ∈ robotPos cfg τ, ∃ u ∈ robotPos cfg σ,
    cfg.dist.get u x ≤ 1 + cfg.dist.get w x
  /-- The only square newly occupied is the one moved to. -/
  occNew : ∀ p, (robotPos cfg τ).contains p = true →
    (robotPos cfg σ).contains p = true ∨ p = dest
  /-- A square serves at most two tiles, so vacating one leaves at most two
  tiles unattended that were attended before. -/
  unattendedStep : unattended cfg σ ≤ unattended cfg τ + 2

/-- One action of the domain. -/
inductive SchemaStep (g : Graph) (cfg : Cfg) (σ τ : AtomState) : Prop
  | paint (q : TileGoal) (h : PaintStep g cfg σ τ q)
  | colour (acquired : Nat) (h : ColourStep cfg σ τ acquired)
  | move (dest : Nat) (h : MoveStep cfg σ τ dest)
  /-- A painting robot that stood above the tile it painted walls in the tile
  it stood on.  The state it reaches has no plan, so no bound is needed of it. -/
  | deadAfter (h : isDead cfg τ = true)

/-! ### The counters, derived from the shapes -/

theorem unpainted_congr {cfg : Cfg} {σ τ : AtomState}
    (h : ∀ t ∈ cfg.tiles, τ t.goalAtom = σ t.goalAtom) :
    unpaintedTiles cfg τ = unpaintedTiles cfg σ :=
  array_filter_congr _ _ _ fun t ht => by simp [h t ht]

namespace PaintStep
variable {g : Graph} {cfg : Cfg} {σ τ : AtomState} {q : TileGoal}

theorem Uc_drop (h : PaintStep g cfg σ τ q) (hnd : cfg.tiles.toList.Nodup) :
    Uc cfg τ + 1 = Uc cfg σ :=
  unmet_size_drop' cfg.tiles (·.goalAtom) (P := σ) (Q := τ) q h.memQ hnd h.unmetQ h.metQ' h.frameTiles

theorem Rc_le (h : PaintStep g cfg σ τ q) : Rc cfg σ ≤ Rc cfg τ := by
  show recolours cfg σ ≤ recolours cfg τ
  unfold recolours
  refine length_le_of_subset _ _ ((distinct_nodup _).filter _) ?_
  intro c hc
  rw [List.mem_filter] at hc ⊢
  obtain ⟨hcm, hcp⟩ := hc
  have hnob : ((cfg.hasColour.getD c #[]).any fun f => σ f) = false := by simpa using hcp
  have hcq : c ≠ q.colour := by
    rintro rfl; rw [h.colourHeld] at hnob; exact Bool.noConfusion hnob
  refine ⟨?_, by rw [h.colourSame c]; exact hcp⟩
  rw [colours_eq] at hcm ⊢
  rw [mem_distinct, List.mem_map] at hcm ⊢
  obtain ⟨t, ht, htc⟩ := hcm
  rw [List.mem_filter] at ht
  have hm : t ∈ cfg.tiles := by simpa using ht.1
  have htq : t ≠ q := by rintro rfl; exact hcq htc.symm
  exact ⟨t, by
    rw [List.mem_filter]
    exact ⟨ht.1, by simpa [liveT, h.frameTiles t hm htq] using ht.2⟩, htc⟩

theorem travel_le (h : PaintStep g cfg σ τ q) (hsound : Distances.Sound g cfg.dist) :
    travel cfg σ ≤ travel cfg τ := by
  rw [travel_eq, travel_eq]
  refine foldl_max_mono _ _ _ ?_ 0 0 (Nat.le_refl _)
  intro t ht
  have hm : t ∈ cfg.tiles := by simpa using ht
  by_cases htq : t = q
  · subst htq
    obtain ⟨p, hp, hpr, hplt⟩ := h.attendedQ
    have hz : cfg.dist.minFrom (robotPos cfg σ) p = 0 := by
      have := minFrom_le_of_mem cfg.dist hpr p
      rw [hsound.self p hplt] at this
      omega
    have hzero : t.paintFrom.foldl (init := cfg.dist.bound)
        (fun a x => min a (cfg.dist.minFrom (robotPos cfg σ) x)) = 0 := by
      rw [← Array.foldl_toList]
      have := foldl_min_le_mem t.paintFrom.toList
        (fun x => cfg.dist.minFrom (robotPos cfg σ) x) (by simpa using hp) cfg.dist.bound
      rw [hz] at this
      omega
    simp [liveT, h.unmetQ, h.metQ', hzero]
  · simp [liveT, h.frameTiles t hm htq, h.robotSame]

theorem unattended_eq' (h : PaintStep g cfg σ τ q) : unattended cfg σ = unattended cfg τ := by
  rw [unattended_eq, unattended_eq]
  refine length_filter_congr _ _ _ ?_
  intro t ht
  have hm : t ∈ cfg.tiles := by simpa using ht
  by_cases htq : t = q
  · subst htq
    obtain ⟨p, hp, hpr, -⟩ := h.attendedQ
    have hany : t.paintFrom.any (robotPos cfg σ).contains = true := by
      have hcontains : (robotPos cfg σ).contains p = true := by simpa using hpr
      obtain ⟨i, hi, hival⟩ := Array.getElem_of_mem hp
      rw [Array.any_eq_true]
      exact ⟨i, hi, by rw [hival]; exact hcontains⟩
    have hatt : unattendedP cfg σ t = false := by unfold unattendedP; rw [hany]; rfl
    simp [liveT, hatt, h.metQ']
  · simp [liveT, h.frameTiles t hm htq, unattendedP, h.robotSame]

theorem forced_le (h : PaintStep g cfg σ τ q) :
    (forcedSquares cfg σ).length ≤ (forcedSquares cfg τ).length := by
  unfold forcedSquares
  refine length_le_of_subset _ _ (distinct_nodup _) ?_
  intro x hx
  rw [mem_distinct, List.mem_filterMap] at hx ⊢
  obtain ⟨t, ht, hval⟩ := hx
  have hmem : t ∈ cfg.tiles ∧ σ t.goalAtom = false := by
    simp only [unpaintedTiles, Array.toList_filter, List.mem_filter] at ht
    exact ⟨by simpa using ht.1, by simpa using ht.2⟩
  have htq : t ≠ q := by
    rintro rfl
    rcases hf : t.forcedFrom with _ | p
    · rw [hf] at hval; simp at hval
    · rw [hf] at hval
      have hocc := h.forcedOcc p hf
      simp only [hocc] at hval
      simp at hval
  refine ⟨t, ?_, ?_⟩
  · simp only [unpaintedTiles, Array.toList_filter, List.mem_filter]
    refine ⟨by simpa using hmem.1, ?_⟩
    simp [h.frameTiles t hmem.1 htq, hmem.2]
  · rw [h.robotSame]; exact hval

theorem Mc_le (h : PaintStep g cfg σ τ q) (hsound : Distances.Sound g cfg.dist) :
    Mc cfg σ ≤ Mc cfg τ := by
  have h1 := h.travel_le hsound
  have h2 := h.unattended_eq'
  have h3 := h.forced_le
  show max (max (travel cfg σ) ((unattended cfg σ + 1) / 2)) (forcedSquares cfg σ).length
    ≤ max (max (travel cfg τ) ((unattended cfg τ + 1) / 2)) (forcedSquares cfg τ).length
  omega

end PaintStep

namespace ColourStep
variable {cfg : Cfg} {σ τ : AtomState} {acquired : Nat}

theorem Uc_eq (h : ColourStep cfg σ τ acquired) : Uc cfg τ = Uc cfg σ := by
  show (unpaintedTiles cfg τ).size = (unpaintedTiles cfg σ).size
  rw [unpainted_congr h.tilesSame]

theorem Rc_le (h : ColourStep cfg σ τ acquired) : Rc cfg σ ≤ Rc cfg τ + 1 := by
  show recolours cfg σ ≤ recolours cfg τ + 1
  unfold recolours
  have hcol : coloursNeeded cfg τ = coloursNeeded cfg σ := by
    unfold coloursNeeded
    rw [unpainted_congr h.tilesSame]
  rw [hcol]
  refine length_le_succ_of_subset _ _ acquired ((distinct_nodup _).filter _) ?_
  intro c hc
  rw [List.mem_filter] at hc
  obtain ⟨hcm, hcp⟩ := hc
  have hnob : ((cfg.hasColour.getD c #[]).any fun f => σ f) = false := by simpa using hcp
  rcases h.colourNew c hnob with hnew | hacq
  · exact Or.inl (by rw [List.mem_filter]; exact ⟨hcm, by simp only [hnew, Bool.not_false]⟩)
  · exact Or.inr hacq

theorem Mc_eq (h : ColourStep cfg σ τ acquired) : Mc cfg τ = Mc cfg σ := by
  have hu : unpaintedTiles cfg τ = unpaintedTiles cfg σ := unpainted_congr h.tilesSame
  have ht : travel cfg τ = travel cfg σ := by unfold travel; rw [hu, h.robotSame]
  have hun : unattended cfg τ = unattended cfg σ := by unfold unattended; rw [hu, h.robotSame]
  have hf : forcedSquares cfg τ = forcedSquares cfg σ := by
    unfold forcedSquares; rw [hu, h.robotSame]
  show max (max (travel cfg τ) ((unattended cfg τ + 1) / 2)) (forcedSquares cfg τ).length
    = max (max (travel cfg σ) ((unattended cfg σ + 1) / 2)) (forcedSquares cfg σ).length
  rw [ht, hun, hf]

end ColourStep

namespace MoveStep
variable {cfg : Cfg} {σ τ : AtomState} {dest : Nat}

theorem Uc_eq (h : MoveStep cfg σ τ dest) : Uc cfg τ = Uc cfg σ := by
  show (unpaintedTiles cfg τ).size = (unpaintedTiles cfg σ).size
  rw [unpainted_congr h.tilesSame]

theorem Rc_eq (h : MoveStep cfg σ τ dest) : Rc cfg τ = Rc cfg σ := by
  show recolours cfg τ = recolours cfg σ
  unfold recolours
  have hcol : coloursNeeded cfg τ = coloursNeeded cfg σ := by
    unfold coloursNeeded
    rw [unpainted_congr h.tilesSame]
  rw [hcol]
  congr 1
  exact List.filter_congr fun c _ => by rw [h.colourSame c]

theorem forced_le (h : MoveStep cfg σ τ dest) :
    (forcedSquares cfg σ).length ≤ (forcedSquares cfg τ).length + 1 := by
  unfold forcedSquares
  refine length_le_succ_of_subset _ _ dest (distinct_nodup _) ?_
  intro x hx
  rw [mem_distinct, List.mem_filterMap] at hx
  obtain ⟨t, ht, hval⟩ := hx
  have hmem : t ∈ cfg.tiles ∧ σ t.goalAtom = false := by
    simp only [unpaintedTiles, Array.toList_filter, List.mem_filter] at ht
    exact ⟨by simpa using ht.1, by simpa using ht.2⟩
  rcases hf : t.forcedFrom with _ | p
  · rw [hf] at hval; simp at hval
  · rw [hf] at hval
    by_cases hocc : (robotPos cfg σ).contains p = true
    · simp only [hocc] at hval; simp at hval
    · have hoccf : (robotPos cfg σ).contains p = false := by simpa using hocc
      simp only [hoccf] at hval
      simp only [Bool.not_false, if_true, Option.some.injEq] at hval
      subst hval
      by_cases hxd : p = dest
      · exact Or.inr hxd
      · refine Or.inl ?_
        rw [mem_distinct, List.mem_filterMap]
        refine ⟨t, ?_, ?_⟩
        · simp only [unpaintedTiles, Array.toList_filter, List.mem_filter]
          refine ⟨by simpa using hmem.1, ?_⟩
          simp [h.tilesSame t hmem.1, hmem.2]
        · have hocc' : (robotPos cfg τ).contains p = false := by
            by_contra hcon
            have hc2 : (robotPos cfg τ).contains p = true := by simpa using hcon
            rcases h.occNew p hc2 with hc | hc
            · rw [hc] at hoccf; exact Bool.noConfusion hoccf
            · exact hxd hc
          rw [hf]
          simp only [hocc', Bool.not_false, if_true]

theorem Mc_le (h : MoveStep cfg σ τ dest) : Mc cfg σ ≤ Mc cfg τ + 1 := by
  have h1 : travel cfg σ ≤ travel cfg τ + 1 :=
    travel_le_succ cfg σ τ (unpainted_congr h.tilesSame) h.stepBound
  have h2 := h.unattendedStep
  have h3 := h.forced_le
  show max (max (travel cfg σ) ((unattended cfg σ + 1) / 2)) (forcedSquares cfg σ).length
    ≤ max (max (travel cfg τ) ((unattended cfg τ + 1) / 2)) (forcedSquares cfg τ).length + 1
  omega

end MoveStep


/-! ### The step -/

theorem effect_of_schema (g : Graph) (cfg : Cfg) (σ τ : AtomState)
    (hnd : cfg.tiles.toList.Nodup) (hsound : Distances.Sound g cfg.dist)
    (hlive : isDead cfg τ = false) (he : SchemaStep g cfg σ τ) : Effect cfg σ τ := by
  cases he with
  | paint q h => exact .paint (h.Uc_drop hnd) h.Rc_le (h.Mc_le hsound)
  | colour a h => exact .changeColour h.Uc_eq h.Rc_le (Nat.le_of_eq h.Mc_eq.symm)
  | move dest h => exact .move h.Uc_eq (Nat.le_of_eq h.Rc_eq.symm) h.Mc_le
  | deadAfter h => rw [hlive] at h; exact absurd h (by simp)


private theorem length_distinct_le : ∀ l : List Nat, (distinct l).length ≤ l.length
  | [] => by simp [distinct]
  | x :: xs => by
      unfold distinct
      refine Nat.succ_le_succ (Nat.le_trans (List.length_filter_le _ _) (length_distinct_le xs))

theorem unpainted_le (cfg : Cfg) (σ : AtomState) : unpainted cfg σ ≤ cfg.tiles.size := by
  unfold unpainted unpaintedTiles
  exact Array.size_filter_le

theorem recolours_le (cfg : Cfg) (σ : AtomState) : recolours cfg σ ≤ cfg.tiles.size := by
  unfold recolours coloursNeeded
  have h1 : (unpaintedTiles cfg σ).toList.length ≤ cfg.tiles.size := by
    have : (unpaintedTiles cfg σ).size ≤ cfg.tiles.size := by
      unfold unpaintedTiles; exact Array.size_filter_le
    rwa [Array.length_toList]
  have h2 : (distinct ((unpaintedTiles cfg σ).toList.map (·.colour))).length
      ≤ (unpaintedTiles cfg σ).toList.length := by
    simpa [List.length_map] using
      (length_distinct_le ((unpaintedTiles cfg σ).toList.map (·.colour)))
  exact Nat.le_trans (List.length_filter_le _ _) (Nat.le_trans h2 h1)

theorem travel_le_bound (cfg : Cfg) (σ : AtomState) : travel cfg σ ≤ cfg.dist.bound := by
  unfold travel
  rw [← Array.foldl_toList]
  refine foldl_max_le_bound _ _ cfg.dist.bound ?_ 0 (Nat.zero_le _)
  intro tile _
  rw [← Array.foldl_toList]
  exact foldl_min_le_init _ _ _

theorem unattended_le (cfg : Cfg) (σ : AtomState) : unattended cfg σ ≤ cfg.tiles.size := by
  unfold unattended
  exact Nat.le_trans Array.size_filter_le (unpainted_le cfg σ)

theorem forcedSquares_le (cfg : Cfg) (σ : AtomState) :
    (forcedSquares cfg σ).length ≤ cfg.tiles.size := by
  unfold forcedSquares
  refine Nat.le_trans (length_distinct_le _) ?_
  refine Nat.le_trans (List.length_filterMap_le _ _) ?_
  have : (unpaintedTiles cfg σ).size ≤ cfg.tiles.size := by
    unfold unpaintedTiles; exact Array.size_filter_le
  rwa [Array.length_toList]

theorem movement_le (cfg : Cfg) (σ : AtomState) :
    movement cfg σ ≤ max cfg.dist.bound cfg.tiles.size := by
  unfold movement
  have hU : (unattended cfg σ + 1) / 2 ≤ cfg.tiles.size := by
    have := unattended_le cfg σ
    omega
  have hT := travel_le_bound cfg σ
  have hF := forcedSquares_le cfg σ
  omega

theorem baseValue_le (cfg : Cfg) (σ : AtomState) :
    baseValue cfg σ ≤ 2 * cfg.tiles.size + max cfg.dist.bound cfg.tiles.size := by
  unfold baseValue
  have := unpainted_le cfg σ
  have := recolours_le cfg σ
  have := movement_le cfg σ
  omega

theorem liftedConsistent {d : Domain} {p : Problem} (rel : Bool) (g : Graph) (cfg : Cfg)
    (Inv : AtomState → Prop) (hnd : cfg.tiles.toList.Nodup)
    (hsound : Distances.Sound g cfg.dist)
    (hshape : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ → o.applicableA σ →
      SchemaStep g cfg σ (o.applyA σ))
    (hdead : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ → o.applicableA σ →
      isDead cfg σ = true → isDead cfg (o.applyA σ) = true)
    (hsize : ∀ σ, baseValue cfg σ ≤ deadEnd)
    (hcost : ∀ o ∈ groundedOps d p rel, 0 < o.cost) :
    LiftedConsistentOn d p rel Inv (value cfg) := by
  intro o ho σ hinv happ
  have hc := hcost o ho
  unfold value
  by_cases hd : isDead cfg σ = true
  · rw [if_pos hd, if_pos (hdead o ho σ hinv happ hd)]
    omega
  · rw [if_neg (by simpa using hd)]
    by_cases hd' : isDead cfg (o.applyA σ) = true
    · rw [if_pos hd']
      exact Nat.le_trans (hsize σ) (Nat.le_add_left _ _)
    · rw [if_neg (by simpa using hd')]
      have he := effect_of_schema g cfg σ (o.applyA σ) hnd hsound (by simpa using hd')
        (hshape o ho σ hinv happ)
      show Uc cfg σ + Rc cfg σ + Mc cfg σ ≤ o.cost + (Uc cfg (o.applyA σ) + Rc cfg (o.applyA σ)
        + Mc cfg (o.applyA σ))
      cases he with
      | paint hU hR hM => omega
      | changeColour hU hR hM => omega
      | move hU hR hM => omega
      | other hU hR hM => omega

/-! ### The compiled boundary -/

theorem improved_goalAwareOn (d : Domain) (p : Problem) (rel : Bool) (cfg : Cfg)
    (Inv : AtomState → Prop)
    (hwf : Task.WF (ground d p rel))
    (hcost : ∀ o ∈ groundedOps d p rel, 0 < o.cost)
    (hsub : ∀ t ∈ cfg.tiles, t.goalAtom ∈ p.goal)
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hpres : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ →
      o.applicableA σ → Inv (o.applyA σ))
    (hv : State → Nat) (hcomp : ComputesOn (ground d p rel) Inv hv (value cfg)) :
    (ground d p rel).GoalAwareOn (Reachable (ground d p rel)) hv :=
  goalAwareOn_of_lifted d p rel hwf hcost hv (value cfg) Inv hcomp hinit hpres
    (liftedGoalAware p cfg hsub)

theorem improved_consistentOn (d : Domain) (p : Problem) (rel : Bool) (g : Graph)
    (cfg : Cfg) (Inv : AtomState → Prop)
    (hwf : Task.WF (ground d p rel))
    (hcost : ∀ o ∈ groundedOps d p rel, 0 < o.cost)
    (hnd : cfg.tiles.toList.Nodup) (hsound : Distances.Sound g cfg.dist)
    (hshape : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ → o.applicableA σ →
      SchemaStep g cfg σ (o.applyA σ))
    (hdead : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ → o.applicableA σ →
      isDead cfg σ = true → isDead cfg (o.applyA σ) = true)
    (hsize : ∀ σ, baseValue cfg σ ≤ deadEnd)
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hpres : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ →
      o.applicableA σ → Inv (o.applyA σ))
    (hv : State → Nat) (hcomp : ComputesOn (ground d p rel) Inv hv (value cfg)) :
    (ground d p rel).ConsistentOn (Reachable (ground d p rel)) hv :=
  consistentOn_of_lifted d p rel hwf hcost hv (value cfg) Inv hcomp hinit hpres
    (liftedConsistent rel g cfg Inv hnd hsound hshape hdead hsize hcost)

theorem improved_admissibleOn (d : Domain) (p : Problem) (rel : Bool) (g : Graph)
    (cfg : Cfg) (Inv : AtomState → Prop)
    (hwf : Task.WF (ground d p rel))
    (hcost : ∀ o ∈ groundedOps d p rel, 0 < o.cost)
    (hsub : ∀ t ∈ cfg.tiles, t.goalAtom ∈ p.goal)
    (hnd : cfg.tiles.toList.Nodup) (hsound : Distances.Sound g cfg.dist)
    (hshape : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ → o.applicableA σ →
      SchemaStep g cfg σ (o.applyA σ))
    (hdead : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ → o.applicableA σ →
      isDead cfg σ = true → isDead cfg (o.applyA σ) = true)
    (hsize : ∀ σ, baseValue cfg σ ≤ deadEnd)
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hpres : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ →
      o.applicableA σ → Inv (o.applyA σ))
    (hv : State → Nat) (hcomp : ComputesOn (ground d p rel) Inv hv (value cfg)) :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel)) hv :=
  admissibleOn_of_lifted d p rel hwf hcost hv (value cfg) Inv hcomp hinit hpres
    (liftedGoalAware p cfg hsub)
    (liftedConsistent rel g cfg Inv hnd hsound hshape hdead hsize hcost)

end Planner.Lifted.Floortile

/- -------------------------------------------------------------------------- -/
/-
The compiled Floortile tables and their atom-level meaning.

Each relation below says that a fact number names the atom in the corresponding
lifted entry.  The static parts of a tile — its colour, the squares it can be
painted from, its forced square — carry no facts, so they are asked to be equal.
-/

namespace Planner.Lifted.Floortile

open Planner Planner.Pddl

abbrev CData := ExampleHeuristics.Floortile.Data
abbrev CTile := ExampleHeuristics.Floortile.TileGoal

structure FactMatch (t : Task) (f : Fact) (a : GroundAtom) : Prop where
  name : t.factNames.getD f default = a
  range : f < t.factNames.size

structure PairMatch (t : Task) (x : Fact × Nat) (y : GroundAtom × Nat) : Prop where
  fact : FactMatch t x.1 y.1
  index : x.2 = y.2

structure TileMatch (t : Task) (x : CTile) (y : TileGoal) : Prop where
  goal : FactMatch t x.goalFact y.goalAtom
  colour : x.colour = y.colour
  paintFrom : x.paintFrom = y.paintFrom
  forcedFrom : x.forcedFrom = y.forcedFrom

/-- A table slot either holds a numbered fact and its atom, or is empty on both. -/
def OptMatch (t : Task) (x : Option Fact) (y : Option GroundAtom) : Prop :=
  match x, y with
  | some f, some a => FactMatch t f a
  | none, none => True
  | _, _ => False

structure DataMatches (t : Task) (c : Cfg) (dd : CData) : Prop where
  dist : dd.dist = c.dist
  adj : dd.adj = c.adj
  clear : List.Forall₂ (OptMatch t) dd.clearFacts.toList c.clearAtoms.toList
  robotAt : List.Forall₂ (fun xs ys =>
    List.Forall₂ (PairMatch t) xs.toList ys.toList) dd.robotAt.toList c.robotAt.toList
  hasColour : List.Forall₂ (fun xs ys =>
    List.Forall₂ (FactMatch t) xs.toList ys.toList) dd.hasColour.toList c.hasColour.toList
  tiles : List.Forall₂ (TileMatch t) dd.tiles.toList c.tiles.toList

theorem test_eq {t : Task} {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) {f : Fact} {a : GroundAtom}
    (h : FactMatch t f a) : s.test f = σ a := by
  rw [← h.name]
  exact (habs.numbered f (by rw [hn]; exact h.range)).symm

/-! ### Small paired-list facts -/

private theorem array_getD_toList {α : Type} (xs : Array α) (i : Nat) (d : α) :
    xs.getD i d = xs.toList.getD i d := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

private theorem forall₂_getD {α β : Type} {R : α → β → Prop} {da : α} {db : β}
    (hd : R da db) : ∀ {l : List α} {m : List β}, List.Forall₂ R l m →
      ∀ i, R (l.getD i da) (m.getD i db) := by
  intro l m h
  induction h with
  | nil => intro i; simpa using hd
  | @cons x y rest1 rest2 hxy _ ih =>
      intro i
      cases i with
      | zero => simpa using hxy
      | succ k => simpa using ih k

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

/-! ### Where the robots stand -/

private theorem positions_eq {t : Task}
    {xss : List (Array (Fact × Nat))} {yss : List (Array (GroundAtom × Nat))}
    (hm : List.Forall₂ (fun xs ys =>
      List.Forall₂ (PairMatch t) xs.toList ys.toList) xss yss)
    {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) :
    xss.filterMap (fun xs => (xs.find? fun x => s.test x.1).map (fun x => x.2)) =
      yss.filterMap (fun ys => (ys.find? fun y => σ y.1).map (fun y => y.2)) := by
  induction hm with
  | nil => rfl
  | @cons xs ys xss yss hxy _ ih =>
      have hloc : (xs.find? fun x => s.test x.1).map (fun x => x.2) =
          (ys.find? fun y => σ y.1).map (fun y => y.2) := by
        rw [← Array.find?_toList, ← Array.find?_toList]
        exact findLoc_eq hxy habs hn
      simp only [List.filterMap_cons]
      rw [hloc, ih]

theorem robotPos_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Floortile.robotPos dd s = robotPos c σ := by
  apply Array.toList_inj.mp
  simpa [ExampleHeuristics.Floortile.robotPos, robotPos, Array.toList_filterMap]
    using positions_eq hm.robotAt habs hn

/-! ### The walk over the still-clear region -/

theorem reachable_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Floortile.reachable dd s = reachable c σ := by
  have hrob := robotPos_matches hm habs hn
  show reachFrom dd.adj (ExampleHeuristics.Floortile.robotPos dd s) _
    = reachFrom c.adj (robotPos c σ) _
  rw [hm.adj, hrob]
  congr 1
  funext x
  congr 1
  have hopt := forall₂_getD (da := (none : Option Fact)) (db := (none : Option GroundAtom))
    trivial hm.clear x
  rw [← array_getD_toList, ← array_getD_toList] at hopt
  rcases hf : dd.clearFacts.getD x none with _ | f <;>
    rcases ha : c.clearAtoms.getD x none with _ | a <;>
    rw [hf, ha] at hopt <;>
    first
      | rfl
      | exact test_eq habs hn hopt
      | exact absurd hopt (by simp [OptMatch])

/-! ### The tiles still to paint -/

private theorem filterTiles {t : Task} {xs : List CTile} {ys : List TileGoal}
    (hm : List.Forall₂ (TileMatch t) xs ys)
    {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) :
    List.Forall₂ (TileMatch t)
      (xs.filter fun x => !s.test x.goalFact) (ys.filter fun y => !σ y.goalAtom) := by
  induction hm with
  | nil => exact List.Forall₂.nil
  | @cons x y xs ys hxy _ ih =>
      have ht := test_eq habs hn hxy.goal
      simp only [List.filter_cons, ht]
      by_cases hp : σ y.goalAtom
      · simp [hp, ih]
      · simp [hp, ih, hxy]

theorem unpainted_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    List.Forall₂ (TileMatch t)
      (ExampleHeuristics.Floortile.unpaintedTiles dd s).toList
      (unpaintedTiles c σ).toList := by
  simpa [ExampleHeuristics.Floortile.unpaintedTiles, unpaintedTiles, Array.toList_filter]
    using filterTiles hm.tiles habs hn

/-! ### The four terms -/

theorem unpaintedCount_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Floortile.unpainted dd s = unpainted c σ := by
  show (ExampleHeuristics.Floortile.unpaintedTiles dd s).size = (unpaintedTiles c σ).size
  rw [← Array.length_toList, ← Array.length_toList]
  exact (unpainted_matches hm habs hn).length_eq

theorem colours_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Floortile.coloursNeeded dd s = coloursNeeded c σ := by
  unfold ExampleHeuristics.Floortile.coloursNeeded coloursNeeded
  congr 1
  exact forall₂_map_eq (unpainted_matches hm habs hn) fun a b hab => hab.colour

theorem recolours_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Floortile.recolours dd s = recolours c σ := by
  unfold ExampleHeuristics.Floortile.recolours recolours
  rw [colours_matches hm habs hn]
  congr 1
  refine List.filter_congr (fun col _ => ?_)
  have hlist := forall₂_getD (da := (#[] : Array Fact)) (db := (#[] : Array GroundAtom))
    (by simpa using List.Forall₂.nil) hm.hasColour col
  rw [← array_getD_toList, ← array_getD_toList] at hlist
  congr 1
  rw [← Array.any_toList, ← Array.any_toList]
  exact forall₂_any hlist (fun a b hab => test_eq habs hn hab)

theorem travel_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Floortile.travel dd s = travel c σ := by
  have hrob := robotPos_matches hm habs hn
  unfold ExampleHeuristics.Floortile.travel travel
  rw [← Array.foldl_toList, ← Array.foldl_toList, hm.dist, hrob]
  have key : ∀ (xs : List CTile) (ys : List TileGoal),
      List.Forall₂ (TileMatch t) xs ys → ∀ acc : Nat,
      xs.foldl (fun acc tile => max acc (tile.paintFrom.foldl (init := c.dist.bound)
          fun a x => min a (c.dist.minFrom (robotPos c σ) x))) acc
        = ys.foldl (fun acc tile => max acc (tile.paintFrom.foldl (init := c.dist.bound)
          fun a x => min a (c.dist.minFrom (robotPos c σ) x))) acc := by
    intro xs ys h
    induction h with
    | nil => intro acc; rfl
    | @cons x y xs ys hxy _ ih =>
        intro acc
        simp only [List.foldl_cons, hxy.paintFrom]
        exact ih _
  exact key _ _ (unpainted_matches hm habs hn) 0

theorem unattended_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Floortile.unattended dd s = unattended c σ := by
  have hrob := robotPos_matches hm habs hn
  have key : ((ExampleHeuristics.Floortile.unpaintedTiles dd s).toList.filter
      (fun tile => !tile.paintFrom.any (ExampleHeuristics.Floortile.robotPos dd s).contains)).length
      = ((unpaintedTiles c σ).toList.filter
        (fun tile => !tile.paintFrom.any (robotPos c σ).contains)).length := by
    refine List.Forall₂.length_eq (R := TileMatch t) ?_
    refine forall₂_filter (unpainted_matches hm habs hn) (fun a b hab => ?_)
    rw [hab.paintFrom, hrob]
  show ((ExampleHeuristics.Floortile.unpaintedTiles dd s).filter _).size
    = ((unpaintedTiles c σ).filter _).size
  rw [size_filter_toList, size_filter_toList]
  exact key

theorem forced_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Floortile.forcedSquares dd s = forcedSquares c σ := by
  have hrob := robotPos_matches hm habs hn
  unfold ExampleHeuristics.Floortile.forcedSquares forcedSquares
  rw [hrob]
  congr 1
  exact forall₂_filterMap_eq (unpainted_matches hm habs hn) (fun a b hab => by
    rw [hab.forcedFrom]; rfl)

theorem isDead_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Floortile.isDead dd s = isDead c σ := by
  have hre := reachable_matches hm habs hn
  unfold ExampleHeuristics.Floortile.isDead isDead
  rw [hre, ← Array.any_toList, ← Array.any_toList]
  exact forall₂_any (unpainted_matches hm habs hn) (fun a b hab => by
    rw [hab.forcedFrom, hab.paintFrom]; rfl)

/-- The executable Floortile value computes the atom-level value. -/
theorem computes {t : Task} {c : Cfg} {dd : CData} (hm : DataMatches t c dd)
    (hn : t.numFacts = t.factNames.size) :
    Computes t (ExampleHeuristics.Floortile.value dd) (value c) := by
  intro s σ habs _
  unfold ExampleHeuristics.Floortile.value value
  rw [isDead_matches hm habs hn]
  by_cases hd : isDead c σ = true
  · rw [if_pos hd, if_pos hd]
  · rw [if_neg (by simpa using hd), if_neg (by simpa using hd)]
    show ExampleHeuristics.Floortile.unpainted dd s + ExampleHeuristics.Floortile.recolours dd s
      + ExampleHeuristics.Floortile.movement dd s
      = unpainted c σ + recolours c σ + movement c σ
    rw [unpaintedCount_matches hm habs hn, recolours_matches hm habs hn]
    congr 1
    unfold ExampleHeuristics.Floortile.movement movement
    rw [travel_matches hm habs hn, unattended_matches hm habs hn, forced_matches hm habs hn]

theorem computesOn_of_matches {t : Task} {c : Cfg} {dd : CData}
    (Inv : AtomState → Prop) (hm : DataMatches t c dd)
    (hn : t.numFacts = t.factNames.size) :
    ComputesOn t Inv (ExampleHeuristics.Floortile.value dd) (value c) := by
  intro s σ habs _
  exact computes hm hn s σ habs trivial


set_option maxHeartbeats 1000000 in
theorem compiled_goalAwareOn (d : Domain) (p : Problem) (rel : Bool) (c : Cfg)
    (Inv : AtomState → Prop)
    (hm : DataMatches (ground d p rel) c
      (ExampleHeuristics.Floortile.compile (ground d p rel)))
    (hwf : Task.WF (ground d p rel))
    (hcost : ∀ o ∈ groundedOps d p rel, 0 < o.cost)
    (hsub : ∀ q ∈ c.tiles, q.goalAtom ∈ p.goal)
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hpres : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ →
      o.applicableA σ → Inv (o.applyA σ)) :
    (ground d p rel).GoalAwareOn (Reachable (ground d p rel))
      (ExampleHeuristics.Floortile.improved (ground d p rel)).eval :=
  improved_goalAwareOn d p rel c Inv hwf hcost hsub hinit hpres _
    (computesOn_of_matches Inv hm rfl)

set_option maxHeartbeats 1000000 in
theorem compiled_consistentOn (d : Domain) (p : Problem) (rel : Bool) (g : Graph)
    (c : Cfg) (Inv : AtomState → Prop)
    (hm : DataMatches (ground d p rel) c
      (ExampleHeuristics.Floortile.compile (ground d p rel)))
    (hwf : Task.WF (ground d p rel))
    (hcost : ∀ o ∈ groundedOps d p rel, 0 < o.cost)
    (hnd : c.tiles.toList.Nodup) (hsound : Distances.Sound g c.dist)
    (hshape : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ → o.applicableA σ →
      SchemaStep g c σ (o.applyA σ))
    (hdead : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ → o.applicableA σ →
      isDead c σ = true → isDead c (o.applyA σ) = true)
    (hsize : ∀ σ, baseValue c σ ≤ deadEnd)
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hpres : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ →
      o.applicableA σ → Inv (o.applyA σ)) :
    (ground d p rel).ConsistentOn (Reachable (ground d p rel))
      (ExampleHeuristics.Floortile.improved (ground d p rel)).eval :=
  improved_consistentOn d p rel g c Inv hwf hcost hnd hsound hshape hdead hsize
    hinit hpres _ (computesOn_of_matches Inv hm rfl)

set_option maxHeartbeats 1000000 in
/-- **Admissible on the compiled task**, given the shape and the dead-end closure. -/
theorem compiled_admissibleOn (d : Domain) (p : Problem) (rel : Bool) (g : Graph)
    (c : Cfg) (Inv : AtomState → Prop)
    (hm : DataMatches (ground d p rel) c
      (ExampleHeuristics.Floortile.compile (ground d p rel)))
    (hwf : Task.WF (ground d p rel))
    (hcost : ∀ o ∈ groundedOps d p rel, 0 < o.cost)
    (hsub : ∀ q ∈ c.tiles, q.goalAtom ∈ p.goal)
    (hnd : c.tiles.toList.Nodup) (hsound : Distances.Sound g c.dist)
    (hshape : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ → o.applicableA σ →
      SchemaStep g c σ (o.applyA σ))
    (hdead : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ → o.applicableA σ →
      isDead c σ = true → isDead c (o.applyA σ) = true)
    (hsize : ∀ σ, baseValue c σ ≤ deadEnd)
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hpres : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ →
      o.applicableA σ → Inv (o.applyA σ)) :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel))
      (ExampleHeuristics.Floortile.improved (ground d p rel)).eval :=
  improved_admissibleOn d p rel g c Inv hwf hcost hsub hnd hsound hshape hdead hsize
    hinit hpres _ (computesOn_of_matches Inv hm rfl)

end Planner.Lifted.Floortile

/- -------------------------------------------------------------------------- -/
/-
The bridge from `compile` to the lifted `Cfg`.

The lifted configuration is the compiled tables read through the task's own
names, so the agreement holds by construction and only the fact ranges have to
be earned.
-/

namespace Planner.Lifted.Floortile

open Planner Planner.Pddl

/-- The atom a fact number names. -/
abbrev atomOf (t : Task) (f : Fact) : GroundAtom := t.factNames.getD f default

def tileOf (t : Task) (x : CTile) : TileGoal where
  goalAtom := atomOf t x.goalFact
  colour := x.colour
  paintFrom := x.paintFrom
  forcedFrom := x.forcedFrom

/-- The configuration a floortile task describes. -/
def cfgOf (t : Task) : Cfg where
  dist := (ExampleHeuristics.Floortile.compile t).dist
  adj := (ExampleHeuristics.Floortile.compile t).adj
  clearAtoms := (ExampleHeuristics.Floortile.compile t).clearFacts.map
    (Option.map (atomOf t))
  robotAt := (ExampleHeuristics.Floortile.compile t).robotAt.map fun xs =>
    xs.map fun y => (atomOf t y.1, y.2)
  hasColour := (ExampleHeuristics.Floortile.compile t).hasColour.map fun xs =>
    xs.map (atomOf t)
  tiles := (ExampleHeuristics.Floortile.compile t).tiles.map (tileOf t)

/-! ### Every fact the tables hold is numbered -/

theorem findMap_range {t : Task} {pred : Name} {P : Fact × GroundAtom → Bool} {f : Fact}
    (h : (((t.factsWith pred).find? P).map (·.1)) = some f) : f < t.factNames.size := by
  rcases hf : (t.factsWith pred).find? P with _ | y
  · rw [hf] at h; simp at h
  · rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    rw [← h]
    exact factsWith_ok y (Array.mem_of_find?_eq_some hf)

private theorem map_pair_fst {α : Type} {f : Fact} {o : Option α} {y : Fact × α}
    (h : o.map (fun i => (f, i)) = some y) : y.1 = f := by
  rcases o with _ | i
  · simp at h
  · simp only [Option.map_some, Option.some.injEq] at h
    rw [← h]

private theorem filterMap_fst_range {t : Task} {pred : Name} {α : Type}
    {g : (Fact × GroundAtom) → Option (Fact × α)}
    (hg : ∀ z y, g z = some y → y.1 = z.1)
    {y : Fact × α} (hy : y ∈ (t.factsWith pred).filterMap g) :
    y.1 < t.factNames.size := by
  obtain ⟨z, hz, hval⟩ := Array.mem_filterMap.mp hy
  rw [hg z y hval]
  exact factsWith_ok z hz

private theorem filterMap_range {t : Task} {pred : Name}
    {g : (Fact × GroundAtom) → Option Fact}
    (hg : ∀ z y, g z = some y → y = z.1)
    {y : Fact} (hy : y ∈ (t.factsWith pred).filterMap g) :
    y < t.factNames.size := by
  obtain ⟨z, hz, hval⟩ := Array.mem_filterMap.mp hy
  rw [hg z y hval]
  exact factsWith_ok z hz

theorem robotAtOf_range (t : Task) (g : Graph) (r : Name) :
    ∀ y ∈ ExampleHeuristics.Floortile.robotAtOf (t.factsWith "robot-at") g r,
      y.1 < t.factNames.size := by
  intro y hy
  obtain ⟨z, hz, hzw⟩ := Array.mem_filterMap.mp hy
  have hzr : z.1 < t.factNames.size := factsWith_ok z hz
  revert hzw
  rcases hargs : z.2.args with _ | ⟨x2, rest⟩
  · simp
  · cases rest with
    | nil => simp
    | cons l2 rest' =>
        cases rest' with
        | cons _ _ => simp
        | nil =>
            simp only []
            by_cases hx2 : (x2 == r) = true
            · simp only [hx2, if_true]
              intro h; rw [map_pair_fst h]; exact hzr
            · simp only [Bool.not_eq_true] at hx2
              simp [hx2]

theorem hasColourOf_range (t : Task) (col : Name) :
    ∀ f ∈ ExampleHeuristics.Floortile.hasColourOf (t.factsWith "robot-has") col,
      f < t.factNames.size := by
  intro f hf
  obtain ⟨z, hz, hzw⟩ := Array.mem_filterMap.mp hf
  have hzr : z.1 < t.factNames.size := factsWith_ok z hz
  revert hzw
  rcases hargs : z.2.args with _ | ⟨r2, rest⟩
  · simp
  · cases rest with
    | nil => simp
    | cons c2 rest' =>
        cases rest' with
        | cons _ _ => simp
        | nil =>
            simp only []
            by_cases hc2 : (c2 == col) = true
            · simp only [hc2, if_true, Option.some.injEq]
              intro h; rw [← h]; exact hzr
            · simp only [Bool.not_eq_true] at hc2
              simp [hc2]

private theorem pairMatch_of_range {t : Task} {y : Fact × Nat}
    (h : y.1 < t.factNames.size) : PairMatch t y (atomOf t y.1, y.2) :=
  ⟨⟨rfl, h⟩, rfl⟩

private theorem optMatch_map {t : Task} {x : Option Fact}
    (h : ∀ f, x = some f → f < t.factNames.size) :
    OptMatch t x (x.map (atomOf t)) := by
  rcases hx : x with _ | f
  · trivial
  · exact ⟨rfl, h f hx⟩

/-- **The compiled tables say of the task exactly what the lifted `Cfg` says.** -/
theorem dataMatches (t : Task) (hwf : Task.WF t) (hn : t.numFacts = t.factNames.size)
    (hsize : t.goalAtoms.size ≤ t.goal.size) :
    DataMatches t (cfgOf t) (ExampleHeuristics.Floortile.compile t) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · show List.Forall₂ _ _ (((ExampleHeuristics.Floortile.compile t).clearFacts.map _).toList)
    rw [Array.toList_map]
    refine forall₂_map_right _ ?_
    intro x hx
    refine optMatch_map ?_
    intro f hf
    have hx' : x ∈ (ExampleHeuristics.Floortile.compile t).clearFacts := by simpa using hx
    obtain ⟨nm, -, hval⟩ := Array.mem_map.mp hx'
    refine findMap_range (pred := "clear") (P := fun z => z.2.args == [nm]) ?_
    rw [show (((t.factsWith "clear").find? fun z => z.2.args == [nm]).map (·.1)) = x from hval, hf]
  · show List.Forall₂ _ _ (((ExampleHeuristics.Floortile.compile t).robotAt.map _).toList)
    rw [Array.toList_map]
    refine forall₂_map_right _ ?_
    intro xs hxs
    show List.Forall₂ (PairMatch t) xs.toList ((xs.map _).toList)
    rw [Array.toList_map]
    refine forall₂_map_right _ ?_
    intro y hy
    refine pairMatch_of_range ?_
    have hxs' : xs ∈ (ExampleHeuristics.Floortile.compile t).robotAt := by simpa using hxs
    obtain ⟨r, -, hval⟩ := Array.mem_map.mp hxs'
    rw [← hval] at hy
    exact robotAtOf_range t _ r y (by simpa using hy)
  · show List.Forall₂ _ _ (((ExampleHeuristics.Floortile.compile t).hasColour.map _).toList)
    rw [Array.toList_map]
    refine forall₂_map_right _ ?_
    intro xs hxs
    show List.Forall₂ (FactMatch t) xs.toList ((xs.map _).toList)
    rw [Array.toList_map]
    refine forall₂_map_right _ ?_
    intro f hf
    refine ⟨rfl, ?_⟩
    have hxs' : xs ∈ (ExampleHeuristics.Floortile.compile t).hasColour := by simpa using hxs
    obtain ⟨col, -, hval⟩ := Array.mem_map.mp hxs'
    rw [← hval] at hf
    exact hasColourOf_range t col f (by simpa using hf)
  · show List.Forall₂ _ _ (((ExampleHeuristics.Floortile.compile t).tiles.map _).toList)
    rw [Array.toList_map]
    refine forall₂_map_right _ ?_
    intro x hx
    refine ⟨⟨rfl, ?_⟩, rfl, rfl, rfl⟩
    have hx' : x ∈ (ExampleHeuristics.Floortile.compile t).tiles := by simpa using hx
    obtain ⟨z, hz, hzval⟩ := Array.mem_filterMap.mp hx'
    obtain ⟨-, hlt, -⟩ := Array.mem_zipIdx hz
    have hgoal : t.goal.getD z.2 0 < t.factNames.size := by
      have hlt2 : z.2 < t.goal.size := by omega
      have hmem : t.goal.getD z.2 0 ∈ t.goal := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt2]
        simpa using Array.getElem_mem hlt2
      rw [← hn]; exact hwf.goal _ hmem
    unfold ExampleHeuristics.Floortile.tileEntry at hzval
    by_cases hpred : (z.1.pred == "painted") = true
    · rcases hargs : z.1.args with _ | ⟨y2, rest⟩
      · simp only [hpred, hargs] at hzval; simp at hzval
      · cases rest with
        | nil => simp only [hpred, hargs] at hzval; simp at hzval
        | cons c2 rest' =>
            cases rest' with
            | cons _ _ => simp only [hpred, hargs] at hzval; simp at hzval
            | nil =>
                simp only [hpred, hargs] at hzval
                rcases hci : (Array.findIdx? (· == c2)
                    (t.objectsOfTypes ["color"])) with _ | ci
                · rw [hci] at hzval; simp at hzval
                · rw [hci] at hzval
                  simp only [Option.map_some, Option.some.injEq] at hzval
                  rw [← hzval]
                  exact hgoal
    · simp only [Bool.not_eq_true] at hpred
      simp only [hpred] at hzval
      simp at hzval

/-! ### On the task the planner grounds -/

theorem goal_size (d : Domain) (p : Problem) (rel : Bool) :
    (ground d p rel).goalAtoms.size ≤ (ground d p rel).goal.size := by
  show p.goal.toArray.size ≤ (p.goal.toArray.map _).size
  rw [Array.size_map]

/-- **The tables agree on the task the planner searches.** -/
theorem dataMatches_ground (d : Domain) (p : Problem) (rel : Bool)
    (hwf : Task.WF (ground d p rel)) :
    DataMatches (ground d p rel) (cfgOf (ground d p rel))
      (ExampleHeuristics.Floortile.compile (ground d p rel)) :=
  dataMatches _ hwf rfl (goal_size d p rel)

end Planner.Lifted.Floortile

/- -------------------------------------------------------------------------- -/
/-
Floortile's invariant, and its preservation.

A robot stands on one tile and holds one colour.  Both are true of a floortile
`:init` and survive all seven schemas: only `move` writes `robot-at`, and only
`change_color` writes `robot-has`.
-/

namespace Planner.Lifted.Floortile

open Planner Planner.Pddl

/-! ### Atoms of different predicates are different -/

@[simp] theorem robotAt_ne_robotHas (r x r' c : Name) : robotAt r x ≠ robotHas r' c := by
  simp [robotAt, robotHas]
@[simp] theorem robotAt_ne_clear (r x y : Name) : robotAt r x ≠ clearT y := by
  simp [robotAt, clearT]
@[simp] theorem robotAt_ne_painted (r x y c : Name) : robotAt r x ≠ painted y c := by
  simp [robotAt, painted]
@[simp] theorem robotHas_ne_robotAt (r c r' x : Name) : robotHas r c ≠ robotAt r' x := by
  simp [robotHas, robotAt]
@[simp] theorem robotHas_ne_clear (r c y : Name) : robotHas r c ≠ clearT y := by
  simp [robotHas, clearT]
@[simp] theorem robotHas_ne_painted (r c y c' : Name) : robotHas r c ≠ painted y c' := by
  simp [robotHas, painted]
@[simp] theorem clear_ne_robotAt (y r x : Name) : clearT y ≠ robotAt r x := by
  simp [clearT, robotAt]
@[simp] theorem clear_ne_robotHas (y r c : Name) : clearT y ≠ robotHas r c := by
  simp [clearT, robotHas]
@[simp] theorem clear_ne_painted (y z c : Name) : clearT y ≠ painted z c := by
  simp [clearT, painted]
@[simp] theorem painted_ne_robotAt (y c r x : Name) : painted y c ≠ robotAt r x := by
  simp [painted, robotAt]
@[simp] theorem painted_ne_robotHas (y c r c' : Name) : painted y c ≠ robotHas r c' := by
  simp [painted, robotHas]
@[simp] theorem painted_ne_clear (y c z : Name) : painted y c ≠ clearT z := by
  simp [painted, clearT]
@[simp] theorem robotAt_eq (r x r' x' : Name) :
    robotAt r x = robotAt r' x' ↔ r = r' ∧ x = x' := by simp [robotAt]
@[simp] theorem robotHas_eq (r c r' c' : Name) :
    robotHas r c = robotHas r' c' ↔ r = r' ∧ c = c' := by simp [robotHas]
@[simp] theorem clear_eq (y y' : Name) : clearT y = clearT y' ↔ y = y' := by simp [clearT]
@[simp] theorem painted_eq (y c y' c' : Name) :
    painted y c = painted y' c' ↔ y = y' ∧ c = c' := by simp [painted]

/-! ### The invariant -/

variable {d : Domain} {p : Problem} {o : AtomOp}

structure Inv (σ : AtomState) : Prop where
  /-- A robot stands on one tile. -/
  oneAt : ∀ r x x', σ (robotAt r x) = true → σ (robotAt r x') = true → x = x'
  /-- And holds one colour. -/
  oneHas : ∀ r c c', σ (robotHas r c) = true → σ (robotHas r c') = true → c = c'
  /-- One tile carries one robot. -/
  oneRobot : ∀ r r' x, σ (robotAt r x) = true → σ (robotAt r' x) = true → r = r'
  /-- A tile a robot stands on is not clear. -/
  noClearUnder : ∀ r x, σ (robotAt r x) = true → σ (clearT x) = false
  /-- A clear tile is not painted. -/
  clearNotPainted : ∀ x c, σ (clearT x) = true → σ (painted x c) = false
  /-- Nor is a tile a robot stands on: it was not clear when it was painted. -/
  occNotPainted : ∀ r x c, σ (robotAt r x) = true → σ (painted x c) = false

theorem inv_preserved (hd : FloortileDomain d) (hf : OpFacts d p o) {σ : AtomState}
    (hinv : Inv σ) (happ : o.applicableA σ) : Inv (o.applyA σ) := by
  have hatDyn : (staticPredicates d).contains (robotAt "" "").pred = false := by
    simpa [robotAt] using robotAt_dynamic hd
  have hhasDyn : (staticPredicates d).contains (robotHas "" "").pred = false := by
    simpa [robotHas] using robotHas_dynamic hd
  have hclDyn : (staticPredicates d).contains (clearT "").pred = false := by
    simpa [clearT] using clear_dynamic hd
  rcases instance_shape hd hf.inst with
    ⟨r, c, c2, hs, ha⟩ | ⟨nm, pr, r, y, x, c, hs, ha, -⟩ | ⟨nm, pr, r, x, y, hs, ha, -⟩
  · -- change_color: only the colour in one hand moves
    obtain ⟨hpre, hadd, hdel⟩ := change_atoms hf.inst hs ha
    have hrc : σ (robotHas r c) = true := pre_holds hf hpre hhasDyn happ
    have hfrAt : ∀ r' z, o.applyA σ (robotAt r' z) = σ (robotAt r' z) := fun r' z =>
      frame_of_lists hf hadd hdel (by simp) (by simp) σ
    have hfrCl : ∀ z, o.applyA σ (clearT z) = σ (clearT z) := fun z =>
      frame_of_lists hf hadd hdel (by simp) (by simp) σ
    have hfrPa : ∀ z c', o.applyA σ (painted z c') = σ (painted z c') := fun z c' =>
      frame_of_lists hf hadd hdel (by simp) (by simp) σ
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro r' u v h1 h2
      rw [hfrAt] at h1 h2; exact hinv.oneAt r' u v h1 h2
    · intro r' a b h1 h2
      by_cases hr : r' = r
      · subst hr
        have key : ∀ z, o.applyA σ (robotHas r' z) = true → z = c2 := by
          intro z hz
          by_cases hz2 : z = c2
          · exact hz2
          · exfalso
            have hnadd : robotHas r' z ∉ [robotHas r' c2] := by simp [hz2]
            by_cases hzc : z = c
            · subst hzc
              rw [falsified_of_lists hf hadd hdel hnadd (by simp) hpre hhasDyn σ] at hz
              exact Bool.noConfusion hz
            · rw [frame_of_lists hf hadd hdel hnadd (by simp [hzc]) σ] at hz
              exact hzc (hinv.oneHas r' z c hz hrc)
        rw [key a h1, key b h2]
      · rw [frame_of_lists hf hadd hdel (by simp [hr]) (by simp [hr]) σ] at h1 h2
        exact hinv.oneHas r' a b h1 h2
    · intro r1 r2 z h1 h2
      rw [hfrAt] at h1 h2; exact hinv.oneRobot r1 r2 z h1 h2
    · intro r' z h1
      rw [hfrAt] at h1; rw [hfrCl]; exact hinv.noClearUnder r' z h1
    · intro z c' h1
      rw [hfrCl] at h1; rw [hfrPa]; exact hinv.clearNotPainted z c' h1
    · intro r' z c' h1
      rw [hfrAt] at h1; rw [hfrPa]; exact hinv.occNotPainted r' z c' h1
  · -- paint: one tile is painted, and stops being clear
    obtain ⟨hpreC, hpreA, hpreCl, -, hadd, hdel⟩ := paint_atoms hf.inst hs ha
    have hrx : σ (robotAt r x) = true := pre_holds hf hpreA hatDyn happ
    have hcly : σ (clearT y) = true := pre_holds hf hpreCl hclDyn happ
    have hnoy : ∀ r', σ (robotAt r' y) = false := by
      intro r'
      by_contra hc
      rw [hinv.noClearUnder r' y (by simpa using hc)] at hcly
      exact Bool.noConfusion hcly
    have hfrAt : ∀ r' z, o.applyA σ (robotAt r' z) = σ (robotAt r' z) := fun r' z =>
      frame_of_lists hf hadd hdel (by simp) (by simp) σ
    have hcly' : o.applyA σ (clearT y) = false :=
      falsified_of_lists hf hadd hdel (by simp) (by simp) hpreCl hclDyn σ
    have hfrCl : ∀ z, z ≠ y → o.applyA σ (clearT z) = σ (clearT z) := fun z hz =>
      frame_of_lists hf hadd hdel (by simp) (by simp [hz]) σ
    have hfrPa : ∀ z c', z ≠ y → o.applyA σ (painted z c') = σ (painted z c') :=
      fun z c' hz => frame_of_lists hf hadd hdel (by simp [hz]) (by simp) σ
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro r' u v h1 h2
      rw [hfrAt] at h1 h2; exact hinv.oneAt r' u v h1 h2
    · intro r' a b h1 h2
      rw [frame_of_lists hf hadd hdel (by simp) (by simp) σ] at h1 h2
      exact hinv.oneHas r' a b h1 h2
    · intro r1 r2 z h1 h2
      rw [hfrAt] at h1 h2; exact hinv.oneRobot r1 r2 z h1 h2
    · intro r' z h1
      rw [hfrAt] at h1
      by_cases hz : z = y
      · rw [hz]; exact hcly'
      · rw [hfrCl z hz]; exact hinv.noClearUnder r' z h1
    · intro z c' h1
      by_cases hz : z = y
      · rw [hz, hcly'] at h1; exact absurd h1 (by simp)
      · rw [hfrCl z hz] at h1
        rw [hfrPa z c' hz]; exact hinv.clearNotPainted z c' h1
    · intro r' z c' h1
      rw [hfrAt] at h1
      by_cases hz : z = y
      · rw [hz] at h1; rw [hnoy r'] at h1; exact absurd h1 (by simp)
      · rw [hfrPa z c' hz]; exact hinv.occNotPainted r' z c' h1
  · -- move: one robot changes tile, freeing the one it leaves
    obtain ⟨hpreA, hpreCl, -, hadd, hdel⟩ := move_atoms hf.inst hs ha
    have hrx : σ (robotAt r x) = true := pre_holds hf hpreA hatDyn happ
    have hcly : σ (clearT y) = true := pre_holds hf hpreCl hclDyn happ
    have hclx : σ (clearT x) = false := hinv.noClearUnder r x hrx
    have hxy : x ≠ y := by
      intro hc; rw [hc, hcly] at hclx; exact Bool.noConfusion hclx
    have hnoy : ∀ r', σ (robotAt r' y) = false := by
      intro r'
      by_contra hc
      rw [hinv.noClearUnder r' y (by simpa using hc)] at hcly
      exact Bool.noConfusion hcly
    have hfrPa : ∀ z c', o.applyA σ (painted z c') = σ (painted z c') := fun z c' =>
      frame_of_lists hf hadd hdel (by simp) (by simp) σ
    have hcly' : o.applyA σ (clearT y) = false :=
      falsified_of_lists hf hadd hdel (by simp [Ne.symm hxy]) (by simp) hpreCl hclDyn σ
    have hfrCl : ∀ z, z ≠ y → z ≠ x → o.applyA σ (clearT z) = σ (clearT z) :=
      fun z hzy hzx => frame_of_lists hf hadd hdel (by simp [hzx]) (by simp [hzy]) σ
    have hfrOther : ∀ r' z, r' ≠ r → o.applyA σ (robotAt r' z) = σ (robotAt r' z) :=
      fun r' z hr => frame_of_lists hf hadd hdel (by simp [hr]) (by simp [hr]) σ
    have hkey : ∀ z, o.applyA σ (robotAt r z) = true → z = y := by
      intro z hz
      by_cases hzy : z = y
      · exact hzy
      · exfalso
        have hnadd : robotAt r z ∉ [robotAt r y, clearT x] := by simp [hzy]
        by_cases hzx : z = x
        · subst hzx
          rw [falsified_of_lists hf hadd hdel hnadd (by simp) hpreA hatDyn σ] at hz
          exact Bool.noConfusion hz
        · rw [frame_of_lists hf hadd hdel hnadd (by simp [hzx]) σ] at hz
          exact hzx (hinv.oneAt r z x hz hrx)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro r' u v h1 h2
      by_cases hr : r' = r
      · subst hr; rw [hkey u h1, hkey v h2]
      · rw [hfrOther r' u hr] at h1; rw [hfrOther r' v hr] at h2
        exact hinv.oneAt r' u v h1 h2
    · intro r' a b h1 h2
      rw [frame_of_lists hf hadd hdel (by simp) (by simp) σ] at h1 h2
      exact hinv.oneHas r' a b h1 h2
    · intro r1 r2 z h1 h2
      by_cases h1r : r1 = r
      · subst h1r
        by_cases h2r : r2 = r1
        · exact h2r.symm
        · exfalso
          rw [hfrOther r2 z h2r] at h2
          rw [hkey z h1, hnoy r2] at h2
          exact Bool.noConfusion h2
      · by_cases h2r : r2 = r
        · exfalso
          subst h2r
          rw [hfrOther r1 z h1r] at h1
          rw [hkey z h2, hnoy r1] at h1
          exact Bool.noConfusion h1
        · rw [hfrOther r1 z h1r] at h1; rw [hfrOther r2 z h2r] at h2
          exact hinv.oneRobot r1 r2 z h1 h2
    · intro r' z h1
      by_cases hr : r' = r
      · subst hr
        rw [hkey z h1]; exact hcly'
      · rw [hfrOther r' z hr] at h1
        by_cases hzy : z = y
        · rw [hzy]; exact hcly'
        · by_cases hzx : z = x
          · exact absurd (hinv.oneRobot r' r x (hzx ▸ h1) hrx) hr
          · rw [hfrCl z hzy hzx]; exact hinv.noClearUnder r' z h1
    · intro z c' h1
      rw [hfrPa]
      by_cases hzx : z = x
      · rw [hzx]; exact hinv.occNotPainted r x c' hrx
      · by_cases hzy : z = y
        · rw [hzy, hcly'] at h1; exact absurd h1 (by simp)
        · rw [hfrCl z hzy hzx] at h1; exact hinv.clearNotPainted z c' h1
    · intro r' z c' h1
      rw [hfrPa]
      by_cases hr : r' = r
      · subst hr
        rw [hkey z h1]; exact hinv.clearNotPainted y c' hcly
      · rw [hfrOther r' z hr] at h1; exact hinv.occNotPainted r' z c' h1

/-! ### `:init` satisfies it, and the planner can check that -/

def initInvCheck (p : Problem) : Bool :=
  ((initPairs p "robot-at").all fun x =>
    (initPairs p "robot-at").all fun y => !(x.1 == y.1) || (x.2 == y.2)) &&
  ((initPairs p "robot-has").all fun x =>
    (initPairs p "robot-has").all fun y => !(x.1 == y.1) || (x.2 == y.2)) &&
  ((initPairs p "robot-at").all fun x =>
    (initPairs p "robot-at").all fun y => !(x.2 == y.2) || (x.1 == y.1)) &&
  ((initPairs p "robot-at").all fun x => !(initOnes p "clear").contains x.2) &&
  ((initOnes p "clear").all fun x =>
    (initPairs p "painted").all fun y => !(y.1 == x)) &&
  ((initPairs p "robot-at").all fun x =>
    (initPairs p "painted").all fun y => !(y.1 == x.2))

theorem initInv_of_check {p : Problem} (h : initInvCheck p = true) :
    Inv (fun a => p.init.toArray.contains a) := by
  simp only [initInvCheck, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  have atMem : ∀ r x, (p.init.toArray.contains (robotAt r x)) = true →
      (r, x) ∈ initPairs p "robot-at" := by
    intro r x hx; exact mem_initPairs.mpr (by simpa [robotAt] using hx)
  have clMem : ∀ x, (p.init.toArray.contains (clearT x)) = true →
      x ∈ initOnes p "clear" := by
    intro x hx; exact mem_initOnes.mpr (by simpa [clearT] using hx)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r x x' hx hx'
    simpa using h1 (r, x) (atMem r x hx) (r, x') (atMem r x' hx')
  · intro r c c' hc hc'
    have m1 : (r, c) ∈ initPairs p "robot-has" := mem_initPairs.mpr (by simpa [robotHas] using hc)
    have m2 : (r, c') ∈ initPairs p "robot-has" := mem_initPairs.mpr (by simpa [robotHas] using hc')
    simpa using h2 (r, c) m1 (r, c') m2
  · intro r r' x hr hr'
    simpa using h3 (r, x) (atMem r x hr) (r', x) (atMem r' x hr')
  · intro r x hr
    by_contra hc
    have hthis := h4 (r, x) (atMem r x hr)
    have hmem := clMem x (by simpa using hc)
    rw [show ((initOnes p "clear").contains (r, x).2) = true from by simpa using hmem] at hthis
    simp at hthis
  · intro x c hx
    by_contra hc
    have hm : (x, c) ∈ initPairs p "painted" :=
      mem_initPairs.mpr (by simpa [painted] using (by simpa using hc :
        (p.init.toArray.contains (painted x c)) = true))
    simpa using h5 x (clMem x hx) (x, c) hm
  · intro r x c hr
    by_contra hc
    have hm : (x, c) ∈ initPairs p "painted" :=
      mem_initPairs.mpr (by simpa [painted] using (by simpa using hc :
        (p.init.toArray.contains (painted x c)) = true))
    simpa using h6 (r, x) (atMem r x hr) (x, c) hm

end Planner.Lifted.Floortile

/- -------------------------------------------------------------------------- -/
/-
What the compiled floortile tables hold, read as atoms.

The robot table holds `robot-at(r, x)` with the node index of `x`, the colour
table holds `robot-has(r, c)` over all robots, and a tile entry holds its
`painted` goal.
-/

namespace Planner.Lifted.Floortile

open Planner Planner.Pddl

/-- The objects the robot table is indexed by. -/
abbrev robots (t : Task) : Array Name := t.objectsOfTypes ["robot"]

/-- And the colour table. -/
abbrev colours (t : Task) : Array Name := t.objectsOfTypes ["color"]

theorem getD_map_lt {α β : Type} (xs : Array α) (f : α → β) {k : Nat} (a : α)
    (b : β) (hk : k < xs.size) : (xs.map f).getD k b = f (xs.getD k a) := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hk),
    Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk]
  simp

theorem getD_map {α β : Type} (xs : Array α) (f : α → β) (k : Nat) (a : α)
    (b : β) (hd : f a = b) : (xs.map f).getD k b = f (xs.getD k a) := by
  by_cases hk : k < xs.size
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hk),
      Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk]
    simp
  · rw [Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none (by simpa using Nat.le_of_not_lt hk),
      Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt hk)]
    simpa using hd.symm

theorem mem_robotAtOf (t : Task) (g : Graph) (r : Name) {y : Fact × Nat}
    (hy : y ∈ ExampleHeuristics.Floortile.robotAtOf (t.factsWith "robot-at") g r) :
    ∃ x, atomOf t y.1 = robotAt r x ∧ g.find? x = some y.2 := by
  obtain ⟨z, hz, hval⟩ := Array.mem_filterMap.mp hy
  obtain ⟨-, hname, hpred⟩ := mem_factsWith hz
  revert hval
  rcases hargs : z.2.args with _ | ⟨u, rest⟩
  · simp
  · cases rest with
    | nil => simp
    | cons l rest' =>
        cases rest' with
        | cons _ _ => simp
        | nil =>
            simp only []
            by_cases hu : (u == r) = true
            · simp only [hu, if_true]
              rcases hfd : g.find? l with _ | i
              · simp
              · simp only [Option.map_some, Option.some.injEq]
                intro h
                refine ⟨l, ?_, ?_⟩
                · rw [← h]
                  show t.factNames.getD z.1 default = robotAt r l
                  rw [hname]
                  unfold robotAt
                  rw [← hpred, show r = u from (by simpa using hu : u = r).symm, ← hargs]
                · rw [← h]; exact hfd
            · simp only [Bool.not_eq_true] at hu
              simp [hu]

theorem mem_robotAtOf_total (t : Task) (g : Graph) (r x : Name) {f : Fact} {i : Nat}
    (hf : f < t.factNames.size) (hname : atomOf t f = robotAt r x)
    (hi : g.find? x = some i) :
    (f, i) ∈ ExampleHeuristics.Floortile.robotAtOf (t.factsWith "robot-at") g r := by
  refine Array.mem_filterMap.mpr ⟨(f, robotAt r x), mem_factsWith_of_named hf hname rfl, ?_⟩
  simp only [robotAt, hi]
  simp

theorem mem_hasColourOf (t : Task) (col : Name) {f : Fact}
    (hf : f ∈ ExampleHeuristics.Floortile.hasColourOf (t.factsWith "robot-has") col) :
    ∃ r, atomOf t f = robotHas r col := by
  obtain ⟨z, hz, hval⟩ := Array.mem_filterMap.mp hf
  obtain ⟨-, hname, hpred⟩ := mem_factsWith hz
  revert hval
  rcases hargs : z.2.args with _ | ⟨r, rest⟩
  · simp
  · cases rest with
    | nil => simp
    | cons c2 rest' =>
        cases rest' with
        | cons _ _ => simp
        | nil =>
            simp only []
            by_cases hc : (c2 == col) = true
            · simp only [hc, if_true, Option.some.injEq]
              intro h
              refine ⟨r, ?_⟩
              rw [← h]
              show t.factNames.getD z.1 default = robotHas r col
              rw [hname]
              unfold robotHas
              rw [← hpred, show col = c2 from (by simpa using hc : c2 = col).symm, ← hargs]
            · simp only [Bool.not_eq_true] at hc
              simp [hc]

theorem mem_hasColourOf_total (t : Task) (r col : Name) {f : Fact}
    (hf : f < t.factNames.size) (hname : atomOf t f = robotHas r col) :
    f ∈ ExampleHeuristics.Floortile.hasColourOf (t.factsWith "robot-has") col := by
  refine Array.mem_filterMap.mpr ⟨(f, robotHas r col),
    mem_factsWith_of_named hf hname rfl, ?_⟩
  simp [robotHas]

/-! ### The robot table of the lifted configuration -/

theorem robotAt_data (t : Task) {xs : Array (GroundAtom × Nat)}
    (hxs : xs ∈ (cfgOf t).robotAt) : ∃ r ∈ robots t, ∀ y ∈ xs, ∃ x,
      y.1 = robotAt r x := by
  have hxs' : xs ∈ ((ExampleHeuristics.Floortile.compile t).robotAt).map
      (fun zs => zs.map fun u => (atomOf t u.1, u.2)) := hxs
  obtain ⟨zs, hzs, hzval⟩ := Array.mem_map.mp hxs'
  have hzs' : zs ∈ (robots t).map (ExampleHeuristics.Floortile.robotAtOf
    (t.factsWith "robot-at") _) := hzs
  obtain ⟨r, hr, hrval⟩ := Array.mem_map.mp hzs'
  refine ⟨r, hr, ?_⟩
  intro y hy
  rw [← hzval] at hy
  obtain ⟨u, hu, huval⟩ := Array.mem_map.mp hy
  rw [← hrval] at hu
  obtain ⟨x, hatom, -⟩ := mem_robotAtOf t _ r hu
  exact ⟨x, by rw [← huval]; exact hatom⟩

/-- And the colour table. -/
theorem hasColour_data (t : Task) {xs : Array GroundAtom}
    (hxs : xs ∈ (cfgOf t).hasColour) : ∃ col ∈ colours t, ∀ a ∈ xs, ∃ r,
      a = robotHas r col := by
  have hxs' : xs ∈ ((ExampleHeuristics.Floortile.compile t).hasColour).map
      (fun zs => zs.map (atomOf t)) := hxs
  obtain ⟨zs, hzs, hzval⟩ := Array.mem_map.mp hxs'
  have hzs' : zs ∈ (colours t).map (ExampleHeuristics.Floortile.hasColourOf
    (t.factsWith "robot-has")) := hzs
  obtain ⟨col, hc, hcval⟩ := Array.mem_map.mp hzs'
  refine ⟨col, hc, ?_⟩
  intro a ha
  rw [← hzval] at ha
  obtain ⟨u, hu, huval⟩ := Array.mem_map.mp ha
  rw [← hcval] at hu
  obtain ⟨r, hatom⟩ := mem_hasColourOf t col hu
  exact ⟨r, by rw [← huval]; exact hatom⟩

/-! ### Frames -/

/-- The robots do not move when no `robot-at` atom does. -/
theorem robotPos_congr {t : Task} {σ τ : AtomState}
    (h : ∀ xs ∈ (cfgOf t).robotAt, ∀ y ∈ xs, τ y.1 = σ y.1) :
    robotPos (cfgOf t) τ = robotPos (cfgOf t) σ := by
  unfold robotPos
  apply Array.toList_inj.mp
  rw [Array.toList_filterMap, Array.toList_filterMap]
  refine List.filterMap_congr ?_
  intro xs hxs
  congr 1
  exact array_find?_congr _ _ _ (fun y hy => h xs (by simpa using hxs) y hy)

/-- And the colours in hand do not move when no `robot-has` atom does. -/
theorem hasColour_congr {t : Task} {σ τ : AtomState} (col : Nat)
    (h : ∀ xs ∈ (cfgOf t).hasColour, ∀ a ∈ xs, τ a = σ a) :
    (((cfgOf t).hasColour.getD col #[]).any τ)
      = (((cfgOf t).hasColour.getD col #[]).any σ) := by
  by_cases hk : col < (cfgOf t).hasColour.size
  · refine array_any_congr _ _ _ (fun a ha => h _ ?_ a ha)
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk]
    simpa using Array.getElem_mem hk
  · rw [Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none (by simpa using Nat.le_of_not_lt hk)]
    simp


/-! ### The walk reaches nothing it may not enter -/

/-- A square the walk marks carries a robot, or is clear. -/
theorem reachable_guarded (c : Cfg) (σ : AtomState) (n : Nat)
    (h : (reachable c σ).getD n false = true) :
    (robotPos c σ).contains n = true ∨
      (match c.clearAtoms.getD n none with | some a => σ a | none => false) = true := by
  rcases Reach.reachFrom_guarded c.adj (robotPos c σ) _ n h with h1 | h2
  · exact Or.inl h1
  · rcases Bool.or_eq_true_iff.mp h2 with h3 | h4
    · exact Or.inl h3
    · exact Or.inr h4

/-! ### Reading the dead-end test -/

/-- The square is clear according to the table. -/
def clearAt (c : Cfg) (σ : AtomState) (u : Nat) : Bool :=
  match c.clearAtoms.getD u none with
  | some a => σ a
  | none => false

/-- The squares the walk may enter. -/
def enterableOf (c : Cfg) (σ : AtomState) (u : Nat) : Bool :=
  (robotPos c σ).contains u || clearAt c σ u

theorem reachable_eq (c : Cfg) (σ : AtomState) :
    reachable c σ = reachFrom c.adj (robotPos c σ) (enterableOf c σ) := rfl

theorem reachable_least (c : Cfg) (σ : AtomState) (Q : Nat → Prop)
    (hstart : ∀ p ∈ robotPos c σ, Q p)
    (hclosed : ∀ u v, Q u → v ∈ c.adj.getD u #[] → enterableOf c σ v = true →
      v < c.adj.size → Q v) :
    ∀ p, (reachable c σ).getD p false = true → Q p := by
  rw [reachable_eq]
  exact Reach.reachFrom_least c.adj (robotPos c σ) (enterableOf c σ) Q hstart hclosed

theorem reachable_closed (c : Cfg) (σ : AtomState) :
    ∀ u v, (reachable c σ).getD u false = true → v ∈ c.adj.getD u #[] →
      enterableOf c σ v = true → v < c.adj.size →
      (reachable c σ).getD v false = true := by
  rw [reachable_eq]
  exact Reach.reachFrom_closed c.adj (robotPos c σ) (enterableOf c σ)

theorem reachable_start (c : Cfg) (σ : AtomState) {p : Nat} (hp : p ∈ robotPos c σ)
    (hlt : p < c.adj.size) : (reachable c σ).getD p false = true := by
  rw [reachable_eq]
  refine Reach.reachFrom_start c.adj (robotPos c σ) (enterableOf c σ) hp ?_ hlt
  unfold enterableOf
  simp [hp]

/-- One walk marks no more than another whose region is at least as wide. -/
theorem reachable_mono (c : Cfg) (σ τ : AtomState)
    (hstart : ∀ p ∈ robotPos c τ, (reachable c σ).getD p false = true)
    (hen : ∀ v, v < c.adj.size → enterableOf c τ v = true → enterableOf c σ v = true) :
    ∀ p, (reachable c τ).getD p false = true → (reachable c σ).getD p false = true :=
  reachable_least c τ _ hstart
    (fun u v hu hv hev hlt => reachable_closed c σ u v hu hv (hen v hlt hev) hlt)

/-- A tile with nowhere left to paint it from. -/
def Blocked (c : Cfg) (σ : AtomState) (q : TileGoal) : Bool :=
  match q.forcedFrom with
  | some p => !(reachable c σ).getD p false
  | none => !q.paintFrom.any fun p => (reachable c σ).getD p false

theorem isDead_of_blocked (c : Cfg) (σ : AtomState) {q : TileGoal} (hq : q ∈ c.tiles)
    (hlive : σ q.goalAtom = false) (hb : Blocked c σ q = true) : isDead c σ = true := by
  unfold isDead
  exact Array.any_eq_true'.mpr ⟨q, Array.mem_filter.mpr ⟨hq, by simp [hlive]⟩, hb⟩

theorem blocked_of_isDead (c : Cfg) (σ : AtomState) (h : isDead c σ = true) :
    ∃ q ∈ c.tiles, σ q.goalAtom = false ∧ Blocked c σ q = true := by
  unfold isDead at h
  obtain ⟨q, hq, hval⟩ := Array.any_eq_true'.mp h
  exact ⟨q, (Array.mem_filter.mp hq).1, by simpa using (Array.mem_filter.mp hq).2, hval⟩

theorem blocked_mono (c : Cfg) (σ τ : AtomState) {q : TileGoal}
    (hsub : ∀ p, (reachable c τ).getD p false = true → (reachable c σ).getD p false = true)
    (h : Blocked c σ q = true) : Blocked c τ q = true := by
  unfold Blocked at h ⊢
  rcases hforced : q.forcedFrom with _ | pn
  · rw [hforced] at h
    simp only [Bool.not_eq_true'] at h ⊢
    rcases hany : q.paintFrom.any (fun p => (reachable c τ).getD p false) with _ | _
    · rfl
    · exfalso
      obtain ⟨pn, hpn, hval⟩ := Array.any_eq_true'.mp hany
      rw [Array.any_eq_true'.mpr ⟨pn, hpn, hsub pn hval⟩] at h
      exact Bool.noConfusion h
  · rw [hforced] at h
    simp only [Bool.not_eq_true'] at h ⊢
    rcases hval : (reachable c τ).getD pn false with _ | _
    · rfl
    · rw [hsub pn hval] at h; exact Bool.noConfusion h


end Planner.Lifted.Floortile

/- -------------------------------------------------------------------------- -/
/-
Every grounded floortile operator has one of the shapes.

The awkward one is `paint_down`.  A robot standing above a tile can paint it,
which takes away the square the tile above must be painted from; the value can
fall by two there.  The state it reaches has no plan, and the dead-end test sees
that at once, so the shape has a case for it and no bound is asked of it.
-/

namespace Planner.Lifted.Floortile

open Planner Planner.Pddl ExampleHeuristics.Floortile

/-! ### The task's own tables -/

abbrev tilesOf (t : Task) : Array Name := t.objectsOfTypes ["tile"]
abbrev coloursOf (t : Task) : Array Name := t.objectsOfTypes ["color"]
abbrev upsOf (t : Task) : Array GroundAtom := t.staticWith "up"
abbrev downsOf (t : Task) : Array GroundAtom := t.staticWith "down"
abbrev graphOf (t : Task) : Graph := moveGraph t (tilesOf t)
abbrev goalTiles (t : Task) : Array Name := goalTilesOf t
abbrev fuelOf (t : Task) : Nat := (tilesOf t).size

/-- The squares tile `y` can be painted from, as the table holds them. -/
def paintFromOf (t : Task) (y : Name) : Array Nat :=
  paintPositions (upsOf t) (downsOf t) (graphOf t) y

/-- The square a capped tile must be painted from. -/
def forcedFromOf (t : Task) (y : Name) : Option Nat :=
  forcedOf (upsOf t) (goalTiles t) (graphOf t) (fuelOf t) y

theorem cfg_adj (t : Task) : (cfgOf t).adj = (graphOf t).adj := rfl

/-- Reading a node index back gives the tile it stands for. -/
theorem graph_node {t : Task} {x : Name} {i : Nat} (h : (graphOf t).find? x = some i) :
    (graphOf t).nodes.getD i "" = x := Graph.find?_node h

theorem graph_lt {t : Task} {x : Name} {i : Nat} (h : (graphOf t).find? x = some i) :
    i < (graphOf t).size := Graph.find?_lt' h

theorem graph_isSome {t : Task} {x : Name} (h : x ∈ tilesOf t) :
    ((graphOf t).find? x).isSome := Graph.find?_isSome' h

theorem graph_edge {t : Task} {pred x y : Name} {i j : Nat}
    (hmem : ({ pred := pred, args := [x, y] } : GroundAtom) ∈ moveEdges t)
    (hx : (graphOf t).find? x = some i) (hy : (graphOf t).find? y = some j) :
    j ∈ (graphOf t).adj.getD i #[] := Graph.mem_adj_of_mem hmem hx hy
theorem cfg_dist (t : Task) : (cfgOf t).dist = Distances.of (graphOf t) := rfl

/-! ### What a floortile task must satisfy -/

/-- Every field is decidable on a parsed domain and problem. -/
structure Pinned (d : Domain) (p : Problem) : Prop where
  domain : FloortileDomain d
  /-- Parser validation supplies shared facts such as object-name uniqueness. -/
  validated : Validated d p
  upStatic : (staticPredicates d).contains "up" = true
  downStatic : (staticPredicates d).contains "down" = true
  leftStatic : (staticPredicates d).contains "left" = true
  rightStatic : (staticPredicates d).contains "right" = true
  goalNotUp : ∀ a ∈ p.goal, a.pred ≠ "up"
  goalNotDown : ∀ a ∈ p.goal, a.pred ≠ "down"
  goalNotLeft : ∀ a ∈ p.goal, a.pred ≠ "left"
  goalNotRight : ∀ a ∈ p.goal, a.pred ≠ "right"
  /-- The parsed goal names each atom once.  Compiled table uniqueness follows. -/
  goalNodup : p.goal.Nodup
  initCheck : initInvCheck p = true
  /-- `up` names two tiles, and names them once each way round. -/
  upPair : ∀ rel : Bool, ∀ a ∈ upsOf (ground d p rel),
    a.args = [a.args.getD 0 "", a.args.getD 1 ""]
  upOneBelow : ∀ rel : Bool, ∀ a ∈ upsOf (ground d p rel), ∀ b ∈ upsOf (ground d p rel),
    a.args.getD 0 "" = b.args.getD 0 "" → a.args.getD 1 "" = b.args.getD 1 ""
  upOneAbove : ∀ rel : Bool, ∀ a ∈ upsOf (ground d p rel), ∀ b ∈ upsOf (ground d p rel),
    a.args.getD 1 "" = b.args.getD 1 "" → a.args.getD 0 "" = b.args.getD 0 ""
  /-- `down(y, x)` says the same as `up(x, y)`. -/
  downUp : ∀ rel : Bool, ∀ a ∈ downsOf (ground d p rel),
    ({ pred := "up", args := [a.args.getD 1 "", a.args.getD 0 ""] } : GroundAtom)
      ∈ upsOf (ground d p rel)
  downPair : ∀ rel : Bool, ∀ a ∈ downsOf (ground d p rel),
    a.args = [a.args.getD 0 "", a.args.getD 1 ""]
  /-- Every colour a goal names is one of the task's colours. -/
  goalColours : ∀ rel : Bool, ∀ a ∈ (ground d p rel).goalAtomsWith "painted",
    (coloursOf (ground d p rel)).contains (a.args.getD 1 "") = true
  /-- The tile, robot and colour types have no subtypes. -/
  tileType : ∀ ob ∈ allObjects d p, d.isSubtype ob.type "tile" = true → ob.type = "tile"
  robotType : ∀ ob ∈ allObjects d p, d.isSubtype ob.type "robot" = true → ob.type = "robot"
  colorType : ∀ ob ∈ allObjects d p, d.isSubtype ob.type "color" = true → ob.type = "color"
  /-- No tile has two goal colours. -/
  tileNameInj : ∀ rel : Bool, ∀ q1 ∈ (cfgOf (ground d p rel)).tiles,
    ∀ q2 ∈ (cfgOf (ground d p rel)).tiles,
      q1.goalAtom.args.getD 0 "" = q2.goalAtom.args.getD 0 "" → q1 = q2
  /-- Each tile of the grid has a `clear` fact of its own. -/
  clearNames : ∀ rel : Bool, ∀ i : Nat, ∀ a : GroundAtom,
    (cfgOf (ground d p rel)).clearAtoms.getD i none = some a →
      a = clearT ((graphOf (ground d p rel)).nodes.getD i "")
  /-- The numeric value fits under the dead-end constant. -/
  small : ∀ rel : Bool,
    2 * (cfgOf (ground d p rel)).tiles.size
      + max (cfgOf (ground d p rel)).dist.bound (cfgOf (ground d p rel)).tiles.size
      ≤ deadEnd

variable {d : Domain} {p : Problem} {o : AtomOp}

/-! ### Reading a node index back -/

theorem graph_adj_size (t : Task) : (graphOf t).adj.size = (graphOf t).size :=
  Graph.adj_size _ _

theorem robot_square_seen (t : Task) {σ : AtomState} {p : Nat}
    (hp : p ∈ robotPos (cfgOf t) σ) (hlt : p < (graphOf t).size) :
    (reachable (cfgOf t) σ).getD p false = true :=
  reachable_start _ _ hp (by rw [cfg_adj, graph_adj_size]; exact hlt)

theorem node_inj (hp : Pinned d p) (rel : Bool) {u v : Nat}
    (hu : u < (graphOf (ground d p rel)).size) (hv : v < (graphOf (ground d p rel)).size)
    (h : (graphOf (ground d p rel)).nodes.getD u ""
      = (graphOf (ground d p rel)).nodes.getD v "") : u = v := by
  have hnd : (graphOf (ground d p rel)).nodes.toList.Nodup := by
    exact objsOf_nodup hp.validated.namesNodup
  have hu' : u < (graphOf (ground d p rel)).nodes.size := hu
  have hv' : v < (graphOf (ground d p rel)).nodes.size := hv
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hu',
    Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hv'] at h
  have hEq : (graphOf (ground d p rel)).nodes.toList[u]'(by simpa using hu')
      = (graphOf (ground d p rel)).nodes.toList[v]'(by simpa using hv') := by
    simpa using h
  exact (List.Nodup.getElem_inj_iff hnd).mp hEq

/-- The `clear` fact of a tile is the one the table holds at that tile's index. -/
theorem clearAtom_of_fact (t : Task) {z : Name} {n f : Nat}
    (hlt : f < t.factNames.size) (hname : atomOf t f = clearT z)
    (hn : (graphOf t).find? z = some n) :
    (cfgOf t).clearAtoms.getD n none = some (clearT z) := by
  have hnlt : n < (tilesOf t).size := graph_lt hn
  have hz : (tilesOf t).getD n "" = z := graph_node hn
  show ((compile t).clearFacts.map (Option.map (atomOf t))).getD n none = _
  rw [getD_map_lt (compile t).clearFacts (Option.map (atomOf t)) none none
    (show n < (compile t).clearFacts.size from by
      show n < ((tilesOf t).map (clearFactOf (t.factsWith "clear"))).size
      simpa using hnlt)]
  rw [show (compile t).clearFacts = (tilesOf t).map (clearFactOf (t.factsWith "clear")) from rfl,
    getD_map_lt (tilesOf t) (clearFactOf (t.factsWith "clear")) "" none hnlt, hz]
  rcases hfind : (t.factsWith "clear").find? (fun w => w.2.args == [z]) with _ | w
  · exfalso
    have hmem : (f, clearT z) ∈ t.factsWith "clear" :=
      mem_factsWith_of_named hlt hname rfl
    have := Array.find?_eq_none.mp hfind (f, clearT z) hmem
    simp [clearT] at this
  · have hwmem : w ∈ t.factsWith "clear" := Array.mem_of_find?_eq_some hfind
    obtain ⟨-, hwname, hwpred⟩ := mem_factsWith hwmem
    have hwargs : w.2.args = [z] := by
      have := (Array.find?_eq_some_iff_getElem.mp hfind).1
      simpa using this
    show (Option.map (atomOf t) ((clearFactOf (t.factsWith "clear") z))) = some (clearT z)
    unfold clearFactOf
    rw [hfind]
    simp only [Option.map_some, Option.some.injEq]
    show t.factNames.getD w.1 default = clearT z
    rw [hwname]
    show w.2 = { pred := "clear", args := [z] }
    rw [← hwargs, ← hwpred]


/-! ### Reading `up` -/

theorem up_mem (hp : Pinned d p) (rel : Bool) {y x : Name}
    (hmem : upA y x ∈ p.init)
    (hnot : upA y x ∉ allAtoms (groundedOps d p rel) p.goal.toArray) :
    upA y x ∈ upsOf (ground d p rel) :=
  mem_staticWith d p rel hmem hnot rfl

theorem argPair_eq {a : GroundAtom} {x y : Name} (h : a.args = [x, y]) :
    argPair a = some (x, y) := by simp [argPair, h]

/-- `belowOf` finds the tile under `y` as soon as any atom names one. -/
theorem belowOf_eq (hp : Pinned d p) (rel : Bool) {y x : Name}
    (hmem : upA y x ∈ upsOf (ground d p rel)) :
    belowOf (upsOf (ground d p rel)) y = some x := by
  set ups := upsOf (ground d p rel) with hups
  rcases hfind : ups.find? (fun a => (argPair a).any fun q => q.1 == y) with _ | a
  · exfalso
    have hpx : argPair (upA y x) = some (y, x) := argPair_eq rfl
    have := Array.find?_eq_none.mp hfind (upA y x) hmem
    rw [hpx] at this
    simp at this
  · have hamem : a ∈ ups := Array.mem_of_find?_eq_some hfind
    have hcond : ((argPair a).any fun q => q.1 == y) = true :=
      (Array.find?_eq_some_iff_getElem.mp hfind).1
    have hpair := argPair_eq (a := a) (hp.upPair rel a hamem)
    rw [hpair] at hcond
    have h0 : a.args.getD 0 "" = y := by simpa using hcond
    have hx0 : (upA y x).args.getD 0 "" = y := by simp [upA]
    have h1 : a.args.getD 1 "" = x :=
      by simpa [upA] using hp.upOneBelow rel a hamem (upA y x) hmem (by rw [h0, hx0])
    show ((ups.find? fun a => (argPair a).any fun q => q.1 == y).bind fun a =>
      (argPair a).map (·.2)) = some x
    rw [hfind]
    show (argPair a).map (·.2) = some x
    rw [hpair, Option.map_some, h1]

/-- And `aboveOf` finds the tile over `y`. -/
theorem aboveOf_eq (hp : Pinned d p) (rel : Bool) {y z : Name}
    (hmem : upA z y ∈ upsOf (ground d p rel)) :
    aboveOf (upsOf (ground d p rel)) y = some z := by
  set ups := upsOf (ground d p rel) with hups
  rcases hfind : ups.find? (fun a => (argPair a).any fun q => q.2 == y) with _ | a
  · exfalso
    have hpz : argPair (upA z y) = some (z, y) := argPair_eq rfl
    have := Array.find?_eq_none.mp hfind (upA z y) hmem
    rw [hpz] at this
    simp at this
  · have hamem : a ∈ ups := Array.mem_of_find?_eq_some hfind
    have hcond : ((argPair a).any fun q => q.2 == y) = true :=
      (Array.find?_eq_some_iff_getElem.mp hfind).1
    have hpair := argPair_eq (a := a) (hp.upPair rel a hamem)
    rw [hpair] at hcond
    have h1 : a.args.getD 1 "" = y := by simpa using hcond
    have hz1 : (upA z y).args.getD 1 "" = y := by simp [upA]
    have h0 : a.args.getD 0 "" = z :=
      by simpa [upA] using hp.upOneAbove rel a hamem (upA z y) hmem (by rw [h1, hz1])
    show ((ups.find? fun a => (argPair a).any fun q => q.2 == y).bind fun a =>
      (argPair a).map (·.1)) = some z
    rw [hfind]
    show (argPair a).map (·.1) = some z
    rw [hpair, Option.map_some, h0]

/-! ### More fuel never turns a cap into a refusal -/

theorem capped_mono (ups : Array GroundAtom) (goals : Array Name) :
    ∀ (fuel : Nat) (y : Name), cappedByGoals ups goals fuel y = true →
      cappedByGoals ups goals (fuel + 1) y = true := by
  intro fuel
  induction fuel with
  | zero => intro y h; simp [cappedByGoals] at h
  | succ n ih =>
      intro y h
      rw [cappedByGoals] at h ⊢
      rcases hab : aboveOf ups y with _ | z
      · exact rfl
      · rw [hab] at h
        simp only [Bool.and_eq_true] at h ⊢
        exact ⟨h.1, ih z h.2⟩

theorem capped_mono' (ups : Array GroundAtom) (goals : Array Name) :
    ∀ (k fuel : Nat) (y : Name), cappedByGoals ups goals fuel y = true →
      cappedByGoals ups goals (fuel + k) y = true := by
  intro k
  induction k with
  | zero => intro fuel y h; exact h
  | succ n ih =>
      intro fuel y h
      exact capped_mono ups goals (fuel + n) y (ih fuel y h)

/-- A capped tile leaves the tile above it capped too. -/
theorem capped_step (ups : Array GroundAtom) (goals : Array Name) {fuel : Nat} {y z : Name}
    (h : cappedByGoals ups goals fuel y = true) (hab : aboveOf ups y = some z) :
    goals.contains z = true ∧ cappedByGoals ups goals fuel z = true := by
  cases fuel with
  | zero => simp [cappedByGoals] at h
  | succ n =>
      rw [cappedByGoals, hab] at h
      simp only [Bool.and_eq_true] at h
      exact ⟨h.1, capped_mono ups goals n z h.2⟩

/-! ### What the tile table holds -/

/-- One entry of the tile table, read as atoms. -/
structure TileShape (t : Task) (q : TileGoal) (y c : Name) : Prop where
  atom : q.goalAtom = painted y c
  paint : q.paintFrom = paintFromOf t y
  forced : q.forcedFrom = forcedFromOf t y
  colour : (coloursOf t).getD q.colour "" = c
  size : q.colour < (coloursOf t).size

private theorem tileEntry_shape {t : Task} {a : GroundAtom} {i : Nat} {x : CTile}
    (h : tileEntry t (coloursOf t) (paintFromOf t) (forcedFromOf t) (a, i) = some x) :
    ∃ y c, a = { pred := "painted", args := [y, c] } ∧ x.goalFact = t.goal.getD i 0 ∧
      x.paintFrom = paintFromOf t y ∧ x.forcedFrom = forcedFromOf t y ∧
      (coloursOf t).getD x.colour "" = c ∧ x.colour < (coloursOf t).size := by
  unfold tileEntry at h
  by_cases hpred : (a.pred == "painted") = true
  · rcases hargs : a.args with _ | ⟨y, rest⟩
    · rw [hargs] at h; simp only [hpred] at h; simp at h
    · cases rest with
      | nil => rw [hargs] at h; simp only [hpred] at h; simp at h
      | cons c rest' =>
          cases rest' with
          | cons _ _ => rw [hargs] at h; simp only [hpred] at h; simp at h
          | nil =>
              rw [hargs] at h
              simp only [hpred] at h
              rcases hci : (coloursOf t).findIdx? (· == c) with _ | ci
              · rw [hci] at h; simp at h
              · rw [hci] at h
                simp only [Option.map_some, Option.some.injEq] at h
                obtain ⟨hlt, hval, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hci
                refine ⟨y, c, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · have hp2 : a.pred = "painted" := by simpa using hpred
                  rw [← hp2, ← hargs]
                · rw [← h]
                · rw [← h]
                · rw [← h]
                · rw [← h]
                  show (coloursOf t).getD ci "" = c
                  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]
                  simpa using hval
                · rw [← h]; exact hlt
  · simp only [Bool.not_eq_true] at hpred
    simp [hpred] at h

/-- **Every tile the table holds is a `painted` goal, with its own squares.** -/
theorem tiles_shape (d : Domain) (p : Problem) (rel : Bool) {q : TileGoal}
    (hq : q ∈ (cfgOf (ground d p rel)).tiles) :
    ∃ y c, TileShape (ground d p rel) q y c := by
  obtain ⟨x, hx, hxq⟩ := Array.mem_map.mp hq
  subst hxq
  obtain ⟨z, hz, hzval⟩ := Array.mem_filterMap.mp hx
  obtain ⟨-, hlt, hget⟩ := Array.mem_zipIdx hz
  obtain ⟨y, c, hatom, hfact, hpaint, hforced, hcol, hsz⟩ := tileEntry_shape hzval
  refine ⟨y, c, ?_, hpaint, hforced, hcol, hsz⟩
  show atomOf (ground d p rel) x.goalFact = painted y c
  rw [hfact]
  obtain ⟨hname, -⟩ := goal_name_eq d p rel (i := z.2) (by simpa using hlt)
  show (ground d p rel).factNames.getD ((ground d p rel).goal.getD z.2 0) default = painted y c
  rw [hname]
  have hz1 : (ground d p rel).goalAtoms[z.2]'(by simpa using hlt) = z.1 := by
    simpa using hget.symm
  rw [hz1, hatom]
  rfl


/-- **Every `painted` goal has a tile in the table.** -/
theorem tiles_cover (d : Domain) (p : Problem) (rel : Bool) {y c : Name}
    (hmem : painted y c ∈ (ground d p rel).goalAtoms)
    (hc : (coloursOf (ground d p rel)).contains c = true) :
    ∃ q ∈ (cfgOf (ground d p rel)).tiles, TileShape (ground d p rel) q y c := by
  obtain ⟨i, hi, hval⟩ := Array.getElem_of_mem hmem
  have hzip : (painted y c, i) ∈ (ground d p rel).goalAtoms.zipIdx := by
    rw [Array.mk_mem_zipIdx_iff_getElem?]
    rw [Array.getElem?_eq_getElem hi, hval]
  rcases hf : (coloursOf (ground d p rel)).findIdx? (· == c) with _ | ci
  · exfalso
    obtain ⟨z, hz, hzc⟩ := Array.contains_iff_exists_mem_beq.mp hc
    have hzc' : (z == c) = true := by
      have : c = z := by simpa using hzc
      simp [this]
    have := Array.findIdx?_eq_some_of_exists (xs := coloursOf (ground d p rel))
      (p := (· == c)) ⟨z, hz, hzc'⟩
    rw [hf] at this
    simp at this
  · refine ⟨tileOf (ground d p rel)
      { goalFact := (ground d p rel).goal.getD i 0, colour := ci,
        paintFrom := paintFromOf (ground d p rel) y,
        forcedFrom := forcedFromOf (ground d p rel) y }, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine Array.mem_map.mpr ⟨_, Array.mem_filterMap.mpr ⟨(painted y c, i), hzip, ?_⟩, rfl⟩
      show tileEntry (ground d p rel) (coloursOf (ground d p rel)) _ _ (painted y c, i) = _
      dsimp only [tileEntry, painted]
      rw [show (("painted" : Name) == "painted") = true from rfl]
      dsimp only
      rw [hf]
      rfl
    · show atomOf (ground d p rel) ((ground d p rel).goal.getD i 0) = painted y c
      obtain ⟨hname, -⟩ := goal_name_eq d p rel (i := i) hi
      show (ground d p rel).factNames.getD ((ground d p rel).goal.getD i 0) default
        = painted y c
      rw [hname, hval]
    · rfl
    · rfl
    · show (coloursOf (ground d p rel)).getD ci "" = c
      obtain ⟨hlt, hval2, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hf
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]
      simpa using hval2
    · exact (Array.findIdx?_eq_some_iff_getElem.mp hf).1


/-! ### Where the robots stand -/

theorem mem_robotPos {t : Task} {σ : AtomState} {n : Nat}
    (h : n ∈ robotPos (cfgOf t) σ) :
    ∃ r x f, r ∈ robots t ∧ f < t.factNames.size ∧ atomOf t f = robotAt r x ∧
      σ (robotAt r x) = true ∧ (graphOf t).find? x = some n := by
  obtain ⟨xs, hxs, hval⟩ := Array.mem_filterMap.mp h
  rcases hfind : xs.find? (fun z => σ z.1) with _ | y
  · rw [hfind] at hval; simp at hval
  · rw [hfind] at hval
    simp only [Option.map_some, Option.some.injEq] at hval
    have hy : y ∈ xs := Array.mem_of_find?_eq_some hfind
    have hσ : σ y.1 = true := (Array.find?_eq_some_iff_getElem.mp hfind).1
    have hxs' : xs ∈ ((compile t).robotAt).map
        (fun zs => zs.map fun u => (atomOf t u.1, u.2)) := hxs
    obtain ⟨zs, hzs, hzval⟩ := Array.mem_map.mp hxs'
    rw [← hzval] at hy
    obtain ⟨u, hu, huval⟩ := Array.mem_map.mp hy
    have hzs' : zs ∈ (robots t).map (robotAtOf (t.factsWith "robot-at") (graphOf t)) := hzs
    obtain ⟨r, hr, hrval⟩ := Array.mem_map.mp hzs'
    rw [← hrval] at hu
    obtain ⟨x, hatom, hnode⟩ := mem_robotAtOf t (graphOf t) r hu
    refine ⟨r, x, u.1, hr, robotAtOf_range t (graphOf t) r u hu, hatom, ?_, ?_⟩
    · rw [← hatom, show atomOf t u.1 = y.1 from by rw [← huval]]; exact hσ
    · rw [hnode, show u.2 = y.2 from by rw [← huval], hval]

theorem node_mem_robotPos {t : Task} {σ : AtomState} {r x : Name} {f n : Nat}
    (hr : r ∈ robots t) (hlt : f < t.factNames.size) (hname : atomOf t f = robotAt r x)
    (hx : (graphOf t).find? x = some n) (hσ : σ (robotAt r x) = true)
    (hone : ∀ r' u v, σ (robotAt r' u) = true → σ (robotAt r' v) = true → u = v) :
    n ∈ robotPos (cfgOf t) σ := by
  set zs := robotAtOf (t.factsWith "robot-at") (graphOf t) r with hzs
  set xs := zs.map (fun u => (atomOf t u.1, u.2)) with hxs
  have hmemRow : xs ∈ (cfgOf t).robotAt :=
    Array.mem_map.mpr ⟨zs, Array.mem_map.mpr ⟨r, hr, rfl⟩, rfl⟩
  have hfn : (f, n) ∈ zs := mem_robotAtOf_total t (graphOf t) r x hlt hname hx
  have hwit : (robotAt r x, n) ∈ xs := by
    refine Array.mem_map.mpr ⟨(f, n), hfn, ?_⟩
    rw [hname]
  rcases hfind : xs.find? (fun z => σ z.1) with _ | y
  · exfalso
    have := Array.find?_eq_none.mp hfind (robotAt r x, n) hwit
    simp only [] at this
    rw [hσ] at this
    simp at this
  · have hy : y ∈ xs := Array.mem_of_find?_eq_some hfind
    have hσy : σ y.1 = true := (Array.find?_eq_some_iff_getElem.mp hfind).1
    obtain ⟨u, hu, huval⟩ := Array.mem_map.mp hy
    obtain ⟨x', hatom, hnode⟩ := mem_robotAtOf t (graphOf t) r hu
    have hσ' : σ (robotAt r x') = true := by
      rw [← hatom, show atomOf t u.1 = y.1 from by rw [← huval]]; exact hσy
    have hxx : x' = x := hone r x' x hσ' hσ
    have hyn : y.2 = n := by
      have : (graphOf t).find? x = some u.2 := by rw [← hxx]; exact hnode
      rw [hx] at this
      rw [show y.2 = u.2 from by rw [← huval]]
      simpa using this.symm
    refine Array.mem_filterMap.mpr ⟨xs, hmemRow, ?_⟩
    rw [hfind]
    simp [hyn]

/-! ### The colour a tile needs -/

theorem hasColour_size (t : Task) : (cfgOf t).hasColour.size = (coloursOf t).size := by
  show ((compile t).hasColour.map (fun xs => xs.map (atomOf t))).size = _
  rw [Array.size_map, show (compile t).hasColour
    = (coloursOf t).map (hasColourOf (t.factsWith "robot-has")) from rfl, Array.size_map]

theorem colour_row (t : Task) {ci : Nat} (hci : ci < (coloursOf t).size) :
    (cfgOf t).hasColour.getD ci #[]
      = (hasColourOf (t.factsWith "robot-has") ((coloursOf t).getD ci "")).map (atomOf t) := by
  show ((compile t).hasColour.map fun xs => xs.map (atomOf t)).getD ci #[] = _
  rw [getD_map_lt (compile t).hasColour (fun xs => xs.map (atomOf t)) #[] #[]
    (show ci < (compile t).hasColour.size from by
      show ci < ((coloursOf t).map (hasColourOf (t.factsWith "robot-has"))).size
      simpa using hci)]
  congr 1
  exact getD_map_lt (coloursOf t) (hasColourOf (t.factsWith "robot-has")) "" #[] hci

theorem colour_held {t : Task} {σ : AtomState} {r c : Name} {ci f : Nat}
    (hci : ci < (coloursOf t).size)
    (hname : (coloursOf t).getD ci "" = c) (hlt : f < t.factNames.size)
    (hfn : atomOf t f = robotHas r c) (hσ : σ (robotHas r c) = true) :
    ((cfgOf t).hasColour.getD ci #[]).any σ = true := by
  rw [colour_row t hci, hname]
  refine Array.any_eq_true'.mpr ⟨robotHas r c, ?_, hσ⟩
  exact Array.mem_map.mpr ⟨f, mem_hasColourOf_total t r c hlt hfn, hfn⟩


/-! ### Objects of the three types -/

theorem mem_tiles (hp : Pinned d p) (rel : Bool) {x : Name}
    (hw : WellTyped d (allObjects d p) "tile" x) : x ∈ tilesOf (ground d p rel) :=
  mem_objsOf_of_wellTyped hp.tileType hw

theorem mem_robots (hp : Pinned d p) (rel : Bool) {r : Name}
    (hw : WellTyped d (allObjects d p) "robot" r) : r ∈ robots (ground d p rel) :=
  mem_objsOf_of_wellTyped hp.robotType hw

theorem mem_colours (hp : Pinned d p) (rel : Bool) {c : Name}
    (hw : WellTyped d (allObjects d p) "color" c) : c ∈ coloursOf (ground d p rel) :=
  mem_objsOf_of_wellTyped hp.colorType hw

/-- A tile of the task is a node of the move graph. -/
theorem node_of_tile (hp : Pinned d p) (rel : Bool) {x : Name}
    (hw : WellTyped d (allObjects d p) "tile" x) :
    ∃ n, (graphOf (ground d p rel)).find? x = some n := by
  have := Graph.find?_isSome' (nodes := tilesOf (ground d p rel))
    (edges := moveEdges (ground d p rel)) (mem_tiles hp rel hw)
  exact Option.isSome_iff_exists.mp this

/-! ### The map atom a schema reads is a static atom of the task -/

theorem static_of_pre (hp : Pinned d p) (rel : Bool) (hf : OpFacts d p o)
    {a : GroundAtom} (hmem : a ∈ hf.inst.pre)
    (hstatic : (staticPredicates d).contains a.pred = true)
    (hgoal : ∀ b ∈ p.goal, b.pred ≠ a.pred) :
    a ∈ (ground d p rel).staticWith a.pred := by
  have hmem' : a ∈ hf.inst.schema.pre.map (instAtom hf.inst.schema.params hf.inst.args) := hmem
  obtain ⟨y, hy, hval⟩ := List.mem_map.mp hmem'
  have hinit : a ∈ p.init := by
    have hpred : y.pred = a.pred := by rw [← hval]; rfl
    have := hf.staticHeld y hy (by rw [hpred]; exact hstatic)
    rw [hval] at this
    simpa using this
  have hnot : a ∉ allAtoms (groundedOps d p rel) p.goal.toArray := by
    intro hc
    exact hgoal _ (mem_goal_of_static d p rel hc hstatic) rfl
  exact mem_staticWith d p rel hinit hnot rfl

/-- The map atom a paint schema reads is one of the two static tables. -/
theorem paint_dir_static (hp : Pinned d p) (rel : Bool) (hf : OpFacts d p o)
    {nm pr r y x c : Name} (hs : hf.inst.schema = paintA nm pr)
    (ha : hf.inst.args = [r, y, x, c])
    (hdir : nm = "paint_up" ∧ pr = "up" ∨ nm = "paint_down" ∧ pr = "down")
    (hpreD : { pred := pr, args := [y, x] } ∈ hf.inst.pre) :
    upA y x ∈ upsOf (ground d p rel) ∨ downA y x ∈ downsOf (ground d p rel) := by
  rcases hdir with ⟨-, hu⟩ | ⟨-, hu⟩
  · refine Or.inl ?_
    have := static_of_pre hp rel hf (a := { pred := pr, args := [y, x] }) hpreD
      (by rw [show ({ pred := pr, args := [y, x] } : GroundAtom).pred = pr from rfl, hu]
          exact hp.upStatic)
      (by
        rw [show ({ pred := pr, args := [y, x] } : GroundAtom).pred = pr from rfl, hu]
        exact fun b hb => hp.goalNotUp b hb)
    rw [show ({ pred := pr, args := [y, x] } : GroundAtom).pred = pr from rfl, hu] at this
    exact this
  · refine Or.inr ?_
    have := static_of_pre hp rel hf (a := { pred := pr, args := [y, x] }) hpreD
      (by rw [show ({ pred := pr, args := [y, x] } : GroundAtom).pred = pr from rfl, hu]
          exact hp.downStatic)
      (by
        rw [show ({ pred := pr, args := [y, x] } : GroundAtom).pred = pr from rfl, hu]
        exact fun b hb => hp.goalNotDown b hb)
    rw [show ({ pred := pr, args := [y, x] } : GroundAtom).pred = pr from rfl, hu] at this
    exact this

/-! ### Frames of the three tables -/

theorem tiles_frame (d : Domain) (p : Problem) (rel : Bool) {σ τ : AtomState}
    (h : ∀ y c, τ (painted y c) = σ (painted y c)) :
    ∀ q ∈ (cfgOf (ground d p rel)).tiles, τ q.goalAtom = σ q.goalAtom := by
  intro q hq
  obtain ⟨y, c, hshape⟩ := tiles_shape d p rel hq
  rw [hshape.atom]
  exact h y c

theorem robots_frame {t : Task} {σ τ : AtomState}
    (h : ∀ r x, τ (robotAt r x) = σ (robotAt r x)) :
    robotPos (cfgOf t) τ = robotPos (cfgOf t) σ := by
  refine robotPos_congr ?_
  intro xs hxs y hy
  obtain ⟨r, -, hall⟩ := robotAt_data t hxs
  obtain ⟨x, hx⟩ := hall y hy
  rw [hx]; exact h r x

theorem colours_frame {t : Task} {σ τ : AtomState}
    (h : ∀ r c, τ (robotHas r c) = σ (robotHas r c)) (col : Nat) :
    (((cfgOf t).hasColour.getD col #[]).any τ)
      = (((cfgOf t).hasColour.getD col #[]).any σ) := by
  refine hasColour_congr col ?_
  intro xs hxs a ha
  obtain ⟨c, -, hall⟩ := hasColour_data t hxs
  obtain ⟨r, hr⟩ := hall a ha
  rw [hr]; exact h r c


/-! ### `change_color` -/

theorem colour_step (hp : Pinned d p) (rel : Bool) (ho : o ∈ groundedOps d p rel)
    (hf : OpFacts d p o) {r c c2 : Name} (hs : hf.inst.schema = changeA)
    (ha : hf.inst.args = [r, c, c2]) {σ : AtomState} (happ : o.applicableA σ) :
    SchemaStep (graphOf (ground d p rel)) (cfgOf (ground d p rel)) σ (o.applyA σ) := by
  obtain ⟨hpre, hadd, hdel⟩ := change_atoms hf.inst hs ha
  have hfrPa : ∀ y c', o.applyA σ (painted y c') = σ (painted y c') := fun y c' =>
    frame_of_lists hf hadd hdel (by simp) (by simp) σ
  have hfrAt : ∀ r' x, o.applyA σ (robotAt r' x) = σ (robotAt r' x) := fun r' x =>
    frame_of_lists hf hadd hdel (by simp) (by simp) σ
  refine .colour (((coloursOf (ground d p rel)).findIdx? (· == c2)).getD 0)
    ⟨tiles_frame d p rel hfrPa, robots_frame hfrAt, ?_⟩
  intro ci hfalse
  by_cases hτ : ((cfgOf (ground d p rel)).hasColour.getD ci #[]).any (o.applyA σ) = true
  · refine Or.inr ?_
    obtain ⟨a, hmem, hval⟩ := Array.any_eq_true'.mp hτ
    have hσa : σ a = false := by
      by_contra hc
      have : ((cfgOf (ground d p rel)).hasColour.getD ci #[]).any σ = true :=
        Array.any_eq_true'.mpr ⟨a, hmem, by simpa using hc⟩
      rw [this] at hfalse
      exact Bool.noConfusion hfalse
    have hadded : a = robotHas r c2 := by
      by_contra hc
      have := falls_of_lists hf hadd (by simp [hc]) hval
      rw [hσa] at this
      exact Bool.noConfusion this
    have hci : ci < (coloursOf (ground d p rel)).size := by
      by_contra hc
      rw [show (cfgOf (ground d p rel)).hasColour.getD ci #[] = #[] from by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none
          (by
            rw [hasColour_size]
            exact Nat.le_of_not_lt hc)]
        rfl] at hmem
      simp at hmem
    have hrow := colour_row (ground d p rel) hci
    rw [hrow] at hmem
    obtain ⟨fa, hfa, hfaval⟩ := Array.mem_map.mp hmem
    obtain ⟨r', hr'⟩ := mem_hasColourOf (ground d p rel)
      ((coloursOf (ground d p rel)).getD ci "") hfa
    have hname : (coloursOf (ground d p rel)).getD ci "" = c2 := by
      have : a = robotHas r' ((coloursOf (ground d p rel)).getD ci "") := by
        rw [← hfaval]; exact hr'
      rw [hadded] at this
      simpa using (by simpa [robotHas] using this.symm : _ ∧ _).2
    have hfind : (coloursOf (ground d p rel)).findIdx? (· == c2) = some ci := by
      refine Array.findIdx?_eq_some_iff_getElem.mpr ⟨hci, ?_, ?_⟩
      · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hci] at hname
        simpa using hname
      · intro j hj hc
        exfalso
        have hjlt : j < (coloursOf (ground d p rel)).size := Nat.lt_trans hj hci
        have hcj : (coloursOf (ground d p rel))[j] = c2 := by simpa using hc
        have hcolours : (coloursOf (ground d p rel)).toList.Nodup := by
          exact objsOf_nodup hp.validated.namesNodup
        have hci2 : (coloursOf (ground d p rel))[ci] = c2 := by
          rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hci] at hname
          simpa using hname
        have hEq : (coloursOf (ground d p rel)).toList[j]'(by simpa using hjlt)
            = (coloursOf (ground d p rel)).toList[ci]'(by simpa using hci) := by
          simp only [Array.getElem_toList]
          rw [hcj, hci2]
        have := (List.Nodup.getElem_inj_iff hcolours).mp hEq
        omega
    rw [hfind]
    rfl
  · exact Or.inl (by simpa using hτ)


/-! ### The squares a tile can be painted from -/

theorem staticWith_pred (t : Task) (pred : Name) {a : GroundAtom}
    (h : a ∈ t.staticWith pred) : a.pred = pred := by
  have := (Array.mem_filter.mp h).2
  simpa using this

theorem mem_paintPositions {t : Task} {y : Name} {n : Nat}
    (h : n ∈ paintFromOf t y) :
    ∃ x, (upA y x ∈ upsOf t ∨ downA y x ∈ downsOf t) ∧
      (graphOf t).find? x = some n := by
  obtain ⟨a, ha, hval⟩ := Array.mem_filterMap.mp h
  revert hval
  rcases hargs : a.args with _ | ⟨t', rest⟩
  · simp
  · cases rest with
    | nil => simp
    | cons x rest' =>
        cases rest' with
        | cons _ _ => simp
        | nil =>
            simp only []
            by_cases hty : (t' == y) = true
            · simp only [hty, if_true]
              intro hfind
              have hty' : t' = y := by simpa using hty
              refine ⟨x, ?_, hfind⟩
              rcases Array.mem_append.mp ha with hu | hd
              · refine Or.inl ?_
                have hpred : a.pred = "up" := staticWith_pred t "up" hu
                have : a = upA y x := by
                  show a = { pred := "up", args := [y, x] }
                  rw [← hpred, ← hty', ← hargs]
                rw [← this]; exact hu
              · refine Or.inr ?_
                have hpred : a.pred = "down" := staticWith_pred t "down" hd
                have : a = downA y x := by
                  show a = { pred := "down", args := [y, x] }
                  rw [← hpred, ← hty', ← hargs]
                rw [← this]; exact hd
            · simp only [Bool.not_eq_true] at hty
              simp [hty]

theorem mem_paintPositions_of {t : Task} {y x : Name} {n : Nat}
    (ha : upA y x ∈ upsOf t ∨ downA y x ∈ downsOf t)
    (hn : (graphOf t).find? x = some n) : n ∈ paintFromOf t y := by
  rcases ha with hu | hd
  · refine Array.mem_filterMap.mpr ⟨upA y x, Array.mem_append.mpr (Or.inl hu), ?_⟩
    show (match (upA y x).args with
      | [t', x'] => if t' == y then (graphOf t).find? x' else none
      | _ => none) = some n
    simpa [upA] using hn
  · refine Array.mem_filterMap.mpr ⟨downA y x, Array.mem_append.mpr (Or.inr hd), ?_⟩
    show (match (downA y x).args with
      | [t', x'] => if t' == y then (graphOf t).find? x' else none
      | _ => none) = some n
    simpa [downA] using hn

theorem mem_tile_paintFrom {t : Task} {q : TileGoal} {y c x : Name} {n : Nat}
    (hshape : TileShape t q y c)
    (ha : upA y x ∈ upsOf t ∨ downA y x ∈ downsOf t)
    (hn : (graphOf t).find? x = some n) : n ∈ q.paintFrom :=
  Eq.subst (motive := fun a => n ∈ a) hshape.paint.symm (mem_paintPositions_of ha hn)

/-! ### A square serves at most two tiles -/

/-- The tile a goal atom names. -/
abbrev tileName (q : TileGoal) : Name := q.goalAtom.args.getD 0 ""

theorem tileName_eq {t : Task} {q : TileGoal} {y c : Name} (h : TileShape t q y c) :
    tileName q = y := by
  show q.goalAtom.args.getD 0 "" = y
  rw [h.atom]; rfl

theorem two_tiles (hp : Pinned d p) (rel : Bool) {nd : Nat}
    (hnd : (cfgOf (ground d p rel)).tiles.toList.Nodup) :
    ((cfgOf (ground d p rel)).tiles.toList.filter
      (fun q => q.paintFrom.contains nd)).length ≤ 2 := by
  set t := ground d p rel
  set A := (graphOf t).nodes.getD nd "" with hA
  set l := (cfgOf t).tiles.toList.filter (fun q => q.paintFrom.contains nd) with hl
  set opts := (aboveOf (upsOf t) A).toList ++ (belowOf (upsOf t) A).toList with hopts
  have hlsub : ∀ q ∈ l, q ∈ (cfgOf t).tiles := by
    intro q hq
    have := (List.mem_filter.mp hq).1
    simpa using this
  have hnames : ∀ q ∈ l, tileName q ∈ opts := by
    intro q hq
    have hmem := hlsub q hq
    have hcon : q.paintFrom.contains nd = true := (List.mem_filter.mp hq).2
    obtain ⟨y, c, hshape⟩ := tiles_shape d p rel hmem
    rw [hshape.paint] at hcon
    obtain ⟨x, hx, hfind⟩ := mem_paintPositions (by simpa using hcon)
    have hxA : x = A := by
      rw [hA, graph_node hfind]
    rw [tileName_eq hshape]
    rcases hx with hu | hd
    · rw [hxA] at hu
      rw [hopts, List.mem_append]
      exact Or.inl (by rw [aboveOf_eq hp rel hu]; simp)
    · rw [hxA] at hd
      have hup : upA A y ∈ upsOf t := by
        have := hp.downUp rel (downA y A) hd
        simpa [downA, upA] using this
      rw [hopts, List.mem_append]
      exact Or.inr (by rw [belowOf_eq hp rel hup]; simp)
  have hinj : ∀ q1 ∈ l, ∀ q2 ∈ l, tileName q1 = tileName q2 → q1 = q2 := by
    intro q1 h1 q2 h2 he
    exact hp.tileNameInj rel q1 (by simpa using hlsub q1 h1) q2 (by simpa using hlsub q2 h2) he
  have hlnd : l.Nodup := hnd.filter _
  have hmapnd : (l.map tileName).Nodup := hlnd.map_on hinj
  have hlen : (l.map tileName).length ≤ opts.length :=
    length_le_of_subset' _ _ hmapnd (by
      intro z hz
      obtain ⟨q, hq, hqv⟩ := List.mem_map.mp hz
      rw [← hqv]
      exact hnames q hq)
  have hopt : opts.length ≤ 2 := by
    rw [hopts, List.length_append]
    have h1 : (aboveOf (upsOf t) A).toList.length ≤ 1 := by
      rcases aboveOf (upsOf t) A with _ | z <;> simp
    have h2 : (belowOf (upsOf t) A).toList.length ≤ 1 := by
      rcases belowOf (upsOf t) A with _ | z <;> simp
    omega
  rw [List.length_map] at hlen
  omega


/-! ### Vacating a square leaves at most two tiles unattended -/

theorem unattended_move (hp : Pinned d p) (rel : Bool) {σ τ : AtomState} {nd : Nat}
    (hnodup : (cfgOf (ground d p rel)).tiles.toList.Nodup)
    (htiles : ∀ q ∈ (cfgOf (ground d p rel)).tiles, τ q.goalAtom = σ q.goalAtom)
    (hocc : ∀ n, (robotPos (cfgOf (ground d p rel)) τ).contains n = true →
      (robotPos (cfgOf (ground d p rel)) σ).contains n = true ∨ n = nd) :
    unattended (cfgOf (ground d p rel)) σ ≤ unattended (cfgOf (ground d p rel)) τ + 2 := by
  set cfg := cfgOf (ground d p rel) with hcfg
  rw [unattended_eq, unattended_eq]
  set P := fun q => unattendedP cfg σ q && liveT σ q with hP
  set Q := fun q => unattendedP cfg τ q && liveT τ q with hQ
  set R := fun q : TileGoal => q.paintFrom.contains nd with hR
  have hsub : ∀ q ∈ cfg.tiles.toList.filter P,
      q ∈ cfg.tiles.toList.filter Q ++ cfg.tiles.toList.filter R := by
    intro q hq
    have hmem : q ∈ cfg.tiles.toList := (List.mem_filter.mp hq).1
    have hPq : P q = true := (List.mem_filter.mp hq).2
    have hlive : liveT σ q = true := (by simpa [hP] using hPq : _ ∧ _).2
    have hatt : unattendedP cfg σ q = true := (by simpa [hP] using hPq : _ ∧ _).1
    by_cases hRq : R q = true
    · exact List.mem_append.mpr (Or.inr (List.mem_filter.mpr ⟨hmem, hRq⟩))
    · refine List.mem_append.mpr (Or.inl (List.mem_filter.mpr ⟨hmem, ?_⟩))
      have hliveτ : liveT τ q = true := by
        rw [liveT] at hlive ⊢
        rw [htiles q (by simpa using hmem)]
        exact hlive
      have hattτ : unattendedP cfg τ q = true := by
        rw [unattendedP] at hatt ⊢
        simp only [Bool.not_eq_true'] at hatt ⊢
        rw [Array.any_eq_false] at hatt ⊢
        intro i hi hc
        rcases hocc _ hc with hs | hs
        · exact hatt i hi hs
        · exact hRq (by
            rw [hR]
            simpa [hs] using (Array.getElem_mem hi))
      simp [hQ, hattτ, hliveτ]
  have hnd1 : (cfg.tiles.toList.filter P).Nodup := hnodup.filter _
  have hlen := length_le_of_subset' _ _ hnd1 hsub
  rw [List.length_append] at hlen
  have h2 : (List.filter R cfg.tiles.toList).length ≤ 2 := by
    rw [hR]; exact two_tiles hp rel (nd := nd) hnodup
  omega


/-! ### The map atom a move reads is an edge -/

theorem dir_static (hp : Pinned d p) (rel : Bool) (hf : OpFacts d p o) {pr y x : Name}
    (hdir : pr = "up" ∨ pr = "down" ∨ pr = "right" ∨ pr = "left")
    (hmem : ({ pred := pr, args := [y, x] } : GroundAtom) ∈ hf.inst.pre) :
    ({ pred := pr, args := [y, x] } : GroundAtom) ∈ (ground d p rel).staticAtoms := by
  have hstatic : (staticPredicates d).contains pr = true := by
    rcases hdir with h | h | h | h <;> rw [h]
    exacts [hp.upStatic, hp.downStatic, hp.rightStatic, hp.leftStatic]
  have hgoal : ∀ b ∈ p.goal, b.pred ≠ pr := by
    rcases hdir with h | h | h | h <;> rw [h] <;>
      exact fun b hb => by
        first
          | exact hp.goalNotUp b hb
          | exact hp.goalNotDown b hb
          | exact hp.goalNotRight b hb
          | exact hp.goalNotLeft b hb
  have := static_of_pre hp rel hf hmem (by simpa using hstatic) (by simpa using hgoal)
  exact (Array.mem_filter.mp this).1

theorem move_edge (hp : Pinned d p) (rel : Bool) (hf : OpFacts d p o) {pr y x : Name}
    (hdir : pr = "up" ∨ pr = "down" ∨ pr = "right" ∨ pr = "left")
    (hmem : ({ pred := pr, args := [y, x] } : GroundAtom) ∈ hf.inst.pre) :
    ({ pred := pr, args := [x, y] } : GroundAtom) ∈ moveEdges (ground d p rel) := by
  refine Array.mem_filterMap.mpr ⟨_, dir_static hp rel hf hdir hmem, ?_⟩
  have hlist : (["up", "down", "left", "right"] : List Name).contains pr = true := by
    rcases hdir with h | h | h | h <;> rw [h] <;> rfl
  simp only [hlist, if_true]


/-! ### `move_up`, `move_down`, `move_right`, `move_left` -/

theorem move_step (hp : Pinned d p) (rel : Bool) (ho : o ∈ groundedOps d p rel)
    (hf : OpFacts d p o) {nm pr r x y : Name} (hs : hf.inst.schema = moveA nm pr)
    (ha : hf.inst.args = [r, x, y])
    (hdir : nm = "move_up" ∧ pr = "up" ∨ nm = "move_down" ∧ pr = "down" ∨
      nm = "move_right" ∧ pr = "right" ∨ nm = "move_left" ∧ pr = "left")
    (hnodup : (cfgOf (ground d p rel)).tiles.toList.Nodup)
    (hsound : Distances.Sound (graphOf (ground d p rel)) (cfgOf (ground d p rel)).dist)
    {σ : AtomState} (hinv : Inv σ) (happ : o.applicableA σ) :
    SchemaStep (graphOf (ground d p rel)) (cfgOf (ground d p rel)) σ (o.applyA σ) := by
  set t := ground d p rel with ht
  have hpr : pr = "up" ∨ pr = "down" ∨ pr = "right" ∨ pr = "left" := by
    rcases hdir with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h)),
      Or.inr (Or.inr (Or.inr h))]
  obtain ⟨hpreA, hpreCl, hpreD, hadd, hdel⟩ := move_atoms hf.inst hs ha
  have hatDyn : (staticPredicates d).contains (robotAt "" "").pred = false := by
    simpa [robotAt] using robotAt_dynamic hp.domain
  have hclDyn : (staticPredicates d).contains (clearT "").pred = false := by
    simpa [clearT] using clear_dynamic hp.domain
  have hrx : σ (robotAt r x) = true := pre_holds hf hpreA hatDyn happ
  have hcly : σ (clearT y) = true := pre_holds hf hpreCl hclDyn happ
  have hclx : σ (clearT x) = false := hinv.noClearUnder r x hrx
  have hxy : x ≠ y := by intro hc; rw [hc, hcly] at hclx; exact Bool.noConfusion hclx
  have hnoy : ∀ r', σ (robotAt r' y) = false := by
    intro r'
    by_contra hc
    rw [hinv.noClearUnder r' y (by simpa using hc)] at hcly
    exact Bool.noConfusion hcly
  -- the three objects are of their declared types
  obtain ⟨r', x', y', hargs, hwr, hwx, hwy⟩ := hf.inst.args_three (by rw [hs]; rfl)
  rw [ha] at hargs
  obtain ⟨hr', hx', hy'⟩ : r' = r ∧ x' = x ∧ y' = y := by
    simp only [List.cons.injEq, and_true] at hargs
    exact ⟨hargs.1.symm, hargs.2.1.symm, hargs.2.2.symm⟩
  rw [hr'] at hwr; rw [hx'] at hwx; rw [hy'] at hwy
  obtain ⟨nx, hnx⟩ := node_of_tile hp rel hwx
  obtain ⟨ny, hny⟩ := node_of_tile hp rel hwy
  -- frames
  have hfrPa : ∀ u c', o.applyA σ (painted u c') = σ (painted u c') := fun u c' =>
    frame_of_lists hf hadd hdel (by simp) (by simp) σ
  have hfrHas : ∀ r2 c', o.applyA σ (robotHas r2 c') = σ (robotHas r2 c') := fun r2 c' =>
    frame_of_lists hf hadd hdel (by simp) (by simp) σ
  have hfrOther : ∀ r2 z, r2 ≠ r → o.applyA σ (robotAt r2 z) = σ (robotAt r2 z) :=
    fun r2 z hr2 => frame_of_lists hf hadd hdel (by simp [hr2]) (by simp [hr2]) σ
  have hkey : ∀ z, o.applyA σ (robotAt r z) = true → z = y := by
    intro z hz
    by_cases hzy : z = y
    · exact hzy
    · exfalso
      have hnadd : robotAt r z ∉ [robotAt r y, clearT x] := by simp [hzy]
      by_cases hzx : z = x
      · subst hzx
        rw [falsified_of_lists hf hadd hdel hnadd (by simp) hpreA hatDyn σ] at hz
        exact Bool.noConfusion hz
      · rw [frame_of_lists hf hadd hdel hnadd (by simp [hzx]) σ] at hz
        exact hzx (hinv.oneAt r z x hz hrx)
  -- where the robots are afterwards
  have hposτ : ∀ n, n ∈ robotPos (cfgOf t) (o.applyA σ) →
      n ∈ robotPos (cfgOf t) σ ∨ n = ny := by
    intro n hn
    obtain ⟨r2, z, f, hr2, hlt, hname, hσ2, hnode⟩ := mem_robotPos hn
    by_cases hr2r : r2 = r
    · subst hr2r
      have hzy : z = y := hkey z hσ2
      rw [hzy] at hnode
      rw [hny] at hnode
      exact Or.inr (by simpa using hnode.symm)
    · refine Or.inl (node_mem_robotPos hr2 hlt hname hnode ?_ hinv.oneAt)
      rw [hfrOther r2 z hr2r] at hσ2
      exact hσ2
  have hnxpos : nx ∈ robotPos (cfgOf t) σ := by
    obtain ⟨f, hlt, hname⟩ := numbered_of_op d p rel ho
      (a := robotAt r x) (Or.inl (pre_mem_op hf hpreA hatDyn))
    exact node_mem_robotPos (mem_robots hp rel hwr) hlt hname hnx hrx hinv.oneAt
  refine .move ny ⟨tiles_frame d p rel hfrPa, colours_frame hfrHas, ?_, ?_, ?_⟩
  · -- one square changes every distance by at most one
    intro a w hw
    rcases hposτ w hw with hσw | hwny
    · exact ⟨w, hσw, Nat.le_add_left _ _⟩
    · refine ⟨nx, hnxpos, ?_⟩
      rw [hwny]
      by_cases hja : a < (graphOf t).size
      · exact hsound.step nx ny a (graph_lt hnx) hja
          (graph_edge (move_edge hp rel hf hpr hpreD) hnx hny)
      · rw [Distances.get_of_col_ge hsound nx (Nat.le_of_not_lt hja),
          Distances.get_of_col_ge hsound ny (Nat.le_of_not_lt hja)]
        omega
  · intro n hn
    rcases hposτ n (by simpa using hn) with h | h
    · exact Or.inl (by simpa using h)
    · exact Or.inr h
  · exact unattended_move hp rel hnodup (tiles_frame d p rel hfrPa)
      (fun n hn => by
        rcases hposτ n (by simpa using hn) with h | h
        · exact Or.inl (by simpa using h)
        · exact Or.inr h)


/-! ### `paint_up` and `paint_down` -/

/-- The goal atom of a tile named by the goal tiles. -/
theorem goalTile_atom {t : Task} {z : Name} (h : z ∈ goalTilesOf t) :
    ∃ cz, painted z cz ∈ t.goalAtoms ∧ painted z cz ∈ t.goalAtomsWith "painted" := by
  obtain ⟨a, hamem, hval⟩ := Array.mem_filterMap.mp h
  have hpred : a.pred = "painted" := by
    have := (Array.mem_filter.mp hamem).2
    simpa using this
  have hgoal : a ∈ t.goalAtoms := (Array.mem_filter.mp hamem).1
  revert hval
  rcases hargs : a.args with _ | ⟨u, rest⟩
  · simp
  · cases rest with
    | nil => simp
    | cons cz rest' =>
        cases rest' with
        | cons _ _ => simp
        | nil =>
            simp only [Option.some.injEq]
            intro hu
            have hatom : a = painted z cz := by
              show a = { pred := "painted", args := [z, cz] }
              rw [← hpred, ← hu, ← hargs]
            exact ⟨cz, by rw [← hatom]; exact hgoal, by rw [← hatom]; exact hamem⟩

/--
**A robot that paints from above walls in the tile it stands on.**

The tile it stands on is a goal tile, still unpainted, and the only square it
can be painted from is the one just painted.  No robot can enter that square
again, so the walk does not reach it and the dead-end test fires.
-/
theorem paint_dead (hp : Pinned d p) (rel : Bool) (hf : OpFacts d p o)
    {nm pr r y x c : Name} (hs : hf.inst.schema = paintA nm pr)
    (ha : hf.inst.args = [r, y, x, c])
    (hdown : downA y x ∈ downsOf (ground d p rel))
    (hcap : cappedByGoals (upsOf (ground d p rel)) (goalTiles (ground d p rel))
      (fuelOf (ground d p rel)) y = true)
    {σ : AtomState} (hinv : Inv σ) (happ : o.applicableA σ) :
    isDead (cfgOf (ground d p rel)) (o.applyA σ) = true := by
  set t := ground d p rel with ht
  obtain ⟨hpreC, hpreA, hpreCl, hpreD, hadd, hdel⟩ := paint_atoms hf.inst hs ha
  have hatDyn : (staticPredicates d).contains (robotAt "" "").pred = false := by
    simpa [robotAt] using robotAt_dynamic hp.domain
  have hclDyn : (staticPredicates d).contains (clearT "").pred = false := by
    simpa [clearT] using clear_dynamic hp.domain
  have hrx : σ (robotAt r x) = true := pre_holds hf hpreA hatDyn happ
  have hcly : σ (clearT y) = true := pre_holds hf hpreCl hclDyn happ
  have hclx : σ (clearT x) = false := hinv.noClearUnder r x hrx
  have hxy : x ≠ y := by intro hc; rw [hc, hcly] at hclx; exact Bool.noConfusion hclx
  have hnoy : ∀ r', σ (robotAt r' y) = false := by
    intro r'
    rcases hc : σ (robotAt r' y) with _ | _
    · rfl
    · rw [hinv.noClearUnder r' y hc] at hcly; exact absurd hcly (by simp)
  have hfrAt : ∀ r2 z, o.applyA σ (robotAt r2 z) = σ (robotAt r2 z) := fun r2 z =>
    frame_of_lists hf hadd hdel (by simp) (by simp) σ
  have hfrPa : ∀ u c2, (u, c2) ≠ (y, c) → o.applyA σ (painted u c2) = σ (painted u c2) := by
    intro u c2 hne
    refine frame_of_lists hf hadd hdel ?_ (by simp) σ
    simp only [List.mem_singleton, painted, GroundAtom.mk.injEq, true_and]
    intro hc2
    refine hne ?_
    have hll : [u, c2] = [y, c] := hc2
    simp only [List.cons.injEq, and_true] at hll
    rw [hll.1, hll.2]
  have hcly' : o.applyA σ (clearT y) = false :=
    falsified_of_lists hf hadd hdel (by simp) (by simp) hpreCl hclDyn σ
  obtain ⟨r', y', x', c', hargs, hwr, hwy, hwx, hwc⟩ := hf.inst.args_four (by rw [hs]; rfl)
  rw [ha] at hargs
  obtain ⟨hr', hy', hx', hc'⟩ : r' = r ∧ y' = y ∧ x' = x ∧ c' = c := by
    simp only [List.cons.injEq, and_true] at hargs
    exact ⟨hargs.1.symm, hargs.2.1.symm, hargs.2.2.1.symm, hargs.2.2.2.symm⟩
  rw [hy'] at hwy
  obtain ⟨ny, hny⟩ := node_of_tile hp rel hwy
  have hnoy_contra : (robotPos (cfgOf t) (o.applyA σ)).contains ny = true → False := by
    intro hcon
    obtain ⟨r2, z, f2, -, -, -, hσ2, hnode⟩ := mem_robotPos (by simpa using hcon)
    have hzy : z = y := by rw [← graph_node hnode, graph_node hny]
    rw [hzy, hfrAt] at hσ2
    rw [hnoy r2] at hσ2
    exact Bool.noConfusion hσ2
  have hup : upA x y ∈ upsOf t := by
    have := hp.downUp rel (downA y x) hdown
    simpa [downA, upA] using this
  obtain ⟨hgoalx, hcapx⟩ :=
    capped_step (upsOf t) (goalTiles t) hcap (aboveOf_eq hp rel hup)
  have hforcedx : forcedFromOf t x = some ny := by
    show (if cappedByGoals (upsOf t) (goalTiles t) (fuelOf t) x = true then
        (belowOf (upsOf t) x).bind (graphOf t).find? else none) = some ny
    rw [if_pos hcapx, belowOf_eq hp rel hup]
    simpa using hny
  obtain ⟨cx, hgoalatom, hgoalw⟩ := goalTile_atom (t := t) (by simpa using hgoalx)
  have hcolx : (coloursOf t).contains cx = true := by
    have := hp.goalColours rel (painted x cx) hgoalw
    simpa [painted] using this
  obtain ⟨qx, hqxmem, hqxshape⟩ := tiles_cover d p rel hgoalatom hcolx
  have hxnpτ : o.applyA σ qx.goalAtom = false := by
    rw [hqxshape.atom, hfrPa x cx (by simp [hxy])]
    exact hinv.occNotPainted r x cx hrx
  unfold isDead
  refine Array.any_eq_true'.mpr ⟨qx, Array.mem_filter.mpr ⟨hqxmem, by simp [hxnpτ]⟩, ?_⟩
  rw [hqxshape.forced, hforcedx]
  simp only [Bool.not_eq_true']
  by_contra hc
  rcases reachable_guarded (cfgOf t) (o.applyA σ) ny (by simpa using hc) with hrob | hcl2
  · exact hnoy_contra hrob
  · revert hcl2
    rcases hclv : (cfgOf t).clearAtoms.getD ny none with _ | a
    · simp
    · have hname := hp.clearNames rel ny a hclv
      rw [hname, graph_node hny]
      show o.applyA σ (clearT y) = true → False
      rw [hcly']
      simp

theorem paint_step (hp : Pinned d p) (rel : Bool) (ho : o ∈ groundedOps d p rel)
    (hf : OpFacts d p o) {nm pr r y x c : Name} (hs : hf.inst.schema = paintA nm pr)
    (ha : hf.inst.args = [r, y, x, c])
    (hdir : nm = "paint_up" ∧ pr = "up" ∨ nm = "paint_down" ∧ pr = "down")
    {σ : AtomState} (hinv : Inv σ) (happ : o.applicableA σ) :
    SchemaStep (graphOf (ground d p rel)) (cfgOf (ground d p rel)) σ (o.applyA σ) := by
  set t := ground d p rel with ht
  have hpr : pr = "up" ∨ pr = "down" ∨ pr = "right" ∨ pr = "left" := by
    rcases hdir with ⟨-, h⟩ | ⟨-, h⟩
    exacts [Or.inl h, Or.inr (Or.inl h)]
  obtain ⟨hpreC, hpreA, hpreCl, hpreD, hadd, hdel⟩ := paint_atoms hf.inst hs ha
  have hatDyn : (staticPredicates d).contains (robotAt "" "").pred = false := by
    simpa [robotAt] using robotAt_dynamic hp.domain
  have hhasDyn : (staticPredicates d).contains (robotHas "" "").pred = false := by
    simpa [robotHas] using robotHas_dynamic hp.domain
  have hclDyn : (staticPredicates d).contains (clearT "").pred = false := by
    simpa [clearT] using clear_dynamic hp.domain
  have hrx : σ (robotAt r x) = true := pre_holds hf hpreA hatDyn happ
  have hcly : σ (clearT y) = true := pre_holds hf hpreCl hclDyn happ
  have hrc : σ (robotHas r c) = true := pre_holds hf hpreC hhasDyn happ
  have hclx : σ (clearT x) = false := hinv.noClearUnder r x hrx
  have hxy : x ≠ y := by intro hc; rw [hc, hcly] at hclx; exact Bool.noConfusion hclx
  have hnoy : ∀ r', σ (robotAt r' y) = false := by
    intro r'
    by_contra hc
    rw [hinv.noClearUnder r' y (by simpa using hc)] at hcly
    exact Bool.noConfusion hcly
  have hfrAt : ∀ r2 z, o.applyA σ (robotAt r2 z) = σ (robotAt r2 z) := fun r2 z =>
    frame_of_lists hf hadd hdel (by simp) (by simp) σ
  have hfrHas : ∀ r2 c2, o.applyA σ (robotHas r2 c2) = σ (robotHas r2 c2) := fun r2 c2 =>
    frame_of_lists hf hadd hdel (by simp) (by simp) σ
  have hfrPa : ∀ u c2, (u, c2) ≠ (y, c) → o.applyA σ (painted u c2) = σ (painted u c2) := by
    intro u c2 hne
    refine frame_of_lists hf hadd hdel ?_ (by simp) σ
    simp only [List.mem_singleton, painted, GroundAtom.mk.injEq, true_and]
    intro hc2
    refine hne ?_
    have hll : [u, c2] = [y, c] := hc2
    simp only [List.cons.injEq, and_true] at hll
    rw [hll.1, hll.2]
  have hcly' : o.applyA σ (clearT y) = false :=
    falsified_of_lists hf hadd hdel (by simp) (by simp) hpreCl hclDyn σ
  -- the tiles that do not move
  have hother : ∀ q ∈ (cfgOf t).tiles, q.goalAtom ≠ painted y c →
      o.applyA σ q.goalAtom = σ q.goalAtom := by
    intro q hq hne
    obtain ⟨u, c2, hshape⟩ := tiles_shape d p rel hq
    rw [hshape.atom] at hne ⊢
    refine hfrPa u c2 ?_
    intro hc
    exact hne (by
      obtain ⟨h1, h2⟩ : u = y ∧ c2 = c := by simpa using hc
      rw [h1, h2])
  by_cases hflip : σ (painted y c) = false ∧ o.applyA σ (painted y c) = true
  · by_cases hq : ∃ q ∈ (cfgOf t).tiles, q.goalAtom = painted y c
    · obtain ⟨q, hqmem, hqatom⟩ := hq
      obtain ⟨y2, c2, hshape⟩ := tiles_shape d p rel hqmem
      have hy2 : y2 = y ∧ c2 = c := by
        have h0 := hshape.atom
        rw [hqatom] at h0
        simpa using h0.symm
      rw [hy2.1, hy2.2] at hshape
      -- the robot stands on a square this tile is painted from
      obtain ⟨r', y', x', c', hargs, hwr, hwy, hwx, hwc⟩ :=
        hf.inst.args_four (by rw [hs]; rfl)
      rw [ha] at hargs
      obtain ⟨hr', hy', hx', hc'⟩ : r' = r ∧ y' = y ∧ x' = x ∧ c' = c := by
        simp only [List.cons.injEq, and_true] at hargs
        exact ⟨hargs.1.symm, hargs.2.1.symm, hargs.2.2.1.symm, hargs.2.2.2.symm⟩
      rw [hr'] at hwr; rw [hy'] at hwy; rw [hx'] at hwx; rw [hc'] at hwc
      obtain ⟨nx, hnx⟩ := node_of_tile hp rel hwx
      obtain ⟨ny, hny⟩ := node_of_tile hp rel hwy
      have hstatic : upA y x ∈ upsOf t ∨ downA y x ∈ downsOf t :=
        paint_dir_static hp rel hf hs ha hdir hpreD
      have hnxpos : nx ∈ robotPos (cfgOf t) σ := by
        obtain ⟨f, hlt, hname⟩ := numbered_of_op d p rel ho
          (a := robotAt r x) (Or.inl (pre_mem_op hf hpreA hatDyn))
        exact node_mem_robotPos (mem_robots hp rel hwr) hlt hname hnx hrx hinv.oneAt
      have hnoy_contra : (robotPos (cfgOf t) (o.applyA σ)).contains ny = true → False := by
        intro hcon
        obtain ⟨r2, z, f2, -, -, -, hσ2, hnode⟩ := mem_robotPos (by simpa using hcon)
        have hzy : z = y := by
          rw [← graph_node hnode, graph_node hny]
        rw [hzy, hfrAt] at hσ2
        rw [hnoy r2] at hσ2
        exact Bool.noConfusion hσ2
      by_cases hocc : ∀ pn, q.forcedFrom = some pn → (robotPos (cfgOf t) σ).contains pn = true
      · refine .paint q ⟨hqmem, by rw [hqatom]; exact hflip.1, by rw [hqatom]; exact hflip.2,
          ?_, robots_frame hfrAt, colours_frame hfrHas, ?_, hocc, ?_⟩
        · intro q2 hq2 hne
          refine hother q2 hq2 ?_
          intro hc
          refine hne (hp.tileNameInj rel q2 hq2 q hqmem ?_)
          rw [hc, hqatom]
        · refine ⟨nx, ?_, hnxpos, graph_lt hnx⟩
          rw [hshape.paint]
          exact mem_paintPositions_of hstatic hnx
        · obtain ⟨f, hlt, hname⟩ := numbered_of_op d p rel ho
            (a := robotHas r c) (Or.inl (pre_mem_op hf hpreC hhasDyn))
          exact colour_held hshape.size hshape.colour hlt hname hrc
      · -- painting from above walls in the tile above
        push_neg at hocc
        obtain ⟨pn, hpn, hpnc⟩ := hocc
        rw [hshape.forced] at hpn
        have hpn2 : (if cappedByGoals (upsOf t) (goalTiles t) (fuelOf t) y = true then
            (belowOf (upsOf t) y).bind (graphOf t).find? else none) = some pn := hpn
        have hcap : cappedByGoals (upsOf t) (goalTiles t) (fuelOf t) y = true := by
          by_contra hc
          rw [if_neg hc] at hpn2
          simp at hpn2
        rw [if_pos hcap] at hpn2
        have hdown : downA y x ∈ downsOf t := by
          rcases hstatic with hu | hd
          · exfalso
            rw [belowOf_eq hp rel hu] at hpn2
            have hpnx : pn = nx := by
              have h2 : (graphOf t).find? x = some pn := hpn2
              rw [hnx] at h2
              simpa using h2.symm
            exact hpnc (by rw [hpnx]; simpa using hnxpos)
          · exact hd
        exact .deadAfter (paint_dead hp rel hf hs ha hdown hcap hinv happ)
    · refine .colour 0 ⟨?_, robots_frame hfrAt, ?_⟩
      · intro q hqmem
        refine hother q hqmem ?_
        intro hc
        exact hq ⟨q, hqmem, hc⟩
      · intro ci hfalse
        exact Or.inl (by rw [colours_frame hfrHas ci]; exact hfalse)
  · refine .colour 0 ⟨?_, robots_frame hfrAt, ?_⟩
    · intro q hqmem
      by_cases hcq : q.goalAtom = painted y c
      · rw [hcq]
        by_cases hσ : σ (painted y c) = false
        · rw [hσ]
          by_contra hne2
          exact hflip ⟨hσ, by simpa using hne2⟩
        · rw [show σ (painted y c) = true from by simpa using hσ]
          by_cases hin : painted y c ∈ o.add
          · exact applyA_add σ hin
          · have hnd2 : painted y c ∉ o.del := by
              intro hc2
              have := hf.subDel _ hc2
              rw [hdel] at this
              simp [painted, clearT] at this
            rw [applyA_frame σ hin hnd2]
            exact (show σ (painted y c) = true from by simpa using hσ)
      · exact hother q hqmem hcq
    · intro ci hfalse
      exact Or.inl (by rw [colours_frame hfrHas ci]; exact hfalse)


/-! ### The dead-end test is closed under the transitions -/

private theorem enterableOf_eq (c : Cfg) (σ : AtomState) (v : Nat) :
    enterableOf c σ v = ((robotPos c σ).contains v || clearAt c σ v) := rfl

private theorem clearAt_eq (c : Cfg) (σ : AtomState) (v : Nat) :
    clearAt c σ v =
      match c.clearAtoms.getD v none with
      | some a => σ a
      | none => false := rfl

/-- A robot standing on the square makes it enterable. -/
theorem enterable_of_robot {σ : AtomState} {v : Nat}
    (h : (robotPos (cfgOf (ground d p rel)) σ).contains v = true) :
    enterableOf (cfgOf (ground d p rel)) σ v = true := by
  rw [enterableOf_eq, h]; rfl

/-- The walk's region, read through the clear table. -/
theorem enterable_of_clear (hp : Pinned d p) (rel : Bool) {σ : AtomState} {v : Nat}
    (hcl : (cfgOf (ground d p rel)).clearAtoms.getD v none
      = some (clearT ((graphOf (ground d p rel)).nodes.getD v "")))
    (hσ : σ (clearT ((graphOf (ground d p rel)).nodes.getD v "")) = true) :
    enterableOf (cfgOf (ground d p rel)) σ v = true := by
  rw [enterableOf_eq, clearAt_eq, hcl]
  change (_ || σ (clearT ((graphOf (ground d p rel)).nodes.getD v ""))) = true
  rw [hσ]; exact Bool.or_true _

/-- What the clear table holds at a square, whatever it holds. -/
theorem clear_table (hp : Pinned d p) (rel : Bool) {σ : AtomState} {v : Nat}
    (h : enterableOf (cfgOf (ground d p rel)) σ v = true) :
    (robotPos (cfgOf (ground d p rel)) σ).contains v = true ∨
      ((cfgOf (ground d p rel)).clearAtoms.getD v none
          = some (clearT ((graphOf (ground d p rel)).nodes.getD v "")) ∧
        σ (clearT ((graphOf (ground d p rel)).nodes.getD v "")) = true) := by
  have hor : (robotPos (cfgOf (ground d p rel)) σ).contains v = true ∨
      clearAt (cfgOf (ground d p rel)) σ v = true :=
    Bool.or_eq_true_iff.mp (enterableOf_eq _ _ _ ▸ h)
  rcases hor with hrob | hcl
  · exact Or.inl hrob
  · refine Or.inr ?_
    have hopt := (cfgOf (ground d p rel)).clearAtoms.getD v none
    revert hcl
    generalize he : (cfgOf (ground d p rel)).clearAtoms.getD v none = e
    cases e with
    | none =>
      intro hcl
      have : false = true := by rw [clearAt_eq, he] at hcl; exact hcl
      exact Bool.noConfusion this
    | some a =>
      intro hcl
      have ha : a = clearT ((graphOf (ground d p rel)).nodes.getD v "") :=
        hp.clearNames rel v a he
      refine ⟨?_, ?_⟩
      · rw [ha]
      · rw [clearAt_eq, he, ha] at hcl; exact hcl



set_option maxHeartbeats 400000 in
theorem paint_this_tile_core (hp : Pinned d p) (rel : Bool)
    (hf : OpFacts d p o) (t : Task) (ht : t = ground d p rel)
    {nm pr r y x c y2 c2 : Name} {nx : Nat} {σ : AtomState} {q0 : TileGoal}
    (hs : hf.inst.schema = paintA nm pr) (ha : hf.inst.args = [r, y, x, c])
    (hshape : TileShape t q0 y2 c2) (hy2 : y2 = y)
    (hst : upA y2 x ∈ upsOf t ∨ downA y2 x ∈ downsOf t)
    (hnx : (graphOf t).find? x = some nx)
    (hnxpos : nx ∈ robotPos (cfgOf t) σ)
    (hq0blocked : Blocked (cfgOf t) σ q0 = true)
    (hinv : Inv σ) (happ : o.applicableA σ) :
    isDead (cfgOf t) (o.applyA σ) = true := by
  have hnxseen := robot_square_seen t hnxpos (graph_lt (t := t) hnx)
  have hpaint := mem_tile_paintFrom (t := t) hshape hst hnx
  rcases hforced : q0.forcedFrom with _ | pn
  · exfalso
    have hb : Blocked (cfgOf t) σ q0 = true := hq0blocked
    unfold Blocked at hb
    rw [hforced] at hb
    simp only [Bool.not_eq_true'] at hb
    rw [Array.any_eq_true'.mpr ⟨nx, hpaint, hnxseen⟩] at hb
    exact Bool.noConfusion hb
  · have hbne : (reachable (cfgOf t) σ).getD pn false = false := by
      have hb : Blocked (cfgOf t) σ q0 = true := hq0blocked
      unfold Blocked at hb
      rw [hforced] at hb
      simpa using hb
    have hpnx : pn ≠ nx := by
      intro hc; rw [hc, hnxseen] at hbne; exact Bool.noConfusion hbne
    have hforced2 : forcedFromOf t y2 = some pn := by
      rw [← hshape.forced]; exact hforced
    have hcap2 : cappedByGoals (upsOf t) (goalTiles t) (fuelOf t) y2 = true := by
      unfold forcedFromOf forcedOf at hforced2
      by_contra hc
      rw [if_neg hc] at hforced2
      cases hforced2
    have hdown2 : downA y2 x ∈ downsOf t := by
      unfold forcedFromOf forcedOf at hforced2
      rw [if_pos hcap2] at hforced2
      rcases hst with hu | hd
      · exfalso
        have hbelow : belowOf (upsOf t) y2 = some x := by
          have hu' : upA y2 x ∈ upsOf (ground d p rel) := ht ▸ hu
          have := belowOf_eq hp rel hu'
          rwa [← ht] at this
        rw [hbelow] at hforced2
        have h2 : (graphOf t).find? x = some pn := hforced2
        rw [hnx] at h2
        exact hpnx (Option.some.inj h2.symm)
      · exact hd
    have hdown : downA y x ∈ downsOf t := by rw [← hy2]; exact hdown2
    have hcap : cappedByGoals (upsOf t) (goalTiles t) (fuelOf t) y = true := by
      rw [← hy2]; exact hcap2
    subst ht
    exact paint_dead hp rel hf hs ha hdown hcap hinv happ

theorem paint_this_tile_dead (hp : Pinned d p) (rel : Bool)
    (ho : o ∈ groundedOps d p rel) (hf : OpFacts d p o)
    {nm pr r y x c : Name} (hs : hf.inst.schema = paintA nm pr)
    (ha : hf.inst.args = [r, y, x, c])
    (hdir : nm = "paint_up" ∧ pr = "up" ∨ nm = "paint_down" ∧ pr = "down")
    (hpreA : robotAt r x ∈ hf.inst.pre)
    (hpreD : { pred := pr, args := [y, x] } ∈ hf.inst.pre)
    (hatDyn : (staticPredicates d).contains (robotAt "" "").pred = false)
    {σ : AtomState} {q0 : TileGoal} (hq0mem : q0 ∈ (cfgOf (ground d p rel)).tiles)
    (hq0y : q0.goalAtom = painted y c)
    (hq0blocked : Blocked (cfgOf (ground d p rel)) σ q0 = true)
    (hinv : Inv σ) (happ : o.applicableA σ)
    (hrx : σ (robotAt r x) = true) :
    isDead (cfgOf (ground d p rel)) (o.applyA σ) = true := by
  set t := ground d p rel with ht
  obtain ⟨y2, c2, hshape⟩ := tiles_shape d p rel hq0mem
  have hy2 : y2 = y :=
    ((painted_eq y2 c2 y c).mp (hshape.atom.symm.trans hq0y)).1
  obtain ⟨r', y', x', c', hargs, hwr, hwy, hwx, hwc⟩ :=
    hf.inst.args_four (by rw [hs]; rfl)
  rw [ha] at hargs
  obtain ⟨hr', hy', hx', hc'⟩ : r' = r ∧ y' = y ∧ x' = x ∧ c' = c := by
    simp only [List.cons.injEq, and_true] at hargs
    exact ⟨hargs.1.symm, hargs.2.1.symm, hargs.2.2.1.symm, hargs.2.2.2.symm⟩
  rw [hr'] at hwr; rw [hx'] at hwx
  obtain ⟨nx, hnx⟩ := node_of_tile hp rel hwx
  have hst : upA y2 x ∈ upsOf t ∨ downA y2 x ∈ downsOf t := by
    have h := paint_dir_static hp rel hf hs ha hdir hpreD
    rw [← hy2] at h; exact h
  have hnxpos : nx ∈ robotPos (cfgOf t) σ := by
    obtain ⟨f2, hlt, hname⟩ := numbered_of_op d p rel ho
      (a := robotAt r x) (Or.inl (pre_mem_op hf hpreA hatDyn))
    exact node_mem_robotPos (mem_robots hp rel hwr) hlt hname hnx hrx hinv.oneAt
  exact paint_this_tile_core hp rel hf t ht hs ha hshape hy2 hst hnx hnxpos hq0blocked hinv happ

set_option maxHeartbeats 400000 in
theorem paint_stays_dead (hp : Pinned d p) (rel : Bool)
    (ho : o ∈ groundedOps d p rel) (hf : OpFacts d p o)
    {nm pr r y x c : Name} (hs : hf.inst.schema = paintA nm pr)
    (ha : hf.inst.args = [r, y, x, c])
    (hdir : nm = "paint_up" ∧ pr = "up" ∨ nm = "paint_down" ∧ pr = "down")
    {σ : AtomState} (hinv : Inv σ) (happ : o.applicableA σ)
    (hdead : isDead (cfgOf (ground d p rel)) σ = true) :
    isDead (cfgOf (ground d p rel)) (o.applyA σ) = true := by
  set t := ground d p rel with ht
  have hatDyn : (staticPredicates d).contains (robotAt "" "").pred = false := by
    simpa [robotAt] using robotAt_dynamic hp.domain
  have hclDyn : (staticPredicates d).contains (clearT "").pred = false := by
    simpa [clearT] using clear_dynamic hp.domain
  obtain ⟨q0, hq0mem, hq0live, hq0blocked⟩ := blocked_of_isDead _ _ hdead
  obtain ⟨hpreC, hpreA, hpreCl, hpreD, hadd, hdel⟩ := paint_atoms hf.inst hs ha
  have hrx : σ (robotAt r x) = true := pre_holds hf hpreA hatDyn happ
  have hcly : σ (clearT y) = true := pre_holds hf hpreCl hclDyn happ
  have hclx : σ (clearT x) = false := hinv.noClearUnder r x hrx
  have hxy : x ≠ y := by intro hc; rw [hc, hcly] at hclx; exact Bool.noConfusion hclx
  have hfrAt : ∀ r2 z, o.applyA σ (robotAt r2 z) = σ (robotAt r2 z) := fun r2 z =>
    frame_of_lists hf hadd hdel (by simp) (by simp) σ
  have hfrCl : ∀ z, z ≠ y → o.applyA σ (clearT z) = σ (clearT z) := fun z hz =>
    frame_of_lists hf hadd hdel (by simp) (by simp [hz]) σ
  have hcly' : o.applyA σ (clearT y) = false :=
    falsified_of_lists hf hadd hdel (by simp) (by simp) hpreCl hclDyn σ
  have hfrPa : ∀ u c2, (u, c2) ≠ (y, c) → o.applyA σ (painted u c2) = σ (painted u c2) := by
    intro u c2 hne
    refine frame_of_lists hf hadd hdel ?_ (by simp) σ
    simp only [List.mem_singleton, painted, GroundAtom.mk.injEq, true_and]
    intro hc2
    refine hne ?_
    have hll : [u, c2] = [y, c] := hc2
    simp only [List.cons.injEq, and_true] at hll
    rw [hll.1, hll.2]
  -- the walk only ever narrows
  have hsub : ∀ pn, (reachable (cfgOf t) (o.applyA σ)).getD pn false = true →
      (reachable (cfgOf t) σ).getD pn false = true := by
    refine reachable_mono _ _ _ ?_ ?_
    · intro pn hpn
      rw [robots_frame hfrAt] at hpn
      obtain ⟨r2, z, f2, -, -, -, -, hnode⟩ := mem_robotPos hpn
      exact reachable_start _ _ hpn (by rw [cfg_adj, graph_adj_size]; exact graph_lt hnode)
    · intro v hv hen
      rcases clear_table hp rel hen with hrob | ⟨hcl, hσa⟩
      · rw [robots_frame hfrAt] at hrob
        exact enterable_of_robot hrob
      · refine enterable_of_clear hp rel hcl ?_
        by_cases hzy : (graphOf t).nodes.getD v "" = y
        · rw [hzy, hcly'] at hσa; exact absurd hσa (by simp)
        · rw [hfrCl _ hzy] at hσa; exact hσa
  by_cases hq0y : q0.goalAtom = painted y c
  · exact paint_this_tile_dead hp rel ho hf hs ha hdir hpreA hpreD hatDyn
      hq0mem hq0y hq0blocked hinv happ hrx
  · refine isDead_of_blocked _ _ hq0mem ?_ (blocked_mono _ σ _ hsub hq0blocked)
    have hlive' : o.applyA σ q0.goalAtom = σ q0.goalAtom := by
      obtain ⟨u, c2, hs⟩ := tiles_shape d p rel hq0mem
      rw [hs.atom]
      refine hfrPa u c2 ?_
      intro heq
      apply hq0y
      rw [hs.atom]
      simpa using heq
    rw [hlive']
    exact hq0live


theorem move_stays_dead (hp : Pinned d p) (rel : Bool)
    (ho : o ∈ groundedOps d p rel) (hf : OpFacts d p o)
    {nm pr r x y : Name} (hs : hf.inst.schema = moveA nm pr)
    (ha : hf.inst.args = [r, x, y])
    (hdir : nm = "move_up" ∧ pr = "up" ∨ nm = "move_down" ∧ pr = "down" ∨
      nm = "move_right" ∧ pr = "right" ∨ nm = "move_left" ∧ pr = "left")
    {σ : AtomState} (hinv : Inv σ) (happ : o.applicableA σ)
    (hdead : isDead (cfgOf (ground d p rel)) σ = true) :
    isDead (cfgOf (ground d p rel)) (o.applyA σ) = true := by
  set t := ground d p rel with ht
  have hatDyn : (staticPredicates d).contains (robotAt "" "").pred = false := by
    simpa [robotAt] using robotAt_dynamic hp.domain
  have hclDyn : (staticPredicates d).contains (clearT "").pred = false := by
    simpa [clearT] using clear_dynamic hp.domain
  obtain ⟨q0, hq0mem, hq0live, hq0blocked⟩ := blocked_of_isDead _ _ hdead
  obtain ⟨hpreA, hpreCl, hpreD, hadd, hdel⟩ := move_atoms hf.inst hs ha
  have hrx : σ (robotAt r x) = true := pre_holds hf hpreA hatDyn happ
  have hcly : σ (clearT y) = true := pre_holds hf hpreCl hclDyn happ
  have hclx : σ (clearT x) = false := hinv.noClearUnder r x hrx
  have hxy : x ≠ y := by intro hc; rw [hc, hcly] at hclx; exact Bool.noConfusion hclx
  have hfrPa : ∀ u c2, o.applyA σ (painted u c2) = σ (painted u c2) := fun u c2 =>
    frame_of_lists hf hadd hdel (by simp) (by simp) σ
  have hfrOther : ∀ r2 z, r2 ≠ r → o.applyA σ (robotAt r2 z) = σ (robotAt r2 z) :=
    fun r2 z hr2 => frame_of_lists hf hadd hdel (by simp [hr2]) (by simp [hr2]) σ
  have hfrCl : ∀ z, z ≠ y → z ≠ x → o.applyA σ (clearT z) = σ (clearT z) :=
    fun z hzy hzx => frame_of_lists hf hadd hdel (by simp [hzx]) (by simp [hzy]) σ
  obtain ⟨r', x', y', hargs, hwr, hwx, hwy⟩ := hf.inst.args_three (by rw [hs]; rfl)
  rw [ha] at hargs
  obtain ⟨hr', hx', hy'⟩ : r' = r ∧ x' = x ∧ y' = y := by
    simp only [List.cons.injEq, and_true] at hargs
    exact ⟨hargs.1.symm, hargs.2.1.symm, hargs.2.2.symm⟩
  rw [hr'] at hwr; rw [hx'] at hwx; rw [hy'] at hwy
  obtain ⟨nx, hnx⟩ := node_of_tile hp rel hwx
  obtain ⟨ny, hny⟩ := node_of_tile hp rel hwy
  have hnxpos : nx ∈ robotPos (cfgOf t) σ := by
    obtain ⟨f2, hlt, hname⟩ := numbered_of_op d p rel ho
      (a := robotAt r x) (Or.inl (pre_mem_op hf hpreA hatDyn))
    exact node_mem_robotPos (mem_robots hp rel hwr) hlt hname hnx hrx hinv.oneAt
  have hnxseen : (reachable (cfgOf t) σ).getD nx false = true :=
    reachable_start _ _ hnxpos (by rw [cfg_adj, graph_adj_size]; exact graph_lt hnx)
  have hclyfact : (cfgOf t).clearAtoms.getD ny none = some (clearT y) := by
    obtain ⟨f2, hlt, hname⟩ := numbered_of_op d p rel ho
      (a := clearT y) (Or.inl (pre_mem_op hf hpreCl hclDyn))
    exact clearAtom_of_fact t hlt hname hny
  have hnyseen : (reachable (cfgOf t) σ).getD ny false = true := by
    refine reachable_closed (cfgOf t) σ nx ny hnxseen ?_ ?_ ?_
    · rw [cfg_adj]
      exact graph_edge (move_edge hp rel hf (by
        rcases hdir with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
        exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h)),
          Or.inr (Or.inr (Or.inr h))]) hpreD) hnx hny
    · refine enterable_of_clear hp rel ?_ ?_
      · rw [hclyfact, graph_node hny]
      · rw [graph_node hny]; exact hcly
    · rw [cfg_adj, graph_adj_size]; exact graph_lt hny
  have hsub : ∀ pn, (reachable (cfgOf t) (o.applyA σ)).getD pn false = true →
      (reachable (cfgOf t) σ).getD pn false = true := by
    refine reachable_mono _ _ _ ?_ ?_
    · intro pn hpn
      obtain ⟨r2, z, f2, hr2, hlt2, hname2, hσ2, hnode2⟩ := mem_robotPos hpn
      by_cases hr2r : r2 = r
      · have hzy : z = y := by
          subst hr2r
          by_cases hzy : z = y
          · exact hzy
          · exfalso
            have hnadd : robotAt r2 z ∉ [robotAt r2 y, clearT x] := by simp [hzy]
            by_cases hzx : z = x
            · subst hzx
              rw [falsified_of_lists hf hadd hdel hnadd (by simp) hpreA hatDyn σ] at hσ2
              exact Bool.noConfusion hσ2
            · rw [frame_of_lists hf hadd hdel hnadd (by simp [hzx]) σ] at hσ2
              exact hzx (hinv.oneAt r2 z x hσ2 hrx)
        rw [hzy, hny] at hnode2
        rw [show pn = ny from by simpa using hnode2.symm]
        exact hnyseen
      · rw [hfrOther r2 z hr2r] at hσ2
        exact reachable_start _ _ (node_mem_robotPos hr2 hlt2 hname2 hnode2 hσ2 hinv.oneAt)
          (by rw [cfg_adj, graph_adj_size]; exact graph_lt hnode2)
    · intro v hv hen
      rcases clear_table hp rel hen with hrob | ⟨hcl, hσa⟩
      · -- a robot stands there afterwards
        obtain ⟨r2, z, f2, hr2, hlt2, hname2, hσ2, hnode2⟩ := mem_robotPos (by simpa using hrob)
        by_cases hr2r : r2 = r
        · have hzy : z = y := by
            subst hr2r
            by_cases hzy : z = y
            · exact hzy
            · exfalso
              have hnadd : robotAt r2 z ∉ [robotAt r2 y, clearT x] := by simp [hzy]
              by_cases hzx : z = x
              · subst hzx
                rw [falsified_of_lists hf hadd hdel hnadd (by simp) hpreA hatDyn σ] at hσ2
                exact Bool.noConfusion hσ2
              · rw [frame_of_lists hf hadd hdel hnadd (by simp [hzx]) σ] at hσ2
                exact hzx (hinv.oneAt r2 z x hσ2 hrx)
          have hvny : v = ny := by
            rw [hzy, hny] at hnode2
            simpa using hnode2.symm
          refine enterable_of_clear hp rel ?_ ?_
          · rw [hvny, hclyfact, graph_node hny]
          · rw [hvny, graph_node hny]; exact hcly
        · rw [hfrOther r2 z hr2r] at hσ2
          refine enterable_of_robot ?_
          have := node_mem_robotPos hr2 hlt2 hname2 hnode2 hσ2 hinv.oneAt
          simpa using this
      · -- the square is clear afterwards
        by_cases hax : (graphOf t).nodes.getD v "" = x
        · -- the square the robot left; it stood there before
          have hvnx : v = nx := by
            refine node_inj hp rel ?_ (graph_lt hnx) ?_
            · rw [← graph_adj_size, ← cfg_adj]; exact hv
            · rw [hax, graph_node hnx]
          refine enterable_of_robot ?_
          rw [hvnx]; simpa using hnxpos
        · by_cases hay : (graphOf t).nodes.getD v "" = y
          · refine enterable_of_clear hp rel hcl ?_
            rw [hay]; exact hcly
          · refine enterable_of_clear hp rel hcl ?_
            rw [hfrCl _ hay hax] at hσa; exact hσa
  refine isDead_of_blocked _ _ hq0mem ?_ (blocked_mono _ σ _ hsub hq0blocked)
  rw [tiles_frame d p rel hfrPa q0 hq0mem]
  exact hq0live

set_option maxHeartbeats 400000 in
theorem dead_closed (hp : Pinned d p) (rel : Bool) :
    ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ → o.applicableA σ →
      isDead (cfgOf (ground d p rel)) σ = true →
      isDead (cfgOf (ground d p rel)) (o.applyA σ) = true := by
  intro o ho σ hinv happ hdead
  set t := ground d p rel with ht
  obtain ⟨hf⟩ := opFacts_ground d p rel ho
  have hatDyn : (staticPredicates d).contains (robotAt "" "").pred = false := by
    simpa [robotAt] using robotAt_dynamic hp.domain
  have hclDyn : (staticPredicates d).contains (clearT "").pred = false := by
    simpa [clearT] using clear_dynamic hp.domain
  obtain ⟨q0, hq0mem, hq0live, hq0blocked⟩ := blocked_of_isDead _ _ hdead
  rcases instance_shape hp.domain hf.inst with
    ⟨r, c, c2, hs, ha⟩ | ⟨nm, pr, r, y, x, c, hs, ha, hdir⟩ | ⟨nm, pr, r, x, y, hs, ha, hdir⟩
  · -- change_color: nothing the walk reads moves
    obtain ⟨hpre, hadd, hdel⟩ := change_atoms hf.inst hs ha
    have hfrAt : ∀ r2 z, o.applyA σ (robotAt r2 z) = σ (robotAt r2 z) := fun r2 z =>
      frame_of_lists hf hadd hdel (by simp) (by simp) σ
    have hfrCl : ∀ z, o.applyA σ (clearT z) = σ (clearT z) := fun z =>
      frame_of_lists hf hadd hdel (by simp) (by simp) σ
    have hfrPa : ∀ u c2, o.applyA σ (painted u c2) = σ (painted u c2) := fun u c2 =>
      frame_of_lists hf hadd hdel (by simp) (by simp) σ
    refine isDead_of_blocked _ _ hq0mem ?_ ?_
    · rw [tiles_frame d p rel hfrPa q0 hq0mem]; exact hq0live
    · refine blocked_mono _ σ _ ?_ hq0blocked
      refine reachable_mono _ _ _ ?_ ?_
      · intro pn hpn
        rw [robots_frame hfrAt] at hpn
        obtain ⟨r2, z, f2, -, -, -, -, hnode⟩ := mem_robotPos hpn
        exact reachable_start _ _ hpn (by rw [cfg_adj, graph_adj_size]; exact graph_lt hnode)
      · intro v hv hen
        rcases clear_table hp rel hen with hrob | ⟨hcl, hσa⟩
        · rw [robots_frame hfrAt] at hrob
          exact enterable_of_robot hrob
        · refine enterable_of_clear hp rel hcl ?_
          rw [hfrCl] at hσa
          exact hσa
  · exact paint_stays_dead hp rel ho hf hs ha hdir hinv happ hdead
  · exact move_stays_dead hp rel ho hf hs ha hdir hinv happ hdead


/-! ### Assembling the shape -/

/-- Every tile of the table is a goal of the problem. -/
theorem goalAtom_mem (d : Domain) (p : Problem) (rel : Bool) :
    ∀ q ∈ (cfgOf (ground d p rel)).tiles, q.goalAtom ∈ p.goal := by
  intro q hq
  obtain ⟨x, hx, hxq⟩ := Array.mem_map.mp hq
  subst hxq
  obtain ⟨z, hz, hzval⟩ := Array.mem_filterMap.mp hx
  obtain ⟨-, hlt, -⟩ := Array.mem_zipIdx hz
  obtain ⟨y, c, -, hfact, -, -, -, -⟩ := tileEntry_shape hzval
  show atomOf (ground d p rel) x.goalFact ∈ p.goal
  rw [hfact]
  exact goalAtom_of_index d p rel (by simpa using hlt)

/-- The goal atoms read back from the compiled tile table are duplicate-free. -/
theorem tile_goalAtoms_nodup (hgoal : p.goal.Nodup) (rel : Bool) :
    ((ExampleHeuristics.Floortile.compile (ground d p rel)).tiles.map
      fun q => atomOf (ground d p rel) q.goalFact).toList.Nodup := by
  have htiles : (ExampleHeuristics.Floortile.compile (ground d p rel)).tiles =
      ((ground d p rel).goalAtoms.zipIdx).filterMap
        (ExampleHeuristics.Floortile.tileEntry (ground d p rel)
          (coloursOf (ground d p rel)) (paintFromOf (ground d p rel))
          (forcedFromOf (ground d p rel))) := rfl
  rw [htiles, Array.map_filterMap]
  refine goalTable_nodup d p rel hgoal _ id ?_
  intro x hx b hb
  obtain ⟨hlt, -⟩ := List.mem_zipIdx' hx
  have hi : x.2 < (ground d p rel).goalAtoms.size := by simpa using hlt
  obtain ⟨y, hy, hval⟩ := Option.map_eq_some_iff.mp hb
  obtain ⟨-, -, -, hgoal, -, -, -, -⟩ := tileEntry_shape hy
  rw [← hval]
  show atomOf (ground d p rel) y.goalFact = _
  rw [hgoal]
  exact atomOf_goal_getD d p rel hi

/-- The compiled tile entries are duplicate-free by their distinct goal atoms. -/
theorem tile_entries_nodup (hp : Pinned d p) (rel : Bool) :
    (cfgOf (ground d p rel)).tiles.toList.Nodup := by
  have heq : ((cfgOf (ground d p rel)).tiles.toList.map (·.goalAtom)) =
      ((ExampleHeuristics.Floortile.compile (ground d p rel)).tiles.map
        fun q => atomOf (ground d p rel) q.goalFact).toList := by
    simp [cfgOf, tileOf, Array.toList_map, List.map_map, Function.comp_def, atomOf]
  exact List.Nodup.of_map (·.goalAtom)
    (by rw [heq]; exact tile_goalAtoms_nodup hp.goalNodup rel)

/-- Every operator costs something. -/
theorem cost_pos (hp : Pinned d p) (rel : Bool) :
    ∀ o ∈ groundedOps d p rel, 0 < o.cost := by
  intro o ho
  obtain ⟨hf⟩ := opFacts_ground d p rel ho
  rw [hf.cost]
  show 0 < hf.inst.schema.cost
  rcases instance_shape hp.domain hf.inst with
    ⟨r, c, c2, hs, ha⟩ | ⟨nm, pr, r2, y, x, c3, hs, ha, hdir⟩ |
      ⟨nm, pr, r4, x, y, hs, ha, hdir⟩
  · rw [hs]; decide
  · rw [hs]; show 0 < 1; omega
  · rw [hs]; show 0 < 1; omega

/-- **Every operator the grounder builds has one of the shapes.** -/
theorem schemaStep_of_ops (hp : Pinned d p) (rel : Bool)
    (hnodup : (cfgOf (ground d p rel)).tiles.toList.Nodup)
    (hsound : Distances.Sound (graphOf (ground d p rel)) (cfgOf (ground d p rel)).dist) :
    ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ → o.applicableA σ →
      SchemaStep (graphOf (ground d p rel)) (cfgOf (ground d p rel)) σ (o.applyA σ) := by
  intro o ho σ hinv happ
  obtain ⟨hf⟩ := opFacts_ground d p rel ho
  rcases instance_shape hp.domain hf.inst with
    ⟨r, c, c2, hs, ha⟩ | ⟨nm, pr, r, y, x, c, hs, ha, hdir⟩ | ⟨nm, pr, r, x, y, hs, ha, hdir⟩
  · exact colour_step hp rel ho hf hs ha happ
  · exact paint_step hp rel ho hf hs ha hdir hinv happ
  · exact move_step hp rel ho hf hs ha hdir hnodup hsound hinv happ

/--
**Floortile's improved heuristic is admissible on the task the grounder builds.**

The dead-end test is closed under every schema (`dead_closed`).  The numeric
value stays under `deadEnd` by `Pinned.small`.
-/
theorem improved_admissible (hp : Pinned d p) (rel : Bool)
    (hwf : Task.WF (ground d p rel))
    (hnodup : (cfgOf (ground d p rel)).tiles.toList.Nodup)
    (hsound : Distances.Sound (graphOf (ground d p rel)) (cfgOf (ground d p rel)).dist) :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel))
      (ExampleHeuristics.Floortile.improved (ground d p rel)).eval :=
  compiled_admissibleOn d p rel (graphOf (ground d p rel)) (cfgOf (ground d p rel)) Inv
    (dataMatches_ground d p rel hwf) hwf (cost_pos hp rel) (goalAtom_mem d p rel) hnodup
    hsound (schemaStep_of_ops hp rel hnodup hsound) (dead_closed hp rel)
    (fun σ => Nat.le_trans (baseValue_le _ σ) (hp.small rel))
    (initInv_of_check hp.initCheck)
    (fun o ho σ hinv happ => by
      obtain ⟨hf⟩ := opFacts_ground d p rel ho
      exact inv_preserved hp.domain hf hinv happ)

/--
**Floortile's improved heuristic never overestimates** on the task the
grounder builds, at every state the search can reach, with relevance pruning on
or off.
-/
theorem improved_admissible_of_pinned (hp : Pinned d p) (rel : Bool) :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel))
      (ExampleHeuristics.Floortile.improved (ground d p rel)).eval :=
  improved_admissible hp rel
    (ground_wf d p rel (cost_pos hp rel))
    (tile_entries_nodup hp rel)
    (by rw [cfg_dist]; exact Distances.sound_of _)


/-- **Floortile's improved heuristic is zero at every reachable goal.** -/
theorem improved_goalAware_of_pinned (hp : Pinned d p) (rel : Bool) :
    (ground d p rel).GoalAwareOn (Reachable (ground d p rel))
      (ExampleHeuristics.Floortile.improved (ground d p rel)).eval :=
  compiled_goalAwareOn d p rel (cfgOf (ground d p rel)) Inv
    (dataMatches_ground d p rel (ground_wf d p rel (cost_pos hp rel)))
    (ground_wf d p rel (cost_pos hp rel)) (cost_pos hp rel) (goalAtom_mem d p rel)
    (initInv_of_check hp.initCheck)
    (fun o ho σ hinv happ => by
      obtain ⟨hf⟩ := opFacts_ground d p rel ho
      exact inv_preserved hp.domain hf hinv happ)

/-- **And is consistent on the states the search can reach.** -/
theorem improved_consistent_of_pinned (hp : Pinned d p) (rel : Bool) :
    (ground d p rel).ConsistentOn (Reachable (ground d p rel))
      (ExampleHeuristics.Floortile.improved (ground d p rel)).eval :=
  compiled_consistentOn d p rel (graphOf (ground d p rel)) (cfgOf (ground d p rel)) Inv
    (dataMatches_ground d p rel (ground_wf d p rel (cost_pos hp rel)))
    (ground_wf d p rel (cost_pos hp rel)) (cost_pos hp rel) (tile_entries_nodup hp rel)
    (by rw [cfg_dist]; exact Distances.sound_of _)
    (schemaStep_of_ops hp rel (tile_entries_nodup hp rel)
      (by rw [cfg_dist]; exact Distances.sound_of _))
    (dead_closed hp rel)
    (fun σ => Nat.le_trans (baseValue_le _ σ) (hp.small rel))
    (initInv_of_check hp.initCheck)
    (fun o ho σ hinv happ => by
      obtain ⟨hf⟩ := opFacts_ground d p rel ho
      exact inv_preserved hp.domain hf hinv happ)

/-! ### The executable certificate

The record above speaks about the grounded task and about both relevance
settings, so the certificate grounds the task both ways and checks the
task-level conditions on each.  Everything else it decides on the parsed domain
and problem.
-/

open ExampleHeuristics.Floortile.Certificate in
theorem up_pair_of {t : Task} (h : mapConds t = true) :
    ∀ a ∈ t.staticWith "up", a.args = [a.args.getD 0 "", a.args.getD 1 ""] := by
  simp only [mapConds, Bool.and_eq_true] at h
  intro a ha
  exact list_eq_two (by simpa using array_all_of_mem h.1.1.1.1 ha)

open ExampleHeuristics.Floortile.Certificate in
theorem down_pair_of {t : Task} (h : mapConds t = true) :
    ∀ a ∈ t.staticWith "down", a.args = [a.args.getD 0 "", a.args.getD 1 ""] := by
  simp only [mapConds, Bool.and_eq_true] at h
  intro a ha
  exact list_eq_two (by simpa using array_all_of_mem h.1.1.1.2 ha)

open ExampleHeuristics.Floortile.Certificate in
theorem up_one_below_of {t : Task} (h : mapConds t = true) :
    ∀ a ∈ t.staticWith "up", ∀ b ∈ t.staticWith "up",
      a.args.getD 0 "" = b.args.getD 0 "" → a.args.getD 1 "" = b.args.getD 1 "" := by
  simp only [mapConds, Bool.and_eq_true] at h
  intro a ha b hb heq
  have hb' := array_all_of_mem (array_all_of_mem h.1.1.2 ha) hb
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, beq_eq_false_iff_ne, ne_eq] at hb'
  rcases hb' with hne | hy
  · exact absurd heq hne
  · exact hy

open ExampleHeuristics.Floortile.Certificate in
theorem up_one_above_of {t : Task} (h : mapConds t = true) :
    ∀ a ∈ t.staticWith "up", ∀ b ∈ t.staticWith "up",
      a.args.getD 1 "" = b.args.getD 1 "" → a.args.getD 0 "" = b.args.getD 0 "" := by
  simp only [mapConds, Bool.and_eq_true] at h
  intro a ha b hb heq
  have hb' := array_all_of_mem (array_all_of_mem h.1.2 ha) hb
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, beq_eq_false_iff_ne, ne_eq] at hb'
  rcases hb' with hne | hy
  · exact absurd heq hne
  · exact hy

open ExampleHeuristics.Floortile.Certificate in
theorem down_up_of {t : Task} (h : mapConds t = true) :
    ∀ a ∈ t.staticWith "down",
      ({ pred := "up", args := [a.args.getD 1 "", a.args.getD 0 ""] } : GroundAtom)
        ∈ t.staticWith "up" := by
  simp only [mapConds, Bool.and_eq_true] at h
  intro a ha
  have hb := array_all_of_mem h.2 ha
  simpa using hb

open ExampleHeuristics.Floortile.Certificate in
theorem goal_colours_of {t : Task} (h : tableConds t = true) :
    ∀ a ∈ t.goalAtomsWith "painted",
      (coloursOf t).contains (a.args.getD 1 "") = true := by
  simp only [tableConds, Bool.and_eq_true] at h
  intro a ha
  exact array_all_of_mem h.1.1.1 ha

open ExampleHeuristics.Floortile.Certificate in
theorem small_of {t : Task} (h : tableConds t = true) :
    2 * (cfgOf t).tiles.size
      + max (cfgOf t).dist.bound (cfgOf t).tiles.size ≤ deadEnd := by
  simp only [tableConds, Bool.and_eq_true] at h
  have := of_decide_eq_true h.2
  simpa [cfgOf] using this

open ExampleHeuristics.Floortile.Certificate in
/-- Each tile's `clear` entry names that tile's own square. -/
theorem clear_names_of {t : Task} (h : tableConds t = true) :
    ∀ i : Nat, ∀ a : GroundAtom,
      (cfgOf t).clearAtoms.getD i none = some a →
        a = clearT ((graphOf t).nodes.getD i "") := by
  simp only [tableConds, Bool.and_eq_true] at h
  have hz := h.1.1.2
  intro i a hi
  have hmap : (cfgOf t).clearAtoms
      = (ExampleHeuristics.Floortile.compile t).clearFacts.map
          (Option.map (atomOf t)) := rfl
  rw [hmap, Array.getD_eq_getD_getElem?, Array.getElem?_map] at hi
  rcases hlt : (ExampleHeuristics.Floortile.compile t).clearFacts[i]? with _ | of
  · rw [hlt] at hi; simp at hi
  · rw [hlt] at hi
    simp only [Option.map_some, Option.getD_some] at hi
    rcases of with _ | f
    · simp at hi
    · simp only [Option.map_some, Option.some.injEq] at hi
      have hsize : i < (ExampleHeuristics.Floortile.compile t).clearFacts.size :=
        Array.getElem?_eq_some_iff.mp hlt |>.1
      have hmem : ((ExampleHeuristics.Floortile.compile t).clearFacts[i], i)
          ∈ (ExampleHeuristics.Floortile.compile t).clearFacts.zipIdx := by
        rw [Array.mem_zipIdx_iff_getElem?]
        simp [Array.getElem?_eq_getElem hsize]
      have hb := array_all_of_mem hz hmem
      have hget : (ExampleHeuristics.Floortile.compile t).clearFacts[i] = some f := by
        have := Array.getElem?_eq_some_iff.mp hlt
        simpa using this.2
      rw [hget] at hb
      simp only [beq_iff_eq] at hb
      rw [← hi, atomOf, hb]
      rfl

open ExampleHeuristics.Floortile.Certificate in
/-- No two tile entries name the same tile. -/
theorem tile_name_inj_of {d : Domain} {p : Problem} (hgoal : p.goal.Nodup)
    (rel : Bool) (h : tableConds (ground d p rel) = true) :
    ∀ q1 ∈ (cfgOf (ground d p rel)).tiles,
      ∀ q2 ∈ (cfgOf (ground d p rel)).tiles,
      q1.goalAtom.args.getD 0 "" = q2.goalAtom.args.getD 0 "" → q1 = q2 := by
  simp only [tableConds, Bool.and_eq_true] at h
  have hpair := h.1.2
  have hatoms : ((ExampleHeuristics.Floortile.compile
      (ground d p rel)).tiles.toList.map
        fun q => atomOf (ground d p rel) q.goalFact).Nodup := by
    simpa [Array.toList_map] using tile_goalAtoms_nodup (d := d) hgoal rel
  intro q1 h1 q2 h2 hname
  have hmap : (cfgOf (ground d p rel)).tiles =
      (ExampleHeuristics.Floortile.compile (ground d p rel)).tiles.map
        (tileOf (ground d p rel)) := rfl
  rw [hmap, Array.mem_map] at h1 h2
  obtain ⟨e1, he1, rfl⟩ := h1
  obtain ⟨e2, he2, rfl⟩ := h2
  have hb := array_all_of_mem (array_all_of_mem hpair he1) he2
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, beq_eq_false_iff_ne,
    ne_eq] at hb
  rcases hb with hne | heq
  · exact absurd hname hne
  · have he : e1 = e2 :=
      List.inj_on_of_nodup_map hatoms (by simpa using he1) (by simpa using he2) heq
    rw [he]

open ExampleHeuristics.Floortile.Certificate in
theorem certificate_sound {d : Domain} {p : Problem}
    (hv : Validated d p)
    (h : ExampleHeuristics.Floortile.Certificate.certified d p = true) :
    Pinned d p := by
  simp only [ExampleHeuristics.Floortile.Certificate.certified,
    ExampleHeuristics.Floortile.Certificate.conditions, Certificate.passes,
    List.all_cons, List.all_nil, Bool.and_eq_true] at h
  rcases h with
    ⟨hactions, hup, hdown, hleft, hright, hgoalEdge, hinit, htile, hrobot, hcolor,
      hgoalNodup, hgoalTile, hfalse, htrue, -⟩
  have hpairs : ∀ pred : Pddl.Name,
      Planner.Certificate.initPairs p pred = initPairs p pred := fun _ => rfl
  have hones : ∀ pred : Pddl.Name,
      Planner.Certificate.initOnes p pred = initOnes p pred := fun _ => rfl
  have htask : ∀ rel : Bool, taskConds d p rel = true := by
    intro rel; cases rel
    · exact hfalse
    · exact htrue
  have hmapc : ∀ rel : Bool, mapConds (ground d p rel) = true := by
    intro rel
    have hb := htask rel
    rw [taskConds, Bool.and_eq_true] at hb
    exact hb.1
  have htabc : ∀ rel : Bool, tableConds (ground d p rel) = true := by
    intro rel
    have hb := htask rel
    rw [taskConds, Bool.and_eq_true] at hb
    exact hb.2
  have hgoalNodup' : p.goal.Nodup := of_decide_eq_true hgoalNodup
  have hedge : ∀ a ∈ p.goal, a.pred ≠ "up" ∧ a.pred ≠ "down" ∧
      a.pred ≠ "left" ∧ a.pred ≠ "right" := by
    rw [List.all_eq_true] at hgoalEdge
    intro a ha
    have hb := hgoalEdge a ha
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hb
    exact ⟨hb.1.1.1, hb.1.1.2, hb.1.2, hb.2⟩
  exact
    { domain := by simpa using hactions
      validated := hv
      upStatic := by simpa using hup
      downStatic := by simpa using hdown
      leftStatic := by simpa using hleft
      rightStatic := by simpa using hright
      goalNotUp := fun a ha => (hedge a ha).1
      goalNotDown := fun a ha => (hedge a ha).2.1
      goalNotLeft := fun a ha => (hedge a ha).2.2.1
      goalNotRight := fun a ha => (hedge a ha).2.2.2
      goalNodup := hgoalNodup'
      initCheck := by
        rw [ExampleHeuristics.Floortile.Certificate.initInvCheck] at hinit
        simpa [hpairs, hones, initInvCheck] using hinit
      upPair := fun rel => up_pair_of (hmapc rel)
      upOneBelow := fun rel => up_one_below_of (hmapc rel)
      upOneAbove := fun rel => up_one_above_of (hmapc rel)
      downUp := fun rel => down_up_of (hmapc rel)
      downPair := fun rel => down_pair_of (hmapc rel)
      goalColours := fun rel => goal_colours_of (htabc rel)
      tileType := Certificate.exactType_sound htile
      robotType := Certificate.exactType_sound hrobot
      colorType := Certificate.exactType_sound hcolor
      tileNameInj := fun rel => tile_name_inj_of hgoalNodup' rel (htabc rel)
      clearNames := fun rel => clear_names_of (htabc rel)
      small := fun rel => small_of (htabc rel) }

theorem improved_goalAware_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool)
    (h : ExampleHeuristics.Floortile.Certificate.certified d p = true) :
    (ground d p rel).GoalAwareOn (Reachable (ground d p rel))
      (ExampleHeuristics.Floortile.improved (ground d p rel)).eval :=
  improved_goalAware_of_pinned (certificate_sound hv h) rel

theorem improved_consistent_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool)
    (h : ExampleHeuristics.Floortile.Certificate.certified d p = true) :
    (ground d p rel).ConsistentOn (Reachable (ground d p rel))
      (ExampleHeuristics.Floortile.improved (ground d p rel)).eval :=
  improved_consistent_of_pinned (certificate_sound hv h) rel

theorem improved_proof_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool) :
    ImprovedProof d p rel
      (ExampleHeuristics.Floortile.Certificate.certified d p)
      (ExampleHeuristics.Floortile.improved (ground d p rel)) :=
  { goalAware := improved_goalAware_of_certificate hv rel
    consistent := improved_consistent_of_certificate hv rel }

theorem improved_admissible_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool)
    (h : ExampleHeuristics.Floortile.Certificate.certified d p = true) :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel))
      (ExampleHeuristics.Floortile.improved (ground d p rel)).eval :=
  (improved_proof_of_certificate hv rel).admissible h

end Planner.Lifted.Floortile
