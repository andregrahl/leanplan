/-
Sokoban's parsed domain, as the vocabulary both of its heuristics read.

This file holds no heuristic proof.  It fixes the two schemas the parser
produces, the atoms they touch, and the record `Pinned` that says what a task
must satisfy.  `Proofs/Domains/Sokoban.lean` and
`Proofs/Domains/SokobanSimple.lean` each read this file, and neither reads the
other.
-/
import Proofs.LiftedHeuristic
import Proofs.CompileSupport
import Proofs.Validation
import Planner.GeneratedDomains.Sokoban

/-
Which domain a Sokoban task came from.

Two schemas, four predicates.  `adjacent` is the only static one; `at-robot`,
`at` and `clear` all move.  Note what `move` does *not* touch: `clear` here means
"no box stands here", not "no robot", so walking never changes it.  Only `push`
does, and it changes exactly two squares — the one the box leaves and the one it
enters.
-/

namespace Planner.Lifted.Sokoban

open Planner Planner.Pddl

/-! ### The domain's atoms -/

abbrev atRobot (l : Name) : GroundAtom := { pred := "at-robot", args := [l] }
abbrev atBox (b l : Name) : GroundAtom := { pred := "at", args := [b, l] }
abbrev clearL (l : Name) : GroundAtom := { pred := "clear", args := [l] }
abbrev adjacent (l1 l2 d : Name) : GroundAtom :=
  { pred := "adjacent", args := [l1, l2, d] }

/-! ### Telling the atoms apart -/

@[simp] theorem atRobot_inj {x y : Name} : (atRobot x = atRobot y) = (x = y) := by
  simp [atRobot]
@[simp] theorem clearL_inj {x y : Name} : (clearL x = clearL y) = (x = y) := by
  simp [clearL]
@[simp] theorem atBox_inj {b l b' l' : Name} :
    (atBox b l = atBox b' l') = (b = b' ∧ l = l') := by simp [atBox]
@[simp] theorem atRobot_ne_atBox (x b l : Name) : atRobot x ≠ atBox b l := by
  simp [atRobot, atBox]
@[simp] theorem atRobot_ne_clearL (x y : Name) : atRobot x ≠ clearL y := by
  simp [atRobot, clearL]
@[simp] theorem atBox_ne_atRobot (b l x : Name) : atBox b l ≠ atRobot x := by
  simp [atRobot, atBox]
@[simp] theorem atBox_ne_clearL (b l y : Name) : atBox b l ≠ clearL y := by
  simp [atBox, clearL]
@[simp] theorem clearL_ne_atRobot (y x : Name) : clearL y ≠ atRobot x := by
  simp [atRobot, clearL]
@[simp] theorem clearL_ne_atBox (y b l : Name) : clearL y ≠ atBox b l := by
  simp [atBox, clearL]

/-! ### The schemas, as the parser produces them -/

abbrev locP (n : Name) : TypedName := { name := n, type := "location" }
abbrev dirP (n : Name) : TypedName := { name := n, type := "direction" }
abbrev boxP (n : Name) : TypedName := { name := n, type := "box" }

abbrev atRobotV (l : Name) : Atom := { pred := "at-robot", args := [.var l] }
abbrev atBoxV (b l : Name) : Atom := { pred := "at", args := [.var b, .var l] }
abbrev clearV (l : Name) : Atom := { pred := "clear", args := [.var l] }
abbrev adjacentV (l1 l2 d : Name) : Atom :=
  { pred := "adjacent", args := [.var l1, .var l2, .var d] }

abbrev moveA : Action := Planner.GeneratedDomains.Sokoban.action0

abbrev pushA : Action := Planner.GeneratedDomains.Sokoban.action1

/-- The parsed domain is Sokoban. -/
abbrev SokobanDomain (d : Domain) : Prop :=
  d.actions = Planner.GeneratedDomains.Sokoban.actions

/-! ### Every predicate the value reads is dynamic -/

theorem atRobot_dynamic {d : Domain} (hd : SokobanDomain d) :
    (staticPredicates d).contains "at-robot" = false :=
  not_static_of_mem_add (a := moveA) (by rw [hd]; simp) (y := atRobotV "?to")
    (by simp [moveA])

theorem atBox_dynamic {d : Domain} (hd : SokobanDomain d) :
    (staticPredicates d).contains "at" = false :=
  not_static_of_mem_add (a := pushA) (by rw [hd]; simp) (y := atBoxV "?b" "?floc")
    (by simp [pushA])

theorem clear_dynamic {d : Domain} (hd : SokobanDomain d) :
    (staticPredicates d).contains "clear" = false :=
  not_static_of_mem_add (a := pushA) (by rw [hd]; simp) (y := clearV "?bloc")
    (by simp [pushA])

/-! ### Instances -/

theorem instance_shape {d : Domain} {objects : List TypedName} (hd : SokobanDomain d)
    (i : Instance d objects) :
    (∃ f t dir, i.schema = moveA ∧ i.args = [f, t, dir]) ∨
    (∃ rl bl fl dir b, i.schema = pushA ∧ i.args = [rl, bl, fl, dir, b]) := by
  have hmem : i.schema ∈ [moveA, pushA] := by
    have hm : i.schema ∈ d.actions := i.mem
    rw [hd] at hm
    exact hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with hs | hs
  · obtain ⟨f, t, dir, ha, -, -, -⟩ := i.args_three (by rw [hs])
    exact Or.inl ⟨f, t, dir, hs, ha⟩
  · obtain ⟨rl, bl, fl, dir, b, ha, -, -, -, -, -⟩ := i.args_five (by rw [hs])
    exact Or.inr ⟨rl, bl, fl, dir, b, hs, ha⟩

/-! ### What each instance reads, adds and deletes -/

theorem move_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {f t dir : Name} (hs : i.schema = moveA) (ha : i.args = [f, t, dir]) :
    atRobot f ∈ i.pre ∧ i.add = [atRobot t] ∧ i.del = [atRobot f] := by
  have hp : i.pre = [clearL t, atRobot f, adjacent f t dir] := by
    rw [i.pre_eq, hs, ha]; rfl
  have hadd : i.add = [atRobot t] := by rw [i.add_eq, hs, ha]; rfl
  have hdel : i.del = [atRobot f] := by rw [i.del_eq, hs, ha]; rfl
  simp [hp, hadd, hdel]

theorem push_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {rl bl fl dir b : Name} (hs : i.schema = pushA)
    (ha : i.args = [rl, bl, fl, dir, b]) :
    atRobot rl ∈ i.pre ∧ atBox b bl ∈ i.pre ∧ clearL fl ∈ i.pre ∧
      i.add = [atRobot bl, atBox b fl, clearL bl] ∧
      i.del = [atRobot rl, atBox b bl, clearL fl] := by
  have hp : i.pre = [atRobot rl, atBox b bl, clearL fl, adjacent rl bl dir,
      adjacent bl fl dir] := by rw [i.pre_eq, hs, ha]; rfl
  have hadd : i.add = [atRobot bl, atBox b fl, clearL bl] := by
    rw [i.add_eq, hs, ha]; rfl
  have hdel : i.del = [atRobot rl, atBox b bl, clearL fl] := by
    rw [i.del_eq, hs, ha]; rfl
  simp [hp, hadd, hdel]

end Planner.Lifted.Sokoban

namespace Planner.Lifted.Sokoban

open Planner Planner.Pddl

/-- What a Sokoban task must satisfy for the proof to apply. -/
structure Pinned (d : Domain) (p : Problem) : Prop where
  /-- The two schemas are the ones the parser produces. -/
  domain : SokobanDomain d
  locationType : "location" ∈ d.typeNames
  directionType : "direction" ∈ d.typeNames
  boxType : "box" ∈ d.typeNames
  /-- The `location` parameter type indexes exactly the square table; it has no
  proper subtype among the problem's objects. -/
  locTypeExact : ∀ o ∈ allObjects d p,
    d.isSubtype o.type "location" = true → o.type = "location"
  /-- And so does the `box` parameter type. -/
  boxTypeExact : ∀ o ∈ allObjects d p,
    d.isSubtype o.type "box" = true → o.type = "box"
  /-- The pair passed the planner's own validators.  `namesNodup` below is read
  off it rather than assumed: validation checks the objects for duplicates, the
  constants for duplicates, and rejects an object that shadows a constant. -/
  validated : Validated d p
  /-- The goal names each atom once. -/
  goalNodup : p.goal.Nodup
  /-- The map never moves: `adjacent` is the domain's one static predicate. -/
  adjacentStatic : (staticPredicates d).contains "adjacent" = true
  /-- The goal mentions no static predicate, as in the shipped Sokoban tasks. -/
  goalDynamic : ∀ a ∈ p.goal, (staticPredicates d).contains a.pred = false
  /--
  No square is adjacent to itself.

  Without this a `move` could be a self-loop, adding and deleting the same
  `at-robot` atom.  The grounder handles that correctly — it drops a delete whose
  atom the schema also adds — but `OpFacts` does not expose the fact, so the
  proof cannot see it.
  -/
  noSelfAdjacent : ∀ l dd : Pddl.Name, adjacent l l dd ∉ p.init
  /--
  Every step of the map steps back.

  This is what makes the robot's own square relevant, and so what makes the
  relevance analysis keep the `at-robot` add of every operator it keeps.  An atom
  is relevant only if some operator that writes into the relevant set reads it,
  and the operator that reads `at-robot ?to` is the move back out of `?to`.

  It holds of every Sokoban task in the benchmark set: the generator emits
  `adjacent` both ways for every pair of neighbouring squares.
  -/
  adjReverses : ∀ l1 l2 dd : Pddl.Name, adjacent l1 l2 dd ∈ p.init →
    ∃ dd' : Pddl.Name, WellTyped d (allObjects d p) "direction" dd' ∧
      adjacent l2 l1 dd' ∈ p.init


end Planner.Lifted.Sokoban

/- -------------------------------------------------------------------------- -/

/-
What a Sokoban task must satisfy, and the parts of its step proof that follow
from the two schemas alone.

`adjacent` is the domain's only static predicate, so a schema's dynamic
preconditions are numbered without further ado.  The frames are simpler than any
other domain's: `move` touches only `at-robot`, and `push` touches all three
dynamic families but each at named squares.
-/

namespace Planner.Lifted.Sokoban

open Planner Planner.Pddl

variable {d : Domain} {p : Problem}

/-- The object names are distinct — decided by validation, not assumed. -/
theorem Pinned.namesNodup {d : Domain} {p : Problem} (hp : Pinned d p) :
    ((allObjects d p).map (·.name)).Nodup := hp.validated.namesNodup

/-- Every parameter of either Sokoban schema has a declared type. -/
theorem params_typed (hp : Pinned d p) {objects : List TypedName}
    (i : Instance d objects) : ∀ pm ∈ i.schema.params, pm.type ∈ d.typeNames := by
  intro pm hpm
  rcases instance_shape hp.domain i with ⟨f, t, dir, hs, -⟩ | ⟨rl, bl, fl, dir, b, hs, -⟩ <;>
    rw [hs] at hpm <;>
    simp only [moveA, pushA, List.mem_cons, List.not_mem_nil, or_false] at hpm
  · rcases hpm with rfl | rfl | rfl
    · exact hp.locationType
    · exact hp.locationType
    · exact hp.directionType
  · rcases hpm with rfl | rfl | rfl | rfl | rfl
    · exact hp.locationType
    · exact hp.locationType
    · exact hp.locationType
    · exact hp.directionType
    · exact hp.boxType

/-- **Every Sokoban operator costs one.** -/
theorem cost_one (hp : Pinned d p) (rel : Bool) :
    ∀ o ∈ groundedOps d p rel, 1 ≤ o.cost := by
  intro o ho
  obtain ⟨hf⟩ := opFacts_ground d p rel ho
  rw [hf.cost]
  show 1 ≤ hf.inst.schema.cost
  rcases instance_shape hp.domain hf.inst with ⟨f, t, dir, hs, -⟩ |
    ⟨rl, bl, fl, dir, b, hs, -⟩ <;> rw [hs] <;> exact Nat.le_refl 1

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

/-! ### Frames -/

/-- An operator that touches no atom of a predicate leaves every such atom. -/
theorem framed_of_pred {o : AtomOp} (hf : OpFacts d p o) {P : Pddl.Name}
    (hadd : ∀ a ∈ hf.inst.add, a.pred ≠ P) (hdel : ∀ a ∈ hf.inst.del, a.pred ≠ P)
    {a : GroundAtom} (ha : a.pred = P) (σ : AtomState) : o.applyA σ a = σ a :=
  applyA_frame σ (fun hm => hadd a (hf.subAdd a hm) ha)
    (fun hm => hdel a (hf.subDel a hm) ha)

/-- And so the facts of that predicate keep their values. -/
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

/-- **`move` touches only `at-robot`.**  `clear` here means "no box stands
here", so walking never changes it. -/
theorem move_touches (i : Instance d objects) {f t dir : Pddl.Name}
    (hs : i.schema = moveA) (ha : i.args = [f, t, dir])
    {a : GroundAtom} (h : a ∈ i.add ∨ a ∈ i.del) : a.pred = "at-robot" := by
  obtain ⟨-, hadd, hdel⟩ := move_atoms i hs ha
  rcases h with h | h
  · rw [hadd] at h
    obtain rfl : a = atRobot t := by simpa using h
    rfl
  · rw [hdel] at h
    obtain rfl : a = atRobot f := by simpa using h
    rfl

/-- **`push` touches the three dynamic families and nothing else.** -/
theorem push_touches (i : Instance d objects) {rl bl fl dir b : Pddl.Name}
    (hs : i.schema = pushA) (ha : i.args = [rl, bl, fl, dir, b])
    {a : GroundAtom} (h : a ∈ i.add ∨ a ∈ i.del) :
    a.pred = "at-robot" ∨ a.pred = "at" ∨ a.pred = "clear" := by
  obtain ⟨-, -, -, hadd, hdel⟩ := push_atoms i hs ha
  rcases h with h | h
  · rw [hadd] at h
    rcases (by simpa using h : a = atRobot bl ∨ a = atBox b fl ∨ a = clearL bl)
      with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rw [hdel] at h
    rcases (by simpa using h : a = atRobot rl ∨ a = atBox b bl ∨ a = clearL fl)
      with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

/-! ### The robot stands in exactly one place

`MoveStep.robotSome` and `PushStep.robotSome` say `robotLoc` reports something at
all, and `robotLoc` reads the *first* true `at-robot` fact — so for it to be the
robot's position there must be exactly one.  Both schemas keep that: each adds
one `at-robot` and deletes the one its precondition names.
-/

/-- The robot stands somewhere, and in one place only. -/
def RobotAt (σ : AtomState) : Prop :=
  (∃ l, σ (atRobot l) = true) ∧
    ∀ l l', σ (atRobot l) = true → σ (atRobot l') = true → l = l'

/--
**A schema that moves the robot from one square to another keeps it.**

Both `move` and `push` have this shape: one `at-robot` added, one deleted, and
the deleted one is a precondition.
-/
theorem robotAt_step {o : AtomOp} (hf : OpFacts d p o) (hd : SokobanDomain d)
    {frm dest : Pddl.Name} {σ : AtomState}
    (hpre : atRobot frm ∈ hf.inst.pre) (hdelmem : atRobot frm ∈ hf.inst.del)
    (hnew : (o.applyA σ) (atRobot dest) = true)
    (haddR : ∀ a ∈ hf.inst.add, a.pred = "at-robot" → a = atRobot dest)
    (happ : o.applicableA σ) (hinv : RobotAt σ) : RobotAt (o.applyA σ) := by
  have hprev : σ (atRobot frm) = true :=
    pre_holds hf hpre (atRobot_dynamic hd) happ
  -- Afterwards the robot is at the destination and nowhere else.
  have key : ∀ x, (o.applyA σ) (atRobot x) = true → x = dest := by
    intro x hx
    by_cases hxt : x = dest
    · exact hxt
    have hnadd : atRobot x ∉ hf.inst.add := fun hm => hxt (by
      simpa using haddR _ hm rfl)
    have hσx : σ (atRobot x) = true := falls_of_lists hf rfl hnadd hx
    have hxf : x = frm := hinv.2 x frm hσx hprev
    subst hxf
    have hdelo : atRobot x ∈ o.del :=
      del_kept hf hdelmem hnadd hpre (atRobot_dynamic hd)
    have hnao : atRobot x ∉ o.add := fun hc => hnadd (hf.subAdd _ hc)
    rw [applyA_del σ hdelo hnao] at hx
    exact absurd hx (by simp)
  exact ⟨⟨dest, hnew⟩, fun l l' h1 h2 => by rw [key l h1, key l' h2]⟩

end Planner.Lifted.Sokoban
