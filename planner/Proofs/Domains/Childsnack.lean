/-
Childsnack's improved heuristic, proved end to end in one file.

The order below is the order the argument is built in.  The first two sections
are the schema-level proof: the improved value over the domain's own data, and
what each schema does to the counters.  The rest lifts that value to the parsed
domain, compiles it against the numbered task, and ends with the four
certificate theorems the registry depends on.

The runtime heuristic, its data, and its certificate stay under `Planner/`.  The
simple heuristic of this domain is proved in
`Proofs/Domains/ChildsnackSimple.lean`.
-/
import Proofs.Combinators
import Proofs.Certificates
import Proofs.SchemaSupport
import Proofs.LiftedHeuristic
import Proofs.StepView
import Proofs.FactTables
import Proofs.CompileSupport
import Proofs.Heuristic
import Planner.ExampleHeuristics.Childsnack.Improved
import Planner.ExampleHeuristics.Childsnack.Domain
import Planner.ExampleHeuristics.Childsnack.Certificate

/- -------------------------------------------------------------------------- -/
/-
Childsnack, improved heuristic: goal-aware, consistent, admissible.

Four families that never share an action — `serve*`, `put_on_tray`, `make*`,
`move_tray` — bounded separately and added.  `Effect` says how one action may
move the four counts.

The delicate case is `serve`, which drops the unserved count *and* takes a
sandwich off a tray, touching two terms at once.  It is safe because the two move
together: serving an allergic child consumes a gluten-free sandwich, so both sides
of `max (nₐ - Aɡ) (n - Aɡ - Aᵣ)` fall by one and the shortfall is unchanged.  The
same cancellation protects the tray moves: serving reduces the waiting children at
a place and the sandwiches standing there by one each, so a place that was
underserved stays underserved and one that was not stays that way.

Serving the *last* child needs its own hypothesis, as it did in spanner.  The
value falls from `1 + S + M + V` to zero, which is within one action only if the
shortfall, the sandwiches to make and the tray moves are all already zero — and
they are, because that child is being served from a tray already standing at their
place, so nothing is owed.

There are no dead ends in this domain.

What is assumed rather than checked: that each grounded operator induces one of
the five effects.  That is a statement about the domain's schemas, and making it a
decidable certificate is the remaining step.
-/

namespace Planner.ExampleHeuristics.Childsnack

open Planner

/-! ### The four quantities -/

abbrev Tc (d : Data) (s : State) : Nat := total d s
abbrev Sc (d : Data) (s : State) : Nat := shortfall d s
abbrev Mc (d : Data) (s : State) : Nat := toMake d s
abbrev Vc (d : Data) (s : State) : Nat := moves d s

/-- How an action may move the four quantities: one constructor per schema family. -/
inductive Effect (d : Data) (s s' : State) : Prop
  | serve (hT : Tc d s' + 1 = Tc d s) (hS : Sc d s ≤ Sc d s') (hM : Mc d s ≤ Mc d s')
      (hV : Vc d s ≤ Vc d s') (hlast : Tc d s' = 0 → Sc d s + Mc d s + Vc d s = 0)
  | putOnTray (hT : Tc d s' = Tc d s) (hS : Sc d s ≤ Sc d s' + 1) (hM : Mc d s ≤ Mc d s')
      (hV : Vc d s ≤ Vc d s')
  | make (hT : Tc d s' = Tc d s) (hS : Sc d s ≤ Sc d s') (hM : Mc d s ≤ Mc d s' + 1)
      (hV : Vc d s ≤ Vc d s')
  | moveTray (hT : Tc d s' = Tc d s) (hS : Sc d s ≤ Sc d s') (hM : Mc d s ≤ Mc d s')
      (hV : Vc d s ≤ Vc d s' + 1)
  | other (hT : Tc d s' = Tc d s) (hS : Sc d s ≤ Sc d s') (hM : Mc d s ≤ Mc d s')
      (hV : Vc d s ≤ Vc d s')

/-! ### The step -/

private theorem step_arith (T S M V T' S' M' V' cost : Nat) (hcost : 1 ≤ cost)
    (h : (T' + 1 = T ∧ S ≤ S' ∧ M ≤ M' ∧ V ≤ V' ∧ (T' = 0 → S + M + V = 0)) ∨
         (T' = T ∧ S ≤ S' + 1 ∧ M ≤ M' ∧ V ≤ V') ∨
         (T' = T ∧ S ≤ S' ∧ M ≤ M' + 1 ∧ V ≤ V') ∨
         (T' = T ∧ S ≤ S' ∧ M ≤ M' ∧ V ≤ V' + 1)) :
    (if T == 0 then 0 else T + S + M + V)
      ≤ cost + (if T' == 0 then 0 else T' + S' + M' + V') := by
  by_cases hz : T = 0
  · simp [hz]
  · rw [if_neg (by simp [hz])]
    by_cases hz' : T' = 0
    · rw [if_pos (by simp [hz'])]
      rcases h with ⟨h1,h2,h3,h4,h5⟩|⟨h1,_,_,_⟩|⟨h1,_,_,_⟩|⟨h1,_,_,_⟩ <;> [skip; omega; omega; omega]
      have := h5 hz'
      omega
    · rw [if_neg (by simp [hz'])]
      rcases h with ⟨h1,h2,h3,h4,_⟩|⟨h1,h2,h3,h4⟩|⟨h1,h2,h3,h4⟩|⟨h1,h2,h3,h4⟩ <;> omega

theorem value_step (d : Data) (s s' : State) (he : Effect d s s')
    (cost : Nat) (hcost : 1 ≤ cost) : value d s ≤ cost + value d s' := by
  show (if Tc d s == 0 then 0 else Tc d s + Sc d s + Mc d s + Vc d s)
      ≤ cost + (if Tc d s' == 0 then 0 else Tc d s' + Sc d s' + Mc d s' + Vc d s')
  refine step_arith _ _ _ _ _ _ _ _ cost hcost ?_
  cases he with
  | serve hT hS hM hV hlast => exact Or.inl ⟨hT, hS, hM, hV, hlast⟩
  | putOnTray hT hS hM hV => exact Or.inr (Or.inl ⟨hT, hS, hM, hV⟩)
  | make hT hS hM hV => exact Or.inr (Or.inr (Or.inl ⟨hT, hS, hM, hV⟩))
  | moveTray hT hS hM hV => exact Or.inr (Or.inr (Or.inr ⟨hT, hS, hM, hV⟩))
  | other hT hS hM hV => exact Or.inr (Or.inr (Or.inr ⟨hT, hS, hM, by omega⟩))

/-! ### Assembly -/

theorem unservedChildren_empty (d : Data) (s : State)
    (hall : ∀ c ∈ d.children, s.test c.goalFact = true) : unservedChildren d s = #[] := by
  unfold unservedChildren
  rw [Array.filter_eq_empty_iff]
  intro x hx
  simp [hall x hx]

theorem value_eq_zero_of_goal (d : Data) (s : State)
    (hall : ∀ c ∈ d.children, s.test c.goalFact = true) : value d s = 0 := by
  unfold value total
  rw [unservedChildren_empty d s hall]
  rfl

theorem improved_goalAware (t : Task)
    (hcompiled : ∀ c ∈ (compile t).children, c.goalFact ∈ t.goal) :
    t.GoalAware (improved t).eval := by
  refine t.goalAware_of _ fun s _ hgoal => ?_
  exact value_eq_zero_of_goal _ s fun c hc => hgoal _ (hcompiled c hc)

theorem improved_consistent (t : Task)
    (heff : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      Effect (compile t) s (op.apply s))
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost) :
    t.Consistent (improved t).eval :=
  t.consistent_of_ops _ fun op hop s hs happ =>
    value_step _ s _ (heff op hop s hs happ) op.cost (hcost op hop)

/-- Never overestimates the cost of reaching the goal. -/
theorem improved_admissible (t : Task)
    (hcompiled : ∀ c ∈ (compile t).children, c.goalFact ∈ t.goal)
    (heff : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      Effect (compile t) s (op.apply s))
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost) :
    t.Admissible (improved t).eval :=
  t.admissible _ (improved_goalAware t hcompiled) (improved_consistent t heff hcost)


/-! ### Discharging the goal-count component from the operator

`Effect`'s hypotheses are statements about states, but the goal count follows from
facts about the operator alone — which of the family's goals it adds, which it
deletes — and those are decidable.  These two lemmas make that step, so a
certificate can establish it rather than a hypothesis assuming it.
-/

/-- `serve` achieves exactly one outstanding goal, so one fewer remains. -/
theorem goalCount_drop_one (d : Data) {n : Nat} {op : Op} {s : State}
    (hop : Op.WF n op) (hs : State.WF n s) (hnd : (d.children).toList.Nodup)
    (x : _) (hx : x ∈ d.children)
    (hxadd : op.add.contains ((·.goalFact) x) = true) (hxs : s.test ((·.goalFact) x) = false)
    (hother : ∀ y ∈ d.children, y ≠ x → op.add.contains ((·.goalFact) y) = false)
    (hdel : ∀ y ∈ d.children, op.del.contains ((·.goalFact) y) = false) :
    ((d.children).filter fun y => !(op.apply s).test ((·.goalFact) y)).size + 1
      = ((d.children).filter fun y => !s.test ((·.goalFact) y)).size :=
  unmet_drop_one d.children (·.goalFact) hop hs hnd x hx hxadd hxs hother hdel

/-- Any operator touching none of the unserved children leaves the count alone. -/
theorem goalCount_unchanged (d : Data) {n : Nat} {op : Op} {s : State}
    (hop : Op.WF n op) (hs : State.WF n s)
    (hadd : ∀ y ∈ d.children, op.add.contains ((·.goalFact) y) = false)
    (hdel : ∀ y ∈ d.children, op.del.contains ((·.goalFact) y) = false) :
    ((d.children).filter fun y => !(op.apply s).test ((·.goalFact) y)).size
      = ((d.children).filter fun y => !s.test ((·.goalFact) y)).size :=
  unmet_unchanged d.children (·.goalFact) hop hs hadd hdel

end Planner.ExampleHeuristics.Childsnack

/- -------------------------------------------------------------------------- -/
/-
Childsnack, stated at the schema level.

`Effect` in `Improved.lean` assumes how one action moves the four counters.  This
file assumes only what the domain's schemas do to the predicates the heuristic
reads — which children are served, which sandwiches are gluten-free and where they
are, how many sandwiches stand at each place, whether a tray is in the kitchen —
and derives the counters.

The `serve` case carries the last-child condition, which is the one `PLAN.md`
records as glossed over in the informal argument.  It is derived here from three
facts about the action: the sandwich served was on a tray, an allergic child is
served a gluten-free one, and the tray was standing where the child waits.
-/

namespace Planner.ExampleHeuristics.Childsnack

open Planner

/-! ### The base quantities as filters -/

def liveC (s : State) (c : ChildInfo) : Bool := !s.test c.goalFact

theorem total_eq (d : Data) (s : State) :
    total d s = (d.children.toList.filter (liveC s)).length := by
  unfold total unservedChildren liveC
  rw [size_filter_toList]

theorem allergic_eq (d : Data) (s : State) :
    allergicLeft d s = (d.children.toList.filter fun c => c.allergic && liveC s c).length := by
  unfold allergicLeft unservedChildren liveC
  rw [size_filter_toList, Array.toList_filter, List.filter_filter]

theorem waiting_eq (d : Data) (s : State) (p : Nat) :
    waitingAt d s p = (d.children.toList.filter fun c => c.place == some p && liveC s c).length := by
  unfold waitingAt unservedChildren liveC
  rw [size_filter_toList, Array.toList_filter, List.filter_filter]

theorem trayAny_eq (d : Data) (s : State) :
    trayAny d s = (d.sandwiches.toList.filter fun sw => onTray s sw).length := by
  unfold trayAny
  rw [size_filter_toList]

theorem trayFree_eq (d : Data) (s : State) :
    trayFree d s = (d.sandwiches.toList.filter fun sw => onTray s sw && isFree s sw).length := by
  unfold trayFree
  rw [size_filter_toList]

theorem kitchenAny_eq (d : Data) (s : State) :
    kitchenAny d s = (d.sandwiches.toList.filter fun sw => inKitchen s sw).length := by
  unfold kitchenAny
  rw [size_filter_toList]

theorem kitchenFree_eq (d : Data) (s : State) :
    kitchenFree d s
      = (d.sandwiches.toList.filter fun sw => inKitchen s sw && isFree s sw).length := by
  unfold kitchenFree
  rw [size_filter_toList]

theorem waitingAt_le_total (d : Data) (s : State) (p : Nat) :
    waitingAt d s p ≤ total d s := by
  rw [waiting_eq, total_eq]
  refine filter_size_le' _ _ _ ?_
  intro c _ hc
  simp only [Bool.and_eq_true] at hc
  exact hc.2

/-! ### What each schema does -/

/-- `serve_sandwich` and `serve_sandwich_no_gluten`. -/
structure ServeStep (d : Data) (s s' : State) (c : ChildInfo) (sw : SandwichInfo) (p : Nat) :
    Prop where
  memC : c ∈ d.children
  memSw : sw ∈ d.sandwiches
  childUnserved : s.test c.goalFact = false
  childServed' : s'.test c.goalFact = true
  childOther : ∀ x ∈ d.children, x ≠ c → s'.test x.goalFact = s.test x.goalFact
  childPlace : c.place = some p
  swOnTray : onTray s sw = true
  swOffTray' : onTray s' sw = false
  swOther : ∀ y ∈ d.sandwiches, y ≠ sw → onTray s' y = onTray s y
  freeSame : ∀ y ∈ d.sandwiches, isFree s' y = isFree s y
  kitchenSame : ∀ y ∈ d.sandwiches, inKitchen s' y = inKitchen s y
  /-- An allergic child is served a gluten-free sandwich. -/
  allergicFree : c.allergic = true → isFree s sw = true
  /-- The tray was standing where the child waits. -/
  loadedHere : loadedAt d s' p + 1 = loadedAt d s p
  loadedOther : ∀ q, q ≠ p → loadedAt d s' q = loadedAt d s q
  trayKitchenSame : trayInKitchen d s' = trayInKitchen d s

/-- `make_sandwich` and `make_sandwich_no_gluten`: one sandwich appears in the kitchen. -/
structure MakeStep (d : Data) (s s' : State) (sw : SandwichInfo) : Prop where
  memSw : sw ∈ d.sandwiches
  childSame : ∀ x ∈ d.children, s'.test x.goalFact = s.test x.goalFact
  trayS : ∀ y ∈ d.sandwiches, onTray s' y = onTray s y
  freeSame : ∀ y ∈ d.sandwiches, isFree s' y = isFree s y
  kitchenBefore : inKitchen s sw = false
  kitchenAfter : inKitchen s' sw = true
  kitchenOther : ∀ y ∈ d.sandwiches, y ≠ sw → inKitchen s' y = inKitchen s y
  loadedSame : ∀ q, loadedAt d s' q = loadedAt d s q
  trayKitchenSame : trayInKitchen d s' = trayInKitchen d s

/-- `put_on_tray`: one sandwich leaves the kitchen for a tray standing there. -/
structure PutOnTrayStep (d : Data) (s s' : State) (sw : SandwichInfo) : Prop where
  memSw : sw ∈ d.sandwiches
  childSame : ∀ x ∈ d.children, s'.test x.goalFact = s.test x.goalFact
  trayBefore : onTray s sw = false
  trayAfter : onTray s' sw = true
  trayOther : ∀ y ∈ d.sandwiches, y ≠ sw → onTray s' y = onTray s y
  freeSame : ∀ y ∈ d.sandwiches, isFree s' y = isFree s y
  kitchenBefore : inKitchen s sw = true
  kitchenAfter : inKitchen s' sw = false
  kitchenOther : ∀ y ∈ d.sandwiches, y ≠ sw → inKitchen s' y = inKitchen s y
  /-- Loading happens at the kitchen, which is never a place to move a tray to. -/
  loadedOff : ∀ q, d.kitchen ≠ some q → loadedAt d s' q = loadedAt d s q
  /-- The tray it was loaded onto was standing in the kitchen. -/
  trayInKitchenBefore : trayInKitchen d s = true

/-- `move_tray`: a tray leaves one place for another; nothing else changes. -/
structure MoveTrayStep (d : Data) (s s' : State) (dest : Nat) : Prop where
  childSame : ∀ x ∈ d.children, s'.test x.goalFact = s.test x.goalFact
  trayS : ∀ y ∈ d.sandwiches, onTray s' y = onTray s y
  freeSame : ∀ y ∈ d.sandwiches, isFree s' y = isFree s y
  kitchenS : ∀ y ∈ d.sandwiches, inKitchen s' y = inKitchen s y
  /-- Only the place the tray arrives at gains sandwiches. -/
  loadedDown : ∀ q, q ≠ dest → loadedAt d s' q ≤ loadedAt d s q
  /-- Either the tray arrives at the kitchen, which is never a target, or it does
  not put a tray into the kitchen that was not there before. -/
  kitchenOrFlag : d.kitchen = some dest ∨
    (trayInKitchen d s = false → trayInKitchen d s' = false)

/-- One action of the domain. -/
inductive SchemaStep (d : Data) (s s' : State) : Prop
  | serve (c : ChildInfo) (sw : SandwichInfo) (p : Nat) (h : ServeStep d s s' c sw p)
  | make (sw : SandwichInfo) (h : MakeStep d s s' sw)
  | putOnTray (sw : SandwichInfo) (h : PutOnTrayStep d s s' sw)
  | moveTray (dest : Nat) (h : MoveTrayStep d s s' dest)

/-! ### The counters, derived from the shapes -/

namespace ServeStep
variable {d : Data} {s s' : State} {c : ChildInfo} {sw : SandwichInfo} {p : Nat}

theorem total_drop (h : ServeStep d s s' c sw p) (hnd : d.children.toList.Nodup) :
    total d s' + 1 = total d s := by
  rw [total_eq, total_eq]
  refine length_filter_erase_one _ (liveC s) (liveC s') c (by simpa using h.memC) hnd
    (by simp [liveC, h.childUnserved]) (by simp [liveC, h.childServed']) ?_
  intro y hy hne
  simp [liveC, h.childOther y (by simpa using hy) hne]

theorem allergic_drop (h : ServeStep d s s' c sw p) (hnd : d.children.toList.Nodup)
    (hal : c.allergic = true) : allergicLeft d s' + 1 = allergicLeft d s := by
  rw [allergic_eq, allergic_eq]
  refine length_filter_erase_one _ _ _ c (by simpa using h.memC) hnd
    (by simp [liveC, hal, h.childUnserved]) (by simp [liveC, h.childServed']) ?_
  intro y hy hne
  simp [liveC, h.childOther y (by simpa using hy) hne]

theorem allergic_same (h : ServeStep d s s' c sw p) (hal : c.allergic = false) :
    allergicLeft d s' = allergicLeft d s := by
  rw [allergic_eq, allergic_eq]
  refine length_filter_congr _ _ _ ?_
  intro y hy
  by_cases hne : y = c
  · subst hne; simp [hal]
  · simp [liveC, h.childOther y (by simpa using hy) hne]

theorem trayAny_drop (h : ServeStep d s s' c sw p) (hnd : d.sandwiches.toList.Nodup) :
    trayAny d s' + 1 = trayAny d s := by
  rw [trayAny_eq, trayAny_eq]
  refine length_filter_erase_one _ _ _ sw (by simpa using h.memSw) hnd
    (by simp [h.swOnTray]) (by simp [h.swOffTray']) ?_
  intro y hy hne
  simp [h.swOther y (by simpa using hy) hne]

theorem trayFree_drop (h : ServeStep d s s' c sw p) (hnd : d.sandwiches.toList.Nodup)
    (hfree : isFree s sw = true) : trayFree d s' + 1 = trayFree d s := by
  rw [trayFree_eq, trayFree_eq]
  refine length_filter_erase_one _ _ _ sw (by simpa using h.memSw) hnd
    (by simp [h.swOnTray, hfree]) (by simp [h.swOffTray']) ?_
  intro y hy hne
  have hm : y ∈ d.sandwiches := by simpa using hy
  simp [h.swOther y hm hne, h.freeSame y hm]

theorem trayFree_same (h : ServeStep d s s' c sw p) (hfree : isFree s sw = false) :
    trayFree d s' = trayFree d s := by
  rw [trayFree_eq, trayFree_eq]
  refine length_filter_congr _ _ _ ?_
  intro y hy
  have hm : y ∈ d.sandwiches := by simpa using hy
  by_cases hne : y = sw
  · subst hne; simp [h.freeSame y hm, hfree]
  · simp [h.swOther y hm hne, h.freeSame y hm]

theorem kitchen_same (h : ServeStep d s s' c sw p) :
    kitchenAny d s' = kitchenAny d s ∧ kitchenFree d s' = kitchenFree d s := by
  constructor
  · rw [kitchenAny_eq, kitchenAny_eq]
    exact length_filter_congr _ _ _ fun y hy => by
      rw [h.kitchenSame y (by simpa using hy)]
  · rw [kitchenFree_eq, kitchenFree_eq]
    refine length_filter_congr _ _ _ ?_
    intro y hy
    have hm : y ∈ d.sandwiches := by simpa using hy
    rw [h.kitchenSame y hm, h.freeSame y hm]

theorem waiting_here (h : ServeStep d s s' c sw p) (hnd : d.children.toList.Nodup) :
    waitingAt d s' p + 1 = waitingAt d s p := by
  rw [waiting_eq, waiting_eq]
  refine length_filter_erase_one _ _ _ c (by simpa using h.memC) hnd
    (by simp [liveC, h.childPlace, h.childUnserved]) (by simp [liveC, h.childServed']) ?_
  intro y hy hne
  simp [liveC, h.childOther y (by simpa using hy) hne]

theorem waiting_other (h : ServeStep d s s' c sw p) {q : Nat} (hq : q ≠ p) :
    waitingAt d s' q = waitingAt d s q := by
  rw [waiting_eq, waiting_eq]
  refine length_filter_congr _ _ _ ?_
  intro y hy
  by_cases hne : y = c
  · subst hne
    have hpq : (p == q) = false := by simp [Ne.symm hq]
    simp [h.childPlace, hpq]
  · simp [liveC, h.childOther y (by simpa using hy) hne]

theorem moveTargets_eq (h : ServeStep d s s' c sw p) (hnd : d.children.toList.Nodup) :
    moveTargets d s' = moveTargets d s := by
  unfold moveTargets
  refine List.filter_congr ?_
  intro q _
  by_cases hq : q = p
  · subst hq
    have h1 := h.loadedHere
    have h2 := h.waiting_here hnd
    by_cases hlt : loadedAt d s q < waitingAt d s q
    · simp [hlt, show loadedAt d s' q < waitingAt d s' q by omega]
    · simp [hlt, show ¬ loadedAt d s' q < waitingAt d s' q by omega]
  · rw [h.loadedOther q hq, h.waiting_other hq]

end ServeStep

theorem allergic_le_total (d : Data) (s : State) : allergicLeft d s ≤ total d s := by
  rw [allergic_eq, total_eq]
  refine filter_size_le' _ _ _ ?_
  intro c _ hc
  simp only [Bool.and_eq_true] at hc
  exact hc.2

theorem moveTargets_nil (d : Data) (s : State) (h : total d s = 0) :
    moveTargets d s = [] := by
  unfold moveTargets
  refine List.filter_eq_nil_iff.mpr ?_
  intro q _ hq
  have hle := waitingAt_le_total d s q
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
  omega

namespace ServeStep
variable {d : Data} {s s' : State} {c : ChildInfo} {sw : SandwichInfo} {p : Nat}

theorem Sc_le (h : ServeStep d s s' c sw p) (hndC : d.children.toList.Nodup)
    (hndS : d.sandwiches.toList.Nodup) : Sc d s ≤ Sc d s' := by
  show shortfall d s ≤ shortfall d s'
  unfold shortfall
  have hT := h.total_drop hndC
  have hTA := h.trayAny_drop hndS
  by_cases hal : c.allergic
  · have hA := h.allergic_drop hndC hal
    have hTF := h.trayFree_drop hndS (h.allergicFree hal)
    omega
  · have hA := h.allergic_same (by simpa using hal)
    by_cases hf : isFree s sw
    · have hTF := h.trayFree_drop hndS hf
      omega
    · have hTF := h.trayFree_same (by simpa using hf)
      omega

theorem Mc_le (h : ServeStep d s s' c sw p) (hndC : d.children.toList.Nodup)
    (hndS : d.sandwiches.toList.Nodup) : Mc d s ≤ Mc d s' := by
  show toMake d s ≤ toMake d s'
  unfold toMake shortfall
  obtain ⟨hKA, hKF⟩ := h.kitchen_same
  have hT := h.total_drop hndC
  have hTA := h.trayAny_drop hndS
  by_cases hal : c.allergic
  · have hA := h.allergic_drop hndC hal
    have hTF := h.trayFree_drop hndS (h.allergicFree hal)
    omega
  · have hA := h.allergic_same (by simpa using hal)
    by_cases hf : isFree s sw
    · have hTF := h.trayFree_drop hndS hf
      omega
    · have hTF := h.trayFree_same (by simpa using hf)
      omega

theorem Vc_le (h : ServeStep d s s' c sw p) (hndC : d.children.toList.Nodup)
    (hndS : d.sandwiches.toList.Nodup) : Vc d s ≤ Vc d s' := by
  show moves d s ≤ moves d s'
  unfold moves
  rw [h.moveTargets_eq hndC, h.trayKitchenSame]
  have hS : shortfall d s ≤ shortfall d s' := h.Sc_le hndC hndS
  by_cases hk : trayInKitchen d s
  · simp [hk]
  · by_cases h0 : 0 < shortfall d s
    · have h0' : 0 < shortfall d s' := by omega
      simp [hk, h0, h0']
    · simp [h0]

theorem last (h : ServeStep d s s' c sw p) (hndC : d.children.toList.Nodup)
    (hndS : d.sandwiches.toList.Nodup) :
    Tc d s' = 0 → Sc d s + Mc d s + Vc d s = 0 := by
  intro hz
  have hT := h.total_drop hndC
  have hTA := h.trayAny_drop hndS
  have hAle' := allergic_le_total d s'
  have hzs : total d s' = 0 := hz
  have hSc : shortfall d s = 0 := by
    unfold shortfall
    by_cases hal : c.allergic
    · have hA := h.allergic_drop hndC hal
      have hTF := h.trayFree_drop hndS (h.allergicFree hal)
      omega
    · have hA := h.allergic_same (by simpa using hal)
      omega
  have hMc : toMake d s = 0 := by
    unfold toMake
    rw [hSc]
    by_cases hal : c.allergic
    · have hA := h.allergic_drop hndC hal
      have hTF := h.trayFree_drop hndS (h.allergicFree hal)
      omega
    · have hA := h.allergic_same (by simpa using hal)
      omega
  have hVc : moves d s = 0 := by
    unfold moves
    have hmt : moveTargets d s = [] := by
      rw [← h.moveTargets_eq hndC]
      exact moveTargets_nil d s' hzs
    rw [hmt]
    simp [hSc]
  show shortfall d s + toMake d s + moves d s = 0
  rw [hSc, hMc, hVc]

end ServeStep

/-! ### Congruences used by the schemas that touch only one family -/

theorem total_congr {d : Data} {s s' : State}
    (h : ∀ x ∈ d.children, s'.test x.goalFact = s.test x.goalFact) :
    total d s' = total d s := by
  rw [total_eq, total_eq]
  exact length_filter_congr _ _ _ fun y hy => by simp [liveC, h y (by simpa using hy)]

theorem allergic_congr {d : Data} {s s' : State}
    (h : ∀ x ∈ d.children, s'.test x.goalFact = s.test x.goalFact) :
    allergicLeft d s' = allergicLeft d s := by
  rw [allergic_eq, allergic_eq]
  exact length_filter_congr _ _ _ fun y hy => by simp [liveC, h y (by simpa using hy)]

theorem waiting_congr {d : Data} {s s' : State}
    (h : ∀ x ∈ d.children, s'.test x.goalFact = s.test x.goalFact) (q : Nat) :
    waitingAt d s' q = waitingAt d s q := by
  rw [waiting_eq, waiting_eq]
  exact length_filter_congr _ _ _ fun y hy => by simp [liveC, h y (by simpa using hy)]

theorem trayAny_congr {d : Data} {s s' : State}
    (h : ∀ y ∈ d.sandwiches, onTray s' y = onTray s y) : trayAny d s' = trayAny d s := by
  rw [trayAny_eq, trayAny_eq]
  exact length_filter_congr _ _ _ fun y hy => by rw [h y (by simpa using hy)]

theorem trayFree_congr {d : Data} {s s' : State}
    (h : ∀ y ∈ d.sandwiches, onTray s' y = onTray s y)
    (hf : ∀ y ∈ d.sandwiches, isFree s' y = isFree s y) : trayFree d s' = trayFree d s := by
  rw [trayFree_eq, trayFree_eq]
  refine length_filter_congr _ _ _ fun y hy => ?_
  have hm : y ∈ d.sandwiches := by simpa using hy
  rw [h y hm, hf y hm]

theorem kitchenAny_congr {d : Data} {s s' : State}
    (h : ∀ y ∈ d.sandwiches, inKitchen s' y = inKitchen s y) :
    kitchenAny d s' = kitchenAny d s := by
  rw [kitchenAny_eq, kitchenAny_eq]
  exact length_filter_congr _ _ _ fun y hy => by rw [h y (by simpa using hy)]

theorem kitchenFree_congr {d : Data} {s s' : State}
    (h : ∀ y ∈ d.sandwiches, inKitchen s' y = inKitchen s y)
    (hf : ∀ y ∈ d.sandwiches, isFree s' y = isFree s y) :
    kitchenFree d s' = kitchenFree d s := by
  rw [kitchenFree_eq, kitchenFree_eq]
  refine length_filter_congr _ _ _ fun y hy => ?_
  have hm : y ∈ d.sandwiches := by simpa using hy
  rw [h y hm, hf y hm]

theorem moveTargets_congr {d : Data} {s s' : State}
    (hw : ∀ q, waitingAt d s' q = waitingAt d s q)
    (hl : ∀ q, loadedAt d s' q = loadedAt d s q) : moveTargets d s' = moveTargets d s := by
  unfold moveTargets
  exact List.filter_congr fun q _ => by rw [hw, hl]

namespace MakeStep
variable {d : Data} {s s' : State} {sw : SandwichInfo}

theorem kitchenAny_gain (h : MakeStep d s s' sw) (hnd : d.sandwiches.toList.Nodup) :
    kitchenAny d s + 1 = kitchenAny d s' := by
  rw [kitchenAny_eq, kitchenAny_eq]
  refine length_filter_erase_one _ _ _ sw (by simpa using h.memSw) hnd
    (by simp [h.kitchenAfter]) (by simp [h.kitchenBefore]) ?_
  intro y hy hne
  rw [h.kitchenOther y (by simpa using hy) hne]

theorem kitchenFree_bound (h : MakeStep d s s' sw) (hnd : d.sandwiches.toList.Nodup) :
    kitchenFree d s ≤ kitchenFree d s' ∧ kitchenFree d s' ≤ kitchenFree d s + 1 := by
  rw [kitchenFree_eq, kitchenFree_eq]
  by_cases hf : isFree s sw
  · have hf' : isFree s' sw = true := by rw [h.freeSame sw h.memSw]; exact hf
    have := length_filter_erase_one d.sandwiches.toList
      (fun y => inKitchen s' y && isFree s' y) (fun y => inKitchen s y && isFree s y) sw
      (by simpa using h.memSw) hnd (by simp [h.kitchenAfter, hf'])
      (by simp [h.kitchenBefore]) ?_
    · omega
    · intro y hy hne
      have hm : y ∈ d.sandwiches := by simpa using hy
      simp only [h.kitchenOther y hm hne, h.freeSame y hm]
  · have hf' : isFree s' sw = false := by rw [h.freeSame sw h.memSw]; simpa using hf
    have : (d.sandwiches.toList.filter fun y => inKitchen s' y && isFree s' y).length
        = (d.sandwiches.toList.filter fun y => inKitchen s y && isFree s y).length := by
      refine length_filter_congr _ _ _ ?_
      intro y hy
      have hm : y ∈ d.sandwiches := by simpa using hy
      by_cases hne : y = sw
      · subst hne; simp [hf, hf']
      · rw [h.kitchenOther y hm hne, h.freeSame y hm]
    omega

theorem Effect_fields (h : MakeStep d s s' sw) (hnd : d.sandwiches.toList.Nodup) :
    Tc d s' = Tc d s ∧ Sc d s ≤ Sc d s' ∧ Mc d s ≤ Mc d s' + 1 ∧ Vc d s ≤ Vc d s' := by
  have hT : total d s' = total d s := total_congr h.childSame
  have hA : allergicLeft d s' = allergicLeft d s := allergic_congr h.childSame
  have hTA : trayAny d s' = trayAny d s := trayAny_congr h.trayS
  have hTF : trayFree d s' = trayFree d s := trayFree_congr h.trayS h.freeSame
  have hKA := h.kitchenAny_gain hnd
  obtain ⟨hKF1, hKF2⟩ := h.kitchenFree_bound hnd
  have hSc : shortfall d s' = shortfall d s := by unfold shortfall; rw [hA, hTF, hT, hTA]
  refine ⟨hT, ?_, ?_, ?_⟩
  · show shortfall d s ≤ shortfall d s'
    omega
  · show toMake d s ≤ toMake d s' + 1
    unfold toMake
    rw [hSc, hA, hTF]
    omega
  · show moves d s ≤ moves d s'
    unfold moves
    rw [moveTargets_congr (waiting_congr h.childSame) h.loadedSame, h.trayKitchenSame, hSc]

end MakeStep

namespace PutOnTrayStep
variable {d : Data} {s s' : State} {sw : SandwichInfo}

theorem trayAny_gain (h : PutOnTrayStep d s s' sw) (hnd : d.sandwiches.toList.Nodup) :
    trayAny d s + 1 = trayAny d s' := by
  rw [trayAny_eq, trayAny_eq]
  refine length_filter_erase_one _ _ _ sw (by simpa using h.memSw) hnd
    (by simp [h.trayAfter]) (by simp [h.trayBefore]) ?_
  intro y hy hne
  simp only [h.trayOther y (by simpa using hy) hne]

theorem kitchenAny_drop (h : PutOnTrayStep d s s' sw) (hnd : d.sandwiches.toList.Nodup) :
    kitchenAny d s' + 1 = kitchenAny d s := by
  rw [kitchenAny_eq, kitchenAny_eq]
  refine length_filter_erase_one _ _ _ sw (by simpa using h.memSw) hnd
    (by simp [h.kitchenBefore]) (by simp [h.kitchenAfter]) ?_
  intro y hy hne
  simp only [h.kitchenOther y (by simpa using hy) hne]

theorem free_gain (h : PutOnTrayStep d s s' sw) (hnd : d.sandwiches.toList.Nodup)
    (hf : isFree s sw = true) :
    trayFree d s + 1 = trayFree d s' ∧ kitchenFree d s' + 1 = kitchenFree d s := by
  have hf' : isFree s' sw = true := by rw [h.freeSame sw h.memSw]; exact hf
  constructor
  · rw [trayFree_eq, trayFree_eq]
    refine length_filter_erase_one _ _ _ sw (by simpa using h.memSw) hnd
      (by simp [h.trayAfter, hf']) (by simp [h.trayBefore]) ?_
    intro y hy hne
    have hm : y ∈ d.sandwiches := by simpa using hy
    simp only [h.trayOther y hm hne, h.freeSame y hm]
  · rw [kitchenFree_eq, kitchenFree_eq]
    refine length_filter_erase_one _ _ _ sw (by simpa using h.memSw) hnd
      (by simp [h.kitchenBefore, hf]) (by simp [h.kitchenAfter]) ?_
    intro y hy hne
    have hm : y ∈ d.sandwiches := by simpa using hy
    simp only [h.kitchenOther y hm hne, h.freeSame y hm]

theorem free_same (h : PutOnTrayStep d s s' sw) (hf : isFree s sw = false) :
    trayFree d s' = trayFree d s ∧ kitchenFree d s' = kitchenFree d s := by
  have hf' : isFree s' sw = false := by rw [h.freeSame sw h.memSw]; exact hf
  constructor
  · rw [trayFree_eq, trayFree_eq]
    refine length_filter_congr _ _ _ ?_
    intro y hy
    have hm : y ∈ d.sandwiches := by simpa using hy
    by_cases hne : y = sw
    · subst hne; simp [hf, hf']
    · simp only [h.trayOther y hm hne, h.freeSame y hm]
  · rw [kitchenFree_eq, kitchenFree_eq]
    refine length_filter_congr _ _ _ ?_
    intro y hy
    have hm : y ∈ d.sandwiches := by simpa using hy
    by_cases hne : y = sw
    · subst hne; simp [hf, hf']
    · simp only [h.kitchenOther y hm hne, h.freeSame y hm]

theorem moveTargets_eq (h : PutOnTrayStep d s s' sw) :
    moveTargets d s' = moveTargets d s := by
  unfold moveTargets
  refine List.filter_congr ?_
  intro q _
  by_cases hk : d.kitchen = some q
  · simp [hk]
  · rw [h.loadedOff q hk, waiting_congr h.childSame q]

theorem Effect_fields (h : PutOnTrayStep d s s' sw) (hnd : d.sandwiches.toList.Nodup) :
    Tc d s' = Tc d s ∧ Sc d s ≤ Sc d s' + 1 ∧ Mc d s ≤ Mc d s' ∧ Vc d s ≤ Vc d s' := by
  have hT : total d s' = total d s := total_congr h.childSame
  have hA : allergicLeft d s' = allergicLeft d s := allergic_congr h.childSame
  have hTA := h.trayAny_gain hnd
  have hKA := h.kitchenAny_drop hnd
  refine ⟨hT, ?_, ?_, ?_⟩
  · show shortfall d s ≤ shortfall d s' + 1
    unfold shortfall
    rw [hA, hT]
    by_cases hf : isFree s sw
    · obtain ⟨h1, -⟩ := h.free_gain hnd hf; omega
    · obtain ⟨h1, -⟩ := h.free_same (by simpa using hf); omega
  · show toMake d s ≤ toMake d s'
    unfold toMake shortfall
    rw [hA, hT]
    by_cases hf : isFree s sw
    · obtain ⟨h1, h2⟩ := h.free_gain hnd hf; omega
    · obtain ⟨h1, h2⟩ := h.free_same (by simpa using hf); omega
  · show moves d s ≤ moves d s'
    unfold moves
    rw [h.moveTargets_eq]
    simp [h.trayInKitchenBefore]

end PutOnTrayStep

namespace MoveTrayStep
variable {d : Data} {s s' : State} {dest : Nat}

theorem base_same (h : MoveTrayStep d s s' dest) :
    shortfall d s' = shortfall d s ∧ toMake d s' = toMake d s := by
  have hT : total d s' = total d s := total_congr h.childSame
  have hA : allergicLeft d s' = allergicLeft d s := allergic_congr h.childSame
  have hTA : trayAny d s' = trayAny d s := trayAny_congr h.trayS
  have hTF : trayFree d s' = trayFree d s := trayFree_congr h.trayS h.freeSame
  have hKA : kitchenAny d s' = kitchenAny d s := kitchenAny_congr h.kitchenS
  have hKF : kitchenFree d s' = kitchenFree d s := kitchenFree_congr h.kitchenS h.freeSame
  have hSc : shortfall d s' = shortfall d s := by unfold shortfall; rw [hA, hTF, hT, hTA]
  exact ⟨hSc, by unfold toMake; rw [hSc, hA, hTF, hKF, hKA]⟩

theorem mt_le (h : MoveTrayStep d s s' dest) :
    (moveTargets d s).length ≤ (moveTargets d s').length + 1 := by
  unfold moveTargets
  refine length_le_succ_of_subset _ _ dest ((List.nodup_range).filter _) ?_
  intro q hq
  by_cases hqd : q = dest
  · exact Or.inr hqd
  · refine Or.inl ?_
    rw [List.mem_filter] at hq ⊢
    obtain ⟨hqm, hqp⟩ := hq
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hqp ⊢
    have hload := h.loadedDown q hqd
    have hw := waiting_congr h.childSame q
    exact ⟨hqm, hqp.1, by omega⟩

theorem Effect_fields (h : MoveTrayStep d s s' dest) :
    Tc d s' = Tc d s ∧ Sc d s ≤ Sc d s' ∧ Mc d s ≤ Mc d s' ∧ Vc d s ≤ Vc d s' + 1 := by
  obtain ⟨hSc, hMc⟩ := h.base_same
  refine ⟨total_congr h.childSame, by show shortfall d s ≤ shortfall d s'; omega,
    by show toMake d s ≤ toMake d s'; omega, ?_⟩
  show moves d s ≤ moves d s' + 1
  unfold moves
  have hmt := h.mt_le
  rcases h.kitchenOrFlag with hk | hflag
  · have hsub : (moveTargets d s).length ≤ (moveTargets d s').length := by
      unfold moveTargets
      refine length_le_of_subset _ _ ((List.nodup_range).filter _) ?_
      intro q hq
      rw [List.mem_filter] at hq ⊢
      obtain ⟨hqm, hqp⟩ := hq
      simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hqp ⊢
      have hqd : q ≠ dest := by rintro rfl; exact hqp.1 hk
      have hload := h.loadedDown q hqd
      have hw := waiting_congr h.childSame q
      exact ⟨hqm, hqp.1, by omega⟩
    have : (if decide (0 < shortfall d s) && !trayInKitchen d s then 1 else 0) ≤ 1 := by
      split <;> omega
    omega
  · have hf : (if decide (0 < shortfall d s) && !trayInKitchen d s then 1 else 0)
        ≤ (if decide (0 < shortfall d s') && !trayInKitchen d s' then 1 else 0) := by
      by_cases hk : trayInKitchen d s
      · simp [hk]
      · have hk' : trayInKitchen d s' = false := hflag (by simpa using hk)
        rw [hSc] at *
        by_cases h0 : 0 < shortfall d s
        · simp [hk, hk', h0, hSc]
        · simp [h0]
    omega

end MoveTrayStep

/-! ### The consistency step, with nothing about the counters assumed -/

theorem effect_of_schema (d : Data) (s s' : State)
    (hndC : d.children.toList.Nodup) (hndS : d.sandwiches.toList.Nodup)
    (he : SchemaStep d s s') : Effect d s s' := by
  cases he with
  | serve c sw p h =>
      exact .serve (h.total_drop hndC) (h.Sc_le hndC hndS) (h.Mc_le hndC hndS)
        (h.Vc_le hndC hndS) (h.last hndC hndS)
  | make sw h =>
      obtain ⟨h1, h2, h3, h4⟩ := h.Effect_fields hndS
      exact .make h1 h2 h3 h4
  | putOnTray sw h =>
      obtain ⟨h1, h2, h3, h4⟩ := h.Effect_fields hndS
      exact .putOnTray h1 h2 h3 h4
  | moveTray dest h =>
      obtain ⟨h1, h2, h3, h4⟩ := h.Effect_fields
      exact .moveTray h1 h2 h3 h4

/-- Zero at every goal state, assuming only what the schemas do. -/
theorem improved_goalAware_of_schema (t : Task)
    (hcompiled : ∀ c ∈ (compile t).children, c.goalFact ∈ t.goal) :
    t.GoalAware (improved t).eval := improved_goalAware t hcompiled

/-- And never falls by more than one action costs. -/
theorem improved_consistent_of_schema (t : Task)
    (hndC : (compile t).children.toList.Nodup)
    (hndS : (compile t).sandwiches.toList.Nodup)
    (hstep : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      SchemaStep (compile t) s (op.apply s))
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost) :
    t.Consistent (improved t).eval :=
  improved_consistent t
    (fun op hop s hs happ => effect_of_schema _ s _ hndC hndS (hstep op hop s hs happ))
    hcost

/-- Never overestimates, assuming only that every operator is one of the schemas. -/
theorem improved_admissible_of_schema (t : Task)
    (hcompiled : ∀ c ∈ (compile t).children, c.goalFact ∈ t.goal)
    (hndC : (compile t).children.toList.Nodup)
    (hndS : (compile t).sandwiches.toList.Nodup)
    (hstep : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      SchemaStep (compile t) s (op.apply s))
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost) :
    t.Admissible (improved t).eval :=
  t.admissible _ (improved_goalAware_of_schema t hcompiled)
    (improved_consistent_of_schema t hndC hndS hstep hcost)

end Planner.ExampleHeuristics.Childsnack

/- -------------------------------------------------------------------------- -/
/-
Childsnack's improved heuristic, at the lifted level.

Four families of actions that never share an action — `serve*`, `put_on_tray`,
`make*`, `move_tray` — counted separately and added.  Nothing here mentions a
`Fact` or a `State`.
-/

namespace Planner.Lifted.Childsnack

open Planner Planner.Pddl

/-! ### The domain's atoms -/

def served (k : Name) : GroundAtom := { pred := "served", args := [k] }
def ontray (sw t : Name) : GroundAtom := { pred := "ontray", args := [sw, t] }
def kitchenSw (sw : Name) : GroundAtom :=
  { pred := "at_kitchen_sandwich", args := [sw] }
def glutenFree (sw : Name) : GroundAtom :=
  { pred := "no_gluten_sandwich", args := [sw] }
def atT (t p : Name) : GroundAtom := { pred := "at", args := [t, p] }
def notexist (sw : Name) : GroundAtom := { pred := "notexist", args := [sw] }

/-- What the problem fixes.  `allergic` and `waitingAt` read static predicates, so
they are read once. -/
structure Cfg where
  children : List Name
  sandwiches : List Name
  trays : List Name
  places : List Name
  allergic : Name → Bool
  waitingAt : Name → Option Name
  kitchen : Option Name

/-! ### Reading the state -/

def unserved (c : Cfg) (σ : AtomState) : List Name :=
  c.children.filter fun k => !σ (served k)

def total (c : Cfg) (σ : AtomState) : Nat := (unserved c σ).length

def allergicLeft (c : Cfg) (σ : AtomState) : Nat :=
  ((unserved c σ).filter fun k => c.allergic k).length

/-- How many unserved children wait at `p`. -/
def waitingAtP (c : Cfg) (σ : AtomState) (p : Name) : Nat :=
  ((unserved c σ).filter fun k => c.waitingAt k == some p).length

def onTray (c : Cfg) (σ : AtomState) (sw : Name) : Bool :=
  c.trays.any fun t => σ (ontray sw t)

def isFree (σ : AtomState) (sw : Name) : Bool := σ (glutenFree sw)

def inKitchen (c : Cfg) (σ : AtomState) (sw : Name) : Bool :=
  !onTray c σ sw && σ (kitchenSw sw)

def trayAny (c : Cfg) (σ : AtomState) : Nat :=
  (c.sandwiches.filter fun sw => onTray c σ sw).length
def trayFree (c : Cfg) (σ : AtomState) : Nat :=
  (c.sandwiches.filter fun sw => onTray c σ sw && isFree σ sw).length
def kitchenAny (c : Cfg) (σ : AtomState) : Nat :=
  (c.sandwiches.filter fun sw => inKitchen c σ sw).length
def kitchenFree (c : Cfg) (σ : AtomState) : Nat :=
  (c.sandwiches.filter fun sw => inKitchen c σ sw && isFree σ sw).length

/-- Sandwiches still to be loaded, matching gluten-free ones to allergic children
first. -/
def shortfall (c : Cfg) (σ : AtomState) : Nat :=
  max (allergicLeft c σ - trayFree c σ) (total c σ - trayAny c σ)

/-- The same shortfall measured against the kitchen instead of the trays. -/
def toMake (c : Cfg) (σ : AtomState) : Nat :=
  max ((allergicLeft c σ - trayFree c σ) - kitchenFree c σ)
    (shortfall c σ - kitchenAny c σ)

/-- Where a tray stands. -/
def trayPlace (c : Cfg) (σ : AtomState) (t : Name) : Option Name :=
  c.places.find? fun p => σ (atT t p)

/-- How many sandwiches sit on one tray. -/
def trayLoad (c : Cfg) (σ : AtomState) (t : Name) : Nat :=
  (c.sandwiches.filter fun sw => σ (ontray sw t)).length

/-- How many sandwiches sit on the trays standing at `p`. -/
def loadedAt (c : Cfg) (σ : AtomState) (p : Name) : Nat :=
  ((c.trays.filter fun t => trayPlace c σ t == some p).map (trayLoad c σ)).sum

def trayInKitchen (c : Cfg) (σ : AtomState) : Bool :=
  c.trays.any fun t => trayPlace c σ t == c.kitchen

/-- Places whose waiting children outnumber the sandwiches standing there. -/
def moveTargets (c : Cfg) (σ : AtomState) : List Name :=
  c.places.filter fun p =>
    c.kitchen != some p && decide (loadedAt c σ p < waitingAtP c σ p)

/-- Tray moves: one per underserved place, and one to bring a tray to the kitchen. -/
def moves (c : Cfg) (σ : AtomState) : Nat :=
  (moveTargets c σ).length +
    (if decide (0 < shortfall c σ) && !trayInKitchen c σ then 1 else 0)

/-- Four families that never share an action, bounded separately and added. -/
def value (c : Cfg) (σ : AtomState) : Nat :=
  if total c σ == 0 then 0
  else total c σ + shortfall c σ + toMake c σ + moves c σ

/-! ### Goal awareness -/

theorem value_eq_zero (c : Cfg) (σ : AtomState)
    (h : ∀ k ∈ c.children, σ (served k) = true) : value c σ = 0 := by
  have hu : unserved c σ = [] := by
    refine List.filter_eq_nil_iff.mpr ?_
    intro k hk
    simp [h k hk]
  unfold value total
  rw [hu]
  simp

/-- Zero once every goal child is served. -/
theorem liftedGoalAware (c : Cfg) (p : Problem)
    (hsub : ∀ k ∈ c.children, served k ∈ p.goal) :
    LiftedGoalAware p (value c) := by
  intro σ hgoal
  refine value_eq_zero c σ fun k hk => ?_
  exact hgoal (served k) (by simpa using hsub k hk)

end Planner.Lifted.Childsnack

/- -------------------------------------------------------------------------- -/
/-
Which domain a childsnack task came from.

One decidable check on the schema list, and the atoms each of the six schemas
produces.
-/

namespace Planner.Lifted.Childsnack

open Planner Planner.Pddl

/-! ### More of the domain's atoms -/

def kitchenBread (b : Name) : GroundAtom := { pred := "at_kitchen_bread", args := [b] }
def kitchenContent (x : Name) : GroundAtom :=
  { pred := "at_kitchen_content", args := [x] }

/-- The static atoms the heuristic reads. -/
def allergicAtom (k : Name) : GroundAtom := { pred := "allergic_gluten", args := [k] }
def notAllergicAtom (k : Name) : GroundAtom :=
  { pred := "not_allergic_gluten", args := [k] }
def waitingAtom (k q : Name) : GroundAtom := { pred := "waiting", args := [k, q] }

/-- Childsnack, together with the three static predicates the heuristic reads.
Each is one decidable check on the task. -/
structure ChildsnackPinned (d : Domain) : Prop where
  actions : ChildsnackDomain d
  allergicStatic : (staticPredicates d).contains "allergic_gluten" = true
  notAllergicStatic : (staticPredicates d).contains "not_allergic_gluten" = true
  waitingStatic : (staticPredicates d).contains "waiting" = true

/-! ### Which predicates the schemas touch -/

theorem served_dynamic {d : Domain} (hd : ChildsnackDomain d) :
    (staticPredicates d).contains "served" = false :=
  not_static_of_mem_add (a := serveA) (by rw [hd]; simp) (y := servedV "?c")
    (by simp [serveA])

theorem ontray_dynamic {d : Domain} (hd : ChildsnackDomain d) :
    (staticPredicates d).contains "ontray" = false :=
  not_static_of_mem_del (a := serveA) (by rw [hd]; simp) (y := ontrayV "?s" "?t")
    (by simp [serveA])

theorem kitchenSw_dynamic {d : Domain} (hd : ChildsnackDomain d) :
    (staticPredicates d).contains "at_kitchen_sandwich" = false :=
  not_static_of_mem_del (a := putA) (by rw [hd]; simp) (y := kitchenSwV "?s")
    (by simp [putA])

theorem glutenFree_dynamic {d : Domain} (hd : ChildsnackDomain d) :
    (staticPredicates d).contains "no_gluten_sandwich" = false :=
  not_static_of_mem_add (a := makeNGA) (by rw [hd]; simp) (y := glutenFreeV "?s")
    (by simp [makeNGA])

theorem at_dynamic {d : Domain} (hd : ChildsnackDomain d) :
    (staticPredicates d).contains "at" = false :=
  not_static_of_mem_del (a := moveA) (by rw [hd]; simp) (y := atV "?t" "?p1")
    (by simp [moveA])

theorem notexist_dynamic {d : Domain} (hd : ChildsnackDomain d) :
    (staticPredicates d).contains "notexist" = false :=
  not_static_of_mem_del (a := makeA) (by rw [hd]; simp) (y := notexistV "?s")
    (by simp [makeA])

/-! ### What an instance of it looks like -/

theorem instance_shape {d : Domain} {objects : List TypedName} (hd : ChildsnackDomain d)
    (i : Instance d objects) :
    (∃ sw b x, i.schema = makeNGA ∧ i.args = [sw, b, x]) ∨
    (∃ sw b x, i.schema = makeA ∧ i.args = [sw, b, x]) ∨
    (∃ sw t, i.schema = putA ∧ i.args = [sw, t] ∧ WellTyped d objects "tray" t) ∨
    (∃ sw k t p, i.schema = serveNGA ∧ i.args = [sw, k, t, p] ∧
      WellTyped d objects "child" k ∧ WellTyped d objects "tray" t ∧
      WellTyped d objects "place" p ∧ WellTyped d objects "sandwich" sw) ∨
    (∃ sw k t p, i.schema = serveA ∧ i.args = [sw, k, t, p] ∧
      WellTyped d objects "child" k ∧ WellTyped d objects "tray" t ∧
      WellTyped d objects "place" p ∧ WellTyped d objects "sandwich" sw) ∨
    (∃ t p1 p2, i.schema = moveA ∧ i.args = [t, p1, p2] ∧
      WellTyped d objects "tray" t ∧ WellTyped d objects "place" p1 ∧
      WellTyped d objects "place" p2) := by
  have hmem : i.schema ∈ [makeNGA, makeA, putA, serveNGA, serveA, moveA] := hd ▸ i.mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h
  · obtain ⟨a, b, x, hargs, -, -, -⟩ := i.args_three (by rw [h])
    exact Or.inl ⟨a, b, x, h, hargs⟩
  · obtain ⟨a, b, x, hargs, -, -, -⟩ := i.args_three (by rw [h])
    exact Or.inr (Or.inl ⟨a, b, x, h, hargs⟩)
  · obtain ⟨a, t, hargs, -, h2⟩ := i.args_two (by rw [h])
    exact Or.inr (Or.inr (Or.inl ⟨a, t, h, hargs, by simpa [trP] using h2⟩))
  · obtain ⟨a, k, t, p, hargs, h1, h2, h3, h4⟩ := i.args_four (by rw [h])
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, k, t, p, h, hargs,
      by simpa [chP] using h2, by simpa [trP] using h3, by simpa [plP] using h4,
      by simpa [swP] using h1⟩)))
  · obtain ⟨a, k, t, p, hargs, h1, h2, h3, h4⟩ := i.args_four (by rw [h])
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, k, t, p, h, hargs,
      by simpa [chP] using h2, by simpa [trP] using h3, by simpa [plP] using h4,
      by simpa [swP] using h1⟩))))
  · obtain ⟨t, p1, p2, hargs, h1, h2, h3⟩ := i.args_three (by rw [h])
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨t, p1, p2, h, hargs,
      by simpa [trP] using h1, by simpa [plP] using h2, by simpa [plP] using h3⟩))))

/-! ### The atoms of each shape, computed -/

theorem makeNG_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {sw b x : Name} (hs : i.schema = makeNGA) (ha : i.args = [sw, b, x]) :
    i.add = [kitchenSw sw, glutenFree sw] ∧
    i.del = [kitchenBread b, kitchenContent x, notexist sw] := by
  constructor
  · rw [Pddl.Instance.add_eq, hs, ha]; rfl
  · rw [Pddl.Instance.del_eq, hs, ha]; rfl

theorem make_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {sw b x : Name} (hs : i.schema = makeA) (ha : i.args = [sw, b, x]) :
    i.add = [kitchenSw sw] ∧
    i.del = [kitchenBread b, kitchenContent x, notexist sw] := by
  constructor
  · rw [Pddl.Instance.add_eq, hs, ha]; rfl
  · rw [Pddl.Instance.del_eq, hs, ha]; rfl

theorem put_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {sw t : Name} (hs : i.schema = putA) (ha : i.args = [sw, t]) :
    kitchenSwV "?s" ∈ i.schema.pre ∧
    instAtom i.schema.params i.args (kitchenSwV "?s") = kitchenSw sw ∧
    atKitchenV "?t" ∈ i.schema.pre ∧
    instAtom i.schema.params i.args (atKitchenV "?t") = atT t "kitchen" ∧
    kitchenSwV "?s" ∈ i.schema.del ∧
    i.add = [ontray sw t] ∧ i.del = [kitchenSw sw] := by
  refine ⟨by rw [hs]; simp [putA], by rw [hs, ha]; rfl,
    by rw [hs]; simp [putA], by rw [hs, ha]; rfl,
    by rw [hs]; simp [putA], ?_, ?_⟩
  · rw [Pddl.Instance.add_eq, hs, ha]; rfl
  · rw [Pddl.Instance.del_eq, hs, ha]; rfl

theorem serveNG_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {sw k t p : Name} (hs : i.schema = serveNGA) (ha : i.args = [sw, k, t, p]) :
    ontrayV "?s" "?t" ∈ i.schema.pre ∧
    instAtom i.schema.params i.args (ontrayV "?s" "?t") = ontray sw t ∧
    atV "?t" "?p" ∈ i.schema.pre ∧
    instAtom i.schema.params i.args (atV "?t" "?p") = atT t p ∧
    glutenFreeV "?s" ∈ i.schema.pre ∧
    instAtom i.schema.params i.args (glutenFreeV "?s") = glutenFree sw ∧
    ontrayV "?s" "?t" ∈ i.schema.del ∧
    i.add = [served k] ∧ i.del = [ontray sw t] := by
  refine ⟨by rw [hs]; simp [serveNGA], by rw [hs, ha]; rfl,
    by rw [hs]; simp [serveNGA], by rw [hs, ha]; rfl,
    by rw [hs]; simp [serveNGA], by rw [hs, ha]; rfl,
    by rw [hs]; simp [serveNGA], ?_, ?_⟩
  · rw [Pddl.Instance.add_eq, hs, ha]; rfl
  · rw [Pddl.Instance.del_eq, hs, ha]; rfl

theorem serve_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {sw k t p : Name} (hs : i.schema = serveA) (ha : i.args = [sw, k, t, p]) :
    ontrayV "?s" "?t" ∈ i.schema.pre ∧
    instAtom i.schema.params i.args (ontrayV "?s" "?t") = ontray sw t ∧
    atV "?t" "?p" ∈ i.schema.pre ∧
    instAtom i.schema.params i.args (atV "?t" "?p") = atT t p ∧
    ontrayV "?s" "?t" ∈ i.schema.del ∧
    i.add = [served k] ∧ i.del = [ontray sw t] := by
  refine ⟨by rw [hs]; simp [serveA], by rw [hs, ha]; rfl,
    by rw [hs]; simp [serveA], by rw [hs, ha]; rfl,
    by rw [hs]; simp [serveA], ?_, ?_⟩
  · rw [Pddl.Instance.add_eq, hs, ha]; rfl
  · rw [Pddl.Instance.del_eq, hs, ha]; rfl

theorem move_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {t p1 p2 : Name} (hs : i.schema = moveA) (ha : i.args = [t, p1, p2]) :
    atV "?t" "?p1" ∈ i.schema.pre ∧
    instAtom i.schema.params i.args (atV "?t" "?p1") = atT t p1 ∧
    atV "?t" "?p1" ∈ i.schema.del ∧
    i.add = [atT t p2] ∧ i.del = [atT t p1] := by
  refine ⟨by rw [hs]; simp [moveA], by rw [hs, ha]; rfl,
    by rw [hs]; simp [moveA], ?_, ?_⟩
  · rw [Pddl.Instance.add_eq, hs, ha]; rfl
  · rw [Pddl.Instance.del_eq, hs, ha]; rfl

end Planner.Lifted.Childsnack

/- -------------------------------------------------------------------------- -/
/-
Childsnack's improved heuristic: the invariant it needs, and its preservation.

Each tray stands at one place; a sandwich that does not exist yet is nowhere and
is not gluten-free; and a sandwich in the kitchen is on no tray.  All four are
true of `:init` and survive every action.
-/

namespace Planner.Lifted.Childsnack

open Planner Planner.Pddl

structure Inv (σ : AtomState) : Prop where
  oneAt : ∀ t p q, σ (atT t p) = true → σ (atT t q) = true → p = q
  freshTray : ∀ sw t, σ (notexist sw) = true → σ (ontray sw t) = false
  freshKitchen : ∀ sw, σ (notexist sw) = true → σ (kitchenSw sw) = false
  freshGluten : ∀ sw, σ (notexist sw) = true → σ (glutenFree sw) = false
  kitchenNotTray : ∀ sw t, σ (kitchenSw sw) = true → σ (ontray sw t) = false
  oneTray : ∀ sw t u, σ (ontray sw t) = true → σ (ontray sw u) = true → t = u

/-! ### Atoms of different predicates are different -/

@[simp] theorem atT_ne_served (t p k : Name) : atT t p ≠ served k := by simp [atT, served]
@[simp] theorem atT_ne_ontray (t p sw u : Name) : atT t p ≠ ontray sw u := by
  simp [atT, ontray]
@[simp] theorem atT_ne_kitchenSw (t p sw : Name) : atT t p ≠ kitchenSw sw := by
  simp [atT, kitchenSw]
@[simp] theorem atT_ne_glutenFree (t p sw : Name) : atT t p ≠ glutenFree sw := by
  simp [atT, glutenFree]
@[simp] theorem atT_ne_notexist (t p sw : Name) : atT t p ≠ notexist sw := by
  simp [atT, notexist]
@[simp] theorem atT_ne_bread (t p b : Name) : atT t p ≠ kitchenBread b := by
  simp [atT, kitchenBread]
@[simp] theorem atT_ne_content (t p x : Name) : atT t p ≠ kitchenContent x := by
  simp [atT, kitchenContent]

@[simp] theorem ontray_ne_served (sw t k : Name) : ontray sw t ≠ served k := by
  simp [ontray, served]
@[simp] theorem ontray_ne_atT (sw t u p : Name) : ontray sw t ≠ atT u p := by
  simp [ontray, atT]
@[simp] theorem ontray_ne_kitchenSw (sw t u : Name) : ontray sw t ≠ kitchenSw u := by
  simp [ontray, kitchenSw]
@[simp] theorem ontray_ne_glutenFree (sw t u : Name) : ontray sw t ≠ glutenFree u := by
  simp [ontray, glutenFree]
@[simp] theorem ontray_ne_notexist (sw t u : Name) : ontray sw t ≠ notexist u := by
  simp [ontray, notexist]
@[simp] theorem ontray_ne_bread (sw t b : Name) : ontray sw t ≠ kitchenBread b := by
  simp [ontray, kitchenBread]
@[simp] theorem ontray_ne_content (sw t x : Name) : ontray sw t ≠ kitchenContent x := by
  simp [ontray, kitchenContent]

@[simp] theorem served_ne_ontray (k sw t : Name) : served k ≠ ontray sw t := by
  simp [served, ontray]
@[simp] theorem served_ne_atT (k t p : Name) : served k ≠ atT t p := by simp [served, atT]
@[simp] theorem served_ne_kitchenSw (k sw : Name) : served k ≠ kitchenSw sw := by
  simp [served, kitchenSw]
@[simp] theorem served_ne_glutenFree (k sw : Name) : served k ≠ glutenFree sw := by
  simp [served, glutenFree]
@[simp] theorem served_ne_notexist (k sw : Name) : served k ≠ notexist sw := by
  simp [served, notexist]
@[simp] theorem served_ne_bread (k b : Name) : served k ≠ kitchenBread b := by
  simp [served, kitchenBread]
@[simp] theorem served_ne_content (k x : Name) : served k ≠ kitchenContent x := by
  simp [served, kitchenContent]

@[simp] theorem kitchenSw_ne_ontray (sw u t : Name) : kitchenSw sw ≠ ontray u t := by
  simp [kitchenSw, ontray]
@[simp] theorem kitchenSw_ne_atT (sw t p : Name) : kitchenSw sw ≠ atT t p := by
  simp [kitchenSw, atT]
@[simp] theorem kitchenSw_ne_served (sw k : Name) : kitchenSw sw ≠ served k := by
  simp [kitchenSw, served]
@[simp] theorem kitchenSw_ne_glutenFree (sw u : Name) : kitchenSw sw ≠ glutenFree u := by
  simp [kitchenSw, glutenFree]
@[simp] theorem kitchenSw_ne_notexist (sw u : Name) : kitchenSw sw ≠ notexist u := by
  simp [kitchenSw, notexist]
@[simp] theorem kitchenSw_ne_bread (sw b : Name) : kitchenSw sw ≠ kitchenBread b := by
  simp [kitchenSw, kitchenBread]
@[simp] theorem kitchenSw_ne_content (sw x : Name) : kitchenSw sw ≠ kitchenContent x := by
  simp [kitchenSw, kitchenContent]

@[simp] theorem glutenFree_ne_ontray (sw u t : Name) : glutenFree sw ≠ ontray u t := by
  simp [glutenFree, ontray]
@[simp] theorem glutenFree_ne_atT (sw t p : Name) : glutenFree sw ≠ atT t p := by
  simp [glutenFree, atT]
@[simp] theorem glutenFree_ne_served (sw k : Name) : glutenFree sw ≠ served k := by
  simp [glutenFree, served]
@[simp] theorem glutenFree_ne_kitchenSw (sw u : Name) : glutenFree sw ≠ kitchenSw u := by
  simp [glutenFree, kitchenSw]
@[simp] theorem glutenFree_ne_notexist (sw u : Name) : glutenFree sw ≠ notexist u := by
  simp [glutenFree, notexist]
@[simp] theorem glutenFree_ne_bread (sw b : Name) : glutenFree sw ≠ kitchenBread b := by
  simp [glutenFree, kitchenBread]
@[simp] theorem glutenFree_ne_content (sw x : Name) : glutenFree sw ≠ kitchenContent x := by
  simp [glutenFree, kitchenContent]

@[simp] theorem glutenFree_inj (u v : Name) : glutenFree u = glutenFree v ↔ u = v := by
  simp [glutenFree]
@[simp] theorem kitchenSw_inj (u v : Name) : kitchenSw u = kitchenSw v ↔ u = v := by
  simp [kitchenSw]

@[simp] theorem notexist_ne_ontray (sw u t : Name) : notexist sw ≠ ontray u t := by
  simp [notexist, ontray]
@[simp] theorem notexist_ne_served (sw k : Name) : notexist sw ≠ served k := by
  simp [notexist, served]
@[simp] theorem notexist_ne_atT (sw t q : Name) : notexist sw ≠ atT t q := by
  simp [notexist, atT]
@[simp] theorem notexist_ne_bread (sw b : Name) : notexist sw ≠ kitchenBread b := by
  simp [notexist, kitchenBread]
@[simp] theorem notexist_ne_content (sw x : Name) : notexist sw ≠ kitchenContent x := by
  simp [notexist, kitchenContent]
@[simp] theorem notexist_ne_kitchenSw (sw u : Name) : notexist sw ≠ kitchenSw u := by
  simp [notexist, kitchenSw]
@[simp] theorem notexist_ne_glutenFree (sw u : Name) : notexist sw ≠ glutenFree u := by
  simp [notexist, glutenFree]

/-! ### Frames -/

private theorem framed {d : Domain} {objects : List TypedName} {o : AtomOp}
    {i : Instance d objects} {a : GroundAtom}
    (hadd : ∀ b ∈ o.add, b ∈ i.add) (hdel : ∀ b ∈ o.del, b ∈ i.del)
    (hna : a ∉ i.add) (hnd : a ∉ i.del) (σ : AtomState) : o.applyA σ a = σ a :=
  applyA_frame σ (fun h => hna (hadd a h)) (fun h => hnd (hdel a h))

/-- An atom the operator cannot add never becomes true. -/
private theorem falls {d : Domain} {objects : List TypedName} {o : AtomOp}
    {i : Instance d objects} {a : GroundAtom}
    (hadd : ∀ b ∈ o.add, b ∈ i.add) (hna : a ∉ i.add)
    {σ : AtomState} (h : o.applyA σ a = true) : σ a = true := by
  have hno : a ∉ o.add := fun hm => hna (hadd a hm)
  by_cases hd : a ∈ o.del
  · rw [applyA_del σ hd hno] at h; exact absurd h (by simp)
  · rwa [applyA_frame σ hno hd] at h

/-! ### Making a sandwich -/

private theorem make_case {d : Domain} {p : Problem} {o : AtomOp} (hf : OpFacts d p o)
    {σ : AtomState} (hinv : Inv σ) {sw b x : Name}
    (hia : ∀ a ∈ hf.inst.add, a = kitchenSw sw ∨ a = glutenFree sw)
    (hid : hf.inst.del = [kitchenBread b, kitchenContent x, notexist sw])
    (hne : σ (notexist sw) = true) (hneF : (o.applyA σ) (notexist sw) = false) :
    Inv (o.applyA σ) := by
  have hA := hf.subAdd
  have hD := hf.subDel
  have hnaT : ∀ u q, atT u q ∉ hf.inst.add := by
    intro u q hm; rcases hia _ hm with h | h <;> simp [atT, kitchenSw, glutenFree] at h
  have hnaO : ∀ u q, ontray u q ∉ hf.inst.add := by
    intro u q hm; rcases hia _ hm with h | h <;> simp [ontray, kitchenSw, glutenFree] at h
  have hnaN : ∀ u, notexist u ∉ hf.inst.add := by
    intro u hm; rcases hia _ hm with h | h <;> simp [notexist, kitchenSw, glutenFree] at h
  have hnaK : ∀ u, u ≠ sw → kitchenSw u ∉ hf.inst.add := by
    intro u hu hm
    rcases hia _ hm with h | h
    · exact hu (by simpa [kitchenSw] using h)
    · simp [kitchenSw, glutenFree] at h
  have hnaG : ∀ u, u ≠ sw → glutenFree u ∉ hf.inst.add := by
    intro u hu hm
    rcases hia _ hm with h | h
    · simp [glutenFree, kitchenSw] at h
    · exact hu (by simpa [glutenFree] using h)
  have hfrO : ∀ u q, (o.applyA σ) (ontray u q) = σ (ontray u q) := fun u q =>
    framed hA hD (hnaO u q) (by rw [hid]; simp) σ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u q r h1 h2
    rw [framed hA hD (hnaT u q) (by rw [hid]; simp) σ] at h1
    rw [framed hA hD (hnaT u r) (by rw [hid]; simp) σ] at h2
    exact hinv.oneAt u q r h1 h2
  · intro u q h1
    rw [hfrO u q]
    exact hinv.freshTray u q (falls hA (hnaN u) h1)
  · intro u h1
    by_cases hu : u = sw
    · subst hu; rw [hneF] at h1; exact absurd h1 (by simp)
    · rw [framed hA hD (hnaK u hu) (by rw [hid]; simp) σ]
      exact hinv.freshKitchen u (falls hA (hnaN u) h1)
  · intro u h1
    by_cases hu : u = sw
    · subst hu; rw [hneF] at h1; exact absurd h1 (by simp)
    · rw [framed hA hD (hnaG u hu) (by rw [hid]; simp) σ]
      exact hinv.freshGluten u (falls hA (hnaN u) h1)
  · intro u q h1
    rw [hfrO u q]
    by_cases hu : u = sw
    · subst hu; exact hinv.freshTray u q hne
    · rw [framed hA hD (hnaK u hu) (by rw [hid]; simp) σ] at h1
      exact hinv.kitchenNotTray u q h1
  · intro u q r h1 h2
    rw [hfrO u q] at h1
    rw [hfrO u r] at h2
    exact hinv.oneTray u q r h1 h2

/-! ### Serving a sandwich -/

private theorem serve_case {d : Domain} {p : Problem} {o : AtomOp} (hf : OpFacts d p o)
    {σ : AtomState} (hinv : Inv σ) {k sw t : Name}
    (hia : hf.inst.add = [served k]) (hid : hf.inst.del = [ontray sw t]) :
    Inv (o.applyA σ) := by
  have hA := hf.subAdd
  have hD := hf.subDel
  have hOfalls : ∀ u q, (o.applyA σ) (ontray u q) = true → σ (ontray u q) = true :=
    fun u q h => falls hA (by rw [hia]; simp) h
  have hfrN : ∀ u, (o.applyA σ) (notexist u) = σ (notexist u) := fun u =>
    framed hA hD (by rw [hia]; simp) (by rw [hid]; simp) σ
  have hfrK : ∀ u, (o.applyA σ) (kitchenSw u) = σ (kitchenSw u) := fun u =>
    framed hA hD (by rw [hia]; simp) (by rw [hid]; simp) σ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u q r h1 h2
    rw [framed hA hD (by rw [hia]; simp) (by rw [hid]; simp) σ] at h1
    rw [framed hA hD (by rw [hia]; simp) (by rw [hid]; simp) σ] at h2
    exact hinv.oneAt u q r h1 h2
  · intro u q h1
    rw [hfrN u] at h1
    by_contra hc
    exact absurd (hinv.freshTray u q h1) (by rw [hOfalls u q (by simpa using hc)]; simp)
  · intro u h1
    rw [hfrN u] at h1
    rw [hfrK u]
    exact hinv.freshKitchen u h1
  · intro u h1
    rw [hfrN u] at h1
    rw [framed hA hD (by rw [hia]; simp) (by rw [hid]; simp) σ]
    exact hinv.freshGluten u h1
  · intro u q h1
    rw [hfrK u] at h1
    by_contra hc
    exact absurd (hinv.kitchenNotTray u q h1)
      (by rw [hOfalls u q (by simpa using hc)]; simp)
  · intro u q r h1 h2
    exact hinv.oneTray u q r (hOfalls u q h1) (hOfalls u r h2)

/-! ### The invariant survives every action -/

theorem inv_preserved {d : Domain} {p : Problem} (hd : ChildsnackDomain d)
    {o : AtomOp} (hf : OpFacts d p o) {σ : AtomState} (hinv : Inv σ)
    (happ : o.applicableA σ) : Inv (o.applyA σ) := by
  have hA := hf.subAdd
  have hD := hf.subDel
  rcases instance_shape hd hf.inst with
    ⟨sw, b, x, hs, ha⟩ | ⟨sw, b, x, hs, ha⟩ | ⟨sw, t, hs, ha, -⟩ |
    ⟨sw, k, t, pl, hs, ha, -, -, -, -⟩ | ⟨sw, k, t, pl, hs, ha, -, -, -, -⟩ |
    ⟨t, p1, p2, hs, ha, -, -, -⟩
  · -- make_sandwich_no_gluten
    obtain ⟨hia, hid⟩ := makeNG_atoms hf.inst hs ha
    have hneS : notexistV "?s" ∈ hf.inst.schema.pre := by rw [hs]; simp [makeNGA]
    have hneD : notexistV "?s" ∈ hf.inst.schema.del := by rw [hs]; simp [makeNGA]
    have hneI : instAtom hf.inst.schema.params hf.inst.args (notexistV "?s")
        = notexist sw := by rw [hs, ha]; rfl
    have hpre : notexist sw ∈ o.pre := by
      have := hf.preComplete (notexistV "?s") hneS (notexist_dynamic hd)
      rwa [hneI] at this
    have hne : σ (notexist sw) = true := happ _ hpre
    have hdel : notexist sw ∈ o.del := by
      have := hf.delComplete (notexistV "?s") hneD (by rw [hneI, hia]; simp)
        (by rw [hneI]; exact hpre)
      rwa [hneI] at this
    exact make_case hf hinv (fun a hm => by rw [hia] at hm; simpa using hm) hid hne
      (applyA_del σ hdel (fun hm => by
        have := hA _ hm; rw [hia] at this; simp at this))
  · -- make_sandwich
    obtain ⟨hia, hid⟩ := make_atoms hf.inst hs ha
    have hneS : notexistV "?s" ∈ hf.inst.schema.pre := by rw [hs]; simp [makeA]
    have hneD : notexistV "?s" ∈ hf.inst.schema.del := by rw [hs]; simp [makeA]
    have hneI : instAtom hf.inst.schema.params hf.inst.args (notexistV "?s")
        = notexist sw := by rw [hs, ha]; rfl
    have hpre : notexist sw ∈ o.pre := by
      have := hf.preComplete (notexistV "?s") hneS (notexist_dynamic hd)
      rwa [hneI] at this
    have hne : σ (notexist sw) = true := happ _ hpre
    have hdel : notexist sw ∈ o.del := by
      have := hf.delComplete (notexistV "?s") hneD (by rw [hneI, hia]; simp)
        (by rw [hneI]; exact hpre)
      rwa [hneI] at this
    exact make_case hf hinv
      (fun a hm => by rw [hia] at hm; exact Or.inl (by simpa using hm)) hid hne
      (applyA_del σ hdel (fun hm => by
        have := hA _ hm; rw [hia] at this; simp at this))
  · -- put_on_tray
    obtain ⟨hkS, hkI, -, -, hkD, hia, hid⟩ := put_atoms hf.inst hs ha
    have hpre : kitchenSw sw ∈ o.pre := by
      have := hf.preComplete (kitchenSwV "?s") hkS (kitchenSw_dynamic hd)
      rwa [hkI] at this
    have hk : σ (kitchenSw sw) = true := happ _ hpre
    have hkdel : kitchenSw sw ∈ o.del := by
      have := hf.delComplete (kitchenSwV "?s") hkD (by rw [hkI, hia]; simp)
        (by rw [hkI]; exact hpre)
      rwa [hkI] at this
    have hkF : (o.applyA σ) (kitchenSw sw) = false :=
      applyA_del σ hkdel (fun hm => by have := hA _ hm; rw [hia] at this; simp at this)
    have hfrO : ∀ u q, ¬(u = sw ∧ q = t) →
        (o.applyA σ) (ontray u q) = σ (ontray u q) := by
      intro u q hne
      refine framed hA hD ?_ (by rw [hid]; simp) σ
      rw [hia]
      simp only [List.mem_singleton, ontray, GroundAtom.mk.injEq, true_and,
        List.cons.injEq, and_true]
      rintro ⟨rfl, rfl⟩; exact hne ⟨rfl, rfl⟩
    have hfrN : ∀ u, (o.applyA σ) (notexist u) = σ (notexist u) := fun u =>
      framed hA hD (by rw [hia]; simp) (by rw [hid]; simp) σ
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro u q r h1 h2
      rw [framed hA hD (by rw [hia]; simp) (by rw [hid]; simp) σ] at h1
      rw [framed hA hD (by rw [hia]; simp) (by rw [hid]; simp) σ] at h2
      exact hinv.oneAt u q r h1 h2
    · intro u q h1
      rw [hfrN u] at h1
      by_cases hu : u = sw ∧ q = t
      · obtain ⟨rfl, rfl⟩ := hu
        rw [hinv.freshKitchen u h1] at hk; exact absurd hk (by simp)
      · rw [hfrO u q hu]; exact hinv.freshTray u q h1
    · intro u h1
      rw [hfrN u] at h1
      by_cases hu : u = sw
      · subst hu; exact hkF
      · rw [framed hA hD (by rw [hia]; simp) (by rw [hid]; simp [kitchenSw, hu]) σ]
        exact hinv.freshKitchen u h1
    · intro u h1
      rw [hfrN u] at h1
      rw [framed hA hD (by rw [hia]; simp) (by rw [hid]; simp) σ]
      exact hinv.freshGluten u h1
    · intro u q h1
      have hu : u ≠ sw := by rintro rfl; rw [hkF] at h1; exact Bool.noConfusion h1
      rw [framed hA hD (by rw [hia]; simp) (by rw [hid]; simp [kitchenSw, hu]) σ] at h1
      rw [hfrO u q (by rintro ⟨rfl, -⟩; exact hu rfl)]
      exact hinv.kitchenNotTray u q h1
    · intro u q r h1 h2
      have hkey : ∀ z, (o.applyA σ) (ontray u z) = true → u = sw → z = t := by
        intro z hz husw
        by_cases hzt : z = t
        · exact hzt
        · subst husw
          rw [hfrO u z (by rintro ⟨-, rfl⟩; exact hzt rfl)] at hz
          rw [hinv.kitchenNotTray u z hk] at hz
          exact absurd hz (by simp)
      by_cases husw : u = sw
      · rw [hkey q h1 husw, hkey r h2 husw]
      · rw [hfrO u q (by rintro ⟨rfl, -⟩; exact husw rfl)] at h1
        rw [hfrO u r (by rintro ⟨rfl, -⟩; exact husw rfl)] at h2
        exact hinv.oneTray u q r h1 h2
  · -- serve_sandwich_no_gluten
    obtain ⟨-, -, -, -, -, -, -, hia, hid⟩ := serveNG_atoms hf.inst hs ha
    exact serve_case hf hinv hia hid
  · -- serve_sandwich
    obtain ⟨-, -, -, -, -, hia, hid⟩ := serve_atoms hf.inst hs ha
    exact serve_case hf hinv hia hid
  · -- move_tray
    obtain ⟨hatS, hatI, hatD, hia, hid⟩ := move_atoms hf.inst hs ha
    have hpre : atT t p1 ∈ o.pre := by
      have := hf.preComplete (atV "?t" "?p1") hatS (at_dynamic hd)
      rwa [hatI] at this
    have hat : σ (atT t p1) = true := happ _ hpre
    have hfrOther : ∀ u q, ¬(u = t ∧ q = p2) → ¬(u = t ∧ q = p1) →
        (o.applyA σ) (atT u q) = σ (atT u q) := by
      intro u q h1 h2
      refine framed hA hD ?_ ?_ σ
      · rw [hia]
        simp only [List.mem_singleton, atT, GroundAtom.mk.injEq, true_and,
          List.cons.injEq, and_true]
        rintro ⟨rfl, rfl⟩; exact h1 ⟨rfl, rfl⟩
      · rw [hid]
        simp only [List.mem_singleton, atT, GroundAtom.mk.injEq, true_and,
          List.cons.injEq, and_true]
        rintro ⟨rfl, rfl⟩; exact h2 ⟨rfl, rfl⟩
    have hfrRest : ∀ (a : GroundAtom), (∀ u q, a ≠ atT u q) →
        (o.applyA σ) a = σ a := by
      intro a hne
      refine framed hA hD ?_ ?_ σ
      · rw [hia]; simp only [List.mem_singleton]; exact hne t p2
      · rw [hid]; simp only [List.mem_singleton]; exact hne t p1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro u q r h1 h2
      by_cases hut : u = t
      · subst hut
        -- only `p1` and `p2` can hold, and `p1` only when the move is trivial
        have hmem : ∀ y, (o.applyA σ) (atT u y) = true → y = p1 ∨ y = p2 := by
          intro y hy
          by_cases hy1 : y = p1
          · exact Or.inl hy1
          · by_cases hy2 : y = p2
            · exact Or.inr hy2
            · rw [hfrOther u y (by rintro ⟨-, rfl⟩; exact hy2 rfl)
                (by rintro ⟨-, rfl⟩; exact hy1 rfl)] at hy
              exact Or.inl (hinv.oneAt u y p1 hy hat)
        by_cases hp : p1 = p2
        · subst hp
          rcases hmem q h1 with rfl | rfl <;> rcases hmem r h2 with rfl | rfl <;> rfl
        · have hp1F : (o.applyA σ) (atT u p1) = false := by
            refine applyA_del σ ?_ (fun hm => by
              have := hA _ hm; rw [hia] at this
              simp only [List.mem_singleton, atT, GroundAtom.mk.injEq, true_and,
                List.cons.injEq, and_true] at this
              exact hp this)
            have := hf.delComplete (atV "?t" "?p1") hatD ?_ ?_
            · rwa [hatI] at this
            · rw [hatI, hia]
              simp only [List.mem_singleton, atT, GroundAtom.mk.injEq, true_and,
                List.cons.injEq, and_true]
              exact fun hc => hp hc
            · rw [hatI]; exact hpre
          rcases hmem q h1 with rfl | rfl
          · rw [hp1F] at h1; exact absurd h1 (by simp)
          · rcases hmem r h2 with rfl | rfl
            · rw [hp1F] at h2; exact absurd h2 (by simp)
            · rfl
      · rw [hfrOther u q (by rintro ⟨rfl, -⟩; exact hut rfl)
          (by rintro ⟨rfl, -⟩; exact hut rfl)] at h1
        rw [hfrOther u r (by rintro ⟨rfl, -⟩; exact hut rfl)
          (by rintro ⟨rfl, -⟩; exact hut rfl)] at h2
        exact hinv.oneAt u q r h1 h2
    · intro u q h1
      rw [hfrRest _ (by intro y z; simp [notexist, atT])] at h1
      rw [hfrRest _ (by intro y z; simp [ontray, atT])]
      exact hinv.freshTray u q h1
    · intro u h1
      rw [hfrRest _ (by intro y z; simp [notexist, atT])] at h1
      rw [hfrRest _ (by intro y z; simp [kitchenSw, atT])]
      exact hinv.freshKitchen u h1
    · intro u h1
      rw [hfrRest _ (by intro y z; simp [notexist, atT])] at h1
      rw [hfrRest _ (by intro y z; simp [glutenFree, atT])]
      exact hinv.freshGluten u h1
    · intro u q h1
      rw [hfrRest _ (by intro y z; simp [kitchenSw, atT])] at h1
      rw [hfrRest _ (by intro y z; simp [ontray, atT])]
      exact hinv.kitchenNotTray u q h1
    · intro u q r h1 h2
      rw [hfrRest _ (by intro y z; simp [ontray, atT])] at h1
      rw [hfrRest _ (by intro y z; simp [ontray, atT])] at h2
      exact hinv.oneTray u q r h1 h2

/-! ### A step that only touches the kitchen

This is both `make` schemas.  Nothing that the tray counts, the place counts or
the move counts read is touched; only the kitchen counts move, and each by one.
-/

theorem value_le_of_kitchen_only {c : Cfg} {σ τ : AtomState} (hnd : c.sandwiches.Nodup)
    (hserved : ∀ k, τ (served k) = σ (served k))
    (hontray : ∀ sw t, τ (ontray sw t) = σ (ontray sw t))
    (hat : ∀ t q, τ (atT t q) = σ (atT t q)) (sw : Name)
    (hgluten : ∀ u, u ≠ sw → τ (glutenFree u) = σ (glutenFree u))
    (hkitchen : ∀ u, u ≠ sw → τ (kitchenSw u) = σ (kitchenSw u))
    (hnotray : ∀ t, σ (ontray sw t) = false)
    (hnokitchen : σ (kitchenSw sw) = false) :
    value c σ ≤ value c τ + 1 := by
  have hun : unserved c τ = unserved c σ := by unfold unserved; simp only [hserved]
  have htot : total c τ = total c σ := by unfold total; rw [hun]
  have hallg : allergicLeft c τ = allergicLeft c σ := by
    unfold allergicLeft; rw [hun]
  have hwait : ∀ q, waitingAtP c τ q = waitingAtP c σ q := by
    intro q; unfold waitingAtP; rw [hun]
  have honT : ∀ u, onTray c τ u = onTray c σ u := by
    intro u; unfold onTray; simp only [hontray]
  have htA : trayAny c τ = trayAny c σ := by unfold trayAny; simp only [honT]
  have htF : trayFree c τ = trayFree c σ := by
    unfold trayFree
    congr 1
    refine List.filter_congr fun u _ => ?_
    by_cases hu : u = sw
    · subst hu
      have h1 : onTray c σ u = false := by
        unfold onTray
        simp only [List.any_eq_false]
        intro t _
        simp [hnotray t]
      rw [honT u, h1]; simp
    · rw [honT u]
      unfold isFree
      rw [hgluten u hu]
  have hshort : shortfall c τ = shortfall c σ := by
    unfold shortfall; rw [hallg, htF, htot, htA]
  have hkA : kitchenAny c τ ≤ kitchenAny c σ + 1 := by
    unfold kitchenAny
    refine length_filter_le_succ _ _ _ sw hnd fun u _ hu => ?_
    unfold inKitchen
    rw [honT u, hkitchen u hu]
  have hkF : kitchenFree c τ ≤ kitchenFree c σ + 1 := by
    unfold kitchenFree
    refine length_filter_le_succ _ _ _ sw hnd fun u _ hu => ?_
    unfold inKitchen isFree
    rw [honT u, hkitchen u hu, hgluten u hu]
  have htoMake : toMake c σ ≤ toMake c τ + 1 := by
    unfold toMake
    rw [hallg, htF, hshort]
    omega
  have hload : ∀ q, loadedAt c τ q = loadedAt c σ q := by
    intro q
    unfold loadedAt trayPlace trayLoad
    simp only [hat, hontray]
  have hmv : moveTargets c τ = moveTargets c σ := by
    unfold moveTargets
    refine List.filter_congr fun q _ => ?_
    rw [hload q, hwait q]
  have htk : trayInKitchen c τ = trayInKitchen c σ := by
    unfold trayInKitchen trayPlace; simp only [hat]
  have hmoves : moves c τ = moves c σ := by
    unfold moves; rw [hmv, hshort, htk]
  unfold value
  rw [htot, hshort, hmoves]
  split <;> omega

/-! ### A step that only moves a tray -/

theorem value_le_of_move {c : Cfg} {σ τ : AtomState} (hplNd : c.places.Nodup)
    (hkitchenSome : c.kitchen.isSome = true)
    (hserved : ∀ k, τ (served k) = σ (served k))
    (hontray : ∀ sw u, τ (ontray sw u) = σ (ontray sw u))
    (hkitchen : ∀ sw, τ (kitchenSw sw) = σ (kitchenSw sw))
    (hgluten : ∀ sw, τ (glutenFree sw) = σ (glutenFree sw))
    {t p2 : Name} (hatOther : ∀ u q, u ≠ t → τ (atT u q) = σ (atT u q))
    (htplace : trayPlace c τ t = some p2 ∨ trayPlace c τ t = none) :
    value c σ ≤ value c τ + 1 := by
  have hun : unserved c τ = unserved c σ := by unfold unserved; simp only [hserved]
  have htot : total c τ = total c σ := by unfold total; rw [hun]
  have hallg : allergicLeft c τ = allergicLeft c σ := by unfold allergicLeft; rw [hun]
  have hwait : ∀ q, waitingAtP c τ q = waitingAtP c σ q := by
    intro q; unfold waitingAtP; rw [hun]
  have honT : ∀ u, onTray c τ u = onTray c σ u := by
    intro u; unfold onTray; simp only [hontray]
  have hshort : shortfall c τ = shortfall c σ := by
    unfold shortfall trayFree trayAny isFree
    simp only [honT, hgluten, hallg, htot]
  have htoMake : toMake c τ = toMake c σ := by
    unfold toMake trayFree kitchenFree kitchenAny inKitchen isFree
    simp only [honT, hgluten, hkitchen, hallg, hshort]
  have htl : ∀ u, trayLoad c τ u = trayLoad c σ u := by
    intro u; unfold trayLoad; simp only [hontray]
  have htp : ∀ u, u ≠ t → trayPlace c τ u = trayPlace c σ u := by
    intro u hu; unfold trayPlace; simp only [hatOther u _ hu]
  have hload : ∀ q, q ≠ p2 → loadedAt c τ q ≤ loadedAt c σ q := by
    intro q hq
    unfold loadedAt
    rw [List.map_congr_left fun u _ => htl u]
    refine sum_filter_mono _ _ _ _ fun u _ hu => ?_
    by_cases hut : u = t
    · subst hut
      rcases htplace with h | h <;> rw [h] at hu <;> simp at hu
      exact absurd hu.symm hq
    · rwa [htp u hut] at hu
  have hsub : ∀ q ∈ moveTargets c σ, q ∈ moveTargets c τ ∨ q = p2 := by
    intro q hq
    by_cases hq2 : q = p2
    · exact Or.inr hq2
    · left
      unfold moveTargets at hq ⊢
      rw [List.mem_filter] at hq ⊢
      refine ⟨hq.1, ?_⟩
      have h2 := hq.2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h2 ⊢
      exact ⟨h2.1, by have := hload q hq2; rw [hwait q]; omega⟩
  have hnd : (moveTargets c σ).Nodup := hplNd.filter _
  have hmoves : moves c σ ≤ moves c τ + 1 := by
    unfold moves
    have hb1 : (if (decide (0 < shortfall c σ) && !trayInKitchen c σ) = true
        then 1 else 0) ≤ 1 := by split <;> omega
    by_cases hk2 : c.kitchen = some p2
    · -- the tray moved into the kitchen, which is never a target
      have hsub' : ∀ q ∈ moveTargets c σ, q ∈ moveTargets c τ := by
        intro q hq
        rcases hsub q hq with h | rfl
        · exact h
        · exfalso
          unfold moveTargets at hq
          rw [List.mem_filter] at hq
          have h2 := hq.2
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h2
          exact h2.1 hk2
      have hlen : (moveTargets c σ).length ≤ (moveTargets c τ).length :=
        length_le_of_subset' _ _ hnd hsub'
      omega
    · -- the tray did not move into the kitchen, so it cannot start one being there
      have hik : trayInKitchen c σ = false → trayInKitchen c τ = false := by
        intro h
        unfold trayInKitchen at h ⊢
        simp only [List.any_eq_false, beq_iff_eq] at h ⊢
        intro u hu
        by_cases hut : u = t
        · subst hut
          rcases htplace with hh | hh <;> rw [hh]
          · exact fun hc => hk2 hc.symm
          · rcases hkk : c.kitchen with _ | z
            · rw [hkk] at hkitchenSome; simp at hkitchenSome
            · simp
        · rw [htp u hut]; exact h u hu
      have hlen : (moveTargets c σ).length ≤ (moveTargets c τ).length + 1 :=
        length_le_succ_of_subset' _ _ p2 hnd hsub
      have hindle : (if (decide (0 < shortfall c σ) && !trayInKitchen c σ) = true
            then 1 else 0)
          ≤ (if (decide (0 < shortfall c τ) && !trayInKitchen c τ) = true
            then 1 else 0) := by
        by_cases hb : (decide (0 < shortfall c σ) && !trayInKitchen c σ) = true
        · rw [if_pos hb]
          simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
            decide_eq_true_eq] at hb
          rw [if_pos (by
            simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
              decide_eq_true_eq]
            exact ⟨by rw [hshort]; exact hb.1, hik hb.2⟩)]
        · rw [if_neg hb]; exact Nat.zero_le _
      omega
  unfold value
  rw [htot, hshort, htoMake]
  split <;> omega

/-! ### Two sums that count disjoint places -/

theorem trayAny_add_kitchenAny (c : Cfg) (σ : AtomState) :
    trayAny c σ + kitchenAny c σ
      = (c.sandwiches.filter fun u => onTray c σ u || σ (kitchenSw u)).length := by
  unfold trayAny kitchenAny
  rw [length_filter_add_or _ _ _ (fun u _ hu => by simp [inKitchen, hu])]
  congr 1
  refine List.filter_congr fun u _ => ?_
  unfold inKitchen
  by_cases hu : onTray c σ u <;> simp [hu]

theorem trayFree_add_kitchenFree (c : Cfg) (σ : AtomState) :
    trayFree c σ + kitchenFree c σ
      = (c.sandwiches.filter fun u => isFree σ u && (onTray c σ u || σ (kitchenSw u))).length := by
  unfold trayFree kitchenFree
  rw [length_filter_add_or _ _ _ (fun u _ hu => by
    simp only [Bool.and_eq_true] at hu
    simp [inKitchen, hu.1])]
  congr 1
  refine List.filter_congr fun u _ => ?_
  unfold inKitchen
  by_cases hu : onTray c σ u <;> by_cases hf : isFree σ u <;> simp [hu, hf]

theorem kitchenFree_le_kitchenAny (c : Cfg) (σ : AtomState) :
    kitchenFree c σ ≤ kitchenAny c σ := by
  unfold kitchenFree kitchenAny
  exact length_filter_mono _ _ _ fun u _ hu => by simp only [Bool.and_eq_true] at hu; exact hu.1

/-! ### Putting a sandwich on a tray -/

theorem value_le_of_put {c : Cfg} {σ τ : AtomState} (hnd : c.sandwiches.Nodup)
    (hserved : ∀ k, τ (served k) = σ (served k))
    (hat : ∀ u q, τ (atT u q) = σ (atT u q))
    (hgluten : ∀ u, τ (glutenFree u) = σ (glutenFree u)) {sw t kq : Name}
    (hontrayOther : ∀ u q, ¬(u = sw ∧ q = t) → τ (ontray u q) = σ (ontray u q))
    (hkitchenOther : ∀ u, u ≠ sw → τ (kitchenSw u) = σ (kitchenSw u))
    (hkSw : σ (kitchenSw sw) = true) (hkSwF : τ (kitchenSw sw) = false)
    (hnotray : ∀ q, σ (ontray sw q) = false)
    (hkq : c.kitchen = some kq) (htmem : t ∈ c.trays)
    (htplace : trayPlace c σ t = some kq) :
    value c σ ≤ value c τ + 1 := by
  have hun : unserved c τ = unserved c σ := by unfold unserved; simp only [hserved]
  have htot : total c τ = total c σ := by unfold total; rw [hun]
  have hallg : allergicLeft c τ = allergicLeft c σ := by unfold allergicLeft; rw [hun]
  have hwait : ∀ q, waitingAtP c τ q = waitingAtP c σ q := by
    intro q; unfold waitingAtP; rw [hun]
  have honTother : ∀ u, u ≠ sw → onTray c τ u = onTray c σ u := by
    intro u hu
    have h : ∀ q, τ (ontray u q) = σ (ontray u q) := fun q =>
      hontrayOther u q (by rintro ⟨rfl, -⟩; exact hu rfl)
    unfold onTray; simp only [h]
  have htpEq : ∀ u, trayPlace c τ u = trayPlace c σ u := by
    intro u; unfold trayPlace; simp only [hat]
  have honTsw : onTray c σ sw = false := by
    unfold onTray; simp only [List.any_eq_false]
    intro q _; simp [hnotray q]
  -- the two counts can only shrink together
  have hAA : trayAny c τ + kitchenAny c τ ≤ trayAny c σ + kitchenAny c σ := by
    rw [trayAny_add_kitchenAny, trayAny_add_kitchenAny]
    refine length_filter_mono _ _ _ fun u _ hu => ?_
    by_cases husw : u = sw
    · subst husw; simp [honTsw, hkSw]
    · rwa [honTother u husw, hkitchenOther u husw] at hu
  have hFF : trayFree c τ + kitchenFree c τ ≤ trayFree c σ + kitchenFree c σ := by
    rw [trayFree_add_kitchenFree, trayFree_add_kitchenFree]
    refine length_filter_mono _ _ _ fun u _ hu => ?_
    simp only [Bool.and_eq_true] at hu ⊢
    have hf : isFree σ u = true := by
      unfold isFree at hu ⊢; rw [← hgluten u]; exact hu.1
    refine ⟨hf, ?_⟩
    by_cases husw : u = sw
    · subst husw; simp [honTsw, hkSw]
    · rw [← honTother u husw, ← hkitchenOther u husw]; exact hu.2
  -- one sandwich may join each tray count
  have hTA : trayAny c τ ≤ trayAny c σ + 1 := by
    unfold trayAny
    exact length_filter_le_succ _ _ _ sw hnd fun u _ hu => honTother u hu
  have hTF : trayFree c τ ≤ trayFree c σ + 1 := by
    unfold trayFree
    refine length_filter_le_succ _ _ _ sw hnd fun u _ hu => ?_
    rw [honTother u hu]
    unfold isFree
    rw [hgluten u]
  have hshort : shortfall c σ ≤ shortfall c τ + 1 := by
    unfold shortfall; rw [hallg, htot]; omega
  have htoMake : toMake c σ ≤ toMake c τ := by
    have h1 := kitchenFree_le_kitchenAny c σ
    have h2 := kitchenFree_le_kitchenAny c τ
    unfold toMake shortfall
    rw [hallg, htot]
    omega
  -- the tray stands in the kitchen, which is never a target
  have htik : trayInKitchen c σ = true := by
    unfold trayInKitchen
    simp only [List.any_eq_true]
    exact ⟨t, htmem, by rw [htplace, hkq]; simp⟩
  have htikτ : trayInKitchen c τ = true := by
    unfold trayInKitchen at htik ⊢
    simp only [htpEq]
    exact htik
  have htlOther : ∀ u, u ≠ t → trayLoad c τ u = trayLoad c σ u := by
    intro u hu
    unfold trayLoad
    exact congrArg List.length (List.filter_congr fun z _ =>
      hontrayOther z u (by rintro ⟨-, rfl⟩; exact hu rfl))
  have hload : ∀ q, q ≠ kq → loadedAt c τ q = loadedAt c σ q := by
    intro q hq
    unfold loadedAt
    have hfilter : (c.trays.filter fun u => trayPlace c τ u == some q)
        = (c.trays.filter fun u => trayPlace c σ u == some q) :=
      List.filter_congr fun u _ => by rw [htpEq u]
    rw [hfilter]
    refine congrArg List.sum (List.map_congr_left fun u hu => ?_)
    rw [List.mem_filter] at hu
    have hut : u ≠ t := by
      rintro rfl
      have h2 := hu.2
      rw [htplace] at h2
      simp only [beq_iff_eq, Option.some.injEq] at h2
      exact hq h2.symm
    exact htlOther u hut
  have hmv : moveTargets c τ = moveTargets c σ := by
    unfold moveTargets
    refine List.filter_congr fun q _ => ?_
    by_cases hqk : q = kq
    · subst hqk; simp [hkq]
    · rw [hload q hqk, hwait q]
  have hmoves : moves c τ = moves c σ := by
    unfold moves; rw [hmv, htik, htikτ]; simp
  unfold value
  rw [htot]
  split <;> omega

/-! ### Serving a child

The delicate case: the count of children drops by one, and a sandwich comes off
a tray at the same time.  Both terms move together and the shortfalls stay put,
so the total falls by exactly the one `serve` action.
-/

set_option maxHeartbeats 1000000 in
theorem value_le_of_serve {c : Cfg} {σ τ : AtomState} (hinv : Inv σ)
    (hswNd : c.sandwiches.Nodup) (hchNd : c.children.Nodup) (htrNd : c.trays.Nodup)
    (hplNd : c.places.Nodup)
    {sw t k p : Name}
    (hservedOther : ∀ x, x ≠ k → τ (served x) = σ (served x))
    (hservedMono : σ (served k) = true → τ (served k) = true)
    (hat : ∀ u q, τ (atT u q) = σ (atT u q))
    (hgluten : ∀ u, τ (glutenFree u) = σ (glutenFree u))
    (hkitchen : ∀ u, τ (kitchenSw u) = σ (kitchenSw u))
    (hontrayOther : ∀ u q, ¬(u = sw ∧ q = t) → τ (ontray u q) = σ (ontray u q))
    (hontraySwt : τ (ontray sw t) = false) (honSw : σ (ontray sw t) = true)
    (htmem : t ∈ c.trays) (hswmem : sw ∈ c.sandwiches) (hpmem : p ∈ c.places)
    (hatTp : σ (atT t p) = true) (hwaitK : c.waitingAt k = some p)
    (hfree : c.allergic k = true → σ (glutenFree sw) = true) :
    value c σ ≤ value c τ + 1 := by
  -- the sandwich leaves the trays, and it is in no kitchen either way
  have honTσ : onTray c σ sw = true := by
    unfold onTray; simp only [List.any_eq_true]; exact ⟨t, htmem, honSw⟩
  have honTτ : onTray c τ sw = false := by
    unfold onTray; simp only [List.any_eq_false]
    intro q _
    by_cases hq : q = t
    · subst hq; simp [hontraySwt]
    · rw [hontrayOther sw q (by rintro ⟨-, rfl⟩; exact hq rfl)]
      by_contra hc
      exact hq (hinv.oneTray sw q t (by simpa using hc) honSw)
  have hkSwF : σ (kitchenSw sw) = false := by
    by_contra hc
    rw [hinv.kitchenNotTray sw t (by simpa using hc)] at honSw
    exact Bool.noConfusion honSw
  have honTother : ∀ u, u ≠ sw → onTray c τ u = onTray c σ u := by
    intro u hu
    have h : ∀ q, τ (ontray u q) = σ (ontray u q) := fun q =>
      hontrayOther u q (by rintro ⟨rfl, -⟩; exact hu rfl)
    unfold onTray; simp only [h]
  have hinKσ : ∀ u, inKitchen c σ u = false → inKitchen c τ u = false := by
    intro u h
    unfold inKitchen at h ⊢
    by_cases hu : u = sw
    · subst hu; simp [hkitchen u, hkSwF]
    · rw [honTother u hu, hkitchen u]; exact h
  have hinK : ∀ u, inKitchen c τ u = inKitchen c σ u := by
    intro u
    by_cases hu : u = sw
    · subst hu
      unfold inKitchen
      rw [honTσ, honTτ, hkitchen u, hkSwF]
      simp
    · unfold inKitchen; rw [honTother u hu, hkitchen u]
  have hkA : kitchenAny c τ = kitchenAny c σ := by
    unfold kitchenAny; simp only [hinK]
  have hkF : kitchenFree c τ = kitchenFree c σ := by
    unfold kitchenFree isFree; simp only [hinK, hgluten]
  -- the tray counts each drop by the one sandwich
  have hTA : trayAny c σ = trayAny c τ + 1 := by
    unfold trayAny
    exact length_filter_drop_one _ _ _ sw hswmem hswNd honTσ honTτ
      fun u _ hu => (honTother u hu).symm
  have hTF : trayFree c σ = trayFree c τ + (if σ (glutenFree sw) then 1 else 0) := by
    unfold trayFree isFree
    by_cases hg : σ (glutenFree sw) = true
    · rw [if_pos hg]
      refine length_filter_drop_one _ _ _ sw hswmem hswNd (by simp [honTσ, hg])
        (by simp [honTτ]) fun u _ hu => ?_
      rw [honTother u hu, hgluten u]
    · rw [if_neg hg, Nat.add_zero]
      refine congrArg List.length (List.filter_congr fun u _ => ?_).symm
      by_cases hu : u = sw
      · subst hu; simp [honTσ, honTτ, hgluten u, hg]
      · rw [honTother u hu, hgluten u]
  -- the tray loses one sandwich, and it stands at `p`
  have htp : trayPlace c σ t = some p := by
    unfold trayPlace
    rcases hfind : c.places.find? (fun q => σ (atT t q)) with _ | q
    · rw [List.find?_eq_none] at hfind
      exact absurd hatTp (by simpa using hfind p hpmem)
    · rw [hinv.oneAt t q p (by simpa using List.find?_some hfind) hatTp]
  have htpEq : ∀ u, trayPlace c τ u = trayPlace c σ u := by
    intro u; unfold trayPlace; simp only [hat]
  have htlOther : ∀ u, u ≠ t → trayLoad c τ u = trayLoad c σ u := by
    intro u hu
    unfold trayLoad
    exact congrArg List.length (List.filter_congr fun z _ =>
      hontrayOther z u (by rintro ⟨-, rfl⟩; exact hu rfl))
  have htlT : trayLoad c σ t = trayLoad c τ t + 1 := by
    unfold trayLoad
    refine length_filter_drop_one _ _ _ sw hswmem hswNd honSw hontraySwt
      fun u _ hu => ?_
    exact (hontrayOther u t (by rintro ⟨rfl, -⟩; exact hu rfl)).symm
  have hloadOther : ∀ q, q ≠ p → loadedAt c τ q = loadedAt c σ q := by
    intro q hq
    unfold loadedAt
    have hfilter : (c.trays.filter fun u => trayPlace c τ u == some q)
        = (c.trays.filter fun u => trayPlace c σ u == some q) :=
      List.filter_congr fun u _ => by rw [htpEq u]
    rw [hfilter]
    refine congrArg List.sum (List.map_congr_left fun u hu => ?_)
    rw [List.mem_filter] at hu
    have hut : u ≠ t := by
      rintro rfl
      have h2 := hu.2
      rw [htp] at h2
      simp only [beq_iff_eq, Option.some.injEq] at h2
      exact hq h2.symm
    exact htlOther u hut
  have hloadP : loadedAt c σ p = loadedAt c τ p + 1 := by
    unfold loadedAt
    have hfilter : (c.trays.filter fun u => trayPlace c τ u == some p)
        = (c.trays.filter fun u => trayPlace c σ u == some p) :=
      List.filter_congr fun u _ => by rw [htpEq u]
    rw [hfilter]
    refine (sum_map_shift _ (trayLoad c τ) (trayLoad c σ) t 1 ?_ (htrNd.filter _) ?_
      ?_).symm
    · rw [List.mem_filter]; exact ⟨htmem, by rw [htp]; simp⟩
    · omega
    · intro u _ hu; exact htlOther u hu
  have htik : trayInKitchen c τ = trayInKitchen c σ := by
    unfold trayInKitchen; simp only [htpEq]
  by_cases hcase : k ∈ c.children ∧ σ (served k) = false ∧ τ (served k) = true
  · -- the child leaves the count, and so does the sandwich
    obtain ⟨hkmem, hkσ, hkτ⟩ := hcase
    have htot : total c σ = total c τ + 1 := by
      unfold total unserved
      exact length_filter_drop_one _ _ _ k hkmem hchNd (by simp [hkσ]) (by simp [hkτ])
        fun x _ hx => (by rw [hservedOther x hx])
    have hallg : allergicLeft c σ
        = allergicLeft c τ + (if c.allergic k then 1 else 0) := by
      unfold allergicLeft unserved
      rw [List.filter_filter, List.filter_filter]
      by_cases hk : c.allergic k
      · rw [if_pos hk]
        exact length_filter_drop_one _ _ _ k hkmem hchNd (by simp [hkσ, hk])
          (by simp [hkτ]) fun x _ hx => by rw [hservedOther x hx]
      · rw [if_neg hk, Nat.add_zero]
        refine congrArg List.length (List.filter_congr fun x _ => ?_)
        by_cases hx : x = k
        · subst hx; simp [hk]
        · rw [hservedOther x hx]
    have hwaitP : waitingAtP c σ p = waitingAtP c τ p + 1 := by
      unfold waitingAtP unserved
      rw [List.filter_filter, List.filter_filter]
      exact length_filter_drop_one _ _ _ k hkmem hchNd (by simp [hkσ, hwaitK])
        (by simp [hkτ]) fun x _ hx => by rw [hservedOther x hx]
    have hwaitO : ∀ q, q ≠ p → waitingAtP c σ q = waitingAtP c τ q := by
      intro q hq
      unfold waitingAtP unserved
      rw [List.filter_filter, List.filter_filter]
      refine congrArg List.length (List.filter_congr fun x _ => ?_)
      by_cases hx : x = k
      · subst hx
        have hne : (c.waitingAt x == some q) = false := by
          rw [hwaitK]
          simp only [beq_eq_false_iff_ne, ne_eq, Option.some.injEq]
          exact fun hc => hq hc.symm
        simp [hne]
      · rw [hservedOther x hx]
    have hcounts : (c.allergic k = true ∧ trayFree c σ = trayFree c τ + 1 ∧
        allergicLeft c σ = allergicLeft c τ + 1) ∨
        (allergicLeft c σ = allergicLeft c τ ∧ trayFree c τ ≤ trayFree c σ) := by
      by_cases hk : c.allergic k
      · exact Or.inl ⟨hk, by rw [hTF, if_pos (hfree hk)], by rw [hallg, if_pos hk]⟩
      · exact Or.inr ⟨by rw [hallg, if_neg hk]; omega, by rw [hTF]; omega⟩
    have hshort : shortfall c σ ≤ shortfall c τ := by
      unfold shortfall
      rcases hcounts with ⟨-, h1, h2⟩ | ⟨h2, h1⟩ <;> omega
    have htoMake : toMake c σ ≤ toMake c τ := by
      unfold toMake shortfall
      rw [hkA, hkF]
      rcases hcounts with ⟨-, h1, h2⟩ | ⟨h2, h1⟩ <;> omega
    have hmv : moveTargets c τ = moveTargets c σ := by
      unfold moveTargets
      refine List.filter_congr fun q _ => ?_
      by_cases hq : q = p
      · subst hq
        have hdec : (decide (loadedAt c τ q < waitingAtP c τ q))
            = (decide (loadedAt c σ q < waitingAtP c σ q)) := by
          rw [hloadP, hwaitP]
          simp only [decide_eq_decide]
          omega
        rw [hdec]
      · rw [hloadOther q hq, hwaitO q hq]
    have hmoves : moves c σ ≤ moves c τ := by
      unfold moves
      rw [hmv, htik]
      by_cases hb : (decide (0 < shortfall c σ) && !trayInKitchen c σ) = true
      · simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
          decide_eq_true_eq] at hb
        rw [if_pos (by
          simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
            decide_eq_true_eq]
          exact hb), if_pos (by
          simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
            decide_eq_true_eq]
          exact ⟨by omega, hb.2⟩)]
      · rw [if_neg hb]; omega
    rcases Nat.eq_zero_or_pos (total c τ) with h0 | hpos
    · -- the last child: everything else is already zero
      have hwle : ∀ q, waitingAtP c τ q ≤ total c τ := by
        intro q; unfold waitingAtP total; exact List.length_filter_le _ _
      have hale : allergicLeft c τ ≤ total c τ := by
        unfold allergicLeft total; exact List.length_filter_le _ _
      have hs0 : shortfall c σ = 0 := by
        unfold shortfall
        rcases hcounts with ⟨-, h1, h2⟩ | ⟨h2, h1⟩ <;> omega
      have ht0 : toMake c σ = 0 := by unfold toMake; rw [hs0]; omega
      have hmt : moveTargets c σ = [] := by
        refine List.filter_eq_nil_iff.mpr fun q _ => ?_
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
        intro _
        have h1 := hwle q
        by_cases hq : q = p
        · subst hq; omega
        · have h2 := hwaitO q hq; omega
      have hm0 : moves c σ = 0 := by
        unfold moves; rw [hmt, hs0]; simp
      have hvτ : value c τ = 0 := by unfold value; rw [h0]; simp
      rw [hvτ]
      unfold value
      rw [if_neg (by rw [htot, h0]; simp), hs0, ht0, hm0, htot, h0]
    · unfold value
      rw [if_neg (by simp only [beq_iff_eq]; omega),
        if_neg (by simp only [beq_iff_eq]; omega)]
      omega
  · -- the count of children does not move
    have hun : unserved c τ = unserved c σ := by
      unfold unserved
      refine List.filter_congr fun x hx => ?_
      by_cases hxk : x = k
      · subst hxk
        by_cases h1 : σ (served x) = true
        · rw [h1, hservedMono h1]
        · have h1' : σ (served x) = false := by simpa using h1
          have h2 : τ (served x) = false := by
            by_contra hc
            exact hcase ⟨hx, h1', by simpa using hc⟩
          rw [h1', h2]
      · rw [hservedOther x hxk]
    have htot : total c τ = total c σ := by unfold total; rw [hun]
    have hallg : allergicLeft c τ = allergicLeft c σ := by unfold allergicLeft; rw [hun]
    have hwait : ∀ q, waitingAtP c τ q = waitingAtP c σ q := by
      intro q; unfold waitingAtP; rw [hun]
    have hshort : shortfall c σ ≤ shortfall c τ := by
      unfold shortfall; rw [hallg, htot, hTA, hTF]; omega
    have htoMake : toMake c σ ≤ toMake c τ := by
      unfold toMake shortfall
      rw [hkA, hkF, hallg, htot, hTA, hTF]
      omega
    have hsub : ∀ q ∈ moveTargets c σ, q ∈ moveTargets c τ := by
      intro q hq
      unfold moveTargets at hq ⊢
      rw [List.mem_filter] at hq ⊢
      refine ⟨hq.1, ?_⟩
      have h2 := hq.2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h2 ⊢
      refine ⟨h2.1, ?_⟩
      rw [hwait q]
      by_cases hqp : q = p
      · subst hqp; omega
      · rw [hloadOther q hqp]; exact h2.2
    have hmoves : moves c σ ≤ moves c τ := by
      unfold moves
      have hlen : (moveTargets c σ).length ≤ (moveTargets c τ).length :=
        length_le_of_subset' _ _ (hplNd.filter _) hsub
      by_cases hb : (decide (0 < shortfall c σ) && !trayInKitchen c σ) = true
      · simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
          decide_eq_true_eq] at hb
        rw [if_pos (by
          simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
            decide_eq_true_eq]
          exact hb), if_pos (by
          simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
            decide_eq_true_eq]
          exact ⟨by omega, by rw [htik]; exact hb.2⟩)]
        omega
      · rw [if_neg hb]; omega
    unfold value
    rw [htot]
    split <;> omega

/-! ### What the configuration owes the problem -/

structure CfgOK (d : Domain) (p : Problem) (c : Cfg) : Prop where
  swNd : c.sandwiches.Nodup
  chNd : c.children.Nodup
  trNd : c.trays.Nodup
  plNd : c.places.Nodup
  sandwiches : ∀ x, WellTyped d (allObjects d p) "sandwich" x → x ∈ c.sandwiches
  trays : ∀ x, WellTyped d (allObjects d p) "tray" x → x ∈ c.trays
  places : ∀ x, WellTyped d (allObjects d p) "place" x → x ∈ c.places
  kitchen : c.kitchen = some "kitchen"
  kitchenPlace : "kitchen" ∈ c.places
  waiting : ∀ x q, (Std.HashSet.ofList p.init).contains (waitingAtom x q) = true →
    c.waitingAt x = some q
  allergicYes : ∀ x, (Std.HashSet.ofList p.init).contains (allergicAtom x) = true →
    c.allergic x = true
  allergicNo : ∀ x, (Std.HashSet.ofList p.init).contains (notAllergicAtom x) = true →
    c.allergic x = false

/-- With one `at` holding, that is where the tray stands. -/
theorem trayPlace_eq {c : Cfg} {σ : AtomState} (hinv : Inv σ) {t q : Name}
    (hq : q ∈ c.places) (hs : σ (atT t q) = true) : trayPlace c σ t = some q := by
  unfold trayPlace
  rcases hfind : c.places.find? (fun z => σ (atT t z)) with _ | z
  · rw [List.find?_eq_none] at hfind
    exact absurd hs (by simpa using hfind q hq)
  · rw [hinv.oneAt t z q (by simpa using List.find?_some hfind) hs]

/-! ### Consistency, over the six schemas -/

set_option maxHeartbeats 1000000 in
theorem liftedConsistent {d : Domain} {p : Problem} {c : Cfg} (hd : ChildsnackPinned d)
    (hok : CfgOK d p c) (relevance : Bool)
    (hfacts : ∀ o ∈ groundedOps d p relevance, Nonempty (OpFacts d p o))
    (hcost : ∀ o ∈ groundedOps d p relevance, 0 < o.cost) :
    LiftedConsistentOn d p relevance (fun σ => Inv σ) (value c) := by
  intro o ho σ hinv happ
  obtain ⟨hf⟩ := hfacts o ho
  have hc1 := hcost o ho
  have hA := hf.subAdd
  have hD := hf.subDel
  rcases instance_shape hd.actions hf.inst with
    ⟨sw, b, x, hs, ha⟩ | ⟨sw, b, x, hs, ha⟩ | ⟨sw, t, hs, ha, htt⟩ |
    ⟨sw, k, t, pl, hs, ha, hkt, htt, hpt, hswt⟩ |
    ⟨sw, k, t, pl, hs, ha, hkt, htt, hpt, hswt⟩ |
    ⟨t, p1, p2, hs, ha, htt, -, hp2t⟩
  · -- make_sandwich_no_gluten
    obtain ⟨hia, hid⟩ := makeNG_atoms hf.inst hs ha
    have hne : σ (notexist sw) = true := by
      have := hf.preComplete (notexistV "?s") (by rw [hs]; simp [makeNGA])
        (notexist_dynamic hd.actions)
      rw [show instAtom hf.inst.schema.params hf.inst.args (notexistV "?s")
        = notexist sw from by rw [hs, ha]; rfl] at this
      exact happ _ this
    have := value_le_of_kitchen_only (c := c) hok.swNd
      (fun z => framed hA hD (by rw [hia]; simp) (by rw [hid]; simp) σ)
      (fun u q => framed hA hD (by rw [hia]; simp) (by rw [hid]; simp) σ)
      (fun u q => framed hA hD (by rw [hia]; simp) (by rw [hid]; simp) σ)
      sw
      (fun u hu => framed hA hD (by rw [hia]; simp [hu]) (by rw [hid]; simp) σ)
      (fun u hu => framed hA hD (by rw [hia]; simp [hu]) (by rw [hid]; simp) σ)
      (fun q => hinv.freshTray sw q hne) (hinv.freshKitchen sw hne)
    omega
  · -- make_sandwich
    obtain ⟨hia, hid⟩ := make_atoms hf.inst hs ha
    have hne : σ (notexist sw) = true := by
      have := hf.preComplete (notexistV "?s") (by rw [hs]; simp [makeA])
        (notexist_dynamic hd.actions)
      rw [show instAtom hf.inst.schema.params hf.inst.args (notexistV "?s")
        = notexist sw from by rw [hs, ha]; rfl] at this
      exact happ _ this
    have := value_le_of_kitchen_only (c := c) hok.swNd
      (fun z => framed hA hD (by rw [hia]; simp) (by rw [hid]; simp) σ)
      (fun u q => framed hA hD (by rw [hia]; simp) (by rw [hid]; simp) σ)
      (fun u q => framed hA hD (by rw [hia]; simp) (by rw [hid]; simp) σ)
      sw
      (fun u hu => framed hA hD (by rw [hia]; simp) (by rw [hid]; simp) σ)
      (fun u hu => framed hA hD (by rw [hia]; simp [hu]) (by rw [hid]; simp) σ)
      (fun q => hinv.freshTray sw q hne) (hinv.freshKitchen sw hne)
    omega
  · -- put_on_tray
    obtain ⟨hkS, hkI, hatS, hatI, hkD, hia, hid⟩ := put_atoms hf.inst hs ha
    have hpre : kitchenSw sw ∈ o.pre := by
      have := hf.preComplete (kitchenSwV "?s") hkS (kitchenSw_dynamic hd.actions)
      rwa [hkI] at this
    have hk : σ (kitchenSw sw) = true := happ _ hpre
    have hkF : (o.applyA σ) (kitchenSw sw) = false := by
      refine applyA_del σ ?_ (fun hm => by
        have := hA _ hm; rw [hia] at this; simp at this)
      have := hf.delComplete (kitchenSwV "?s") hkD (by rw [hkI, hia]; simp)
        (by rw [hkI]; exact hpre)
      rwa [hkI] at this
    have hatK : σ (atT t "kitchen") = true := by
      have := hf.preComplete (atKitchenV "?t") hatS (at_dynamic hd.actions)
      rw [hatI] at this; exact happ _ this
    have := value_le_of_put (c := c) hok.swNd
      (fun z => framed hA hD (by rw [hia]; simp) (by rw [hid]; simp) σ)
      (fun u q => framed hA hD (by rw [hia]; simp) (by rw [hid]; simp) σ)
      (fun u => framed hA hD (by rw [hia]; simp) (by rw [hid]; simp) σ)
      (fun u q hne => by
        refine framed hA hD ?_ (by rw [hid]; simp) σ
        rw [hia]
        simp only [List.mem_singleton, ontray, GroundAtom.mk.injEq, true_and,
          List.cons.injEq, and_true]
        rintro ⟨rfl, rfl⟩; exact hne ⟨rfl, rfl⟩)
      (fun u hu => framed hA hD (by rw [hia]; simp) (by rw [hid]; simp [hu]) σ)
      hk hkF (fun q => hinv.kitchenNotTray sw q hk) hok.kitchen
      (hok.trays t htt) (trayPlace_eq hinv hok.kitchenPlace hatK)
    omega
  · -- serve_sandwich_no_gluten
    obtain ⟨honS, honI, hatS, hatI, hgS, hgI, honD, hia, hid⟩ :=
      serveNG_atoms hf.inst hs ha
    have hpreOn : ontray sw t ∈ o.pre := by
      have := hf.preComplete (ontrayV "?s" "?t") honS (ontray_dynamic hd.actions)
      rwa [honI] at this
    have honSw : σ (ontray sw t) = true := happ _ hpreOn
    have honF : (o.applyA σ) (ontray sw t) = false := by
      refine applyA_del σ ?_ (fun hm => by
        have h2 := hA _ hm; rw [hia] at h2; simp at h2)
      have := hf.delComplete (ontrayV "?s" "?t") honD (by rw [honI, hia]; simp)
        (by rw [honI]; exact hpreOn)
      rwa [honI] at this
    have hatTp : σ (atT t pl) = true := by
      have := hf.preComplete (atV "?t" "?p") hatS (at_dynamic hd.actions)
      rw [hatI] at this; exact happ _ this
    have hgl : σ (glutenFree sw) = true := by
      have := hf.preComplete (glutenFreeV "?s") hgS (glutenFree_dynamic hd.actions)
      rw [hgI] at this; exact happ _ this
    have hwaitK : c.waitingAt k = some pl := by
      refine hok.waiting k pl ?_
      have := hf.staticHeld (waitingV "?c" "?p") (by rw [hs]; simp [serveNGA])
        hd.waitingStatic
      rw [show instAtom hf.inst.schema.params hf.inst.args (waitingV "?c" "?p")
        = waitingAtom k pl from by rw [hs, ha]; rfl] at this
      exact this
    have := value_le_of_serve (c := c) hinv hok.swNd hok.chNd hok.trNd hok.plNd
      (fun z hz => framed hA hD (by rw [hia]; simpa [served] using hz)
        (by rw [hid]; simp) σ)
      (fun h => by
        by_cases hm : served k ∈ o.add
        · exact applyA_add σ hm
        · rwa [applyA_frame σ hm (fun hm2 => by
            have := hD _ hm2; rw [hid] at this; simp at this)])
      (fun u q => framed hA hD (by rw [hia]; simp) (by rw [hid]; simp) σ)
      (fun u => framed hA hD (by rw [hia]; simp) (by rw [hid]; simp) σ)
      (fun u => framed hA hD (by rw [hia]; simp) (by rw [hid]; simp) σ)
      (fun u q hne => by
        refine framed hA hD (by rw [hia]; simp) ?_ σ
        rw [hid]
        simp only [List.mem_singleton, ontray, GroundAtom.mk.injEq, true_and,
          List.cons.injEq, and_true]
        rintro ⟨rfl, rfl⟩; exact hne ⟨rfl, rfl⟩)
      honF honSw (hok.trays t htt) (hok.sandwiches sw hswt) (hok.places pl hpt)
      hatTp hwaitK (fun _ => hgl)
    omega
  · -- serve_sandwich
    obtain ⟨honS, honI, hatS, hatI, honD, hia, hid⟩ := serve_atoms hf.inst hs ha
    have hpreOn : ontray sw t ∈ o.pre := by
      have := hf.preComplete (ontrayV "?s" "?t") honS (ontray_dynamic hd.actions)
      rwa [honI] at this
    have honSw : σ (ontray sw t) = true := happ _ hpreOn
    have honF : (o.applyA σ) (ontray sw t) = false := by
      refine applyA_del σ ?_ (fun hm => by
        have := hA _ hm; rw [hia] at this; simp at this)
      have := hf.delComplete (ontrayV "?s" "?t") honD (by rw [honI, hia]; simp)
        (by rw [honI]; exact hpreOn)
      rwa [honI] at this
    have hatTp : σ (atT t pl) = true := by
      have := hf.preComplete (atV "?t" "?p") hatS (at_dynamic hd.actions)
      rw [hatI] at this; exact happ _ this
    have hwaitK : c.waitingAt k = some pl := by
      refine hok.waiting k pl ?_
      have := hf.staticHeld (waitingV "?c" "?p") (by rw [hs]; simp [serveA])
        hd.waitingStatic
      rw [show instAtom hf.inst.schema.params hf.inst.args (waitingV "?c" "?p")
        = waitingAtom k pl from by rw [hs, ha]; rfl] at this
      exact this
    have hnotAll : c.allergic k = false := by
      refine hok.allergicNo k ?_
      have := hf.staticHeld (notAllergicV "?c") (by rw [hs]; simp [serveA])
        hd.notAllergicStatic
      rw [show instAtom hf.inst.schema.params hf.inst.args (notAllergicV "?c")
        = notAllergicAtom k from by rw [hs, ha]; rfl] at this
      exact this
    have := value_le_of_serve (c := c) hinv hok.swNd hok.chNd hok.trNd hok.plNd
      (fun z hz => framed hA hD (by rw [hia]; simpa [served] using hz)
        (by rw [hid]; simp) σ)
      (fun h => by
        by_cases hm : served k ∈ o.add
        · exact applyA_add σ hm
        · rwa [applyA_frame σ hm (fun hm2 => by
            have := hD _ hm2; rw [hid] at this; simp at this)])
      (fun u q => framed hA hD (by rw [hia]; simp) (by rw [hid]; simp) σ)
      (fun u => framed hA hD (by rw [hia]; simp) (by rw [hid]; simp) σ)
      (fun u => framed hA hD (by rw [hia]; simp) (by rw [hid]; simp) σ)
      (fun u q hne => by
        refine framed hA hD (by rw [hia]; simp) ?_ σ
        rw [hid]
        simp only [List.mem_singleton, ontray, GroundAtom.mk.injEq, true_and,
          List.cons.injEq, and_true]
        rintro ⟨rfl, rfl⟩; exact hne ⟨rfl, rfl⟩)
      honF honSw (hok.trays t htt) (hok.sandwiches sw hswt) (hok.places pl hpt)
      hatTp hwaitK (fun hc => absurd hc (by rw [hnotAll]; simp))
    omega
  · -- move_tray
    obtain ⟨hatS, hatI, hatD, hia, hid⟩ := move_atoms hf.inst hs ha
    have hfrRest : ∀ (a : GroundAtom), (∀ u q, a ≠ atT u q) →
        (o.applyA σ) a = σ a := by
      intro a hne
      refine framed hA hD ?_ ?_ σ
      · rw [hia]; simp only [List.mem_singleton]; exact hne t p2
      · rw [hid]; simp only [List.mem_singleton]; exact hne t p1
    have hother : ∀ u q, u ≠ t → (o.applyA σ) (atT u q) = σ (atT u q) := by
      intro u q hu
      refine framed hA hD ?_ ?_ σ
      · rw [hia]; simp only [List.mem_singleton, atT, GroundAtom.mk.injEq, true_and,
          List.cons.injEq, and_true]
        rintro ⟨rfl, -⟩; exact hu rfl
      · rw [hid]; simp only [List.mem_singleton, atT, GroundAtom.mk.injEq, true_and,
          List.cons.injEq, and_true]
        rintro ⟨rfl, -⟩; exact hu rfl
    have hpre : atT t p1 ∈ o.pre := by
      have := hf.preComplete (atV "?t" "?p1") hatS (at_dynamic hd.actions)
      rwa [hatI] at this
    have hat1 : σ (atT t p1) = true := happ _ hpre
    have hkey : ∀ z, (o.applyA σ) (atT t z) = true → z = p2 := by
      intro z hz
      by_cases hz2 : z = p2
      · exact hz2
      · exfalso
        by_cases hz1 : z = p1
        · subst hz1
          have hdel : atT t z ∈ o.del := by
            have := hf.delComplete (atV "?t" "?p1") hatD ?_ ?_
            · rwa [hatI] at this
            · rw [hatI, hia]
              simp only [List.mem_singleton, atT, GroundAtom.mk.injEq, true_and,
                List.cons.injEq, and_true]
              exact fun hc => hz2 hc
            · rw [hatI]; exact hpre
          rw [applyA_del σ hdel (fun hm => by
            have h2 := hA _ hm; rw [hia] at h2
            simp only [List.mem_singleton, atT, GroundAtom.mk.injEq, true_and,
              List.cons.injEq, and_true] at h2
            exact hz2 h2)] at hz
          exact absurd hz (by simp)
        · rw [framed hA hD
            (by rw [hia]
                simp only [List.mem_singleton, atT, GroundAtom.mk.injEq, true_and,
                  List.cons.injEq, and_true]
                exact fun hc => hz2 hc)
            (by rw [hid]
                simp only [List.mem_singleton, atT, GroundAtom.mk.injEq, true_and,
                  List.cons.injEq, and_true]
                exact fun hc => hz1 hc) σ] at hz
          exact hz1 (hinv.oneAt t z p1 hz hat1)
    have hplace : trayPlace c (o.applyA σ) t = some p2 ∨
        trayPlace c (o.applyA σ) t = none := by
      rcases hfind : trayPlace c (o.applyA σ) t with _ | z
      · exact Or.inr rfl
      · left
        have hz : (o.applyA σ) (atT t z) = true := by
          unfold trayPlace at hfind
          simpa using List.find?_some hfind
        rw [hkey z hz]
    have := value_le_of_move (c := c) hok.plNd (by simp [hok.kitchen])
      (fun z => hfrRest _ (by intro y w; simp [served, atT]))
      (fun u q => hfrRest _ (by intro y w; simp [ontray, atT]))
      (fun u => hfrRest _ (by intro y w; simp [kitchenSw, atT]))
      (fun u => hfrRest _ (by intro y w; simp [glutenFree, atT]))
      hother hplace
    omega

theorem invPreserved {d : Domain} {p : Problem} (hd : ChildsnackPinned d)
    (relevance : Bool)
    (hfacts : ∀ o ∈ groundedOps d p relevance, Nonempty (OpFacts d p o)) :
    ∀ o ∈ groundedOps d p relevance, ∀ σ, Inv σ → o.applicableA σ → Inv (o.applyA σ) :=
  fun o ho σ hinv happ => inv_preserved hd.actions (hfacts o ho).some hinv happ

/-- **Childsnack's improved heuristic is goal-aware.** -/
theorem improved_goalAwareOn (d : Domain) (p : Problem) (relevance : Bool)
    (c : Cfg) (hd : ChildsnackPinned d) (hok : CfgOK d p c)
    (hwf : Task.WF (ground d p relevance))
    (hcost : ∀ o ∈ groundedOps d p relevance, 0 < o.cost)
    (hfacts : ∀ o ∈ groundedOps d p relevance, Nonempty (OpFacts d p o))
    (hsub : ∀ k ∈ c.children, served k ∈ p.goal)
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hv : State → Nat)
    (hcomp : ComputesOn (ground d p relevance) (fun σ => Inv σ) hv (value c)) :
    (ground d p relevance).GoalAwareOn (Reachable (ground d p relevance)) hv :=
  goalAwareOn_of_lifted d p relevance hwf hcost hv (value c) (fun σ => Inv σ) hcomp
    hinit (invPreserved hd relevance hfacts) (liftedGoalAware c p hsub)

/-- **Childsnack's improved heuristic is consistent.** -/
theorem improved_consistentOn (d : Domain) (p : Problem) (relevance : Bool)
    (c : Cfg) (hd : ChildsnackPinned d) (hok : CfgOK d p c)
    (hwf : Task.WF (ground d p relevance))
    (hcost : ∀ o ∈ groundedOps d p relevance, 0 < o.cost)
    (hfacts : ∀ o ∈ groundedOps d p relevance, Nonempty (OpFacts d p o))
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hv : State → Nat)
    (hcomp : ComputesOn (ground d p relevance) (fun σ => Inv σ) hv (value c)) :
    (ground d p relevance).ConsistentOn (Reachable (ground d p relevance)) hv :=
  consistentOn_of_lifted d p relevance hwf hcost hv (value c) (fun σ => Inv σ) hcomp
    hinit (invPreserved hd relevance hfacts)
    (liftedConsistent hd hok relevance hfacts hcost)

/--
**Childsnack's improved heuristic is admissible.**  Anything that computes the
lifted value is admissible on every state the search can reach.
-/
theorem improved_admissibleOn (d : Domain) (p : Problem) (relevance : Bool)
    (c : Cfg) (hd : ChildsnackPinned d) (hok : CfgOK d p c)
    (hwf : Task.WF (ground d p relevance))
    (hcost : ∀ o ∈ groundedOps d p relevance, 0 < o.cost)
    (hfacts : ∀ o ∈ groundedOps d p relevance, Nonempty (OpFacts d p o))
    (hsub : ∀ k ∈ c.children, served k ∈ p.goal)
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hv : State → Nat)
    (hcomp : ComputesOn (ground d p relevance) (fun σ => Inv σ) hv (value c)) :
    (ground d p relevance).AdmissibleOn (Reachable (ground d p relevance)) hv :=
  admissibleOn_of_lifted d p relevance hwf hcost hv (value c) (fun σ => Inv σ) hcomp
    hinit (invPreserved hd relevance hfacts) (liftedGoalAware c p hsub)
    (liftedConsistent hd hok relevance hfacts hcost)

end Planner.Lifted.Childsnack

/- -------------------------------------------------------------------------- -/
/-
What the compiled childsnack heuristic must match.

Three tables have to line up with the `Cfg`: the children, the sandwiches, and
the trays.  The tray table is two arrays indexed by tray position, so it is
paired through `zipIdx`: each entry carries its own index, and the load facts are
read at that index inside the relation.
-/

namespace Planner.Lifted.Childsnack

open Planner Planner.Pddl

abbrev CData := ExampleHeuristics.Childsnack.Data
abbrev CChild := ExampleHeuristics.Childsnack.ChildInfo
abbrev CSw := ExampleHeuristics.Childsnack.SandwichInfo

/-- The place a compiled index stands for. -/
def nameOf (c : Cfg) (i : Nat) : Pddl.Name := c.places.getD i ""

theorem nameOf_mem {c : Cfg} {i : Nat} (h : i < c.places.length) :
    nameOf c i ∈ c.places := by
  unfold nameOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

theorem nameOf_inj {c : Cfg} (hnd : c.places.Nodup) {i j : Nat}
    (hi : i < c.places.length) (hj : j < c.places.length)
    (h : nameOf c i = nameOf c j) : i = j := by
  unfold nameOf at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] at h
  exact (List.getElem_inj hnd).mp (by simpa using h)

/-- Reading one numbered fact as the atom it names. -/
theorem test_eq {t : Task} {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) {f : Fact} {a : GroundAtom}
    (hname : t.factNames.getD f default = a) (hrange : f < t.factNames.size) :
    s.test f = σ a := by
  rw [← hname]
  exact (habs.numbered f (by rw [hn]; exact hrange)).symm

/-! ### What each table must say -/

structure ChildMatch (t : Task) (c : Cfg) (ci : CChild) (k : Pddl.Name) : Prop where
  goalName : t.factNames.getD ci.goalFact default = served k
  goalRange : ci.goalFact < t.factNames.size
  allergic : ci.allergic = c.allergic k
  place : ci.place.map (nameOf c) = c.waitingAt k
  placeRange : ∀ i, ci.place = some i → i < c.places.length

structure SwMatch (t : Task) (c : Cfg) (si : CSw) (sw : Pddl.Name) : Prop where
  kitchenSome : ∀ f, si.kitchenFact = some f →
    t.factNames.getD f default = kitchenSw sw ∧ f < t.factNames.size
  /-- No fact for it means the atom is false wherever the search goes.  Stated of
  the states the task abstracts, which is all `ComputesOn` ever asks about. -/
  kitchenNone : si.kitchenFact = none →
    ∀ (s : State) (σ : AtomState), Abstracts t s σ → σ (kitchenSw sw) = false
  freeSome : ∀ f, si.glutenFreeFact = some f →
    t.factNames.getD f default = glutenFree sw ∧ f < t.factNames.size
  freeNone : si.glutenFreeFact = none →
    ∀ (s : State) (σ : AtomState), Abstracts t s σ → σ (glutenFree sw) = false
  onPairs : List.Forall₂ (fun f tr =>
    t.factNames.getD f default = ontray sw tr ∧ f < t.factNames.size)
    si.onTrayFacts.toList c.trays

structure TrayMatch (t : Task) (c : Cfg) (dd : CData)
    (x : Array (Fact × Nat) × Nat) (tr : Pddl.Name) : Prop where
  atNames : ∀ y ∈ x.1, t.factNames.getD y.1 default = atT tr (nameOf c y.2) ∧
    y.1 < t.factNames.size ∧ y.2 < c.places.length
  atOnto : ∀ q ∈ c.places, ∃ y ∈ x.1, nameOf c y.2 = q
  loadPairs : List.Forall₂ (fun f sw =>
    t.factNames.getD f default = ontray sw tr ∧ f < t.factNames.size)
    (dd.trayLoad.getD x.2 #[]).toList c.sandwiches

/-- The three tables read the same objects as the `Cfg`. -/
structure DataMatches (t : Task) (c : Cfg) (dd : CData) : Prop where
  plNd : c.places.Nodup
  children : List.Forall₂ (ChildMatch t c) dd.children.toList c.children
  sandwiches : List.Forall₂ (SwMatch t c) dd.sandwiches.toList c.sandwiches
  trays : List.Forall₂ (TrayMatch t c dd) dd.trayAt.zipIdx.toList c.trays
  kitchen : ∃ i, dd.kitchen = some i ∧ c.kitchen = some (nameOf c i) ∧
    i < c.places.length
  placeCount : dd.placeCount = c.places.length

/-! ### The children -/

theorem served_matches {t : Task} {c : Cfg} {ci : CChild} {k : Pddl.Name}
    (hc : ChildMatch t c ci k) {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) : s.test ci.goalFact = σ (served k) :=
  test_eq habs hn hc.goalName hc.goalRange

theorem unserved_pairs {t : Task} {c : Cfg} {dd : CData} (hm : DataMatches t c dd)
    {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) :
    List.Forall₂ (ChildMatch t c)
      (ExampleHeuristics.Childsnack.unservedChildren dd s).toList (unserved c σ) := by
  unfold ExampleHeuristics.Childsnack.unservedChildren unserved
  rw [Array.toList_filter]
  refine forall₂_filter hm.children fun ci k hc => ?_
  rw [served_matches hc habs hn]

theorem total_matches {t : Task} {c : Cfg} {dd : CData} (hm : DataMatches t c dd)
    {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Childsnack.total dd s = total c σ := by
  unfold ExampleHeuristics.Childsnack.total total
  rw [← Array.length_toList]
  exact (unserved_pairs hm habs hn).length_eq

theorem allergicLeft_matches {t : Task} {c : Cfg} {dd : CData} (hm : DataMatches t c dd)
    {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Childsnack.allergicLeft dd s = allergicLeft c σ := by
  unfold ExampleHeuristics.Childsnack.allergicLeft allergicLeft
  rw [← Array.length_toList, Array.toList_filter]
  exact (forall₂_filter (unserved_pairs hm habs hn) fun ci k hc => hc.allergic).length_eq

theorem waitingAt_matches {t : Task} {c : Cfg} {dd : CData} (hm : DataMatches t c dd)
    {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) {i : Nat} (hi : i < c.places.length) :
    ExampleHeuristics.Childsnack.waitingAt dd s i = waitingAtP c σ (nameOf c i) := by
  unfold ExampleHeuristics.Childsnack.waitingAt waitingAtP
  rw [← Array.length_toList, Array.toList_filter]
  refine (forall₂_filter (unserved_pairs hm habs hn) fun ci k hc => ?_).length_eq
  rcases hp : ci.place with _ | j
  · have := hc.place
    rw [hp] at this
    simp only [Option.map_none] at this
    rw [← this]; simp
  · have hcp := hc.place
    rw [hp] at hcp
    simp only [Option.map_some] at hcp
    rw [← hcp]
    by_cases hji : j = i
    · subst hji; simp
    · have hne : nameOf c j ≠ nameOf c i := fun hcc =>
        hji (nameOf_inj hm.plNd (hc.placeRange j hp) hi hcc)
      simp [hji, hne]

/-! ### The sandwiches -/

theorem onTray_matches {t : Task} {c : Cfg} {si : CSw} {sw : Pddl.Name}
    (hs : SwMatch t c si sw) {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Childsnack.onTray s si = onTray c σ sw := by
  unfold ExampleHeuristics.Childsnack.onTray onTray
  rw [← Array.any_toList]
  exact forall₂_any hs.onPairs fun f tr hr => test_eq habs hn hr.1 hr.2

theorem isFree_matches {t : Task} {c : Cfg} {si : CSw} {sw : Pddl.Name}
    (hs : SwMatch t c si sw) {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Childsnack.isFree s si = isFree σ sw := by
  unfold ExampleHeuristics.Childsnack.isFree isFree
  rcases hf : si.glutenFreeFact with _ | f
  · rw [hs.freeNone hf s σ habs]
  · obtain ⟨hname, hrange⟩ := hs.freeSome f hf
    exact test_eq habs hn hname hrange

theorem inKitchen_matches {t : Task} {c : Cfg} {si : CSw} {sw : Pddl.Name}
    (hs : SwMatch t c si sw) {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Childsnack.inKitchen s si = inKitchen c σ sw := by
  unfold ExampleHeuristics.Childsnack.inKitchen inKitchen
  rw [onTray_matches hs habs hn]
  congr 1
  rcases hf : si.kitchenFact with _ | f
  · rw [hs.kitchenNone hf s σ habs]
  · obtain ⟨hname, hrange⟩ := hs.kitchenSome f hf
    exact test_eq habs hn hname hrange

theorem trayAny_matches {t : Task} {c : Cfg} {dd : CData} (hm : DataMatches t c dd)
    {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Childsnack.trayAny dd s = trayAny c σ := by
  unfold ExampleHeuristics.Childsnack.trayAny trayAny
  rw [← Array.length_toList, Array.toList_filter]
  exact (forall₂_filter hm.sandwiches fun si sw hs =>
    onTray_matches hs habs hn).length_eq

theorem trayFree_matches {t : Task} {c : Cfg} {dd : CData} (hm : DataMatches t c dd)
    {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Childsnack.trayFree dd s = trayFree c σ := by
  unfold ExampleHeuristics.Childsnack.trayFree trayFree
  rw [← Array.length_toList, Array.toList_filter]
  refine (forall₂_filter hm.sandwiches fun si sw hs => ?_).length_eq
  rw [onTray_matches hs habs hn, isFree_matches hs habs hn]

theorem kitchenAny_matches {t : Task} {c : Cfg} {dd : CData} (hm : DataMatches t c dd)
    {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Childsnack.kitchenAny dd s = kitchenAny c σ := by
  unfold ExampleHeuristics.Childsnack.kitchenAny kitchenAny
  rw [← Array.length_toList, Array.toList_filter]
  exact (forall₂_filter hm.sandwiches fun si sw hs =>
    inKitchen_matches hs habs hn).length_eq

theorem kitchenFree_matches {t : Task} {c : Cfg} {dd : CData} (hm : DataMatches t c dd)
    {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Childsnack.kitchenFree dd s = kitchenFree c σ := by
  unfold ExampleHeuristics.Childsnack.kitchenFree kitchenFree
  rw [← Array.length_toList, Array.toList_filter]
  refine (forall₂_filter hm.sandwiches fun si sw hs => ?_).length_eq
  rw [inKitchen_matches hs habs hn, isFree_matches hs habs hn]

theorem shortfall_matches {t : Task} {c : Cfg} {dd : CData} (hm : DataMatches t c dd)
    {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Childsnack.shortfall dd s = shortfall c σ := by
  unfold ExampleHeuristics.Childsnack.shortfall shortfall
  rw [allergicLeft_matches hm habs hn, trayFree_matches hm habs hn,
    total_matches hm habs hn, trayAny_matches hm habs hn]

theorem toMake_matches {t : Task} {c : Cfg} {dd : CData} (hm : DataMatches t c dd)
    {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Childsnack.toMake dd s = toMake c σ := by
  unfold ExampleHeuristics.Childsnack.toMake toMake
  rw [allergicLeft_matches hm habs hn, trayFree_matches hm habs hn,
    kitchenFree_matches hm habs hn, shortfall_matches hm habs hn,
    kitchenAny_matches hm habs hn]

/-! ### The trays -/

/-- Where a tray stands, read compiled or lifted, is the same place. -/
theorem trayPlace_matches {t : Task} {c : Cfg} {dd : CData}
    {x : Array (Fact × Nat) × Nat} {tr : Pddl.Name} (hx : TrayMatch t c dd x tr)
    {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) (hinv : Inv σ) :
    (ExampleHeuristics.Childsnack.trayPlace dd s x.1).map (nameOf c)
      = trayPlace c σ tr := by
  unfold ExampleHeuristics.Childsnack.trayPlace
  rcases hfind : x.1.find? (fun y => s.test y.1) with _ | y
  · rw [hfind]
    simp only [Option.map_none]
    symm
    unfold trayPlace
    rw [List.find?_eq_none]
    intro q hq
    obtain ⟨z, hz, hzq⟩ := hx.atOnto q hq
    obtain ⟨hname, hrange, -⟩ := hx.atNames z hz
    have hfalse : s.test z.1 = false := by
      have := Array.find?_eq_none.mp hfind z hz
      simpa using this
    have hσ : σ (atT tr (nameOf c z.2)) = false := by
      rw [← test_eq habs hn hname hrange]; exact hfalse
    rw [hzq] at hσ
    simp [hσ]
  · rw [hfind]
    obtain ⟨hname, hrange, hidx⟩ := hx.atNames y (Array.mem_of_find?_eq_some hfind)
    have htrue : σ (atT tr (nameOf c y.2)) = true := by
      rw [← test_eq habs hn hname hrange]
      simpa using Array.find?_some hfind
    simp only [Option.map_some]
    exact (trayPlace_eq hinv (nameOf_mem hidx) htrue).symm

theorem trayPlace_range {t : Task} {c : Cfg} {dd : CData}
    {x : Array (Fact × Nat) × Nat} {tr : Pddl.Name} (hx : TrayMatch t c dd x tr)
    {s : State} {k : Nat}
    (h : ExampleHeuristics.Childsnack.trayPlace dd s x.1 = some k) :
    k < c.places.length := by
  unfold ExampleHeuristics.Childsnack.trayPlace at h
  rcases hfind : x.1.find? (fun y => s.test y.1) with _ | y
  · rw [hfind] at h; simp at h
  · rw [hfind] at h
    simp only [Option.map_some, Option.some.injEq] at h
    obtain ⟨-, -, hidx⟩ := hx.atNames y (Array.mem_of_find?_eq_some hfind)
    rw [← h]; exact hidx

/-- Asking whether a tray stands at an indexed place is the same question. -/
theorem trayPlace_at {t : Task} {c : Cfg} {dd : CData}
    (hnd : c.places.Nodup) {x : Array (Fact × Nat) × Nat} {tr : Pddl.Name}
    (hx : TrayMatch t c dd x tr) {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) (hinv : Inv σ) {i : Nat}
    (hi : i < c.places.length) :
    (ExampleHeuristics.Childsnack.trayPlace dd s x.1 == some i)
      = (trayPlace c σ tr == some (nameOf c i)) := by
  have hp := trayPlace_matches hx habs hn hinv
  rcases hf : ExampleHeuristics.Childsnack.trayPlace dd s x.1 with _ | j
  · rw [hf] at hp; simp only [Option.map_none] at hp
    rw [← hp]; simp
  · rw [hf] at hp; simp only [Option.map_some] at hp
    rw [← hp]
    have hjr := trayPlace_range hx hf
    by_cases hji : j = i
    · subst hji; simp
    · have hne : nameOf c j ≠ nameOf c i := fun hcc =>
        hji (nameOf_inj hnd hjr hi hcc)
      simp [hji, hne]

/-- How many sandwiches one tray carries. -/
theorem trayLoad_matches {t : Task} {c : Cfg} {dd : CData}
    {x : Array (Fact × Nat) × Nat} {tr : Pddl.Name} (hx : TrayMatch t c dd x tr)
    {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) :
    countHolding (dd.trayLoad.getD x.2 #[]) s = trayLoad c σ tr := by
  rw [countHolding_eq, ← Array.length_toList, Array.toList_filter]
  unfold trayLoad
  exact (forall₂_filter hx.loadPairs fun f sw hr =>
    test_eq habs hn hr.1 hr.2).length_eq

theorem loadedAt_matches {t : Task} {c : Cfg} {dd : CData} (hm : DataMatches t c dd)
    {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) (hinv : Inv σ) {i : Nat}
    (hi : i < c.places.length) :
    ExampleHeuristics.Childsnack.loadedAt dd s i = loadedAt c σ (nameOf c i) := by
  unfold ExampleHeuristics.Childsnack.loadedAt loadedAt
  rw [← Array.foldl_toList]
  rw [show (fun (acc : Nat) (x : Array (Fact × Nat) × Nat) =>
      if ExampleHeuristics.Childsnack.trayPlace dd s x.1 == some i then
        acc + countHolding (dd.trayLoad.getD x.2 #[]) s else acc)
    = (fun acc x => acc + (if ExampleHeuristics.Childsnack.trayPlace dd s x.1 == some i
        then countHolding (dd.trayLoad.getD x.2 #[]) s else 0)) from by
      funext acc x; split <;> simp]
  rw [foldl_add_eq_sum, Nat.zero_add, ← sum_filter_eq_ite]
  refine forall₂_map_sum (forall₂_filter hm.trays fun x tr hx => ?_) _ _
    fun x tr hx => trayLoad_matches hx habs hn
  exact trayPlace_at hm.plNd hx habs hn hinv hi

theorem trayInKitchen_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) (hinv : Inv σ) :
    ExampleHeuristics.Childsnack.trayInKitchen dd s = trayInKitchen c σ := by
  obtain ⟨ki, hdk, hck, hkr⟩ := hm.kitchen
  unfold ExampleHeuristics.Childsnack.trayInKitchen trayInKitchen
  rw [← Array.any_toList, ← any_zipIdx (fun y => ExampleHeuristics.Childsnack.trayPlace
    dd s y == dd.kitchen) dd.trayAt.toList 0, ← Array.toList_zipIdx]
  refine forall₂_any hm.trays fun x tr hx => ?_
  rw [hdk, hck]
  exact trayPlace_at hm.plNd hx habs hn hinv hkr

/-! ### The places that need a tray -/

theorem nameOf_surj {c : Cfg} {q : Pddl.Name} (hq : q ∈ c.places) :
    ∃ i, i < c.places.length ∧ nameOf c i = q := by
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hq
  refine ⟨i, hi, ?_⟩
  unfold nameOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  simpa using hget

theorem moveTargets_matches {t : Task} {c : Cfg} {dd : CData} (hm : DataMatches t c dd)
    {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) (hinv : Inv σ) :
    (ExampleHeuristics.Childsnack.moveTargets dd s).length
      = (moveTargets c σ).length := by
  obtain ⟨ki, hdk, hck, hkr⟩ := hm.kitchen
  have hpred : ∀ i, i < c.places.length →
      ((dd.kitchen != some i) &&
        decide (ExampleHeuristics.Childsnack.loadedAt dd s i
          < ExampleHeuristics.Childsnack.waitingAt dd s i))
      = ((c.kitchen != some (nameOf c i)) &&
        decide (loadedAt c σ (nameOf c i) < waitingAtP c σ (nameOf c i))) := by
    intro i hi
    have hb : (dd.kitchen != some i) = (c.kitchen != some (nameOf c i)) := by
      rw [hdk, hck]
      by_cases hki : ki = i
      · subst hki; simp
      · have hne : nameOf c ki ≠ nameOf c i := fun hcc =>
          hki (nameOf_inj hm.plNd hkr hi hcc)
        have h1 : (some ki != some i) = true := by simp [hki]
        have h2 : (some (nameOf c ki) != some (nameOf c i)) = true := by simp [hne]
        rw [h1, h2]
    rw [loadedAt_matches hm habs hn hinv hi, waitingAt_matches hm habs hn hi, hb]
  have hrange : ∀ i ∈ ExampleHeuristics.Childsnack.moveTargets dd s,
      i < c.places.length := by
    intro i hi
    unfold ExampleHeuristics.Childsnack.moveTargets at hi
    rw [List.mem_filter, List.mem_range] at hi
    rw [← hm.placeCount]; exact hi.1
  refine length_eq_of_naming _ _ (nameOf c)
    (List.nodup_range.filter _) (hm.plNd.filter _) ?_ ?_ ?_
  · intro i hi j hj hij
    exact nameOf_inj hm.plNd (hrange i hi) (hrange j hj) hij
  · intro i hi
    have hir := hrange i hi
    unfold ExampleHeuristics.Childsnack.moveTargets at hi
    rw [List.mem_filter] at hi
    unfold moveTargets
    rw [List.mem_filter]
    exact ⟨nameOf_mem hir, by rw [← hpred i hir]; exact hi.2⟩
  · intro q hq
    unfold moveTargets at hq
    rw [List.mem_filter] at hq
    obtain ⟨i, hir, rfl⟩ := nameOf_surj hq.1
    refine ⟨i, ?_, rfl⟩
    unfold ExampleHeuristics.Childsnack.moveTargets
    rw [List.mem_filter, List.mem_range]
    exact ⟨by rw [hm.placeCount]; exact hir, by rw [hpred i hir]; exact hq.2⟩

theorem moves_matches {t : Task} {c : Cfg} {dd : CData} (hm : DataMatches t c dd)
    {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) (hinv : Inv σ) :
    ExampleHeuristics.Childsnack.moves dd s = moves c σ := by
  unfold ExampleHeuristics.Childsnack.moves moves
  rw [moveTargets_matches hm habs hn hinv, shortfall_matches hm habs hn,
    trayInKitchen_matches hm habs hn hinv]

/-! ### `Computes`, for childsnack -/

/--
**The compiled childsnack heuristic computes the lifted one.**  All four
families, and the guard that stops the count once every child is served.
-/
theorem computes {t : Task} {c : Cfg} {dd : CData} (hm : DataMatches t c dd)
    (hn : t.numFacts = t.factNames.size) :
    ComputesOn t (fun σ => Inv σ) (ExampleHeuristics.Childsnack.value dd) (value c) := by
  intro s σ habs hinv
  show (if ExampleHeuristics.Childsnack.total dd s == 0 then 0
    else ExampleHeuristics.Childsnack.total dd s
      + ExampleHeuristics.Childsnack.shortfall dd s
      + ExampleHeuristics.Childsnack.toMake dd s
      + ExampleHeuristics.Childsnack.moves dd s) = _
  rw [total_matches hm habs hn, shortfall_matches hm habs hn,
    toMake_matches hm habs hn, moves_matches hm habs hn hinv]
  rfl

end Planner.Lifted.Childsnack

/- -------------------------------------------------------------------------- -/
/-
What `compile` produces for a childsnack task.

The third bridge, and the one with the most tables: children read off the goal,
sandwiches and trays read off the object lists, two static predicates
(`allergic_gluten`, `waiting`) read off `staticAtoms`, and one atom family —
`no_gluten_sandwich` — that a problem without gluten-free ingredients never
numbers at all.  `unnamed_false` covers that last case: the atom is not in
`:init` either, so it is false wherever the search goes.
-/

namespace Planner.Lifted.Childsnack

open Planner Planner.Pddl

/-! ### What one decidable pass over the problem establishes -/

/-- The children the goal asks to serve. -/
def goalKids (p : Problem) : List Name :=
  p.goal.filterMap fun a =>
    match a.pred == "served", a.args with
    | true, [k] => some k
    | _, _ => none

/-- The `at` atoms of `:init`, as (tray, place) pairs. -/
def atPairs (p : Problem) : List (Name × Name) :=
  p.init.filterMap fun a =>
    match a.pred == "at", a.args with
    | true, [t, q] => some (t, q)
    | _, _ => none

/-- The tray of every `ontray` atom of `:init`, per sandwich. -/
def onPairs (p : Problem) : List (Name × Name) :=
  p.init.filterMap fun a =>
    match a.pred == "ontray", a.args with
    | true, [sw, t] => some (sw, t)
    | _, _ => none

/-- The sandwiches `:init` declares not to exist. -/
def notexistSws (p : Problem) : List Name :=
  p.init.filterMap fun a =>
    match a.pred == "notexist", a.args with
    | true, [sw] => some sw
    | _, _ => none

/-- The sandwiches `:init` puts in the kitchen. -/
def kitchenSws (p : Problem) : List Name :=
  p.init.filterMap fun a =>
    match a.pred == "at_kitchen_sandwich", a.args with
    | true, [sw] => some sw
    | _, _ => none

/-- The gluten-free sandwiches `:init` declares. -/
def freeSws (p : Problem) : List Name :=
  p.init.filterMap fun a =>
    match a.pred == "no_gluten_sandwich", a.args with
    | true, [sw] => some sw
    | _, _ => none

/--
A tray stands in one place, a sandwich that does not exist is nowhere and is not
gluten free, one in the kitchen is on no tray, and one on a tray is on one tray.
-/
def initInvCheck (p : Problem) : Bool :=
  (atPairs p).all (fun x => (atPairs p).all fun y => !(x.1 == y.1) || x.2 == y.2) &&
  (notexistSws p).all (fun sw =>
    ((onPairs p).all fun x => x.1 != sw) && !(kitchenSws p).contains sw &&
      !(freeSws p).contains sw) &&
  (kitchenSws p).all (fun sw => (onPairs p).all fun x => x.1 != sw) &&
  (onPairs p).all fun x => (onPairs p).all fun y => !(x.1 == y.1) || x.2 == y.2

structure ChildsnackProblem (d : Domain) (p : Problem) : Prop where
  /-- The domain is childsnack, with its three static predicates. -/
  domain : ChildsnackPinned d
  swType : "sandwich" ∈ d.typeNames
  trType : "tray" ∈ d.typeNames
  plType : "place" ∈ d.typeNames
  chType : "child" ∈ d.typeNames
  brType : "bread-portion" ∈ d.typeNames
  coType : "content-portion" ∈ d.typeNames
  /-- Parser validation supplies shared facts such as object-name uniqueness. -/
  validated : Validated d p
  /-- The problem has a tray and a sandwich, so `put_on_tray` has an instance. -/
  someTray : ∃ o ∈ allObjects d p, o.type = "tray"
  someSw : ∃ o ∈ allObjects d p, o.type = "sandwich"
  /-- `kitchen` is a place. -/
  kitchenObj : ∃ o ∈ allObjects d p, o.name = "kitchen" ∧ o.type = "place"
  /-- Every goal atom asks for a child to be served. -/
  goalServed : ∀ a ∈ p.goal, ∃ k ∈ goalKids p, a = served k
  goalNodup : (goalKids p).Nodup
  /-- No object type used by the heuristic has a subtype among the objects. -/
  swExact : ∀ o ∈ allObjects d p, d.isSubtype o.type "sandwich" = true → o.type = "sandwich"
  trExact : ∀ o ∈ allObjects d p, d.isSubtype o.type "tray" = true → o.type = "tray"
  plExact : ∀ o ∈ allObjects d p, d.isSubtype o.type "place" = true → o.type = "place"
  /-- `:init` gives each child one place to wait at, a declared one. -/
  waitingUnique : ∀ a ∈ p.init, ∀ b ∈ p.init, a.pred = "waiting" → b.pred = "waiting" →
    a.args.head? = b.args.head? → a = b
  waitingTyped : ∀ a ∈ p.init, a.pred = "waiting" →
    ∃ o ∈ allObjects d p, a.args = [a.args.headD "", o.name] ∧ o.type = "place"
  /-- No child is both allergic and not. -/
  allergicSplit : ∀ a ∈ p.init, a.pred = "not_allergic_gluten" →
    ∀ b ∈ p.init, b.pred = "allergic_gluten" → a.args ≠ b.args
  /-- No sandwich exists yet, so none is declared gluten free. -/
  noFreeInit : ∀ a ∈ p.init, a.pred ≠ "no_gluten_sandwich"
  /-- Some child has to be served, and every goal child waits somewhere and has a
  declared allergy status. -/
  someGoal : goalKids p ≠ []
  goalChildTyped : ∀ k ∈ goalKids p, ∃ o ∈ allObjects d p, o.name = k ∧ o.type = "child"
  childServable : ∀ k ∈ goalKids p,
    (∃ a ∈ p.init, a.pred = "waiting" ∧ a.args.headD "" = k) ∧
    (allergicAtom k ∈ p.init ∨ notAllergicAtom k ∈ p.init)
  /-- `:init` satisfies the invariant the value reads positions under. -/
  initCheck : initInvCheck p = true

/-! ### The invariant on `:init`, decided -/

section InitMem

variable {p : Problem}

theorem mem_atPairs {t q : Name} : (t, q) ∈ atPairs p ↔ atT t q ∈ p.init := by
  constructor
  · intro h
    rw [atPairs, List.mem_filterMap] at h
    obtain ⟨a, ha, hval⟩ := h
    by_cases hpred : (a.pred == "at") = true
    · rcases hargs : a.args with _ | ⟨t', rest⟩
      · simp [hpred, hargs] at hval
      · cases rest with
        | nil => simp [hpred, hargs] at hval
        | cons q' rest' =>
            cases rest' with
            | cons _ _ => simp [hpred, hargs] at hval
            | nil =>
                simp only [hpred, hargs, Option.some.injEq, Prod.mk.injEq] at hval
                obtain ⟨e1, e2⟩ := hval
                have : a = atT t q := by
                  show a = { pred := "at", args := [t, q] }
                  rw [← e1, ← e2, ← hargs, ← (by simpa using hpred : a.pred = "at")]
                rwa [← this]
    · simp only [Bool.not_eq_true] at hpred
      simp [hpred] at hval
  · intro h
    exact List.mem_filterMap.mpr ⟨atT t q, h, by simp [atT]⟩

theorem mem_onPairs {sw t : Name} : (sw, t) ∈ onPairs p ↔ ontray sw t ∈ p.init := by
  constructor
  · intro h
    rw [onPairs, List.mem_filterMap] at h
    obtain ⟨a, ha, hval⟩ := h
    by_cases hpred : (a.pred == "ontray") = true
    · rcases hargs : a.args with _ | ⟨s', rest⟩
      · simp [hpred, hargs] at hval
      · cases rest with
        | nil => simp [hpred, hargs] at hval
        | cons t' rest' =>
            cases rest' with
            | cons _ _ => simp [hpred, hargs] at hval
            | nil =>
                simp only [hpred, hargs, Option.some.injEq, Prod.mk.injEq] at hval
                obtain ⟨e1, e2⟩ := hval
                have : a = ontray sw t := by
                  show a = { pred := "ontray", args := [sw, t] }
                  rw [← e1, ← e2, ← hargs, ← (by simpa using hpred : a.pred = "ontray")]
                rwa [← this]
    · simp only [Bool.not_eq_true] at hpred
      simp [hpred] at hval
  · intro h
    exact List.mem_filterMap.mpr ⟨ontray sw t, h, by simp [ontray]⟩

theorem mem_notexistSws {sw : Name} : sw ∈ notexistSws p ↔ notexist sw ∈ p.init := by
  constructor
  · intro h
    rw [notexistSws, List.mem_filterMap] at h
    obtain ⟨a, ha, hval⟩ := h
    by_cases hpred : (a.pred == "notexist") = true
    · rcases hargs : a.args with _ | ⟨s', rest⟩
      · simp [hpred, hargs] at hval
      · cases rest with
        | cons _ _ => simp [hpred, hargs] at hval
        | nil =>
            simp only [hpred, hargs, Option.some.injEq] at hval
            have : a = notexist sw := by
              show a = { pred := "notexist", args := [sw] }
              rw [← hval, ← hargs, ← (by simpa using hpred : a.pred = "notexist")]
            rwa [← this]
    · simp only [Bool.not_eq_true] at hpred
      simp [hpred] at hval
  · intro h
    exact List.mem_filterMap.mpr ⟨notexist sw, h, by simp [notexist]⟩

theorem mem_kitchenSws {sw : Name} : sw ∈ kitchenSws p ↔ kitchenSw sw ∈ p.init := by
  constructor
  · intro h
    rw [kitchenSws, List.mem_filterMap] at h
    obtain ⟨a, ha, hval⟩ := h
    by_cases hpred : (a.pred == "at_kitchen_sandwich") = true
    · rcases hargs : a.args with _ | ⟨s', rest⟩
      · simp [hpred, hargs] at hval
      · cases rest with
        | cons _ _ => simp [hpred, hargs] at hval
        | nil =>
            simp only [hpred, hargs, Option.some.injEq] at hval
            have : a = kitchenSw sw := by
              show a = { pred := "at_kitchen_sandwich", args := [sw] }
              rw [← hval, ← hargs,
                ← (by simpa using hpred : a.pred = "at_kitchen_sandwich")]
            rwa [← this]
    · simp only [Bool.not_eq_true] at hpred
      simp [hpred] at hval
  · intro h
    exact List.mem_filterMap.mpr ⟨kitchenSw sw, h, by simp [kitchenSw]⟩

theorem mem_freeSws {sw : Name} : sw ∈ freeSws p ↔ glutenFree sw ∈ p.init := by
  constructor
  · intro h
    rw [freeSws, List.mem_filterMap] at h
    obtain ⟨a, ha, hval⟩ := h
    by_cases hpred : (a.pred == "no_gluten_sandwich") = true
    · rcases hargs : a.args with _ | ⟨s', rest⟩
      · simp [hpred, hargs] at hval
      · cases rest with
        | cons _ _ => simp [hpred, hargs] at hval
        | nil =>
            simp only [hpred, hargs, Option.some.injEq] at hval
            have : a = glutenFree sw := by
              show a = { pred := "no_gluten_sandwich", args := [sw] }
              rw [← hval, ← hargs,
                ← (by simpa using hpred : a.pred = "no_gluten_sandwich")]
            rwa [← this]
    · simp only [Bool.not_eq_true] at hpred
      simp [hpred] at hval
  · intro h
    exact List.mem_filterMap.mpr ⟨glutenFree sw, h, by simp [glutenFree]⟩

end InitMem

theorem initInv_of_check {p : Problem} (h : initInvCheck p = true) :
    Inv (fun a => p.init.toArray.contains a) := by
  simp only [initInvCheck, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t q r hq hr
    have := h1 (t, q) (mem_atPairs.mpr (by simpa using hq))
    simpa using this (t, r) (mem_atPairs.mpr (by simpa using hr))
  · intro sw t hne
    rcases hc : (p.init.toArray.contains (ontray sw t)) with _ | _
    · rfl
    · exfalso
      have hn := h2 sw (mem_notexistSws.mpr (by simpa using hne))
      simp only [Bool.and_eq_true, List.all_eq_true] at hn
      have := hn.1.1 (sw, t) (mem_onPairs.mpr (by simpa using hc))
      simp at this
  · intro sw hne
    rcases hc : (p.init.toArray.contains (kitchenSw sw)) with _ | _
    · rfl
    · exfalso
      have hn := h2 sw (mem_notexistSws.mpr (by simpa using hne))
      simp only [Bool.and_eq_true] at hn
      have hk : sw ∈ kitchenSws p := mem_kitchenSws.mpr (by simpa using hc)
      have := hn.1.2
      simp only [Bool.not_eq_true'] at this
      rw [Bool.eq_false_iff] at this
      exact this (by simpa using hk)
  · intro sw hne
    rcases hc : (p.init.toArray.contains (glutenFree sw)) with _ | _
    · rfl
    · exfalso
      have hn := h2 sw (mem_notexistSws.mpr (by simpa using hne))
      simp only [Bool.and_eq_true] at hn
      have hk : sw ∈ freeSws p := mem_freeSws.mpr (by simpa using hc)
      have := hn.2
      simp only [Bool.not_eq_true'] at this
      rw [Bool.eq_false_iff] at this
      exact this (by simpa using hk)
  · intro sw t hk
    rcases hc : (p.init.toArray.contains (ontray sw t)) with _ | _
    · rfl
    · exfalso
      have := h3 sw (mem_kitchenSws.mpr (by simpa using hk))
      have := this (sw, t) (mem_onPairs.mpr (by simpa using hc))
      simp at this
  · intro sw t u ht hu
    have := h4 (sw, t) (mem_onPairs.mpr (by simpa using ht))
    simpa using this (sw, u) (mem_onPairs.mpr (by simpa using hu))

/-- What the tables need of the task: every atom the heuristic looks up has a
fact. -/
structure ChildsnackNumbered (d : Domain) (p : Problem) (rel : Bool) : Prop where
  kitchenF : ∀ sw, WellTyped d (allObjects d p) "sandwich" sw →
    ∃ n, n < (taskOf d p rel).numFacts ∧
      (taskOf d p rel).factNames.getD n default = kitchenSw sw
  ontrayF : ∀ sw tr, WellTyped d (allObjects d p) "sandwich" sw →
    WellTyped d (allObjects d p) "tray" tr →
    ∃ n, n < (taskOf d p rel).numFacts ∧
      (taskOf d p rel).factNames.getD n default = ontray sw tr
  atTF : ∀ tr q, WellTyped d (allObjects d p) "tray" tr →
    WellTyped d (allObjects d p) "place" q →
    ∃ n, n < (taskOf d p rel).numFacts ∧
      (taskOf d p rel).factNames.getD n default = atT tr q

/-! ### The `Cfg` the task describes -/

/-- The child a goal entry names, if it names one. -/
def kidEntry (t : Task) (x : GroundAtom × Nat) : Option Name :=
  match x.1.pred == "served", x.1.args with
  | true, [k] => some k
  | _, _ => none

/-- Where the task says a child waits. -/
def waitingOf (t : Task) (k : Name) : Option Name :=
  ((t.staticWith "waiting").find? fun b =>
      match b.args with
      | [y, _] => y == k
      | _ => false).bind fun b =>
    match b.args with
    | [_, q] => if ((objsOf t "place").findIdx? (· == q)).isSome then some q else none
    | _ => none

def cfgOf (t : Task) : Cfg where
  children := t.goalAtoms.zipIdx.toList.filterMap (kidEntry t)
  sandwiches := (objsOf t "sandwich").toList
  trays := (objsOf t "tray").toList
  places := (objsOf t "place").toList
  allergic := fun k => (t.staticWith "allergic_gluten").any fun b => b.args == [k]
  waitingAt := waitingOf t
  kitchen := some "kitchen"

theorem cfgOf_places (t : Task) : (cfgOf t).places = (objsOf t "place").toList := rfl
theorem cfgOf_trays (t : Task) : (cfgOf t).trays = (objsOf t "tray").toList := rfl
theorem cfgOf_sandwiches (t : Task) :
    (cfgOf t).sandwiches = (objsOf t "sandwich").toList := rfl

theorem nameOf_cfgOf (t : Task) (i : Nat) :
    nameOf (cfgOf t) i = (objsOf t "place").getD i "" := by
  unfold nameOf
  rw [cfgOf_places, List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?]
  simp

theorem placeIndex_sound {t : Task} {q : Name} {i : Nat}
    (h : (objsOf t "place").findIdx? (· == q) = some i) :
    i < (objsOf t "place").size ∧ nameOf (cfgOf t) i = q := by
  obtain ⟨hlt, hval⟩ := findIdx_sound h
  exact ⟨hlt, by rw [nameOf_cfgOf]; exact hval⟩

theorem cfgOf_children (d : Domain) (p : Problem) :
    (cfgOf (taskOf d p rel)).children = goalKids p := by
  show (taskOf d p rel).goalAtoms.zipIdx.toList.filterMap (kidEntry (taskOf d p rel)) = _
  rw [show (taskOf d p rel).goalAtoms.zipIdx.toList = p.goal.zipIdx 0 from by
    simp [taskOf_goalAtoms]]
  exact filterMap_zipIdx (fun a => kidEntry (taskOf d p rel) (a, 0)) p.goal 0

/-! ### The two schemas that number every atom the heuristic reads -/

def putInst {d : Domain} {p : Problem} (hd : ChildsnackDomain d) {sw tr : Name}
    (h1 : WellTyped d (allObjects d p) "sandwich" sw)
    (h2 : WellTyped d (allObjects d p) "tray" tr) : Instance d (allObjects d p) where
  schema := putA
  mem := by rw [hd]; simp
  args := [sw, tr]
  typed := List.Forall₂.cons h1 (List.Forall₂.cons h2 List.Forall₂.nil)

def moveInst {d : Domain} {p : Problem} (hd : ChildsnackDomain d) {tr q1 q2 : Name}
    (h1 : WellTyped d (allObjects d p) "tray" tr)
    (h2 : WellTyped d (allObjects d p) "place" q1)
    (h3 : WellTyped d (allObjects d p) "place" q2) : Instance d (allObjects d p) where
  schema := moveA
  mem := by rw [hd]; simp
  args := [tr, q1, q2]
  typed := List.Forall₂.cons h1 (List.Forall₂.cons h2 (List.Forall₂.cons h3 List.Forall₂.nil))

theorem put_named {d : Domain} {p : Problem} (hd : ChildsnackDomain d)
    (hsw : "sandwich" ∈ d.typeNames) (htr : "tray" ∈ d.typeNames) {sw tr : Name}
    (h1 : WellTyped d (allObjects d p) "sandwich" sw)
    (h2 : WellTyped d (allObjects d p) "tray" tr) {y : Atom}
    (hy : y ∈ putA.pre ∨ y ∈ putA.add ∨ y ∈ putA.del) :
    ∃ n, n < (taskOf d p false).numFacts ∧
      (taskOf d p false).factNames.getD n default = instAtom putA.params [sw, tr] y := by
  refine ground_names_instance d p (putInst (p := p) hd h1 h2) ?_ ?_ ?_
  · intro pm hpm
    have : pm = swP ∨ pm = trP "?t" := by simpa [putInst, putA] using hpm
    rcases this with rfl | rfl
    · exact hsw
    · exact htr
  · intro z hz hc
    have hz' : z = kitchenSwV "?s" ∨ z = atKitchenV "?t" := by simpa [putInst, putA] using hz
    rcases hz' with rfl | rfl
    · have h' : (staticPredicates d).contains "at_kitchen_sandwich" = true := hc
      rw [kitchenSw_dynamic hd] at h'; exact absurd h' (by simp)
    · have h' : (staticPredicates d).contains "at" = true := hc
      rw [at_dynamic hd] at h'; exact absurd h' (by simp)
  · rcases hy with h | h | h
    · refine Or.inl ⟨by simpa [putInst] using h, ?_⟩
      have hz' : y = kitchenSwV "?s" ∨ y = atKitchenV "?t" := by simpa [putA] using h
      rcases hz' with rfl | rfl
      · exact kitchenSw_dynamic hd
      · exact at_dynamic hd
    · exact Or.inr (Or.inl (by simpa [putInst] using h))
    · exact Or.inr (Or.inr (by simpa [putInst] using h))

theorem kitchenSw_named {d : Domain} {p : Problem} (hd : ChildsnackDomain d)
    (hsw : "sandwich" ∈ d.typeNames) (htr : "tray" ∈ d.typeNames) {sw tr : Name}
    (h1 : WellTyped d (allObjects d p) "sandwich" sw)
    (h2 : WellTyped d (allObjects d p) "tray" tr) :
    ∃ n, n < (taskOf d p false).numFacts ∧
      (taskOf d p false).factNames.getD n default = kitchenSw sw := by
  have h := put_named hd hsw htr h1 h2 (y := kitchenSwV "?s") (Or.inl (by simp [putA]))
  simpa [instAtom, putA, swP, trP, kitchenSwV, kitchenSw] using h

theorem ontray_named {d : Domain} {p : Problem} (hd : ChildsnackDomain d)
    (hsw : "sandwich" ∈ d.typeNames) (htr : "tray" ∈ d.typeNames) {sw tr : Name}
    (h1 : WellTyped d (allObjects d p) "sandwich" sw)
    (h2 : WellTyped d (allObjects d p) "tray" tr) :
    ∃ n, n < (taskOf d p false).numFacts ∧
      (taskOf d p false).factNames.getD n default = ontray sw tr := by
  have h := put_named hd hsw htr h1 h2 (y := ontrayV "?s" "?t")
    (Or.inr (Or.inl (by simp [putA])))
  simpa [instAtom, putA, swP, trP, ontrayV, ontray] using h

theorem atT_named {d : Domain} {p : Problem} (hd : ChildsnackDomain d)
    (htr : "tray" ∈ d.typeNames) (hpl : "place" ∈ d.typeNames) {tr q : Name}
    (h1 : WellTyped d (allObjects d p) "tray" tr)
    (h2 : WellTyped d (allObjects d p) "place" q) :
    ∃ n, n < (taskOf d p false).numFacts ∧
      (taskOf d p false).factNames.getD n default = atT tr q := by
  have h := ground_names_instance d p (moveInst (p := p) hd h1 h2 h2)
    (y := atV "?t" "?p1") ?_ ?_ ?_
  · simpa [moveInst, instAtom, moveA, trP, plP, atV, atT] using h
  · intro pm hpm
    have : pm = trP "?t" ∨ pm = plP "?p1" ∨ pm = plP "?p2" := by
      simpa [moveInst, moveA] using hpm
    rcases this with rfl | rfl | rfl
    · exact htr
    · exact hpl
    · exact hpl
  · intro z hz hc
    have hz' : z = atV "?t" "?p1" := by simpa [moveInst, moveA] using hz
    subst hz'
    have h' : (staticPredicates d).contains "at" = true := hc
    rw [at_dynamic hd] at h'; exact absurd h' (by simp)
  · exact Or.inl ⟨by simp [moveInst, moveA], at_dynamic hd⟩

/-! ### What `compile` returns, named -/

/-- The `ontray` fact for one sandwich on one tray, as `compile` looks it up. -/
abbrev onFactOf (t : Task) (sw tr : Name) : Option Fact :=
  ((t.factsWith "ontray").find? fun y => y.2.args == [sw, tr]).map (·.1)

theorem compile_children (t : Task) :
    (ExampleHeuristics.Childsnack.compile t).children
      = t.goalAtoms.zipIdx.filterMap
          (ExampleHeuristics.Childsnack.childEntry t (t.staticWith "allergic_gluten")
            (t.staticWith "waiting") (fun q => (objsOf t "place").findIdx? (· == q))) := rfl

theorem compile_sandwiches (t : Task) :
    (ExampleHeuristics.Childsnack.compile t).sandwiches
      = (objsOf t "sandwich").map fun sw =>
        { kitchenFact :=
            ((t.factsWith "at_kitchen_sandwich").find? fun y => y.2.args == [sw]).map (·.1)
          glutenFreeFact :=
            ((t.factsWith "no_gluten_sandwich").find? fun y => y.2.args == [sw]).map (·.1)
          onTrayFacts := (objsOf t "tray").filterMap (onFactOf t sw) } := rfl

theorem compile_trayAt (t : Task) :
    (ExampleHeuristics.Childsnack.compile t).trayAt
      = (objsOf t "tray").map fun tr =>
        (t.factsWith "at").filterMap fun y =>
          match y.2.args with
          | [x, q] =>
              if x == tr then ((objsOf t "place").findIdx? (· == q)).map ((y.1, ·)) else none
          | _ => none := rfl

theorem compile_trayLoad (t : Task) :
    (ExampleHeuristics.Childsnack.compile t).trayLoad
      = (objsOf t "tray").map fun tr => (objsOf t "sandwich").filterMap (onFactOf t · tr) := rfl

theorem compile_kitchen (t : Task) :
    (ExampleHeuristics.Childsnack.compile t).kitchen
      = (objsOf t "place").findIdx? (· == "kitchen") := rfl

theorem compile_placeCount (t : Task) :
    (ExampleHeuristics.Childsnack.compile t).placeCount = (objsOf t "place").size := rfl

theorem waitingOf_of_find {t : Task} {k : Name} {b : GroundAtom}
    (hfind : (t.staticWith "waiting").find? (fun b =>
      match b.args with
      | [y, _] => y == k
      | _ => false) = some b) :
    waitingOf t k = (match b.args with
      | [_, q] => if ((objsOf t "place").findIdx? (· == q)).isSome then some q else none
      | _ => none) := by
  rw [waitingOf, hfind]; rfl

/-! ### The tables -/

section Match

variable {d : Domain} {p : Problem} {rel : Bool} (hp : ChildsnackProblem d p)
  (hn : ChildsnackNumbered d p rel)

include hp

theorem some_tray : ∃ tr, WellTyped d (allObjects d p) "tray" tr := by
  obtain ⟨o, ho, ht⟩ := hp.someTray
  exact ⟨o.name, wellTyped_of_type ho ht⟩

theorem some_sw : ∃ sw, WellTyped d (allObjects d p) "sandwich" sw := by
  obtain ⟨o, ho, ht⟩ := hp.someSw
  exact ⟨o.name, wellTyped_of_type ho ht⟩

theorem kitchen_place : "kitchen" ∈ objsOf (taskOf d p rel) "place" := by
  obtain ⟨o, ho, hn, ht⟩ := hp.kitchenObj
  exact mem_objsOf ho hn ht

/-- With pruning off, grounding completeness numbers all three atom families. -/
theorem childsnackNumbered_false : ChildsnackNumbered d p false := by
  obtain ⟨tr0, htr0⟩ := some_tray hp
  exact ⟨fun sw hsw => kitchenSw_named hp.domain.actions hp.swType hp.trType hsw htr0,
    fun sw tr hsw htr => ontray_named hp.domain.actions hp.swType hp.trType hsw htr,
    fun tr q htr hq => atT_named hp.domain.actions hp.trType hp.plType htr hq⟩

include hn in
/-- The `ontray` lookup always succeeds, and names the atom it was asked for. -/
theorem onFact_some {sw tr : Name}
    (hsw : WellTyped d (allObjects d p) "sandwich" sw)
    (htr : WellTyped d (allObjects d p) "tray" tr) :
    ∃ f, onFactOf (taskOf d p rel) sw tr = some f ∧
      (taskOf d p rel).factNames.getD f default = ontray sw tr ∧
      f < (taskOf d p rel).factNames.size := by
  obtain ⟨n, hlt, hname⟩ :=
    hn.ontrayF sw tr hsw htr
  have hmem : (n, ontray sw tr) ∈ (taskOf d p rel).factsWith "ontray" :=
    mem_factsWith_of_named (by rwa [← taskOf_numFacts]) hname rfl
  rcases hfind : (((taskOf d p rel).factsWith "ontray").find?
      fun y => y.2.args == [sw, tr]) with _ | z
  · rw [Array.find?_eq_none] at hfind
    exact absurd (hfind _ hmem) (by simp [ontray])
  · refine ⟨z.1, by simp [onFactOf, hfind], ?_, ?_⟩
    · have := factsWith_find_args_map (t := taskOf d p rel) (pred := "ontray")
        (args := [sw, tr]) (f := z.1) (by simp [hfind])
      rw [this]; rfl
    · exact (mem_factsWith (Array.mem_of_find?_eq_some hfind)).1

/-! ### The sandwiches -/

include hn in
theorem swMatch {sw : Name} (hsw : sw ∈ objsOf (taskOf d p rel) "sandwich") :
    SwMatch (taskOf d p rel) (cfgOf (taskOf d p rel))
      { kitchenFact := (((taskOf d p rel).factsWith "at_kitchen_sandwich").find?
          fun y => y.2.args == [sw]).map (·.1)
        glutenFreeFact := (((taskOf d p rel).factsWith "no_gluten_sandwich").find?
          fun y => y.2.args == [sw]).map (·.1)
        onTrayFacts := (objsOf (taskOf d p rel) "tray").filterMap (onFactOf (taskOf d p rel) sw) }
      sw := by
  have hswT : WellTyped d (allObjects d p) "sandwich" sw := objsOf_wellTyped hsw
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f hf
    refine ⟨by rw [factsWith_find_args_map hf]; rfl, ?_⟩
    rcases hfind : (((taskOf d p rel).factsWith "at_kitchen_sandwich").find?
        fun y => y.2.args == [sw]) with _ | z
    · rw [hfind] at hf; simp at hf
    · rw [hfind] at hf
      simp only [Option.map_some, Option.some.injEq] at hf
      subst hf
      exact (mem_factsWith (Array.mem_of_find?_eq_some hfind)).1
  · -- a sandwich always has a kitchen fact, because `put_on_tray` reads one
    intro hnone
    obtain ⟨tr, htr⟩ := some_tray hp
    obtain ⟨n, hlt, hname⟩ :=
      hn.kitchenF sw hswT
    have hmem : (n, kitchenSw sw) ∈ (taskOf d p rel).factsWith "at_kitchen_sandwich" :=
      mem_factsWith_of_named (by rwa [← taskOf_numFacts]) hname rfl
    rcases hfind : (((taskOf d p rel).factsWith "at_kitchen_sandwich").find?
        fun y => y.2.args == [sw]) with _ | z
    · rw [Array.find?_eq_none] at hfind
      exact absurd (hfind _ hmem) (by simp [kitchenSw])
    · rw [hfind] at hnone; simp at hnone
  · intro f hf
    refine ⟨by rw [factsWith_find_args_map hf]; rfl, ?_⟩
    rcases hfind : (((taskOf d p rel).factsWith "no_gluten_sandwich").find?
        fun y => y.2.args == [sw]) with _ | z
    · rw [hfind] at hf; simp at hf
    · rw [hfind] at hf
      simp only [Option.map_some, Option.some.injEq] at hf
      subst hf
      exact (mem_factsWith (Array.mem_of_find?_eq_some hfind)).1
  · -- no fact, so the atom was never numbered, and `:init` does not hold it
    intro hnone s σ habs
    refine unnamed_false d p rel habs ?_ ?_
    · intro f hflt hname
      have hmem : (f, glutenFree sw) ∈ (taskOf d p rel).factsWith "no_gluten_sandwich" :=
        mem_factsWith_of_named (by rwa [taskOf_numFacts] at hflt) hname rfl
      rcases hfind : (((taskOf d p rel).factsWith "no_gluten_sandwich").find?
          fun y => y.2.args == [sw]) with _ | z
      · rw [Array.find?_eq_none] at hfind
        exact absurd (hfind _ hmem) (by simp [glutenFree])
      · rw [hfind] at hnone; simp at hnone
    · intro hc
      exact hp.noFreeInit _ hc rfl
  · show List.Forall₂ _ ((objsOf (taskOf d p rel) "tray").filterMap
      (onFactOf (taskOf d p rel) sw)).toList _
    rw [Array.toList_filterMap]
    refine forall₂_filterMap_total _ ?_
    intro tr htr
    obtain ⟨f, hf, hname, hrange⟩ :=
      onFact_some hp hn hswT (objsOf_wellTyped (by simpa using htr))
    exact ⟨f, hf, hname, hrange⟩

/-! ### The trays -/

include hn in
theorem trayMatch {tr : Name} {i : Nat} (htr : tr ∈ objsOf (taskOf d p rel) "tray")
    (hi : i < (objsOf (taskOf d p rel) "tray").size)
    (hit : (objsOf (taskOf d p rel) "tray")[i]'hi = tr) :
    TrayMatch (taskOf d p rel) (cfgOf (taskOf d p rel))
      (ExampleHeuristics.Childsnack.compile (taskOf d p rel))
      ((((taskOf d p rel).factsWith "at").filterMap fun y =>
          match y.2.args with
          | [x, q] =>
              if x == tr then
                ((objsOf (taskOf d p rel) "place").findIdx? (· == q)).map ((y.1, ·))
              else none
          | _ => none), i) tr := by
  have htrT : WellTyped d (allObjects d p) "tray" tr := objsOf_wellTyped htr
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    rw [Array.mem_filterMap] at hy
    obtain ⟨z, hz, hval⟩ := hy
    obtain ⟨hzr, hzn, hzp⟩ := mem_factsWith hz
    rcases hza : z.2.args with _ | ⟨c1, rest⟩
    · rw [hza] at hval; simp at hval
    · cases rest with
      | nil => rw [hza] at hval; simp at hval
      | cons q rest' =>
          cases rest' with
          | cons _ _ => rw [hza] at hval; simp at hval
          | nil =>
              rw [hza] at hval
              dsimp only at hval
              by_cases hc1 : (c1 == tr) = true
              · rw [if_pos hc1] at hval
                rcases hj : (objsOf (taskOf d p rel) "place").findIdx? (· == q) with _ | j
                · rw [hj] at hval; simp at hval
                · rw [hj] at hval
                  simp only [Option.map_some, Option.some.injEq] at hval
                  subst hval
                  obtain ⟨hjl, hjn⟩ := placeIndex_sound hj
                  refine ⟨?_, hzr, ?_⟩
                  · rw [hzn, hjn]
                    show z.2 = { pred := "at", args := [tr, q] }
                    rw [(by simpa using hc1 : c1 = tr)] at hza
                    rw [← hzp, ← hza]
                  · rw [cfgOf_places]; simpa using hjl
              · rw [if_neg hc1] at hval; simp at hval
  · intro q hq
    rw [cfgOf_places] at hq
    have hqm : q ∈ objsOf (taskOf d p rel) "place" := by simpa using hq
    obtain ⟨n, hnlt, hnname⟩ :=
      hn.atTF tr q htrT (objsOf_wellTyped hqm)
    obtain ⟨j, hj⟩ := findIdx_total hqm
    refine ⟨(n, j), ?_, (placeIndex_sound hj).2⟩
    rw [Array.mem_filterMap]
    refine ⟨(n, atT tr q),
      mem_factsWith_of_named (by rwa [← taskOf_numFacts]) hnname rfl, ?_⟩
    simp [atT, hj]
  · have hload : (ExampleHeuristics.Childsnack.compile (taskOf d p rel)).trayLoad.getD i #[]
        = (objsOf (taskOf d p rel) "sandwich").filterMap (onFactOf (taskOf d p rel) · tr) := by
      rw [compile_trayLoad, Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem (by simpa using hi)]
      simp only [Option.getD_some, Array.getElem_map, hit]
    rw [hload, cfgOf_sandwiches, Array.toList_filterMap]
    refine forall₂_filterMap_total _ ?_
    intro sw hsw
    obtain ⟨f, hf, hname, hrange⟩ :=
      onFact_some hp hn (objsOf_wellTyped (by simpa using hsw)) htrT
    exact ⟨f, hf, hname, hrange⟩

/-! ### The children -/

include hn in
theorem childMatch {x : GroundAtom × Nat} {k : Name}
    (hx : x ∈ (taskOf d p rel).goalAtoms.zipIdx)
    (hpred : x.1.pred = "served") (hargs : x.1.args = [k]) :
    ChildMatch (taskOf d p rel) (cfgOf (taskOf d p rel))
      { goalFact := (taskOf d p rel).goal.getD x.2 0
        allergic := ((taskOf d p rel).staticWith "allergic_gluten").any
          fun b => b.args == [k]
        place := (((taskOf d p rel).staticWith "waiting").find? fun b =>
          match b.args with
          | [y, _] => y == k
          | _ => false).bind fun b =>
            match b.args with
            | [_, q] => (objsOf (taskOf d p rel) "place").findIdx? (· == q)
            | _ => none }
      k := by
  have hget : (taskOf d p rel).goalAtoms[x.2]? = some x.1 := Array.mem_zipIdx_iff_getElem?.mp hx
  have hlt : x.2 < (taskOf d p rel).goalAtoms.size := by
    by_contra hc
    rw [Array.getElem?_eq_none (by omega)] at hget
    simp at hget
  have hatom : (taskOf d p rel).goalAtoms[x.2]'hlt = served k := by
    rw [Array.getElem?_eq_getElem hlt] at hget
    have hs : x.1 = served k := by
      show x.1 = { pred := "served", args := [k] }
      rw [← hpred, ← hargs]
    rw [← hs]; simpa using hget
  obtain ⟨hname, hrange⟩ := goal_name_eq d p rel hlt
  refine ⟨by rw [hname, hatom], hrange, rfl, ?_, ?_⟩
  · show Option.map _ _ = waitingOf (taskOf d p rel) k
    rcases hfind : (((taskOf d p rel).staticWith "waiting").find? fun b =>
        match b.args with
        | [y, _] => y == k
        | _ => false) with _ | b
    · rw [hfind, waitingOf, hfind]; rfl
    · rw [hfind, waitingOf_of_find hfind]
      simp only [Option.bind_some]
      rcases hba : b.args with _ | ⟨y, rest⟩
      · rfl
      · cases rest with
        | nil => rfl
        | cons q rest' =>
            cases rest' with
            | cons _ _ => rfl
            | nil =>
                dsimp only
                rcases hj : (objsOf (taskOf d p rel) "place").findIdx? (· == q) with _ | j
                · simp [hj]
                · rw [if_pos (by simp)]
                  simp only [Option.map_some, Option.some.injEq]
                  exact (placeIndex_sound hj).2
  · intro i hi
    rcases hfind : (((taskOf d p rel).staticWith "waiting").find? fun b =>
        match b.args with
        | [y, _] => y == k
        | _ => false) with _ | b
    · rw [hfind] at hi; simp at hi
    · rw [hfind] at hi
      simp only [Option.bind_some] at hi
      revert hi
      rcases hba : b.args with _ | ⟨y, rest⟩
      · intro hi; simp at hi
      · cases rest with
        | nil => intro hi; simp at hi
        | cons q rest' =>
            cases rest' with
            | cons _ _ => intro hi; simp at hi
            | nil =>
                intro hi
                dsimp only at hi
                rw [cfgOf_places]
                simpa using (placeIndex_sound hi).1

/-! ### The three tables together -/

include hn in
theorem dataMatches :
    DataMatches (taskOf d p rel) (cfgOf (taskOf d p rel))
      (ExampleHeuristics.Childsnack.compile (taskOf d p rel)) := by
  refine ⟨by rw [cfgOf_places]; exact objsOf_nodup hp.validated.namesNodup,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [compile_children, Array.toList_filterMap]
    show List.Forall₂ _ _ ((taskOf d p rel).goalAtoms.zipIdx.toList.filterMap
      (kidEntry (taskOf d p rel)))
    refine forall₂_filterMap _ ?_
    intro x hx
    by_cases hpred : (x.1.pred == "served") = true
    · rcases hargs : x.1.args with _ | ⟨k, rest⟩
      · exact ⟨fun ci hci => by
          simp [ExampleHeuristics.Childsnack.childEntry, hpred, hargs] at hci,
        fun _ => by simp [kidEntry, hpred, hargs]⟩
      · cases rest with
        | cons _ _ =>
            exact ⟨fun ci hci => by
              simp [ExampleHeuristics.Childsnack.childEntry, hpred, hargs] at hci,
            fun _ => by simp [kidEntry, hpred, hargs]⟩
        | nil =>
            refine ⟨fun ci hci => ⟨k, by simp [kidEntry, hpred, hargs], ?_⟩, fun hn => ?_⟩
            · simp only [ExampleHeuristics.Childsnack.childEntry, hpred, hargs,
                Option.some.injEq] at hci
              rw [← hci]
              exact childMatch hp hn (Array.mem_def.mpr (by simpa using hx))
                (by simpa using hpred) hargs
            · simp [ExampleHeuristics.Childsnack.childEntry, hpred, hargs] at hn
    · simp only [Bool.not_eq_true] at hpred
      exact ⟨fun ci hci => by
        simp [ExampleHeuristics.Childsnack.childEntry, hpred] at hci,
      fun _ => by simp [kidEntry, hpred]⟩
  · rw [compile_sandwiches, Array.toList_map, cfgOf_sandwiches]
    exact forall₂_map_left _ fun sw hsw => swMatch hp hn (by simpa using hsw)
  · rw [compile_trayAt, cfgOf_trays]
    simp only [Array.toList_zipIdx, Array.toList_map]
    refine forall₂_map_zipIdx _ 0 ?_
    intro i hi
    have hlt : i < (objsOf (taskOf d p rel) "tray").size := by simpa using hi
    have heq : (objsOf (taskOf d p rel) "tray").toList[i]'hi
        = (objsOf (taskOf d p rel) "tray")[i]'hlt := by simp
    rw [Nat.zero_add, heq]
    exact trayMatch hp hn (Array.getElem_mem hlt) hlt rfl
  · obtain ⟨i, hi⟩ := findIdx_total (kitchen_place hp)
    refine ⟨i, by rw [compile_kitchen]; exact hi, ?_, ?_⟩
    · show (some "kitchen" : Option Name) = some (nameOf (cfgOf (taskOf d p rel)) i)
      rw [(placeIndex_sound hi).2]
    · rw [cfgOf_places]; simpa using (placeIndex_sound hi).1
  · rw [compile_placeCount, cfgOf_places]; simp

/-! ### The configuration is the one the lifted proof asks for -/

theorem goal_of_goalKids {k : Name} (hk : k ∈ goalKids p) : served k ∈ p.goal := by
  rw [goalKids, List.mem_filterMap] at hk
  obtain ⟨a, ha, hval⟩ := hk
  by_cases hpred : (a.pred == "served") = true
  · rcases hargs : a.args with _ | ⟨k', rest⟩
    · simp [hpred, hargs] at hval
    · cases rest with
      | cons _ _ => simp [hpred, hargs] at hval
      | nil =>
          simp only [hpred, hargs, Option.some.injEq] at hval
          have : a = served k := by
            show a = { pred := "served", args := [k] }
            rw [← hval, ← hargs, ← (by simpa using hpred : a.pred = "served")]
          rwa [← this]
  · simp only [Bool.not_eq_true] at hpred
    simp [hpred] at hval

/-- A static atom of `:init` that is not a goal atom is in `staticWith`. -/
theorem static_mem {a : GroundAtom} (hinit : a ∈ p.init)
    (hst : (staticPredicates d).contains a.pred = true) (hne : a.pred ≠ "served") :
    a ∈ (taskOf d p rel).staticWith a.pred := by
  refine mem_staticWith d p rel hinit ?_ rfl
  intro hmem
  obtain ⟨k, -, hk⟩ := hp.goalServed _ (mem_goal_of_static d p rel hmem hst)
  exact hne (by rw [hk]; rfl)

theorem cfgOK : CfgOK d p (cfgOf (taskOf d p rel)) := by
  refine ⟨by rw [cfgOf_sandwiches]; exact objsOf_nodup hp.validated.namesNodup,
    by rw [cfgOf_children]; exact hp.goalNodup,
    by rw [cfgOf_trays]; exact objsOf_nodup hp.validated.namesNodup,
    by rw [cfgOf_places]; exact objsOf_nodup hp.validated.namesNodup,
    ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨o, ho, hn, hs⟩ := hx
    rw [cfgOf_sandwiches]
    simpa using (mem_objsOf ho hn (hp.swExact o ho hs) : x ∈ objsOf (taskOf d p rel) "sandwich")
  · intro x hx
    obtain ⟨o, ho, hn, hs⟩ := hx
    rw [cfgOf_trays]
    simpa using (mem_objsOf ho hn (hp.trExact o ho hs) : x ∈ objsOf (taskOf d p rel) "tray")
  · intro x hx
    obtain ⟨o, ho, hn, hs⟩ := hx
    rw [cfgOf_places]
    simpa using (mem_objsOf ho hn (hp.plExact o ho hs) : x ∈ objsOf (taskOf d p rel) "place")
  · rw [cfgOf_places]; simpa using kitchen_place hp
  · -- `waiting` is static, so the whole of it survives in `staticAtoms`
    intro x q hcon
    have hinit : waitingAtom x q ∈ p.init := by simpa using hcon
    have hst : waitingAtom x q ∈ (taskOf d p rel).staticWith "waiting" :=
      static_mem hp hinit (by simpa [waitingAtom] using hp.domain.waitingStatic)
        (by simp [waitingAtom])
    obtain ⟨o, ho, hargs, hty⟩ := hp.waitingTyped _ hinit rfl
    have hoq : q = o.name := by simpa [waitingAtom] using hargs
    have hqm : q ∈ objsOf (taskOf d p rel) "place" := mem_objsOf ho hoq.symm hty
    obtain ⟨j, hj⟩ := findIdx_total hqm
    rcases hfind : (((taskOf d p rel).staticWith "waiting").find? fun b =>
        match b.args with
        | [y, _] => y == x
        | _ => false) with _ | b
    · rw [Array.find?_eq_none] at hfind
      exact absurd (hfind _ hst) (by simp [waitingAtom])
    · have hbmem := Array.mem_of_find?_eq_some hfind
      have hbp := Array.find?_some hfind
      obtain ⟨hbinit, hbpred⟩ := staticWith_sub d p rel hbmem
      have hbq : b.args.head? = some x := by
        rcases hba : b.args with _ | ⟨y, rest⟩
        · rw [hba] at hbp; simp at hbp
        · cases rest with
          | nil => rw [hba] at hbp; simp at hbp
          | cons _ rest' =>
              cases rest' with
              | cons _ _ => rw [hba] at hbp; simp at hbp
              | nil =>
                  rw [hba] at hbp
                  simp only [List.head?_cons, Option.some.injEq]
                  simpa using hbp
      have hbeq : b = waitingAtom x q :=
        hp.waitingUnique b hbinit _ hinit hbpred rfl (by rw [hbq]; simp [waitingAtom])
      show waitingOf (taskOf d p rel) x = some q
      rw [waitingOf_of_find hfind, hbeq]
      show (if ((objsOf (taskOf d p rel) "place").findIdx? (· == q)).isSome then some q
        else none) = some q
      rw [if_pos (by rw [hj]; simp)]
  · intro x hcon
    have hinit : allergicAtom x ∈ p.init := by simpa using hcon
    have hst : allergicAtom x ∈ (taskOf d p rel).staticWith "allergic_gluten" :=
      static_mem hp hinit (by simpa [allergicAtom] using hp.domain.allergicStatic)
        (by simp [allergicAtom])
    show ((taskOf d p rel).staticWith "allergic_gluten").any (fun b => b.args == [x]) = true
    rw [← Array.any_toList]
    exact List.any_eq_true.mpr ⟨allergicAtom x, by simpa using hst, by simp [allergicAtom]⟩
  · intro x hcon
    have hinit : notAllergicAtom x ∈ p.init := by simpa using hcon
    show ((taskOf d p rel).staticWith "allergic_gluten").any (fun b => b.args == [x]) = false
    rw [Bool.eq_false_iff]
    intro hany
    rw [← Array.any_toList] at hany
    obtain ⟨b, hb', hbargs⟩ := List.any_eq_true.mp hany
    have hb : b ∈ (taskOf d p rel).staticWith "allergic_gluten" := by simpa using hb'
    obtain ⟨hbinit, hbpred⟩ := staticWith_sub d p rel hb
    have hbeq : b = allergicAtom x := by
      show b = { pred := "allergic_gluten", args := [x] }
      rw [← hbpred, ← (by simpa using hbargs : b.args = [x])]
    exact hp.allergicSplit _ hinit rfl b hbinit hbpred
      (by rw [hbeq]; simp [notAllergicAtom, allergicAtom])

theorem served_sub : ∀ k ∈ (cfgOf (taskOf d p rel)).children, served k ∈ p.goal := by
  intro k hk
  rw [cfgOf_children] at hk
  exact goal_of_goalKids hp hk

/-! ### Childsnack, end to end -/

theorem opFacts_all : ∀ o ∈ groundedOps d p rel, Nonempty (OpFacts d p o) :=
  fun o ho => opFacts_ground d p rel ho

set_option maxHeartbeats 1000000 in
theorem cost_pos : ∀ o ∈ groundedOps d p rel, 0 < o.cost := by
  intro o ho
  obtain ⟨f⟩ := opFacts_all hp o ho
  rw [f.cost]
  show 0 < f.inst.schema.cost
  have hmem : f.inst.schema ∈ [makeNGA, makeA, putA, serveNGA, serveA, moveA] :=
    hp.domain.actions ▸ f.inst.mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h <;> rw [h] <;>
    simp [makeNGA, makeA, putA, serveNGA, serveA, moveA]

include hn in
set_option maxHeartbeats 1000000 in
/-- **Childsnack's improved heuristic is goal-aware on the task the planner
searches.** -/
theorem improved_goalAware :
    (ground d p rel).GoalAwareOn (Reachable (ground d p rel))
      (ExampleHeuristics.Childsnack.improved (ground d p rel)).eval :=
  improved_goalAwareOn d p rel (cfgOf (taskOf d p rel)) hp.domain (cfgOK hp)
    (ground_wf d p rel (cost_pos hp)) (cost_pos hp) (opFacts_all hp)
    (served_sub hp) (initInv_of_check hp.initCheck) _
    (computes (dataMatches hp hn) rfl)

include hn in
set_option maxHeartbeats 1000000 in
/-- **Childsnack's improved heuristic is consistent on the task the planner
searches.** -/
theorem improved_consistent :
    (ground d p rel).ConsistentOn (Reachable (ground d p rel))
      (ExampleHeuristics.Childsnack.improved (ground d p rel)).eval :=
  improved_consistentOn d p rel (cfgOf (taskOf d p rel)) hp.domain (cfgOK hp)
    (ground_wf d p rel (cost_pos hp)) (cost_pos hp) (opFacts_all hp)
    (initInv_of_check hp.initCheck) _
    (computes (dataMatches hp hn) rfl)

include hn in
set_option maxHeartbeats 1000000 in
/--
**Childsnack's improved heuristic is admissible on the task the planner searches.**
-/
theorem improved_admissible :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel))
      (ExampleHeuristics.Childsnack.improved (ground d p rel)).eval :=
  improved_admissibleOn d p rel (cfgOf (taskOf d p rel)) hp.domain (cfgOK hp)
    (ground_wf d p rel (cost_pos hp)) (cost_pos hp) (opFacts_all hp)
    (served_sub hp) (initInv_of_check hp.initCheck) _
    (computes (dataMatches hp hn) rfl)

end Match

/-! ### With the relevance analysis on

Childsnack's chain has three steps.  A child's `served` goal is relevant, and the
`serve` that would meet it adds that goal atom, so it survives and closure puts
`ontray` and `at` in the set.  Every `put_on_tray` then adds a relevant `ontray`,
which brings `at_kitchen_sandwich` in, and every `move_tray` adds a relevant `at`,
which brings the rest of the places in.
-/

section Pruned

variable {d : Domain} {p : Problem} (hp : ChildsnackProblem d p)

private abbrev rset : Std.HashSet GroundAtom := relevantSet (rawOps d p) p.goal.toArray

private theorem serveNGA_nopre : ∀ z ∈ serveNGA.pre, z.pred ≠ "served" := by
  intro z hz
  have hz' : z = allergicV "?c" ∨ z = ontrayV "?s" "?t" ∨ z = waitingV "?c" "?p" ∨
      z = glutenFreeV "?s" ∨ z = atV "?t" "?p" := by simpa [serveNGA] using hz
  rcases hz' with rfl | rfl | rfl | rfl | rfl <;>
    simp [allergicV, ontrayV, waitingV, glutenFreeV, atV]

private theorem serveA_nopre : ∀ z ∈ serveA.pre, z.pred ≠ "served" := by
  intro z hz
  have hz' : z = notAllergicV "?c" ∨ z = waitingV "?c" "?p" ∨ z = ontrayV "?s" "?t" ∨
      z = atV "?t" "?p" := by simpa [serveA] using hz
  rcases hz' with rfl | rfl | rfl | rfl <;> simp [notAllergicV, ontrayV, waitingV, atV]

private theorem touches_of_add {o : AtomOp} {r : Std.HashSet GroundAtom} {x : GroundAtom}
    (hx : x ∈ o.add) (hr : r.contains x = true) : o.touches r = true := by
  simp only [AtomOp.touches, Bool.or_eq_true, Array.any_eq_true]
  obtain ⟨i, hi, hval⟩ := Array.getElem_of_mem hx
  exact Or.inl ⟨i, hi, by rw [hval]; exact hr⟩

include hp

/-- Every parameter of a childsnack schema has a declared type the heuristic
indexes, or one it does not read. -/
private theorem inst_hty' (i : Instance d (allObjects d p)) :
    ∀ pm ∈ i.schema.params, pm.type ∈ d.typeNames := by
  intro pm hpm
  have hmem : i.schema ∈ [makeNGA, makeA, putA, serveNGA, serveA, moveA] :=
    hp.domain.actions ▸ i.mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  have hpm' : pm.type = "sandwich" ∨ pm.type = "bread-portion" ∨
      pm.type = "content-portion" ∨ pm.type = "tray" ∨ pm.type = "child" ∨
      pm.type = "place" := by
    rcases hmem with h | h | h | h | h | h <;> rw [h] at hpm <;>
      simp only [makeNGA, makeA, putA, serveNGA, serveA, moveA, swP, brP, coP, trP, chP,
        plP, List.mem_cons, List.not_mem_nil, or_false] at hpm <;>
      rcases hpm with rfl | rfl | rfl | rfl <;> simp
  rcases hpm' with h | h | h | h | h | h <;> rw [h]
  · exact hp.swType
  · exact hp.brType
  · exact hp.coType
  · exact hp.trType
  · exact hp.chType
  · exact hp.plType

/-! #### The four schemas the chain uses, as the grounder emits them -/

private def serveRaw (a : Action) (sw k tr q : Name) : AtomOp :=
  mkOp a (a.pre.filter fun x => !(staticPredicates d).contains x.pred) #[sw, k, tr, q]

private def putRaw (sw tr : Name) : AtomOp :=
  mkOp putA (putA.pre.filter fun x => !(staticPredicates d).contains x.pred) #[sw, tr]

private def moveRaw (tr q1 q2 : Name) : AtomOp :=
  mkOp moveA (moveA.pre.filter fun x => !(staticPredicates d).contains x.pred) #[tr, q1, q2]

private theorem dynPut :
    putA.pre.filter (fun x => !(staticPredicates d).contains x.pred) = putA.pre := by
  refine List.filter_eq_self.mpr ?_
  intro y hy
  have hy' : y = kitchenSwV "?s" ∨ y = atKitchenV "?t" := by simpa [putA] using hy
  rcases hy' with rfl | rfl
  · simpa using kitchenSw_dynamic hp.domain.actions
  · simpa [atKitchenV] using at_dynamic hp.domain.actions

private theorem dynMove :
    moveA.pre.filter (fun x => !(staticPredicates d).contains x.pred) = moveA.pre := by
  refine List.filter_eq_self.mpr ?_
  intro y hy
  have hy' : y = atV "?t" "?p1" := by simpa [moveA] using hy
  rcases hy' with rfl
  simpa [atV] using at_dynamic hp.domain.actions

private theorem put_hstat {sw tr : Name} :
    ∀ y ∈ putA.pre, (staticPredicates d).contains y.pred = true →
      instAtom putA.params [sw, tr] y ∈ p.init := by
  intro y hy hc
  have hy' : y = kitchenSwV "?s" ∨ y = atKitchenV "?t" := by simpa [putA] using hy
  rcases hy' with rfl | rfl
  · have h' : (staticPredicates d).contains "at_kitchen_sandwich" = true := hc
    rw [kitchenSw_dynamic hp.domain.actions] at h'; exact absurd h' (by simp)
  · have h' : (staticPredicates d).contains "at" = true := hc
    rw [at_dynamic hp.domain.actions] at h'; exact absurd h' (by simp)

private theorem move_hstat {tr q1 q2 : Name} :
    ∀ y ∈ moveA.pre, (staticPredicates d).contains y.pred = true →
      instAtom moveA.params [tr, q1, q2] y ∈ p.init := by
  intro y hy hc
  have hy' : y = atV "?t" "?p1" := by simpa [moveA] using hy
  rcases hy' with rfl
  have h' : (staticPredicates d).contains "at" = true := hc
  rw [at_dynamic hp.domain.actions] at h'; exact absurd h' (by simp)

private theorem putRaw_mem {sw tr : Name}
    (hsw : WellTyped d (allObjects d p) "sandwich" sw)
    (htr : WellTyped d (allObjects d p) "tray" tr) : putRaw (d := d) sw tr ∈ rawOps d p := by
  rw [← groundedOps_false]
  refine groundedOps_complete d p (a := putA) (by rw [hp.domain.actions]; simp) #[sw, tr]
    rfl (inst_hty' hp (putInst (p := p) hp.domain.actions hsw htr)) ?_ (put_hstat hp)
  exact List.Forall₂.cons hsw (List.Forall₂.cons htr List.Forall₂.nil)

private theorem moveRaw_mem {tr q1 q2 : Name}
    (htr : WellTyped d (allObjects d p) "tray" tr)
    (h1 : WellTyped d (allObjects d p) "place" q1)
    (h2 : WellTyped d (allObjects d p) "place" q2) :
    moveRaw (d := d) tr q1 q2 ∈ rawOps d p := by
  rw [← groundedOps_false]
  refine groundedOps_complete d p (a := moveA) (by rw [hp.domain.actions]; simp)
    #[tr, q1, q2] rfl (inst_hty' hp (moveInst (p := p) hp.domain.actions htr h1 h2)) ?_
    (move_hstat hp)
  exact List.Forall₂.cons htr (List.Forall₂.cons h1 (List.Forall₂.cons h2 List.Forall₂.nil))

variable (hok : relevantOK (rawOps d p) p.goal.toArray (rset (d := d) (p := p)) = true)

include hok

/-- A `serve` that would meet a relevant goal brings its `ontray` and its `at`
into the set.  Both serve schemas have the same shape here, so the argument is
made once and applied twice. -/
private theorem serve_rel {a : Action} {sw k tr q : Name} (hmem : a ∈ d.actions)
    (hpar : a.params = [swP, chP, trP "?t", plP "?p"]) (hadd : a.add = [servedV "?c"])
    (hon : ontrayV "?s" "?t" ∈ a.pre) (hat : atV "?t" "?p" ∈ a.pre)
    (hnp : ∀ z ∈ a.pre, z.pred ≠ "served")
    (hst : ∀ y ∈ a.pre, (staticPredicates d).contains y.pred = true →
      instAtom a.params [sw, k, tr, q] y ∈ p.init)
    (hsw : WellTyped d (allObjects d p) "sandwich" sw)
    (hk : WellTyped d (allObjects d p) "child" k)
    (htr : WellTyped d (allObjects d p) "tray" tr)
    (hq : WellTyped d (allObjects d p) "place" q)
    (hgoal : (rset (d := d) (p := p)).contains (served k) = true) :
    (rset (d := d) (p := p)).contains (ontray sw tr) = true ∧
    (rset (d := d) (p := p)).contains (atT tr q) = true ∧
    (∃ f, f < (taskOf d p true).numFacts ∧
      (taskOf d p true).factNames.getD f default = ontray sw tr) ∧
    (∃ f, f < (taskOf d p true).numFacts ∧
      (taskOf d p true).factNames.getD f default = atT tr q) := by
  have htyped : List.Forall₂ (fun (pm : TypedName) (o : Name) =>
      WellTyped d (allObjects d p) pm.type o) a.params [sw, k, tr, q] := by
    rw [hpar]
    exact List.Forall₂.cons hsw (List.Forall₂.cons hk
      (List.Forall₂.cons htr (List.Forall₂.cons hq List.Forall₂.nil)))
  have hraw : serveRaw (d := d) a sw k tr q ∈ rawOps d p := by
    rw [← groundedOps_false]
    refine groundedOps_complete d p hmem #[sw, k, tr, q] (by rw [hpar]; rfl) ?_ ?_ hst
    · intro pm hpm
      rw [hpar] at hpm
      have : pm = swP ∨ pm = chP ∨ pm = trP "?t" ∨ pm = plP "?p" := by simpa using hpm
      rcases this with rfl | rfl | rfl | rfl
      · exact hp.swType
      · exact hp.chType
      · exact hp.trType
      · exact hp.plType
    · exact htyped
  have hservedAdd : served k ∈ (serveRaw (d := d) a sw k tr q).add := by
    have h := mem_mkOp_add a (a.pre.filter fun y =>
      !(staticPredicates d).contains y.pred) #[sw, k, tr, q] (y := servedV "?c")
      (by rw [hadd]; simp) ?_
    · have hv : instAtom a.params [sw, k, tr, q] (servedV "?c") = served k := by
        rw [hpar]; rfl
      simpa [serveRaw, hv] using h
    · intro z hz
      have hz' : z ∈ a.pre := (List.mem_filter.mp hz).1
      intro hcon
      exact hnp z hz' (by
        have : (instAtom a.params [sw, k, tr, q] z).pred
            = (instAtom a.params [sw, k, tr, q] (servedV "?c")).pred := by rw [hcon]
        simpa [instAtom, servedV] using this)
  have hpre := (relevance_verified hok).1 _ hraw (touches_of_add hservedAdd hgoal)
  have hin : ∀ y ∈ a.pre, (staticPredicates d).contains y.pred = false →
      instAtom a.params [sw, k, tr, q] y ∈ (serveRaw (d := d) a sw k tr q).pre := by
    intro y hy hdyn
    have := mem_mkOp_pre a (a.pre.filter fun z => !(staticPredicates d).contains z.pred)
      #[sw, k, tr, q] (y := y) (List.mem_filter.mpr ⟨hy, by rw [hdyn]; rfl⟩)
    simpa [serveRaw] using this
  have hvon : instAtom a.params [sw, k, tr, q] (ontrayV "?s" "?t") = ontray sw tr := by
    rw [hpar]; rfl
  have hvat : instAtom a.params [sw, k, tr, q] (atV "?t" "?p") = atT tr q := by
    rw [hpar]; rfl
  have hname : ∀ y ∈ a.pre, (staticPredicates d).contains y.pred = false →
      ∃ f, f < (taskOf d p true).numFacts ∧
        (taskOf d p true).factNames.getD f default = instAtom a.params [sw, k, tr, q] y := by
    intro y hy hdyn
    exact ground_names_instance_pruned d p
      ({ schema := a, mem := hmem, args := [sw, k, tr, q], typed := htyped } :
        Instance d (allObjects d p))
      (inst_hty' hp _) hst _ (relevance_verified hok).2.2
      (touches_of_add hservedAdd hgoal) (Or.inl ⟨hy, hdyn⟩)
  refine ⟨by rw [← hvon]; exact hpre _ (hin _ hon (ontray_dynamic hp.domain.actions)),
    by rw [← hvat]; exact hpre _ (hin _ hat (at_dynamic hp.domain.actions)), ?_, ?_⟩
  · rw [← hvon]; exact hname _ hon (ontray_dynamic hp.domain.actions)
  · rw [← hvat]; exact hname _ hat (at_dynamic hp.domain.actions)

/-- A goal child, with the place they wait at and the schema that would serve
them. -/
private theorem serve_seed {sw tr : Name}
    (hsw : WellTyped d (allObjects d p) "sandwich" sw)
    (htr : WellTyped d (allObjects d p) "tray" tr) :
    ∃ q, WellTyped d (allObjects d p) "place" q ∧
      (rset (d := d) (p := p)).contains (ontray sw tr) = true ∧
      (rset (d := d) (p := p)).contains (atT tr q) = true ∧
      (∃ f, f < (taskOf d p true).numFacts ∧
        (taskOf d p true).factNames.getD f default = ontray sw tr) ∧
      (∃ f, f < (taskOf d p true).numFacts ∧
        (taskOf d p true).factNames.getD f default = atT tr q) := by
  obtain ⟨k, hk⟩ := List.exists_mem_of_ne_nil _ hp.someGoal
  obtain ⟨⟨aw, haw, hawp, hawh⟩, hall⟩ := hp.childServable k hk
  obtain ⟨ow, how, hwargs, hwty⟩ := hp.waitingTyped aw haw hawp
  rw [hawh] at hwargs
  have hwq : aw = waitingAtom k ow.name := by
    show aw = { pred := "waiting", args := [k, ow.name] }
    rw [← hawp, ← hwargs]
  have hqT : WellTyped d (allObjects d p) "place" ow.name := wellTyped_of_type how hwty
  obtain ⟨ok, hok', hkn, hkty⟩ := hp.goalChildTyped k hk
  have hkT : WellTyped d (allObjects d p) "child" k := hkn ▸ wellTyped_of_type hok' hkty
  have hgoal : (rset (d := d) (p := p)).contains (served k) = true :=
    (relevance_verified hok).2.1 _ (by simpa using goal_of_goalKids hp hk)
  refine ⟨ow.name, hqT, ?_⟩
  rcases hall with hA | hN
  · -- the child is allergic, so `serve_sandwich_no_gluten` is the one that exists
    refine serve_rel hp hok (a := serveNGA) (by rw [hp.domain.actions]; simp) rfl rfl
      (by simp [serveNGA]) (by simp [serveNGA]) serveNGA_nopre ?_ hsw hkT htr hqT hgoal
    intro y hy hc
    have hy' : y = allergicV "?c" ∨ y = ontrayV "?s" "?t" ∨ y = waitingV "?c" "?p" ∨
        y = glutenFreeV "?s" ∨ y = atV "?t" "?p" := by simpa [serveNGA] using hy
    rcases hy' with rfl | rfl | rfl | rfl | rfl
    · simpa [instAtom, serveNGA, swP, chP, trP, plP, allergicV, allergicAtom] using hA
    · have h' : (staticPredicates d).contains "ontray" = true := hc
      rw [ontray_dynamic hp.domain.actions] at h'; exact absurd h' (by simp)
    · have hv : instAtom serveNGA.params [sw, k, tr, ow.name] (waitingV "?c" "?p")
          = waitingAtom k ow.name := rfl
      rw [hv, ← hwq]; exact haw
    · have h' : (staticPredicates d).contains "no_gluten_sandwich" = true := hc
      rw [glutenFree_dynamic hp.domain.actions] at h'; exact absurd h' (by simp)
    · have h' : (staticPredicates d).contains "at" = true := hc
      rw [at_dynamic hp.domain.actions] at h'; exact absurd h' (by simp)
  · refine serve_rel hp hok (a := serveA) (by rw [hp.domain.actions]; simp) rfl rfl
      (by simp [serveA]) (by simp [serveA]) serveA_nopre ?_ hsw hkT htr hqT hgoal
    intro y hy hc
    have hy' : y = notAllergicV "?c" ∨ y = waitingV "?c" "?p" ∨ y = ontrayV "?s" "?t" ∨
        y = atV "?t" "?p" := by simpa [serveA] using hy
    rcases hy' with rfl | rfl | rfl | rfl
    · simpa [instAtom, serveA, swP, chP, trP, plP, notAllergicV, notAllergicAtom] using hN
    · have hv : instAtom serveA.params [sw, k, tr, ow.name] (waitingV "?c" "?p")
          = waitingAtom k ow.name := rfl
      rw [hv, ← hwq]; exact haw
    · have h' : (staticPredicates d).contains "ontray" = true := hc
      rw [ontray_dynamic hp.domain.actions] at h'; exact absurd h' (by simp)
    · have h' : (staticPredicates d).contains "at" = true := hc
      rw [at_dynamic hp.domain.actions] at h'; exact absurd h' (by simp)

omit hok in
/-- `put_on_tray` adds an `ontray`, which the serve step has already made relevant. -/
private theorem put_touches {sw tr : Name}
    (hon : (rset (d := d) (p := p)).contains (ontray sw tr) = true) :
    (putRaw (d := d) sw tr).touches (rset (d := d) (p := p)) = true := by
  refine touches_of_add ?_ hon
  have h := mem_mkOp_add putA (putA.pre.filter fun y =>
    !(staticPredicates d).contains y.pred) #[sw, tr] (y := ontrayV "?s" "?t")
    (by simp [putA]) ?_
  · simpa [putRaw, instAtom, putA, swP, trP, ontrayV, ontray] using h
  · intro z hz
    have hz' : z = kitchenSwV "?s" ∨ z = atKitchenV "?t" := by
      rw [dynPut hp] at hz; simpa [putA] using hz
    rcases hz' with rfl | rfl <;>
      simp [instAtom, putA, swP, trP, kitchenSwV, atKitchenV, ontrayV, atT, ontray]

/-- **The three families are numbered with pruning on, too.** -/
theorem childsnackNumbered_verified : ChildsnackNumbered d p true := by
  have hrdef := (relevance_verified hok).2.2
  refine ⟨?_, ?_, ?_⟩
  · intro sw hsw
    obtain ⟨tr, htr⟩ := some_tray hp
    obtain ⟨-, -, hon, -, -, -⟩ := serve_seed hp hok hsw htr
    have h := ground_names_instance_pruned d p (putInst (p := p) hp.domain.actions hsw htr)
      (inst_hty' hp _) (put_hstat hp) _ hrdef (put_touches hp hon)
      (y := kitchenSwV "?s")
      (Or.inl ⟨by simp [putInst, putA], kitchenSw_dynamic hp.domain.actions⟩)
    exact h
  · intro sw tr hsw htr
    obtain ⟨-, -, -, -, hname, -⟩ := serve_seed hp hok hsw htr
    exact hname
  · intro tr q htr hq
    obtain ⟨sw, hsw⟩ := some_sw hp
    obtain ⟨q0, hq0, -, hat0, -, hname0⟩ := serve_seed hp hok hsw htr
    by_cases hqq : q = q0
    · rw [hqq]; exact hname0
    · -- the `move_tray` that would bring the tray back reads `at tr q`
      have hadd : atT tr q0 ∈ (moveRaw (d := d) tr q q0).add := by
        have h := mem_mkOp_add moveA (moveA.pre.filter fun y =>
          !(staticPredicates d).contains y.pred) #[tr, q, q0] (y := atV "?t" "?p2")
          (by simp [moveA]) ?_
        · simpa [moveRaw, instAtom, moveA, trP, plP, atV, atT] using h
        · intro z hz
          have hz' : z = atV "?t" "?p1" := by
            rw [dynMove hp] at hz; simpa [moveA] using hz
          rcases hz' with rfl
          have hv1 : instAtom moveA.params [tr, q, q0] (atV "?t" "?p1") = atT tr q := rfl
          have hv2 : instAtom moveA.params [tr, q, q0] (atV "?t" "?p2") = atT tr q0 := rfl
          rw [hv1, hv2]
          intro hcon
          exact hqq (by simpa [atT] using hcon)
      have h := ground_names_instance_pruned d p
        (moveInst (p := p) hp.domain.actions htr hq hq0)
        (inst_hty' hp _) (move_hstat hp) _ hrdef (touches_of_add hadd hat0)
        (y := atV "?t" "?p1") (Or.inl ⟨by simp [moveInst, moveA], at_dynamic hp.domain.actions⟩)
      exact h

end Pruned

section Numbered

variable {d : Domain} {p : Problem} (hp : ChildsnackProblem d p)

include hp

/-- **The tables are complete on the task the planner grounds, pruning or not.** -/
theorem childsnackNumbered (rel : Bool) : ChildsnackNumbered d p rel := by
  cases rel with
  | false => exact childsnackNumbered_false hp
  | true =>
      by_cases hok : relevantOK (rawOps d p) p.goal.toArray
          (relevantSet (rawOps d p) p.goal.toArray) = true
      · exact childsnackNumbered_verified hp hok
      · have heq : taskOf d p true = taskOf d p false :=
          taskOf_eq_of_unverified d p (by simpa using hok)
        obtain ⟨f1, f2, f3⟩ := childsnackNumbered_false hp
        refine ⟨fun sw hsw => ?_, fun sw tr hsw htr => ?_, fun tr q htr hq => ?_⟩
        · rw [heq]; exact f1 sw hsw
        · rw [heq]; exact f2 sw tr hsw htr
        · rw [heq]; exact f3 tr q htr hq

set_option maxHeartbeats 1000000 in
/--
**Childsnack's improved heuristic is admissible on the task the planner
searches**, with the relevance analysis on or off.
-/
theorem improved_admissible_of_pinned (rel : Bool) :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel))
      (ExampleHeuristics.Childsnack.improved (ground d p rel)).eval :=
  improved_admissible hp (childsnackNumbered hp rel)

set_option maxHeartbeats 1000000 in
/-- And goal-aware, and consistent. -/
theorem improved_goalAware_of_pinned (rel : Bool) :
    (ground d p rel).GoalAwareOn (Reachable (ground d p rel))
      (ExampleHeuristics.Childsnack.improved (ground d p rel)).eval :=
  improved_goalAware hp (childsnackNumbered hp rel)

set_option maxHeartbeats 1000000 in
theorem improved_consistent_of_pinned (rel : Bool) :
    (ground d p rel).ConsistentOn (Reachable (ground d p rel))
      (ExampleHeuristics.Childsnack.improved (ground d p rel)).eval :=
  improved_consistent hp (childsnackNumbered hp rel)

end Numbered

end Planner.Lifted.Childsnack

/- -------------------------------------------------------------------------- -/
/-
A childsnack domain and problem that satisfy `ChildsnackProblem`.

Every field is discharged by `decide`.
-/

namespace Planner.Lifted.Childsnack

open Planner Planner.Pddl

private def one (ty : Name) : List TypedName := [{ name := "?x", type := ty }]
private def two (a b : Name) : List TypedName :=
  [{ name := "?x", type := a }, { name := "?y", type := b }]

def exDomain : Domain where
  name := "child-snack"
  requirements := [":strips", ":typing"]
  types := [{ name := "child", parent := "object" },
            { name := "bread-portion", parent := "object" },
            { name := "content-portion", parent := "object" },
            { name := "sandwich", parent := "object" },
            { name := "tray", parent := "object" },
            { name := "place", parent := "object" }]
  constants := [{ name := "kitchen", type := "place" }]
  predicates :=
    [ { name := "at_kitchen_bread", params := one "bread-portion" },
      { name := "at_kitchen_content", params := one "content-portion" },
      { name := "at_kitchen_sandwich", params := one "sandwich" },
      { name := "no_gluten_bread", params := one "bread-portion" },
      { name := "no_gluten_content", params := one "content-portion" },
      { name := "ontray", params := two "sandwich" "tray" },
      { name := "no_gluten_sandwich", params := one "sandwich" },
      { name := "allergic_gluten", params := one "child" },
      { name := "not_allergic_gluten", params := one "child" },
      { name := "served", params := one "child" },
      { name := "waiting", params := two "child" "place" },
      { name := "at", params := two "tray" "place" },
      { name := "notexist", params := one "sandwich" } ]
  actions := [makeNGA, makeA, putA, serveNGA, serveA, moveA]

def exProblem : Problem where
  name := "child-snack-1"
  domainName := "child-snack"
  objects :=
    [ { name := "c1", type := "child" },
      { name := "s1", type := "sandwich" },
      { name := "t1", type := "tray" },
      { name := "b1", type := "bread-portion" },
      { name := "co1", type := "content-portion" },
      { name := "table1", type := "place" } ]
  init :=
    [ { pred := "at_kitchen_bread", args := ["b1"] },
      { pred := "at_kitchen_content", args := ["co1"] },
      notAllergicAtom "c1",
      waitingAtom "c1" "table1",
      notexist "s1",
      atT "t1" "kitchen" ]
  goal := [served "c1"]

theorem exPinned : ChildsnackProblem exDomain exProblem := by
  refine ⟨⟨rfl, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try decide
  exact { domainOK := by decide, problemOK := by decide }

/-- And so the heuristic the planner runs is admissible on that task, with the
relevance analysis on, which is how the planner runs by default. -/
theorem ex_admissible :
    (ground exDomain exProblem true).AdmissibleOn
      (Reachable (ground exDomain exProblem true))
      (ExampleHeuristics.Childsnack.improved (ground exDomain exProblem true)).eval :=
  improved_admissible_of_pinned exPinned true

end Planner.Lifted.Childsnack

/- -------------------------------------------------------------------------- -/
/-
Soundness of the executable certificate for the improved Childsnack heuristic.
-/

namespace Planner.Lifted.Childsnack

open Planner Planner.Pddl

theorem certificate_sound {d : Domain} {p : Problem}
    (hv : Validated d p)
    (h : ExampleHeuristics.Childsnack.Certificate.certified d p = true) :
    ChildsnackProblem d p := by
  simp only [ExampleHeuristics.Childsnack.Certificate.certified,
    ExampleHeuristics.Childsnack.Certificate.conditions, Certificate.passes,
    List.all_cons, List.all_nil, Bool.and_eq_true] at h
  rcases h with
    ⟨hactions, hallergicStatic, hnotAllergicStatic, hwaitingStatic,
      hswType, htrType, hplType, hchType, hbrType, hcoType,
      hsomeTray, hsomeSw, hkitchen, hgoalShape, hgoalNodup,
      hswExact, htrExact, hplExact, hwaitingUnique, hwaitingTyped,
      hallergySeparated, hnoFree, hsomeGoal, hgoalTyped, hservable, hinit⟩
  refine
    { domain :=
        ⟨by simpa using hactions, by simpa using hallergicStatic,
          by simpa using hnotAllergicStatic, by simpa using hwaitingStatic⟩
      swType := by simpa using hswType
      trType := by simpa using htrType
      plType := by simpa using hplType
      chType := by simpa using hchType
      brType := by simpa using hbrType
      coType := by simpa using hcoType
      validated := hv
      someTray := Certificate.hasObject_sound hsomeTray
      someSw := Certificate.hasObject_sound hsomeSw
      kitchenObj := Certificate.objectNamedWithType_sound hkitchen
      goalServed := ?_
      goalNodup := of_decide_eq_true hgoalNodup
      swExact := Certificate.exactType_sound hswExact
      trExact := Certificate.exactType_sound htrExact
      plExact := Certificate.exactType_sound hplExact
      waitingUnique := ?_
      waitingTyped := ?_
      allergicSplit := ?_
      noFreeInit := ?_
      someGoal := ?_
      goalChildTyped := ?_
      childServable := ?_
      initCheck := ?_ }
  · intro a ha
    rw [ExampleHeuristics.Childsnack.Certificate.goalShape,
      List.all_eq_true] at hgoalShape
    have hs := hgoalShape a ha
    by_cases hpred : (a.pred == "served") = true
    · rcases hargs : a.args with _ | ⟨k, rest⟩
      · simp [hpred, hargs] at hs
      · cases rest with
        | cons _ _ => simp [hpred, hargs] at hs
        | nil =>
            refine ⟨k, ?_, ?_⟩
            · exact List.mem_filterMap.mpr ⟨a, ha, by simp [hpred, hargs]⟩
            · show a = { pred := "served", args := [k] }
              cases a
              simp_all
    · simp [hpred] at hs
  · intro a ha b hb hpa hpb hhead
    rw [ExampleHeuristics.Childsnack.Certificate.waitingUnique,
      List.all_eq_true] at hwaitingUnique
    have hab := hwaitingUnique a ha
    rw [List.all_eq_true] at hab
    have heq := hab b hb
    simp [hpa, hpb, hhead] at heq
    exact heq
  · intro a ha hpred
    rw [ExampleHeuristics.Childsnack.Certificate.waitingTyped,
      List.all_eq_true] at hwaitingTyped
    have ht := hwaitingTyped a ha
    rcases hargs : a.args with _ | ⟨k, rest⟩
    · simp [hpred, hargs] at ht
    · cases rest with
      | nil => simp [hpred, hargs] at ht
      | cons q rest' =>
          cases rest' with
          | cons _ _ => simp [hpred, hargs] at ht
          | nil =>
              simp [hpred, hargs] at ht
              obtain ⟨o, ho, hn, hty⟩ := Certificate.objectNamedWithType_sound ht
              refine ⟨o, ho, ?_, hty⟩
              simp [hargs, hn]
  · intro a ha hpa b hb hpb
    rw [ExampleHeuristics.Childsnack.Certificate.allergySeparated,
      List.all_eq_true] at hallergySeparated
    have hab := hallergySeparated a ha
    rw [List.all_eq_true] at hab
    have hne := hab b hb
    simpa [hpa, hpb] using hne
  · intro a ha
    rw [ExampleHeuristics.Childsnack.Certificate.noFreeInitially,
      List.all_eq_true] at hnoFree
    have hne := hnoFree a ha
    simpa using hne
  · intro hempty
    have hempty' : ExampleHeuristics.Childsnack.Certificate.goalKids p = [] := by
      simpa [ExampleHeuristics.Childsnack.Certificate.goalKids, goalKids] using hempty
    rw [hempty'] at hsomeGoal
    simp at hsomeGoal
  · intro k hk
    rw [ExampleHeuristics.Childsnack.Certificate.goalChildrenTyped,
      List.all_eq_true] at hgoalTyped
    have ht := hgoalTyped k
      (by simpa [ExampleHeuristics.Childsnack.Certificate.goalKids, goalKids] using hk)
    exact Certificate.objectNamedWithType_sound ht
  · intro k hk
    rw [ExampleHeuristics.Childsnack.Certificate.childServable,
      List.all_eq_true] at hservable
    have hs := hservable k
      (by simpa [ExampleHeuristics.Childsnack.Certificate.goalKids, goalKids] using hk)
    rw [Bool.and_eq_true] at hs
    constructor
    · rw [List.any_eq_true] at hs
      obtain ⟨a, ha, hboth⟩ := hs.1
      rw [Bool.and_eq_true] at hboth
      exact ⟨a, ha, by simpa using hboth.1, by simpa using hboth.2⟩
    · simpa [allergicAtom, notAllergicAtom] using hs.2
  · simpa [ExampleHeuristics.Childsnack.Certificate.initInvCheck,
      ExampleHeuristics.Childsnack.Certificate.atPairs,
      ExampleHeuristics.Childsnack.Certificate.onPairs,
      ExampleHeuristics.Childsnack.Certificate.notexistSws,
      ExampleHeuristics.Childsnack.Certificate.kitchenSws,
      ExampleHeuristics.Childsnack.Certificate.freeSws,
      initInvCheck, atPairs, onPairs, notexistSws, kitchenSws, freeSws] using hinit.1

theorem improved_goalAware_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool)
    (h : ExampleHeuristics.Childsnack.Certificate.certified d p = true) :
    (ground d p rel).GoalAwareOn (Reachable (ground d p rel))
      (ExampleHeuristics.Childsnack.improved (ground d p rel)).eval :=
  improved_goalAware_of_pinned (certificate_sound hv h) rel

theorem improved_consistent_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool)
    (h : ExampleHeuristics.Childsnack.Certificate.certified d p = true) :
    (ground d p rel).ConsistentOn (Reachable (ground d p rel))
      (ExampleHeuristics.Childsnack.improved (ground d p rel)).eval :=
  improved_consistent_of_pinned (certificate_sound hv h) rel

theorem improved_proof_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool) :
    ImprovedProof d p rel
      (ExampleHeuristics.Childsnack.Certificate.certified d p)
      (ExampleHeuristics.Childsnack.improved (ground d p rel)) :=
  { goalAware := improved_goalAware_of_certificate hv rel
    consistent := improved_consistent_of_certificate hv rel }

theorem improved_admissible_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool)
    (h : ExampleHeuristics.Childsnack.Certificate.certified d p = true) :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel))
      (ExampleHeuristics.Childsnack.improved (ground d p rel)).eval :=
  (improved_proof_of_certificate hv rel).admissible h

end Planner.Lifted.Childsnack
