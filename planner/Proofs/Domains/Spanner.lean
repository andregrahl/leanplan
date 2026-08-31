/-
Spanner's improved heuristic, proved end to end in one file.

The order below is the order the argument is built in.  The first two sections
are the schema-level proof: the improved value over the domain's own data, and
what each schema does to the counters.  The rest lifts that value to the parsed
domain, compiles it against the numbered task, and ends with the four
certificate theorems the registry depends on.

The runtime heuristic, its data, and its certificate stay under `Planner/`.  The
simple heuristic of this domain is proved in `Proofs/Domains/SpannerSimple.lean`.
-/
import Proofs.Combinators
import Proofs.Certificates
import Proofs.Distance
import Proofs.SchemaSupport
import Proofs.LiftedHeuristic
import Proofs.FactTables
import Proofs.CompileSupport
import Proofs.Validation
import Proofs.Heuristic
import Planner.ExampleHeuristics.Spanner.Improved
import Planner.ExampleHeuristics.Spanner.Domain
import Planner.ExampleHeuristics.Spanner.Certificate

/- -------------------------------------------------------------------------- -/
/-
Spanner, improved heuristic: goal-aware, and consistent for every task whose
operators act on the heuristic's quantities the way the domain's schemas do.

The heuristic counts four things: the goal nuts still loose, the usable spanners
in hand, the usable spanners still within reach on the ground, and how far the
nearest man is from the farthest loose nut.  Everything the argument needs is a
statement about how one action moves those four, and `Effect` below is that
statement — one constructor per schema family.

  * `tighten_nut` consumes a loose nut *and* the usable spanner it uses, so both
    counts fall by one together.  It cannot lower the walking bound, because the
    nut it removes is the one the man is standing on, whose distance is zero, so
    the maximum over the rest is unchanged.
  * `pickup_spanner` moves a spanner from the ground into the hand.  The pool of
    usable spanners the man can still get at does not grow, and the men do not
    move, so the walking bound is untouched.
  * `walk` moves a man one link forward.  Reachability from a man's position can
    only shrink — anything reachable after the step was reachable before it — so
    the spanners still in reach cannot increase, and the walking bound moves by at
    most one, which is the triangle inequality for the distance table.

From those, two obligations.  `dead_closed` is the one that matters: the corridor
is one-way, so once the usable spanners a man carries or can still reach fall
below the number of loose nuts, they never recover.  Each family shows this its
own way — `tighten_nut` decrements both sides of the comparison at once, and it
needs a carried spanner to fire, which is what keeps the loose count from
reaching zero in a dead state.  `base_step` is the arithmetic: no action lowers
the numeric part by more than its cost.

What is assumed rather than checked: that each grounded operator induces one of
the four effects.  That is a statement about the domain's schemas, and turning it
into a decidable certificate the planner verifies when it loads the task is the
remaining step for this domain.
-/

namespace Planner.ExampleHeuristics.Spanner

open Planner

/-! ### The four quantities -/

/-- Nuts still loose. -/
abbrev Lc (d : Data) (s : State) : Nat := (looseNuts d s).size
/-- Usable spanners carried. -/
abbrev Cc (d : Data) (s : State) : Nat := (carriedSpanners d s).size
/-- Usable spanners still within reach on the ground. -/
abbrev Ac (d : Data) (s : State) : Nat := (aheadSpanners d s (menLocations d s)).size
/-- The walking bound. -/
abbrev Wc (d : Data) (s : State) : Nat := walkBound d s (menLocations d s)

/-- How an action may move the four quantities: one constructor per schema family. -/
inductive Effect (d : Data) (s s' : State) : Prop
  | tighten (hL : Lc d s' + 1 = Lc d s) (hC : Cc d s' + 1 = Cc d s)
      (hW : Wc d s ≤ Wc d s') (hA : Ac d s' ≤ Ac d s)
  | pickup (hL : Lc d s' = Lc d s) (hC : Cc d s + 1 = Cc d s')
      (hW : Wc d s = Wc d s') (hR : Cc d s' + Ac d s' ≤ Cc d s + Ac d s)
  | walk (hL : Lc d s' = Lc d s) (hC : Cc d s' = Cc d s)
      (hW : Wc d s ≤ Wc d s' + 1) (hA : Ac d s' ≤ Ac d s)
  | other (hL : Lc d s' = Lc d s) (hC : Cc d s' = Cc d s)
      (hW : Wc d s ≤ Wc d s') (hA : Ac d s' ≤ Ac d s)

/-! ### Discharging the loose-nut component from the operator

`Effect`'s hypotheses are statements about states, but the first of them follows
from facts about the operator alone — which nut goals it adds, which it deletes —
and those are decidable.  These two lemmas make that step, so a certificate can
establish the loose-nut count rather than a hypothesis assuming it.  The other
three quantities need the same treatment against the spanner and distance data.
-/

/-- `tighten_nut` achieves exactly one outstanding nut goal, so one fewer is loose. -/
theorem loose_drop_one (d : Data) {n : Nat} {op : Op} {s : State}
    (hop : Op.WF n op) (hs : State.WF n s) (hnd : d.nuts.toList.Nodup)
    (x : Fact × Nat) (hx : x ∈ d.nuts)
    (hxadd : op.add.contains x.1 = true) (hxs : s.test x.1 = false)
    (hother : ∀ y ∈ d.nuts, y ≠ x → op.add.contains y.1 = false)
    (hdel : ∀ y ∈ d.nuts, op.del.contains y.1 = false) :
    Lc d (op.apply s) + 1 = Lc d s :=
  unmet_drop_one d.nuts (·.1) hop hs hnd x hx hxadd hxs hother hdel

/-- Any operator touching no nut goal leaves the loose count alone. -/
theorem loose_unchanged (d : Data) {n : Nat} {op : Op} {s : State}
    (hop : Op.WF n op) (hs : State.WF n s)
    (hadd : ∀ y ∈ d.nuts, op.add.contains y.1 = false)
    (hdel : ∀ y ∈ d.nuts, op.del.contains y.1 = false) :
    Lc d (op.apply s) = Lc d s :=
  unmet_unchanged d.nuts (·.1) hop hs hadd hdel

/-! ### Discharging the spanner counts

Both spanner quantities are filters with compound predicates — usable *and*
carried, usable *and* reachable on the ground — so they move by the same two
shapes as any other count.  `tighten_nut` makes one carried spanner unusable;
`pickup_spanner` moves one from the ground into the hand; anything else leaves
both alone.
-/

/-- `tighten_nut` consumes exactly one carried usable spanner. -/
theorem carried_drop_one (d : Data) (s s' : State) (sp : SpannerInfo)
    (hsp : sp ∈ d.spanners) (hnd : d.spanners.toList.Nodup)
    (hbefore : (s.test sp.usableFact && sp.carryFacts.any fun f => s.test f) = true)
    (hafter : (s'.test sp.usableFact && sp.carryFacts.any fun f => s'.test f) = false)
    (hrest : ∀ y ∈ d.spanners, y ≠ sp →
        (s.test y.usableFact && y.carryFacts.any fun f => s.test f)
          = (s'.test y.usableFact && y.carryFacts.any fun f => s'.test f)) :
    Cc d s' + 1 = Cc d s :=
  filter_size_drop_one d.spanners _ _ sp hsp hnd hbefore hafter hrest

/-- `pickup_spanner` gains exactly one carried usable spanner. -/
theorem carried_gain_one (d : Data) (s s' : State) (sp : SpannerInfo)
    (hsp : sp ∈ d.spanners) (hnd : d.spanners.toList.Nodup)
    (hbefore : (s.test sp.usableFact && sp.carryFacts.any fun f => s.test f) = false)
    (hafter : (s'.test sp.usableFact && sp.carryFacts.any fun f => s'.test f) = true)
    (hrest : ∀ y ∈ d.spanners, y ≠ sp →
        (s'.test y.usableFact && y.carryFacts.any fun f => s'.test f)
          = (s.test y.usableFact && y.carryFacts.any fun f => s.test f)) :
    Cc d s + 1 = Cc d s' :=
  filter_size_drop_one d.spanners _ _ sp hsp hnd hafter hbefore hrest

/-- Anything touching neither usability nor carriage leaves the count alone. -/
theorem carried_unchanged (d : Data) (s s' : State)
    (h : ∀ y ∈ d.spanners,
        (s'.test y.usableFact && y.carryFacts.any fun f => s'.test f)
          = (s.test y.usableFact && y.carryFacts.any fun f => s.test f)) :
    Cc d s' = Cc d s :=
  filter_size_congr d.spanners _ _ h

/-- The spanners still within reach never grow along a transition. -/
theorem ahead_mono (d : Data) (s s' : State) (men men' : Array Nat)
    (h : ∀ y ∈ d.spanners,
        (s'.test y.usableFact && !(y.carryFacts.any fun f => s'.test f) &&
          (match y.atFacts.find? fun z => s'.test z.1 with
           | some (_, l) => decide (d.dist.minFrom men' l < d.dist.bound)
           | none => false))
          = (s.test y.usableFact && !(y.carryFacts.any fun f => s.test f) &&
          (match y.atFacts.find? fun z => s.test z.1 with
           | some (_, l) => decide (d.dist.minFrom men l < d.dist.bound)
           | none => false))) :
    (aheadSpanners d s' men').size = (aheadSpanners d s men).size :=
  filter_size_congr d.spanners _ _ h

/-! ### Discharging the walking bound

The walking term is a maximum over the loose nuts of the distance from the nearest
man.  `walk` moves a man one link, which moves every one of those distances by at
most one, so the maximum does too — that is the triangle inequality of `Sound`
lifted through `minFrom` and then through the maximum.  `tighten_nut` removes a
nut the man is standing on, whose distance is zero, so the maximum over what
remains is no smaller.
-/

/-- Walking one link moves the bound by at most one. -/
theorem walk_le_succ (d : Data) (s s' : State)
    (hloose : looseNuts d s' = looseNuts d s)
    (hstep : ∀ l, ∀ w ∈ menLocations d s', ∃ u ∈ menLocations d s,
        d.dist.get u l ≤ 1 + d.dist.get w l) :
    Wc d s ≤ Wc d s' + 1 := by
  show walkBound d s (menLocations d s) ≤ walkBound d s' (menLocations d s') + 1
  unfold walkBound
  rw [hloose, ← Array.foldl_toList, ← Array.foldl_toList]
  have := foldl_max_le_succ (looseNuts d s).toList
    (fun x => d.dist.minFrom (menLocations d s) x.2)
    (fun x => d.dist.minFrom (menLocations d s') x.2)
    (fun x _ => minFrom_le_succ d.dist _ _ x.2 (hstep x.2)) 0 0 (by omega)
  simpa [Nat.add_comm] using this

/-- Removing a nut the man is standing on cannot lower the bound. -/
theorem walk_le_of_tighten (d : Data) (s s' : State)
    (hmen : menLocations d s' = menLocations d s)
    (hcover : ∀ x ∈ looseNuts d s,
        d.dist.minFrom (menLocations d s) x.2 = 0 ∨ x ∈ looseNuts d s') :
    Wc d s ≤ Wc d s' := by
  show walkBound d s (menLocations d s) ≤ walkBound d s' (menLocations d s')
  unfold walkBound
  rw [hmen, ← Array.foldl_toList, ← Array.foldl_toList]
  refine foldl_max_le_bound (looseNuts d s).toList _ _ ?_ 0 (Nat.zero_le _)
  intro x hx
  rcases hcover x (by simpa using hx) with h0 | hmem
  · rw [h0]; exact Nat.zero_le _
  · exact foldl_max_ge_mem (looseNuts d s').toList
      (fun y => d.dist.minFrom (menLocations d s) y.2) (by simpa using hmem) 0

/-! ### Splitting the value into a dead-end test and a number -/

/-- The dead-end test: fewer usable spanners in reach than nuts still loose. -/
def isDead (d : Data) (s : State) : Bool :=
  !(Lc d s == 0) && decide (Cc d s + Ac d s < Lc d s)

/-- The numeric part. -/
def baseValue (d : Data) (s : State) : Nat :=
  if Lc d s == 0 then 0 else Lc d s + (Lc d s - Cc d s) + Wc d s

theorem value_eq (d : Data) (s : State) :
    value d s = if isDead d s then deadEnd else baseValue d s := by
  unfold value isDead baseValue
  by_cases h : Lc d s == 0
  · simp [h]
  · simp only [h, Bool.not_false, Bool.true_and, decide_eq_true_eq]
    split <;> simp_all

/-! ### The two obligations -/

/-- Dead-endedness is closed under every action, which is what makes the constant safe. -/
theorem dead_closed (d : Data) (s s' : State) (he : Effect d s s')
    (hd : isDead d s = true) : isDead d s' = true := by
  simp only [isDead, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
    Bool.not_eq_true', decide_eq_true_eq] at hd ⊢
  obtain ⟨hne, hlt⟩ := hd
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq] at hne ⊢
  cases he with
  | tighten hL hC hW hA => exact ⟨by omega, by omega⟩
  | pickup hL hC hW hR => exact ⟨by omega, by omega⟩
  | walk hL hC hW hA => exact ⟨by omega, by omega⟩
  | other hL hC hW hA => exact ⟨by omega, by omega⟩

/-- Pure arithmetic: the four effects, against the value's shape. -/
private theorem step_arith (L C W L' C' W' cost : Nat) (hcost : 1 ≤ cost)
    (hz' : L' = 0 → W' = 0)
    (h : (L' + 1 = L ∧ C' + 1 = C ∧ W ≤ W') ∨
         (L' = L ∧ C + 1 = C' ∧ W = W') ∨
         (L' = L ∧ C' = C ∧ W ≤ W' + 1) ∨
         (L' = L ∧ C' = C ∧ W ≤ W')) :
    (if L == 0 then 0 else L + (L - C) + W)
      ≤ cost + (if L' == 0 then 0 else L' + (L' - C') + W') := by
  by_cases hz : L = 0
  · simp [hz]
  · by_cases hz0 : L' = 0
    · have hw0 := hz' hz0
      simp only [hz0, hz, beq_self_eq_true, if_true, beq_iff_eq]
      rw [if_neg (by simp [hz])]
      rcases h with ⟨h1,h2,h3⟩|⟨h1,h2,h3⟩|⟨h1,h2,h3⟩|⟨h1,h2,h3⟩ <;> omega
    · simp only [beq_iff_eq]
      rw [if_neg hz, if_neg hz0]
      rcases h with ⟨h1,h2,h3⟩|⟨h1,h2,h3⟩|⟨h1,h2,h3⟩|⟨h1,h2,h3⟩ <;> omega

private theorem bound_arith (L C W N B : Nat) (h1 : L ≤ N) (h2 : W ≤ B) :
    L + (L - C) + W ≤ 2 * N + B := by omega

/-- With no nut loose there is nothing to walk to. -/
theorem walkBound_zero (d : Data) (s : State) (h : Lc d s = 0) : Wc d s = 0 := by
  have he : looseNuts d s = #[] := Array.size_eq_zero_iff.mp h
  show walkBound d s (menLocations d s) = 0
  unfold walkBound
  rw [he]
  rfl

/--
No action lowers the numeric part by more than its cost.

The delicate case is tightening the *last* nut, where the value falls from
`1 + 0 + W` to zero.  That is only within one action if `W` is already zero — and
it is, because the nut being tightened is the one the man is standing on, so the
bound over what remains, which is nothing, is zero.
-/
theorem base_step (d : Data) (s s' : State) (he : Effect d s s') (cost : Nat) (hcost : 1 ≤ cost) :
    baseValue d s ≤ cost + baseValue d s' := by
  refine step_arith _ _ _ _ _ _ cost hcost (fun h => walkBound_zero d s' h) ?_
  cases he with
  | tighten hL hC hW _ => exact Or.inl ⟨hL, hC, hW⟩
  | pickup hL hC hW _ => exact Or.inr (Or.inl ⟨hL, hC, hW⟩)
  | walk hL hC hW _ => exact Or.inr (Or.inr (Or.inl ⟨hL, hC, hW⟩))
  | other hL hC hW _ => exact Or.inr (Or.inr (Or.inr ⟨hL, hC, hW⟩))

/-! ### The numeric part is bounded, so stepping into a dead end cannot make it jump -/

theorem walkBound_le (d : Data) (s : State) (men : Array Nat) :
    walkBound d s men ≤ d.dist.bound := by
  unfold walkBound
  have key : ∀ (l : List (Planner.Fact × Nat)) (b : Nat), b ≤ d.dist.bound →
      l.foldl (fun acc x => max acc (d.dist.minFrom men x.2)) b ≤ d.dist.bound := by
    intro l
    induction l with
    | nil => intro b hb; exact hb
    | cons x rest ih =>
        intro b hb
        exact ih _ (by simp only [Nat.max_le]; exact ⟨hb, Distances.minFrom_le _ _ _⟩)
  rw [← Array.foldl_toList]
  exact key _ 0 (Nat.zero_le _)

theorem baseValue_le (d : Data) (s : State) :
    baseValue d s ≤ 2 * d.nuts.size + d.dist.bound := by
  unfold baseValue
  split
  · omega
  · exact bound_arith _ _ _ _ _ Array.size_filter_le (walkBound_le d s (menLocations d s))

/-! ### Assembly -/

theorem looseNuts_empty (d : Data) (s : State) (hall : ∀ x ∈ d.nuts, s.test x.1 = true) :
    looseNuts d s = #[] := by
  unfold looseNuts
  rw [Array.filter_eq_empty_iff]
  intro x hx
  simp [hall x hx]

theorem value_eq_zero_of_goal (d : Data) (s : State)
    (hall : ∀ x ∈ d.nuts, s.test x.1 = true) : value d s = 0 := by
  unfold value
  rw [looseNuts_empty d s hall]
  rfl

theorem improved_goalAware (t : Task)
    (hcompiled : ∀ x ∈ (compile t).nuts, x.1 ∈ t.goal) :
    t.GoalAware (improved t).eval := by
  refine t.goalAware_of _ fun s _ hgoal => ?_
  exact value_eq_zero_of_goal _ s fun x hx => hgoal _ (hcompiled x hx)

/--
Consistency, for any task whose operators act as the domain's schemas do and
whose size leaves room below the dead-end constant.
-/
theorem improved_consistent (t : Task)
    (heff : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      Effect (compile t) s (op.apply s))
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost)
    (hsize : 2 * (compile t).nuts.size + (compile t).dist.bound ≤ deadEnd) :
    t.Consistent (improved t).eval := by
  have hval : (improved t).eval = fun s =>
      if isDead (compile t) s then deadEnd else baseValue (compile t) s := by
    funext s; exact value_eq _ _
  rw [hval]
  refine consistent_deadEnd _ _ ?_ ?_ ?_
  · exact fun op hop s hs happ hd => dead_closed _ _ _ (heff op hop s hs happ) hd
  · exact fun s => Nat.le_trans (baseValue_le _ s) hsize
  · exact fun op hop s hs happ hd hd' =>
      base_step _ _ _ (heff op hop s hs happ) op.cost (hcost op hop)

/-- Never overestimates the cost of reaching the goal. -/
theorem improved_admissible (t : Task)
    (hcompiled : ∀ x ∈ (compile t).nuts, x.1 ∈ t.goal)
    (heff : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      Effect (compile t) s (op.apply s))
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost)
    (hsize : 2 * (compile t).nuts.size + (compile t).dist.bound ≤ deadEnd) :
    t.Admissible (improved t).eval :=
  t.admissible _ (improved_goalAware t hcompiled) (improved_consistent t heff hcost hsize)

end Planner.ExampleHeuristics.Spanner

/- -------------------------------------------------------------------------- -/
/-
Spanner, stated at the schema level.

`Effect` in `Improved.lean` assumes how one action moves the four counters.  This
file assumes only what the domain's three schemas do to the predicates the
heuristic reads — which nuts are tightened, which spanners are usable and carried,
where the men stand — and derives the counters.  The lemmas doing the deriving are
already in `Improved.lean`; what was missing was a statement of the schemas to
feed them.

Spanner has exactly three schemas, so `Effect`'s fourth constructor, `other`, is
unreachable here.
-/

namespace Planner.ExampleHeuristics.Spanner

open Planner

/-- Carried and usable, as the counter reads it. -/
def carriedP (s : State) (sp : SpannerInfo) : Bool :=
  s.test sp.usableFact && sp.carryFacts.any fun f => s.test f

/-- Usable, on the ground, and still reachable. -/
def aheadP (d : Data) (s : State) (men : Array Nat) (sp : SpannerInfo) : Bool :=
  s.test sp.usableFact && !(sp.carryFacts.any fun f => s.test f) &&
    (match sp.atFacts.find? fun z => s.test z.1 with
     | some (_, l) => decide (d.dist.minFrom men l < d.dist.bound)
     | none => false)

/-- `tighten_nut`: one nut is tightened and the spanner used becomes unusable. -/
structure TightenStep (d : Data) (s s' : State) (x : Fact × Nat) (sp : SpannerInfo) :
    Prop where
  memX : x ∈ d.nuts
  nutBefore : s.test x.1 = false
  nutAfter : s'.test x.1 = true
  nutOther : ∀ y ∈ d.nuts, y ≠ x → s'.test y.1 = s.test y.1
  memSp : sp ∈ d.spanners
  spBefore : carriedP s sp = true
  spAfter : carriedP s' sp = false
  spOther : ∀ y ∈ d.spanners, y ≠ sp → carriedP s y = carriedP s' y
  /-- Nobody moved. -/
  menSame : menLocations d s' = menLocations d s
  /-- The spanner used was in hand, so it was never in the reachable-on-ground set. -/
  aheadSame : ∀ y ∈ d.spanners,
    aheadP d s' (menLocations d s') y = aheadP d s (menLocations d s) y
  /-- The nut tightened is the one the man is standing on. -/
  cover : ∀ y ∈ looseNuts d s,
    d.dist.minFrom (menLocations d s) y.2 = 0 ∨ y ∈ looseNuts d s'

/-- `pickup_spanner`: one usable spanner moves from the ground into a hand. -/
structure PickupStep (d : Data) (s s' : State) (sp : SpannerInfo) : Prop where
  memSp : sp ∈ d.spanners
  nutSame : ∀ y ∈ d.nuts, s'.test y.1 = s.test y.1
  spBefore : carriedP s sp = false
  spAfter : carriedP s' sp = true
  spOther : ∀ y ∈ d.spanners, y ≠ sp → carriedP s' y = carriedP s y
  menSame : menLocations d s' = menLocations d s
  /-- The spanner picked up leaves the reachable-on-ground set, and nothing joins it. -/
  aheadBefore : aheadP d s (menLocations d s) sp = true
  aheadAfter : aheadP d s' (menLocations d s') sp = false
  aheadOther : ∀ y ∈ d.spanners, y ≠ sp →
    aheadP d s (menLocations d s) y = aheadP d s' (menLocations d s') y

/-- `walk`: one man moves one link; nuts and spanners stay where they are. -/
structure WalkStep (d : Data) (s s' : State) : Prop where
  nutSame : ∀ y ∈ d.nuts, s'.test y.1 = s.test y.1
  spSame : ∀ y ∈ d.spanners, carriedP s' y = carriedP s y
  /-- Walking never brings a spanner within reach that was out of reach. -/
  aheadSub : ∀ y ∈ d.spanners,
    aheadP d s' (menLocations d s') y = true → aheadP d s (menLocations d s) y = true
  /-- One link changes every man's distance to any place by at most one. -/
  stepBound : ∀ l, ∀ w ∈ menLocations d s', ∃ u ∈ menLocations d s,
    d.dist.get u l ≤ 1 + d.dist.get w l

/-- One action of the domain. -/
inductive SchemaStep (d : Data) (s s' : State) : Prop
  | tighten (x : Fact × Nat) (sp : SpannerInfo) (h : TightenStep d s s' x sp)
  | pickup (sp : SpannerInfo) (h : PickupStep d s s' sp)
  | walk (h : WalkStep d s s')

/-! ### The counters, derived from the shapes -/

theorem looseNuts_congr {d : Data} {s s' : State}
    (h : ∀ y ∈ d.nuts, s'.test y.1 = s.test y.1) : looseNuts d s' = looseNuts d s :=
  array_filter_congr _ _ _ fun y hy => by simp [h y hy]

theorem effect_of_schema (d : Data) (s s' : State)
    (hnuts : d.nuts.toList.Nodup) (hsp : d.spanners.toList.Nodup)
    (he : SchemaStep d s s') : Effect d s s' := by
  cases he with
  | tighten x sp h =>
      refine .tighten ?_ ?_ ?_ ?_
      · exact unmet_size_drop d.nuts (·.1) x h.memX hnuts h.nutBefore h.nutAfter h.nutOther
      · exact carried_drop_one d s s' sp h.memSp hsp h.spBefore h.spAfter h.spOther
      · exact walk_le_of_tighten d s s' h.menSame h.cover
      · exact Nat.le_of_eq (ahead_mono d s s' _ _ h.aheadSame)
  | pickup sp h =>
      have hloose : looseNuts d s' = looseNuts d s := looseNuts_congr h.nutSame
      have hC : Cc d s + 1 = Cc d s' :=
        carried_gain_one d s s' sp h.memSp hsp h.spBefore h.spAfter h.spOther
      have hA : Ac d s' + 1 = Ac d s :=
        filter_size_drop_one d.spanners _ _ sp h.memSp hsp h.aheadBefore h.aheadAfter
          h.aheadOther
      refine .pickup ?_ hC ?_ ?_
      · show (looseNuts d s').size = (looseNuts d s).size
        rw [hloose]
      · show walkBound d s (menLocations d s) = walkBound d s' (menLocations d s')
        unfold walkBound
        rw [hloose, h.menSame]
      · omega
  | walk h =>
      have hloose : looseNuts d s' = looseNuts d s := looseNuts_congr h.nutSame
      refine .walk ?_ ?_ ?_ ?_
      · show (looseNuts d s').size = (looseNuts d s).size
        rw [hloose]
      · exact carried_unchanged d s s' h.spSame
      · exact walk_le_succ d s s' hloose h.stepBound
      · exact filter_size_le d.spanners _ _ h.aheadSub

/-- Zero at every goal state, assuming only what the schemas do. -/
theorem improved_goalAware_of_schema (t : Task)
    (hcompiled : ∀ x ∈ (compile t).nuts, x.1 ∈ t.goal) :
    t.GoalAware (improved t).eval := improved_goalAware t hcompiled

/-- And never falls by more than one action costs. -/
theorem improved_consistent_of_schema (t : Task)
    (hnuts : (compile t).nuts.toList.Nodup) (hsp : (compile t).spanners.toList.Nodup)
    (hstep : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      SchemaStep (compile t) s (op.apply s))
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost)
    (hsize : 2 * (compile t).nuts.size + (compile t).dist.bound ≤ deadEnd) :
    t.Consistent (improved t).eval :=
  improved_consistent t
    (fun op hop s hs happ => effect_of_schema _ s _ hnuts hsp (hstep op hop s hs happ))
    hcost hsize

/-- Never overestimates, assuming only that every operator is one of the schemas. -/
theorem improved_admissible_of_schema (t : Task)
    (hcompiled : ∀ x ∈ (compile t).nuts, x.1 ∈ t.goal)
    (hnuts : (compile t).nuts.toList.Nodup) (hsp : (compile t).spanners.toList.Nodup)
    (hstep : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      SchemaStep (compile t) s (op.apply s))
    (hcost : ∀ op ∈ t.ops, 1 ≤ op.cost)
    (hsize : 2 * (compile t).nuts.size + (compile t).dist.bound ≤ deadEnd) :
    t.Admissible (improved t).eval :=
  t.admissible _ (improved_goalAware_of_schema t hcompiled)
    (improved_consistent_of_schema t hnuts hsp hstep hcost hsize)

end Planner.ExampleHeuristics.Spanner

/- -------------------------------------------------------------------------- -/
/-
Which domain a Spanner task came from.

The equation on `actions` fixes the three schemas exactly as the parser produces
them.  The remaining lemmas expose their instantiated atoms, which lets the
heuristic proof reason about one lifted transition without mentioning grounding
or fact numbers.
-/

namespace Planner.Lifted.Spanner

open Planner Planner.Pddl

theorem at_dynamic {d : Domain} (hd : SpannerDomain d) :
    (staticPredicates d).contains "at" = false :=
  not_static_of_mem_del (a := walkA) (by rw [hd]; simp) (y := atV "?m" "?start")
    (by simp [walkA])

theorem carrying_dynamic {d : Domain} (hd : SpannerDomain d) :
    (staticPredicates d).contains "carrying" = false :=
  not_static_of_mem_add (a := pickupA) (by rw [hd]; simp)
    (y := carryingV "?m" "?s") (by simp [pickupA])

theorem usable_dynamic {d : Domain} (hd : SpannerDomain d) :
    (staticPredicates d).contains "usable" = false :=
  not_static_of_mem_del (a := tightenA) (by rw [hd]; simp) (y := usableV "?s")
    (by simp [tightenA])

theorem tightened_dynamic {d : Domain} (hd : SpannerDomain d) :
    (staticPredicates d).contains "tightened" = false :=
  not_static_of_mem_add (a := tightenA) (by rw [hd]; simp) (y := tightenedV "?n")
    (by simp [tightenA])

theorem loose_dynamic {d : Domain} (hd : SpannerDomain d) :
    (staticPredicates d).contains "loose" = false :=
  not_static_of_mem_del (a := tightenA) (by rw [hd]; simp) (y := looseV "?n")
    (by simp [tightenA])

/-! ### Instances -/

theorem instance_shape {d : Domain} {objects : List TypedName} (hd : SpannerDomain d)
    (i : Instance d objects) :
    (∃ l₁ l₂ m, i.schema = walkA ∧ i.args = [l₁, l₂, m]) ∨
    (∃ l s m, i.schema = pickupA ∧ i.args = [l, s, m]) ∨
    (∃ l s m n, i.schema = tightenA ∧ i.args = [l, s, m, n]) := by
  have hmem : i.schema ∈ [walkA, pickupA, tightenA] := hd ▸ i.mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with hs | hs | hs
  · obtain ⟨l₁, l₂, m, ha, -, -, -⟩ := i.args_three (by rw [hs])
    exact Or.inl ⟨l₁, l₂, m, hs, ha⟩
  · obtain ⟨l, s, m, ha, -, -, -⟩ := i.args_three (by rw [hs])
    exact Or.inr (Or.inl ⟨l, s, m, hs, ha⟩)
  · obtain ⟨l, s, m, n, ha, -, -, -, -⟩ := i.args_four (by rw [hs])
    exact Or.inr (Or.inr ⟨l, s, m, n, hs, ha⟩)

theorem walk_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {l₁ l₂ m : Name} (hs : i.schema = walkA) (ha : i.args = [l₁, l₂, m]) :
    atAtom m l₁ ∈ i.pre ∧ link l₁ l₂ ∈ i.pre ∧
    i.add = [atAtom m l₂] ∧ i.del = [atAtom m l₁] := by
  have hp : i.pre = [atAtom m l₁, link l₁ l₂] := by
    rw [i.pre_eq, hs, ha]
    rfl
  have hadd : i.add = [atAtom m l₂] := by rw [i.add_eq, hs, ha]; rfl
  have hdel : i.del = [atAtom m l₁] := by rw [i.del_eq, hs, ha]; rfl
  simp [hp, hadd, hdel]

theorem pickup_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {l s m : Name} (hs : i.schema = pickupA) (ha : i.args = [l, s, m]) :
    atAtom m l ∈ i.pre ∧ atAtom s l ∈ i.pre ∧
    i.add = [carrying m s] ∧ i.del = [atAtom s l] := by
  have hp : i.pre = [atAtom m l, atAtom s l] := by rw [i.pre_eq, hs, ha]; rfl
  have hadd : i.add = [carrying m s] := by rw [i.add_eq, hs, ha]; rfl
  have hdel : i.del = [atAtom s l] := by rw [i.del_eq, hs, ha]; rfl
  simp [hp, hadd, hdel]

theorem tighten_atoms {d : Domain} {objects : List TypedName} (i : Instance d objects)
    {l s m n : Name} (hs : i.schema = tightenA) (ha : i.args = [l, s, m, n]) :
    atAtom m l ∈ i.pre ∧ atAtom n l ∈ i.pre ∧ carrying m s ∈ i.pre ∧
    usable s ∈ i.pre ∧ loose n ∈ i.pre ∧
    i.add = [tightened n] ∧ i.del = [loose n, usable s] := by
  have hp : i.pre = [atAtom m l, atAtom n l, carrying m s, usable s, loose n] := by
    rw [i.pre_eq, hs, ha]
    rfl
  have hadd : i.add = [tightened n] := by rw [i.add_eq, hs, ha]; rfl
  have hdel : i.del = [loose n, usable s] := by rw [i.del_eq, hs, ha]; rfl
  simp [hp, hadd, hdel]

end Planner.Lifted.Spanner

/- -------------------------------------------------------------------------- -/
/-
Spanner's improved heuristic over ground atoms.

The data has the same shape as the compiled heuristic, but its tables contain
atoms instead of fact numbers.  This keeps the value close to the executable
one while making the consistency argument independent of grounding.
-/

namespace Planner.Lifted.Spanner

open Planner Planner.Pddl

structure SpannerInfo where
  usableAtom : GroundAtom
  carryAtoms : Array GroundAtom
  atAtoms : Array (GroundAtom × Nat)
  deriving Inhabited, DecidableEq

structure Cfg where
  dist : Distances
  menAt : Array (Array (GroundAtom × Nat))
  nuts : Array (GroundAtom × Nat)
  spanners : Array SpannerInfo
  deriving Inhabited

@[inline] def menLocations (c : Cfg) (σ : AtomState) : Array Nat :=
  c.menAt.filterMap fun atoms => (atoms.find? fun x => σ x.1).map (·.2)

@[inline] def looseNuts (c : Cfg) (σ : AtomState) : Array (GroundAtom × Nat) :=
  c.nuts.filter fun x => !σ x.1

@[inline] def walkBound (c : Cfg) (σ : AtomState) (men : Array Nat) : Nat :=
  (looseNuts c σ).foldl (init := 0) fun acc x => max acc (c.dist.minFrom men x.2)

@[inline] def carriedP (σ : AtomState) (sp : SpannerInfo) : Bool :=
  σ sp.usableAtom && sp.carryAtoms.any σ

@[inline] def carriedSpanners (c : Cfg) (σ : AtomState) : Array SpannerInfo :=
  c.spanners.filter (carriedP σ)

@[inline] def aheadP (c : Cfg) (σ : AtomState) (men : Array Nat)
    (sp : SpannerInfo) : Bool :=
  σ sp.usableAtom && !sp.carryAtoms.any σ &&
    (match sp.atAtoms.find? fun x => σ x.1 with
     | some (_, l) => decide (c.dist.minFrom men l < c.dist.bound)
     | none => false)

@[inline] def aheadSpanners (c : Cfg) (σ : AtomState) (men : Array Nat) :
    Array SpannerInfo := c.spanners.filter (aheadP c σ men)

def value (c : Cfg) (σ : AtomState) : Nat :=
  let men := menLocations c σ
  let loose := (looseNuts c σ).size
  let carried := (carriedSpanners c σ).size
  if loose == 0 then 0
  else if carried + (aheadSpanners c σ men).size < loose then deadEnd
  else loose + (loose - carried) + walkBound c σ men

/-! ### Goal awareness -/

theorem looseNuts_empty (c : Cfg) (σ : AtomState)
    (h : ∀ x ∈ c.nuts, σ x.1 = true) : looseNuts c σ = #[] := by
  unfold looseNuts
  rw [Array.filter_eq_empty_iff]
  intro x hx
  simp [h x hx]

theorem value_eq_zero (c : Cfg) (σ : AtomState)
    (h : ∀ x ∈ c.nuts, σ x.1 = true) : value c σ = 0 := by
  unfold value
  rw [looseNuts_empty c σ h]
  rfl

theorem liftedGoalAware (p : Problem) (c : Cfg)
    (hsub : ∀ x ∈ c.nuts, x.1 ∈ p.goal) : LiftedGoalAware p (value c) := by
  intro σ hgoal
  exact value_eq_zero c σ fun x hx => hgoal x.1 (by simpa using hsub x hx)

end Planner.Lifted.Spanner

/- -------------------------------------------------------------------------- -/
/-
Consistency of Spanner's improved heuristic at the lifted level.

The proof separates the predicate-level shape of one action from the arithmetic
of the value.  In particular, the dead-end constant is safe because the number
of usable spanners that remain available never increases while a loose nut
remains.
-/

namespace Planner.Lifted.Spanner

open Planner Planner.Pddl

abbrev Lc (c : Cfg) (σ : AtomState) : Nat := (looseNuts c σ).size
abbrev Cc (c : Cfg) (σ : AtomState) : Nat := (carriedSpanners c σ).size
abbrev Ac (c : Cfg) (σ : AtomState) : Nat :=
  (aheadSpanners c σ (menLocations c σ)).size
abbrev Wc (c : Cfg) (σ : AtomState) : Nat := walkBound c σ (menLocations c σ)

structure TightenStep (c : Cfg) (σ τ : AtomState)
    (x : GroundAtom × Nat) (sp : SpannerInfo) : Prop where
  memX : x ∈ c.nuts
  nutBefore : σ x.1 = false
  nutAfter : τ x.1 = true
  nutOther : ∀ y ∈ c.nuts, y ≠ x → τ y.1 = σ y.1
  memSp : sp ∈ c.spanners
  spBefore : carriedP σ sp = true
  spAfter : carriedP τ sp = false
  spOther : ∀ y ∈ c.spanners, y ≠ sp → carriedP σ y = carriedP τ y
  menSame : menLocations c τ = menLocations c σ
  aheadSame : ∀ y ∈ c.spanners,
    aheadP c τ (menLocations c τ) y = aheadP c σ (menLocations c σ) y
  cover : ∀ y ∈ looseNuts c σ,
    c.dist.minFrom (menLocations c σ) y.2 = 0 ∨ y ∈ looseNuts c τ

structure PickupStep (c : Cfg) (σ τ : AtomState) (sp : SpannerInfo) : Prop where
  memSp : sp ∈ c.spanners
  nutSame : ∀ y ∈ c.nuts, τ y.1 = σ y.1
  spBefore : carriedP σ sp = false
  spAfter : carriedP τ sp = true
  spOther : ∀ y ∈ c.spanners, y ≠ sp → carriedP τ y = carriedP σ y
  menSame : menLocations c τ = menLocations c σ
  aheadBefore : aheadP c σ (menLocations c σ) sp = true
  aheadAfter : aheadP c τ (menLocations c τ) sp = false
  aheadOther : ∀ y ∈ c.spanners, y ≠ sp →
    aheadP c σ (menLocations c σ) y = aheadP c τ (menLocations c τ) y

structure WalkStep (c : Cfg) (σ τ : AtomState) : Prop where
  nutSame : ∀ y ∈ c.nuts, τ y.1 = σ y.1
  spSame : ∀ y ∈ c.spanners, carriedP τ y = carriedP σ y
  aheadSub : ∀ y ∈ c.spanners,
    aheadP c τ (menLocations c τ) y = true →
      aheadP c σ (menLocations c σ) y = true
  stepBound : ∀ l, ∀ w ∈ menLocations c τ, ∃ u ∈ menLocations c σ,
    c.dist.get u l ≤ 1 + c.dist.get w l

/--
A step that discharges no goal nut.  Two actions have this shape: tightening a
nut the goal does not ask for, which spends a spanner without shortening the
list, and picking up a spanner already spent, which changes nothing the value
reads.  Neither can be a `TightenStep` or a `PickupStep`, because both of those
say a count moves by exactly one.
-/
structure StallStep (c : Cfg) (σ τ : AtomState) : Prop where
  nutSame : ∀ y ∈ c.nuts, τ y.1 = σ y.1
  carriedDrop : ∀ y ∈ c.spanners, carriedP τ y = true → carriedP σ y = true
  menSame : menLocations c τ = menLocations c σ
  aheadDrop : ∀ y ∈ c.spanners,
    aheadP c τ (menLocations c τ) y = true → aheadP c σ (menLocations c σ) y = true

inductive SchemaStep (c : Cfg) (σ τ : AtomState) : Prop
  | tighten (x : GroundAtom × Nat) (sp : SpannerInfo) (h : TightenStep c σ τ x sp)
  | pickup (sp : SpannerInfo) (h : PickupStep c σ τ sp)
  | walk (h : WalkStep c σ τ)
  | stall (h : StallStep c σ τ)

theorem loose_drop {c : Cfg} {σ τ : AtomState} {x : GroundAtom × Nat}
    (h : TightenStep c σ τ x sp) (hnd : c.nuts.toList.Nodup) :
    Lc c τ + 1 = Lc c σ := by
  unfold Lc looseNuts
  rw [size_filter_toList, size_filter_toList]
  refine length_filter_erase_one _ _ _ x (by simpa using h.memX) hnd
    (by simp [h.nutBefore]) (by simp [h.nutAfter]) ?_
  intro y hy hne
  rw [h.nutOther y (by simpa using hy) hne]

theorem carried_drop {c : Cfg} {σ τ : AtomState} {x : GroundAtom × Nat}
    {sp : SpannerInfo} (h : TightenStep c σ τ x sp)
    (hnd : c.spanners.toList.Nodup) : Cc c τ + 1 = Cc c σ := by
  unfold Cc carriedSpanners
  rw [size_filter_toList, size_filter_toList]
  refine length_filter_erase_one _ _ _ sp (by simpa using h.memSp) hnd h.spBefore h.spAfter ?_
  intro y hy hne
  exact h.spOther y (by simpa using hy) hne

theorem loose_congr {c : Cfg} {σ τ : AtomState}
    (h : ∀ y ∈ c.nuts, τ y.1 = σ y.1) : looseNuts c τ = looseNuts c σ :=
  array_filter_congr _ _ _ fun y hy => by simp [h y hy]

theorem carried_gain {c : Cfg} {σ τ : AtomState} {sp : SpannerInfo}
    (h : PickupStep c σ τ sp) (hnd : c.spanners.toList.Nodup) :
    Cc c σ + 1 = Cc c τ := by
  unfold Cc carriedSpanners
  rw [size_filter_toList, size_filter_toList]
  refine length_filter_erase_one _ _ _ sp (by simpa using h.memSp) hnd h.spAfter h.spBefore ?_
  intro y hy hne
  exact h.spOther y (by simpa using hy) hne

theorem carried_congr {c : Cfg} {σ τ : AtomState}
    (h : ∀ y ∈ c.spanners, carriedP τ y = carriedP σ y) : Cc c τ = Cc c σ := by
  unfold Cc carriedSpanners
  rw [size_filter_toList, size_filter_toList]
  exact length_filter_congr _ _ _ fun y hy => h y (by simpa using hy)

theorem walk_le_of_tighten {c : Cfg} {σ τ : AtomState} {x : GroundAtom × Nat}
    {sp : SpannerInfo} (h : TightenStep c σ τ x sp) : Wc c σ ≤ Wc c τ := by
  unfold Wc walkBound
  rw [h.menSame, ← Array.foldl_toList, ← Array.foldl_toList]
  refine foldl_max_le_bound (looseNuts c σ).toList _ _ ?_ 0 (Nat.zero_le _)
  intro y hy
  rcases h.cover y (by simpa using hy) with hzero | hmem
  · rw [hzero]
    exact Nat.zero_le _
  · exact foldl_max_ge_mem (looseNuts c τ).toList
      (fun z => c.dist.minFrom (menLocations c σ) z.2) (by simpa using hmem) 0

theorem walk_le_succ {c : Cfg} {σ τ : AtomState} (h : WalkStep c σ τ) :
    Wc c σ ≤ Wc c τ + 1 := by
  have hloose := loose_congr h.nutSame
  unfold Wc walkBound
  rw [hloose, ← Array.foldl_toList, ← Array.foldl_toList]
  have key := foldl_max_le_succ (looseNuts c σ).toList
    (fun x => c.dist.minFrom (menLocations c σ) x.2)
    (fun x => c.dist.minFrom (menLocations c τ) x.2)
    (fun x _ => minFrom_le_succ c.dist _ _ x.2 (h.stepBound x.2)) 0 0 (by omega)
  simpa [Nat.add_comm] using key

theorem ahead_same {c : Cfg} {σ τ : AtomState} {x : GroundAtom × Nat}
    {sp : SpannerInfo} (h : TightenStep c σ τ x sp) : Ac c τ = Ac c σ := by
  unfold Ac aheadSpanners
  rw [size_filter_toList, size_filter_toList]
  exact length_filter_congr _ _ _ fun y hy => h.aheadSame y (by simpa using hy)

theorem ahead_drop {c : Cfg} {σ τ : AtomState} {sp : SpannerInfo}
    (h : PickupStep c σ τ sp) (hnd : c.spanners.toList.Nodup) : Ac c τ + 1 = Ac c σ := by
  unfold Ac aheadSpanners
  rw [size_filter_toList, size_filter_toList]
  refine length_filter_erase_one _ _ _ sp (by simpa using h.memSp) hnd
    h.aheadBefore h.aheadAfter ?_
  intro y hy hne
  exact h.aheadOther y (by simpa using hy) hne

theorem ahead_le {c : Cfg} {σ τ : AtomState} (h : WalkStep c σ τ) : Ac c τ ≤ Ac c σ :=
  filter_size_le c.spanners _ _ h.aheadSub

inductive Effect (c : Cfg) (σ τ : AtomState) : Prop
  | tighten (hL : Lc c τ + 1 = Lc c σ) (hC : Cc c τ + 1 = Cc c σ)
      (hW : Wc c σ ≤ Wc c τ) (hA : Ac c τ ≤ Ac c σ)
  | pickup (hL : Lc c τ = Lc c σ) (hC : Cc c σ + 1 = Cc c τ)
      (hW : Wc c σ = Wc c τ) (hR : Cc c τ + Ac c τ ≤ Cc c σ + Ac c σ)
  | walk (hL : Lc c τ = Lc c σ) (hC : Cc c τ = Cc c σ)
      (hW : Wc c σ ≤ Wc c τ + 1) (hA : Ac c τ ≤ Ac c σ)
  | consume (hL : Lc c τ = Lc c σ) (hC : Cc c τ ≤ Cc c σ)
      (hW : Wc c σ ≤ Wc c τ) (hA : Ac c τ ≤ Ac c σ)

theorem effect_of_schema (c : Cfg) (σ τ : AtomState)
    (hn : c.nuts.toList.Nodup) (hs : c.spanners.toList.Nodup)
    (h : SchemaStep c σ τ) : Effect c σ τ := by
  cases h with
  | tighten x sp h =>
      exact .tighten (loose_drop h hn) (carried_drop h hs) (walk_le_of_tighten h)
        (Nat.le_of_eq (ahead_same h))
  | pickup sp h =>
      have hl := loose_congr h.nutSame
      have hc := carried_gain h hs
      have ha := ahead_drop h hs
      refine .pickup ?_ hc ?_ ?_
      · exact congrArg Array.size hl
      · unfold Wc walkBound
        rw [hl, h.menSame]
      · omega
  | walk h =>
      exact .walk (congrArg Array.size (loose_congr h.nutSame)) (carried_congr h.spSame)
        (walk_le_succ h) (ahead_le h)
  | stall h =>
      have hl := loose_congr h.nutSame
      refine .consume (congrArg Array.size hl) (filter_size_le c.spanners _ _ h.carriedDrop)
        ?_ (filter_size_le c.spanners _ _ h.aheadDrop)
      unfold Wc walkBound
      rw [hl, h.menSame]

def isDead (c : Cfg) (σ : AtomState) : Bool :=
  !(Lc c σ == 0) && decide (Cc c σ + Ac c σ < Lc c σ)

def baseValue (c : Cfg) (σ : AtomState) : Nat :=
  if Lc c σ == 0 then 0 else Lc c σ + (Lc c σ - Cc c σ) + Wc c σ

theorem value_eq (c : Cfg) (σ : AtomState) :
    value c σ = if isDead c σ then deadEnd else baseValue c σ := by
  unfold value isDead baseValue
  by_cases h : Lc c σ == 0
  · simp [h]
  · simp only [h, Bool.not_false, Bool.true_and, decide_eq_true_eq]
    split <;> simp_all

theorem dead_closed {c : Cfg} {σ τ : AtomState} (h : Effect c σ τ)
    (hd : isDead c σ = true) : isDead c τ = true := by
  simp only [isDead, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
    Bool.not_eq_true', decide_eq_true_eq] at hd ⊢
  obtain ⟨hne, hlt⟩ := hd
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq] at hne ⊢
  cases h with
  | tighten hL hC _ hA => exact ⟨by omega, by omega⟩
  | pickup hL hC _ hR => exact ⟨by omega, by omega⟩
  | walk hL hC _ hA => exact ⟨by omega, by omega⟩
  | consume hL hC _ hA => exact ⟨by omega, by omega⟩

private theorem step_arith (L C W L' C' W' cost : Nat) (hcost : 1 ≤ cost)
    (hz' : L' = 0 → W' = 0)
    (h : (L' + 1 = L ∧ C' + 1 = C ∧ W ≤ W') ∨
         (L' = L ∧ C + 1 = C' ∧ W = W') ∨
         (L' = L ∧ C' = C ∧ W ≤ W' + 1) ∨
         (L' = L ∧ C' ≤ C ∧ W ≤ W')) :
    (if L == 0 then 0 else L + (L - C) + W)
      ≤ cost + (if L' == 0 then 0 else L' + (L' - C') + W') := by
  by_cases hz : L = 0
  · simp [hz]
  · by_cases hz0 : L' = 0
    · have hw0 := hz' hz0
      simp only [hz0, hz, beq_self_eq_true, if_true, beq_iff_eq]
      rw [if_neg (by simp [hz])]
      rcases h with ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ <;> omega
    · simp only [beq_iff_eq]
      rw [if_neg hz, if_neg hz0]
      rcases h with ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ <;> omega

theorem walkBound_zero (c : Cfg) (σ : AtomState) (h : Lc c σ = 0) : Wc c σ = 0 := by
  have he : looseNuts c σ = #[] := Array.size_eq_zero_iff.mp h
  unfold Wc walkBound
  rw [he]
  rfl

theorem base_step {c : Cfg} {σ τ : AtomState} (h : Effect c σ τ)
    (cost : Nat) (hcost : 1 ≤ cost) : baseValue c σ ≤ cost + baseValue c τ := by
  unfold baseValue
  refine step_arith _ _ _ _ _ _ cost hcost (fun hz => walkBound_zero c τ hz) ?_
  cases h with
  | tighten hL hC hW _ => exact Or.inl ⟨hL, hC, hW⟩
  | pickup hL hC hW _ => exact Or.inr (Or.inl ⟨hL, hC, hW⟩)
  | walk hL hC hW _ => exact Or.inr (Or.inr (Or.inl ⟨hL, hC, hW⟩))
  | consume hL hC hW _ => exact Or.inr (Or.inr (Or.inr ⟨hL, hC, hW⟩))

theorem walkBound_le (c : Cfg) (σ : AtomState) (men : Array Nat) :
    walkBound c σ men ≤ c.dist.bound := by
  unfold walkBound
  rw [← Array.foldl_toList]
  refine foldl_max_le_bound (looseNuts c σ).toList _ _ ?_ 0 (Nat.zero_le _)
  intro x hx
  exact Distances.minFrom_le _ _ _

theorem baseValue_le (c : Cfg) (σ : AtomState) :
    baseValue c σ ≤ 2 * c.nuts.size + c.dist.bound := by
  unfold baseValue
  split
  · omega
  · have hL : Lc c σ ≤ c.nuts.size := Array.size_filter_le
    have hW : Wc c σ ≤ c.dist.bound := walkBound_le c σ (menLocations c σ)
    omega

theorem value_step (c : Cfg) (σ τ : AtomState)
    (hn : c.nuts.toList.Nodup) (hs : c.spanners.toList.Nodup)
    (hshape : SchemaStep c σ τ) (cost : Nat) (hcost : 1 ≤ cost)
    (hsize : 2 * c.nuts.size + c.dist.bound ≤ deadEnd) :
    value c σ ≤ cost + value c τ := by
  have he := effect_of_schema c σ τ hn hs hshape
  rw [value_eq, value_eq]
  by_cases hd : isDead c σ = true
  · rw [if_pos hd, if_pos (dead_closed he hd)]
    omega
  · rw [if_neg (by simpa using hd)]
    by_cases hd' : isDead c τ = true
    · rw [if_pos hd']
      exact Nat.le_trans (baseValue_le c σ) (Nat.le_trans hsize (Nat.le_add_left _ _))
    · rw [if_neg (by simpa using hd')]
      exact base_step he cost hcost

theorem liftedConsistent {d : Domain} {p : Problem} (rel : Bool) (c : Cfg)
    (Inv : AtomState → Prop)
    (hn : c.nuts.toList.Nodup) (hs : c.spanners.toList.Nodup)
    (hshape : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ → o.applicableA σ →
      SchemaStep c σ (o.applyA σ))
    (hcost : ∀ o ∈ groundedOps d p rel, 0 < o.cost)
    (hsize : 2 * c.nuts.size + c.dist.bound ≤ deadEnd) :
    LiftedConsistentOn d p rel Inv (value c) := by
  intro o ho σ hinv happ
  exact value_step c σ (o.applyA σ) hn hs (hshape o ho σ hinv happ) o.cost
    (hcost o ho) hsize

/-! ### The compiled boundary -/

theorem improved_goalAwareOn (d : Domain) (p : Problem) (rel : Bool) (c : Cfg)
    (Inv : AtomState → Prop)
    (hwf : Task.WF (ground d p rel))
    (hcost : ∀ o ∈ groundedOps d p rel, 0 < o.cost)
    (hsub : ∀ x ∈ c.nuts, x.1 ∈ p.goal)
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hpres : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ →
      o.applicableA σ → Inv (o.applyA σ))
    (hv : State → Nat) (hcomp : ComputesOn (ground d p rel) Inv hv (value c)) :
    (ground d p rel).GoalAwareOn (Reachable (ground d p rel)) hv :=
  goalAwareOn_of_lifted d p rel hwf hcost hv (value c) Inv hcomp hinit hpres
    (liftedGoalAware p c hsub)

theorem improved_consistentOn (d : Domain) (p : Problem) (rel : Bool) (c : Cfg)
    (Inv : AtomState → Prop)
    (hwf : Task.WF (ground d p rel))
    (hcost : ∀ o ∈ groundedOps d p rel, 0 < o.cost)
    (hn : c.nuts.toList.Nodup) (hs : c.spanners.toList.Nodup)
    (hshape : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ → o.applicableA σ →
      SchemaStep c σ (o.applyA σ))
    (hsize : 2 * c.nuts.size + c.dist.bound ≤ deadEnd)
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hpres : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ →
      o.applicableA σ → Inv (o.applyA σ))
    (hv : State → Nat) (hcomp : ComputesOn (ground d p rel) Inv hv (value c)) :
    (ground d p rel).ConsistentOn (Reachable (ground d p rel)) hv :=
  consistentOn_of_lifted d p rel hwf hcost hv (value c) Inv hcomp hinit hpres
    (liftedConsistent rel c Inv hn hs hshape hcost hsize)

theorem improved_admissibleOn (d : Domain) (p : Problem) (rel : Bool) (c : Cfg)
    (Inv : AtomState → Prop)
    (hwf : Task.WF (ground d p rel))
    (hcost : ∀ o ∈ groundedOps d p rel, 0 < o.cost)
    (hsub : ∀ x ∈ c.nuts, x.1 ∈ p.goal)
    (hn : c.nuts.toList.Nodup) (hs : c.spanners.toList.Nodup)
    (hshape : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ → o.applicableA σ →
      SchemaStep c σ (o.applyA σ))
    (hsize : 2 * c.nuts.size + c.dist.bound ≤ deadEnd)
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hpres : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ →
      o.applicableA σ → Inv (o.applyA σ))
    (hv : State → Nat) (hcomp : ComputesOn (ground d p rel) Inv hv (value c)) :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel)) hv :=
  admissibleOn_of_lifted d p rel hwf hcost hv (value c) Inv hcomp hinit hpres
    (liftedGoalAware p c hsub) (liftedConsistent rel c Inv hn hs hshape hcost hsize)

end Planner.Lifted.Spanner

/- -------------------------------------------------------------------------- -/
/-
The compiled Spanner tables and their atom-level meaning.

Each relation below says that a fact number names the atom in the corresponding
lifted entry.  The value theorem then follows structurally: paired searches find
the same location, paired filters retain the same entries, and both sides fold
the same distance table.
-/

namespace Planner.Lifted.Spanner

open Planner Planner.Pddl

abbrev CData := ExampleHeuristics.Spanner.Data
abbrev CSpanner := ExampleHeuristics.Spanner.SpannerInfo

structure FactMatch (t : Task) (f : Fact) (a : GroundAtom) : Prop where
  name : t.factNames.getD f default = a
  range : f < t.factNames.size

structure PairMatch (t : Task) (x : Fact × Nat) (y : GroundAtom × Nat) : Prop where
  fact : FactMatch t x.1 y.1
  index : x.2 = y.2

structure SpannerMatch (t : Task) (x : CSpanner) (y : SpannerInfo) : Prop where
  usable : FactMatch t x.usableFact y.usableAtom
  carry : List.Forall₂ (FactMatch t) x.carryFacts.toList y.carryAtoms.toList
  positions : List.Forall₂ (PairMatch t) x.atFacts.toList y.atAtoms.toList

structure DataMatches (t : Task) (c : Cfg) (dd : CData) : Prop where
  dist : dd.dist = c.dist
  men : List.Forall₂ (fun xs ys =>
    List.Forall₂ (PairMatch t) xs.toList ys.toList) dd.menAt.toList c.menAt.toList
  nuts : List.Forall₂ (PairMatch t) dd.nuts.toList c.nuts.toList
  spanners : List.Forall₂ (SpannerMatch t) dd.spanners.toList c.spanners.toList

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

private theorem locations_eq {t : Task}
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
      have hloc :
          (xs.find? fun x => s.test x.1).map (fun x => x.2) =
            (ys.find? fun y => σ y.1).map (fun y => y.2) := by
        rw [← Array.find?_toList, ← Array.find?_toList]
        exact findLoc_eq hxy habs hn
      simp only [List.filterMap_cons]
      rw [hloc, ih]

theorem menLocations_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Spanner.menLocations dd s = menLocations c σ := by
  apply Array.toList_inj.mp
  simpa [ExampleHeuristics.Spanner.menLocations, menLocations,
    Array.toList_filterMap] using locations_eq hm.men habs hn

private theorem filterPairs {t : Task} {xs : List (Fact × Nat)}
    {ys : List (GroundAtom × Nat)} (hm : List.Forall₂ (PairMatch t) xs ys)
    {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) :
    List.Forall₂ (PairMatch t)
      (xs.filter fun x => !s.test x.1) (ys.filter fun y => !σ y.1) := by
  induction hm with
  | nil => exact .nil
  | @cons x y xs ys hxy _ ih =>
      have ht := test_eq habs hn hxy.fact
      simp only [List.filter_cons, ht]
      by_cases hp : σ y.1
      · simp [hp, ih]
      · simp [hp, ih, hxy]

theorem looseNuts_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    List.Forall₂ (PairMatch t)
      (ExampleHeuristics.Spanner.looseNuts dd s).toList (looseNuts c σ).toList := by
  simpa [ExampleHeuristics.Spanner.looseNuts, looseNuts, Array.toList_filter]
    using filterPairs hm.nuts habs hn

private theorem anyFacts_eq {t : Task} {fs : List Fact} {as : List GroundAtom}
    (hm : List.Forall₂ (FactMatch t) fs as) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    fs.any s.test = as.any σ :=
  forall₂_any hm (fun _ _ h => test_eq habs hn h)

private theorem carriedP_matches {t : Task} {x : CSpanner} {y : SpannerInfo}
    (hm : SpannerMatch t x y) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    (s.test x.usableFact && x.carryFacts.any s.test) = carriedP σ y := by
  unfold carriedP
  rw [test_eq habs hn hm.usable]
  have hcarry : x.carryFacts.any s.test = y.carryAtoms.any σ := by
    simpa [Array.any_toList] using anyFacts_eq hm.carry habs hn
  rw [hcarry]

private theorem aheadP_matches {t : Task} {c : Cfg} {dd : CData}
    (hd : dd.dist = c.dist) {x : CSpanner} {y : SpannerInfo}
    (hm : SpannerMatch t x y) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size)
    (hmen : ExampleHeuristics.Spanner.menLocations dd s = menLocations c σ) :
    (s.test x.usableFact && !(x.carryFacts.any s.test) &&
      (match x.atFacts.find? fun z => s.test z.1 with
       | some (_, l) => decide (dd.dist.minFrom
           (ExampleHeuristics.Spanner.menLocations dd s) l < dd.dist.bound)
       | none => false)) = aheadP c σ (menLocations c σ) y := by
  unfold aheadP
  rw [test_eq habs hn hm.usable]
  have hcarry : x.carryFacts.any s.test = y.carryAtoms.any σ := by
    simpa [Array.any_toList] using anyFacts_eq hm.carry habs hn
  rw [hcarry]
  have hloc :
      (x.atFacts.find? fun z => s.test z.1).map (fun z => z.2) =
        (y.atAtoms.find? fun z => σ z.1).map (fun z => z.2) := by
    rw [← Array.find?_toList, ← Array.find?_toList]
    exact findLoc_eq hm.positions habs hn
  rcases hf : x.atFacts.find? (fun z => s.test z.1) with _ | ⟨f, l⟩
  · rw [hf] at hloc
    simp only [Option.map_none] at hloc
    have hg : y.atAtoms.find? (fun z => σ z.1) = none := by
      cases h : y.atAtoms.find? (fun z => σ z.1) with
      | none => rfl
      | some z => simp [h] at hloc
    simp [hf, hg]
  · rw [hf] at hloc
    simp only [Option.map_some] at hloc
    rcases hg : y.atAtoms.find? (fun z => σ z.1) with _ | ⟨a, k⟩
    · simp [hg] at hloc
    · simp only [hg, Option.map_some, Option.some.injEq] at hloc
      subst k
      simp [hf, hg, hd, hmen]

private theorem filterLength_eq {t : Task} {xs : List CSpanner} {ys : List SpannerInfo}
    (hm : List.Forall₂ (SpannerMatch t) xs ys) (P : CSpanner → Bool)
    (Q : SpannerInfo → Bool) (hpq : ∀ x y, SpannerMatch t x y → P x = Q y) :
    (xs.filter P).length = (ys.filter Q).length := by
  induction hm with
  | nil => rfl
  | @cons x y xs ys hxy _ ih =>
      have h := hpq x y hxy
      simp only [List.filter_cons]
      rw [h]
      cases Q y <;> simp [ih]

theorem carriedSpanners_size_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    (ExampleHeuristics.Spanner.carriedSpanners dd s).size = (carriedSpanners c σ).size := by
  rw [← Array.length_toList, ← Array.length_toList]
  simpa [ExampleHeuristics.Spanner.carriedSpanners, carriedSpanners, Array.toList_filter]
    using filterLength_eq hm.spanners _ _
      (fun _ _ h => carriedP_matches h habs hn)

theorem aheadSpanners_size_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    (ExampleHeuristics.Spanner.aheadSpanners dd s
      (ExampleHeuristics.Spanner.menLocations dd s)).size =
      (aheadSpanners c σ (menLocations c σ)).size := by
  have hmen := menLocations_matches hm habs hn
  rw [← Array.length_toList, ← Array.length_toList]
  simpa [ExampleHeuristics.Spanner.aheadSpanners, aheadSpanners,
    Array.toList_filter] using
    filterLength_eq hm.spanners _ _
      (fun _ _ h => aheadP_matches hm.dist h habs hn hmen)

private theorem foldWalk_eq {t : Task} {c : Cfg} {dd : CData}
    (hd : dd.dist = c.dist) (men : Array Nat)
    {xs : List (Fact × Nat)} {ys : List (GroundAtom × Nat)}
    (hm : List.Forall₂ (PairMatch t) xs ys) (acc : Nat) :
    xs.foldl (fun acc x => max acc (dd.dist.minFrom men x.2)) acc =
      ys.foldl (fun acc y => max acc (c.dist.minFrom men y.2)) acc := by
  rw [hd]
  induction hm generalizing acc with
  | nil => rfl
  | @cons x y xs ys hxy _ ih =>
      simp only [List.foldl_cons, hxy.index]
      exact ih _

theorem walkBound_matches {t : Task} {c : Cfg} {dd : CData}
    (hm : DataMatches t c dd) {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size) :
    ExampleHeuristics.Spanner.walkBound dd s
      (ExampleHeuristics.Spanner.menLocations dd s) =
      walkBound c σ (menLocations c σ) := by
  have hloose := looseNuts_matches hm habs hn
  have hmen := menLocations_matches hm habs hn
  unfold ExampleHeuristics.Spanner.walkBound walkBound
  rw [← Array.foldl_toList, ← Array.foldl_toList, hmen]
  exact foldWalk_eq hm.dist _ hloose 0

/-- The executable Spanner value computes the atom-level value. -/
theorem computes {t : Task} {c : Cfg} {dd : CData} (hm : DataMatches t c dd)
    (hn : t.numFacts = t.factNames.size) :
    Computes t (ExampleHeuristics.Spanner.value dd) (value c) := by
  intro s σ habs _
  have hmen := menLocations_matches hm habs hn
  have hloose : (ExampleHeuristics.Spanner.looseNuts dd s).size =
      (looseNuts c σ).size := by
    simpa using (looseNuts_matches hm habs hn).length_eq
  have hcarried := carriedSpanners_size_matches hm habs hn
  have hahead := aheadSpanners_size_matches hm habs hn
  have hwalk := walkBound_matches hm habs hn
  rw [hmen] at hahead hwalk
  unfold ExampleHeuristics.Spanner.value value
  simp only
  rw [hmen, hloose, hcarried, hahead, hwalk]

/-! ### The executable boundary -/

theorem computesOn_of_matches {t : Task} {c : Cfg} {dd : CData}
    (Inv : AtomState → Prop) (hm : DataMatches t c dd)
    (hn : t.numFacts = t.factNames.size) :
    ComputesOn t Inv (ExampleHeuristics.Spanner.value dd) (value c) := by
  intro s σ habs _
  exact computes hm hn s σ habs trivial

set_option maxHeartbeats 1000000 in
/-- Goal awareness for the compiled value, after its tables have been matched. -/
theorem compiled_goalAwareOn (d : Domain) (p : Problem) (rel : Bool) (c : Cfg)
    (Inv : AtomState → Prop)
    (hm : DataMatches (ground d p rel) c
      (ExampleHeuristics.Spanner.compile (ground d p rel)))
    (hwf : Task.WF (ground d p rel))
    (hcost : ∀ o ∈ groundedOps d p rel, 0 < o.cost)
    (hsub : ∀ x ∈ c.nuts, x.1 ∈ p.goal)
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hpres : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ →
      o.applicableA σ → Inv (o.applyA σ)) :
    (ground d p rel).GoalAwareOn (Reachable (ground d p rel))
      (ExampleHeuristics.Spanner.improved (ground d p rel)).eval :=
  improved_goalAwareOn d p rel c (Inv := Inv) hwf hcost hsub hinit hpres _
    (computesOn_of_matches Inv hm rfl)

set_option maxHeartbeats 1000000 in
/-- Consistency for the compiled value, after its tables have been matched. -/
theorem compiled_consistentOn (d : Domain) (p : Problem) (rel : Bool) (c : Cfg)
    (Inv : AtomState → Prop)
    (hm : DataMatches (ground d p rel) c
      (ExampleHeuristics.Spanner.compile (ground d p rel)))
    (hwf : Task.WF (ground d p rel))
    (hcost : ∀ o ∈ groundedOps d p rel, 0 < o.cost)
    (hn : c.nuts.toList.Nodup) (hs : c.spanners.toList.Nodup)
    (hshape : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ →
      o.applicableA σ → SchemaStep c σ (o.applyA σ))
    (hsize : 2 * c.nuts.size + c.dist.bound ≤ deadEnd)
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hpres : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ →
      o.applicableA σ → Inv (o.applyA σ)) :
    (ground d p rel).ConsistentOn (Reachable (ground d p rel))
      (ExampleHeuristics.Spanner.improved (ground d p rel)).eval :=
  improved_consistentOn d p rel c (Inv := Inv) hwf hcost hn hs hshape hsize hinit hpres _
    (computesOn_of_matches Inv hm rfl)

set_option maxHeartbeats 1000000 in
/-- Admissibility follows from the two executable properties. -/
theorem compiled_admissibleOn (d : Domain) (p : Problem) (rel : Bool) (c : Cfg)
    (Inv : AtomState → Prop)
    (hm : DataMatches (ground d p rel) c
      (ExampleHeuristics.Spanner.compile (ground d p rel)))
    (hwf : Task.WF (ground d p rel))
    (hcost : ∀ o ∈ groundedOps d p rel, 0 < o.cost)
    (hsub : ∀ x ∈ c.nuts, x.1 ∈ p.goal)
    (hn : c.nuts.toList.Nodup) (hs : c.spanners.toList.Nodup)
    (hshape : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ →
      o.applicableA σ → SchemaStep c σ (o.applyA σ))
    (hsize : 2 * c.nuts.size + c.dist.bound ≤ deadEnd)
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hpres : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ →
      o.applicableA σ → Inv (o.applyA σ)) :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel))
      (ExampleHeuristics.Spanner.improved (ground d p rel)).eval :=
  improved_admissibleOn d p rel c (Inv := Inv) hwf hcost hsub hn hs hshape hsize hinit hpres _
    (computesOn_of_matches Inv hm rfl)

end Planner.Lifted.Spanner

/- -------------------------------------------------------------------------- -/
/-
The bridge from `compile` to the lifted `Cfg`.

`Proofs/Lifted/SpannerComputes.lean` says what it takes for the compiled tables
and a lifted `Cfg` to agree: each fact number names the atom in the corresponding
lifted entry.  This file supplies such a `Cfg` — the one that reads every fact of
`compile` through the task's own names — and discharges the agreement outright.

What is left after this file is the shape of one transition, `SchemaStep`, which
is about the domain's schemas rather than about the tables.
-/

namespace Planner.Lifted.Spanner

open Planner Planner.Pddl

/-! ### The `Cfg` a task describes -/

/-- The atom a fact number names. -/
abbrev atomOf (t : Task) (f : Fact) : GroundAtom := t.factNames.getD f default

/-- One compiled spanner record, read through the task's names. -/
def spannerOf (t : Task) (x : CSpanner) : SpannerInfo where
  usableAtom := atomOf t x.usableFact
  carryAtoms := x.carryFacts.map (atomOf t)
  atAtoms := x.atFacts.map fun y => (atomOf t y.1, y.2)

/-- The configuration a spanner task describes. -/
def cfgOf (t : Task) : Cfg where
  dist := (ExampleHeuristics.Spanner.compile t).dist
  menAt := (ExampleHeuristics.Spanner.compile t).menAt.map fun xs =>
    xs.map fun y => (atomOf t y.1, y.2)
  nuts := (ExampleHeuristics.Spanner.compile t).nuts.map fun y => (atomOf t y.1, y.2)
  spanners := (ExampleHeuristics.Spanner.compile t).spanners.map (spannerOf t)

/-! ### Every fact the tables hold is numbered

`FactMatch` asks two things of a fact: that it names the atom the lifted entry
holds, which `cfgOf` makes true by construction, and that it is in range.  The
range is what the tables have to earn.
-/

theorem atOf_range (t : Task) (g : Graph) (who : Name) :
    ∀ y ∈ ExampleHeuristics.Spanner.atOf (t.factsWith "at") g who,
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
                intro h
                rw [← h]
                exact hzr
            · simp only [Bool.not_eq_true] at hx
              simp [hx]

theorem carryFacts_range (t : Task) (sp : Name) :
    ∀ f ∈ (t.factsWith "carrying").filterMap (fun z =>
      match z.2.args with
      | [_, x] => if x == sp then some z.1 else none
      | _ => none), f < t.factNames.size := by
  intro f hf
  obtain ⟨z, hz, hval⟩ := Array.mem_filterMap.mp hf
  have hzr : z.1 < t.factNames.size := factsWith_ok z hz
  revert hval
  rcases hargs : z.2.args with _ | ⟨x, rest⟩
  · simp
  · cases rest with
    | nil => simp
    | cons y rest' =>
        cases rest' with
        | cons _ _ => simp
        | nil =>
            simp only []
            by_cases hy : (y == sp) = true
            · simp only [hy, if_true, Option.some.injEq]
              intro h; rw [← h]; exact hzr
            · simp only [Bool.not_eq_true] at hy
              simp [hy]

/-- A compiled spanner record holds facts in range. -/
theorem spannerEntry_range {t : Task} {g : Graph} {sp : Name} {x : CSpanner}
    (h : ExampleHeuristics.Spanner.spannerEntry (t.factsWith "usable")
      (t.factsWith "carrying") (ExampleHeuristics.Spanner.atOf (t.factsWith "at") g) sp
      = some x) :
    x.usableFact < t.factNames.size ∧
      (∀ f ∈ x.carryFacts, f < t.factNames.size) ∧
      (∀ y ∈ x.atFacts, y.1 < t.factNames.size) := by
  unfold ExampleHeuristics.Spanner.spannerEntry at h
  rcases hf : (t.factsWith "usable").find? (fun y => y.2.args == [sp]) with _ | y
  · rw [hf] at h; simp at h
  · rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    refine ⟨factsWith_ok y (Array.mem_of_find?_eq_some hf), ?_, ?_⟩
    · exact carryFacts_range t sp
    · exact atOf_range t g sp

/-- And the nut table holds goal facts, which are in range. -/
theorem nutEntry_range {t : Task} (hwf : Task.WF t) (hn : t.numFacts = t.factNames.size)
    (hsize : t.goalAtoms.size ≤ t.goal.size) {at? : Name → Array (Fact × Nat)}
    {x : GroundAtom × Nat} (hx : x ∈ t.goalAtoms.zipIdx) {y : Fact × Nat}
    (h : ExampleHeuristics.Spanner.nutEntry t at? x = some y) :
    y.1 < t.factNames.size := by
  have hlt : x.2 < t.goal.size := by
    obtain ⟨-, h2, -⟩ := Array.mem_zipIdx hx
    omega
  have hmem : t.goal.getD x.2 0 ∈ t.goal := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]
    simpa using Array.getElem_mem hlt
  have hgoal : t.goal.getD x.2 0 < t.factNames.size := by
    rw [← hn]; exact hwf.goal _ hmem
  unfold ExampleHeuristics.Spanner.nutEntry at h
  by_cases hpred : (x.1.pred == "tightened") = true
  · rcases hargs : x.1.args with _ | ⟨n, rest⟩
    · simp only [hpred, hargs] at h; simp at h
    · cases rest with
      | cons _ _ => simp only [hpred, hargs] at h; simp at h
      | nil =>
          simp only [hpred, hargs] at h
          rcases hfind : (at? n).find? (fun z => t.init.test z.1) with _ | z
          · rw [hfind] at h; simp at h
          · rw [hfind] at h
            simp only [Option.map_some, Option.some.injEq] at h
            rw [← h]; exact hgoal
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
    DataMatches t (cfgOf t) (ExampleHeuristics.Spanner.compile t) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · show List.Forall₂ _ _ (((ExampleHeuristics.Spanner.compile t).menAt.map _).toList)
    rw [Array.toList_map]
    refine forall₂_map_right _ ?_
    intro xs hxs
    show List.Forall₂ (PairMatch t) xs.toList ((xs.map _).toList)
    rw [Array.toList_map]
    refine forall₂_map_right _ ?_
    intro y hy
    refine pairMatch_of_range ?_
    have hxs' : xs ∈ (t.objectsOfTypes ["man"]).map
        (ExampleHeuristics.Spanner.atOf (t.factsWith "at")
          (Graph.ofStatic t "link" (t.objectsOfTypes ["location"]))) := by
      simpa [ExampleHeuristics.Spanner.compile] using hxs
    obtain ⟨who, -, hval⟩ := Array.mem_map.mp hxs'
    rw [← hval] at hy
    exact atOf_range t _ who y (by simpa using hy)
  · show List.Forall₂ _ _ (((ExampleHeuristics.Spanner.compile t).nuts.map _).toList)
    rw [Array.toList_map]
    refine forall₂_map_right _ ?_
    intro y hy
    refine pairMatch_of_range ?_
    have hy' : y ∈ (ExampleHeuristics.Spanner.compile t).nuts := by simpa using hy
    obtain ⟨x, hx, hval⟩ := Array.mem_filterMap.mp hy'
    exact nutEntry_range hwf hn hsize hx hval
  · show List.Forall₂ _ _ (((ExampleHeuristics.Spanner.compile t).spanners.map _).toList)
    rw [Array.toList_map]
    refine forall₂_map_right _ ?_
    intro x hx
    have hx' : x ∈ (ExampleHeuristics.Spanner.compile t).spanners := by simpa using hx
    obtain ⟨sp, -, hval⟩ := Array.mem_filterMap.mp hx'
    obtain ⟨hu, hc, ha⟩ := spannerEntry_range hval
    refine ⟨⟨rfl, hu⟩, ?_, ?_⟩
    · show List.Forall₂ (FactMatch t) x.carryFacts.toList ((x.carryFacts.map _).toList)
      rw [Array.toList_map]
      refine forall₂_map_right _ ?_
      intro f hf
      exact ⟨rfl, hc f (by simpa using hf)⟩
    · show List.Forall₂ (PairMatch t) x.atFacts.toList ((x.atFacts.map _).toList)
      rw [Array.toList_map]
      refine forall₂_map_right _ ?_
      intro y hy
      exact pairMatch_of_range (ha y (by simpa using hy))

/-! ### On the task the planner grounds -/

theorem goal_size (d : Domain) (p : Problem) (rel : Bool) :
    (ground d p rel).goalAtoms.size ≤ (ground d p rel).goal.size := by
  show p.goal.toArray.size ≤ (p.goal.toArray.map _).size
  rw [Array.size_map]

/-- **The tables agree on the task the planner searches.** -/
theorem dataMatches_ground (d : Domain) (p : Problem) (rel : Bool)
    (hwf : Task.WF (ground d p rel)) :
    DataMatches (ground d p rel) (cfgOf (ground d p rel))
      (ExampleHeuristics.Spanner.compile (ground d p rel)) :=
  dataMatches _ hwf rfl (goal_size d p rel)


/-! ### The goal atoms the nut table names -/

/-- **Every nut entry names a goal atom of the problem.** -/
theorem goalAtom_mem (d : Domain) (p : Problem) (rel : Bool) :
    ∀ x ∈ (cfgOf (ground d p rel)).nuts, x.1 ∈ p.goal := by
  intro x hx
  have hx' : x ∈ (ExampleHeuristics.Spanner.compile (ground d p rel)).nuts.map
      (fun y => (atomOf (ground d p rel) y.1, y.2)) := hx
  obtain ⟨y, hy, hval⟩ := Array.mem_map.mp hx'
  obtain ⟨z, hz, hzval⟩ := Array.mem_filterMap.mp
    (hy : y ∈ (ExampleHeuristics.Spanner.compile (ground d p rel)).nuts)
  obtain ⟨-, hlt, -⟩ := Array.mem_zipIdx hz
  have hi : z.2 < (ground d p rel).goalAtoms.size := by simpa using hlt
  have hgoal : y.1 = (ground d p rel).goal.getD z.2 0 := by
    unfold ExampleHeuristics.Spanner.nutEntry at hzval
    by_cases hpred : (z.1.pred == "tightened") = true
    · rcases hargs : z.1.args with _ | ⟨n, rest⟩
      · simp only [hpred, hargs] at hzval; simp at hzval
      · cases rest with
        | cons _ _ => simp only [hpred, hargs] at hzval; simp at hzval
        | nil =>
            simp only [hpred, hargs] at hzval
            rcases hf : (ExampleHeuristics.Spanner.atOf
              ((ground d p rel).factsWith "at")
              (Graph.ofStatic (ground d p rel) "link"
                ((ground d p rel).objectsOfTypes ["location"])) n).find?
                (fun w => (ground d p rel).init.test w.1) with _ | w
            · rw [hf] at hzval; simp at hzval
            · rw [hf] at hzval
              simp only [Option.map_some, Option.some.injEq] at hzval
              rw [← hzval]
    · simp only [Bool.not_eq_true] at hpred
      simp only [hpred] at hzval
      simp at hzval
  subst hval
  show atomOf (ground d p rel) y.1 ∈ p.goal
  rw [hgoal]
  exact goalAtom_of_index d p rel hi

/--
**Spanner's improved heuristic is admissible on the task the planner searches**,
with nothing about its tables assumed.

What is left are the obligations about the domain's schemas: that every grounded
operator moves the state in one of the four shapes of `SchemaStep`, and that the
invariant the shapes need holds of `:init` and survives every operator.
-/
theorem improved_admissible_of_shape (d : Domain) (p : Problem) (rel : Bool)
    (Inv : AtomState → Prop)
    (hwf : Task.WF (ground d p rel))
    (hcost : ∀ o ∈ groundedOps d p rel, 0 < o.cost)
    (hnd : (cfgOf (ground d p rel)).nuts.toList.Nodup)
    (hs : (cfgOf (ground d p rel)).spanners.toList.Nodup)
    (hshape : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ → o.applicableA σ →
      SchemaStep (cfgOf (ground d p rel)) σ (o.applyA σ))
    (hsize : 2 * (cfgOf (ground d p rel)).nuts.size
      + (cfgOf (ground d p rel)).dist.bound ≤ deadEnd)
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hpres : ∀ o ∈ groundedOps d p rel, ∀ σ, Inv σ →
      o.applicableA σ → Inv (o.applyA σ)) :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel))
      (ExampleHeuristics.Spanner.improved (ground d p rel)).eval :=
  compiled_admissibleOn d p rel _ Inv (dataMatches_ground d p rel hwf) hwf hcost
    (goalAtom_mem d p rel) hnd hs hshape hsize hinit hpres

end Planner.Lifted.Spanner

/- -------------------------------------------------------------------------- -/
/-
Spanner's invariant, and its preservation.

Nothing stands in two places, a loose nut is not already tightened, and a nut
never moves.  The third is what the walking bound rests on: the value reads each
nut's position out of `:init` once, and that reading stays right only because no
schema touches an `at` of a nut.
-/

namespace Planner.Lifted.Spanner

open Planner Planner.Pddl

/-! ### Atoms of different predicates are different -/

@[simp] theorem atAtom_ne_carrying (x l m s : Name) : atAtom x l ≠ carrying m s := by
  simp [atAtom, carrying]
@[simp] theorem atAtom_ne_usable (x l s : Name) : atAtom x l ≠ usable s := by
  simp [atAtom, usable]
@[simp] theorem atAtom_ne_loose (x l n : Name) : atAtom x l ≠ loose n := by
  simp [atAtom, loose]
@[simp] theorem atAtom_ne_tightened (x l n : Name) : atAtom x l ≠ tightened n := by
  simp [atAtom, tightened]
@[simp] theorem carrying_ne_usable (m s t : Name) : carrying m s ≠ usable t := by
  simp [carrying, usable]
@[simp] theorem carrying_ne_loose (m s n : Name) : carrying m s ≠ loose n := by
  simp [carrying, loose]
@[simp] theorem carrying_ne_tightened (m s n : Name) : carrying m s ≠ tightened n := by
  simp [carrying, tightened]
@[simp] theorem carrying_ne_atAtom (m s x l : Name) : carrying m s ≠ atAtom x l := by
  simp [carrying, atAtom]
@[simp] theorem usable_ne_atAtom (s x l : Name) : usable s ≠ atAtom x l := by
  simp [usable, atAtom]
@[simp] theorem usable_ne_carrying (s m t : Name) : usable s ≠ carrying m t := by
  simp [usable, carrying]
@[simp] theorem usable_ne_loose (s n : Name) : usable s ≠ loose n := by
  simp [usable, loose]
@[simp] theorem usable_ne_tightened (s n : Name) : usable s ≠ tightened n := by
  simp [usable, tightened]
@[simp] theorem loose_ne_tightened (n m : Name) : loose n ≠ tightened m := by
  simp [loose, tightened]
@[simp] theorem tightened_ne_loose (n m : Name) : tightened n ≠ loose m := by
  simp [tightened, loose]
@[simp] theorem tightened_ne_usable (n s : Name) : tightened n ≠ usable s := by
  simp [tightened, usable]
@[simp] theorem loose_ne_atAtom (n x l : Name) : loose n ≠ atAtom x l := by
  simp [loose, atAtom]
@[simp] theorem loose_ne_carrying (n m s : Name) : loose n ≠ carrying m s := by
  simp [loose, carrying]
@[simp] theorem loose_ne_usable (n s : Name) : loose n ≠ usable s := by
  simp [loose, usable]
@[simp] theorem tightened_ne_atAtom (n x l : Name) : tightened n ≠ atAtom x l := by
  simp [tightened, atAtom]
@[simp] theorem tightened_ne_carrying (n m s : Name) : tightened n ≠ carrying m s := by
  simp [tightened, carrying]

@[simp] theorem atAtom_eq (x l x' l' : Name) :
    atAtom x l = atAtom x' l' ↔ x = x' ∧ l = l' := by simp [atAtom]
@[simp] theorem carrying_eq (m s m' s' : Name) :
    carrying m s = carrying m' s' ↔ m = m' ∧ s = s' := by simp [carrying]
@[simp] theorem usable_eq (s s' : Name) : usable s = usable s' ↔ s = s' := by
  simp [usable]
@[simp] theorem loose_eq (n n' : Name) : loose n = loose n' ↔ n = n' := by simp [loose]
@[simp] theorem tightened_eq (n n' : Name) : tightened n = tightened n' ↔ n = n' := by
  simp [tightened]

/-! ### The invariant -/

variable {d : Domain} {p : Problem} {o : AtomOp}

structure Inv (d : Domain) (p : Problem) (σ : AtomState) : Prop where
  /-- Nothing stands in two places. -/
  oneAt : ∀ x l l', σ (atAtom x l) = true → σ (atAtom x l') = true → l = l'
  /-- A loose nut is not already tightened. -/
  looseNotTight : ∀ n, σ (loose n) = true → σ (tightened n) = false
  /-- A carried spanner is not also on the ground. -/
  carryNotAt : ∀ m s l, σ (carrying m s) = true → σ (atAtom s l) = false
  /-- A nut never moves, so `:init` settles where it stands. -/
  nutFixed : ∀ n l, WellTyped d (allObjects d p) "nut" n →
    (σ (atAtom n l) = true ↔ atAtom n l ∈ p.init)

/-! ### It survives every action -/

theorem inv_preserved (hd : SpannerDomain d)
    (hnd : ((allObjects d p).map (·.name)).Nodup)
    (hnm : ∀ ob ∈ allObjects d p, d.isSubtype ob.type "nut" = true →
      d.isSubtype ob.type "man" = false)
    (hns : ∀ ob ∈ allObjects d p, d.isSubtype ob.type "nut" = true →
      d.isSubtype ob.type "spanner" = false)
    (hf : OpFacts d p o) {σ : AtomState} (hinv : Inv d p σ)
    (happ : o.applicableA σ) : Inv d p (o.applyA σ) := by
  have hatDyn : (staticPredicates d).contains (atAtom "" "").pred = false := by
    simpa [atAtom] using at_dynamic hd
  rcases instance_shape hd hf.inst with
    ⟨l1, l2, m, hs, ha⟩ | ⟨l, s, m, hs, ha⟩ | ⟨l, s, m, n0, hs, ha⟩
  · -- walk: only the man's place moves
    obtain ⟨hpre, hlink, hadd, hdel⟩ := walk_atoms hf.inst hs ha
    have hm1 : σ (atAtom m l1) = true := pre_holds hf hpre hatDyn happ
    obtain ⟨a1, a2, a3, ha3, hw1, hw2, hw3⟩ :=
      hf.inst.args_three (show hf.inst.schema.params = [locP "?start", locP "?end", manP] by
        rw [hs]; rfl)
    rw [ha] at ha3
    obtain ⟨rfl, rfl, rfl⟩ : l1 = a1 ∧ l2 = a2 ∧ m = a3 := by simpa using ha3
    have hwm : WellTyped d (allObjects d p) "man" m := hw3
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x lx lx' h1 h2
      by_cases hxm : x = m
      · subst hxm
        have key : ∀ n, o.applyA σ (atAtom x n) = true → n = l2 := by
          intro nn hn
          by_cases hn2 : nn = l2
          · exact hn2
          · exfalso
            by_cases hn1 : nn = l1
            · subst hn1
              rw [falsified_of_lists hf hadd hdel (by simp [hn2]) (by simp) hpre hatDyn σ] at hn
              exact Bool.noConfusion hn
            · rw [frame_of_lists hf hadd hdel (by simp [hn2]) (by simp [hn1]) σ] at hn
              exact hn1 (hinv.oneAt x nn l1 hn hm1)
        rw [key lx h1, key lx' h2]
      · rw [frame_of_lists hf hadd hdel (by simp [hxm]) (by simp [hxm]) σ] at h1 h2
        exact hinv.oneAt x lx lx' h1 h2
    · intro nn h
      rw [frame_of_lists hf hadd hdel (by simp) (by simp) σ] at h ⊢
      exact hinv.looseNotTight nn h
    · intro mm ss ll h
      rw [frame_of_lists hf hadd hdel (by simp) (by simp) σ] at h
      by_cases hsm : ss = m
      · subst hsm
        exfalso
        exact absurd (hinv.carryNotAt mm ss l1 h) (by rw [hm1]; simp)
      · rw [frame_of_lists hf hadd hdel (by simp [hsm]) (by simp [hsm]) σ]
        exact hinv.carryNotAt mm ss ll h
    · intro nn ln hwn
      have hne : nn ≠ m := ne_of_types hnd hnm hwn hwm
      rw [frame_of_lists hf hadd hdel (by simp [hne]) (by simp [hne]) σ]
      exact hinv.nutFixed nn ln hwn
  · -- pickup: the spanner leaves the ground
    obtain ⟨hpreM, hpreS, hadd, hdel⟩ := pickup_atoms hf.inst hs ha
    obtain ⟨a1, a2, a3, ha3, hw1, hw2, hw3⟩ :=
      hf.inst.args_three (show hf.inst.schema.params = [locP "?l", spannerP, manP] by
        rw [hs]; rfl)
    rw [ha] at ha3
    obtain ⟨rfl, rfl, rfl⟩ : l = a1 ∧ s = a2 ∧ m = a3 := by simpa using ha3
    have hws : WellTyped d (allObjects d p) "spanner" s := hw2
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x lx lx' h1 h2
      exact hinv.oneAt x lx lx'
        (falls_of_lists hf hadd (by simp) h1) (falls_of_lists hf hadd (by simp) h2)
    · intro nn h
      rw [frame_of_lists hf hadd hdel (by simp) (by simp) σ] at h ⊢
      exact hinv.looseNotTight nn h
    · intro mm ss ll h
      have hsl : σ (atAtom s l) = true := pre_holds hf hpreS hatDyn happ
      by_cases hss : ss = s
      · subst hss
        rcases hb : o.applyA σ (atAtom ss ll) with _ | _
        · rfl
        · exfalso
          have hbef : σ (atAtom ss ll) = true := falls_of_lists hf hadd (by simp) hb
          have hll : ll = l := hinv.oneAt ss ll l hbef hsl
          subst hll
          rw [falsified_of_lists hf hadd hdel (by simp) (by simp) hpreS hatDyn σ] at hb
          exact Bool.noConfusion hb
      · rw [frame_of_lists hf hadd hdel (by simp) (by simp [hss]) σ]
        refine hinv.carryNotAt mm ss ll ?_
        rw [frame_of_lists hf hadd hdel (by simp [hss]) (by simp) σ] at h
        exact h
    · intro nn ln hwn
      have hne : nn ≠ s := ne_of_types hnd hns hwn hws
      rw [frame_of_lists hf hadd hdel (by simp) (by simp [hne]) σ]
      exact hinv.nutFixed nn ln hwn
  · -- tighten: the nut is done and the spanner is spent
    obtain ⟨hpreM, hpreN, hpreC, hpreU, hpreL, hadd, hdel⟩ := tighten_atoms hf.inst hs ha
    have hlooseDyn : (staticPredicates d).contains (loose "").pred = false := by
      simpa [loose] using loose_dynamic hd
    have hl0 : σ (loose n0) = true := pre_holds hf hpreL hlooseDyn happ
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x lx lx' h1 h2
      rw [frame_of_lists hf hadd hdel (by simp) (by simp) σ] at h1 h2
      exact hinv.oneAt x lx lx' h1 h2
    · intro nn h
      by_cases hnn : nn = n0
      · subst hnn
        rw [falsified_of_lists hf hadd hdel (by simp) (by simp) hpreL hlooseDyn σ] at h
        exact Bool.noConfusion h
      · rw [frame_of_lists hf hadd hdel (by simp) (by simp [hnn]) σ] at h
        rw [frame_of_lists hf hadd hdel (by simp [hnn]) (by simp) σ]
        exact hinv.looseNotTight nn h
    · intro mm ss ll h
      rw [frame_of_lists hf hadd hdel (by simp) (by simp) σ] at h
      rw [frame_of_lists hf hadd hdel (by simp) (by simp) σ]
      exact hinv.carryNotAt mm ss ll h
    · intro nn ln hwn
      rw [frame_of_lists hf hadd hdel (by simp) (by simp) σ]
      exact hinv.nutFixed nn ln hwn

/-! ### `:init` satisfies it, and the planner can check that -/

/-- One pass over `:init` decides the three fields it can decide. -/
def initInvCheck (p : Problem) : Bool :=
  ((initPairs p "at").all fun x =>
    (initPairs p "at").all fun y => !(x.1 == y.1) || (x.2 == y.2)) &&
  ((initOnes p "loose").all fun n => !(p.init.contains (tightened n))) &&
  ((initPairs p "carrying").all fun x =>
    (initPairs p "at").all fun y => !(y.1 == x.2))

theorem initInv_of_check {d : Domain} {p : Problem} (h : initInvCheck p = true) :
    Inv d p (fun a => p.init.toArray.contains a) := by
  simp only [initInvCheck, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x l l' hl hl'
    have m1 : (x, l) ∈ initPairs p "at" := mem_initPairs.mpr (by simpa using hl)
    have m2 : (x, l') ∈ initPairs p "at" := mem_initPairs.mpr (by simpa using hl')
    simpa using h1 (x, l) m1 (x, l') m2
  · intro n hn
    have m1 : n ∈ initOnes p "loose" := mem_initOnes.mpr (by simpa using hn)
    have := h2 n m1
    simp only [Bool.not_eq_true'] at this
    simpa using this
  · intro m s l hc
    have m1 : (m, s) ∈ initPairs p "carrying" := mem_initPairs.mpr (by simpa using hc)
    by_cases hb : p.init.toArray.contains (atAtom s l) = true
    · exfalso
      have m2 : (s, l) ∈ initPairs p "at" := mem_initPairs.mpr (by simpa using hb)
      have := h3 (m, s) m1 (s, l) m2
      simp at this
    · simpa using hb
  · intro n l _
    constructor
    · intro hn; simpa using hn
    · intro hn; simpa using hn


end Planner.Lifted.Spanner

/- -------------------------------------------------------------------------- -/
/-
What the compiled spanner tables hold, read as atoms.

The men's lists hold `at(m, l)` with the node index of `l`, the nut list holds
the `tightened` goals with the place `:init` put each nut, and a spanner record
holds its `usable`, its `carrying` and its `at` atoms.
-/

namespace Planner.Lifted.Spanner

open Planner Planner.Pddl

/-- The graph the heuristic builds. -/
abbrev graphOf (t : Task) : Graph :=
  Graph.ofStatic t "link" (t.objectsOfTypes ["location"])

theorem cfg_dist (t : Task) : (cfgOf t).dist = Distances.of (graphOf t) := rfl

/-- The objects the men's table is indexed by. -/
abbrev men (t : Task) : Array Name := t.objectsOfTypes ["man"]

theorem mem_atOf (t : Task) (who : Name) {y : Fact × Nat}
    (hy : y ∈ ExampleHeuristics.Spanner.atOf (t.factsWith "at") (graphOf t) who) :
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
              rcases hfd : (graphOf t).find? l with _ | i
              · simp
              · simp only [Option.map_some, Option.some.injEq]
                intro h
                refine ⟨l, ?_, ?_⟩
                · rw [← h]
                  show t.factNames.getD z.1 default = atAtom who l
                  rw [hname]
                  unfold atAtom
                  rw [← hpred, show who = x from (by simpa using hx : x = who).symm, ← hargs]
                · rw [← h]; exact hfd
            · simp only [Bool.not_eq_true] at hx
              simp [hx]

theorem mem_atOf_total (t : Task) (who l : Name) {f : Fact} {i : Nat}
    (hf : f < t.factNames.size) (hname : atomOf t f = atAtom who l)
    (hi : (graphOf t).find? l = some i) :
    (f, i) ∈ ExampleHeuristics.Spanner.atOf (t.factsWith "at") (graphOf t) who := by
  refine Array.mem_filterMap.mpr ⟨(f, atAtom who l), mem_factsWith_of_named hf hname rfl, ?_⟩
  simp only [atAtom, hi]
  simp

/-! ### The men's table -/

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

/-- Each entry of the men's table is one man's list. -/
theorem menAt_data (t : Task) {xs : Array (GroundAtom × Nat)}
    (hxs : xs ∈ (cfgOf t).menAt) : ∃ w ∈ men t,
      xs = (ExampleHeuristics.Spanner.atOf (t.factsWith "at") (graphOf t) w).map
        (fun u => (atomOf t u.1, u.2)) := by
  have hxs' : xs ∈ ((ExampleHeuristics.Spanner.compile t).menAt).map
      (fun zs => zs.map fun u => (atomOf t u.1, u.2)) := hxs
  obtain ⟨zs, hzs, hzval⟩ := Array.mem_map.mp hxs'
  have hzs' : zs ∈ (men t).map
      (ExampleHeuristics.Spanner.atOf (t.factsWith "at") (graphOf t)) := hzs
  obtain ⟨w, hw, hwval⟩ := Array.mem_map.mp hzs'
  exact ⟨w, hw, by rw [← hzval, ← hwval]⟩

/-- Every atom in the men's table is an `at` of one of the men. -/
theorem mem_menAt (t : Task) {xs : Array (GroundAtom × Nat)}
    (hxs : xs ∈ (cfgOf t).menAt) {y : GroundAtom × Nat} (hy : y ∈ xs) :
    ∃ w l, y.1 = atAtom w l ∧ (graphOf t).find? l = some y.2 ∧ w ∈ men t := by
  have hxs' : xs ∈ ((ExampleHeuristics.Spanner.compile t).menAt).map
      (fun zs => zs.map fun u => (atomOf t u.1, u.2)) := hxs
  obtain ⟨zs, hzs, hzval⟩ := Array.mem_map.mp hxs'
  have hzs' : zs ∈ (men t).map
      (ExampleHeuristics.Spanner.atOf (t.factsWith "at") (graphOf t)) := hzs
  obtain ⟨w, hw, hwval⟩ := Array.mem_map.mp hzs'
  rw [← hzval] at hy
  obtain ⟨u, hu, huval⟩ := Array.mem_map.mp hy
  rw [← hwval] at hu
  obtain ⟨l, hatom, hidx⟩ := mem_atOf t w hu
  exact ⟨w, l, by rw [← huval]; exact hatom, by rw [← huval]; exact hidx, hw⟩

/-- And the atoms of one man form one entry of it. -/
theorem menAt_mem (t : Task) {w : Name} (hw : w ∈ men t) :
    (ExampleHeuristics.Spanner.atOf (t.factsWith "at") (graphOf t) w).map
      (fun u => (atomOf t u.1, u.2)) ∈ (cfgOf t).menAt := by
  show _ ∈ ((ExampleHeuristics.Spanner.compile t).menAt).map _
  refine Array.mem_map.mpr ⟨_, ?_, rfl⟩
  show _ ∈ (men t).map (ExampleHeuristics.Spanner.atOf (t.factsWith "at") (graphOf t))
  exact Array.mem_map.mpr ⟨w, hw, rfl⟩

/-! ### Where a man stands -/

/-- With one `at` of a man holding, his place is one of the places the value reads. -/
theorem menLoc_mem (t : Task) {σ : AtomState} (hinv : Inv d p σ)
    {w l : Name} {i : Nat} (hw : w ∈ men t) {f : Fact}
    (hf : f < t.factNames.size) (hname : atomOf t f = atAtom w l)
    (hi : (graphOf t).find? l = some i) (hσ : σ (atAtom w l) = true) :
    i ∈ menLocations (cfgOf t) σ := by
  refine Array.mem_filterMap.mpr ⟨_, menAt_mem t hw, ?_⟩
  have hmem : (atAtom w l, i) ∈ (ExampleHeuristics.Spanner.atOf (t.factsWith "at")
      (graphOf t) w).map (fun u => (atomOf t u.1, u.2)) := by
    refine Array.mem_map.mpr ⟨(f, i), mem_atOf_total t w l hf hname hi, ?_⟩
    simp only [Prod.mk.injEq]
    exact ⟨hname, trivial⟩
  rcases hfind : ((ExampleHeuristics.Spanner.atOf (t.factsWith "at") (graphOf t) w).map
      (fun u => (atomOf t u.1, u.2))).find? (fun x => σ x.1) with _ | z
  · exfalso
    rw [Array.find?_eq_none] at hfind
    have := hfind _ hmem
    simp only [Bool.not_eq_true] at this
    rw [hσ] at this
    exact Bool.noConfusion this
  · rw [hfind]
    have hzmem := Array.mem_of_find?_eq_some hfind
    have hzσ : σ z.1 = true := by simpa using Array.find?_some hfind
    obtain ⟨u, hu, huval⟩ := Array.mem_map.mp hzmem
    obtain ⟨l', hatom, hidx⟩ := mem_atOf t w hu
    have hz1 : z.1 = atAtom w l' := by rw [← huval]; exact hatom
    have hz2 : (graphOf t).find? l' = some z.2 := by rw [← huval]; exact hidx
    rw [hz1] at hzσ
    have hll : l' = l := hinv.oneAt w l' l hzσ hσ
    subst hll
    have : z.2 = i := Option.some.inj (hz2.symm.trans hi)
    show some z.2 = some i
    rw [this]

/-! ### The nut table -/

/--
What a nut entry holds: a `tightened` goal, and the node index of the place
`:init` put that nut.  The value reads the place once, and the invariant is what
keeps that reading right.
-/
theorem nuts_data (d : Domain) (p : Problem) (rel : Bool) :
    ∀ y ∈ (cfgOf (ground d p rel)).nuts, ∃ (n l : Name) (i : Nat) (u : Fact × Nat),
      i < (ground d p rel).goalAtoms.size ∧
      (ground d p rel).goalAtoms.getD i default = tightened n ∧
      ExampleHeuristics.Spanner.nutEntry (ground d p rel)
        (ExampleHeuristics.Spanner.atOf ((ground d p rel).factsWith "at")
          (graphOf (ground d p rel))) (tightened n, i) = some u ∧
      y = (atomOf (ground d p rel) u.1, u.2) ∧
      y.1 = tightened n ∧ atAtom n l ∈ p.init ∧
      (graphOf (ground d p rel)).find? l = some y.2 := by
  intro y hy
  have hy' : y ∈ ((ExampleHeuristics.Spanner.compile (ground d p rel)).nuts).map
      (fun u => (atomOf (ground d p rel) u.1, u.2)) := hy
  obtain ⟨u, hu, huval⟩ := Array.mem_map.mp hy'
  obtain ⟨z, hz, hzval⟩ := Array.mem_filterMap.mp
    (hu : u ∈ (ExampleHeuristics.Spanner.compile (ground d p rel)).nuts)
  obtain ⟨-, hlt, hget⟩ := Array.mem_zipIdx hz
  simp only [Nat.zero_add, Nat.sub_zero] at hlt hget
  have hzorig := hzval
  unfold ExampleHeuristics.Spanner.nutEntry at hzval
  by_cases hpred : (z.1.pred == "tightened") = true
  · rcases hargs : z.1.args with _ | ⟨n, rest⟩
    · simp only [hpred, hargs] at hzval; simp at hzval
    · cases rest with
      | cons _ _ => simp only [hpred, hargs] at hzval; simp at hzval
      | nil =>
          simp only [hpred, hargs] at hzval
          rcases hfind : (ExampleHeuristics.Spanner.atOf
              ((ground d p rel).factsWith "at") (graphOf (ground d p rel)) n).find?
              (fun w => (ground d p rel).init.test w.1) with _ | w
          · rw [hfind] at hzval; simp at hzval
          · rw [hfind] at hzval
            simp only [Option.map_some, Option.some.injEq] at hzval
            have hwmem := Array.mem_of_find?_eq_some hfind
            have hwtest : (ground d p rel).init.test w.1 = true := by
              simpa using Array.find?_some hfind
            obtain ⟨l, hatom, hidx⟩ := mem_atOf (ground d p rel) n hwmem
            have hpred0 : z.1.pred = "tightened" := by simpa using hpred
            have hz1 : z.1 = tightened n := by
              unfold tightened; rw [← hpred0, ← hargs]
            refine ⟨n, l, z.2, u, hlt, ?_, ?_, huval.symm, ?_, ?_, ?_⟩
            · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]
              simpa using hget.symm.trans hz1
            · rw [← hz1]
              show ExampleHeuristics.Spanner.nutEntry _ _ (z.1, z.2) = some u
              exact hzorig
            · -- the entry's atom is the goal atom, which is `tightened n`
              have hpred' : z.1.pred = "tightened" := by simpa using hpred
              have hz1 : z.1 = tightened n := by
                unfold tightened; rw [← hpred', ← hargs]
              have hu1 : u.1 = (ground d p rel).goal.getD z.2 0 := by rw [← hzval]
              obtain ⟨hn, -⟩ := goal_name_eq d p rel hlt
              have hn' : atomOf (ground d p rel) ((ground d p rel).goal.getD z.2 0)
                  = (ground d p rel).goalAtoms[z.2]'hlt := hn
              rw [← huval]
              show atomOf (ground d p rel) u.1 = tightened n
              rw [hu1, hn', ← hget, hz1]
            · -- the place is one `:init` names
              have hrange : w.1 < (ground d p rel).factNames.size := by
                have hw2 : w ∈ ExampleHeuristics.Spanner.atOf
                    ((ground d p rel).factsWith "at") (graphOf (ground d p rel)) n := hwmem
                obtain ⟨v, hv, hvval⟩ := Array.mem_filterMap.mp hw2
                have hvr : v.1 < (ground d p rel).factNames.size := factsWith_ok v hv
                revert hvval
                rcases hargs2 : v.2.args with _ | ⟨x2, rest2⟩
                · simp
                · cases rest2 with
                  | nil => simp
                  | cons l2 rest3 =>
                      cases rest3 with
                      | cons _ _ => simp
                      | nil =>
                          simp only []
                          by_cases hx2 : (x2 == n) = true
                          · simp only [hx2, if_true]
                            rcases hfd2 : (graphOf (ground d p rel)).find? l2 with _ | i2
                            · simp
                            · simp only [Option.map_some, Option.some.injEq]
                              intro h; rw [← h]; exact hvr
                          · simp only [Bool.not_eq_true] at hx2
                            simp [hx2]
              have habs := assemble_init (groundedOps d p rel) p.goal.toArray
                p.init.toArray (allObjects d p).toArray d.name
              have hnum := habs.numbered w.1 hrange
              have hmem : atomOf (ground d p rel) w.1 ∈ p.init := by
                have h2 : p.init.toArray.contains
                    (atomOf (ground d p rel) w.1) = true := hnum.trans hwtest
                simpa using h2
              rw [hatom] at hmem
              exact hmem
            · rw [← huval]
              show (graphOf (ground d p rel)).find? l = some u.2
              rw [← hzval]
              exact hidx
  · simp only [Bool.not_eq_true] at hpred
    simp only [hpred] at hzval
    simp at hzval


/-! ### The spanner table -/

/-- What a spanner record holds: its `usable`, its `carrying` and its `at` atoms. -/
theorem spanners_data (t : Task) : ∀ x ∈ (cfgOf t).spanners, ∃ (s : Name) (u : CSpanner),
    s ∈ t.objectsOfTypes ["spanner"] ∧
    ExampleHeuristics.Spanner.spannerEntry (t.factsWith "usable") (t.factsWith "carrying")
      (ExampleHeuristics.Spanner.atOf (t.factsWith "at") (graphOf t)) s = some u ∧
    x = spannerOf t u ∧
    x.usableAtom = usable s ∧
    (∀ y ∈ x.carryAtoms, ∃ m, y = carrying m s) ∧
    (∀ y ∈ x.atAtoms, ∃ l, y.1 = atAtom s l ∧ (graphOf t).find? l = some y.2) := by
  intro x hx
  have hx' : x ∈ ((ExampleHeuristics.Spanner.compile t).spanners).map (spannerOf t) := hx
  obtain ⟨u, hu, huval⟩ := Array.mem_map.mp hx'
  obtain ⟨s, hsmem, hsval⟩ := Array.mem_filterMap.mp
    (hu : u ∈ (ExampleHeuristics.Spanner.compile t).spanners)
  refine ⟨s, u, hsmem, hsval, huval.symm, ?_, ?_, ?_⟩
  · unfold ExampleHeuristics.Spanner.spannerEntry at hsval
    rcases hfd : (t.factsWith "usable").find? (fun w => w.2.args == [s]) with _ | w
    · rw [hfd] at hsval; simp at hsval
    · rw [hfd] at hsval
      simp only [Option.map_some, Option.some.injEq] at hsval
      obtain ⟨hrange, hname, hpred⟩ := mem_factsWith (Array.mem_of_find?_eq_some hfd)
      have hargs : w.2.args = [s] := by simpa using Array.find?_some hfd
      rw [← huval]
      show atomOf t u.usableFact = usable s
      rw [← hsval]
      show t.factNames.getD w.1 default = usable s
      rw [hname]
      unfold usable
      rw [← hpred, ← hargs]
  · intro y hy
    rw [← huval] at hy
    have hy' : y ∈ u.carryFacts.map (atomOf t) := hy
    obtain ⟨g, hg, hgval⟩ := Array.mem_map.mp hy'
    unfold ExampleHeuristics.Spanner.spannerEntry at hsval
    rcases hfd : (t.factsWith "usable").find? (fun w => w.2.args == [s]) with _ | w
    · rw [hfd] at hsval; simp at hsval
    · rw [hfd] at hsval
      simp only [Option.map_some, Option.some.injEq] at hsval
      rw [← hsval] at hg
      obtain ⟨z, hz, hzval⟩ := Array.mem_filterMap.mp hg
      obtain ⟨-, hname, hpred⟩ := mem_factsWith hz
      revert hzval
      rcases hargs : z.2.args with _ | ⟨m, rest⟩
      · simp
      · cases rest with
        | nil => simp
        | cons x2 rest' =>
            cases rest' with
            | cons _ _ => simp
            | nil =>
                simp only []
                by_cases hxs : (x2 == s) = true
                · simp only [hxs, if_true, Option.some.injEq]
                  intro h
                  refine ⟨m, ?_⟩
                  rw [← hgval, ← h]
                  show t.factNames.getD z.1 default = carrying m s
                  rw [hname]
                  unfold carrying
                  rw [← hpred, show s = x2 from (by simpa using hxs : x2 = s).symm, ← hargs]
                · simp only [Bool.not_eq_true] at hxs
                  simp [hxs]
  · intro y hy
    rw [← huval] at hy
    have hy' : y ∈ u.atFacts.map (fun z => (atomOf t z.1, z.2)) := hy
    obtain ⟨z, hz, hzval⟩ := Array.mem_map.mp hy'
    unfold ExampleHeuristics.Spanner.spannerEntry at hsval
    rcases hfd : (t.factsWith "usable").find? (fun w => w.2.args == [s]) with _ | w
    · rw [hfd] at hsval; simp at hsval
    · rw [hfd] at hsval
      simp only [Option.map_some, Option.some.injEq] at hsval
      rw [← hsval] at hz
      obtain ⟨l, hatom, hidx⟩ := mem_atOf t s hz
      exact ⟨l, by rw [← hzval]; exact hatom, by rw [← hzval]; exact hidx⟩


/-! ### Placing an atom into a spanner record -/

/-- The record for a spanner whose `usable` is numbered. -/
theorem spanners_mem (t : Task) {s : Name} (hs : s ∈ t.objectsOfTypes ["spanner"])
    {f : Fact} (hf : f < t.factNames.size) (hname : atomOf t f = usable s) :
    ∃ x ∈ (cfgOf t).spanners, x.usableAtom = usable s ∧
      ∃ u : CSpanner, ExampleHeuristics.Spanner.spannerEntry (t.factsWith "usable")
        (t.factsWith "carrying")
        (ExampleHeuristics.Spanner.atOf (t.factsWith "at") (graphOf t)) s = some u ∧
        x = spannerOf t u := by
  have hmem : (f, usable s) ∈ t.factsWith "usable" := mem_factsWith_of_named hf hname rfl
  rcases hfd : (t.factsWith "usable").find? (fun y => y.2.args == [s]) with _ | w
  · exfalso
    rw [Array.find?_eq_none] at hfd
    have := hfd _ hmem
    simp [usable] at this
  · have hentry : ExampleHeuristics.Spanner.spannerEntry (t.factsWith "usable")
        (t.factsWith "carrying")
        (ExampleHeuristics.Spanner.atOf (t.factsWith "at") (graphOf t)) s
        = some { usableFact := w.1
                 carryFacts := (t.factsWith "carrying").filterMap fun z =>
                   match z.2.args with
                   | [_, x] => if x == s then some z.1 else none
                   | _ => none
                 atFacts := ExampleHeuristics.Spanner.atOf (t.factsWith "at") (graphOf t) s } := by
      unfold ExampleHeuristics.Spanner.spannerEntry
      rw [hfd]
      rfl
    refine ⟨spannerOf t _, ?_, ?_, _, hentry, rfl⟩
    · show _ ∈ ((ExampleHeuristics.Spanner.compile t).spanners).map (spannerOf t)
      refine Array.mem_map.mpr ⟨_, ?_, rfl⟩
      show _ ∈ (t.objectsOfTypes ["spanner"]).filterMap _
      exact Array.mem_filterMap.mpr ⟨s, hs, hentry⟩
    · show atomOf t w.1 = usable s
      have := factsWith_find_args hfd
      show t.factNames.getD w.1 default = usable s
      rw [this]
      rfl

theorem mem_carryAtoms_total (t : Task) {x : SpannerInfo} {s : Name} {u : CSpanner}
    (hx : x = spannerOf t u)
    (hu : ExampleHeuristics.Spanner.spannerEntry (t.factsWith "usable")
      (t.factsWith "carrying")
      (ExampleHeuristics.Spanner.atOf (t.factsWith "at") (graphOf t)) s = some u)
    {m : Name} {f : Fact} (hf : f < t.factNames.size)
    (hname : atomOf t f = carrying m s) : carrying m s ∈ x.carryAtoms := by
  unfold ExampleHeuristics.Spanner.spannerEntry at hu
  rcases hfd : (t.factsWith "usable").find? (fun y => y.2.args == [s]) with _ | w
  · rw [hfd] at hu; simp at hu
  · rw [hfd] at hu
    simp only [Option.map_some, Option.some.injEq] at hu
    rw [hx]
    show carrying m s ∈ u.carryFacts.map (atomOf t)
    refine Array.mem_map.mpr ⟨f, ?_, hname⟩
    rw [← hu]
    refine Array.mem_filterMap.mpr ⟨(f, carrying m s),
      mem_factsWith_of_named hf hname rfl, ?_⟩
    simp [carrying]

theorem mem_spAtAtoms_total (t : Task) {x : SpannerInfo} {s : Name} {u : CSpanner}
    (hx : x = spannerOf t u)
    (hu : ExampleHeuristics.Spanner.spannerEntry (t.factsWith "usable")
      (t.factsWith "carrying")
      (ExampleHeuristics.Spanner.atOf (t.factsWith "at") (graphOf t)) s = some u)
    {l : Name} {f : Fact} {i : Nat} (hf : f < t.factNames.size)
    (hname : atomOf t f = atAtom s l) (hi : (graphOf t).find? l = some i) :
    (atAtom s l, i) ∈ x.atAtoms := by
  unfold ExampleHeuristics.Spanner.spannerEntry at hu
  rcases hfd : (t.factsWith "usable").find? (fun y => y.2.args == [s]) with _ | w
  · rw [hfd] at hu; simp at hu
  · rw [hfd] at hu
    simp only [Option.map_some, Option.some.injEq] at hu
    rw [hx]
    show (atAtom s l, i) ∈ u.atFacts.map (fun z => (atomOf t z.1, z.2))
    refine Array.mem_map.mpr ⟨(f, i), ?_, ?_⟩
    · rw [← hu]; exact mem_atOf_total t s l hf hname hi
    · simp only [Prod.mk.injEq]
      exact ⟨hname, trivial⟩


/-! ### One record per object -/

/-- Two records about the same spanner are the same record. -/
theorem spanner_unique (t : Task) {x x' : SpannerInfo}
    (hx : x ∈ (cfgOf t).spanners) (hx' : x' ∈ (cfgOf t).spanners) {s : Name}
    (hs : x.usableAtom = usable s) (hs' : x'.usableAtom = usable s) : x = x' := by
  obtain ⟨s1, u1, -, he1, hv1, hn1, -, -⟩ := spanners_data t x hx
  obtain ⟨s2, u2, -, he2, hv2, hn2, -, -⟩ := spanners_data t x' hx'
  have h1 : s1 = s := by rw [hn1] at hs; simpa using hs
  have h2 : s2 = s := by rw [hn2] at hs'; simpa using hs'
  subst h1; subst h2
  rw [he1] at he2
  rw [hv1, hv2, Option.some.inj he2]

/-- Two entries about the same nut are the same entry, when the goal has no
repeats.  Without that the value would count one nut twice. -/
theorem nut_unique (d : Domain) (p : Problem) (rel : Bool) (hnd : p.goal.Nodup)
    {y y' : GroundAtom × Nat} (hy : y ∈ (cfgOf (ground d p rel)).nuts)
    (hy' : y' ∈ (cfgOf (ground d p rel)).nuts) {n : Name}
    (hn : y.1 = tightened n) (hn' : y'.1 = tightened n) : y = y' := by
  obtain ⟨n1, -, i, u, hilt, hga, he, hval, hy1, -, -⟩ := nuts_data d p rel y hy
  obtain ⟨n2, -, j, u', hjlt, hgb, he', hval', hy1', -, -⟩ := nuts_data d p rel y' hy'
  have h1 : n1 = n := by rw [hy1] at hn; simpa using hn
  have h2 : n2 = n := by rw [hy1'] at hn'; simpa using hn'
  subst h1; subst h2
  have hgl : (ground d p rel).goalAtoms.toList.Nodup := by
    simpa [taskOf_goalAtoms] using hnd
  have hij : i = j := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hilt] at hga
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hjlt] at hgb
    simp only [Option.getD_some] at hga hgb
    have hkey : (ground d p rel).goalAtoms.toList[i]'(by simpa using hilt)
        = (ground d p rel).goalAtoms.toList[j]'(by simpa using hjlt) := by
      show (ground d p rel).goalAtoms[i] = (ground d p rel).goalAtoms[j]
      rw [hga, hgb]
    exact (List.Nodup.getElem_inj_iff hgl).mp hkey
  subst hij
  rw [he] at he'
  rw [hval, hval', Option.some.inj he']


end Planner.Lifted.Spanner

/- -------------------------------------------------------------------------- -/
/-
Every grounded spanner operator has one of the four shapes.

The walk case is where the one-way map shows up: a spanner still reachable after
a walk was reachable before it, which needs `Distances.Sound.reach` and not the
triangle inequality.
-/

namespace Planner.Lifted.Spanner

open Planner Planner.Pddl

/-! ### What a spanner task must satisfy -/

/-- Every field is decidable on a parsed domain and problem. -/
structure Pinned (d : Domain) (p : Problem) : Prop where
  domain : SpannerDomain d
  /-- The pair passed the planner's own validators.  `namesNodup` below is read
  off it rather than assumed: validation checks the objects for duplicates, the
  constants for duplicates, and rejects an object that shadows a constant. -/
  validated : Validated d p
  locType : ∀ o ∈ allObjects d p, d.isSubtype o.type "location" = true → o.type = "location"
  manType : ∀ o ∈ allObjects d p, d.isSubtype o.type "man" = true → o.type = "man"
  spannerType : ∀ o ∈ allObjects d p,
    d.isSubtype o.type "spanner" = true → o.type = "spanner"
  nutNotMan : ∀ o ∈ allObjects d p,
    d.isSubtype o.type "nut" = true → d.isSubtype o.type "man" = false
  nutNotSpanner : ∀ o ∈ allObjects d p,
    d.isSubtype o.type "nut" = true → d.isSubtype o.type "spanner" = false
  spannerNotMan : ∀ o ∈ allObjects d p,
    d.isSubtype o.type "spanner" = true → d.isSubtype o.type "man" = false
  linkStatic : (staticPredicates d).contains "link" = true
  goalNotLink : ∀ a ∈ p.goal, a.pred ≠ "link"
  goalNodup : p.goal.Nodup
  initCheck : initInvCheck p = true

/-- The object names are distinct — decided by validation, not assumed. -/
theorem Pinned.namesNodup {d : Domain} {p : Problem} (hp : Pinned d p) :
    ((allObjects d p).map (·.name)).Nodup := hp.validated.namesNodup

variable {d : Domain} {p : Problem} {o : AtomOp}

theorem mem_locs (hp : Pinned d p) (rel : Bool) {l : Name}
    (hw : WellTyped d (allObjects d p) "location" l) :
    l ∈ (ground d p rel).objectsOfTypes ["location"] :=
  mem_objsOf_of_wellTyped hp.locType hw

theorem mem_mans (hp : Pinned d p) (rel : Bool) {m : Name}
    (hw : WellTyped d (allObjects d p) "man" m) : m ∈ men (ground d p rel) :=
  mem_objsOf_of_wellTyped hp.manType hw

/-- A spanner is never one of the men. -/
theorem spanner_ne_man (hp : Pinned d p) {s m : Name}
    (hs : WellTyped d (allObjects d p) "spanner" s)
    (hm : WellTyped d (allObjects d p) "man" m) : s ≠ m :=
  ne_of_types hp.namesNodup hp.spannerNotMan hs hm

/-! ### The link the walker used is an edge of the graph -/

theorem link_edge (hp : Pinned d p) (rel : Bool)
    (ho : o ∈ groundedOps d p rel) (hf : OpFacts d p o) {l1 l2 : Name}
    (hlink : link l1 l2 ∈ hf.inst.pre) {i1 i2 : Nat}
    (h1 : (graphOf (ground d p rel)).find? l1 = some i1)
    (h2 : (graphOf (ground d p rel)).find? l2 = some i2) :
    i2 ∈ (graphOf (ground d p rel)).adj.getD i1 #[] := by
  have hmem' : link l1 l2 ∈
      hf.inst.schema.pre.map (instAtom hf.inst.schema.params hf.inst.args) := hlink
  obtain ⟨y, hy, hval⟩ := List.mem_map.mp hmem'
  have hy2 : y.pred = (link l1 l2).pred := by rw [← hval]; rfl
  have hypred : y.pred = "link" := by rw [hy2]; rfl
  have hinit : link l1 l2 ∈ p.init := by
    have := hf.staticHeld y hy (by rw [hypred]; exact hp.linkStatic)
    rw [hval] at this
    simpa using this
  have hnot : link l1 l2 ∉ allAtoms (groundedOps d p rel) p.goal.toArray := by
    intro hc
    exact hp.goalNotLink _ (mem_goal_of_static d p rel hc hp.linkStatic) rfl
  exact Graph.mem_adj_of_static (mem_staticAtoms d p rel hinit hnot) h1 h2

/-! ### Small congruences the cases use -/

theorem carriedP_congr {σ τ : AtomState} {sp : SpannerInfo}
    (hu : τ sp.usableAtom = σ sp.usableAtom)
    (hc : ∀ y ∈ sp.carryAtoms, τ y = σ y) : carriedP τ sp = carriedP σ sp := by
  unfold carriedP
  rw [hu, array_any_congr _ _ _ hc]

/-! ### Where the men are after a walk -/

theorem menLoc_walk (hp : Pinned d p) (rel : Bool) (hf : OpFacts d p o) {l1 l2 m : Name}
    (hadd : hf.inst.add = [atAtom m l2]) (hdel : hf.inst.del = [atAtom m l1])
    (hpre : atAtom m l1 ∈ hf.inst.pre) {σ : AtomState} (hinv : Inv d p σ)
    (hm1 : σ (atAtom m l1) = true) {i2 : Nat}
    (hi2 : (graphOf (ground d p rel)).find? l2 = some i2) :
    ∀ w ∈ menLocations (cfgOf (ground d p rel)) (o.applyA σ),
      w ∈ menLocations (cfgOf (ground d p rel)) σ ∨ w = i2 := by
  have hatDyn : (staticPredicates d).contains (atAtom "" "").pred = false := by
    simpa [atAtom] using at_dynamic hp.domain
  intro w hw
  obtain ⟨xs, hxs, hval⟩ := Array.mem_filterMap.mp hw
  rcases hfind : xs.find? (fun x => (o.applyA σ) x.1) with _ | z
  · rw [hfind] at hval; simp at hval
  · rw [hfind] at hval
    simp only [Option.map_some, Option.some.injEq] at hval
    have hzmem : z ∈ xs := Array.mem_of_find?_eq_some hfind
    have hzτ : (o.applyA σ) z.1 = true := by simpa using Array.find?_some hfind
    obtain ⟨w0, hw0mem, hxseq⟩ := menAt_data (ground d p rel) hxs
    obtain ⟨l, hatom, hidx⟩ : ∃ l, z.1 = atAtom w0 l ∧
        (graphOf (ground d p rel)).find? l = some z.2 := by
      rw [hxseq] at hzmem
      obtain ⟨u, hu, huval⟩ := Array.mem_map.mp hzmem
      obtain ⟨l, ha, hi⟩ := mem_atOf (ground d p rel) w0 hu
      exact ⟨l, by rw [← huval]; exact ha, by rw [← huval]; exact hi⟩
    by_cases hw0 : w0 = m
    · subst hw0
      rw [hatom] at hzτ
      by_cases hl2 : l = l2
      · subst hl2
        rw [hi2] at hidx
        exact Or.inr (by rw [← hval, (Option.some.inj hidx).symm])
      · exfalso
        have hbef : σ (atAtom w0 l) = true := falls_of_lists hf hadd (by simp [hl2]) hzτ
        have hll : l = l1 := hinv.oneAt w0 l l1 hbef hm1
        subst hll
        rw [falsified_of_lists hf hadd hdel (by simp [hl2]) (by simp) hpre hatDyn σ] at hzτ
        exact Bool.noConfusion hzτ
    · refine Or.inl (Array.mem_filterMap.mpr ⟨xs, hxs, ?_⟩)
      have hcong : xs.find? (fun x => (o.applyA σ) x.1) = xs.find? (fun x => σ x.1) := by
        refine array_find?_congr _ _ _ (fun y hy => ?_)
        obtain ⟨l', hatom', -⟩ : ∃ l', y.1 = atAtom w0 l' ∧
            (graphOf (ground d p rel)).find? l' = some y.2 := by
          rw [hxseq] at hy
          obtain ⟨u, hu, huval⟩ := Array.mem_map.mp hy
          obtain ⟨l', ha, hi⟩ := mem_atOf (ground d p rel) w0 hu
          exact ⟨l', by rw [← huval]; exact ha, by rw [← huval]; exact hi⟩
        rw [hatom', frame_of_lists hf hadd hdel (by simp [hw0]) (by simp [hw0]) σ]
      rw [hcong] at hfind
      rw [hfind]
      simpa using hval


/-! ### `walk` -/

set_option maxHeartbeats 4000000 in
theorem walk_step (hp : Pinned d p) (rel : Bool) (ho : o ∈ groundedOps d p rel) (hf : OpFacts d p o)
    (hsound : Distances.Sound (graphOf (ground d p rel))
      (cfgOf (ground d p rel)).dist)
    {l1 l2 m : Name} (hs : hf.inst.schema = walkA) (hargs : hf.inst.args = [l1, l2, m])
    {σ : AtomState} (hinv : Inv d p σ) (happ : o.applicableA σ) :
    SchemaStep (cfgOf (ground d p rel)) σ (o.applyA σ) := by
  have hatDyn : (staticPredicates d).contains (atAtom "" "").pred = false := by
    simpa [atAtom] using at_dynamic hp.domain
  obtain ⟨hpre, hlink, hadd, hdel⟩ := walk_atoms hf.inst hs hargs
  have hm1 : σ (atAtom m l1) = true := pre_holds hf hpre hatDyn happ
  obtain ⟨a1, a2, a3, ha3, hw1, hw2, hw3⟩ :=
    hf.inst.args_three (show hf.inst.schema.params = [locP "?start", locP "?end", manP] by
      rw [hs]; rfl)
  rw [hargs] at ha3
  obtain ⟨rfl, rfl, rfl⟩ : l1 = a1 ∧ l2 = a2 ∧ m = a3 := by simpa using ha3
  have hwl1 : WellTyped d (allObjects d p) "location" l1 := hw1
  have hwl2 : WellTyped d (allObjects d p) "location" l2 := hw2
  have hwm : WellTyped d (allObjects d p) "man" m := hw3
  obtain ⟨i1, hi1⟩ := Option.isSome_iff_exists.mp
    (Graph.find?_isSome (t := ground d p rel) (pred := "link") (mem_locs hp rel hwl1))
  obtain ⟨i2, hi2⟩ := Option.isSome_iff_exists.mp
    (Graph.find?_isSome (t := ground d p rel) (pred := "link") (mem_locs hp rel hwl2))
  have hedge := link_edge hp rel ho hf hlink hi1 hi2
  obtain ⟨fm, hfmlt, hfmname⟩ :=
    numbered_of_op d p rel ho (Or.inl (pre_mem_op hf hpre hatDyn))
  have hi1mem : i1 ∈ menLocations (cfgOf (ground d p rel)) σ :=
    menLoc_mem (ground d p rel) hinv (mem_mans hp rel hwm) hfmlt hfmname hi1 hm1
  have hcases := menLoc_walk hp rel hf hadd hdel hpre hinv hm1 hi2
  -- the pieces of the state the value reads, off the men
  have hframeNut : ∀ y ∈ (cfgOf (ground d p rel)).nuts,
      (o.applyA σ) y.1 = σ y.1 := by
    intro y hy
    obtain ⟨n, -, -, -, -, -, -, -, hy1, -, -⟩ := nuts_data d p rel y hy
    rw [hy1]
    exact frame_of_lists hf hadd hdel (by simp) (by simp) σ
  have hspData : ∀ y ∈ (cfgOf (ground d p rel)).spanners, ∃ s : Name, s ≠ m ∧
      y.usableAtom = usable s ∧ (∀ z ∈ y.carryAtoms, ∃ m', z = carrying m' s) ∧
      (∀ z ∈ y.atAtoms, ∃ l, z.1 = atAtom s l ∧
        (graphOf (ground d p rel)).find? l = some z.2) := by
    intro y hy
    obtain ⟨s, u, hsmem, -, -, hu, hc, ha⟩ := spanners_data (ground d p rel) y hy
    refine ⟨s, spanner_ne_man hp ?_ hwm, hu, hc, ha⟩
    have := objsOf_wellTyped (d := d) (p := p) (rel := rel) (ty := "spanner") hsmem
    exact this
  have hframeSp : ∀ y ∈ (cfgOf (ground d p rel)).spanners,
      carriedP (o.applyA σ) y = carriedP σ y := by
    intro y hy
    obtain ⟨s, hsm, hu, hc, -⟩ := hspData y hy
    refine carriedP_congr ?_ ?_
    · rw [hu]; exact frame_of_lists hf hadd hdel (by simp) (by simp) σ
    · intro z hz
      obtain ⟨m', rfl⟩ := hc z hz
      exact frame_of_lists hf hadd hdel (by simp) (by simp) σ
  refine SchemaStep.walk ⟨hframeNut, hframeSp, ?_, ?_⟩
  · -- a spanner reachable afterwards was reachable before
    intro y hy hahead
    obtain ⟨s, hsm, hu, hc, ha⟩ := hspData y hy
    have hfindEq : y.atAtoms.find? (fun z => (o.applyA σ) z.1)
        = y.atAtoms.find? (fun z => σ z.1) := by
      refine array_find?_congr _ _ _ (fun z hz => ?_)
      obtain ⟨l, hl, -⟩ := ha z hz
      rw [hl]
      exact frame_of_lists hf hadd hdel (by simp [hsm]) (by simp [hsm]) σ
    have hus : (o.applyA σ) y.usableAtom = σ y.usableAtom := by
      rw [hu]; exact frame_of_lists hf hadd hdel (by simp) (by simp) σ
    have hcar : y.carryAtoms.any (o.applyA σ) = y.carryAtoms.any σ := by
      refine array_any_congr _ _ _ (fun z hz => ?_)
      obtain ⟨m', rfl⟩ := hc z hz
      exact frame_of_lists hf hadd hdel (by simp) (by simp) σ
    unfold aheadP at hahead ⊢
    rw [hus, hcar, hfindEq] at hahead
    rcases hfd : y.atAtoms.find? (fun z => σ z.1) with _ | z
    · rw [hfd] at hahead; simp at hahead
    · rw [hfd] at hahead ⊢
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hahead ⊢
      obtain ⟨hleft, hlt⟩ := hahead
      refine ⟨hleft, ?_⟩
      obtain ⟨l, -, hidx⟩ := ha z (Array.mem_of_find?_eq_some hfd)
      have hzlt : z.2 < (graphOf (ground d p rel)).size := Graph.find?_lt hidx
      obtain ⟨u, hu2, hult⟩ := minFrom_lt_bound _ hlt
      rcases hcases u hu2 with hmem | rfl
      · exact Nat.lt_of_le_of_lt
          (minFrom_le_of_mem _ hmem z.2) hult
      · exact Nat.lt_of_le_of_lt (minFrom_le_of_mem _ hi1mem z.2)
          (hsound.reach i1 u z.2 (Graph.find?_lt hi1) hzlt hedge hult)
  · -- one walk is one edge
    intro l w hw
    rcases hcases w hw with hmem | rfl
    · exact ⟨w, hmem, by omega⟩
    · refine ⟨i1, hi1mem, ?_⟩
      by_cases hl : l < (graphOf (ground d p rel)).size
      · exact hsound.step i1 w l (Graph.find?_lt hi1) hl hedge
      · rw [Distances.get_of_col_ge hsound i1 (by omega),
          Distances.get_of_col_ge hsound w (by omega)]
        omega


/-! ### `pickup_spanner` -/

set_option maxHeartbeats 4000000 in
theorem pickup_step (hp : Pinned d p) (rel : Bool) (ho : o ∈ groundedOps d p rel) (hf : OpFacts d p o)
    (hsound : Distances.Sound (graphOf (ground d p rel))
      (cfgOf (ground d p rel)).dist)
    {l s m : Name} (hs : hf.inst.schema = pickupA) (hargs : hf.inst.args = [l, s, m])
    {σ : AtomState} (hinv : Inv d p σ) (happ : o.applicableA σ) :
    SchemaStep (cfgOf (ground d p rel)) σ (o.applyA σ) := by
  have hatDyn : (staticPredicates d).contains (atAtom "" "").pred = false := by
    simpa [atAtom] using at_dynamic hp.domain
  obtain ⟨hpreM, hpreS, hadd, hdel⟩ := pickup_atoms hf.inst hs hargs
  have hml : σ (atAtom m l) = true := pre_holds hf hpreM hatDyn happ
  have hsl : σ (atAtom s l) = true := pre_holds hf hpreS hatDyn happ
  obtain ⟨a1, a2, a3, ha3, hw1, hw2, hw3⟩ :=
    hf.inst.args_three (show hf.inst.schema.params = [locP "?l", spannerP, manP] by
      rw [hs]; rfl)
  rw [hargs] at ha3
  obtain ⟨rfl, rfl, rfl⟩ : l = a1 ∧ s = a2 ∧ m = a3 := by simpa using ha3
  have hwl : WellTyped d (allObjects d p) "location" l := hw1
  have hws : WellTyped d (allObjects d p) "spanner" s := hw2
  have hwm : WellTyped d (allObjects d p) "man" m := hw3
  have hsm : s ≠ m := spanner_ne_man hp hws hwm
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp
    (Graph.find?_isSome (t := ground d p rel) (pred := "link") (mem_locs hp rel hwl))
  -- the men do not move
  have hmenSame : menLocations (cfgOf (ground d p rel)) (o.applyA σ)
      = menLocations (cfgOf (ground d p rel)) σ := by
    unfold menLocations
    apply Array.toList_inj.mp
    rw [Array.toList_filterMap, Array.toList_filterMap]
    refine List.filterMap_congr ?_
    intro xs hxs
    obtain ⟨w, hw, hxseq⟩ := menAt_data (ground d p rel) (by simpa using hxs)
    have hwm2 : w ≠ s :=
      Ne.symm (spanner_ne_man hp hws (objsOf_wellTyped (rel := rel) hw))
    congr 1
    refine array_find?_congr _ _ _ (fun y hy => ?_)
    obtain ⟨l', hl', -⟩ : ∃ l', y.1 = atAtom w l' ∧
        (graphOf (ground d p rel)).find? l' = some y.2 := by
      rw [hxseq] at hy
      obtain ⟨u, hu, huval⟩ := Array.mem_map.mp hy
      obtain ⟨l', ha, hii⟩ := mem_atOf (ground d p rel) w hu
      exact ⟨l', by rw [← huval]; exact ha, by rw [← huval]; exact hii⟩
    rw [hl']
    exact frame_of_lists hf hadd hdel (by simp) (by simp [hwm2]) σ
  have hframeNut : ∀ y ∈ (cfgOf (ground d p rel)).nuts,
      (o.applyA σ) y.1 = σ y.1 := by
    intro y hy
    obtain ⟨n, -, -, -, -, -, -, -, hy1, -, -⟩ := nuts_data d p rel y hy
    rw [hy1]
    exact frame_of_lists hf hadd hdel (by simp) (by simp) σ
  -- no carry atom of this spanner held before
  have hnoCarry : ∀ m' : Name, σ (carrying m' s) = false := by
    intro m'
    rcases hb : σ (carrying m' s) with _ | _
    · rfl
    · exact absurd (hinv.carryNotAt m' s l hb) (by rw [hsl]; simp)
  -- the spanner leaves the ground
  have hatGone : ∀ x : Name, (o.applyA σ) (atAtom s x) = false := by
    intro x
    by_cases hx : x = l
    · rw [hx]
      exact falsified_of_lists hf hadd hdel (by simp) (by simp) hpreS hatDyn σ
    · rcases hb : (o.applyA σ) (atAtom s x) with _ | _
      · rfl
      · exact absurd (hinv.oneAt s x l (falls_of_lists hf hadd (by simp) hb) hsl) hx
  -- records about other spanners do not move
  have hother : ∀ y ∈ (cfgOf (ground d p rel)).spanners, ∀ s' : Name,
      y.usableAtom = usable s' → s' ≠ s →
      ((o.applyA σ) y.usableAtom = σ y.usableAtom ∧
        y.carryAtoms.any (o.applyA σ) = y.carryAtoms.any σ ∧
        y.atAtoms.find? (fun z => (o.applyA σ) z.1) = y.atAtoms.find? (fun z => σ z.1)) := by
    intro y hy s' hu hne
    obtain ⟨s2, u2, -, -, -, hu2, hc2, ha2⟩ := spanners_data (ground d p rel) y hy
    have hs2 : s2 = s' := by rw [hu2] at hu; simpa using hu
    subst hs2
    refine ⟨?_, ?_, ?_⟩
    · rw [hu]; exact frame_of_lists hf hadd hdel (by simp) (by simp) σ
    · refine array_any_congr _ _ _ (fun z hz => ?_)
      obtain ⟨m', rfl⟩ := hc2 z hz
      exact frame_of_lists hf hadd hdel (by simp [hne]) (by simp) σ
    · refine array_find?_congr _ _ _ (fun z hz => ?_)
      obtain ⟨l', hl', -⟩ := ha2 z hz
      rw [hl']
      exact frame_of_lists hf hadd hdel (by simp) (by simp [hne]) σ
  -- if the analysis dropped the add, nothing the value reads moves
  by_cases hcarryAdd : carrying m s ∈ o.add
  swap
  · have hcarFrame : ∀ m' s' : Name,
        (o.applyA σ) (carrying m' s') = σ (carrying m' s') := by
      intro m' s'
      refine applyA_frame σ ?_ ?_
      · intro hc
        have hm2 := hf.subAdd _ hc
        rw [hadd] at hm2
        simp only [List.mem_singleton, carrying_eq] at hm2
        obtain ⟨rfl, rfl⟩ := hm2
        exact hcarryAdd hc
      · intro hc
        have hm2 := hf.subDel _ hc
        rw [hdel] at hm2
        simp at hm2
    have husFrame : ∀ s' : Name, (o.applyA σ) (usable s') = σ (usable s') := by
      intro s'
      exact frame_of_lists hf hadd hdel (by simp) (by simp) σ
    refine SchemaStep.stall ⟨hframeNut, ?_, hmenSame, ?_⟩
    · intro y hy hyt
      obtain ⟨s3, -, -, -, -, hu3, hc3, -⟩ := spanners_data (ground d p rel) y hy
      revert hyt
      simp only [carriedP, hu3, husFrame]
      have : y.carryAtoms.any (o.applyA σ) = y.carryAtoms.any σ := by
        refine array_any_congr _ _ _ (fun z hz => ?_)
        obtain ⟨m', rfl⟩ := hc3 z hz
        exact hcarFrame m' s3
      rw [this]
      exact fun h => h
    · intro y hy hyt
      obtain ⟨s3, -, -, -, -, hu3, hc3, hat3⟩ := spanners_data (ground d p rel) y hy
      by_cases hs3 : s3 = s
      · exfalso
        subst hs3
        revert hyt
        have hnone : y.atAtoms.find? (fun z => (o.applyA σ) z.1) = none := by
          rw [Array.find?_eq_none]
          intro z hz
          obtain ⟨l', hl', -⟩ := hat3 z hz
          rw [hl', hatGone l']
          simp
        simp only [aheadP, hnone]
        simp
      · have hcar : y.carryAtoms.any (o.applyA σ) = y.carryAtoms.any σ := by
          refine array_any_congr _ _ _ (fun z hz => ?_)
          obtain ⟨m', rfl⟩ := hc3 z hz
          exact hcarFrame m' s3
        have hat : y.atAtoms.find? (fun z => (o.applyA σ) z.1)
            = y.atAtoms.find? (fun z => σ z.1) := by
          refine array_find?_congr _ _ _ (fun z hz => ?_)
          obtain ⟨l', hl', -⟩ := hat3 z hz
          rw [hl']
          exact frame_of_lists hf hadd hdel (by simp) (by simp [hs3]) σ
        revert hyt
        simp only [aheadP, hu3, husFrame, hcar, hat, hmenSame]
        exact fun h => h
  have hcarryTrue : (o.applyA σ) (carrying m s) = true := applyA_add σ hcarryAdd
  by_cases hex : ∃ sp ∈ (cfgOf (ground d p rel)).spanners, sp.usableAtom = usable s
  · obtain ⟨sp, hsp, hspu⟩ := hex
    obtain ⟨s2, u2, -, hentry, hxe, hu2, hc2, ha2⟩ :=
      spanners_data (ground d p rel) sp hsp
    have hs2 : s2 = s := by rw [hu2] at hspu; simpa using hspu
    rw [hs2] at hu2 hc2 ha2 hentry
    have hcarryMem : carrying m s ∈ sp.carryAtoms := by
      obtain ⟨fc, hfclt, hfcname⟩ := numbered_of_op d p rel ho (Or.inr (Or.inl hcarryAdd))
      exact mem_carryAtoms_total (ground d p rel) hxe hentry hfclt hfcname
    have hcarryFalse : sp.carryAtoms.any σ = false := by
      rw [← Array.any_toList]
      rcases hb : sp.carryAtoms.toList.any σ with _ | _
      · rfl
      · exfalso
        obtain ⟨z, hz, hzt⟩ := List.any_eq_true.mp hb
        obtain ⟨m', rfl⟩ := hc2 z (by simpa using hz)
        rw [hnoCarry m'] at hzt
        exact Bool.noConfusion hzt
    have hcarryTrue' : sp.carryAtoms.any (o.applyA σ) = true := by
      rw [← Array.any_toList]
      exact List.any_eq_true.mpr ⟨carrying m s, by simpa using hcarryMem, hcarryTrue⟩
    by_cases hus : σ (usable s) = true
    · -- a real pick-up
      obtain ⟨fs, hfslt, hfsname⟩ :=
        numbered_of_op d p rel ho (Or.inl (pre_mem_op hf hpreS hatDyn))
      have hatMem : (atAtom s l, i) ∈ sp.atAtoms :=
        mem_spAtAtoms_total (ground d p rel) hxe hentry hfslt hfsname hi
      obtain ⟨fm, hfmlt, hfmname⟩ :=
        numbered_of_op d p rel ho (Or.inl (pre_mem_op hf hpreM hatDyn))
      have himem : i ∈ menLocations (cfgOf (ground d p rel)) σ :=
        menLoc_mem (ground d p rel) hinv (mem_mans hp rel hwm) hfmlt hfmname hi hml
      have hfindσ : sp.atAtoms.find? (fun z => σ z.1) = some (atAtom s l, i) := by
        rcases hfd : sp.atAtoms.find? (fun z => σ z.1) with _ | z
        · exfalso
          rw [Array.find?_eq_none] at hfd
          have := hfd _ hatMem
          simp only [Bool.not_eq_true] at this
          rw [hsl] at this
          exact Bool.noConfusion this
        · have hzmem := Array.mem_of_find?_eq_some hfd
          have hzσ : σ z.1 = true := by simpa using Array.find?_some hfd
          obtain ⟨l', hl', hidx'⟩ := ha2 z hzmem
          rw [hl'] at hzσ
          have : l' = l := hinv.oneAt s l' l hzσ hsl
          subst this
          rw [hi] at hidx'
          have h2 : z.2 = i := (Option.some.inj hidx').symm
          rw [hfd]
          have : z = (atAtom s l', i) := by
            rcases z with ⟨z1, z2⟩
            simp only [Prod.mk.injEq]
            exact ⟨by simpa using hl', by simpa using h2⟩
          rw [this]
      have hzero : (cfgOf (ground d p rel)).dist.minFrom
          (menLocations (cfgOf (ground d p rel)) σ) i = 0 := by
        have h1 := minFrom_le_of_mem (cfgOf (ground d p rel)).dist himem i
        rw [hsound.self i (Graph.find?_lt hi)] at h1
        omega
      have hbpos : 0 < (cfgOf (ground d p rel)).dist.bound := by
        have hb1 := hsound.boundGe
        have hb2 := Graph.find?_lt hi
        exact Nat.lt_of_le_of_lt (Nat.zero_le i) (Nat.lt_of_lt_of_le hb2 hb1)
      refine SchemaStep.pickup sp ⟨hsp, hframeNut, ?_, ?_, ?_, hmenSame, ?_, ?_, ?_⟩
      · unfold carriedP; rw [hcarryFalse]; simp
      · unfold carriedP
        rw [hcarryTrue', hu2, frame_of_lists hf hadd hdel (by simp) (by simp) σ, hus]
        simp
      · intro y hy hne
        obtain ⟨s3, -, -, -, -, hu3, -, -⟩ := spanners_data (ground d p rel) y hy
        have hne3 : s3 ≠ s := by
          intro hc
          exact hne (spanner_unique (ground d p rel) hy hsp (by rw [hu3, hc]) hu2)
        obtain ⟨h1, h2, -⟩ := hother y hy s3 hu3 hne3
        simp only [carriedP]
        rw [h1, h2]
      · unfold aheadP
        rw [hu2, hus, hcarryFalse, hfindσ]
        simp only [Bool.not_false, Bool.and_true, Bool.true_and, decide_eq_true_eq]
        rw [hzero]
        exact hbpos
      · unfold aheadP
        rw [hcarryTrue']
        simp
      · intro y hy hne
        obtain ⟨s3, -, -, -, -, hu3, -, -⟩ := spanners_data (ground d p rel) y hy
        have hne3 : s3 ≠ s := by
          intro hc
          exact hne (spanner_unique (ground d p rel) hy hsp (by rw [hu3, hc]) hu2)
        obtain ⟨h1, h2, h3⟩ := hother y hy s3 hu3 hne3
        simp only [aheadP]
        rw [hmenSame, h1, h2, h3]
    · -- the spanner is already spent, so nothing the value reads moves
      refine SchemaStep.stall ⟨hframeNut, ?_, hmenSame, ?_⟩ <;>
        · intro y hy hyt
          obtain ⟨s3, -, -, -, -, hu3, -, -⟩ := spanners_data (ground d p rel) y hy
          by_cases hne3 : s3 = s
          · exfalso
            subst hne3
            revert hyt
            simp only [carriedP, aheadP, hu3]
            rw [frame_of_lists hf hadd hdel (by simp) (by simp) σ,
              show σ (usable s3) = false from by simpa using hus]
            simp
          · obtain ⟨h1, h2, h3⟩ := hother y hy s3 hu3 hne3
            revert hyt
            simp only [carriedP, aheadP, h1, h2, h3, hmenSame]
            exact fun h => h
  · -- no record names this spanner
    refine SchemaStep.stall ⟨hframeNut, ?_, hmenSame, ?_⟩ <;>
      · intro y hy hyt
        obtain ⟨s3, -, -, -, -, hu3, -, -⟩ := spanners_data (ground d p rel) y hy
        have hne3 : s3 ≠ s := by
          intro hc
          exact hex ⟨y, hy, by rw [hu3, hc]⟩
        obtain ⟨h1, h2, h3⟩ := hother y hy s3 hu3 hne3
        revert hyt
        simp only [carriedP, aheadP, h1, h2, h3, hmenSame]
        exact fun h => h


/-! ### `tighten_nut` -/

set_option maxHeartbeats 4000000 in
theorem tighten_step (hp : Pinned d p) (rel : Bool) (ho : o ∈ groundedOps d p rel) (hf : OpFacts d p o)
    (hsound : Distances.Sound (graphOf (ground d p rel))
      (cfgOf (ground d p rel)).dist)
    {l s m n0 : Name} (hs : hf.inst.schema = tightenA)
    (hargs : hf.inst.args = [l, s, m, n0])
    {σ : AtomState} (hinv : Inv d p σ) (happ : o.applicableA σ) :
    SchemaStep (cfgOf (ground d p rel)) σ (o.applyA σ) := by
  have hatDyn : (staticPredicates d).contains (atAtom "" "").pred = false := by
    simpa [atAtom] using at_dynamic hp.domain
  have hcarDyn : (staticPredicates d).contains (carrying "" "").pred = false := by
    simpa [carrying] using carrying_dynamic hp.domain
  have husDyn : (staticPredicates d).contains (usable "").pred = false := by
    simpa [usable] using usable_dynamic hp.domain
  have hloDyn : (staticPredicates d).contains (loose "").pred = false := by
    simpa [loose] using loose_dynamic hp.domain
  obtain ⟨hpreM, hpreN, hpreC, hpreU, hpreL, hadd, hdel⟩ := tighten_atoms hf.inst hs hargs
  have hml : σ (atAtom m l) = true := pre_holds hf hpreM hatDyn happ
  have hnl : σ (atAtom n0 l) = true := pre_holds hf hpreN hatDyn happ
  have hcar : σ (carrying m s) = true := pre_holds hf hpreC hcarDyn happ
  have hus : σ (usable s) = true := pre_holds hf hpreU husDyn happ
  have hlo : σ (loose n0) = true := pre_holds hf hpreL hloDyn happ
  obtain ⟨a1, a2, a3, a4, ha4, hw1, hw2, hw3, hw4⟩ :=
    hf.inst.args_four (show hf.inst.schema.params = [locP "?l", spannerP, manP, nutP] by
      rw [hs]; rfl)
  rw [hargs] at ha4
  obtain ⟨rfl, rfl, rfl, rfl⟩ : l = a1 ∧ s = a2 ∧ m = a3 ∧ n0 = a4 := by simpa using ha4
  have hwl : WellTyped d (allObjects d p) "location" l := hw1
  have hwm : WellTyped d (allObjects d p) "man" m := hw3
  have hwn : WellTyped d (allObjects d p) "nut" n0 := hw4
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp
    (Graph.find?_isSome (t := ground d p rel) (pred := "link") (mem_locs hp rel hwl))
  -- the spanner is spent
  have huGone : (o.applyA σ) (usable s) = false :=
    falsified_of_lists hf hadd hdel (by simp) (by simp) hpreU husDyn σ
  have htBefore : σ (tightened n0) = false := hinv.looseNotTight n0 hlo
  -- the men do not move
  have hmenSame : menLocations (cfgOf (ground d p rel)) (o.applyA σ)
      = menLocations (cfgOf (ground d p rel)) σ := by
    unfold menLocations
    apply Array.toList_inj.mp
    rw [Array.toList_filterMap, Array.toList_filterMap]
    refine List.filterMap_congr ?_
    intro xs hxs
    obtain ⟨w, hw, hxseq⟩ := menAt_data (ground d p rel) (by simpa using hxs)
    congr 1
    refine array_find?_congr _ _ _ (fun y hy => ?_)
    obtain ⟨l', hl', -⟩ : ∃ l', y.1 = atAtom w l' ∧
        (graphOf (ground d p rel)).find? l' = some y.2 := by
      rw [hxseq] at hy
      obtain ⟨u, hu, huval⟩ := Array.mem_map.mp hy
      obtain ⟨l', ha, hii⟩ := mem_atOf (ground d p rel) w hu
      exact ⟨l', by rw [← huval]; exact ha, by rw [← huval]; exact hii⟩
    rw [hl']
    exact frame_of_lists hf hadd hdel (by simp) (by simp) σ
  -- the record for the spanner it spent
  obtain ⟨fu, hfult, hfuname⟩ :=
    numbered_of_op d p rel ho (Or.inl (pre_mem_op hf hpreU husDyn))
  obtain ⟨sp, hsp, hspu, u2, hentry, hxe⟩ :=
    spanners_mem (ground d p rel)
      (mem_objsOf_of_wellTyped (rel := rel) hp.spannerType hw2) hfult hfuname
  obtain ⟨fc, hfclt, hfcname⟩ :=
    numbered_of_op d p rel ho (Or.inl (pre_mem_op hf hpreC hcarDyn))
  have hcarryMem : carrying m s ∈ sp.carryAtoms :=
    mem_carryAtoms_total (ground d p rel) hxe hentry hfclt hfcname
  have hcarryAny : sp.carryAtoms.any σ = true := by
    rw [← Array.any_toList]
    exact List.any_eq_true.mpr ⟨carrying m s, by simpa using hcarryMem, hcar⟩
  have hcarrySame : sp.carryAtoms.any (o.applyA σ) = sp.carryAtoms.any σ := by
    obtain ⟨s3, -, -, -, -, -, hc2, -⟩ := spanners_data (ground d p rel) sp hsp
    refine array_any_congr _ _ _ (fun z hz => ?_)
    obtain ⟨m', rfl⟩ := hc2 z hz
    exact frame_of_lists hf hadd hdel (by simp) (by simp) σ
  -- other records do not move
  have hother : ∀ y ∈ (cfgOf (ground d p rel)).spanners, y ≠ sp →
      ((o.applyA σ) y.usableAtom = σ y.usableAtom ∧
        y.carryAtoms.any (o.applyA σ) = y.carryAtoms.any σ ∧
        y.atAtoms.find? (fun z => (o.applyA σ) z.1) = y.atAtoms.find? (fun z => σ z.1)) := by
    intro y hy hne
    obtain ⟨s3, -, -, -, -, hu3, hc3, ha3⟩ := spanners_data (ground d p rel) y hy
    have hne3 : s3 ≠ s := by
      intro hc
      exact hne (spanner_unique (ground d p rel) hy hsp (by rw [hu3, hc]) hspu)
    refine ⟨?_, ?_, ?_⟩
    · rw [hu3]; exact frame_of_lists hf hadd hdel (by simp) (by simp [hne3]) σ
    · refine array_any_congr _ _ _ (fun z hz => ?_)
      obtain ⟨m', rfl⟩ := hc3 z hz
      exact frame_of_lists hf hadd hdel (by simp) (by simp) σ
    · refine array_find?_congr _ _ _ (fun z hz => ?_)
      obtain ⟨l', hl', -⟩ := ha3 z hz
      rw [hl']
      exact frame_of_lists hf hadd hdel (by simp) (by simp) σ
  -- if the analysis dropped the add, nothing the value reads moves
  by_cases htAdd : tightened n0 ∈ o.add
  swap
  · have hnutAll : ∀ y ∈ (cfgOf (ground d p rel)).nuts,
        (o.applyA σ) y.1 = σ y.1 := by
      intro y hy
      obtain ⟨n', -, -, -, -, -, -, -, hy1, -, -⟩ := nuts_data d p rel y hy
      rw [hy1]
      refine applyA_frame σ ?_ ?_
      · intro hc
        have hm2 := hf.subAdd _ hc
        rw [hadd] at hm2
        simp only [List.mem_singleton, tightened_eq] at hm2
        subst hm2
        exact htAdd hc
      · intro hc
        have hm2 := hf.subDel _ hc
        rw [hdel] at hm2
        simp at hm2
    refine SchemaStep.stall ⟨hnutAll, ?_, hmenSame, ?_⟩ <;>
      · intro y hy hyt
        by_cases hyy : y = sp
        · exfalso
          subst hyy
          revert hyt
          simp only [carriedP, aheadP, hspu, huGone]
          simp
        · obtain ⟨h1, h2, h3⟩ := hother y hy hyy
          revert hyt
          simp only [carriedP, aheadP, h1, h2, h3, hmenSame]
          exact fun h => h
  have htTrue : (o.applyA σ) (tightened n0) = true := applyA_add σ htAdd
  by_cases hex : ∃ x ∈ (cfgOf (ground d p rel)).nuts, x.1 = tightened n0
  · obtain ⟨x, hx, hx1⟩ := hex
    have hnutOther : ∀ y ∈ (cfgOf (ground d p rel)).nuts, y ≠ x →
        (o.applyA σ) y.1 = σ y.1 := by
      intro y hy hne
      obtain ⟨n', -, -, -, -, -, -, -, hy1, -, -⟩ := nuts_data d p rel y hy
      have hnn : n' ≠ n0 := by
        intro hc
        exact hne (nut_unique d p rel hp.goalNodup hy hx (by rw [hy1, hc]) hx1)
      rw [hy1]
      exact frame_of_lists hf hadd hdel (by simp [hnn]) (by simp [hnn]) σ
    -- the man stands on the nut he tightens
    have hzero : (cfgOf (ground d p rel)).dist.minFrom
        (menLocations (cfgOf (ground d p rel)) σ) x.2 = 0 := by
      obtain ⟨n', l', -, -, -, -, -, -, hy1, hinit', hidx'⟩ := nuts_data d p rel x hx
      have hnn : n' = n0 := by rw [hy1] at hx1; simpa using hx1
      subst hnn
      have hσl' : σ (atAtom n' l') = true := (hinv.nutFixed n' l' hwn).mpr hinit'
      have hll : l' = l := hinv.oneAt n' l' l hσl' hnl
      subst hll
      rw [hi] at hidx'
      have hx2 : x.2 = i := (Option.some.inj hidx').symm
      obtain ⟨fm, hfmlt, hfmname⟩ :=
        numbered_of_op d p rel ho (Or.inl (pre_mem_op hf hpreM hatDyn))
      have himem : i ∈ menLocations (cfgOf (ground d p rel)) σ :=
        menLoc_mem (ground d p rel) hinv (mem_mans hp rel hwm) hfmlt hfmname hi hml
      rw [hx2]
      have h1 := minFrom_le_of_mem (cfgOf (ground d p rel)).dist himem i
      rw [hsound.self i (Graph.find?_lt hi)] at h1
      omega
    refine SchemaStep.tighten x sp ⟨hx, ?_, ?_, hnutOther, hsp, ?_, ?_, ?_, hmenSame,
      ?_, ?_⟩
    · rw [hx1]; exact htBefore
    · rw [hx1]; exact htTrue
    · unfold carriedP; rw [hspu, hus, hcarryAny]; simp
    · unfold carriedP; rw [hspu, huGone]; simp
    · intro y hy hne
      obtain ⟨h1, h2, -⟩ := hother y hy hne
      simp only [carriedP]
      rw [h1, h2]
    · intro y hy
      by_cases hyy : y = sp
      · subst hyy
        simp only [aheadP]
        rw [hmenSame, hspu, huGone, hcarrySame, hcarryAny, hus]
        simp
      · obtain ⟨h1, h2, h3⟩ := hother y hy hyy
        simp only [aheadP, h1, h2, h3, hmenSame]
    · intro y hy
      by_cases hyx : y = x
      · subst hyx
        exact Or.inl hzero
      · refine Or.inr ?_
        have hymem : y ∈ (cfgOf (ground d p rel)).nuts :=
          (Array.mem_filter.mp hy).1
        have hyσ : σ y.1 = false := by
          have := (Array.mem_filter.mp hy).2
          simpa using this
        refine Array.mem_filter.mpr ⟨hymem, ?_⟩
        rw [hnutOther y hymem hyx, hyσ]
        simp
  · -- the nut has no goal, so nothing the value reads moves
    have hnutSame : ∀ y ∈ (cfgOf (ground d p rel)).nuts, (o.applyA σ) y.1 = σ y.1 := by
      intro y hy
      obtain ⟨n', -, -, -, -, -, -, -, hy1, -, -⟩ := nuts_data d p rel y hy
      have hnn : n' ≠ n0 := by
        intro hc
        exact hex ⟨y, hy, by rw [hy1, hc]⟩
      rw [hy1]
      exact frame_of_lists hf hadd hdel (by simp [hnn]) (by simp [hnn]) σ
    refine SchemaStep.stall ⟨hnutSame, ?_, hmenSame, ?_⟩ <;>
      · intro y hy hyt
        by_cases hyy : y = sp
        · exfalso
          subst hyy
          revert hyt
          simp only [carriedP, aheadP, hspu, huGone]
          simp
        · obtain ⟨h1, h2, h3⟩ := hother y hy hyy
          revert hyt
          simp only [carriedP, aheadP, h1, h2, h3, hmenSame]
          exact fun h => h


/-! ### Assembling the shape -/

/-- Every operator costs something. -/
theorem cost_pos (hp : Pinned d p) (rel : Bool) :
    ∀ o ∈ groundedOps d p rel, 0 < o.cost := by
  intro o ho
  obtain ⟨hf⟩ := opFacts_ground d p rel ho
  rw [hf.cost]
  show 0 < hf.inst.schema.cost
  rcases instance_shape hp.domain hf.inst with ⟨-, -, -, hs, -⟩ | ⟨-, -, -, hs, -⟩ |
    ⟨-, -, -, -, hs, -⟩ <;> rw [hs] <;> decide

/--
**Every operator the grounder builds is one of the four shapes**, on the task it
builds without relevance pruning.
-/
theorem schemaStep_of_ops (hp : Pinned d p) (rel : Bool)
    (hsound : Distances.Sound (graphOf (ground d p rel))
      (cfgOf (ground d p rel)).dist) :
    ∀ o ∈ groundedOps d p rel, ∀ σ, Inv d p σ → o.applicableA σ →
      SchemaStep (cfgOf (ground d p rel)) σ (o.applyA σ) := by
  intro o ho σ hinv happ
  obtain ⟨hf⟩ := opFacts_ground d p rel ho
  rcases instance_shape hp.domain hf.inst with
    ⟨l1, l2, m, hs, ha⟩ | ⟨l, s, m, hs, ha⟩ | ⟨l, s, m, n0, hs, ha⟩
  · exact walk_step hp rel ho hf hsound hs ha hinv happ
  · exact pickup_step hp rel ho hf hsound hs ha hinv happ
  · exact tighten_step hp rel ho hf hsound hs ha hinv happ

/--
**The nut table has no duplicate entry.**

Each entry stores the fact of the goal atom it came from, and the problem's goal
names each atom once.  `Pinned.goalNodup` is what supplies that.
-/
theorem nuts_nodup (hp : Pinned d p) (rel : Bool) :
    (cfgOf (ground d p rel)).nuts.toList.Nodup := by
  show ((ExampleHeuristics.Spanner.compile (ground d p rel)).nuts.map
    (fun y => (atomOf (ground d p rel) y.1, y.2))).toList.Nodup
  have hnt : (ExampleHeuristics.Spanner.compile (ground d p rel)).nuts
      = ((ground d p rel).goalAtoms.zipIdx).filterMap
        (ExampleHeuristics.Spanner.nutEntry (ground d p rel)
          (ExampleHeuristics.Spanner.atOf ((ground d p rel).factsWith "at")
            (Graph.ofStatic (ground d p rel) "link"
              ((ground d p rel).objectsOfTypes ["location"])))) := rfl
  rw [hnt, Array.map_filterMap]
  refine goalTable_nodup d p rel hp.goalNodup _ (·.1) ?_
  intro x hx b hb
  obtain ⟨hlt, -⟩ := List.mem_zipIdx' hx
  have hi : x.2 < (taskOf d p rel).goalAtoms.size := by simpa using hlt
  obtain ⟨y, hy, hval⟩ := Option.map_eq_some_iff.mp hb
  have hgoal : y.1 = (ground d p rel).goal.getD x.2 0 := by
    unfold ExampleHeuristics.Spanner.nutEntry at hy
    by_cases hpred : (x.1.pred == "tightened") = true
    · rcases hargs : x.1.args with _ | ⟨n, rest⟩
      · simp only [hpred, hargs] at hy; simp at hy
      · cases rest with
        | cons _ _ => simp only [hpred, hargs] at hy; simp at hy
        | nil =>
            simp only [hpred, hargs] at hy
            rcases hf : (ExampleHeuristics.Spanner.atOf
              ((ground d p rel).factsWith "at")
              (Graph.ofStatic (ground d p rel) "link"
                ((ground d p rel).objectsOfTypes ["location"])) n).find?
                (fun w => (ground d p rel).init.test w.1) with _ | w
            · rw [hf] at hy; simp at hy
            · rw [hf] at hy
              simp only [Option.map_some, Option.some.injEq] at hy
              rw [← hy]
    · simp only [Bool.not_eq_true] at hpred
      simp only [hpred] at hy
      simp at hy
  rw [← hval]
  show atomOf (ground d p rel) y.1 = _
  rw [hgoal]
  exact atomOf_goal_getD d p rel hi

/-- A spanner's `usable` entry names the spanner it was built for. -/
theorem entry_names (t : Task) {cf : Array (Fact × GroundAtom)}
    {at? : Name → Array (Fact × Nat)} {sp : Name} {b : SpannerInfo}
    (hb : Option.map (spannerOf t)
      (ExampleHeuristics.Spanner.spannerEntry (t.factsWith "usable") cf at? sp)
        = some b) : b.usableAtom.args = [sp] := by
  obtain ⟨x, hx, hval⟩ := Option.map_eq_some_iff.mp hb
  unfold ExampleHeuristics.Spanner.spannerEntry at hx
  obtain ⟨y, hy, hyval⟩ := Option.map_eq_some_iff.mp hx
  have hmem : y ∈ t.factsWith "usable" := Array.mem_of_find?_eq_some hy
  have hpred : (y.2.args == [sp]) = true := by
    have := Array.find?_eq_some_iff_getElem.mp hy
    exact this.1
  obtain ⟨-, hname, -⟩ := mem_factsWith (f := y.1) (a := y.2) (by simpa using hmem)
  rw [← hval, ← hyval]
  show (atomOf t y.1).args = [sp]
  rw [show atomOf t y.1 = y.2 from hname]
  simpa using hpred

/--
**The spanner table has no duplicate entry.**

Unlike the nut table this one is not built from the goal: it walks the spanner
objects, whose names are distinct.  And an entry names its own spanner, through
the `usable` atom the fact it stores is the number of.
-/
theorem spanners_nodup (hp : Pinned d p) (rel : Bool) :
    (cfgOf (ground d p rel)).spanners.toList.Nodup := by
  show ((ExampleHeuristics.Spanner.compile (ground d p rel)).spanners.map
    (spannerOf (ground d p rel))).toList.Nodup
  have hsp : (ExampleHeuristics.Spanner.compile (ground d p rel)).spanners
      = ((ground d p rel).objectsOfTypes ["spanner"]).filterMap
        (ExampleHeuristics.Spanner.spannerEntry
          ((ground d p rel).factsWith "usable")
          ((ground d p rel).factsWith "carrying")
          (ExampleHeuristics.Spanner.atOf ((ground d p rel).factsWith "at")
            (Graph.ofStatic (ground d p rel) "link"
              ((ground d p rel).objectsOfTypes ["location"])))) := rfl
  rw [hsp, Array.map_filterMap, Array.toList_filterMap]
  refine List.Nodup.filterMap_on (objsOf_nodup hp.namesNodup) ?_
  intro sp hsp1 sp' hsp2 b hb hb'
  have h1 := entry_names (ground d p rel) hb
  have h2 := entry_names (ground d p rel) hb'
  rw [h1] at h2
  simpa using h2

/--
**Spanner's improved heuristic is admissible on the task the grounder builds**,
with nothing about the heuristic assumed.

The dead-end constant is part of the claim: once the spanners a man carries and
those still ahead of him are fewer than the nuts still loose, no transition can
recover, and returning the constant there is what makes the search skip the
doomed subtree.
-/
theorem improved_goalAware (hp : Pinned d p) (rel : Bool) :
    (ground d p rel).GoalAwareOn (Reachable (ground d p rel))
      (ExampleHeuristics.Spanner.improved (ground d p rel)).eval := by
  have hwf := ground_wf d p rel (cost_pos hp rel)
  exact compiled_goalAwareOn d p rel _ (Inv d p)
    (dataMatches_ground d p rel hwf) hwf (cost_pos hp rel) (goalAtom_mem d p rel)
    (initInv_of_check hp.initCheck)
    (fun o ho σ hinv happ => by
      obtain ⟨hf⟩ := opFacts_ground d p rel ho
      exact inv_preserved hp.domain hp.namesNodup hp.nutNotMan hp.nutNotSpanner hf
        hinv happ)

theorem improved_consistent (hp : Pinned d p) (rel : Bool)
    (hsize : 2 * (cfgOf (ground d p rel)).nuts.size
      + (cfgOf (ground d p rel)).dist.bound ≤ deadEnd) :
    (ground d p rel).ConsistentOn (Reachable (ground d p rel))
      (ExampleHeuristics.Spanner.improved (ground d p rel)).eval := by
  have hwf := ground_wf d p rel (cost_pos hp rel)
  exact compiled_consistentOn d p rel _ (Inv d p)
    (dataMatches_ground d p rel hwf) hwf (cost_pos hp rel) (nuts_nodup hp rel)
    (spanners_nodup hp rel)
    (schemaStep_of_ops hp rel (by rw [cfg_dist]; exact Distances.sound_of _)) hsize
    (initInv_of_check hp.initCheck)
    (fun o ho σ hinv happ => by
      obtain ⟨hf⟩ := opFacts_ground d p rel ho
      exact inv_preserved hp.domain hp.namesNodup hp.nutNotMan hp.nutNotSpanner hf
        hinv happ)

theorem improved_admissible (hp : Pinned d p) (rel : Bool)
    (hsize : 2 * (cfgOf (ground d p rel)).nuts.size
      + (cfgOf (ground d p rel)).dist.bound ≤ deadEnd) :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel))
      (ExampleHeuristics.Spanner.improved (ground d p rel)).eval :=
  improved_admissible_of_shape d p rel (Inv d p)
    (ground_wf d p rel (cost_pos hp rel)) (cost_pos hp rel) (nuts_nodup hp rel) (spanners_nodup hp rel)
    (schemaStep_of_ops hp rel (by rw [cfg_dist]; exact Distances.sound_of _)) hsize
    (initInv_of_check hp.initCheck)
    (fun o ho σ hinv happ => by
      obtain ⟨hf⟩ := opFacts_ground d p rel ho
      exact inv_preserved hp.domain hp.namesNodup hp.nutNotMan hp.nutNotSpanner hf
        hinv happ)


end Planner.Lifted.Spanner

/- -------------------------------------------------------------------------- -/
/-
Soundness of the executable certificate for the improved Spanner heuristic.
-/

namespace Planner.Lifted.Spanner

open Planner Planner.Pddl

theorem certificate_sound {d : Domain} {p : Problem} {t : Task}
    (hv : Validated d p)
    (h : ExampleHeuristics.Spanner.Certificate.certified d p t = true) :
    Pinned d p ∧
      2 * (ExampleHeuristics.Spanner.compile t).nuts.size
        + (ExampleHeuristics.Spanner.compile t).dist.bound ≤ deadEnd := by
  simp only [ExampleHeuristics.Spanner.Certificate.certified,
    ExampleHeuristics.Spanner.Certificate.conditions, Certificate.passes,
    List.all_cons, List.all_nil, Bool.and_eq_true] at h
  rcases h with
    ⟨hactions, hloc, hman, hspanner, hnutMan, hnutSpanner,
      hspannerMan, hlink, hgoalLink, hgoalNodup, hinit, hbound⟩
  constructor
  · refine
      { domain := by simpa using hactions
        validated := hv
        locType := Certificate.exactType_sound hloc
        manType := Certificate.exactType_sound hman
        spannerType := Certificate.exactType_sound hspanner
        nutNotMan := Certificate.disjointTypes_sound hnutMan
        nutNotSpanner := Certificate.disjointTypes_sound hnutSpanner
        spannerNotMan := Certificate.disjointTypes_sound hspannerMan
        linkStatic := by simpa using hlink
        goalNotLink := ?_
        goalNodup := of_decide_eq_true hgoalNodup
        initCheck := ?_ }
    · rw [List.all_eq_true] at hgoalLink
      intro a ha
      have hn := hgoalLink a ha
      simpa using hn
    · simpa [ExampleHeuristics.Spanner.Certificate.initInvCheck,
        Certificate.initPairs, Certificate.initOnes, initInvCheck,
        initPairs, initOnes, tightened] using hinit
  · simpa [ExampleHeuristics.Spanner.Certificate.sizeBound] using
      (of_decide_eq_true hbound.1)

theorem improved_goalAware_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool)
    (h : ExampleHeuristics.Spanner.Certificate.certified d p (ground d p rel) = true) :
    (ground d p rel).GoalAwareOn (Reachable (ground d p rel))
      (ExampleHeuristics.Spanner.improved (ground d p rel)).eval :=
  improved_goalAware (certificate_sound hv h).1 rel

theorem improved_consistent_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool)
    (h : ExampleHeuristics.Spanner.Certificate.certified d p (ground d p rel) = true) :
    (ground d p rel).ConsistentOn (Reachable (ground d p rel))
      (ExampleHeuristics.Spanner.improved (ground d p rel)).eval := by
  obtain ⟨hp, hsize⟩ := certificate_sound hv h
  exact improved_consistent hp rel (by simpa [cfgOf] using hsize)

theorem improved_proof_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool) :
    ImprovedProof d p rel
      (ExampleHeuristics.Spanner.Certificate.certified d p (ground d p rel))
      (ExampleHeuristics.Spanner.improved (ground d p rel)) :=
  { goalAware := improved_goalAware_of_certificate hv rel
    consistent := improved_consistent_of_certificate hv rel }

theorem improved_admissible_of_certificate {d : Domain} {p : Problem}
    (hv : Validated d p) (rel : Bool)
    (h : ExampleHeuristics.Spanner.Certificate.certified d p (ground d p rel) = true) :
    (ground d p rel).AdmissibleOn (Reachable (ground d p rel))
      (ExampleHeuristics.Spanner.improved (ground d p rel)).eval := by
  exact (improved_proof_of_certificate hv rel).admissible h

end Planner.Lifted.Spanner
