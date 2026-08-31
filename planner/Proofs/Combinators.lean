/-
The reusable pieces every domain heuristic proof is built from.

Three things recur in all twenty proofs:

  * `consistent_of_ops` turns the global consistency statement into one
    obligation per operator, on well-formed states, with the successor already
    expanded to `op.apply s`;
  * `Op.test_apply_le` says the only way a fact becomes true is by being added,
    which is the whole content of every "this action achieves at most one goal
    atom" argument;
  * `missing` counts unsatisfied goal facts, with the two monotonicity lemmas
    that turn "at most one new" into "drops by at most one".

A `max` of consistent heuristics is consistent, which is how a heuristic built
from several independent lower bounds on the same action family is assembled.
Sums are *not* combined generically: a sum is only admissible when the terms
bound disjoint action families, which is a domain fact, so each domain proves its
own sum bound with `omega` from the per-term facts.
-/
import Proofs.Properties

namespace Planner

/-! ### Per-operator consistency -/

/--
Consistency reduced to one obligation per operator.  Note the hypotheses the
obligation may use: the state is well formed and the operator is applicable, so
its preconditions hold.
-/
theorem Task.consistent_of_ops (t : Task) (h : State → Nat)
    (key : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      h s ≤ op.cost + h (op.apply s)) :
    t.Consistent h := by
  rintro s i s' hs ⟨hlt, happ, rfl⟩
  have hmem : t.ops[i] ∈ t.ops := Array.getElem_mem hlt
  have := key t.ops[i] hmem s hs happ
  simpa [Task.actionCost, Array.getElem?_eq_getElem, hlt] using this

/-- Goal awareness reduced to an obligation on well-formed goal states. -/
theorem Task.goalAware_of (t : Task) (h : State → Nat)
    (key : ∀ s, State.WF t.numFacts s → (∀ f ∈ t.goal, s.test f = true) → h s = 0) :
    t.GoalAware h := by
  intro s hs hgoal
  exact key s hs (Task.isGoal_iff.mp hgoal)

/-- `consistent_of_ops`, relative to an extra invariant the operator may assume. -/
theorem Task.consistentOn_of_ops (t : Task) (Q : State → Prop) (h : State → Nat)
    (key : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → Q s → op.applicable s = true →
      h s ≤ op.cost + h (op.apply s)) :
    t.ConsistentOn Q h := by
  rintro s i s' ⟨hs, hq⟩ ⟨hlt, happ, rfl⟩
  have hmem : t.ops[i] ∈ t.ops := Array.getElem_mem hlt
  have := key t.ops[i] hmem s hs hq happ
  simpa [Task.actionCost, Array.getElem?_eq_getElem, hlt] using this

/-- `goalAware_of`, relative to an extra invariant. -/
theorem Task.goalAwareOn_of (t : Task) (Q : State → Prop) (h : State → Nat)
    (key : ∀ s, State.WF t.numFacts s → Q s → (∀ f ∈ t.goal, s.test f = true) → h s = 0) :
    t.GoalAwareOn Q h := by
  rintro s ⟨hs, hq⟩ hgoal
  exact key s hs hq (Task.isGoal_iff.mp hgoal)

/-! ### What a transition can make true -/

/--
The only facts true after an operator that were not true before are the ones the
operator adds.  Every "this action achieves at most one goal atom" argument is
this lemma plus a look at the operator's add list.
-/
theorem Op.test_apply_le {n : Nat} {op : Op} {s : State} (hop : Op.WF n op)
    (hs : State.WF n s) {f : Fact} (hnew : (op.apply s).test f = true) :
    s.test f = true ∨ op.add.contains f = true := by
  rw [Op.test_apply hop hs] at hnew
  by_cases hA : op.add.contains f
  · exact Or.inr hA
  · by_cases hD : op.del.contains f <;> simp_all

/-- A fact the operator adds holds afterwards. -/
theorem Op.test_apply_add {n : Nat} {op : Op} {s : State} (hop : Op.WF n op)
    (hs : State.WF n s) {f : Fact} (hf : op.add.contains f = true) :
    (op.apply s).test f = true := by
  rw [Op.test_apply hop hs, if_pos hf]

/-- A fact the operator deletes but does not add fails afterwards. -/
theorem Op.test_apply_del {n : Nat} {op : Op} {s : State} (hop : Op.WF n op)
    (hs : State.WF n s) {f : Fact} (hadd : op.add.contains f = false)
    (hdel : op.del.contains f = true) :
    (op.apply s).test f = false := by
  rw [Op.test_apply hop hs, if_neg (by simp only [hadd]; exact Bool.false_ne_true), if_pos hdel]

/-- A fact the operator neither adds nor deletes is unchanged. -/
theorem Op.test_apply_same {n : Nat} {op : Op} {s : State} (hop : Op.WF n op)
    (hs : State.WF n s) {f : Fact} (hadd : op.add.contains f = false)
    (hdel : op.del.contains f = false) :
    (op.apply s).test f = s.test f := by
  rw [Op.test_apply hop hs, if_neg (by simp only [hadd]; exact Bool.false_ne_true),
    if_neg (by simp only [hdel]; exact Bool.false_ne_true)]

/-! ### Counting unsatisfied facts -/

/-- How many facts of `goals` fail to hold in `s`. -/
def missing (goals : List Fact) (s : State) : Nat :=
  goals.countP fun f => !s.test f

@[simp] theorem missing_nil (s : State) : missing [] s = 0 := rfl

theorem missing_eq_zero_iff {goals : List Fact} {s : State} :
    missing goals s = 0 ↔ ∀ f ∈ goals, s.test f = true := by
  simp [missing, List.countP_eq_zero]

theorem missing_eq_zero {goals : List Fact} {s : State}
    (hall : ∀ f ∈ goals, s.test f = true) : missing goals s = 0 :=
  missing_eq_zero_iff.mpr hall

/-- If a transition makes no counted fact newly true, the count cannot fall. -/
theorem missing_mono {goals : List Fact} {s s' : State}
    (hnew : ∀ f ∈ goals, s'.test f = true → s.test f = true) :
    missing goals s ≤ missing goals s' := by
  refine List.countP_mono_left ?_
  intro f hf hfs
  simp only [Bool.not_eq_true'] at hfs ⊢
  by_contra hcon
  simp only [Bool.not_eq_false] at hcon
  rw [hnew f hf hcon] at hfs
  exact absurd hfs (by simp)

/-- If at most the single fact `x` becomes newly true, the count falls by at most one. -/
theorem missing_le_succ {goals : List Fact} (hnd : goals.Nodup) {s s' : State} (x : Fact)
    (hnew : ∀ f ∈ goals, f ≠ x → s'.test f = true → s.test f = true) :
    missing goals s ≤ 1 + missing goals s' := by
  induction goals with
  | nil => simp
  | cons b rest ih =>
      have hnd' : rest.Nodup := hnd.of_cons
      have hb : b ∉ rest := by simpa using hnd.notMem
      by_cases hbx : b = x
      · subst hbx
        have hrest : ∀ f ∈ rest, f ≠ b → s'.test f = true → s.test f = true :=
          fun f hf hfx => hnew f (by simp [hf]) hfx
        have hall : ∀ f ∈ rest, s'.test f = true → s.test f = true := by
          intro f hf hfs
          exact hrest f hf (by rintro rfl; exact hb hf) hfs
        have := missing_mono (goals := rest) hall
        simp only [missing, List.countP_cons] at *
        split <;> split <;> omega
      · have hrest : ∀ f ∈ rest, f ≠ x → s'.test f = true → s.test f = true :=
          fun f hf hfx => hnew f (by simp [hf]) hfx
        have hIH := ih hnd' hrest
        have hbcase : s'.test b = true → s.test b = true := hnew b (by simp) hbx
        simp only [missing, List.countP_cons] at *
        split <;> split <;> simp_all <;> omega

/-! ### Reasoning about the heuristics' loops

The heuristics are written with `for` loops over arrays, for speed and because
they read like the argument they implement.  Those desugar to `forIn`, which two
lemmas make tractable: `Array.forIn_toList` moves to the underlying list, where
induction works, and `forIn_yield_self` says a loop whose body always `continue`s
leaves the accumulator alone.

The second is exactly the shape every one of these loops takes at a goal state:
each skips the goals that already hold, and at a goal state they all do.
-/

theorem forIn_yield_self {α β : Type} (l : List α) (b : β) (f : α → β → Id (ForInStep β))
    (h : ∀ x ∈ l, ∀ c, f x c = ForInStep.yield c) : (forIn l b f : Id β) = b := by
  induction l generalizing b with
  | nil => rfl
  | cons x rest ih =>
      rw [List.forIn_cons, h x (by simp) b]
      simpa using ih b (fun y hy c => h y (by simp [hy]) c)

/--
The same, but only requiring the body to fix the *initial* accumulator.

Loops carrying an early `return` thread an extra marker through the accumulator,
so their body does not preserve an arbitrary value — it rebuilds one with the
marker cleared.  It does fix the value the loop starts from, which is all the
argument needs.
-/
theorem forIn_yield_fixed {α β : Type} (l : List α) (b : β) (f : α → β → Id (ForInStep β))
    (h : ∀ x ∈ l, f x b = ForInStep.yield b) : (forIn l b f : Id β) = b := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
      rw [List.forIn_cons, h x (by simp)]
      simpa using ih (fun y hy => h y (by simp [hy]))

/--
An accumulating loop is a fold.

This is the tool the consistency proofs need.  Goal awareness only had to show the
loops do nothing, but consistency has to say what they compute, and that means
getting at the accumulator as a function of the collection — which is what
`List.foldl` gives and `forIn` does not.
-/
theorem forIn_fold {α β : Type} (l : List α) (b : β) (f : α → β → β) :
    (forIn l b (fun x c => pure (ForInStep.yield (f x c))) : Id β)
      = l.foldl (fun c x => f x c) b := by
  induction l generalizing b with
  | nil => rfl
  | cons x rest ih => simpa using ih (f x b)

/--
The general form: any loop body that always yields is a fold over the function it
yields.  The caller supplies that function and discharges the equation, which is
`split <;> rfl` whenever the body is a chain of `if`s — that is, always, here.
-/
theorem forIn_fold_gen {α β : Type} (l : List α) (b : β) (g : α → β → β)
    (f : α → β → Id (ForInStep β)) (h : ∀ x c, f x c = pure (ForInStep.yield (g x c))) :
    (forIn l b f : Id β) = l.foldl (fun c x => g x c) b := by
  induction l generalizing b with
  | nil => rfl
  | cons x rest ih => rw [List.forIn_cons, h x b]; simpa using ih (g x b)

/-- The same for a loop that skips the elements satisfying `p`, which is the shape
every one of these heuristics uses to skip the goals that already hold. -/
theorem forIn_fold_ite {α β : Type} (l : List α) (b : β) (p : α → Bool) (f : α → β → β) :
    (forIn l b (fun x c => if p x then pure (ForInStep.yield c)
                           else pure (ForInStep.yield (f x c))) : Id β)
      = l.foldl (fun c x => if p x then c else f x c) b := by
  induction l generalizing b with
  | nil => rfl
  | cons x rest ih =>
      by_cases h : p x
      · simpa [h] using ih b
      · simpa [h] using ih (f x b)

/-! ### Dead ends

Four of the strong heuristics report `deadEnd` on states they have shown have no
plan.  Splitting such a heuristic into a decidable dead-end test and a numeric
bound is worth doing once: the test contributes nothing to admissibility, because
a state with no plan has no plan cost to underestimate, and it contributes to
consistency only through being closed under successors, which is usually the
easiest fact about it to prove.
-/

/--
Goal awareness for a heuristic with a dead-end branch.  A goal state is never
dead, and the numeric part vanishes there.
-/
theorem goalAware_deadEnd {t : Task} (dead : State → Bool) (base : State → Nat)
    (hgoalAlive : ∀ s, State.WF t.numFacts s → (∀ f ∈ t.goal, s.test f = true) →
      dead s = false)
    (hbase : ∀ s, State.WF t.numFacts s → (∀ f ∈ t.goal, s.test f = true) → base s = 0) :
    t.GoalAware (fun s => if dead s then deadEnd else base s) := by
  refine t.goalAware_of _ fun s hs hg => ?_
  rw [hgoalAlive s hs hg]
  simpa using hbase s hs hg

/--
Consistency for a heuristic with a dead-end branch, in three obligations.

Being dead must be closed under successors — that is what makes the constant
safe — the numeric part must never exceed `deadEnd`, so that stepping *into* a
dead end cannot make the value jump, and the numeric part must be consistent
along transitions that stay alive.  Nothing is required of transitions leaving a
dead state, which is the point of the split.
-/
theorem consistent_deadEnd {t : Task} (dead : State → Bool) (base : State → Nat)
    (hclosed : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      dead s = true → dead (op.apply s) = true)
    (hbound : ∀ s, base s ≤ deadEnd)
    (halive : ∀ op ∈ t.ops, ∀ s, State.WF t.numFacts s → op.applicable s = true →
      dead s = false → dead (op.apply s) = false →
      base s ≤ op.cost + base (op.apply s)) :
    t.Consistent (fun s => if dead s then deadEnd else base s) := by
  refine t.consistent_of_ops _ fun op hop s hs happ => ?_
  by_cases hd : dead s = true
  · rw [if_pos hd, if_pos (hclosed op hop s hs happ hd)]
    omega
  · simp only [Bool.not_eq_true] at hd
    rw [if_neg (by simp [hd])]
    by_cases hd' : dead (op.apply s) = true
    · rw [if_pos hd']
      have := hbound s
      omega
    · simp only [Bool.not_eq_true] at hd'
      rw [if_neg (by simp [hd'])]
      exact halive op hop s hs happ hd hd'

/-! ### Combining bounds on the same action family -/

theorem goalAware_max {t : Task} {h₁ h₂ : State → Nat}
    (g₁ : t.GoalAware h₁) (g₂ : t.GoalAware h₂) :
    t.GoalAware fun s => max (h₁ s) (h₂ s) := by
  intro s hs hgoal
  simp [g₁ s hs hgoal, g₂ s hs hgoal]

theorem consistent_max {t : Task} {h₁ h₂ : State → Nat}
    (c₁ : t.Consistent h₁) (c₂ : t.Consistent h₂) :
    t.Consistent fun s => max (h₁ s) (h₂ s) := by
  intro s i s' hs hstep
  have b₁ := c₁ s i s' hs hstep
  have b₂ := c₂ s i s' hs hstep
  simp only [Nat.max_le]
  constructor
  · exact Nat.le_trans b₁ (Nat.add_le_add_left (Nat.le_max_left _ _) _)
  · exact Nat.le_trans b₂ (Nat.add_le_add_left (Nat.le_max_right _ _) _)

/-! ### Reading a table through a changed predicate

Every domain reads a position out of a list or an array with `find?`, then has to
show the answer did not move when the state changed away from the entries the
predicate looks at.  The argument is the same list induction in each domain, so
it is proved here once.
-/

theorem find?_congr {α : Type} (l : List α) (P Q : α → Bool)
    (h : ∀ x ∈ l, P x = Q x) : l.find? P = l.find? Q := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.find?_cons, h a (List.mem_cons_self ..),
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem array_find?_congr {α : Type} (xs : Array α) (P Q : α → Bool)
    (h : ∀ x ∈ xs, P x = Q x) : xs.find? P = xs.find? Q := by
  rw [← Array.find?_toList, ← Array.find?_toList]
  exact find?_congr _ _ _ fun y hy => h y (by simpa using hy)

theorem any_congr {α : Type} (l : List α) (P Q : α → Bool)
    (h : ∀ x ∈ l, P x = Q x) : l.any P = l.any Q := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.any_cons, h a (List.mem_cons_self ..),
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem array_any_congr {α : Type} (xs : Array α) (P Q : α → Bool)
    (h : ∀ x ∈ xs, P x = Q x) : xs.any P = xs.any Q := by
  rw [← Array.any_toList, ← Array.any_toList]
  exact any_congr _ _ _ fun y hy => h y (by simpa using hy)

/-! ### Folds that only ever fall

A value built by folding a running bound over a list, where every step can only
lower it, is bounded by where it started, and vanishes when one element of the
list forces zero.
-/

theorem foldl_le_init_of_mono {α : Type} (F : Nat → α → Nat)
    (hmono : ∀ b x, F b x ≤ b) : ∀ (l : List α) (b : Nat), l.foldl F b ≤ b := by
  intro l
  induction l with
  | nil => intro b; exact Nat.le_refl _
  | cons x rest ih => intro b; exact Nat.le_trans (ih _) (hmono b x)

theorem foldl_eq_zero_of_mem {α : Type} (F : Nat → α → Nat)
    (hmono : ∀ b x, F b x ≤ b) {l : List α} {x : α} (hx : x ∈ l)
    (hz : ∀ b, F b x = 0) : ∀ b, l.foldl F b = 0 := by
  induction l with
  | nil => simp at hx
  | cons y rest ih =>
      intro b
      rcases List.mem_cons.mp hx with rfl | hmem
      · rw [List.foldl_cons, hz b]
        exact Nat.le_antisymm (foldl_le_init_of_mono F hmono rest 0) (Nat.zero_le _)
      · rw [List.foldl_cons]
        exact ih hmem _

theorem foldl_min_le_init' {α : Type} (f : α → Nat) :
    ∀ (l : List α) (b : Nat), l.foldl (fun acc y => min acc (f y)) b ≤ b := by
  intro l
  induction l with
  | nil => intro b; exact Nat.le_refl _
  | cons x rest ih => intro b; exact Nat.le_trans (ih _) (Nat.min_le_left _ _)

/-! ### Sums over a filtered list

A counting heuristic sums a per-object term over the objects a filter keeps.
These three lemmas compare two such sums: when the filter and the term agree
everywhere, when they agree away from one object that may move the sum by one,
and when every kept term is zero.
-/

theorem sum_filter_congr {α : Type} (P Q : α → Bool) (f g : α → Nat) :
    ∀ l : List α, (∀ y ∈ l, P y = Q y ∧ f y = g y) →
      ((l.filter P).map f).sum = ((l.filter Q).map g).sum := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons y rest ih =>
      intro h
      obtain ⟨hPQ, hfg⟩ := h y (by simp)
      have hr := ih fun z hz => h z (by simp [hz])
      by_cases hQ : Q y = true
      · rw [List.filter_cons_of_pos (by rw [hPQ]; exact hQ),
          List.filter_cons_of_pos hQ, List.map_cons, List.map_cons,
          List.sum_cons, List.sum_cons, hfg, hr]
      · rw [List.filter_cons_of_neg (by rw [hPQ]; exact hQ),
          List.filter_cons_of_neg hQ]
        exact hr

/-- One element may move the sum by one; the rest must agree. -/
theorem sum_filter_exchange {α : Type} (P Q : α → Bool) (f g : α → Nat) (x : α) :
    ∀ l : List α, l.Nodup →
      (∀ y ∈ l, y ≠ x → P y = Q y ∧ f y = g y) →
      ((if P x = true then f x else 0) ≤ (if Q x = true then g x else 0) + 1) →
      ((l.filter P).map f).sum ≤ ((l.filter Q).map g).sum + 1 := by
  intro l
  induction l with
  | nil => intro _ _ _; simp
  | cons y rest ih =>
      intro hnd h hx
      obtain ⟨hy, hrest⟩ := List.nodup_cons.mp hnd
      by_cases hyx : y = x
      · subst hyx
        have hcongr := sum_filter_congr P Q f g rest
          (fun z hz => h z (by simp [hz]) (fun hc => hy (hc ▸ hz)))
        by_cases hP : P y = true
        · rw [List.filter_cons_of_pos hP, List.map_cons, List.sum_cons]
          rw [if_pos hP] at hx
          by_cases hQ : Q y = true
          · rw [List.filter_cons_of_pos hQ, List.map_cons, List.sum_cons]
            rw [if_pos hQ] at hx
            omega
          · rw [List.filter_cons_of_neg hQ]
            rw [if_neg hQ] at hx
            omega
        · rw [List.filter_cons_of_neg hP]
          by_cases hQ : Q y = true
          · rw [List.filter_cons_of_pos hQ, List.map_cons, List.sum_cons]
            omega
          · rw [List.filter_cons_of_neg hQ]
            omega
      · obtain ⟨hPQ, hfg⟩ := h y (by simp) hyx
        have hih := ih hrest (fun z hz => h z (by simp [hz])) hx
        by_cases hQ : Q y = true
        · rw [List.filter_cons_of_pos (by rw [hPQ]; exact hQ),
            List.filter_cons_of_pos hQ, List.map_cons, List.map_cons,
            List.sum_cons, List.sum_cons, hfg]
          omega
        · rw [List.filter_cons_of_neg (by rw [hPQ]; exact hQ),
            List.filter_cons_of_neg hQ]
          exact hih

/-- The sum vanishes when every term the filter keeps is zero. -/
theorem sum_filter_eq_zero {α : Type} (P : α → Bool) (f : α → Nat) :
    ∀ l : List α, (∀ y ∈ l, P y = true → f y = 0) →
      ((l.filter P).map f).sum = 0 := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons y rest ih =>
      intro h
      have hr := ih fun z hz => h z (by simp [hz])
      by_cases hP : P y = true
      · rw [List.filter_cons_of_pos hP, List.map_cons, List.sum_cons,
          h y (by simp) hP, hr]
      · rw [List.filter_cons_of_neg hP]
        exact hr

/-- One member that satisfies the predicate makes `any` true. -/
theorem array_any_of_mem {α : Type} {xs : Array α} {P : α → Bool} {x : α}
    (hx : x ∈ xs) (h : P x = true) : xs.any P = true := by
  rw [← Array.any_toList]
  exact List.any_eq_true.mpr ⟨x, by simpa using hx, h⟩

/-- A two-element list is its own two entries. -/
theorem list_eq_two {α : Type} [Inhabited α] {l : List α} (h : l.length = 2) :
    l = [l.getD 0 default, l.getD 1 default] := by
  match l, h with
  | [_, _], _ => rfl

/-- `Array.all` read at one member.  The library states it by index. -/
theorem array_all_of_mem {α : Type} {xs : Array α} {P : α → Bool} (h : xs.all P = true)
    {x : α} (hx : x ∈ xs) : P x = true := by
  rw [← Array.all_toList] at h
  exact (List.all_eq_true.mp h) x (by simpa using hx)

end Planner
