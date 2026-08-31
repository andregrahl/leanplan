/-
Some fuel always suffices.

`loop` recurses on a `Nat` fuel, so soundness, optimality and completeness all
carry the side condition that the fuel did not run out.  `astar_mono` already
showed fuel is nothing but a resource bound; what is missing is that a bound
exists.  This file supplies it, by exhibiting a measure the loop strictly
decreases.

The measure is

    μ(s) = (entries on the open list) + Σ_{σ well formed} pot(s.best, σ)

where `pot` is the recorded cost of `σ`, capped at `card + 1`, and `card` is the
number of well-formed states — `Proofs/Finite.lean`.  A state never yet reached
contributes the cap.

Each loop iteration pops exactly one entry, which drops the first summand by one,
and then expands.  Expansion only ever changes the two summands through `record`,
which fires precisely when the new cost undercuts what `best` holds: it pushes at
most one entry and strictly lowers that state's potential, so it cannot raise μ.
Every iteration therefore lowers μ by at least one, and `μ + 1` iterations
suffice.

The cap is what makes the potential finite, and `g_lt_card` is what makes the cap
legitimate: no node ever carries a cost the cap does not exceed.
-/
import Proofs.Search.AStar
import Proofs.Finite

namespace Planner

namespace OpenList

/-! ### Counting what is on the open list

`count` is a field the structure carries, and nothing ties it to the buckets, so
the measure counts the node indices actually stored: a sum over the bucket array
of a sum over each row.  `totalOf` is that sum, written over indices so that the
one-element change a `modify` makes is a single `Finset` split.
-/

private theorem getD_push_lt' {α : Type} [Inhabited α] (a : Array α) (x : α) {j : Nat}
    (h : j < a.size) : (a.push x).getD j default = a.getD j default := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, h, Nat.ne_of_lt h]

private theorem getD_push_eq' {α : Type} [Inhabited α] (a : Array α) (x : α) :
    (a.push x).getD a.size default = x := by
  simp [Array.getD_eq_getD_getElem?]

/-- The sum of `f` over an array's elements, indexed. -/
def totalOf {α : Type} [Inhabited α] (a : Array α) (f : α → Nat) : Nat :=
  ∑ i ∈ Finset.range a.size, f (a.getD i default)

theorem totalOf_push {α : Type} [Inhabited α] (a : Array α) (x : α) (f : α → Nat) :
    totalOf (a.push x) f = totalOf a f + f x := by
  unfold totalOf
  rw [Array.size_push, Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [getD_push_lt' a x (Finset.mem_range.mp hj)]
  · rw [getD_push_eq']

/-- A `modify` changes exactly the one summand it writes. -/
theorem totalOf_modify {α : Type} [Inhabited α] (a : Array α) (i : Nat) (g : α → α)
    (f : α → Nat) (hi : i < a.size) :
    totalOf (a.modify i g) f + f (a.getD i default)
      = totalOf a f + f (g (a.getD i default)) := by
  unfold totalOf
  have hmem : i ∈ Finset.range a.size := Finset.mem_range.mpr hi
  have hsize : (a.modify i g).size = a.size := Array.size_modify ..
  rw [hsize]
  rw [← Finset.add_sum_erase _ (fun j => f (a.getD j default)) hmem,
      ← Finset.add_sum_erase _ (fun j => f ((a.modify i g).getD j default)) hmem]
  have hcong : ∑ j ∈ (Finset.range a.size).erase i, f ((a.modify i g).getD j default)
      = ∑ j ∈ (Finset.range a.size).erase i, f (a.getD j default) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [getD_modify_ne a i j g default (fun hc => (Finset.mem_erase.mp hj).1 hc.symm)]
  rw [hcong, getD_modify_self a i g default hi]
  omega

/-- Padding with a zero-weight element changes nothing. -/
theorem totalOf_widen {α : Type} [Inhabited α] (a : Array α) (i : Nat) (pad : α)
    (f : α → Nat) (hpad : f pad = 0) :
    totalOf (widen a i pad) f = totalOf a f := by
  unfold totalOf widen
  split
  · rfl
  · rename_i h
    simp only [Array.size_append, Array.size_replicate]
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive _ (Nat.zero_le a.size)
          (by omega : a.size ≤ a.size + (i + 1 - a.size))]
    have hlow : ∑ j ∈ Finset.Ico 0 a.size,
        f ((a ++ Array.replicate (i + 1 - a.size) pad).getD j default)
        = ∑ j ∈ Finset.Ico 0 a.size, f (a.getD j default) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j < a.size := (Finset.mem_Ico.mp hj).2
      congr 1
      simp [Array.getD_eq_getD_getElem?, hj', Array.getElem?_append]
    have hhigh : ∑ j ∈ Finset.Ico a.size (a.size + (i + 1 - a.size)),
        f ((a ++ Array.replicate (i + 1 - a.size) pad).getD j default) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hj
      have hval : (a ++ Array.replicate (i + 1 - a.size) pad).getD j default = pad := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simp; omega)]
        simp [Array.getElem_append, Nat.not_lt.mpr hlo]
      rw [hval, hpad]
    rw [hlow, hhigh, Nat.add_zero]

/-- How many entries the open list is really holding. -/
def entries (q : OpenList) : Nat :=
  totalOf q.buckets (fun row => totalOf row Array.size)

private theorem bucketTotal_nil : (fun row : Array (Array Nat) => totalOf row Array.size) #[] = 0 := by
  simp [totalOf]

theorem push_entries (q : OpenList) (e : Entry) : entries (q.push e) = entries q + 1 := by
  have hf : e.f < (widen q.buckets e.f #[]).size := lt_size_widen _ _ _
  have hh : e.h < (widen ((widen q.buckets e.f #[]).getD e.f #[]) e.h #[]).size :=
    lt_size_widen _ _ _
  -- The inner row gains one node index.
  have hrow : ∀ row : Array (Array Nat),
      totalOf ((widen row e.h #[]).modify e.h (·.push e.node)) Array.size
        = totalOf row Array.size + 1 := by
    intro row
    have hh' : e.h < (widen row e.h #[]).size := lt_size_widen _ _ _
    have := totalOf_modify (widen row e.h #[]) e.h (·.push e.node) Array.size hh'
    rw [totalOf_widen row e.h #[] Array.size rfl] at this
    simp only [Array.size_push] at this
    omega
  show totalOf ((widen q.buckets e.f #[]).modify e.f
      (fun row => (widen row e.h #[]).modify e.h (·.push e.node)))
      (fun row => totalOf row Array.size) = entries q + 1
  have hmod := totalOf_modify (widen q.buckets e.f #[]) e.f
    (fun row => (widen row e.h #[]).modify e.h (·.push e.node))
    (fun row => totalOf row Array.size) hf
  simp only [hrow] at hmod
  rw [totalOf_widen q.buckets e.f #[] _ bucketTotal_nil] at hmod
  show _ = entries q + 1
  unfold entries
  omega

/-- Popping removes exactly one entry. -/
theorem pop?_entries {q : OpenList} {e : Entry} {q' : OpenList}
    (h : q.pop? = some (e, q')) : entries q = entries q' + 1 := by
  simp only [pop?] at h
  split at h
  · simp at h
  · rename_i f hfind
    split at h
    · simp at h
    · rename_i hrow hrowfind
      have hstack : (q.buckets.getD f default).getD hrow default ≠ #[] :=
        firstNonEmptyRow_spec _ _ _ hrowfind
      have hfsize : f < q.buckets.size := by
        by_contra hc
        exact hstack (by rw [getD_of_size_le _ _ _ (Nat.not_lt.mp hc)]; rfl)
      have hhsize : hrow < (q.buckets.getD f default).size := by
        by_contra hc
        exact hstack (getD_of_size_le _ _ _ (Nat.not_lt.mp hc))
      split at h
      · simp at h
      · rename_i node hback
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, hq'⟩ := h
        subst hq'
        -- The stack the pop drains has something in it, so it shortens by one.
        have hpos : 0 < ((q.buckets.getD f default).getD hrow default).size := by
          rcases Nat.eq_zero_or_pos ((q.buckets.getD f default).getD hrow default).size with hz | hp
          · exact absurd (Array.size_eq_zero_iff.mp hz) hstack
          · exact hp
        have hrowEq : totalOf ((q.buckets.getD f default).modify hrow (·.pop)) Array.size + 1
            = totalOf (q.buckets.getD f default) Array.size := by
          have := totalOf_modify (q.buckets.getD f default) hrow (·.pop) Array.size hhsize
          simp only [Array.size_pop] at this
          omega
        have hmod := totalOf_modify q.buckets f (fun row => row.modify hrow (·.pop))
          (fun row => totalOf row Array.size) hfsize
        simp only at hmod
        show totalOf q.buckets (fun row => totalOf row Array.size)
          = totalOf (q.buckets.modify f fun row => row.modify hrow (·.pop))
              (fun row => totalOf row Array.size) + 1
        omega

end OpenList

/-! ### The potential of the cheapest-cost map

A state the search has never reached counts for the cap; one it has reached at
cost `g` counts for `g`.  `record` only writes a cost strictly below what is
there, so every write strictly lowers the potential — and `g_lt_card` keeps every
cost written under the cap, which is what makes "strictly lower" a real decrease
rather than a `min` that saturates.
-/

/-- How many well-formed states the task has. -/
noncomputable def stateCard (t : Task) : Nat :=
  Fintype.card {s : State // State.WF t.numFacts s}

/-- What one state contributes: its recorded cost, capped, or the cap if unreached. -/
noncomputable def pot (t : Task) (best : Std.HashMap State Nat)
    (σ : {s : State // State.WF t.numFacts s}) : Nat :=
  match best[σ.val]? with
  | none => stateCard t + 1
  | some g => min g (stateCard t + 1)

/-- The potential of the whole map. -/
noncomputable def Phi (t : Task) (best : Std.HashMap State Nat) : Nat :=
  ∑ σ : {s : State // State.WF t.numFacts s}, pot t best σ

theorem pot_le (t : Task) (best : Std.HashMap State Nat) (σ) :
    pot t best σ ≤ stateCard t + 1 := by
  unfold pot
  split
  · exact Nat.le_refl _
  · exact Nat.min_le_right _ _

/-- The potential starts below the square of the state count and never rises. -/
theorem Phi_le (t : Task) (best : Std.HashMap State Nat) :
    Phi t best ≤ stateCard t * (stateCard t + 1) := by
  unfold Phi
  calc ∑ σ : {s : State // State.WF t.numFacts s}, pot t best σ
      ≤ ∑ _σ : {s : State // State.WF t.numFacts s}, (stateCard t + 1) :=
        Finset.sum_le_sum fun σ _ => pot_le t best σ
    _ = stateCard t * (stateCard t + 1) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        rfl

/-- Recording a strictly better cost for a well-formed state lowers the potential. -/
theorem Phi_insert_lt (t : Task) (best : Std.HashMap State Nat) {σ₀ : State}
    (hwf : State.WF t.numFacts σ₀) {g : Nat} (hg : g ≤ stateCard t)
    (hnew : ∀ g₀, best[σ₀]? = some g₀ → g < g₀) :
    Phi t (best.insert σ₀ g) + 1 ≤ Phi t best := by
  classical
  set x : {s : State // State.WF t.numFacts s} := ⟨σ₀, hwf⟩ with hx
  have hmem : x ∈ (Finset.univ : Finset {s : State // State.WF t.numFacts s}) :=
    Finset.mem_univ x
  have hoff : ∀ σ ∈ (Finset.univ : Finset {s : State // State.WF t.numFacts s}).erase x,
      pot t (best.insert σ₀ g) σ = pot t best σ := by
    intro σ hσ
    have hne : σ.val ≠ σ₀ := by
      intro hc
      exact (Finset.mem_erase.mp hσ).1 (Subtype.ext hc)
    unfold pot
    rw [Std.HashMap.getElem?_insert, if_neg (by simpa using fun hc => hne hc.symm)]
  have hat : pot t (best.insert σ₀ g) x + 1 ≤ pot t best x := by
    have hnewval : pot t (best.insert σ₀ g) x = g := by
      unfold pot
      rw [show (best.insert σ₀ g)[x.val]? = some g by rw [hx]; simp]
      exact Nat.min_eq_left (by omega)
    have hold : g + 1 ≤ pot t best x := by
      unfold pot
      cases hb : best[x.val]? with
      | none => show g + 1 ≤ stateCard t + 1; omega
      | some g₀ =>
          have hlt := hnew g₀ (by rw [← hb, hx])
          show g + 1 ≤ min g₀ (stateCard t + 1)
          omega
    omega
  have e1 : Phi t (best.insert σ₀ g)
      = pot t (best.insert σ₀ g) x + ∑ σ ∈ Finset.univ.erase x, pot t (best.insert σ₀ g) σ := by
    unfold Phi
    exact (Finset.add_sum_erase _ (fun σ => pot t (best.insert σ₀ g) σ) hmem).symm
  have e2 : Phi t best = pot t best x + ∑ σ ∈ Finset.univ.erase x, pot t best σ := by
    unfold Phi
    exact (Finset.add_sum_erase _ (fun σ => pot t best σ) hmem).symm
  have e3 : ∑ σ ∈ Finset.univ.erase x, pot t (best.insert σ₀ g) σ
      = ∑ σ ∈ Finset.univ.erase x, pot t best σ := Finset.sum_congr rfl hoff
  omega

/-! ### The measure the loop decreases -/

/-- Open-list entries plus potential. -/
noncomputable def fuelMeasure (t : Task) (s : Search) : Nat :=
  s.openList.entries + Phi t s.best

theorem record_measure (t : Task) (heur : Heuristic) (id i : Nat) (succ : State) (g : Nat)
    (s : Search) (hwf : State.WF t.numFacts succ) (hg : g ≤ stateCard t)
    (hnew : ∀ g₀, s.best[succ]? = some g₀ → g < g₀) :
    fuelMeasure t (record heur id i succ g s) ≤ fuelMeasure t s := by
  have hphi := Phi_insert_lt t s.best hwf hg hnew
  unfold fuelMeasure
  simp only [record]
  split
  · show s.openList.entries + Phi t (s.best.insert succ g) ≤ s.openList.entries + Phi t s.best
    omega
  · show (s.openList.push _).entries + Phi t (s.best.insert succ g)
      ≤ s.openList.entries + Phi t s.best
    rw [OpenList.push_entries]
    omega

/-! ### Expansion cannot raise the measure -/

theorem expandOne_measure (t : Task) (heur : Heuristic) (id i : Nat) (node : Node)
    (s : Search) (hnode : State.WF t.numFacts node.state) (hg : node.g < stateCard t)
    (hunit : ∀ op ∈ t.ops, op.cost = 1) :
    fuelMeasure t (expandOne t heur id node i s) ≤ fuelMeasure t s := by
  have hcost : (t.ops.getD i default).cost ≤ 1 := by
    by_cases hi : i < t.ops.size
    · rw [OpenList.getD_eq_getElem _ _ _ hi, hunit _ (Array.getElem_mem hi)]
    · rw [OpenList.getD_of_size_le _ _ _ (Nat.not_lt.mp hi)]
      exact Nat.zero_le 1
  have hwfsucc : State.WF t.numFacts ((t.ops.getD i default).apply node.state) :=
    Op.wf_apply _ hnode
  simp only [expandOne]
  split
  · split
    · rename_i previous hprev
      split
      · rename_i hlt
        refine record_measure t heur id i _ _ s hwfsucc (by omega) ?_
        intro g₀ hg₀
        have hp : s.best[(t.ops.getD i default).apply node.state]? = some previous := hprev
        rw [hp] at hg₀
        simp only [Option.some.injEq] at hg₀
        omega
      · exact Nat.le_refl _
    · rename_i hnone
      refine record_measure t heur id i _ _ s hwfsucc (by omega) ?_
      intro g₀ hg₀
      have hp : s.best[(t.ops.getD i default).apply node.state]? = none := hnone
      rw [hp] at hg₀
      simp at hg₀
  · exact Nat.le_refl _

theorem expandFrom_measure (t : Task) (heur : Heuristic) (id : Nat) (node : Node)
    (hnode : State.WF t.numFacts node.state) (hg : node.g < stateCard t)
    (hunit : ∀ op ∈ t.ops, op.cost = 1) :
    ∀ (fuel i : Nat) (s : Search),
      fuelMeasure t (expandFrom t heur id node fuel i s) ≤ fuelMeasure t s := by
  intro fuel
  induction fuel with
  | zero => intro i s; exact Nat.le_refl _
  | succ fuel ih =>
      intro i s
      rw [expandFrom]
      split
      · exact Nat.le_trans (ih (i + 1) _)
          (expandOne_measure t heur id i node s hnode hg hunit)
      · exact Nat.le_refl _

theorem expand_measure (t : Task) (heur : Heuristic) (id : Nat) (node : Node) (s : Search)
    (hnode : State.WF t.numFacts node.state) (hg : node.g < stateCard t)
    (hunit : ∀ op ∈ t.ops, op.cost = 1) :
    fuelMeasure t (expand t heur id node s) ≤ fuelMeasure t s := by
  rw [expand]
  exact expandFrom_measure t heur id node hnode hg hunit t.ops.size 0 _

/-! ### Every iteration lowers the measure

A pop takes one entry off the list, and the expansion that follows cannot put the
measure back.  So the loop runs for at most `fuelMeasure` iterations, and the
three invariants it needs — `NodesOK`, `NoRepeat` and `NodeGBounded` — are all
already proved to survive an expansion.
-/

theorem loop_terminates (t : Task) (heur : Heuristic) (hwf : Task.WF t)
    (hunit : ∀ op ∈ t.ops, op.cost = 1) :
    ∀ (fuel : Nat) (s : Search), NodesOK t s.nodes → NodesOK.NoRepeat s.nodes →
      NodeGBounded s → fuelMeasure t s < fuel →
      (loop t heur fuel s).outcome ≠ Outcome.outOfFuel := by
  have hpos : ∀ op ∈ t.ops, 0 < op.cost := fun op hop => by rw [hunit op hop]; omega
  intro fuel
  induction fuel with
  | zero => intro s _ _ _ hlt; omega
  | succ fuel ih =>
      intro s ok hnr hnb hlt
      rw [loop]
      cases hpop : s.openList.pop? with
      | none => simp
      | some pr =>
          obtain ⟨entry, rest⟩ := pr
          -- One entry leaves the list, so the measure drops by exactly one.
          have hrest : fuelMeasure t { s with openList := rest } + 1 = fuelMeasure t s := by
            have := OpenList.pop?_entries hpop
            show rest.entries + Phi t s.best + 1 = s.openList.entries + Phi t s.best
            omega
          simp only [hpop]
          cases hnode : s.nodes[entry.node]? with
          | none =>
              simp only [hnode]
              exact ih _ ok hnr hnb (by omega)
          | some node =>
              simp only [hnode]
              have hltn : entry.node < s.nodes.size := by
                by_contra hc
                rw [Array.getElem?_eq_none (Nat.not_lt.mp hc)] at hnode
                simp at hnode
              have hget : s.nodes.getD entry.node default = node := by
                rw [Array.getD_eq_getD_getElem?, hnode]
                rfl
              by_cases hstale : s.best.getD node.state node.g < node.g
              · simp only [if_pos hstale]
                exact ih _ ok hnr hnb (by omega)
              · simp only [if_neg hstale]
                by_cases hgoal : t.isGoal node.state = true
                · simp only [if_pos hgoal]
                  simp
                · simp only [if_neg hgoal]
                  have hstwf : State.WF t.numFacts node.state := by
                    rw [← hget]
                    exact NodesOK.states_wf hwf ok _ hltn
                  have hgcard : node.g < stateCard t := by
                    rw [← hget]
                    exact g_lt_card t hwf ok hnr hunit _ hltn
                  refine ih _ ?_ ?_ ?_ ?_
                  · exact expand_nodesOK t heur entry.node _ node ok hltn hget.symm
                  · exact expand_noRepeat t heur entry.node node _ hpos ok hnb hnr hltn hget
                  · exact expand_nodeGBounded t heur entry.node node _ hnb
                  · have := expand_measure t heur entry.node node
                      { s with openList := rest } hstwf hgcard hunit
                    omega

/-! ### A fuel that always suffices -/

/--
**Some fuel always suffices.**  With more than `card · (card + 1) + 1` iterations
available — `card` being the number of well-formed states — the loop cannot run
out of fuel, so `outOfFuel` is never the answer and the three theorems of
`Proofs/Search/AStar.lean` lose their side condition.
-/
theorem astar_terminates (t : Task) (heur : Heuristic) (hwf : Task.WF t)
    (hunit : ∀ op ∈ t.ops, op.cost = 1) (fuel : Nat)
    (hfuel : stateCard t * (stateCard t + 1) + 1 < fuel) :
    (astar t heur fuel).outcome ≠ Outcome.outOfFuel := by
  have ok : NodesOK t #[Node.root t] := by
    refine ⟨by simp, ?_, ?_, ?_⟩
    · simp [Array.getD_eq_getD_getElem?, Node.root]
    · intro j hj hpos; simp at hj; omega
    · intro j hj hpos; simp at hj; omega
  have hnbInit : ∀ (s : Search), s.nodes = #[Node.root t] →
      s.best = (∅ : Std.HashMap State Nat).insert t.init 0 → NodeGBounded s := by
    intro s hn hb j k hk
    rw [hn] at hk
    rcases j with _ | j
    · have hkr : k = Node.root t := by simpa using hk.symm
      subst hkr
      refine ⟨0, ?_, Nat.le_refl _⟩
      rw [hb]
      simp [Node.root]
    · simp at hk
  have hempty : OpenList.empty.entries = 0 := by
    simp [OpenList.entries, OpenList.totalOf, OpenList.empty]
  have hphi : Phi t (((∅ : Std.HashMap State Nat).insert t.init 0)) ≤
      stateCard t * (stateCard t + 1) := Phi_le t _
  rw [astar]
  split
  · refine loop_terminates t heur hwf hunit fuel _ ok (noRepeat_init t)
      (hnbInit _ rfl rfl) ?_
    show OpenList.empty.entries + Phi t ((∅ : Std.HashMap State Nat).insert t.init 0) < fuel
    omega
  · refine loop_terminates t heur hwf hunit fuel _ ok (noRepeat_init t)
      (hnbInit _ rfl rfl) ?_
    show (OpenList.empty.push _).entries
      + Phi t ((∅ : Std.HashMap State Nat).insert t.init 0) < fuel
    rw [OpenList.push_entries]
    omega

/--
With enough fuel the search always returns an answer: either a plan or
`unsolvable`.  Combined with `astar_sound`, `astar_optimal` and `astar_complete`,
this is what makes those three unconditional for a large enough fuel.
-/
theorem astar_decides (t : Task) (heur : Heuristic) (hwf : Task.WF t)
    (hunit : ∀ op ∈ t.ops, op.cost = 1) (fuel : Nat)
    (hfuel : stateCard t * (stateCard t + 1) + 1 < fuel) :
    (∃ plan cost, (astar t heur fuel).outcome = Outcome.solved plan cost) ∨
      (astar t heur fuel).outcome = Outcome.unsolvable := by
  have h := astar_terminates t heur hwf hunit fuel hfuel
  cases hout : (astar t heur fuel).outcome with
  | solved plan cost => exact Or.inl ⟨plan, cost, rfl⟩
  | unsolvable => exact Or.inr rfl
  | outOfFuel => exact absurd hout h

/--
The fuel the planner actually passes suffices for every task whose state space
the bound fits under it — which, since a search must hold a node per state it
expands, is every task that can be run at all.
-/
theorem astar_defaultFuel (t : Task) (heur : Heuristic) (hwf : Task.WF t)
    (hunit : ∀ op ∈ t.ops, op.cost = 1)
    (hsmall : stateCard t * (stateCard t + 1) + 1 < defaultFuel) :
    (astar t heur defaultFuel).outcome ≠ Outcome.outOfFuel :=
  astar_terminates t heur hwf hunit defaultFuel hsmall

end Planner
