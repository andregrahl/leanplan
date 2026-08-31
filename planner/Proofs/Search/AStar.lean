/-
A* is sound: every plan it prints is a real plan.

The search maintains `NodesOK` — node 0 is the initial state, and every other
node is one real transition past its parent, with `g` the accumulated cost.  Both
places that create nodes preserve it: `astar` starts with the root alone, and
`expandOne` only ever appends a node for an operator it has just checked to be
applicable.  Combined with `NodesOK.planTo_valid`, the plan the search extracts
from a goal node executes from the initial state to a goal state and costs
exactly what the search reports.

Nothing here needs the open list to be well behaved: the loop looks nodes up with
`nodes[i]?` and skips an entry that names no node, so soundness holds whatever
the open list does.  That is deliberate — a bug in the priority queue could make
the planner slow, or could cost optimality, but it can never make the planner
print something that is not a plan.
-/
import Proofs.Search.Node
import Proofs.Search.OpenList
import Planner.Search.AStar

namespace Planner

/-! ### Reading a pushed array -/

private theorem getD_push_lt (a : Array Node) (x : Node) {j : Nat} (h : j < a.size) :
    (a.push x).getD j default = a.getD j default := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, h, Nat.ne_of_lt h]

private theorem getD_push_eq (a : Array Node) (x : Node) :
    (a.push x).getD a.size default = x := by
  simp [Array.getD_eq_getD_getElem?]

/-! ### Appending one successor -/

/-- Appending a node reached by a real transition from an existing node. -/
theorem NodesOK.push {t : Task} {nodes : Array Node} (ok : NodesOK t nodes)
    {id i : Nat} {succ : State} {cost : Nat} (hid : id < nodes.size)
    (hstep : t.step (nodes.getD id default).state i succ) (hcost : cost = t.actionCost i) :
    NodesOK t (nodes.push
      { state := succ, g := (nodes.getD id default).g + cost, parent := id, op := some i }) := by
  subst hcost
  refine ⟨by simp, ?_, ?_, ?_⟩
  · rw [getD_push_lt _ _ ok.nonempty]
    exact ok.root
  · intro j hj hpos
    simp only [Array.size_push] at hj
    by_cases hlt : j < nodes.size
    · rw [getD_push_lt _ _ hlt]
      exact ok.parentLt j hlt hpos
    · have hje : j = nodes.size := by omega
      subst hje
      rw [getD_push_eq]
      exact hid
  · intro j hj hpos
    simp only [Array.size_push] at hj
    by_cases hlt : j < nodes.size
    · obtain ⟨op, hop, hstep', hg⟩ := ok.step j hlt hpos
      have hparent : (nodes.getD j default).parent < nodes.size :=
        Nat.lt_trans (ok.parentLt j hlt hpos) hlt
      simp only [getD_push_lt _ _ hlt, getD_push_lt _ _ hparent]
      exact ⟨op, hop, hstep', hg⟩
    · have hje : j = nodes.size := by omega
      subst hje
      simp only [getD_push_eq, getD_push_lt _ _ hid]
      exact ⟨i, rfl, hstep, rfl⟩

/-! ### What one operator does to the node array -/

/-- Recording a successor either changes nothing or appends exactly that node. -/
theorem record_nodes (heur : Heuristic) (id i : Nat) (succ : State) (g : Nat) (s : Search) :
    (record heur id i succ g s).nodes = s.nodes ∨
      (record heur id i succ g s).nodes =
        s.nodes.push { state := succ, g, parent := id, op := some i } := by
  simp only [record]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/--
Trying one operator either leaves the node array alone or appends exactly one
node, and in the second case the operator was applicable.  Separating this from
the invariant keeps the case analysis in one place.
-/
theorem expandOne_nodes (t : Task) (heur : Heuristic) (id : Nat) (node : Node) (i : Nat)
    (s : Search) :
    (expandOne t heur id node i s).nodes = s.nodes ∨
      ((t.ops.getD i default).applicable node.state = true ∧
       (expandOne t heur id node i s).nodes = s.nodes.push
         { state := (t.ops.getD i default).apply node.state,
           g := node.g + (t.ops.getD i default).cost, parent := id, op := some i }) := by
  simp only [expandOne]
  split
  · rename_i happ
    split
    · split
      · rcases record_nodes heur id i _ _ s with h | h
        · exact Or.inl h
        · exact Or.inr ⟨happ, h⟩
      · exact Or.inl rfl
    · rcases record_nodes heur id i _ _ s with h | h
      · exact Or.inl h
      · exact Or.inr ⟨happ, h⟩
  · exact Or.inl rfl

theorem expandOne_size (t : Task) (heur : Heuristic) (id : Nat) (node : Node) (i : Nat)
    (s : Search) : s.nodes.size ≤ (expandOne t heur id node i s).nodes.size := by
  rcases expandOne_nodes t heur id node i s with h | ⟨_, h⟩
  · rw [h]
  · rw [h]; simp

theorem expandOne_getElem (t : Task) (heur : Heuristic) (id : Nat) (node : Node) (i : Nat)
    (s : Search) {j : Nat} (hj : j < s.nodes.size) :
    (expandOne t heur id node i s).nodes.getD j default = s.nodes.getD j default := by
  rcases expandOne_nodes t heur id node i s with h | ⟨_, h⟩
  · rw [h]
  · rw [h]; exact getD_push_lt _ _ hj

theorem expandOne_nodesOK (t : Task) (heur : Heuristic) (id i : Nat) (s : Search)
    (node : Node) (ok : NodesOK t s.nodes) (hid : id < s.nodes.size)
    (hnode : node = s.nodes.getD id default) (hi : i < t.ops.size) :
    NodesOK t (expandOne t heur id node i s).nodes := by
  subst hnode
  have hop : t.ops.getD i default = t.ops[i] := by simp [Array.getD, hi]
  rcases expandOne_nodes t heur id (s.nodes.getD id default) i s with h | ⟨happ, h⟩
  · rw [h]; exact ok
  · rw [h]
    refine ok.push hid ⟨hi, ?_, ?_⟩ ?_
    · rw [← hop]; exact happ
    · rw [hop]
    · simp [Task.actionCost, hi, hop]

/-! ### The whole expansion preserves the invariant -/

theorem expandFrom_nodesOK (t : Task) (heur : Heuristic) (id : Nat) :
    ∀ (fuel i : Nat) (s : Search) (node : Node), NodesOK t s.nodes → id < s.nodes.size →
      node = s.nodes.getD id default →
      NodesOK t (expandFrom t heur id node fuel i s).nodes := by
  intro fuel
  induction fuel with
  | zero => intro i s node ok _ _; exact ok
  | succ fuel ih =>
      intro i s node ok hid hnode
      rw [expandFrom]
      split
      · rename_i hi
        have hok := expandOne_nodesOK t heur id i s node ok hid hnode hi
        have hid' : id < (expandOne t heur id node i s).nodes.size :=
          Nat.lt_of_lt_of_le hid (expandOne_size t heur id node i s)
        have hnode' : node = (expandOne t heur id node i s).nodes.getD id default := by
          rw [expandOne_getElem t heur id node i s hid]; exact hnode
        exact ih (i + 1) (expandOne t heur id node i s) node hok hid' hnode'
      · exact ok

theorem expand_nodesOK (t : Task) (heur : Heuristic) (id : Nat) (s : Search) (node : Node)
    (ok : NodesOK t s.nodes) (hid : id < s.nodes.size)
    (hnode : node = s.nodes.getD id default) :
    NodesOK t (expand t heur id node s).nodes := by
  rw [expand]
  exact expandFrom_nodesOK t heur id t.ops.size 0
    { s with expanded := s.expanded + 1 } node ok hid hnode


/-! ### How `best` evolves

`best` records the cheapest `g` at which each state has been reached.  Two facts
matter for optimality: it never rises, and expanding a node leaves every
successor recorded at no more than the node's cost plus one action.
-/

/-- `s'` knows a route to every state `s` knew of, and never a worse one. -/
def Improves (s s' : Search) : Prop :=
  ∀ (σ : State) (g : Nat), s.best[σ]? = some g → ∃ g' : Nat, s'.best[σ]? = some g' ∧ g' ≤ g

theorem Improves.refl (s : Search) : Improves s s := fun _ g h => ⟨g, h, Nat.le_refl _⟩

theorem Improves.trans {a b c : Search} (hab : Improves a b) (hbc : Improves b c) :
    Improves a c := by
  intro σ g h
  obtain ⟨g', hg', hle'⟩ := hab σ g h
  obtain ⟨g'', hg'', hle''⟩ := hbc σ g' hg'
  exact ⟨g'', hg'', Nat.le_trans hle'' hle'⟩

/-- Inserting a smaller value, or a value for an unseen state, improves `best`. -/
private theorem improves_insert (s : Search) (σ : State) (g : Nat)
    (hnew : ∀ g₀, s.best[σ]? = some g₀ → g ≤ g₀) :
    Improves s { s with best := s.best.insert σ g } := by
  intro τ gτ hτ
  by_cases hσ : τ = σ
  · subst hσ
    exact ⟨g, by simp, hnew gτ hτ⟩
  · refine ⟨gτ, ?_, Nat.le_refl _⟩
    show (s.best.insert σ g)[τ]? = some gτ
    rw [Std.HashMap.getElem?_insert, if_neg (by simpa using fun h => hσ h.symm)]
    exact hτ

theorem record_improves (heur : Heuristic) (id i : Nat) (succ : State) (g : Nat)
    (s : Search) (hnew : ∀ g₀, s.best[succ]? = some g₀ → g ≤ g₀) :
    Improves s (record heur id i succ g s) := by
  simp only [record]
  split <;> exact improves_insert s succ g hnew

theorem expandOne_improves (t : Task) (heur : Heuristic) (id : Nat) (node : Node)
    (i : Nat) (s : Search) : Improves s (expandOne t heur id node i s) := by
  simp only [expandOne]
  split
  · split
    · rename_i previous hprev
      split
      · rename_i hlt
        refine record_improves _ _ _ _ _ _ ?_
        intro g₀ hg₀
        have : s.best[(t.ops.getD i default).apply node.state]? = some previous := hprev
        rw [this] at hg₀
        simp only [Option.some.injEq] at hg₀
        omega
      · exact Improves.refl _
    · rename_i hnone
      refine record_improves _ _ _ _ _ _ ?_
      intro g₀ hg₀
      have : s.best[(t.ops.getD i default).apply node.state]? = none := hnone
      rw [this] at hg₀
      simp at hg₀
  · exact Improves.refl _

theorem expandFrom_improves (t : Task) (heur : Heuristic) (id : Nat) (node : Node) :
    ∀ (fuel i : Nat) (s : Search), Improves s (expandFrom t heur id node fuel i s) := by
  intro fuel
  induction fuel with
  | zero => intro i s; exact Improves.refl _
  | succ fuel ih =>
      intro i s
      rw [expandFrom]
      split
      · exact (expandOne_improves t heur id node i s).trans (ih (i + 1) _)
      · exact Improves.refl _

theorem expand_improves (t : Task) (heur : Heuristic) (id : Nat) (node : Node) (s : Search) :
    Improves s (expand t heur id node s) := by
  rw [expand]
  have h0 : Improves s { s with expanded := s.expanded + 1 } :=
    fun σ g h => ⟨g, h, Nat.le_refl _⟩
  exact h0.trans (expandFrom_improves t heur id node t.ops.size 0 _)

/-- Whatever `record` does with the open list, it always records the cost. -/
theorem record_best (heur : Heuristic) (id i : Nat) (succ : State) (g : Nat) (s : Search) :
    (record heur id i succ g s).best[succ]? = some g := by
  simp only [record]
  split <;> simp

/--
Trying an applicable operator always leaves its successor recorded at no more
than one action further: either the search inserts the new cost, or it keeps a
cost it already had, which it only kept because that one was no larger.
-/
theorem expandOne_records (t : Task) (heur : Heuristic) (id i : Nat) (node : Node)
    (s : Search) (hi : i < t.ops.size) (happ : t.ops[i].applicable node.state = true) :
    ∃ g', (expandOne t heur id node i s).best[t.ops[i].apply node.state]? = some g' ∧
      g' ≤ node.g + t.ops[i].cost := by
  have hgetD : t.ops.getD i default = t.ops[i] := OpenList.getD_eq_getElem _ _ _ hi
  simp only [expandOne, hgetD, if_pos happ]
  split
  · rename_i previous hprev
    split
    · exact ⟨_, record_best _ _ _ _ _ _, Nat.le_refl _⟩
    · rename_i hge
      exact ⟨previous, hprev, by omega⟩
  · exact ⟨_, record_best _ _ _ _ _ _, Nat.le_refl _⟩

/-- Sweeping the operators from `i` records every applicable one at or after `i`. -/
theorem expandFrom_records (t : Task) (heur : Heuristic) (id : Nat) (node : Node) :
    ∀ (fuel i : Nat) (s : Search) (j : Nat) (hj : j < t.ops.size), i ≤ j → j < i + fuel →
      t.ops[j].applicable node.state = true →
      ∃ g', (expandFrom t heur id node fuel i s).best[t.ops[j].apply node.state]? = some g' ∧
        g' ≤ node.g + t.ops[j].cost := by
  intro fuel
  induction fuel with
  | zero => intro i s j hj hij hlt _; omega
  | succ fuel ih =>
      intro i s j hj hij hlt happ
      rw [expandFrom]
      split
      · rename_i hi
        rcases Nat.eq_or_lt_of_le hij with hje | hgt
        · cases hje
          obtain ⟨g', hg', hle⟩ := expandOne_records t heur id i node s hj happ
          obtain ⟨g'', hg'', hle''⟩ :=
            expandFrom_improves t heur id node fuel (i + 1) _ _ g' hg'
          exact ⟨g'', hg'', by omega⟩
        · exact ih (i + 1) _ j hj hgt (by omega) happ
      · omega

/-! ### The frontier invariant

The heart of optimality.  For every state the search has a route to, either the
node holding that route is still on the open list — with the priority the search
gave it — or that node has been expanded, in which case every successor is
already recorded at no more than one action further.

Nothing here mentions a "closed set": the second disjunct *is* what being closed
buys, stated as a property of `best` alone, which is what makes the invariant a
predicate on the search state and nothing else.
-/

/-- The open list holds the entry the search created for `σ` at cost `g`. -/
def OpenFor (heur : Heuristic) (s : Search) (σ : State) (g : Nat) : Prop :=
  ∃ e, s.openList.Mem e ∧ e.f = g + heur.eval σ ∧
    ∃ k, s.nodes[e.node]? = some k ∧ k.state = σ ∧ k.g = g

/-- Expanding `σ` records every successor at no more than one action further. -/
def Relaxed (t : Task) (s : Search) (σ : State) (g : Nat) : Prop :=
  ∀ op ∈ t.ops, op.applicable σ = true →
    ∃ g' : Nat, s.best[op.apply σ]? = some g' ∧ g' ≤ g + op.cost

def Frontier (t : Task) (heur : Heuristic) (s : Search) : Prop :=
  ∀ (σ : State) (g : Nat), s.best[σ]? = some g → heur.eval σ < deadEnd →
    OpenFor heur s σ g ∨ Relaxed t s σ g

/-- Growing the node array and the open list cannot lose an `OpenFor` witness. -/
theorem OpenFor.mono {heur : Heuristic} {s s' : Search} {σ : State} {g : Nat}
    (h : OpenFor heur s σ g)
    (hopen : ∀ e, s.openList.Mem e → s'.openList.Mem e)
    (hnodes : ∀ (i : Nat) (k : Node), s.nodes[i]? = some k → s'.nodes[i]? = some k) :
    OpenFor heur s' σ g := by
  obtain ⟨e, hmem, hf, k, hk, hstate, hg⟩ := h
  exact ⟨e, hopen e hmem, hf, k, hnodes _ _ hk, hstate, hg⟩

/-- Lowering values in `best` cannot lose a `Relaxed` witness. -/
theorem Relaxed.mono {t : Task} {s s' : Search} {σ : State} {g : Nat}
    (h : Relaxed t s σ g) (himp : Improves s s') : Relaxed t s' σ g := by
  intro op hop happ
  obtain ⟨g', hg', hle⟩ := h op hop happ
  obtain ⟨g'', hg'', hle'⟩ := himp _ _ hg'
  exact ⟨g'', hg'', Nat.le_trans hle' hle⟩

/-- Expanding a node makes it `Relaxed`: every successor is now recorded. -/
theorem expand_relaxed (t : Task) (heur : Heuristic) (id : Nat) (node : Node) (s : Search) :
    Relaxed t (expand t heur id node s) node.state node.g := by
  intro op hop happ
  obtain ⟨j, hj, hjop⟩ := Array.getElem_of_mem hop
  subst hjop
  rw [expand]
  exact expandFrom_records t heur id node t.ops.size 0 _ j hj (Nat.zero_le _) (by omega) happ

/--
A state the search has just recorded, and not proved a dead end, is on the open
list at exactly the priority it was given.

This is the second half of frontier maintenance.  `record` inserts into `best`
and pushes an entry in the same breath, so the two can never drift apart — except
on a dead end, where it deliberately inserts without pushing, and `Frontier`
excuses exactly that case by its `heur.eval σ < deadEnd` hypothesis.
-/
theorem record_openFor (heur : Heuristic) (id i : Nat) (succ : State) (g : Nat)
    (s : Search) (hlt : heur.eval succ < deadEnd) :
    OpenFor heur (record heur id i succ g s) succ g := by
  have hnot : ¬ heur.eval succ ≥ deadEnd := by omega
  simp only [record, if_neg hnot]
  refine ⟨{ f := g + heur.eval succ, h := heur.eval succ, node := s.nodes.size }, ?_, rfl,
    { state := succ, g, parent := id, op := some i }, ?_, rfl, rfl⟩
  · exact OpenList.push_mem_self _ _
  · exact Array.getElem?_push_size

/-- The search starts with the initial state open at its own priority. -/
theorem frontier_init (t : Task) (heur : Heuristic) :
    Frontier t heur
      { openList := OpenList.empty.push { f := heur.eval t.init, h := heur.eval t.init, node := 0 }
        nodes := #[Node.root t]
        best := (∅ : Std.HashMap State Nat).insert t.init 0
        expanded := 0, generated := 0, evaluated := 1, pruned := 0 } := by
  intro σ g hbest _
  by_cases hσ : σ = t.init
  · -- The only state recorded is the initial one, at cost zero, and it is open.
    have h0 : ((∅ : Std.HashMap State Nat).insert t.init 0)[σ]? = some 0 := by
      rw [hσ]; simp
    rw [h0] at hbest
    have hg : g = 0 := by simpa using hbest.symm
    subst hg
    refine Or.inl ⟨{ f := heur.eval t.init, h := heur.eval t.init, node := 0 },
      OpenList.push_mem_self _ _, ?_, Node.root t, ?_, hσ.symm, rfl⟩
    · show heur.eval t.init = 0 + heur.eval σ
      rw [hσ, Nat.zero_add]
    · show (#[Node.root t] : Array Node)[0]? = some (Node.root t)
      simp
  · exfalso
    rw [Std.HashMap.getElem?_insert, if_neg (by simpa using fun h => hσ h.symm)] at hbest
    simp at hbest

/-! ### Frontier maintenance

Three lemmas, one per branch of the loop.  Two of them discard an open-list entry
without expanding; the third expands.
-/

private theorem getElem?_push_lt {α : Type} [Inhabited α] (a : Array α) (x : α) {j : Nat}
    (h : j < a.size) : (a.push x)[j]? = a[j]? := by
  rw [Array.getElem?_eq_getElem h, Array.getElem?_eq_getElem (by simp; omega),
    Array.getElem_push_lt]

/-- `record` only ever adds to the open list and to the node array. -/
theorem record_mono (heur : Heuristic) (id i : Nat) (succ : State) (g : Nat) (s : Search) :
    (∀ e, s.openList.Mem e → (record heur id i succ g s).openList.Mem e) ∧
      (∀ (j : Nat) (k : Node), s.nodes[j]? = some k → (record heur id i succ g s).nodes[j]? = some k) := by
  simp only [record]
  split
  · exact ⟨fun _ he => he, fun _ _ h => h⟩
  · refine ⟨fun e he => OpenList.push_mem _ _ _ he, fun j k h => ?_⟩
    have hj : j < s.nodes.size := by
      by_contra hcon
      rw [Array.getElem?_eq_none (by omega)] at h
      simp at h
    show (s.nodes.push _)[j]? = some k
    rw [getElem?_push_lt _ _ hj]
    exact h

theorem expandOne_mono (t : Task) (heur : Heuristic) (id i : Nat) (node : Node) (s : Search) :
    (∀ e, s.openList.Mem e → (expandOne t heur id node i s).openList.Mem e) ∧
      (∀ (j : Nat) (k : Node), s.nodes[j]? = some k → (expandOne t heur id node i s).nodes[j]? = some k) := by
  simp only [expandOne]
  split
  · split
    · split
      · exact record_mono _ _ _ _ _ _
      · exact ⟨fun _ he => he, fun _ _ h => h⟩
    · exact record_mono _ _ _ _ _ _
  · exact ⟨fun _ he => he, fun _ _ h => h⟩

theorem expandFrom_mono (t : Task) (heur : Heuristic) (id : Nat) (node : Node) :
    ∀ (fuel i : Nat) (s : Search),
      (∀ e, s.openList.Mem e → (expandFrom t heur id node fuel i s).openList.Mem e) ∧
        (∀ (j : Nat) (k : Node), s.nodes[j]? = some k → (expandFrom t heur id node fuel i s).nodes[j]? = some k) := by
  intro fuel
  induction fuel with
  | zero => intro i s; exact ⟨fun _ he => he, fun _ _ h => h⟩
  | succ fuel ih =>
      intro i s
      rw [expandFrom]
      split
      · obtain ⟨h1, h2⟩ := expandOne_mono t heur id i node s
        obtain ⟨h3, h4⟩ := ih (i + 1) (expandOne t heur id node i s)
        exact ⟨fun e he => h3 e (h1 e he), fun j k h => h4 j k (h2 j k h)⟩
      · exact ⟨fun _ he => he, fun _ _ h => h⟩

theorem expand_mono (t : Task) (heur : Heuristic) (id : Nat) (node : Node) (s : Search) :
    (∀ e, s.openList.Mem e → (expand t heur id node s).openList.Mem e) ∧
      (∀ (j : Nat) (k : Node), s.nodes[j]? = some k → (expand t heur id node s).nodes[j]? = some k) := by
  rw [expand]
  exact expandFrom_mono t heur id node t.ops.size 0 { s with expanded := s.expanded + 1 }

/-- Looking up a state other than the one recorded sees straight through. -/
private theorem record_best_ne (heur : Heuristic) (id i : Nat) (succ : State) (g₀ : Nat)
    (s : Search) {σ : State} (hσ : σ ≠ succ) :
    (record heur id i succ g₀ s).best[σ]? = s.best[σ]? := by
  simp only [record]
  split <;>
    · show (s.best.insert succ g₀)[σ]? = _
      rw [Std.HashMap.getElem?_insert, if_neg (by simpa using fun h => hσ h.symm)]

/-- After `record`, a state's cost is either the one it already had, or it is open. -/
theorem record_openFor_of_best (heur : Heuristic) (id i : Nat) (succ : State) (g₀ : Nat)
    (s : Search) {σ : State} {g : Nat}
    (hbest : (record heur id i succ g₀ s).best[σ]? = some g)
    (hlt : heur.eval σ < deadEnd) :
    s.best[σ]? = some g ∨ OpenFor heur (record heur id i succ g₀ s) σ g := by
  by_cases hσ : σ = succ
  · have hb : (record heur id i succ g₀ s).best[σ]? = some g₀ := by
      rw [hσ]; exact record_best _ _ _ _ _ _
    rw [hb] at hbest
    have hgg : g = g₀ := by simpa using hbest.symm
    subst hgg
    refine Or.inr ?_
    rw [hσ]
    exact record_openFor heur id i succ g s (by rw [← hσ]; exact hlt)
  · exact Or.inl (by rw [← record_best_ne heur id i succ g₀ s hσ]; exact hbest)

/-- `expandOne` either leaves `best` alone or is exactly one `record`. -/
private theorem expandOne_shape (t : Task) (heur : Heuristic) (id i : Nat) (node : Node)
    (s : Search) :
    (∀ (σ : State), (expandOne t heur id node i s).best[σ]? = s.best[σ]?) ∨
      ∃ succ g₀, expandOne t heur id node i s = record heur id i succ g₀ s := by
  simp only [expandOne]
  split
  · split
    · split
      · exact Or.inr ⟨_, _, rfl⟩
      · exact Or.inl fun _ => rfl
    · exact Or.inr ⟨_, _, rfl⟩
  · exact Or.inl fun _ => rfl

theorem expandOne_openFor (t : Task) (heur : Heuristic) (id i : Nat) (node : Node) (s : Search)
    {σ : State} {g : Nat} (hbest : (expandOne t heur id node i s).best[σ]? = some g)
    (hlt : heur.eval σ < deadEnd) :
    s.best[σ]? = some g ∨ OpenFor heur (expandOne t heur id node i s) σ g := by
  rcases expandOne_shape t heur id i node s with h | ⟨succ, g₀, heq⟩
  · exact Or.inl (by rw [← h σ]; exact hbest)
  · rw [heq] at hbest ⊢
    exact record_openFor_of_best _ _ _ _ _ _ hbest hlt

theorem expandFrom_openFor (t : Task) (heur : Heuristic) (id : Nat) (node : Node) :
    ∀ (fuel i : Nat) (s : Search) {σ : State} {g : Nat},
      (expandFrom t heur id node fuel i s).best[σ]? = some g → heur.eval σ < deadEnd →
      s.best[σ]? = some g ∨ OpenFor heur (expandFrom t heur id node fuel i s) σ g := by
  intro fuel
  induction fuel with
  | zero => intro i s σ g hbest _; exact Or.inl hbest
  | succ fuel ih =>
      intro i s σ g hbest hlt
      rw [expandFrom] at hbest ⊢
      split at hbest
      · rename_i hi
        rw [if_pos hi]
        rcases ih (i + 1) (expandOne t heur id node i s) hbest hlt with h | h
        · rcases expandOne_openFor t heur id i node s h hlt with h' | h'
          · exact Or.inl h'
          · obtain ⟨h1, h2⟩ := expandFrom_mono t heur id node fuel (i + 1)
              (expandOne t heur id node i s)
            exact Or.inr (h'.mono h1 h2)
        · exact Or.inr h
      · rename_i hi
        rw [if_neg hi]
        exact Or.inl hbest

theorem expand_openFor (t : Task) (heur : Heuristic) (id : Nat) (node : Node) (s : Search)
    {σ : State} {g : Nat} (hbest : (expand t heur id node s).best[σ]? = some g)
    (hlt : heur.eval σ < deadEnd) :
    s.best[σ]? = some g ∨ OpenFor heur (expand t heur id node s) σ g := by
  rw [expand] at hbest ⊢
  exact expandFrom_openFor t heur id node t.ops.size 0 _ hbest hlt

/--
Dropping an open-list entry without expanding keeps the invariant, in both
branches where the loop does so.

The entry dropped is never the `OpenFor` witness for the cost `best` currently
records.  Two entries with the same node index denote the very same node, so a
witness for `(σ, g)` sitting at `entry.node` would force `σ` and `g` to be that
node's own state and `g` — which a dangling entry rules out, since it names no
node at all, and a stale entry rules out too, since the search has already beaten
the `g` its node carries.
-/
theorem frontier_discard (t : Task) (heur : Heuristic) (s : Search)
    {entry : Entry} {rest : OpenList} (hq : s.openList.WF)
    (hpop : s.openList.pop? = some (entry, rest))
    (hF : Frontier t heur s)
    (hdrop : ∀ k, s.nodes[entry.node]? = some k → s.best[k.state]? ≠ some k.g) :
    Frontier t heur { s with openList := rest } := by
  intro σ g hbest hlt
  rcases hF σ g hbest hlt with ⟨e, hmem, hf, k, hk, hkstate, hkg⟩ | hrel
  · have hne : e.node ≠ entry.node := by
      intro heq
      refine hdrop k (by rw [← heq]; exact hk) ?_
      rw [hkstate, hkg]; exact hbest
    obtain ⟨-, -, hsurv, -⟩ := OpenList.pop?_spec hq hpop
    exact Or.inl ⟨e, hsurv e hmem hne, hf, k, hk, hkstate, hkg⟩
  · exact Or.inr hrel

/--
Expanding keeps the invariant.

Three things can be true of a state after the expansion.  If the expansion
recorded it, `record` pushed it and it is open.  If it kept the cost it already
had, the old invariant still speaks about it — unless its witness was the entry
just popped, and then that state is the one being expanded, which `expand_relaxed`
has just made `Relaxed`.  That last case is the whole point of the invariant's
second disjunct: it is what replaces a closed set.
-/
theorem frontier_expand (t : Task) (heur : Heuristic) (s : Search)
    {entry : Entry} {rest : OpenList} (hq : s.openList.WF)
    (hpop : s.openList.pop? = some (entry, rest))
    {node : Node} (hnode : s.nodes[entry.node]? = some node)
    (hF : Frontier t heur s) :
    Frontier t heur (expand t heur entry.node node { s with openList := rest }) := by
  intro σ g hbest hlt
  obtain ⟨hopenMono, hnodeMono⟩ := expand_mono t heur entry.node node { s with openList := rest }
  have hdrop : Improves s { s with openList := rest } := fun _ g h => ⟨g, h, Nat.le_refl _⟩
  rcases expand_openFor t heur entry.node node { s with openList := rest } hbest hlt with
    hold | hopen
  · rcases hF σ g hold hlt with ⟨e, hmem, hf, k, hk, hkstate, hkg⟩ | hrel
    · by_cases hne : e.node = entry.node
      · have hknode : k = node := by
          rw [hne, hnode] at hk
          simpa using hk.symm
        subst hknode
        refine Or.inr ?_
        rw [← hkstate, ← hkg]
        exact expand_relaxed t heur entry.node k _
      · obtain ⟨-, -, hsurv, -⟩ := OpenList.pop?_spec hq hpop
        have hbase : OpenFor heur { s with openList := rest } σ g :=
          ⟨e, hsurv e hmem hne, hf, k, hk, hkstate, hkg⟩
        exact Or.inl (hbase.mono hopenMono hnodeMono)
    · exact Or.inr (hrel.mono
        (hdrop.trans (expand_improves t heur entry.node node { s with openList := rest })))
  · exact Or.inl hopen

/--
A goal state the search has recorded is still on the open list.

`Frontier` alone is not enough for optimality.  Its second disjunct says a state
has been expanded, and for a goal that can never have happened: the loop tests
for a goal on *pop* and returns immediately, so it expands only non-goals.  This
invariant records exactly that, and it is what turns "the goal is known at cost
`g`" into "an entry of priority `g` is waiting to be popped".
-/
def GoalsOpen (t : Task) (heur : Heuristic) (s : Search) : Prop :=
  ∀ (σ : State) (g : Nat), s.best[σ]? = some g → t.isGoal σ = true →
    heur.eval σ < deadEnd → OpenFor heur s σ g

theorem goalsOpen_discard (t : Task) (heur : Heuristic) (s : Search)
    {entry : Entry} {rest : OpenList} (hq : s.openList.WF)
    (hpop : s.openList.pop? = some (entry, rest))
    (hG : GoalsOpen t heur s)
    (hdrop : ∀ k, s.nodes[entry.node]? = some k → s.best[k.state]? ≠ some k.g) :
    GoalsOpen t heur { s with openList := rest } := by
  intro σ g hbest hgoal hlt
  obtain ⟨e, hmem, hf, k, hk, hkstate, hkg⟩ := hG σ g hbest hgoal hlt
  have hne : e.node ≠ entry.node := by
    intro heq
    refine hdrop k (by rw [← heq]; exact hk) ?_
    rw [hkstate, hkg]; exact hbest
  obtain ⟨-, -, hsurv, -⟩ := OpenList.pop?_spec hq hpop
  exact ⟨e, hsurv e hmem hne, hf, k, hk, hkstate, hkg⟩

theorem goalsOpen_expand (t : Task) (heur : Heuristic) (s : Search)
    {entry : Entry} {rest : OpenList} (hq : s.openList.WF)
    (hpop : s.openList.pop? = some (entry, rest))
    {node : Node} (hnode : s.nodes[entry.node]? = some node)
    (hnotgoal : t.isGoal node.state = false)
    (hG : GoalsOpen t heur s) :
    GoalsOpen t heur (expand t heur entry.node node { s with openList := rest }) := by
  intro σ g hbest hgoal hlt
  obtain ⟨hopenMono, hnodeMono⟩ := expand_mono t heur entry.node node { s with openList := rest }
  rcases expand_openFor t heur entry.node node { s with openList := rest } hbest hlt with
    hold | hopen
  · obtain ⟨e, hmem, hf, k, hk, hkstate, hkg⟩ := hG σ g hold hgoal hlt
    have hne : e.node ≠ entry.node := by
      intro heq
      have hknode : k = node := by
        rw [heq, hnode] at hk
        simpa using hk.symm
      subst hknode
      rw [hkstate] at hnotgoal
      rw [hgoal] at hnotgoal
      exact Bool.noConfusion hnotgoal
    obtain ⟨-, -, hsurv, -⟩ := OpenList.pop?_spec hq hpop
    have hbase : OpenFor heur { s with openList := rest } σ g :=
      ⟨e, hsurv e hmem hne, hf, k, hk, hkstate, hkg⟩
    exact hbase.mono hopenMono hnodeMono
  · exact hopen

private theorem lt_size_of_getElem? {α : Type} [Inhabited α] {a : Array α} {j : Nat} {x : α}
    (h : a[j]? = some x) : j < a.size := by
  by_contra hcon
  rw [Array.getElem?_eq_none (by omega)] at h
  simp at h

/--
Every open entry names a node, and carries the priority that node earns: `f = g + h`.

`OpenFor` says this of the witness it produces; this says it of *every* entry,
which is what makes the popped entry's minimality say something about its `g`.
-/
def EntryOK (heur : Heuristic) (s : Search) : Prop :=
  ∀ e, s.openList.Mem e → ∃ k, s.nodes[e.node]? = some k ∧ e.f = k.g + heur.eval k.state

theorem record_entryOK (heur : Heuristic) (id i : Nat) (succ : State) (g : Nat) (s : Search)
    (hE : EntryOK heur s) : EntryOK heur (record heur id i succ g s) := by
  simp only [record]
  split
  · exact hE
  · intro e hmem
    rcases OpenList.mem_push hmem with hold | ⟨hf, -, hnode⟩
    · -- an entry that was already there names a node the push did not disturb
      obtain ⟨k, hk, hfk⟩ := hE e hold
      refine ⟨k, ?_, hfk⟩
      rw [getElem?_push_lt _ _ (lt_size_of_getElem? hk)]
      exact hk
    · -- the entry just pushed names the node just appended
      refine ⟨{ state := succ, g, parent := id, op := some i }, ?_, hf⟩
      rw [hnode]; exact Array.getElem?_push_size

theorem expandOne_entryOK (t : Task) (heur : Heuristic) (id i : Nat) (node : Node) (s : Search)
    (hE : EntryOK heur s) : EntryOK heur (expandOne t heur id node i s) := by
  rcases expandOne_shape t heur id i node s with _ | ⟨succ, g₀, heq⟩
  · simp only [expandOne]
    split
    · split
      · split
        · exact record_entryOK _ _ _ _ _ _ hE
        · exact hE
      · exact record_entryOK _ _ _ _ _ _ hE
    · exact hE
  · rw [heq]; exact record_entryOK _ _ _ _ _ _ hE

theorem expandFrom_entryOK (t : Task) (heur : Heuristic) (id : Nat) (node : Node) :
    ∀ (fuel i : Nat) (s : Search), EntryOK heur s →
      EntryOK heur (expandFrom t heur id node fuel i s) := by
  intro fuel
  induction fuel with
  | zero => intro i s hE; exact hE
  | succ fuel ih =>
      intro i s hE
      rw [expandFrom]
      split
      · exact ih (i + 1) _ (expandOne_entryOK t heur id i node s hE)
      · exact hE

theorem expand_entryOK (t : Task) (heur : Heuristic) (id : Nat) (node : Node) (s : Search)
    (hE : EntryOK heur s) : EntryOK heur (expand t heur id node s) := by
  rw [expand]
  exact expandFrom_entryOK t heur id node t.ops.size 0 _ hE

/-- The state invariant survives a whole execution, not just one action. -/
theorem invariant_executes {S A : Type} {m : PlanningModel S A} {P : S → Prop}
    (hP : Invariant m P) : ∀ {s : S} {pl : List A} {f : S}, P s → Executes m s pl f → P f := by
  intro s pl f hs hexec
  induction hexec with
  | nil _ => exact hs
  | cons htrans _ ih => exact ih (hP _ _ _ hs htrans)

theorem record_wf (heur : Heuristic) (id i : Nat) (succ : State) (g : Nat) (s : Search)
    (hq : s.openList.WF) : (record heur id i succ g s).openList.WF := by
  simp only [record]
  split
  · exact hq
  · exact OpenList.push_wf hq _

theorem expandOne_wf (t : Task) (heur : Heuristic) (id i : Nat) (node : Node) (s : Search)
    (hq : s.openList.WF) : (expandOne t heur id node i s).openList.WF := by
  rcases expandOne_shape t heur id i node s with _ | ⟨succ, g₀, heq⟩
  · simp only [expandOne]
    split
    · split
      · split
        · exact record_wf _ _ _ _ _ _ hq
        · exact hq
      · exact record_wf _ _ _ _ _ _ hq
    · exact hq
  · rw [heq]; exact record_wf _ _ _ _ _ _ hq

theorem expandFrom_wf (t : Task) (heur : Heuristic) (id : Nat) (node : Node) :
    ∀ (fuel i : Nat) (s : Search), s.openList.WF →
      (expandFrom t heur id node fuel i s).openList.WF := by
  intro fuel
  induction fuel with
  | zero => intro i s hq; exact hq
  | succ fuel ih =>
      intro i s hq
      rw [expandFrom]
      split
      · exact ih (i + 1) _ (expandOne_wf t heur id i node s hq)
      · exact hq

theorem expand_wf (t : Task) (heur : Heuristic) (id : Nat) (node : Node) (s : Search)
    (hq : s.openList.WF) : (expand t heur id node s).openList.WF := by
  rw [expand]
  exact expandFrom_wf t heur id node t.ops.size 0 _ hq

/-- `best` never rises, and zero is the floor, so the initial state stays at zero. -/
theorem init_stays (s s' : Search) (t : Task) (himp : Improves s s')
    (h : s.best[t.init]? = some 0) : s'.best[t.init]? = some 0 := by
  obtain ⟨g', hg', hle⟩ := himp _ _ h
  have : g' = 0 := by omega
  rw [← this]; exact hg'

/-! ### Soundness -/

private theorem deadEnd_pos : 0 < deadEnd := by decide

/--
The heart of the optimality argument, and the only place the heuristic's
admissibility is used.

`Frontier` says that every state the search knows a route to is either still open
at the priority it was given, or has been expanded with all of its successors
recorded.  Walk any plan from such a state and that dichotomy can only end one of
two ways.  Either some state along the plan is still open — and then its `f` is at
most the cost of the whole plan, because `g` is what the search has already paid
and the heuristic never overestimates what is left — or every state along it has
been recorded instead, the goal included, at no more than the plan's cost.

Either way the search is holding something that costs at most this plan, which is
what forbids it from returning anything dearer.
-/
theorem frontier_bound (t : Task) (heur : Heuristic) (P : State → Prop)
    (hP : Invariant t.model P)
    (hga : GoalAware t.model P heur.eval)
    (hadm : Admissible t.model P heur.eval)
    {s : Search} (hF : Frontier t heur s)
    {σ : State} {plan : List Nat} {final : State}
    (hexec : Executes t.model σ plan final) :
    ∀ {g : Nat}, s.best[σ]? = some g → P σ → t.model.isGoal final →
      g + planCost t.model plan < deadEnd →
      (∃ e, s.openList.Mem e ∧ e.f ≤ g + planCost t.model plan) ∨
        (∃ g', s.best[final]? = some g' ∧ g' ≤ g + planCost t.model plan) := by
  induction hexec with
  | nil σ' =>
      intro g hbest hPσ hgoal _
      have hzero : heur.eval σ' = 0 := hga σ' hPσ hgoal
      have hlt : heur.eval σ' < deadEnd := by rw [hzero]; exact deadEnd_pos
      rcases hF σ' g hbest hlt with ⟨e, hmem, hf, _⟩ | hrel
      · exact Or.inl ⟨e, hmem, by simp [planCost, hf, hzero]⟩
      · exact Or.inr ⟨g, hbest, by simp [planCost]⟩
  | @cons σ' mid final' a rest htrans hrest ih =>
      intro g hbest hPσ hgoal hlive
      -- The heuristic cannot exceed the cost of the plan still ahead of it.
      have hle : heur.eval σ' ≤ planCost t.model (a :: rest) :=
        hadm σ' (a :: rest) final' hPσ (Executes.cons htrans hrest) hgoal
      have hlt : heur.eval σ' < deadEnd := by
        have : planCost t.model (a :: rest) ≤ g + planCost t.model (a :: rest) := Nat.le_add_left _ _
        omega
      rcases hF σ' g hbest hlt with ⟨e, hmem, hf, _⟩ | hrel
      · exact Or.inl ⟨e, hmem, by omega⟩
      · -- Every successor is recorded, so follow the plan one step and recurse.
        obtain ⟨ha, happ, hmid⟩ := htrans
        obtain ⟨g₁, hg₁, hle₁⟩ := hrel t.ops[a] (Array.getElem_mem ha) happ
        have hcost : t.actionCost a = t.ops[a].cost := by
          simp [Task.actionCost, Array.getElem?_eq_getElem ha]
        have hbest₁ : s.best[mid]? = some g₁ := by rw [hmid]; exact hg₁
        have hlive₁ : g₁ + planCost t.model rest < deadEnd := by
          simp only [planCost, Task.model_actionCost] at hlive
          omega
        rcases ih hbest₁ (hP σ' a mid hPσ ⟨ha, happ, hmid⟩) hgoal hlive₁ with
          ⟨e, hmem, hbound⟩ | ⟨g', hg', hbound⟩
        · refine Or.inl ⟨e, hmem, ?_⟩
          simp only [planCost, Task.model_actionCost]
          omega
        · refine Or.inr ⟨g', hg', ?_⟩
          simp only [planCost, Task.model_actionCost]
          omega

/-- Every iteration keeps `NodesOK`, and a solved outcome carries a real plan. -/
theorem loop_sound (t : Task) (heur : Heuristic) :
    ∀ (fuel : Nat) (s : Search), NodesOK t s.nodes →
      ∀ plan cost, (loop t heur fuel s).outcome = .solved plan cost →
        ∃ final, Executes t.model t.init plan.toList final ∧ t.isGoal final = true ∧
          planCost t.model plan.toList = cost := by
  intro fuel
  induction fuel with
  | zero => intro s _ plan cost h; simp [loop] at h
  | succ fuel ih =>
      intro s ok plan cost h
      rw [loop] at h
      split at h
      · simp at h
      · rename_i entry rest _
        split at h
        · exact ih { s with openList := rest } ok plan cost h
        · rename_i node hnode
          obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.mp hnode
          have hget : node = s.nodes.getD entry.node default := by
            rw [Array.getD_eq_getD_getElem?, hnode]
            rfl
          split at h
          · exact ih { s with openList := rest } ok plan cost h
          · split at h
            · -- A goal node was popped: read the plan off the parent chain.
              rename_i hgoal
              obtain ⟨hplan, hcost⟩ :=
                ok.planTo_valid entry.node hlt (s.nodes.size + 1) (by omega)
              have hp : plan = extractPlan s.nodes entry.node :=
                (by simpa [Outcome.planOf] using congrArg Outcome.planOf h : _ = plan).symm
              have hc : cost = node.g :=
                (by simpa [Outcome.costOf] using congrArg Outcome.costOf h : _ = cost).symm
              refine ⟨node.state, ?_, hgoal, ?_⟩
              · rw [hp, extractPlan, hget]; exact hplan
              · rw [hp, extractPlan, hc, hget]; exact hcost
            · exact ih _ (expand_nodesOK t heur entry.node { s with openList := rest } node
                ok hlt hget) plan cost h

/-! ### Optimality -/

/-- Only the initial state is recorded at startup, and at cost zero. -/
private theorem best_init_only {t : Task} {σ : State} {g : Nat}
    (hb : ((∅ : Std.HashMap State Nat).insert t.init 0)[σ]? = some g) : σ = t.init ∧ g = 0 := by
  by_cases hσ : σ = t.init
  · refine ⟨hσ, ?_⟩
    rw [hσ] at hb; simp at hb; omega
  · exfalso
    rw [Std.HashMap.getElem?_insert, if_neg (by simpa using fun h => hσ h.symm)] at hb
    simp at hb

theorem goalsOpen_init (t : Task) (heur : Heuristic) :
    GoalsOpen t heur
      { openList := OpenList.empty.push { f := heur.eval t.init, h := heur.eval t.init, node := 0 }
        nodes := #[Node.root t]
        best := (∅ : Std.HashMap State Nat).insert t.init 0
        expanded := 0, generated := 0, evaluated := 1, pruned := 0 } := by
  intro σ g hbest _ _
  obtain ⟨hσ, hg⟩ := best_init_only hbest
  subst hg
  refine ⟨{ f := heur.eval t.init, h := heur.eval t.init, node := 0 },
    OpenList.push_mem_self _ _, ?_, Node.root t, ?_, hσ.symm, rfl⟩
  · show heur.eval t.init = 0 + heur.eval σ
    rw [hσ, Nat.zero_add]
  · show (#[Node.root t] : Array Node)[0]? = some (Node.root t)
    simp

theorem entryOK_init (t : Task) (heur : Heuristic) :
    EntryOK heur
      { openList := OpenList.empty.push { f := heur.eval t.init, h := heur.eval t.init, node := 0 }
        nodes := #[Node.root t]
        best := (∅ : Std.HashMap State Nat).insert t.init 0
        expanded := 0, generated := 0, evaluated := 1, pruned := 0 } := by
  intro e he
  rcases OpenList.mem_push he with hold | ⟨hf, -, hnode⟩
  · exact absurd hold (OpenList.not_mem_empty e)
  · refine ⟨Node.root t, ?_, ?_⟩
    · rw [hnode]
      show (#[Node.root t] : Array Node)[0]? = some (Node.root t)
      simp
    · rw [hf]
      show heur.eval t.init = (Node.root t).g + heur.eval (Node.root t).state
      simp [Node.root]



/--
The loop never returns a plan dearer than one that exists.

At the moment it returns, the goal node it popped had the least `f` on the open
list.  `frontier_bound` produces an open entry whose `f` is at most the cost of
*any* goal-reaching plan, so the popped entry's `f` is at most that as well; and
`EntryOK` says that `f` is the node's own `g` plus its heuristic value, hence at
least its `g`.  The cost returned is that `g`.

The `deadEnd` side condition is what the pruning rule needs: a heuristic may
report `deadEnd` only on states it has shown have no plan, so no plan costing
less than `deadEnd` is ever pruned away.
-/
theorem loop_optimal (t : Task) (heur : Heuristic) (P : State → Prop)
    (hP : Invariant t.model P) (hPinit : P t.init)
    (hga : GoalAware t.model P heur.eval)
    (hadm : Admissible t.model P heur.eval) :
    ∀ (fuel : Nat) (s : Search), s.openList.WF → Frontier t heur s → GoalsOpen t heur s →
      EntryOK heur s → s.best[t.init]? = some 0 →
      ∀ {plan : Array Nat} {cost : Nat},
        (loop t heur fuel s).outcome = .solved plan cost →
        ∀ (pl : List Nat) (final : State), Executes t.model t.init pl final →
          t.model.isGoal final → planCost t.model pl < deadEnd →
          cost ≤ planCost t.model pl := by
  intro fuel
  induction fuel with
  | zero => intro s _ _ _ _ _ plan cost hout; simp [loop] at hout
  | succ fuel ih =>
      intro s hq hF hG hE hinit plan cost hout pl final hexec hgoal hlive
      rw [loop] at hout
      split at hout
      · simp at hout
      · rename_i entry rest hpop
        obtain ⟨hentryMem, hmin, hsurv, hwf'⟩ := OpenList.pop?_spec hq hpop
        have hrestE : EntryOK heur { s with openList := rest } :=
          fun e he => hE e (OpenList.pop?_mem_mono hpop e he)
        split at hout
        · rename_i hnone
          have hdrop : ∀ k, s.nodes[entry.node]? = some k → s.best[k.state]? ≠ some k.g := by
            intro k hk; rw [hnone] at hk; simp at hk
          exact ih _ hwf' (frontier_discard t heur s hq hpop hF hdrop)
            (goalsOpen_discard t heur s hq hpop hG hdrop) hrestE hinit hout pl final hexec
            hgoal hlive
        · rename_i node hnode
          split at hout
          · rename_i hstale
            have hdrop : ∀ k, s.nodes[entry.node]? = some k → s.best[k.state]? ≠ some k.g := by
              intro k hk hcon
              rw [hnode] at hk
              have hkn : k = node := by simpa using hk.symm
              subst hkn
              rw [Std.HashMap.getD_eq_getD_getElem?, hcon] at hstale
              simp at hstale
            exact ih _ hwf' (frontier_discard t heur s hq hpop hF hdrop)
              (goalsOpen_discard t heur s hq hpop hG hdrop) hrestE hinit hout pl final hexec
              hgoal hlive
          · split at hout
            · -- A goal node was popped: this is the return, and it is optimal.
              rename_i hgoalNode
              have hc : cost = node.g :=
                (by simpa [Outcome.costOf] using congrArg Outcome.costOf hout : _ = cost).symm
              have hPfinal : P final := invariant_executes hP hPinit hexec
              have hzero : heur.eval final = 0 := hga final hPfinal hgoal
              have hopen : ∃ e, s.openList.Mem e ∧ e.f ≤ planCost t.model pl := by
                rcases frontier_bound t heur P hP hga hadm hF hexec hinit hPinit hgoal
                    (by omega) with ⟨e, hmem, hb⟩ | ⟨g', hg', hb⟩
                · exact ⟨e, hmem, by omega⟩
                · obtain ⟨e, hmem, hf, -⟩ :=
                    hG final g' hg' (by simpa using hgoal) (by rw [hzero]; exact deadEnd_pos)
                  exact ⟨e, hmem, by omega⟩
              obtain ⟨e, hmem, hb⟩ := hopen
              obtain ⟨k, hk, hfk⟩ := hE entry hentryMem
              rw [hnode] at hk
              have hkn : k = node := by simpa using hk.symm
              subst hkn
              have hle := hmin e hmem
              omega
            · rename_i hnotgoal
              exact ih _ (expand_wf t heur entry.node node _ hwf')
                (frontier_expand t heur s hq hpop hnode hF)
                (goalsOpen_expand t heur s hq hpop hnode (by simpa using hnotgoal) hG)
                (expand_entryOK t heur entry.node node _ hrestE)
                (init_stays _ _ t (expand_improves t heur entry.node node _) hinit)
                hout pl final hexec hgoal hlive

/-- Any plan `astar` prints executes from the initial state to a goal state, at the cost it reports. -/
theorem astar_sound (t : Task) (heur : Heuristic) (fuel : Nat)
    {plan : Array Nat} {cost : Nat}
    (h : (astar t heur fuel).outcome = .solved plan cost) :
    ∃ final, Executes t.model t.init plan.toList final ∧ t.isGoal final = true ∧
      planCost t.model plan.toList = cost := by
  have ok : NodesOK t #[Node.root t] := by
    refine ⟨by simp, ?_, ?_, ?_⟩
    · simp [Array.getD_eq_getD_getElem?, Node.root]
    · intro j hj hpos; simp at hj; omega
    · intro j hj hpos; simp at hj; omega
  rw [astar] at h
  split at h <;> exact loop_sound t heur fuel _ ok plan cost h

/--
The loop reports `unsolvable` only when there is no plan.

The argument is short, because the invariants already carry it.  `unsolvable` is
returned exactly when the open list runs dry, and `pop?_none` says nothing is on
it.  But if a plan existed, `frontier_bound` would hand back either an open entry
— impossible — or the goal recorded in `best`, and `GoalsOpen` turns a recorded
goal into an open entry, which is impossible for the same reason.

The bound is stated as "every goal-reaching plan costs at least `deadEnd`" rather
than "no plan exists", which is the honest form: pruning may discard a state the
heuristic called a dead end, so what the search rules out is plans cheaper than
`deadEnd`.
-/
theorem loop_complete (t : Task) (heur : Heuristic) (P : State → Prop)
    (hP : Invariant t.model P) (hPinit : P t.init)
    (hga : GoalAware t.model P heur.eval)
    (hadm : Admissible t.model P heur.eval) :
    ∀ (fuel : Nat) (s : Search), s.openList.WF → Frontier t heur s → GoalsOpen t heur s →
      EntryOK heur s → s.best[t.init]? = some 0 →
      (loop t heur fuel s).outcome = .unsolvable →
      ∀ (pl : List Nat) (final : State), Executes t.model t.init pl final →
        t.model.isGoal final → deadEnd ≤ planCost t.model pl := by
  intro fuel
  induction fuel with
  | zero => intro s _ _ _ _ _ hout; simp [loop] at hout
  | succ fuel ih =>
      intro s hq hF hG hE hinit hout pl final hexec hgoal
      by_contra hcon
      push_neg at hcon
      rw [loop] at hout
      split at hout
      · -- The open list ran dry, yet a cheap plan exists: impossible.
        rename_i hpopnone
        have hno : ∀ e, ¬ s.openList.Mem e := OpenList.pop?_none hq hpopnone
        have hPfinal : P final := invariant_executes hP hPinit hexec
        have hzero : heur.eval final = 0 := hga final hPfinal hgoal
        rcases frontier_bound t heur P hP hga hadm hF hexec hinit hPinit hgoal (by omega) with
          ⟨e, hmem, -⟩ | ⟨g', hg', -⟩
        · exact hno e hmem
        · obtain ⟨e, hmem, -⟩ :=
            hG final g' hg' (by simpa using hgoal) (by rw [hzero]; exact deadEnd_pos)
          exact hno e hmem
      · rename_i entry rest hpop
        obtain ⟨hentryMem, hmin, hsurv, hwf'⟩ := OpenList.pop?_spec hq hpop
        have hrestE : EntryOK heur { s with openList := rest } :=
          fun e he => hE e (OpenList.pop?_mem_mono hpop e he)
        split at hout
        · rename_i hnone
          have hdrop : ∀ k, s.nodes[entry.node]? = some k → s.best[k.state]? ≠ some k.g := by
            intro k hk; rw [hnone] at hk; simp at hk
          exact absurd (ih _ hwf' (frontier_discard t heur s hq hpop hF hdrop)
            (goalsOpen_discard t heur s hq hpop hG hdrop) hrestE hinit hout pl final hexec hgoal)
            (by omega)
        · rename_i node hnode
          split at hout
          · rename_i hstale
            have hdrop : ∀ k, s.nodes[entry.node]? = some k → s.best[k.state]? ≠ some k.g := by
              intro k hk hcon2
              rw [hnode] at hk
              have hkn : k = node := by simpa using hk.symm
              subst hkn
              rw [Std.HashMap.getD_eq_getD_getElem?, hcon2] at hstale
              simp at hstale
            exact absurd (ih _ hwf' (frontier_discard t heur s hq hpop hF hdrop)
              (goalsOpen_discard t heur s hq hpop hG hdrop) hrestE hinit hout pl final hexec hgoal)
              (by omega)
          · split at hout
            · simp at hout
            · rename_i hnotgoal
              exact absurd (ih _ (expand_wf t heur entry.node node _ hwf')
                (frontier_expand t heur s hq hpop hnode hF)
                (goalsOpen_expand t heur s hq hpop hnode (by simpa using hnotgoal) hG)
                (expand_entryOK t heur entry.node node _ hrestE)
                (init_stays _ _ t (expand_improves t heur entry.node node _) hinit)
                hout pl final hexec hgoal) (by omega)

/--
**A\* is optimal.**  The plan it prints costs no more than any goal-reaching plan.

The heuristic must be goal-aware and consistent — hence admissible — relative to
an invariant the initial state satisfies, and the plan compared against must cost
less than `deadEnd`, which is the side condition the pruning rule needs.
-/
theorem astar_optimal (t : Task) (heur : Heuristic) (P : State → Prop)
    (hP : Invariant t.model P) (hPinit : P t.init)
    (hga : GoalAware t.model P heur.eval)
    (hadm : Admissible t.model P heur.eval) (fuel : Nat)
    {plan : Array Nat} {cost : Nat}
    (hout : (astar t heur fuel).outcome = .solved plan cost)
    (pl : List Nat) (final : State) (hexec : Executes t.model t.init pl final)
    (hgoal : t.model.isGoal final) (hlive : planCost t.model pl < deadEnd) :
    cost ≤ planCost t.model pl := by
  have hbest : ((∅ : Std.HashMap State Nat).insert t.init 0)[t.init]? = some 0 := by simp
  rw [astar] at hout
  split at hout
  · -- The initial state is a dead end, so nothing is ever opened.
    rename_i hdead
    have hdead' : deadEnd ≤ heur.eval t.init := by simpa [Node.root] using hdead
    refine loop_optimal t heur P hP hPinit hga hadm fuel _ OpenList.empty_wf ?_ ?_ ?_ hbest
      hout pl final hexec hgoal hlive
    · intro σ g hb hlt
      rw [(best_init_only hb).1] at hlt
      omega
    · intro σ g hb _ hlt
      rw [(best_init_only hb).1] at hlt
      omega
    · intro e he
      exact absurd he (OpenList.not_mem_empty e)
  · exact loop_optimal t heur P hP hPinit hga hadm fuel _
      (OpenList.push_wf OpenList.empty_wf _) (frontier_init t heur) (goalsOpen_init t heur)
      (entryOK_init t heur) hbest hout pl final hexec hgoal hlive

/--
**A\* is complete.**  It reports `unsolvable` only when every goal-reaching plan
costs at least `deadEnd` — which, with unit costs and `deadEnd = 2^40`, is to say
there is no plan.

The bound is stated this way rather than as "no plan exists" because it is the
honest form: a heuristic may prune a state it reports as a dead end, so what the
search rules out is plans cheaper than `deadEnd`.
-/
theorem astar_complete (t : Task) (heur : Heuristic) (P : State → Prop)
    (hP : Invariant t.model P) (hPinit : P t.init)
    (hga : GoalAware t.model P heur.eval)
    (hadm : Admissible t.model P heur.eval) (fuel : Nat)
    (hout : (astar t heur fuel).outcome = .unsolvable)
    (pl : List Nat) (final : State) (hexec : Executes t.model t.init pl final)
    (hgoal : t.model.isGoal final) :
    deadEnd ≤ planCost t.model pl := by
  have hbest : ((∅ : Std.HashMap State Nat).insert t.init 0)[t.init]? = some 0 := by simp
  rw [astar] at hout
  split at hout
  · rename_i hdead
    have hdead' : deadEnd ≤ heur.eval t.init := by simpa [Node.root] using hdead
    refine loop_complete t heur P hP hPinit hga hadm fuel _ OpenList.empty_wf ?_ ?_ ?_ hbest
      hout pl final hexec hgoal
    · intro σ g hb hlt
      rw [(best_init_only hb).1] at hlt
      omega
    · intro σ g hb _ hlt
      rw [(best_init_only hb).1] at hlt
      omega
    · intro e he
      exact absurd he (OpenList.not_mem_empty e)
  · exact loop_complete t heur P hP hPinit hga hadm fuel _
      (OpenList.push_wf OpenList.empty_wf _) (frontier_init t heur) (goalsOpen_init t heur)
      (entryOK_init t heur) hbest hout pl final hexec hgoal

/-! ### Towards the fuel bound

`Proofs/Finite.lean` shows the state space is finite; the counting on top of it
starts here.  Every node the search creates records its state in `best` at the same
moment, and `record` only fires when the new cost undercuts what was there — so a
node's cost is never below what `best` currently holds for its state.  That is the
invariant the chain-distinctness argument needs: a state repeating on a parent
chain would have to have been recorded at a larger cost than it already had.
-/

/-- Every node's cost is at least what `best` records for its state. -/
def NodeGBounded (s : Search) : Prop :=
  ∀ (i : Nat) (k : Node), s.nodes[i]? = some k →
    ∃ g, s.best[k.state]? = some g ∧ g ≤ k.g

theorem record_nodeGBounded (heur : Heuristic) (id i : Nat) (succ : State) (g : Nat)
    (s : Search) (h : NodeGBounded s)
    (hnew : ∀ g₀, s.best[succ]? = some g₀ → g < g₀) :
    NodeGBounded (record heur id i succ g s) := by
  have lookup : ∀ (σ : State) (b : Nat), s.best[σ]? = some b →
      ∃ b', (s.best.insert succ g)[σ]? = some b' ∧ b' ≤ max b g := by
    intro σ b hb
    by_cases hσ : σ = succ
    · refine ⟨g, ?_, Nat.le_max_right _ _⟩
      rw [hσ]; simp
    · refine ⟨b, ?_, Nat.le_max_left _ _⟩
      rw [Std.HashMap.getElem?_insert, if_neg (by simpa using fun hc => hσ hc.symm)]
      exact hb
  simp only [record]
  split
  · intro j k hk
    obtain ⟨b, hb, hle⟩ := h j k hk
    by_cases hσ : k.state = succ
    · refine ⟨g, ?_, ?_⟩
      · show (s.best.insert succ g)[k.state]? = some g
        rw [hσ]; simp
      · have := hnew b (by rw [← hσ]; exact hb)
        omega
    · refine ⟨b, ?_, hle⟩
      show (s.best.insert succ g)[k.state]? = some b
      rw [Std.HashMap.getElem?_insert, if_neg (by simpa using fun hc => hσ hc.symm)]
      exact hb
  · intro j k hk
    by_cases hj : j < s.nodes.size
    · have hk' : s.nodes[j]? = some k := by
        rw [← getElem?_push_lt s.nodes { state := succ, g, parent := id, op := some i } hj]
        exact hk
      obtain ⟨b, hb, hle⟩ := h j k hk'
      by_cases hσ : k.state = succ
      · refine ⟨g, ?_, ?_⟩
        · show (s.best.insert succ g)[k.state]? = some g
          rw [hσ]; simp
        · have := hnew b (by rw [← hσ]; exact hb)
          omega
      · refine ⟨b, ?_, hle⟩
        show (s.best.insert succ g)[k.state]? = some b
        rw [Std.HashMap.getElem?_insert, if_neg (by simpa using fun hc => hσ hc.symm)]
        exact hb
    · have hjs : j = s.nodes.size := by
        have := lt_size_of_getElem? hk
        simp only [Array.size_push] at this
        omega
      have hknew : k = { state := succ, g, parent := id, op := some i } := by
        rw [hjs] at hk
        rw [Array.getElem?_push_size] at hk
        simpa using hk.symm
      subst hknew
      refine ⟨g, ?_, Nat.le_refl _⟩
      show (s.best.insert succ g)[succ]? = some g
      simp

theorem expandOne_nodeGBounded (t : Task) (heur : Heuristic) (id i : Nat) (node : Node)
    (s : Search) (h : NodeGBounded s) : NodeGBounded (expandOne t heur id node i s) := by
  simp only [expandOne]
  split
  · split
    · rename_i previous hprev
      split
      · rename_i hlt
        refine record_nodeGBounded _ _ _ _ _ _ h ?_
        intro g₀ hg₀
        have hp : s.best[(t.ops.getD i default).apply node.state]? = some previous := hprev
        rw [hp] at hg₀
        simp only [Option.some.injEq] at hg₀
        omega
      · exact h
    · rename_i hnone
      refine record_nodeGBounded _ _ _ _ _ _ h ?_
      intro g₀ hg₀
      have hp : s.best[(t.ops.getD i default).apply node.state]? = none := hnone
      rw [hp] at hg₀
      simp at hg₀
  · exact h

theorem expandFrom_nodeGBounded (t : Task) (heur : Heuristic) (id : Nat) (node : Node) :
    ∀ (fuel i : Nat) (s : Search), NodeGBounded s →
      NodeGBounded (expandFrom t heur id node fuel i s) := by
  intro fuel
  induction fuel with
  | zero => intro i s h; exact h
  | succ fuel ih =>
      intro i s h
      rw [expandFrom]
      split
      · exact ih (i + 1) _ (expandOne_nodeGBounded t heur id i node s h)
      · exact h

theorem expand_nodeGBounded (t : Task) (heur : Heuristic) (id : Nat) (node : Node) (s : Search)
    (h : NodeGBounded s) : NodeGBounded (expand t heur id node s) := by
  rw [expand]
  exact expandFrom_nodeGBounded t heur id node t.ops.size 0 _ h

/-- The invariant holds at startup: the only node is the root, recorded at zero. -/
theorem nodeGBounded_init (t : Task) (heur : Heuristic) (ol : OpenList) :
    NodeGBounded
      { openList := ol
        nodes := #[Node.root t]
        best := (∅ : Std.HashMap State Nat).insert t.init 0
        expanded := 0, generated := 0, evaluated := 1, pruned := 0 } := by
  intro j k hk
  have hj : j = 0 := by
    have := lt_size_of_getElem? hk
    simp at this
    omega
  subst hj
  have hkr : k = Node.root t := by
    simpa using hk.symm
  subst hkr
  exact ⟨0, by simp [Node.root], Nat.le_refl _⟩

/--
The state a `record` is about to append is new to its parent's chain.

This is the step the whole fuel bound turns on.  Suppose the state already sat on
the chain, at some node `j`.  `NodeGBounded` puts `best` for that state at or below
`j`'s cost, `ancestor_g_le` puts `j`'s cost at or below the parent's, and the node
being created costs strictly more than the parent — so `best` for that state is
strictly below the new cost.  But `record` only fires when the new cost is strictly
*below* `best`.  The state cannot have been there.
-/
theorem record_fresh (t : Task) (id : Nat) (succ : State) (g : Nat) (s : Search)
    (ok : NodesOK t s.nodes) (hcost : ∀ op ∈ t.ops, 0 < op.cost)
    (hnb : NodeGBounded s) (hid : id < s.nodes.size)
    (hg : (s.nodes.getD id default).g < g)
    (hnew : ∀ g₀, s.best[succ]? = some g₀ → g < g₀) :
    ∀ j, NodesOK.Ancestor s.nodes id j → (s.nodes.getD j default).state ≠ succ := by
  intro j hanc heq
  have hjle : j ≤ id := NodesOK.ancestor_le ok id hid j hanc
  have hjlt : j < s.nodes.size := Nat.lt_of_le_of_lt hjle hid
  have hgj : (s.nodes.getD j default).g ≤ (s.nodes.getD id default).g :=
    NodesOK.ancestor_g_le ok hcost id hid j hanc
  have hjnode : s.nodes[j]? = some (s.nodes.getD j default) := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hjlt]
    rfl
  obtain ⟨b, hb, hble⟩ := hnb j _ hjnode
  rw [heq] at hb
  have := hnew b hb
  omega

/-- `record` keeps chains repeat-free. -/
theorem record_noRepeat (t : Task) (heur : Heuristic) (id i : Nat) (succ : State) (g : Nat)
    (s : Search) (ok : NodesOK t s.nodes) (hcost : ∀ op ∈ t.ops, 0 < op.cost)
    (hnb : NodeGBounded s) (hnr : NodesOK.NoRepeat s.nodes)
    (hid : id < s.nodes.size) (hg : (s.nodes.getD id default).g < g)
    (hnew : ∀ g₀, s.best[succ]? = some g₀ → g < g₀) :
    NodesOK.NoRepeat (record heur id i succ g s).nodes := by
  simp only [record]
  split
  · exact hnr
  · exact NodesOK.noRepeat_push ok hnr _ hid
      (record_fresh t id succ g s ok hcost hnb hid hg hnew)

/-- Trying one operator keeps chains repeat-free. -/
theorem expandOne_noRepeat (t : Task) (heur : Heuristic) (id i : Nat) (node : Node)
    (s : Search) (ok : NodesOK t s.nodes) (hcost : ∀ op ∈ t.ops, 0 < op.cost)
    (hnb : NodeGBounded s) (hnr : NodesOK.NoRepeat s.nodes)
    (hid : id < s.nodes.size) (hget : s.nodes.getD id default = node)
    (hi : i < t.ops.size) :
    NodesOK.NoRepeat (expandOne t heur id node i s).nodes := by
  have hgpos : (s.nodes.getD id default).g < node.g + t.ops[i].cost := by
    rw [hget]
    have := hcost _ (Array.getElem_mem hi)
    omega
  have hgetD : t.ops.getD i default = t.ops[i] := OpenList.getD_eq_getElem _ _ _ hi
  simp only [expandOne, hgetD]
  split
  · split
    · rename_i previous hprev
      split
      · rename_i hlt2
        refine record_noRepeat t heur id i _ _ s ok hcost hnb hnr hid hgpos ?_
        intro g₀ hg₀
        have hp : s.best[t.ops[i].apply node.state]? = some previous := hprev
        rw [hp] at hg₀
        simp only [Option.some.injEq] at hg₀
        omega
      · exact hnr
    · rename_i hnone
      refine record_noRepeat t heur id i _ _ s ok hcost hnb hnr hid hgpos ?_
      intro g₀ hg₀
      have hp : s.best[t.ops[i].apply node.state]? = none := hnone
      rw [hp] at hg₀
      simp at hg₀
  · exact hnr

/-- Sweeping the operators keeps chains repeat-free. -/
theorem expandFrom_noRepeat (t : Task) (heur : Heuristic) (id : Nat) (node : Node)
    (hcost : ∀ op ∈ t.ops, 0 < op.cost) :
    ∀ (fuel i : Nat) (s : Search), NodesOK t s.nodes → NodeGBounded s →
      NodesOK.NoRepeat s.nodes → id < s.nodes.size → s.nodes.getD id default = node →
      NodesOK.NoRepeat (expandFrom t heur id node fuel i s).nodes := by
  intro fuel
  induction fuel with
  | zero => intro i s _ _ hnr _ _; exact hnr
  | succ fuel ih =>
      intro i s ok hnb hnr hid hget
      rw [expandFrom]
      split
      · rename_i hi
        refine ih (i + 1) _ ?_ ?_ ?_ ?_ ?_
        · exact expandOne_nodesOK t heur id i s node ok hid hget.symm hi
        · exact expandOne_nodeGBounded t heur id i node s hnb
        · exact expandOne_noRepeat t heur id i node s ok hcost hnb hnr hid hget hi
        · exact Nat.lt_of_lt_of_le hid (expandOne_size t heur id node i s)
        · rw [expandOne_getElem t heur id node i s hid]; exact hget
      · exact hnr

/-- Expanding a node keeps chains repeat-free. -/
theorem expand_noRepeat (t : Task) (heur : Heuristic) (id : Nat) (node : Node) (s : Search)
    (hcost : ∀ op ∈ t.ops, 0 < op.cost) (ok : NodesOK t s.nodes) (hnb : NodeGBounded s)
    (hnr : NodesOK.NoRepeat s.nodes) (hid : id < s.nodes.size)
    (hget : s.nodes.getD id default = node) :
    NodesOK.NoRepeat (expand t heur id node s).nodes := by
  rw [expand]
  exact expandFrom_noRepeat t heur id node hcost t.ops.size 0 _ ok hnb hnr hid hget

/-- At startup the only chain is the root's, so nothing repeats. -/
theorem noRepeat_init (t : Task) : NodesOK.NoRepeat #[Node.root t] := by
  intro i hi j ha hne
  simp only [Array.size_singleton] at hi
  have hi0 : i = 0 := by omega
  subst hi0
  cases ha with
  | self => exact absurd rfl hne
  | step hpos _ => exact absurd hpos (by omega)

/-! ### Fuel is only a resource bound

The three theorems above are all conditional on the loop not running out of fuel.
This says that is the *only* thing fuel can affect: whenever the search finishes,
giving it more fuel returns exactly the same result, so `outOfFuel` is a report of
exhaustion rather than a fourth kind of answer. What is still not proved is that
some fuel always suffices; `Main.lean` passes `2^62`, which exceeds the number of
states any search fitting in memory can expand by many orders of magnitude.
-/

theorem loop_mono (t : Task) (heur : Heuristic) :
    ∀ (fuel k : Nat) (s : Search), (loop t heur fuel s).outcome ≠ .outOfFuel →
      loop t heur (fuel + k) s = loop t heur fuel s := by
  intro fuel
  induction fuel with
  | zero => intro k s h; simp [loop] at h
  | succ fuel ih =>
      intro k s h
      rw [show fuel + 1 + k = (fuel + k) + 1 by omega, loop, loop]
      rw [loop] at h
      cases hpop : s.openList.pop? with
      | none => simp only
      | some pr =>
          obtain ⟨entry, rest⟩ := pr
          simp only [hpop] at h ⊢
          cases hnode : s.nodes[entry.node]? with
          | none =>
              simp only [hnode] at h ⊢
              exact ih k _ h
          | some node =>
              simp only [hnode] at h ⊢
              by_cases hstale : s.best.getD node.state node.g < node.g
              · simp only [if_pos hstale] at h ⊢
                exact ih k _ h
              · simp only [if_neg hstale] at h ⊢
                by_cases hgoal : t.isGoal node.state = true
                · simp only [if_pos hgoal]
                · simp only [if_neg hgoal] at h ⊢
                  exact ih k _ h

/-- Whenever the search finishes, more fuel returns exactly the same result. -/
theorem astar_mono (t : Task) (heur : Heuristic) (fuel k : Nat)
    (h : (astar t heur fuel).outcome ≠ .outOfFuel) :
    astar t heur (fuel + k) = astar t heur fuel := by
  simp only [astar] at h ⊢
  split
  · rename_i hd
    simp only [if_pos hd] at h
    exact loop_mono t heur fuel k _ h
  · rename_i hd
    simp only [if_neg hd] at h
    exact loop_mono t heur fuel k _ h

end Planner
