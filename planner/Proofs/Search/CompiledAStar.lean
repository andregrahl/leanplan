/- Correctness of the production A* over the compiled runtime task. -/
import Proofs.CompiledTask
import Proofs.Search.AStar
import Planner.Search.CompiledAStar

namespace Planner

private theorem bit_zero_of_lsb {word : UInt64} (h : (word &&& 1 != 0) = true) :
    word.toBitVec.getLsbD 0 = true := by
  have hw := State.word_test word 0 (by omega)
  have hw' : (word &&& 1 != 0) = word.toBitVec.getLsbD 0 := by simpa using hw
  rw [hw'] at h
  exact h

private theorem lsb_of_bit_zero {word : UInt64}
    (h : word.toBitVec.getLsbD 0 = true) : (word &&& 1 != 0) = true := by
  have hw := State.word_test word 0 (by omega)
  have hw' : (word &&& 1 != 0) = word.toBitVec.getLsbD 0 := by simpa using hw
  rw [hw']
  exact h

private theorem bit_shift_one (word : UInt64) (bit : Nat) :
    (word >>> 1).toBitVec.getLsbD bit = word.toBitVec.getLsbD (bit + 1) := by
  simpa [UInt64.toBitVec_shiftRight, BitVec.getLsbD_ushiftRight, Nat.add_comm]

/-- Running a known-applicable compiled operator either keeps the node array or appends it. -/
theorem expandApplicableCompiled_nodes (t : CompiledTask) (heur : Heuristic)
    (id i : Nat) (node : Node) (s : Search) :
    (expandApplicableCompiled t heur id i node s).nodes = s.nodes ∨
      (expandApplicableCompiled t heur id i node s).nodes = s.nodes.push
        { state := (t.ops.getD i default).apply node.state,
          g := node.g + (t.ops.getD i default).logical.cost,
          parent := id, op := some i } := by
  simp only [expandApplicableCompiled]
  split
  · split
    · exact record_nodes _ _ _ _ _ _
    · exact Or.inl rfl
  · exact record_nodes _ _ _ _ _ _

theorem expandCandidateCompiled_nodes (t : CompiledTask) (heur : Heuristic)
    (id i : Nat) (node : Node) (s : Search) :
    (expandCandidateCompiled t heur id i node s).nodes = s.nodes ∨
      (expandCandidateCompiled t heur id i node s).nodes = s.nodes.push
        { state := (t.ops.getD i default).apply node.state,
          g := node.g + (t.ops.getD i default).logical.cost,
          parent := id, op := some i } := by
  simp only [expandCandidateCompiled]
  split
  · exact expandApplicableCompiled_nodes t heur id i node s
  · exact Or.inl rfl

theorem expandCandidateCompiled_size (t : CompiledTask) (heur : Heuristic)
    (id i : Nat) (node : Node) (s : Search) :
    s.nodes.size ≤ (expandCandidateCompiled t heur id i node s).nodes.size := by
  rcases expandCandidateCompiled_nodes t heur id i node s with h | h
  · rw [h]
  · rw [h]
    simp

theorem expandCandidateCompiled_getD (t : CompiledTask) (heur : Heuristic)
    (id i : Nat) (node : Node) (s : Search) {j : Nat} (hj : j < s.nodes.size) :
    (expandCandidateCompiled t heur id i node s).nodes.getD j default =
      s.nodes.getD j default := by
  rcases expandCandidateCompiled_nodes t heur id i node s with h | h
  · rw [h]
  · rw [h]
    exact NodesOK.getD_push_lt _ _ hj

/-- A candidate reached through its true trigger is a real logical transition. -/
theorem expandCandidateCompiled_nodesOK (t : Task) (heur : Heuristic)
    (id i : Nat) (node : Node) (s : Search) (hwf : Task.WF t)
    (ok : NodesOK t s.nodes) (hid : id < s.nodes.size)
    (hnode : node = s.nodes.getD id default) (hi : i < t.ops.size)
    (htrigger : triggerSatisfied t i node.state = true) :
    NodesOK t (expandCandidateCompiled (compileTaskIdentity t) heur id i node s).nodes := by
  let cop := (compileTaskIdentity t).ops[i]'(by simpa using hi)
  have hget : (compileTaskIdentity t).ops.getD i default = cop := by
    simp [Array.getD, hi, cop]
  have hlogical : cop.logical = t.ops[i] := compileTaskIdentity_op_logical t hi
  have hstate : State.WF t.numFacts node.state := by
    rw [hnode]
    exact NodesOK.states_wf hwf ok id hid
  simp only [expandCandidateCompiled, hget]
  split
  · rename_i hcond
    have happ : cop.applicable node.state = true := by
      by_cases hempty : cop.remainingPre.isEmpty
      · rw [CompiledOp.applicable, Array.isEmpty_iff.mp hempty]
        simp [State.holdsAll]
      · simpa [hempty] using hcond
    have happLogical : t.ops[i].applicable node.state = true := by
      rw [← compileTaskIdentity_op_applicable t node.state hi htrigger]
      exact happ
    rcases expandApplicableCompiled_nodes (compileTaskIdentity t) heur id i node s with h | h
    · rw [h]
      exact ok
    · rw [h, hget]
      have happly : cop.apply node.state = t.ops[i].apply node.state :=
        compileTaskIdentity_op_apply t node.state hwf hi hstate
      rw [happly, hlogical]
      rw [hnode]
      refine ok.push hid ⟨hi, ?_, rfl⟩ ?_
      · simpa [← hnode] using happLogical
      simp [Task.actionCost, hi]
  · exact ok

theorem expandBucketCompiledFrom_nodesOK (t : Task) (heur : Heuristic)
    (id : Nat) (node : Node) (ids : Array Nat) (hwf : Task.WF t)
    (hids : ∀ i ∈ ids, i < t.ops.size ∧ triggerSatisfied t i node.state = true) :
    ∀ (fuel pos : Nat) (s : Search), NodesOK t s.nodes → id < s.nodes.size →
      node = s.nodes.getD id default →
      NodesOK t
        (expandBucketCompiledFrom (compileTaskIdentity t) heur id node ids fuel pos s).nodes := by
  intro fuel
  induction fuel with
  | zero => intro pos s ok _ _; exact ok
  | succ fuel ih =>
      intro pos s ok hid hnode
      rw [expandBucketCompiledFrom]
      split
      · rename_i hpos
        let i := ids[pos]
        have himem : i ∈ ids := by
          simp [i]
        obtain ⟨hi, htrigger⟩ := hids i himem
        have ok' := expandCandidateCompiled_nodesOK t heur id i node s hwf ok hid hnode hi htrigger
        have hid' : id <
            (expandCandidateCompiled (compileTaskIdentity t) heur id i node s).nodes.size :=
          Nat.lt_of_lt_of_le hid
            (expandCandidateCompiled_size (compileTaskIdentity t) heur id i node s)
        have hnode' : node =
            (expandCandidateCompiled (compileTaskIdentity t) heur id i node s).nodes.getD
              id default := by
          rw [expandCandidateCompiled_getD (compileTaskIdentity t) heur id i node s hid]
          exact hnode
        exact ih (pos + 1)
          (expandCandidateCompiled (compileTaskIdentity t) heur id i node s) ok' hid' hnode'
      · exact ok

theorem expandBucketCompiledFrom_size (t : CompiledTask) (heur : Heuristic)
    (id : Nat) (node : Node) (ids : Array Nat) :
    ∀ (fuel pos : Nat) (s : Search), s.nodes.size ≤
      (expandBucketCompiledFrom t heur id node ids fuel pos s).nodes.size := by
  intro fuel
  induction fuel with
  | zero => intro pos s; exact Nat.le_refl _
  | succ fuel ih =>
      intro pos s
      rw [expandBucketCompiledFrom]
      split
      · exact Nat.le_trans (expandCandidateCompiled_size t heur id _ node s) (ih (pos + 1) _)
      · exact Nat.le_refl _

theorem expandBucketCompiledFrom_getD (t : CompiledTask) (heur : Heuristic)
    (id : Nat) (node : Node) (ids : Array Nat) :
    ∀ (fuel pos : Nat) (s : Search) {j : Nat}, j < s.nodes.size →
      (expandBucketCompiledFrom t heur id node ids fuel pos s).nodes.getD j default =
        s.nodes.getD j default := by
  intro fuel
  induction fuel with
  | zero => intro pos s j hj; rfl
  | succ fuel ih =>
      intro pos s j hj
      rw [expandBucketCompiledFrom]
      split
      · rw [ih (pos + 1) _
          (Nat.lt_of_lt_of_le hj (expandCandidateCompiled_size t heur id _ node s)),
          expandCandidateCompiled_getD t heur id _ node s hj]
        simp [Array.getD, hj]
      · rfl

private theorem fallback_ids_good (t : Task) (s : State) :
    ∀ i ∈ (compileSuccessorGenerator t).fallback,
      i < t.ops.size ∧ triggerSatisfied t i s = true := by
  intro i hi
  obtain ⟨hlt, hnone⟩ := SuccessorGenerator.mem_fallback.mp hi
  exact ⟨hlt, by simp [triggerSatisfied, hnone]⟩

private theorem fact_bucket_ids_good (t : Task) (s : State) (fact : Nat)
    (htrue : s.test fact = true) :
    ∀ i ∈ (compileSuccessorGenerator t).byFact.getD fact #[],
      i < t.ops.size ∧ triggerSatisfied t i s = true := by
  intro i hi
  by_cases hf : fact < t.numFacts
  · obtain ⟨hlt, htrigger⟩ := (SuccessorGenerator.mem_byFact hf).mp hi
    exact ⟨hlt, by simp [triggerSatisfied, htrigger, htrue]⟩
  · have : (compileSuccessorGenerator t).byFact.getD fact #[] = #[] := by
      simp [compileSuccessorGenerator, hf]
    rw [this] at hi
    simp at hi

theorem expandWordCompiled_nodesOK (t : Task) (heur : Heuristic)
    (id : Nat) (node : Node) (wordIndex : Nat) (original : UInt64)
    (hwf : Task.WF t) (horiginal : original = node.state.words.getD wordIndex 0) :
    ∀ (fuel offset : Nat) (word : UInt64) (s : Search),
      offset + fuel = 64 →
      (∀ bit, bit < fuel →
        word.toBitVec.getLsbD bit = original.toBitVec.getLsbD (offset + bit)) →
      NodesOK t s.nodes → id < s.nodes.size → node = s.nodes.getD id default →
      NodesOK t
        (expandWordCompiled (compileTaskIdentity t) heur id node (wordIndex * 64)
          fuel word s).nodes := by
  intro fuel
  induction fuel with
  | zero => intro offset word s _ _ ok _ _; exact ok
  | succ fuel ih =>
      intro offset word s hsum hbits ok hid hnode
      rw [expandWordCompiled]
      split
      · exact ok
      · rename_i hnonzero
        have hbit : 64 - (fuel + 1) = offset := by omega
        split
        · rename_i hlsb
          have hzero : word.toBitVec.getLsbD 0 = true := bit_zero_of_lsb hlsb
          have horigBit : original.toBitVec.getLsbD offset = true := by
            have hb0 : word.toBitVec.getLsbD 0 =
                original.toBitVec.getLsbD offset := by
              simpa using hbits 0 (by omega)
            rw [← hb0]
            exact hzero
          have htest : node.state.test (wordIndex * 64 + offset) = true := by
            rw [State.test_word_bit _ _ _ (by omega), ← horiginal]
            exact horigBit
          let ids := (compileSuccessorGenerator t).byFact.getD
            (wordIndex * 64 + offset) #[]
          have hids : ∀ i ∈ ids,
              i < t.ops.size ∧ triggerSatisfied t i node.state = true := by
            exact fact_bucket_ids_good t node.state (wordIndex * 64 + offset) htest
          let next := expandBucketCompiledFrom (compileTaskIdentity t) heur id node ids
            ids.size 0 s
          have ok' : NodesOK t next.nodes := by
            exact expandBucketCompiledFrom_nodesOK t heur id node ids hwf hids
              ids.size 0 s ok hid hnode
          have hid' : id < next.nodes.size := by
            exact Nat.lt_of_lt_of_le hid
              (expandBucketCompiledFrom_size (compileTaskIdentity t) heur id node ids
                ids.size 0 s)
          have hnode' : node = next.nodes.getD id default := by
            rw [expandBucketCompiledFrom_getD (compileTaskIdentity t) heur id node ids
              ids.size 0 s hid]
            exact hnode
          have hbits' : ∀ bit, bit < fuel →
              (word >>> 1).toBitVec.getLsbD bit =
                original.toBitVec.getLsbD (offset + 1 + bit) := by
            intro bit hb
            rw [bit_shift_one]
            rw [show offset + 1 + bit = offset + (bit + 1) by omega]
            exact hbits (bit + 1) (by omega)
          simpa [hbit, ids, next] using
            ih (offset + 1) (word >>> 1) next (by omega) hbits' ok' hid' hnode'
        · rename_i hlsb
          have hbits' : ∀ bit, bit < fuel →
              (word >>> 1).toBitVec.getLsbD bit =
                original.toBitVec.getLsbD (offset + 1 + bit) := by
            intro bit hb
            rw [bit_shift_one]
            rw [show offset + 1 + bit = offset + (bit + 1) by omega]
            exact hbits (bit + 1) (by omega)
          simpa [hbit] using
            ih (offset + 1) (word >>> 1) s (by omega) hbits' ok hid hnode

theorem expandWordCompiled_size (t : CompiledTask) (heur : Heuristic)
    (id : Nat) (node : Node) (base : Nat) :
    ∀ (fuel : Nat) (word : UInt64) (s : Search), s.nodes.size ≤
      (expandWordCompiled t heur id node base fuel word s).nodes.size := by
  intro fuel
  induction fuel with
  | zero => intro word s; exact Nat.le_refl _
  | succ fuel ih =>
      intro word s
      rw [expandWordCompiled]
      split
      · exact Nat.le_refl _
      · split
        · exact Nat.le_trans
            (expandBucketCompiledFrom_size t heur id node _ _ 0 s) (ih _ _)
        · exact ih _ _

theorem expandWordCompiled_getD (t : CompiledTask) (heur : Heuristic)
    (id : Nat) (node : Node) (base : Nat) :
    ∀ (fuel : Nat) (word : UInt64) (s : Search) {j : Nat}, j < s.nodes.size →
      (expandWordCompiled t heur id node base fuel word s).nodes.getD j default =
        s.nodes.getD j default := by
  intro fuel
  induction fuel with
  | zero => intro word s j hj; rfl
  | succ fuel ih =>
      intro word s j hj
      rw [expandWordCompiled]
      split
      · rfl
      · split
        · rw [ih _ _ (Nat.lt_of_lt_of_le hj
              (expandBucketCompiledFrom_size t heur id node _ _ 0 s)),
            expandBucketCompiledFrom_getD t heur id node _ _ 0 s hj]
          simp [Array.getD, hj]
        · rw [ih (word >>> 1) s hj]
          simp [Array.getD, hj]

theorem expandWordsCompiledFrom_size (t : CompiledTask) (heur : Heuristic)
    (id : Nat) (node : Node) :
    ∀ (fuel wordIndex : Nat) (s : Search), s.nodes.size ≤
      (expandWordsCompiledFrom t heur id node fuel wordIndex s).nodes.size := by
  intro fuel
  induction fuel with
  | zero => intro wordIndex s; exact Nat.le_refl _
  | succ fuel ih =>
      intro wordIndex s
      rw [expandWordsCompiledFrom]
      split
      · exact Nat.le_trans
          (expandWordCompiled_size t heur id node _ 64 _ s) (ih (wordIndex + 1) _)
      · exact Nat.le_refl _

theorem expandWordsCompiledFrom_getD (t : CompiledTask) (heur : Heuristic)
    (id : Nat) (node : Node) :
    ∀ (fuel wordIndex : Nat) (s : Search) {j : Nat}, j < s.nodes.size →
      (expandWordsCompiledFrom t heur id node fuel wordIndex s).nodes.getD j default =
        s.nodes.getD j default := by
  intro fuel
  induction fuel with
  | zero => intro wordIndex s j hj; rfl
  | succ fuel ih =>
      intro wordIndex s j hj
      rw [expandWordsCompiledFrom]
      split
      · rw [ih (wordIndex + 1) _ (Nat.lt_of_lt_of_le hj
              (expandWordCompiled_size t heur id node _ 64 _ s)),
            expandWordCompiled_getD t heur id node _ 64 _ s hj]
        simp [Array.getD, hj]
      · rfl

theorem expandWordsCompiledFrom_nodesOK (t : Task) (heur : Heuristic)
    (id : Nat) (node : Node) (hwf : Task.WF t) :
    ∀ (fuel wordIndex : Nat) (s : Search), NodesOK t s.nodes →
      id < s.nodes.size → node = s.nodes.getD id default →
      NodesOK t
        (expandWordsCompiledFrom (compileTaskIdentity t) heur id node fuel wordIndex s).nodes := by
  intro fuel
  induction fuel with
  | zero => intro wordIndex s ok _ _; exact ok
  | succ fuel ih =>
      intro wordIndex s ok hid hnode
      rw [expandWordsCompiledFrom]
      split
      · rename_i hwordIndex
        let word := node.state.words[wordIndex]
        have horiginal : word = node.state.words.getD wordIndex 0 := by
          simp [word, Array.getD, hwordIndex]
        have hbits : ∀ bit, bit < 64 →
            word.toBitVec.getLsbD bit = word.toBitVec.getLsbD (0 + bit) := by simp
        let next := expandWordCompiled (compileTaskIdentity t) heur id node
          (wordIndex * 64) 64 word s
        have ok' : NodesOK t next.nodes := by
          exact expandWordCompiled_nodesOK t heur id node wordIndex word hwf horiginal
            64 0 word s (by omega) hbits ok hid hnode
        have hid' : id < next.nodes.size := by
          exact Nat.lt_of_lt_of_le hid
            (expandWordCompiled_size (compileTaskIdentity t) heur id node
              (wordIndex * 64) 64 word s)
        have hnode' : node = next.nodes.getD id default := by
          rw [expandWordCompiled_getD (compileTaskIdentity t) heur id node
            (wordIndex * 64) 64 word s hid]
          exact hnode
        exact ih (wordIndex + 1) next ok' hid' hnode'
      · exact ok

/-- The complete compiled expansion preserves the logical node-chain invariant. -/
theorem expandCompiled_nodesOK (t : Task) (heur : Heuristic) (id : Nat)
    (node : Node) (s : Search) (hwf : Task.WF t) (ok : NodesOK t s.nodes)
    (hid : id < s.nodes.size) (hnode : node = s.nodes.getD id default) :
    NodesOK t (expandCompiled (compileTaskIdentity t) heur id node s).nodes := by
  rw [expandCompiled]
  let start := { s with expanded := s.expanded + 1 }
  let fallback := (compileSuccessorGenerator t).fallback
  let afterFallback := expandBucketCompiledFrom (compileTaskIdentity t) heur id node
    fallback fallback.size 0 start
  have hids : ∀ i ∈ fallback,
      i < t.ops.size ∧ triggerSatisfied t i node.state = true :=
    fallback_ids_good t node.state
  have ok' : NodesOK t afterFallback.nodes := by
    exact expandBucketCompiledFrom_nodesOK t heur id node fallback hwf hids
      fallback.size 0 start ok hid hnode
  have hid' : id < afterFallback.nodes.size := by
    exact Nat.lt_of_lt_of_le hid
      (expandBucketCompiledFrom_size (compileTaskIdentity t) heur id node fallback
        fallback.size 0 start)
  have hnode' : node = afterFallback.nodes.getD id default := by
    rw [expandBucketCompiledFrom_getD (compileTaskIdentity t) heur id node fallback
      fallback.size 0 start hid]
    exact hnode
  exact expandWordsCompiledFrom_nodesOK t heur id node hwf node.state.words.size 0
    afterFallback ok' hid' hnode'

@[simp] theorem traceExpansionCheckpoint_eq (interval : Nat) (s : Search) :
    traceExpansionCheckpoint interval s = s := by
  simp only [traceExpansionCheckpoint]
  split
  · change (match dbgTrace s!"Expansion checkpoint: {s.expanded} state(s)."
        (fun _ => ()) with | () => s) = s
    generalize (dbgTrace s!"Expansion checkpoint: {s.expanded} state(s)."
      (fun _ => ()) : Unit) = traced
    cases traced
    rfl
  · rfl

/-- Every solved compiled-loop outcome is a real logical plan. -/
theorem loopCompiled_sound (t : Task) (heur : Heuristic) (hwf : Task.WF t)
    (checkpointInterval : Option Nat) :
    ∀ (fuel : Nat) (s : Search), NodesOK t s.nodes →
      ∀ plan cost,
        (loopCompiled (compileTaskIdentity t) heur checkpointInterval fuel s).outcome =
          .solved plan cost →
        ∃ final, Executes t.model t.init plan.toList final ∧ t.isGoal final = true ∧
          planCost t.model plan.toList = cost := by
  intro fuel
  induction fuel with
  | zero => intro s _ plan cost h; simp [loopCompiled] at h
  | succ fuel ih =>
      intro s ok plan cost h
      rw [loopCompiled] at h
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
            · rename_i hgoal
              obtain ⟨hplan, hcost⟩ :=
                ok.planTo_valid entry.node hlt (s.nodes.size + 1) (by omega)
              have hp : plan = extractPlan s.nodes entry.node :=
                (by simpa [Outcome.planOf] using congrArg Outcome.planOf h : _ = plan).symm
              have hc : cost = node.g :=
                (by simpa [Outcome.costOf] using congrArg Outcome.costOf h : _ = cost).symm
              refine ⟨node.state, ?_, ?_, ?_⟩
              · rw [hp, extractPlan, hget]
                exact hplan
              · exact hgoal
              · rw [hp, extractPlan, hc, hget]
                exact hcost
            · have ok' := expandCompiled_nodesOK t heur entry.node node
                  { s with openList := rest } hwf ok hlt hget
              cases checkpointInterval with
              | none => exact ih _ ok' plan cost h
              | some interval =>
                  simp only at h
                  rw [traceExpansionCheckpoint_eq] at h
                  exact ih _ ok' plan cost h

/-- Any plan printed by the production compiled A* is executable and reaches the goal. -/
theorem astarCompiled_sound (t : Task) (heur : Heuristic) (hwf : Task.WF t)
    (fuel : Nat) (checkpointInterval : Option Nat := none)
    {plan : Array Nat} {cost : Nat}
    (h : (astarCompiled t heur fuel checkpointInterval).outcome = .solved plan cost) :
    ∃ final, Executes t.model t.init plan.toList final ∧ t.isGoal final = true ∧
      planCost t.model plan.toList = cost := by
  have ok : NodesOK t #[Node.root t] := by
    refine ⟨by simp, ?_, ?_, ?_⟩
    · simp [Array.getD_eq_getD_getElem?, Node.root]
    · intro j hj hpos
      simp at hj
      omega
    · intro j hj hpos
      simp at hj
      omega
  rw [astarCompiled] at h
  split at h <;>
    exact loopCompiled_sound t heur hwf checkpointInterval fuel _ ok plan cost h

/-! ### Monotonicity of the duplicate table -/

theorem expandApplicableCompiled_improves (t : CompiledTask) (heur : Heuristic)
    (id i : Nat) (node : Node) (s : Search) :
    Improves s (expandApplicableCompiled t heur id i node s) := by
  simp only [expandApplicableCompiled]
  split
  · split
    · rename_i previous hprevious hlt
      apply record_improves
      intro g₀ hg₀
      have hprevious' :
          s.best[((t.ops.getD i default).apply node.state)]? = some previous := hprevious
      rw [hprevious'] at hg₀
      simp only [Option.some.injEq] at hg₀
      omega
    · exact Improves.refl _
  · rename_i hnone
    apply record_improves
    intro g₀ hg₀
    have hnone' : s.best[((t.ops.getD i default).apply node.state)]? = none := hnone
    rw [hnone'] at hg₀
    simp at hg₀

theorem expandCandidateCompiled_improves (t : CompiledTask) (heur : Heuristic)
    (id i : Nat) (node : Node) (s : Search) :
    Improves s (expandCandidateCompiled t heur id i node s) := by
  simp only [expandCandidateCompiled]
  split
  · exact expandApplicableCompiled_improves t heur id i node s
  · exact Improves.refl _

theorem expandBucketCompiledFrom_improves (t : CompiledTask) (heur : Heuristic)
    (id : Nat) (node : Node) (ids : Array Nat) :
    ∀ (fuel pos : Nat) (s : Search),
      Improves s (expandBucketCompiledFrom t heur id node ids fuel pos s) := by
  intro fuel
  induction fuel with
  | zero => intro pos s; exact Improves.refl _
  | succ fuel ih =>
      intro pos s
      rw [expandBucketCompiledFrom]
      split
      · exact (expandCandidateCompiled_improves t heur id _ node s).trans (ih (pos + 1) _)
      · exact Improves.refl _

theorem expandWordCompiled_improves (t : CompiledTask) (heur : Heuristic)
    (id : Nat) (node : Node) (base : Nat) :
    ∀ (fuel : Nat) (word : UInt64) (s : Search),
      Improves s (expandWordCompiled t heur id node base fuel word s) := by
  intro fuel
  induction fuel with
  | zero => intro word s; exact Improves.refl _
  | succ fuel ih =>
      intro word s
      rw [expandWordCompiled]
      split
      · exact Improves.refl _
      · split
        · exact (expandBucketCompiledFrom_improves t heur id node _ _ 0 s).trans (ih _ _)
        · exact ih _ _

theorem expandWordsCompiledFrom_improves (t : CompiledTask) (heur : Heuristic)
    (id : Nat) (node : Node) :
    ∀ (fuel wordIndex : Nat) (s : Search),
      Improves s (expandWordsCompiledFrom t heur id node fuel wordIndex s) := by
  intro fuel
  induction fuel with
  | zero => intro wordIndex s; exact Improves.refl _
  | succ fuel ih =>
      intro wordIndex s
      rw [expandWordsCompiledFrom]
      split
      · exact (expandWordCompiled_improves t heur id node _ 64 _ s).trans
          (ih (wordIndex + 1) _)
      · exact Improves.refl _

theorem expandCompiled_improves (t : CompiledTask) (heur : Heuristic)
    (id : Nat) (node : Node) (s : Search) :
    Improves s (expandCompiled t heur id node s) := by
  rw [expandCompiled]
  have hstart : Improves s { s with expanded := s.expanded + 1 } :=
    fun σ g h => ⟨g, h, Nat.le_refl _⟩
  exact hstart.trans
    ((expandBucketCompiledFrom_improves t heur id node t.successors.fallback
      t.successors.fallback.size 0 _).trans
      (expandWordsCompiledFrom_improves t heur id node node.state.words.size 0 _))

/-! ### Recording every candidate reached by the packed traversal -/

/-- Processing a compiled operator records its successor at no more than its new path cost. -/
theorem expandApplicableCompiled_records (t : CompiledTask) (heur : Heuristic)
    (id i : Nat) (node : Node) (s : Search) :
    ∃ g', (expandApplicableCompiled t heur id i node s).best[
        (t.ops.getD i default).apply node.state]? = some g' ∧
      g' ≤ node.g + (t.ops.getD i default).logical.cost := by
  simp only [expandApplicableCompiled]
  split
  · rename_i previous hprevious
    split
    · exact ⟨_, record_best _ _ _ _ _ _, Nat.le_refl _⟩
    · rename_i hge
      exact ⟨previous, hprevious, by omega⟩
  · exact ⟨_, record_best _ _ _ _ _ _, Nat.le_refl _⟩

/-- A candidate whose shortened precondition passes records its compiled successor. -/
theorem expandCandidateCompiled_records (t : CompiledTask) (heur : Heuristic)
    (id i : Nat) (node : Node) (s : Search)
    (hpass : ((t.ops.getD i default).remainingPre.isEmpty ||
      (t.ops.getD i default).applicable node.state) = true) :
    ∃ g', (expandCandidateCompiled t heur id i node s).best[
        (t.ops.getD i default).apply node.state]? = some g' ∧
      g' ≤ node.g + (t.ops.getD i default).logical.cost := by
  simp only [expandCandidateCompiled]
  rw [if_pos hpass]
  exact expandApplicableCompiled_records t heur id i node s

/-- Sweeping a bucket reaches every position inside the requested slice. -/
theorem expandBucketCompiledFrom_records (t : CompiledTask) (heur : Heuristic)
    (id : Nat) (node : Node) (ids : Array Nat) :
    ∀ (fuel pos : Nat) (s : Search) (target : Nat),
      target < ids.size → pos ≤ target → target < pos + fuel →
      (((t.ops.getD (ids.getD target 0) default).remainingPre.isEmpty ||
        (t.ops.getD (ids.getD target 0) default).applicable node.state) = true) →
      ∃ g', (expandBucketCompiledFrom t heur id node ids fuel pos s).best[
          (t.ops.getD (ids.getD target 0) default).apply node.state]? = some g' ∧
        g' ≤ node.g + (t.ops.getD (ids.getD target 0) default).logical.cost := by
  intro fuel
  induction fuel with
  | zero => intro pos s target _ _ hlt _; omega
  | succ fuel ih =>
      intro pos s target htarget hpos hfuel hpass
      rw [expandBucketCompiledFrom]
      have hwithin : pos < ids.size := by omega
      rw [if_pos hwithin]
      rcases Nat.eq_or_lt_of_le hpos with rfl | hnext
      · have hrecord := expandCandidateCompiled_records t heur id (ids.getD pos 0) node s hpass
        obtain ⟨g', hg', hle⟩ := hrecord
        obtain ⟨g'', hg'', hle'⟩ :=
          expandBucketCompiledFrom_improves t heur id node ids fuel (pos + 1)
            (expandCandidateCompiled t heur id (ids.getD pos 0) node s) _ g' hg'
        exact ⟨g'', hg'', Nat.le_trans hle' hle⟩
      · exact ih (pos + 1)
          (expandCandidateCompiled t heur id (ids.getD pos 0) node s) target
          htarget hnext (by omega) hpass

/-- The packed word loop reaches every set bit and sweeps its entire fact bucket. -/
theorem expandWordCompiled_records (t : CompiledTask) (heur : Heuristic)
    (id : Nat) (node : Node) (base : Nat) :
    ∀ (fuel : Nat) (word : UInt64) (s : Search) (target targetPos i : Nat),
      fuel ≤ 64 → target < fuel → word.toBitVec.getLsbD target = true →
      targetPos < (t.successors.byFact.getD (base + (64 - fuel + target)) #[]).size →
      (t.successors.byFact.getD (base + (64 - fuel + target)) #[]).getD targetPos 0 = i →
      (((t.ops.getD i default).remainingPre.isEmpty ||
        (t.ops.getD i default).applicable node.state) = true) →
      ∃ g', (expandWordCompiled t heur id node base fuel word s).best[
          (t.ops.getD i default).apply node.state]? = some g' ∧
        g' ≤ node.g + (t.ops.getD i default).logical.cost := by
  intro fuel
  induction fuel with
  | zero => intro word s target targetPos i _ htarget; omega
  | succ fuel ih =>
      intro word s target targetPos i hfuel htarget hbit htargetPos htargetId hpass
      rw [expandWordCompiled]
      have hword : word ≠ 0 := by
        intro hzero
        subst word
        simp at hbit
      rw [if_neg (by simpa using hword)]
      rcases target with _ | target
      · have hlsb : (word &&& 1 != 0) = true := lsb_of_bit_zero hbit
        simp only [hlsb, if_true]
        let ids := t.successors.byFact.getD (base + (64 - (fuel + 1))) #[]
        have hsize : targetPos < ids.size := by simpa [ids] using htargetPos
        have hid : ids.getD targetPos 0 = i := by simpa [ids] using htargetId
        have hrecord := expandBucketCompiledFrom_records t heur id node ids ids.size 0 s
          targetPos hsize (Nat.zero_le _) (by omega)
        rw [hid] at hrecord
        obtain ⟨g', hg', hle⟩ := hrecord hpass
        obtain ⟨g'', hg'', hle'⟩ :=
          expandWordCompiled_improves t heur id node base fuel (word >>> 1)
            (expandBucketCompiledFrom t heur id node ids ids.size 0 s) _ g' hg'
        exact ⟨g'', hg'', Nat.le_trans hle' hle⟩
      · have hshift : (word >>> 1).toBitVec.getLsbD target = true := by
          rw [bit_shift_one]
          exact hbit
        have hfact : base + (64 - (fuel + 1) + (target + 1)) =
            base + (64 - fuel + target) := by omega
        rw [hfact] at htargetPos htargetId
        by_cases hlsb : (word &&& 1 != 0) = true
        · simp only [hlsb, if_true]
          exact ih (word >>> 1)
            (expandBucketCompiledFrom t heur id node
              (t.successors.byFact.getD (base + (64 - (fuel + 1))) #[])
              (t.successors.byFact.getD (base + (64 - (fuel + 1))) #[]).size 0 s)
            target targetPos i (by omega) (by omega) hshift htargetPos htargetId hpass
        · have hlsbFalse : (word &&& 1 != 0) = false := Bool.eq_false_of_not_eq_true hlsb
          simp only [hlsbFalse, if_false]
          exact ih (word >>> 1) s target targetPos i (by omega) (by omega)
            hshift htargetPos htargetId hpass

/-- The outer packed-state loop reaches every in-range word and every set bit in it. -/
theorem expandWordsCompiledFrom_records (t : CompiledTask) (heur : Heuristic)
    (id : Nat) (node : Node) :
    ∀ (fuel wordIndex : Nat) (s : Search) (targetWord targetBit targetPos i : Nat),
      targetWord < node.state.words.size → wordIndex ≤ targetWord →
      targetWord < wordIndex + fuel → targetBit < 64 →
      (node.state.words.getD targetWord 0).toBitVec.getLsbD targetBit = true →
      targetPos <
        (t.successors.byFact.getD (targetWord * 64 + targetBit) #[]).size →
      (t.successors.byFact.getD (targetWord * 64 + targetBit) #[]).getD targetPos 0 = i →
      (((t.ops.getD i default).remainingPre.isEmpty ||
        (t.ops.getD i default).applicable node.state) = true) →
      ∃ g', (expandWordsCompiledFrom t heur id node fuel wordIndex s).best[
          (t.ops.getD i default).apply node.state]? = some g' ∧
        g' ≤ node.g + (t.ops.getD i default).logical.cost := by
  intro fuel
  induction fuel with
  | zero => intro wordIndex s targetWord targetBit targetPos i _ _ hlt; omega
  | succ fuel ih =>
      intro wordIndex s targetWord targetBit targetPos i htargetWord hwordIndex hfuel
        htargetBit hbit htargetPos htargetId hpass
      rw [expandWordsCompiledFrom]
      have hwithin : wordIndex < node.state.words.size := by omega
      rw [if_pos hwithin]
      rcases Nat.eq_or_lt_of_le hwordIndex with rfl | hnext
      · have hrecord := expandWordCompiled_records t heur id node (wordIndex * 64)
          64 (node.state.words.getD wordIndex 0) s targetBit targetPos i
          (by omega) htargetBit hbit
        have hbase : wordIndex * 64 + (64 - 64 + targetBit) =
            wordIndex * 64 + targetBit := by omega
        rw [hbase] at hrecord
        obtain ⟨g', hg', hle⟩ := hrecord htargetPos htargetId hpass
        obtain ⟨g'', hg'', hle'⟩ :=
          expandWordsCompiledFrom_improves t heur id node fuel (wordIndex + 1)
            (expandWordCompiled t heur id node (wordIndex * 64) 64
              (node.state.words.getD wordIndex 0) s) _ g' hg'
        exact ⟨g'', hg'', Nat.le_trans hle' hle⟩
      · exact ih (wordIndex + 1)
          (expandWordCompiled t heur id node (wordIndex * 64) 64
            (node.state.words.getD wordIndex 0) s)
          targetWord targetBit targetPos i htargetWord hnext (by omega) htargetBit
          hbit htargetPos htargetId hpass

/-- A complete packed expansion records every applicable logical successor. -/
theorem expandCompiled_records (t : Task) (heur : Heuristic) (id i : Nat)
    (node : Node) (s : Search) (hwf : Task.WF t) (hstate : State.WF t.numFacts node.state)
    (hi : i < t.ops.size) (happ : t.ops[i].applicable node.state = true) :
    ∃ g', (expandCompiled (compileTaskIdentity t) heur id node s).best[
        t.ops[i].apply node.state]? = some g' ∧ g' ≤ node.g + t.ops[i].cost := by
  let ct := compileTaskIdentity t
  let start := { s with expanded := s.expanded + 1 }
  let fallback := ct.successors.fallback
  let afterFallback :=
    expandBucketCompiledFrom ct heur id node fallback fallback.size 0 start
  let cop := ct.ops[i]'(by simpa [ct] using hi)
  have hget : ct.ops.getD i default = cop := by
    simp [Array.getD, hi, ct, cop]
  have hlogical : cop.logical = t.ops[i] := by
    simpa [ct, cop] using compileTaskIdentity_op_logical t hi
  cases htrigger : operatorTrigger? t i with
  | none =>
      have himem : i ∈ fallback := by
        exact SuccessorGenerator.mem_fallback.mpr ⟨hi, htrigger⟩
      obtain ⟨targetPos, htargetPos, htargetId⟩ := Array.getElem_of_mem himem
      have htargetId' : fallback.getD targetPos 0 = i := by
        simp [Array.getD, htargetPos, htargetId]
      have htriggerSat : triggerSatisfied t i node.state = true := by
        simp [triggerSatisfied, htrigger]
      have hcapp : cop.applicable node.state = true := by
        rw [compileTaskIdentity_op_applicable t node.state hi htriggerSat]
        exact happ
      have hpass : (cop.remainingPre.isEmpty || cop.applicable node.state) = true := by
        simp [hcapp]
      have hrecord := expandBucketCompiledFrom_records ct heur id node fallback
        fallback.size 0 start targetPos htargetPos (Nat.zero_le _) (by omega)
      rw [htargetId', hget] at hrecord
      obtain ⟨g', hg', hle⟩ := hrecord hpass
      obtain ⟨g'', hg'', hle'⟩ :=
        expandWordsCompiledFrom_improves ct heur id node node.state.words.size 0
          afterFallback _ g' (by simpa [afterFallback] using hg')
      rw [expandCompiled]
      change ∃ g',
        (expandWordsCompiledFrom ct heur id node node.state.words.size 0 afterFallback).best[
            t.ops[i].apply node.state]? = some g' ∧ g' ≤ node.g + t.ops[i].cost
      have happly : cop.apply node.state = t.ops[i].apply node.state := by
        simpa [ct, cop] using compileTaskIdentity_op_apply t node.state hwf hi hstate
      rw [happly] at hg''
      rw [hlogical] at hle
      exact ⟨g'', hg'', Nat.le_trans hle' hle⟩
  | some f =>
      obtain ⟨hf, hpre⟩ := SuccessorGenerator.trigger_precondition hi htrigger
      have htrue : node.state.test f = true := (Op.applicable_iff.mp happ) f hpre
      have himem : i ∈ ct.successors.byFact.getD f #[] := by
        exact SuccessorGenerator.mem_byFact hf |>.mpr ⟨hi, htrigger⟩
      obtain ⟨targetPos, htargetPos, htargetId⟩ := Array.getElem_of_mem himem
      have htargetId' : (ct.successors.byFact.getD f #[]).getD targetPos 0 = i := by
        rw [OpenList.getD_eq_getElem _ _ _ htargetPos, htargetId]
      have htriggerSat : triggerSatisfied t i node.state = true := by
        simpa [triggerSatisfied, htrigger] using htrue
      have hcapp : cop.applicable node.state = true := by
        rw [compileTaskIdentity_op_applicable t node.state hi htriggerSat]
        exact happ
      have hpass : (cop.remainingPre.isEmpty || cop.applicable node.state) = true := by
        simp [hcapp]
      let targetWord := f >>> 6
      let targetBit := f &&& 63
      have htargetBit : targetBit < 64 := State.mask_lt f
      have hparts : targetWord * 64 + targetBit = f := by
        simp only [targetWord, targetBit, State.shift_eq, State.mask_eq]
        rw [Nat.mul_comm]
        exact Nat.div_add_mod f 64
      have htargetWord : targetWord < node.state.words.size := State.lt_words hstate hf
      have hbit : (node.state.words.getD targetWord 0).toBitVec.getLsbD targetBit = true := by
        rw [← State.test_word_bit node.state targetWord targetBit htargetBit, hparts]
        exact htrue
      have hrecord := expandWordsCompiledFrom_records ct heur id node
        node.state.words.size 0 afterFallback targetWord targetBit targetPos i
        htargetWord (Nat.zero_le _) (by simpa using htargetWord) htargetBit hbit
      rw [hparts] at hrecord
      rw [htargetId', hget] at hrecord
      obtain ⟨g', hg', hle⟩ := hrecord htargetPos rfl hpass
      rw [expandCompiled]
      change ∃ g',
        (expandWordsCompiledFrom ct heur id node node.state.words.size 0 afterFallback).best[
            t.ops[i].apply node.state]? = some g' ∧ g' ≤ node.g + t.ops[i].cost
      have happly : cop.apply node.state = t.ops[i].apply node.state := by
        simpa [ct, cop] using compileTaskIdentity_op_apply t node.state hwf hi hstate
      rw [happly] at hg'
      rw [hlogical] at hle
      exact ⟨g', hg', hle⟩

/-! ### One compositional contract for frontier maintenance -/

/-- Everything the A* invariants need from a sequence of `record` operations. -/
structure SearchExtension (heur : Heuristic) (before after : Search) : Prop where
  improves : Improves before after
  openMono : ∀ e, before.openList.Mem e → after.openList.Mem e
  nodeMono : ∀ (j : Nat) (k : Node), before.nodes[j]? = some k → after.nodes[j]? = some k
  newOpen : ∀ {sigma : State} {g : Nat}, after.best[sigma]? = some g →
    heur.eval sigma < deadEnd → before.best[sigma]? = some g ∨ OpenFor heur after sigma g
  entryOK : EntryOK heur before → EntryOK heur after
  queueWF : before.openList.WF → after.openList.WF

namespace SearchExtension

theorem refl (heur : Heuristic) (s : Search) : SearchExtension heur s s :=
  ⟨Improves.refl _, fun _ h => h, fun _ _ h => h, fun h _ => Or.inl h,
    fun h => h, fun h => h⟩

theorem trans {heur : Heuristic} {a b c : Search}
    (hab : SearchExtension heur a b) (hbc : SearchExtension heur b c) :
    SearchExtension heur a c := by
  refine ⟨hab.improves.trans hbc.improves,
    fun e h => hbc.openMono e (hab.openMono e h),
    fun j k h => hbc.nodeMono j k (hab.nodeMono j k h), ?_,
    fun h => hbc.entryOK (hab.entryOK h), fun h => hbc.queueWF (hab.queueWF h)⟩
  intro sigma g hbest hlt
  rcases hbc.newOpen hbest hlt with hbest' | hopen
  · rcases hab.newOpen hbest' hlt with hbest'' | hopen'
    · exact Or.inl hbest''
    · exact Or.inr (hopen'.mono hbc.openMono hbc.nodeMono)
  · exact Or.inr hopen

end SearchExtension

private theorem record_extension (heur : Heuristic) (id i : Nat) (succ : State) (g : Nat)
    (s : Search) (hnew : ∀ g₀, s.best[succ]? = some g₀ → g < g₀) :
    SearchExtension heur s (record heur id i succ g s) := by
  obtain ⟨hopen, hnodes⟩ := record_mono heur id i succ g s
  refine ⟨record_improves heur id i succ g s (fun g₀ h => by have := hnew g₀ h; omega),
    hopen, hnodes, ?_, record_entryOK heur id i succ g s, record_wf heur id i succ g s⟩
  intro sigma g' hbest hlt
  exact record_openFor_of_best heur id i succ g s hbest hlt

private theorem generated_extension (heur : Heuristic) (s : Search) :
    SearchExtension heur s { s with generated := s.generated + 1 } :=
  ⟨Improves.refl _, fun _ h => h, fun _ _ h => h, fun h _ => Or.inl h,
    fun h => h, fun h => h⟩

private theorem expanded_extension (heur : Heuristic) (s : Search) :
    SearchExtension heur s { s with expanded := s.expanded + 1 } :=
  ⟨Improves.refl _, fun _ h => h, fun _ _ h => h, fun h _ => Or.inl h,
    fun h => h, fun h => h⟩

theorem expandApplicableCompiled_extension (t : CompiledTask) (heur : Heuristic)
    (id i : Nat) (node : Node) (s : Search) :
    SearchExtension heur s (expandApplicableCompiled t heur id i node s) := by
  simp only [expandApplicableCompiled]
  split
  · rename_i previous hprevious
    split
    · rename_i hlt
      apply record_extension
      intro g₀ hg₀
      have hp : s.best[((t.ops.getD i default).apply node.state)]? = some previous := hprevious
      rw [hp] at hg₀
      simp only [Option.some.injEq] at hg₀
      omega
    · exact generated_extension heur s
  · rename_i hnone
    apply record_extension
    intro g₀ hg₀
    have hn : s.best[((t.ops.getD i default).apply node.state)]? = none := hnone
    rw [hn] at hg₀
    simp at hg₀

theorem expandCandidateCompiled_extension (t : CompiledTask) (heur : Heuristic)
    (id i : Nat) (node : Node) (s : Search) :
    SearchExtension heur s (expandCandidateCompiled t heur id i node s) := by
  simp only [expandCandidateCompiled]
  split
  · exact expandApplicableCompiled_extension t heur id i node s
  · exact SearchExtension.refl heur s

theorem expandBucketCompiledFrom_extension (t : CompiledTask) (heur : Heuristic)
    (id : Nat) (node : Node) (ids : Array Nat) :
    ∀ (fuel pos : Nat) (s : Search),
      SearchExtension heur s (expandBucketCompiledFrom t heur id node ids fuel pos s) := by
  intro fuel
  induction fuel with
  | zero => intro pos s; exact SearchExtension.refl heur s
  | succ fuel ih =>
      intro pos s
      rw [expandBucketCompiledFrom]
      split
      · exact (expandCandidateCompiled_extension t heur id _ node s).trans (ih (pos + 1) _)
      · exact SearchExtension.refl heur s

theorem expandWordCompiled_extension (t : CompiledTask) (heur : Heuristic)
    (id : Nat) (node : Node) (base : Nat) :
    ∀ (fuel : Nat) (word : UInt64) (s : Search),
      SearchExtension heur s (expandWordCompiled t heur id node base fuel word s) := by
  intro fuel
  induction fuel with
  | zero => intro word s; exact SearchExtension.refl heur s
  | succ fuel ih =>
      intro word s
      rw [expandWordCompiled]
      split
      · exact SearchExtension.refl heur s
      · split
        · exact (expandBucketCompiledFrom_extension t heur id node _ _ 0 s).trans (ih _ _)
        · exact ih _ _

theorem expandWordsCompiledFrom_extension (t : CompiledTask) (heur : Heuristic)
    (id : Nat) (node : Node) :
    ∀ (fuel wordIndex : Nat) (s : Search),
      SearchExtension heur s (expandWordsCompiledFrom t heur id node fuel wordIndex s) := by
  intro fuel
  induction fuel with
  | zero => intro wordIndex s; exact SearchExtension.refl heur s
  | succ fuel ih =>
      intro wordIndex s
      rw [expandWordsCompiledFrom]
      split
      · exact (expandWordCompiled_extension t heur id node _ 64 _ s).trans
          (ih (wordIndex + 1) _)
      · exact SearchExtension.refl heur s

theorem expandCompiled_extension (t : CompiledTask) (heur : Heuristic)
    (id : Nat) (node : Node) (s : Search) :
    SearchExtension heur s (expandCompiled t heur id node s) := by
  rw [expandCompiled]
  exact (expanded_extension heur s).trans
    ((expandBucketCompiledFrom_extension t heur id node t.successors.fallback
      t.successors.fallback.size 0 _).trans
      (expandWordsCompiledFrom_extension t heur id node node.state.words.size 0 _))

/-- Expanding a node with the packed engine relaxes every logical successor. -/
theorem expandCompiled_relaxed (t : Task) (heur : Heuristic) (id : Nat)
    (node : Node) (s : Search) (hwf : Task.WF t)
    (hstate : State.WF t.numFacts node.state) :
    Relaxed t (expandCompiled (compileTaskIdentity t) heur id node s) node.state node.g := by
  intro op hop happ
  obtain ⟨i, hi, hiop⟩ := Array.getElem_of_mem hop
  subst hiop
  exact expandCompiled_records t heur id i node s hwf hstate hi happ

theorem frontier_expand_compiled (t : Task) (heur : Heuristic) (s : Search)
    {entry : Entry} {rest : OpenList} (hq : s.openList.WF)
    (hpop : s.openList.pop? = some (entry, rest))
    {node : Node} (hnode : s.nodes[entry.node]? = some node)
    (hwf : Task.WF t) (hstate : State.WF t.numFacts node.state)
    (hF : Frontier t heur s) :
    Frontier t heur
      (expandCompiled (compileTaskIdentity t) heur entry.node node { s with openList := rest }) := by
  intro sigma g hbest hlt
  let base := { s with openList := rest }
  let ext := expandCompiled_extension (compileTaskIdentity t) heur entry.node node base
  have hdrop : Improves s base := fun _ g' h => ⟨g', h, Nat.le_refl _⟩
  rcases ext.newOpen hbest hlt with hold | hopen
  · rcases hF sigma g hold hlt with ⟨e, hmem, hf, k, hk, hkstate, hkg⟩ | hrel
    · by_cases hne : e.node = entry.node
      · have hknode : k = node := by
          rw [hne, hnode] at hk
          simpa using hk.symm
        subst hknode
        refine Or.inr ?_
        rw [← hkstate, ← hkg]
        exact expandCompiled_relaxed t heur entry.node k base hwf hstate
      · obtain ⟨-, -, hsurv, -⟩ := OpenList.pop?_spec hq hpop
        have hopenBase : OpenFor heur base sigma g :=
          ⟨e, hsurv e hmem hne, hf, k, hk, hkstate, hkg⟩
        exact Or.inl (hopenBase.mono ext.openMono ext.nodeMono)
    · exact Or.inr (hrel.mono (hdrop.trans ext.improves))
  · exact Or.inl hopen

theorem goalsOpen_expand_compiled (t : Task) (heur : Heuristic) (s : Search)
    {entry : Entry} {rest : OpenList} (hq : s.openList.WF)
    (hpop : s.openList.pop? = some (entry, rest))
    {node : Node} (hnode : s.nodes[entry.node]? = some node)
    (hnotgoal : t.isGoal node.state = false) (hG : GoalsOpen t heur s) :
    GoalsOpen t heur
      (expandCompiled (compileTaskIdentity t) heur entry.node node { s with openList := rest }) := by
  intro sigma g hbest hgoal hlt
  let base := { s with openList := rest }
  let ext := expandCompiled_extension (compileTaskIdentity t) heur entry.node node base
  rcases ext.newOpen hbest hlt with hold | hopen
  · obtain ⟨e, hmem, hf, k, hk, hkstate, hkg⟩ := hG sigma g hold hgoal hlt
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
    have hopenBase : OpenFor heur base sigma g :=
      ⟨e, hsurv e hmem hne, hf, k, hk, hkstate, hkg⟩
    exact hopenBase.mono ext.openMono ext.nodeMono
  · exact hopen

/-! ### Optimality and completeness of the single production loop -/

theorem loopCompiled_optimal (t : Task) (heur : Heuristic) (P : State → Prop)
    (hwf : Task.WF t) (hP : Invariant t.model P) (hPinit : P t.init)
    (hga : GoalAware t.model P heur.eval) (hadm : Admissible t.model P heur.eval)
    (checkpointInterval : Option Nat) :
    ∀ (fuel : Nat) (s : Search), NodesOK t s.nodes → s.openList.WF →
      Frontier t heur s → GoalsOpen t heur s → EntryOK heur s →
      s.best[t.init]? = some 0 →
      ∀ {plan : Array Nat} {cost : Nat},
        (loopCompiled (compileTaskIdentity t) heur checkpointInterval fuel s).outcome =
          .solved plan cost →
        ∀ (pl : List Nat) (final : State), Executes t.model t.init pl final →
          t.model.isGoal final → planCost t.model pl < deadEnd →
          cost ≤ planCost t.model pl := by
  intro fuel
  induction fuel with
  | zero => intro s _ _ _ _ _ _ plan cost hout; simp [loopCompiled] at hout
  | succ fuel ih =>
      intro s ok hq hF hG hE hinit plan cost hout pl final hexec hgoal hlive
      rw [loopCompiled] at hout
      split at hout
      · simp at hout
      · rename_i entry rest hpop
        obtain ⟨hentryMem, hmin, hsurv, hwfQueue'⟩ := OpenList.pop?_spec hq hpop
        have hrestE : EntryOK heur { s with openList := rest } :=
          fun e he => hE e (OpenList.pop?_mem_mono hpop e he)
        split at hout
        · rename_i hnone
          have hdrop : ∀ k, s.nodes[entry.node]? = some k →
              s.best[k.state]? ≠ some k.g := by
            intro k hk
            rw [hnone] at hk
            simp at hk
          exact ih { s with openList := rest } ok hwfQueue'
            (frontier_discard t heur s hq hpop hF hdrop)
            (goalsOpen_discard t heur s hq hpop hG hdrop) hrestE hinit hout
            pl final hexec hgoal hlive
        · rename_i node hnode
          have hnodeLt : entry.node < s.nodes.size :=
            Array.getElem?_eq_some_iff.mp hnode |>.1
          have hget : node = s.nodes.getD entry.node default := by
            rw [Array.getD_eq_getD_getElem?, hnode]
            rfl
          have hstate : State.WF t.numFacts node.state := by
            rw [hget]
            exact NodesOK.states_wf hwf ok entry.node hnodeLt
          split at hout
          · rename_i hstale
            have hdrop : ∀ k, s.nodes[entry.node]? = some k →
                s.best[k.state]? ≠ some k.g := by
              intro k hk hcon
              rw [hnode] at hk
              have hkn : k = node := by simpa using hk.symm
              subst hkn
              rw [Std.HashMap.getD_eq_getD_getElem?, hcon] at hstale
              simp at hstale
            exact ih { s with openList := rest } ok hwfQueue'
              (frontier_discard t heur s hq hpop hF hdrop)
              (goalsOpen_discard t heur s hq hpop hG hdrop) hrestE hinit hout
              pl final hexec hgoal hlive
          · split at hout
            · rename_i hgoalNode
              have hc : cost = node.g :=
                (by simpa [Outcome.costOf] using congrArg Outcome.costOf hout : _ = cost).symm
              have hPfinal : P final := invariant_executes hP hPinit hexec
              have hzero : heur.eval final = 0 := hga final hPfinal hgoal
              have hopen : ∃ e, s.openList.Mem e ∧ e.f ≤ planCost t.model pl := by
                rcases frontier_bound t heur P hP hga hadm hF hexec hinit hPinit hgoal
                    (by omega) with ⟨e, hmem, hb⟩ | ⟨g', hg', hb⟩
                · exact ⟨e, hmem, by omega⟩
                · obtain ⟨e, hmem, hf, -⟩ :=
                    hG final g' hg' (by simpa using hgoal)
                      (by rw [hzero]; decide)
                  exact ⟨e, hmem, by omega⟩
              obtain ⟨e, hmem, hb⟩ := hopen
              obtain ⟨k, hk, hfk⟩ := hE entry hentryMem
              rw [hnode] at hk
              have hkn : k = node := by simpa using hk.symm
              subst hkn
              have hle := hmin e hmem
              omega
            · rename_i hnotgoal
              let base := { s with openList := rest }
              let next := expandCompiled (compileTaskIdentity t) heur entry.node node base
              let ext := expandCompiled_extension (compileTaskIdentity t) heur entry.node node base
              have ok' : NodesOK t next.nodes :=
                expandCompiled_nodesOK t heur entry.node node base hwf ok hnodeLt hget
              have hF' : Frontier t heur next :=
                frontier_expand_compiled t heur s hq hpop hnode hwf hstate hF
              have hG' : GoalsOpen t heur next :=
                goalsOpen_expand_compiled t heur s hq hpop hnode
                  (by simpa [compileTaskIdentity_isGoal] using hnotgoal) hG
              have hE' : EntryOK heur next := ext.entryOK hrestE
              have hq' : next.openList.WF := ext.queueWF hwfQueue'
              have hinit' : next.best[t.init]? = some 0 :=
                init_stays base next t ext.improves hinit
              cases checkpointInterval with
              | none =>
                  exact ih next ok' hq' hF' hG' hE' hinit' hout
                    pl final hexec hgoal hlive
              | some interval =>
                  simp only at hout
                  rw [traceExpansionCheckpoint_eq] at hout
                  exact ih next ok' hq' hF' hG' hE' hinit' hout
                    pl final hexec hgoal hlive

private theorem best_init_only_capacity {capacity : Nat} {t : Task} {sigma : State} {g : Nat}
    (hb : ((Std.HashMap.emptyWithCapacity capacity : Std.HashMap State Nat).insert
      t.init 0)[sigma]? = some g) : sigma = t.init ∧ g = 0 := by
  by_cases hsigma : sigma = t.init
  · refine ⟨hsigma, ?_⟩
    rw [hsigma] at hb
    simp at hb
    omega
  · exfalso
    rw [Std.HashMap.getElem?_insert,
      if_neg (by simpa using fun h => hsigma h.symm)] at hb
    simp at hb

private theorem nodesOK_root (t : Task) : NodesOK t #[Node.root t] := by
  refine ⟨by simp, ?_, ?_, ?_⟩
  · simp [Array.getD_eq_getD_getElem?, Node.root]
  · intro j hj hpos
    simp at hj
    omega
  · intro j hj hpos
    simp at hj
    omega

theorem frontier_init_capacity (t : Task) (heur : Heuristic) (capacity : Nat) :
    Frontier t heur
      { openList := OpenList.empty.push
          { f := heur.eval t.init, h := heur.eval t.init, node := 0 }
        nodes := #[Node.root t]
        best := (Std.HashMap.emptyWithCapacity capacity : Std.HashMap State Nat).insert
          t.init 0
        expanded := 0, generated := 0, evaluated := 1, pruned := 0 } := by
  intro sigma g hbest _
  obtain ⟨hsigma, hg⟩ := best_init_only_capacity hbest
  subst hg
  refine Or.inl ⟨{ f := heur.eval t.init, h := heur.eval t.init, node := 0 },
    OpenList.push_mem_self _ _, ?_, Node.root t, ?_, hsigma.symm, rfl⟩
  · show heur.eval t.init = 0 + heur.eval sigma
    rw [hsigma, Nat.zero_add]
  · show (#[Node.root t] : Array Node)[0]? = some (Node.root t)
    simp

theorem goalsOpen_init_capacity (t : Task) (heur : Heuristic) (capacity : Nat) :
    GoalsOpen t heur
      { openList := OpenList.empty.push
          { f := heur.eval t.init, h := heur.eval t.init, node := 0 }
        nodes := #[Node.root t]
        best := (Std.HashMap.emptyWithCapacity capacity : Std.HashMap State Nat).insert
          t.init 0
        expanded := 0, generated := 0, evaluated := 1, pruned := 0 } := by
  intro sigma g hbest _ _
  obtain ⟨hsigma, hg⟩ := best_init_only_capacity hbest
  subst hg
  refine ⟨{ f := heur.eval t.init, h := heur.eval t.init, node := 0 },
    OpenList.push_mem_self _ _, ?_, Node.root t, ?_, hsigma.symm, rfl⟩
  · show heur.eval t.init = 0 + heur.eval sigma
    rw [hsigma, Nat.zero_add]
  · show (#[Node.root t] : Array Node)[0]? = some (Node.root t)
    simp

theorem entryOK_init_capacity (t : Task) (heur : Heuristic) (capacity : Nat) :
    EntryOK heur
      { openList := OpenList.empty.push
          { f := heur.eval t.init, h := heur.eval t.init, node := 0 }
        nodes := #[Node.root t]
        best := (Std.HashMap.emptyWithCapacity capacity : Std.HashMap State Nat).insert
          t.init 0
        expanded := 0, generated := 0, evaluated := 1, pruned := 0 } := by
  intro e he
  rcases OpenList.mem_push he with hold | ⟨hf, -, hnode⟩
  · exact absurd hold (OpenList.not_mem_empty e)
  · refine ⟨Node.root t, ?_, ?_⟩
    · rw [hnode]
      show (#[Node.root t] : Array Node)[0]? = some (Node.root t)
      simp
    · rw [hf]
      simp [Node.root]

/-- The single production A* returns an optimal plan under the common heuristic contract. -/
theorem astarCompiled_optimal (t : Task) (heur : Heuristic) (P : State → Prop)
    (hwf : Task.WF t) (hP : Invariant t.model P) (hPinit : P t.init)
    (hga : GoalAware t.model P heur.eval) (hadm : Admissible t.model P heur.eval)
    (fuel : Nat) (checkpointInterval : Option Nat := none)
    {plan : Array Nat} {cost : Nat}
    (hout : (astarCompiled t heur fuel checkpointInterval).outcome = .solved plan cost)
    (pl : List Nat) (final : State) (hexec : Executes t.model t.init pl final)
    (hgoal : t.model.isGoal final) (hlive : planCost t.model pl < deadEnd) :
    cost ≤ planCost t.model pl := by
  let start : Search :=
    { openList := OpenList.empty
      nodes := #[Node.root t]
      best := (Std.HashMap.emptyWithCapacity 1048576 : Std.HashMap State Nat).insert
        t.init 0
      expanded := 0, generated := 0, evaluated := 1, pruned := 0 }
  have hbest : start.best[t.init]? = some 0 := by simp [start]
  rw [astarCompiled] at hout
  split at hout
  · rename_i hdead
    have hdead' : deadEnd ≤ heur.eval t.init := by
      simpa [Node.root] using hdead
    refine loopCompiled_optimal t heur P hwf hP hPinit hga hadm checkpointInterval fuel
      { start with pruned := 1 } (nodesOK_root t) OpenList.empty_wf ?_ ?_ ?_ hbest
      hout pl final hexec hgoal hlive
    · intro sigma g hb hlt
      rw [(best_init_only_capacity hb).1] at hlt
      omega
    · intro sigma g hb _ hlt
      rw [(best_init_only_capacity hb).1] at hlt
      omega
    · intro e he
      exact absurd he (OpenList.not_mem_empty e)
  · exact loopCompiled_optimal t heur P hwf hP hPinit hga hadm checkpointInterval fuel _
      (nodesOK_root t) (OpenList.push_wf OpenList.empty_wf _)
      (frontier_init_capacity t heur 1048576) (goalsOpen_init_capacity t heur 1048576)
      (entryOK_init_capacity t heur 1048576) hbest hout pl final hexec hgoal hlive

theorem loopCompiled_complete (t : Task) (heur : Heuristic) (P : State → Prop)
    (hwf : Task.WF t) (hP : Invariant t.model P) (hPinit : P t.init)
    (hga : GoalAware t.model P heur.eval) (hadm : Admissible t.model P heur.eval)
    (checkpointInterval : Option Nat) :
    ∀ (fuel : Nat) (s : Search), NodesOK t s.nodes → s.openList.WF →
      Frontier t heur s → GoalsOpen t heur s → EntryOK heur s →
      s.best[t.init]? = some 0 →
      (loopCompiled (compileTaskIdentity t) heur checkpointInterval fuel s).outcome =
        .unsolvable →
      ∀ (pl : List Nat) (final : State), Executes t.model t.init pl final →
        t.model.isGoal final → deadEnd ≤ planCost t.model pl := by
  intro fuel
  induction fuel with
  | zero => intro s _ _ _ _ _ _ hout; simp [loopCompiled] at hout
  | succ fuel ih =>
      intro s ok hq hF hG hE hinit hout pl final hexec hgoal
      by_contra hcon
      push Not at hcon
      rw [loopCompiled] at hout
      split at hout
      · rename_i hpopnone
        have hno : ∀ e, ¬ s.openList.Mem e := OpenList.pop?_none hq hpopnone
        have hPfinal : P final := invariant_executes hP hPinit hexec
        have hzero : heur.eval final = 0 := hga final hPfinal hgoal
        rcases frontier_bound t heur P hP hga hadm hF hexec hinit hPinit hgoal
            (by omega) with ⟨e, hmem, -⟩ | ⟨g', hg', -⟩
        · exact hno e hmem
        · obtain ⟨e, hmem, -⟩ :=
            hG final g' hg' (by simpa using hgoal) (by rw [hzero]; decide)
          exact hno e hmem
      · rename_i entry rest hpop
        obtain ⟨-, -, -, hwfQueue'⟩ := OpenList.pop?_spec hq hpop
        have hrestE : EntryOK heur { s with openList := rest } :=
          fun e he => hE e (OpenList.pop?_mem_mono hpop e he)
        split at hout
        · rename_i hnone
          have hdrop : ∀ k, s.nodes[entry.node]? = some k →
              s.best[k.state]? ≠ some k.g := by
            intro k hk
            rw [hnone] at hk
            simp at hk
          exact absurd (ih { s with openList := rest } ok hwfQueue'
            (frontier_discard t heur s hq hpop hF hdrop)
            (goalsOpen_discard t heur s hq hpop hG hdrop) hrestE hinit hout
            pl final hexec hgoal) (by omega)
        · rename_i node hnode
          have hnodeLt : entry.node < s.nodes.size :=
            Array.getElem?_eq_some_iff.mp hnode |>.1
          have hget : node = s.nodes.getD entry.node default := by
            rw [Array.getD_eq_getD_getElem?, hnode]
            rfl
          have hstate : State.WF t.numFacts node.state := by
            rw [hget]
            exact NodesOK.states_wf hwf ok entry.node hnodeLt
          split at hout
          · rename_i hstale
            have hdrop : ∀ k, s.nodes[entry.node]? = some k →
                s.best[k.state]? ≠ some k.g := by
              intro k hk hcon2
              rw [hnode] at hk
              have hkn : k = node := by simpa using hk.symm
              subst hkn
              rw [Std.HashMap.getD_eq_getD_getElem?, hcon2] at hstale
              simp at hstale
            exact absurd (ih { s with openList := rest } ok hwfQueue'
              (frontier_discard t heur s hq hpop hF hdrop)
              (goalsOpen_discard t heur s hq hpop hG hdrop) hrestE hinit hout
              pl final hexec hgoal) (by omega)
          · split at hout
            · simp at hout
            · rename_i hnotgoal
              let base := { s with openList := rest }
              let next := expandCompiled (compileTaskIdentity t) heur entry.node node base
              let ext := expandCompiled_extension (compileTaskIdentity t) heur entry.node node base
              have ok' : NodesOK t next.nodes :=
                expandCompiled_nodesOK t heur entry.node node base hwf ok hnodeLt hget
              have hF' : Frontier t heur next :=
                frontier_expand_compiled t heur s hq hpop hnode hwf hstate hF
              have hG' : GoalsOpen t heur next :=
                goalsOpen_expand_compiled t heur s hq hpop hnode
                  (by simpa [compileTaskIdentity_isGoal] using hnotgoal) hG
              have hE' : EntryOK heur next := ext.entryOK hrestE
              have hq' : next.openList.WF := ext.queueWF hwfQueue'
              have hinit' : next.best[t.init]? = some 0 :=
                init_stays base next t ext.improves hinit
              cases checkpointInterval with
              | none =>
                  exact absurd (ih next ok' hq' hF' hG' hE' hinit' hout
                    pl final hexec hgoal) (by omega)
              | some interval =>
                  simp only at hout
                  rw [traceExpansionCheckpoint_eq] at hout
                  exact absurd (ih next ok' hq' hF' hG' hE' hinit' hout
                    pl final hexec hgoal) (by omega)

/-- An `unsolvable` result from the production A* rules out every cheap plan. -/
theorem astarCompiled_complete (t : Task) (heur : Heuristic) (P : State → Prop)
    (hwf : Task.WF t) (hP : Invariant t.model P) (hPinit : P t.init)
    (hga : GoalAware t.model P heur.eval) (hadm : Admissible t.model P heur.eval)
    (fuel : Nat) (checkpointInterval : Option Nat := none)
    (hout : (astarCompiled t heur fuel checkpointInterval).outcome = .unsolvable)
    (pl : List Nat) (final : State) (hexec : Executes t.model t.init pl final)
    (hgoal : t.model.isGoal final) : deadEnd ≤ planCost t.model pl := by
  let start : Search :=
    { openList := OpenList.empty
      nodes := #[Node.root t]
      best := (Std.HashMap.emptyWithCapacity 1048576 : Std.HashMap State Nat).insert
        t.init 0
      expanded := 0, generated := 0, evaluated := 1, pruned := 0 }
  have hbest : start.best[t.init]? = some 0 := by simp [start]
  rw [astarCompiled] at hout
  split at hout
  · rename_i hdead
    refine loopCompiled_complete t heur P hwf hP hPinit hga hadm checkpointInterval fuel
      { start with pruned := 1 } (nodesOK_root t) OpenList.empty_wf ?_ ?_ ?_ hbest
      hout pl final hexec hgoal
    · intro sigma g hb hlt
      have hdead' : deadEnd ≤ heur.eval t.init := by simpa [Node.root] using hdead
      rw [(best_init_only_capacity hb).1] at hlt
      omega
    · intro sigma g hb _ hlt
      have hdead' : deadEnd ≤ heur.eval t.init := by simpa [Node.root] using hdead
      rw [(best_init_only_capacity hb).1] at hlt
      omega
    · intro e he
      exact absurd he (OpenList.not_mem_empty e)
  · exact loopCompiled_complete t heur P hwf hP hPinit hga hadm checkpointInterval fuel _
      (nodesOK_root t) (OpenList.push_wf OpenList.empty_wf _)
      (frontier_init_capacity t heur 1048576) (goalsOpen_init_capacity t heur 1048576)
      (entryOK_init_capacity t heur 1048576) hbest hout pl final hexec hgoal

/-- Once the production loop finishes, extra fuel cannot change its result. -/
theorem loopCompiled_mono (t : CompiledTask) (heur : Heuristic)
    (checkpointInterval : Option Nat) :
    ∀ (fuel k : Nat) (s : Search),
      (loopCompiled t heur checkpointInterval fuel s).outcome ≠ .outOfFuel →
      loopCompiled t heur checkpointInterval (fuel + k) s =
        loopCompiled t heur checkpointInterval fuel s := by
  intro fuel
  induction fuel with
  | zero => intro k s h; simp [loopCompiled] at h
  | succ fuel ih =>
      intro k s h
      rw [show fuel + 1 + k = (fuel + k) + 1 by omega, loopCompiled, loopCompiled]
      rw [loopCompiled] at h
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
                  cases checkpointInterval with
                  | none => exact ih k _ h
                  | some interval =>
                      simp only [traceExpansionCheckpoint_eq] at h ⊢
                      exact ih k _ h

/-- Whenever the production A* finishes, adding fuel returns the identical result. -/
theorem astarCompiled_mono (t : Task) (heur : Heuristic) (fuel k : Nat)
    (checkpointInterval : Option Nat := none)
    (h : (astarCompiled t heur fuel checkpointInterval).outcome ≠ .outOfFuel) :
    astarCompiled t heur (fuel + k) checkpointInterval =
      astarCompiled t heur fuel checkpointInterval := by
  simp only [astarCompiled] at h ⊢
  split
  · rename_i hd
    simp only [if_pos hd] at h
    exact loopCompiled_mono _ _ checkpointInterval fuel k _ h
  · rename_i hd
    simp only [if_neg hd] at h
    exact loopCompiled_mono _ _ checkpointInterval fuel k _ h

end Planner
