/-
The identity compiled-task boundary preserves the exact logical task.  These
lemmas are the initial simulation contract; later compiler passes extend this
file rather than changing the certificate-facing `Task` semantics.
-/
import Proofs.Search.SuccessorGenerator
import Proofs.GroundingCorrect
import Planner.CompiledTask

namespace Planner

@[simp] theorem compileTaskIdentity_source (t : Task) :
    (compileTaskIdentity t).source = t := rfl

@[simp] theorem compileTaskIdentity_init (t : Task) :
    (compileTaskIdentity t).init = t.init := rfl

@[simp] theorem compileTaskIdentity_goal (t : Task) :
    (compileTaskIdentity t).goal = t.goal := rfl

@[simp] theorem compileTaskIdentity_ops_size (t : Task) :
    (compileTaskIdentity t).ops.size = t.ops.size := by
  simp [compileTaskIdentity]

@[simp] theorem compileTaskIdentity_successors (t : Task) :
    (compileTaskIdentity t).successors = compileSuccessorGenerator t := rfl

theorem compileTaskIdentity_isGoal (t : Task) (s : State) :
    (compileTaskIdentity t).isGoal s = t.isGoal s := by
  rfl

theorem compileTaskIdentity_sourceOp (t : Task) (i : Nat) :
    (compileTaskIdentity t).sourceOp? i = t.ops[i]? := by
  rfl

theorem compileTaskIdentity_op_sourceId (t : Task) {i : Nat} (hi : i < t.ops.size) :
    ((compileTaskIdentity t).ops[i]'(by simpa using hi)).sourceId = i := by
  simp [compileTaskIdentity, hi]

theorem compileTaskIdentity_op_logical (t : Task) {i : Nat} (hi : i < t.ops.size) :
    ((compileTaskIdentity t).ops[i]'(by simpa using hi)).logical = t.ops[i] := by
  simp [compileTaskIdentity, hi]

theorem compileTaskIdentity_op_remainingPre (t : Task) {i : Nat} (hi : i < t.ops.size) :
    ((compileTaskIdentity t).ops[i]'(by simpa using hi)).remainingPre =
      match operatorTrigger? t i with
      | some trigger => t.ops[i].pre.filter (· != trigger)
      | none => t.ops[i].pre := by
  simp [compileTaskIdentity, hi]
  rfl

private theorem holdsAll_filter_known (s : State) (facts : Array Fact) (trigger : Fact)
    (htrigger : s.test trigger = true) :
    s.holdsAll (facts.filter (· != trigger)) = s.holdsAll facts := by
  refine Bool.eq_iff_iff.mpr ?_
  simp only [State.holdsAll, ← Array.all_toList, List.all_eq_true]
  constructor
  · intro h f hf
    by_cases hft : f = trigger
    · simpa [hft] using htrigger
    · apply h f
      have haf : f ∈ facts.filter (· != trigger) :=
        Array.mem_filter.mpr ⟨by simpa using hf, by simp [hft]⟩
      simpa using haf
  · intro h f hf
    apply h f
    have haf : f ∈ facts.filter (· != trigger) := by simpa using hf
    simpa using (Array.mem_filter.mp haf).1

/-- Once its trigger is known true, the shortened compiled precondition is exact. -/
theorem compileTaskIdentity_op_applicable (t : Task) (s : State) {i : Nat}
    (hi : i < t.ops.size) (htrigger : triggerSatisfied t i s = true) :
    ((compileTaskIdentity t).ops[i]'(by simpa using hi)).applicable s =
      t.ops[i].applicable s := by
  rw [CompiledOp.applicable, Op.applicable,
    compileTaskIdentity_op_remainingPre t hi]
  cases htrig : operatorTrigger? t i with
  | none => rfl
  | some trigger =>
      have htrue : s.test trigger = true := by
        simpa [triggerSatisfied, htrig] using htrigger
      exact holdsAll_filter_known s t.ops[i].pre trigger htrue

private theorem effect_apply_size (effect : EffectWord) (words : Array UInt64) :
    (effect.apply words).size = words.size := by
  simp [EffectWord.apply]

private theorem effect_apply_getD_same (effect : EffectWord) (words : Array UInt64)
    (hi : effect.index < words.size) :
    (effect.apply words).getD effect.index 0 =
      ((words.getD effect.index 0 &&& ~~~effect.del) ||| effect.add) := by
  simp [EffectWord.apply, Array.getD_eq_getD_getElem?, hi]

private theorem effect_apply_getD_other (effect : EffectWord) (words : Array UInt64)
    {i : Nat} (hne : i ≠ effect.index) :
    (effect.apply words).getD i 0 = words.getD i 0 := by
  simp [EffectWord.apply, Array.getD_eq_getD_getElem?, hne, Ne.symm hne]

private theorem foldl_effects_size (effects : List EffectWord) (words : Array UInt64) :
    (effects.foldl (fun words effect => effect.apply words) words).size = words.size := by
  induction effects generalizing words with
  | nil => rfl
  | cons effect rest ih =>
      rw [List.foldl_cons, ih, effect_apply_size]

private theorem foldl_effects_getD_none (effects : List EffectWord) (words : Array UInt64)
    {i : Nat} (hnone : ∀ effect ∈ effects, effect.index ≠ i) :
    (effects.foldl (fun words effect => effect.apply words) words).getD i 0 =
      words.getD i 0 := by
  induction effects generalizing words with
  | nil => rfl
  | cons effect rest ih =>
      rw [List.foldl_cons, ih]
      · exact effect_apply_getD_other effect words (Ne.symm (hnone effect (by simp)))
      · intro other hmem
        exact hnone other (by simp [hmem])

private theorem foldl_effects_getD_mem (effects : List EffectWord) (words : Array UInt64)
    (hnodup : (effects.map EffectWord.index).Nodup) (effect : EffectWord)
    (hmem : effect ∈ effects) (hi : effect.index < words.size) :
    (effects.foldl (fun words effect => effect.apply words) words).getD effect.index 0 =
      ((words.getD effect.index 0 &&& ~~~effect.del) ||| effect.add) := by
  induction effects generalizing words with
  | nil => simp at hmem
  | cons head rest ih =>
      simp only [List.foldl_cons]
      have hhead : head.index ∉ rest.map EffectWord.index := (List.nodup_cons.mp hnodup).1
      have hrest : (rest.map EffectWord.index).Nodup := (List.nodup_cons.mp hnodup).2
      rcases List.mem_cons.mp hmem with rfl | htail
      · rw [foldl_effects_getD_none rest (EffectWord.apply effect words)]
        · exact effect_apply_getD_same effect words hi
        · intro other hother heq
          exact hhead (List.mem_map.mpr ⟨other, hother, heq⟩)
      · have hne : effect.index ≠ head.index := by
          intro heq
          exact hhead (List.mem_map.mpr ⟨effect, htail, heq⟩)
        rw [ih (EffectWord.apply head words) hrest htail]
        · rw [effect_apply_getD_other head words hne]
        · rw [effect_apply_size]
          exact hi

private theorem compileEffectWord?_eq_some_index {addMask delMask : State}
    {index : Nat} {effect : EffectWord}
    (h : compileEffectWord? addMask delMask index = some effect) :
    effect.index = index := by
  simp only [compileEffectWord?] at h
  split at h
  · simp at h
  · exact (congrArg EffectWord.index (Option.some.inj h)).symm

private theorem compileEffectWords_indices_nodup (numFacts : Nat)
    (add del : Array Fact) :
    (((compileEffectWords numFacts add del).toList).map EffectWord.index).Nodup := by
  let addMask := State.ofFacts numFacts add
  let delMask := State.ofFacts numFacts del
  let emit := compileEffectWord? addMask delMask
  have hsource : ∀ {index : Nat} {effect : EffectWord},
      emit index = some effect → effect.index = index := by
    intro index effect h
    exact compileEffectWord?_eq_some_index h
  have hout : (List.filterMap emit (List.range (State.wordsFor numFacts))).Nodup := by
    apply List.Nodup.filterMap _ List.nodup_range
    intro i j effect hi hj
    have hii : effect.index = i := hsource (by simpa using hi)
    have hjj : effect.index = j := hsource (by simpa using hj)
    omega
  have hmap := hout.map_on (f := EffectWord.index) (by
    intro a ha b hb hab
    obtain ⟨i, hi, hia⟩ := List.mem_filterMap.mp ha
    obtain ⟨j, hj, hjb⟩ := List.mem_filterMap.mp hb
    have hij : i = j := by
      rw [← hsource hia, ← hsource hjb]
      exact hab
    subst j
    rw [hia] at hjb
    exact Option.some.inj hjb)
  simpa [compileEffectWords, addMask, delMask, emit] using hmap

private theorem compileEffectWords_getD (numFacts : Nat) (add del : Array Fact)
    (words : Array UInt64) (hsize : words.size = State.wordsFor numFacts)
    {index : Nat} (hi : index < State.wordsFor numFacts) :
    ((compileEffectWords numFacts add del).foldl
      (fun words effect => effect.apply words) words).getD index 0 =
      ((words.getD index 0 &&&
          ~~~(State.ofFacts numFacts del).words.getD index 0) |||
        (State.ofFacts numFacts add).words.getD index 0) := by
  let addMask := State.ofFacts numFacts add
  let delMask := State.ofFacts numFacts del
  let addWord := addMask.words.getD index 0
  let delWord := delMask.words.getD index 0
  by_cases hzero : addWord == 0 && delWord == 0
  · have hz := Bool.and_eq_true_iff.mp hzero
    have haddZero : addWord = 0 := eq_of_beq hz.1
    have hdelZero : delWord = 0 := eq_of_beq hz.2
    rw [← Array.foldl_toList,
      foldl_effects_getD_none (compileEffectWords numFacts add del).toList words]
    · simp [addMask, delMask, addWord, delWord, haddZero, hdelZero]
    · intro effect hmem heq
      have harr : effect ∈ compileEffectWords numFacts add del := by simpa using hmem
      rw [compileEffectWords] at harr
      obtain ⟨source, hsource, hemit⟩ := Array.mem_filterMap.mp harr
      have hsourceIndex : effect.index = source := compileEffectWord?_eq_some_index hemit
      have hsi : source = index := by omega
      subst source
      simp [compileEffectWord?, heq, addMask, delMask, addWord, delWord,
        haddZero, hdelZero] at hemit
  · let effect : EffectWord := { index, add := addWord, del := delWord }
    have hemit : compileEffectWord? addMask delMask index = some effect := by
      simp only [compileEffectWord?]
      rw [if_neg hzero]
    have hmem : effect ∈ (compileEffectWords numFacts add del).toList := by
      have : effect ∈ compileEffectWords numFacts add del := by
        apply Array.mem_filterMap.mpr
        refine ⟨index, by simp [hi], ?_⟩
        simpa [addMask, delMask] using hemit
      simpa using this
    rw [← Array.foldl_toList,
      foldl_effects_getD_mem (compileEffectWords numFacts add del).toList words
        (compileEffectWords_indices_nodup numFacts add del) effect hmem
        (by simpa [effect, hsize] using hi)]

private theorem compiled_effects_apply_eq {numFacts : Nat} (op : Op) (s : State)
    (hop : Op.WF numFacts op) (hs : State.WF numFacts s) :
    ({ words := (compileEffectWords numFacts op.add op.del).foldl
        (fun words effect => effect.apply words) s.words } : State) = op.apply s := by
  apply State.ext_test
  · rw [← Array.foldl_toList, foldl_effects_size,
      (Op.wf_apply op hs).size, hs.size]
  · intro f hf
    have hf' : f >>> 6 < s.words.size := by
      simpa only [← Array.foldl_toList, foldl_effects_size] using hf
    have hword : f >>> 6 < State.wordsFor numFacts := by
      rw [← hs.size]
      exact hf'
    have hcompiled := compileEffectWords_getD numFacts op.add op.del s.words hs.size hword
    rw [Op.test_apply hop hs]
    simp only [State.test]
    rw [hcompiled, State.word_test _ _ (State.mask_lt f),
      UInt64.toBitVec_or, BitVec.getLsbD_or,
      UInt64.toBitVec_and, BitVec.getLsbD_and,
      UInt64.toBitVec_not, BitVec.getLsbD_not]
    have hadd := State.test_ofFacts numFacts op.add hop.add f
    have hdel := State.test_ofFacts numFacts op.del hop.del f
    simp only [State.test, State.word_test _ _ (State.mask_lt f)] at hadd hdel
    have hsbit :
        (s.words.getD (f >>> 6) 0).toBitVec.getLsbD (f &&& 63) =
          (s.words.getD (f >>> 6) 0 &&&
            (1 <<< (UInt64.ofNat (f &&& 63))) != 0) := by
      exact (State.word_test _ _ (State.mask_lt f)).symm
    rw [hadd, hdel, hsbit]
    cases ha : op.add.contains f <;> cases hd : op.del.contains f <;>
      simp [State.mask_lt f]

/-- The sparse compiled effect program implements the logical operator exactly. -/
theorem compileTaskIdentity_op_apply (t : Task) (s : State) (hwf : Task.WF t)
    {i : Nat} (hi : i < t.ops.size) (hs : State.WF t.numFacts s) :
    ((compileTaskIdentity t).ops[i]'(by simpa using hi)).apply s = t.ops[i].apply s := by
  rw [CompiledOp.apply]
  have heffects :
      ((compileTaskIdentity t).ops[i]'(by simpa using hi)).effects =
        compileEffectWords t.numFacts t.ops[i].add t.ops[i].del := by
    simp [compileTaskIdentity]
  rw [heffects]
  apply compiled_effects_apply_eq t.ops[i] s
  exact hwf.ops t.ops[i] (by simp [hi])
  exact hs

theorem compileTaskIdentity_applicable_sound (t : Task) (s : State) {i : Nat}
    (hi : i ∈ (compileTaskIdentity t).applicableIds s) :
    i < t.ops.size ∧ (t.ops.getD i default).applicable s = true := by
  exact SuccessorGenerator.applicableIds_sound hi

theorem compileTaskIdentity_applicable_complete (t : Task) (s : State) {i : Nat}
    (hi : i < t.ops.size) (happ : t.ops[i].applicable s = true) :
    i ∈ (compileTaskIdentity t).applicableIds s := by
  exact SuccessorGenerator.applicableIds_complete hi happ

end Planner
