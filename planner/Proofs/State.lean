/-
What the bit-set state representation of `Planner/State.lean` means.

Everything above this file reasons about states through a handful of lemmas —
`test` after `insert`, `test` after `erase`, and the invariance of the word count
— so the packed representation is opened exactly once, here.
-/
import Mathlib.Tactic
import Planner.State

namespace Planner.State

/-! ### Fact numbering -/

theorem shift_eq (f : Fact) : f >>> 6 = f / 64 := by
  simpa using Nat.shiftRight_eq_div_pow f 6

theorem mask_eq (f : Fact) : f &&& 63 = f % 64 := by
  have h : (63 : Nat) = 2 ^ 6 - 1 := by norm_num
  rw [h, Nat.and_two_pow_sub_one_eq_mod]

theorem mask_lt (f : Fact) : f &&& 63 < 64 := by
  rw [mask_eq]; exact Nat.mod_lt _ (by norm_num)

/-- A fact is determined by the word it lives in and the bit it occupies. -/
theorem eq_of_parts {f g : Nat} (hw : f >>> 6 = g >>> 6) (hb : f &&& 63 = g &&& 63) :
    f = g := by
  have h1 : f / 64 = g / 64 := by rw [← shift_eq, ← shift_eq]; exact hw
  have h2 : f % 64 = g % 64 := by rw [← mask_eq, ← mask_eq]; exact hb
  omega

/-! ### One word -/

/-- The mask `1 <<< b` is the `b`-th power of two, for `b` below the word width. -/
theorem mask_toBitVec (b : Nat) (hb : b < 64) :
    ((1 : UInt64) <<< (UInt64.ofNat b)).toBitVec = BitVec.twoPow 64 b := by
  simp [BitVec.twoPow, Nat.mod_eq_of_lt hb]

/-- Masking a word with a single bit is nonzero exactly when that bit is set. -/
theorem word_test (w : UInt64) (b : Nat) (hb : b < 64) :
    (w &&& ((1 : UInt64) <<< (UInt64.ofNat b)) != 0) = w.toBitVec.getLsbD b := by
  have key : (w &&& ((1 : UInt64) <<< (UInt64.ofNat b))).toBitVec
      = if w.toBitVec.getLsbD b then BitVec.twoPow 64 b else 0#64 := by
    simp [mask_toBitVec b hb, BitVec.and_twoPow]
  cases hbit : w.toBitVec.getLsbD b with
  | true =>
      simp only [hbit, if_true] at key
      have hne : w &&& ((1 : UInt64) <<< (UInt64.ofNat b)) ≠ 0 := by
        intro h
        rw [h] at key
        have hb' : ((0 : UInt64).toBitVec).getLsbD b = (BitVec.twoPow 64 b).getLsbD b := by
          rw [key]
        simp [hb] at hb'
      simp [hne]
  | false =>
      simp only [hbit] at key
      have heq : w &&& ((1 : UInt64) <<< (UInt64.ofNat b)) = 0 :=
        UInt64.toBitVec_inj.mp (by simpa using key)
      simp [heq]

/-! ### Word counts -/

@[simp] theorem size_insert (s : State) (f : Fact) :
    (s.insert f).words.size = s.words.size := by
  simp [insert]

@[simp] theorem size_erase (s : State) (f : Fact) :
    (s.erase f).words.size = s.words.size := by
  simp [erase]

/-! ### Reading a fact after a write -/

private theorem getD_setIfInBounds (a : Array UInt64) (i j : Nat) (v : UInt64)
    (hi : i < a.size) :
    (a.setIfInBounds i v).getD j 0 = if j = i then v else a.getD j 0 := by
  by_cases hj : j = i
  · subst hj; simp [Array.getD_eq_getD_getElem?, hi]
  · simp [Array.getD_eq_getD_getElem?, hj, Ne.symm hj]

/-- `test` reads the bit that `insert` writes, and leaves every other bit alone. -/
theorem test_insert (s : State) (f g : Fact) (hg : g >>> 6 < s.words.size) :
    (s.insert g).test f = (decide (f = g) || s.test f) := by
  simp only [insert, test, getD_setIfInBounds _ _ _ _ hg]
  by_cases hword : f >>> 6 = g >>> 6
  · rw [if_pos hword, hword, word_test _ _ (mask_lt f), word_test _ _ (mask_lt f),
      UInt64.toBitVec_or, BitVec.getLsbD_or, mask_toBitVec _ (mask_lt g),
      BitVec.getLsbD_twoPow]
    by_cases hbit : f &&& 63 = g &&& 63
    · have hfg : f = g := eq_of_parts hword hbit
      simp [hfg, mask_lt g]
    · have hne : f ≠ g := fun h => hbit (by rw [h])
      have hbit' : ¬ (g &&& 63 = f &&& 63) := fun h => hbit h.symm
      simp [hne, hbit']
  · rw [if_neg hword]
    have hne : f ≠ g := fun h => hword (by rw [h])
    simp [hne]

/-- `test` reads the bit that `erase` clears, and leaves every other bit alone. -/
theorem test_erase (s : State) (f g : Fact) (hg : g >>> 6 < s.words.size) :
    (s.erase g).test f = (!decide (f = g) && s.test f) := by
  simp only [erase, test, getD_setIfInBounds _ _ _ _ hg]
  by_cases hword : f >>> 6 = g >>> 6
  · rw [if_pos hword, hword, word_test _ _ (mask_lt f), word_test _ _ (mask_lt f),
      UInt64.toBitVec_and, BitVec.getLsbD_and, UInt64.toBitVec_not, BitVec.getLsbD_not,
      mask_toBitVec _ (mask_lt g), BitVec.getLsbD_twoPow]
    by_cases hbit : f &&& 63 = g &&& 63
    · have hfg : f = g := eq_of_parts hword hbit
      simp [hfg, mask_lt g]
    · have hne : f ≠ g := fun h => hbit (by rw [h])
      have hbit' : ¬ (g &&& 63 = f &&& 63) := fun h => hbit h.symm
      simp [hne, mask_lt f, hbit']
  · rw [if_neg hword]
    have hne : f ≠ g := fun h => hword (by rw [h])
    simp [hne]

end Planner.State
