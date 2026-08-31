/-
States as packed bit sets.

A grounded task numbers its facts `0 .. numFacts-1`; a state is the set of facts
that hold, stored as `⌈numFacts / 64⌉` machine words.  This is the single data
structure the search loop touches per node, so it is deliberately tiny: a state is
one array, comparison is one array comparison, and a successor is one array copy
followed by in-place bit updates (Lean updates arrays in place when the reference
is unique, which it is inside `applyOp`).
-/

namespace Planner

/-- A fact is an index into the task's fact table. -/
abbrev Fact := Nat

/-- A state: bit `f` of word `f / 64` is set exactly when fact `f` holds. -/
structure State where
  words : Array UInt64
  deriving Inhabited

/-- Equality is word-by-word.  Spelled out rather than derived so that the
`LawfulBEq` instance below — which the closed list's `HashMap` lemmas need — can
be proved directly. -/
instance : BEq State := ⟨fun a b => a.words == b.words⟩

instance : LawfulBEq State where
  eq_of_beq {a b} h := by
    cases a with | mk wa => cases b with | mk wb =>
    have : wa = wb := eq_of_beq h
    simp [this]
  rfl {a} := by
    cases a with | mk w =>
    show (w == w) = true
    simp

namespace State

/-- Number of 64-bit words needed to hold `numFacts` facts. -/
@[inline] def wordsFor (numFacts : Nat) : Nat := (numFacts + 63) / 64

/-- The state in which no fact holds. -/
@[inline] def empty (numFacts : Nat) : State :=
  { words := Array.replicate (wordsFor numFacts) 0 }

@[inline] def test (s : State) (f : Fact) : Bool :=
  (s.words.getD (f >>> 6) 0 &&& (1 <<< (UInt64.ofNat (f &&& 63)))) != 0

@[inline] def insert (s : State) (f : Fact) : State :=
  let i := f >>> 6
  { words := s.words.setIfInBounds i (s.words.getD i 0 ||| (1 <<< (UInt64.ofNat (f &&& 63)))) }

@[inline] def erase (s : State) (f : Fact) : State :=
  let i := f >>> 6
  { words := s.words.setIfInBounds i (s.words.getD i 0 &&& ~~~(1 <<< (UInt64.ofNat (f &&& 63)))) }

/-- Whether every fact in `facts` holds in `s`. -/
@[inline] def holdsAll (s : State) (facts : Array Fact) : Bool :=
  facts.all s.test

/-- Build a state from a list of facts that hold. -/
def ofFacts (numFacts : Nat) (facts : Array Fact) : State :=
  facts.foldl (init := empty numFacts) fun s f => s.insert f

/-- The facts that hold, in increasing order.  Used only for output and tests. -/
def toFacts (s : State) (numFacts : Nat) : Array Fact := Id.run do
  let mut out := #[]
  for f in [0:numFacts] do
    if s.test f then out := out.push f
  return out

/-- FNV-1a over the words.  Cheap and adequate for the closed-list hash map. -/
def hash (s : State) : UInt64 :=
  s.words.foldl (init := 1469598103934665603) fun h w =>
    (h ^^^ w) * 1099511628211

instance : Hashable State := ⟨State.hash⟩

end State

end Planner
