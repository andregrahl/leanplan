/-
Blocks World, improved heuristic.

The classic *must-move* analysis.  A block has to be moved when

  * its goal support is not in place — the goal wants `on b c` or `on-table b`
    and it does not hold; or
  * it is in the hand, and so has to be put down before anything else is grabbed; or
  * it sits on a block that itself has to move; or
  * it sits on a block the goal wants clear, or wants a *different* block on.

The `holding` case is not redundant.  Every IPC instance fixes a goal support for
every block, so a held block is always caught by the first case there; an instance
whose goal leaves a block's support open is caught only by this one, and without
it the count drops by two across a single `unstack` — see `Proofs/Domains/
Blocksworld/Improved.lean`.

That set is a least fixed point: the base cases above, closed upwards along the
current towers, since everything stacked on a block that must move must come off
first.  It is read off the other way round, by walking *down* from each block to
see whether anything at or below it is a base case, because that is the form the
consistency argument inducts on.

Blocks that must move split in two:

  * those with an unmet goal support (`MG`) need a grab — `pickup` or `unstack` —
    *and* a place — `putdown` or `stack` — because only a place can establish
    `on` or `on-table`;
  * the rest (`MO`) only have to get out of the way, so they need a grab, and a
    place too unless they are the one block left in the hand at the end.

So grabs are at least `|MG| + |MO|`, one fewer if the arm already holds a block
that must move, and places are at least `|MG| + |MO|`, one fewer if anything in
`MO` may stay in the hand.

Some blocks have to be moved *twice*, and that is where the remaining slack was.
A block has to go somewhere temporary when its own destination is not ready and
it is sitting in the way of making it ready: its goal support `b` still has to
move, and the block is either in the hand already, or standing on some block that
the goal wants underneath it — so it must get out of the way before `b` can be
put where it belongs, and only then can it come back.  Each such block costs one
extra grab and one extra place.

The count is taken together with the unmet `clear` goals, which no single action
can advance by more than one either, and the larger of the two wins.
-/
import Planner.ExampleHeuristics.Base

namespace Planner.ExampleHeuristics.Blocksworld

open Planner.Pddl

/-- What the heuristic needs to know about one block. -/
structure BlockInfo where
  /-- The facts `on(block, c)`, with `c`'s index. -/
  onFacts : Array (Fact × Nat)
  /-- The fact `on-table(block)`. -/
  onTableFact : Option Fact
  /-- The fact `holding(block)`. -/
  holdingFact : Option Fact
  /-- The goal fact `on(block, c)` with `c`, if the goal fixes a support. -/
  goalOn : Option (Fact × Nat)
  /-- The goal fact `on-table(block)`, if the goal fixes it. -/
  goalOnTable : Option Fact
  /-- Whether the goal wants this block clear. -/
  goalClear : Bool
  /-- The block the goal wants directly on this one, if any. -/
  goalCarries : Option Nat
  deriving Inhabited

structure Data where
  blocks : Array BlockInfo
  /-- The goal facts of the `clear` family. -/
  clearGoals : Array Fact
  deriving Inhabited

/-! ### The per-block table builders

Named so that the proofs can read one entry at a time; `compile` just maps
`blockInfoOf` over the object list.
-/

/-- The fact whose atom is `pred(b)` for the single argument `b`, if listed. -/
def supportFactOf (tbl : Array (Fact × GroundAtom)) (b : Name) : Option Fact :=
  (tbl.find? fun (_, a) => a.args == [b]).map (·.1)

/-- The `on(b, c)` facts of `b`, each paired with `c`'s index in the object list. -/
def onEntriesOf (idx : Name → Option Nat) (b : Name)
    (onFacts : Array (Fact × GroundAtom)) : Array (Fact × Nat) :=
  onFacts.filterMap fun (f, a) =>
    match a.args with
    | [x, c] => if x == b then (idx c).map ((f, ·)) else none
    | _ => none

/-- The goal fact naming atom `a`: its position among the goal atoms, read back
through the task's goal. -/
def goalFactOf (t : Task) (a : GroundAtom) : Option Fact :=
  (t.goalAtoms.zipIdx.find? fun (b, _) => b == a).map fun (_, i) => t.goal.getD i 0

/-- The goal support of `b`: the goal fact `on(b, c)` paired with `c`'s index,
if the goal fixes a support. -/
def goalOnOf (t : Task) (idx : Name → Option Nat) (b : Name)
    (goalOnAtoms : Array GroundAtom) : Option (Fact × Nat) :=
  (goalOnAtoms.find? fun a =>
    match a.args with
    | [x, _] => x == b
    | _ => false).bind fun a =>
      match a.args with
      | [_, c] => do let f ← goalFactOf t a; let ci ← idx c; pure (f, ci)
      | _ => none

/-- The block the goal wants standing on `b`, by index. -/
def goalCarriesOf (idx : Name → Option Nat) (b : Name)
    (goalOnAtoms : Array GroundAtom) : Option Nat :=
  (goalOnAtoms.find? fun a =>
    match a.args with
    | [_, c] => c == b
    | _ => false).bind fun a =>
      match a.args with
      | [x, _] => idx x
      | _ => none

def blockInfoOf (t : Task) (idx : Name → Option Nat) (b : Name)
    (onFacts onTableFacts holdingFacts : Array (Fact × GroundAtom))
    (goalOnAtoms goalTableAtoms goalClearAtoms : Array GroundAtom) : BlockInfo :=
  { onFacts := onEntriesOf idx b onFacts
    onTableFact := supportFactOf onTableFacts b
    holdingFact := supportFactOf holdingFacts b
    goalOn := goalOnOf t idx b goalOnAtoms
    goalOnTable := (goalTableAtoms.find? fun a => a.args == [b]).bind (goalFactOf t)
    goalClear := goalClearAtoms.any fun a => a.args == [b]
    goalCarries := goalCarriesOf idx b goalOnAtoms }

def compile (t : Task) : Data :=
  let names := t.objectNames
  let idx : Name → Option Nat := fun b => names.findIdx? (· == b)
  let onFacts := t.factsWith "on"
  let onTableFacts := t.factsWith "on-table"
  let holdingFacts := t.factsWith "holding"
  let goalOnAtoms := t.goalAtomsWith "on"
  let goalTableAtoms := t.goalAtomsWith "on-table"
  let goalClearAtoms := t.goalAtomsWith "clear"
  { blocks := names.map fun b =>
      blockInfoOf t idx b onFacts onTableFacts holdingFacts
        goalOnAtoms goalTableAtoms goalClearAtoms,
    clearGoals := t.goalFactsWith ["clear"] }

/-- Unmet `clear` goals: one action each, since a single action clears one block. -/
@[inline] def clearBound (d : Data) (s : State) : Nat := countMissing d.clearGoals s

/-! ### The must-move analysis, written for the proofs

Every quantity above is recomputed here as a plain function of the state, with the
fixpoint expressed as a depth-bounded unfolding *downwards*: a block must move
when a block at or below it in its current tower is a seed.  That is the same set
the upward sweep marks, and it is the form the consistency argument can induct on.
-/

/-- The block directly under `b`, read off the state. -/
def supportOf (d : Data) (s : State) (b : Nat) : Option Nat :=
  ((d.blocks.getD b default).onFacts.find? fun (f, _) => s.test f).map (·.2)

/-- Whether the arm is holding `b`. -/
def isHeld (d : Data) (s : State) (b : Nat) : Bool :=
  match (d.blocks.getD b default).holdingFact with
  | some f => s.test f
  | none => false

/-- Whether the goal fixes a support for `b` that does not hold. -/
def supportUnmet (d : Data) (s : State) (b : Nat) : Bool :=
  let info := d.blocks.getD b default
  (match info.goalOn with
   | some (f, _) => !s.test f
   | none => false) ||
  (match info.goalOnTable with
   | some f => !s.test f
   | none => false)

/-- Whether `b` sits on a block the goal wants clear, or wants a different block on. -/
def blocking (d : Data) (s : State) (b : Nat) : Bool :=
  match supportOf d s b with
  | some c =>
      let below := d.blocks.getD c default
      below.goalClear ||
        (match below.goalCarries with
         | some x => x != b
         | none => false)
  | none => false

/-- The base cases: `b` has to move for a reason of its own. -/
def seed (d : Data) (s : State) (b : Nat) : Bool :=
  supportUnmet d s b || blocking d s b || isHeld d s b

/-- The fixpoint, unfolded `k` levels down `b`'s tower. -/
def mustMoveAux (d : Data) (s : State) : Nat → Nat → Bool
  | 0, _ => false
  | k + 1, b =>
      seed d s b ||
        match supportOf d s b with
        | some c => mustMoveAux d s k c
        | none => false

/-- `b` has to move: it is a seed, or it stands on a block that has to move. -/
def mustMove (d : Data) (s : State) (b : Nat) : Bool :=
  mustMoveAux d s (d.blocks.size + 1) b

/-- Does the goal want `target` below `b`, following `b`'s goal tower down `k` levels? -/
def inGoalChainAux (d : Data) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | k + 1, b, target =>
      match (d.blocks.getD b default).goalOn with
      | some (_, next) => next == target || inGoalChainAux d k next target
      | none => false

/-- Does the goal want `target` somewhere below `b`? -/
def inGoalChain (d : Data) (b target : Nat) : Bool :=
  inGoalChainAux d d.blocks.size b target

/-- `b` must be parked somewhere temporary: its destination is not ready and it is
in the way of getting it ready. -/
def detour (d : Data) (s : State) (b : Nat) : Bool :=
  match (d.blocks.getD b default).goalOn with
  | some (_, target) =>
      mustMove d s target &&
        (isHeld d s b ||
          (match supportOf d s b with
           | some sup => inGoalChain d b sup
           | none => false))
  | none => false

/-- The blocks, by index. -/
def blockList (d : Data) : List Nat := List.range d.blocks.size

/-- Blocks that must move and need placing where the goal wants them. -/
def needPlace (d : Data) (s : State) : Nat :=
  (blockList d).countP fun b => mustMove d s b && supportUnmet d s b

/-- Blocks that must move but only have to get out of the way. -/
def needClearing (d : Data) (s : State) : Nat :=
  (blockList d).countP fun b => mustMove d s b && !supportUnmet d s b

/-- One grab is already done when the arm holds a block that must move. -/
def heldNeedsPlace (d : Data) (s : State) : Nat :=
  if (blockList d).any fun b => mustMove d s b && isHeld d s b then 1 else 0

/-- Blocks that must be moved twice. -/
def detours (d : Data) (s : State) : Nat :=
  (blockList d).countP fun b => mustMove d s b && detour d s b

/--
The must-move bound: every block that has to move needs its own grab and its own
place, less the one already in the hand, less the one that may stay in the hand,
plus two per detour.
-/
def moveBound (d : Data) (s : State) : Nat :=
  let m := needPlace d s + needClearing d s
  let grabs := m - heldNeedsPlace d s + detours d s
  let places := m - (if needClearing d s > 0 then 1 else 0) + detours d s
  grabs + places

/-- The larger of the two bounds; both bound the same actions, so they combine with `max`. -/
def value (d : Data) (s : State) : Nat := max (clearBound d s) (moveBound d s)

def improved (t : Task) : Heuristic :=
  let d := compile t
  { name := "blocksworld-improved", eval := value d }

end Planner.ExampleHeuristics.Blocksworld
