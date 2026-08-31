/-
The heuristic interface and the pieces every domain heuristic is built from.

Mirrors pyperplan's `heuristics/heuristic_base.py`, with one difference that
matters for speed: a heuristic is *compiled* once against the task, so all the
per-task work — locating goal facts, reading static atoms, building distance
tables — happens before search starts, and the per-state call is a fold over
small integer arrays.
-/
import Planner.Task

namespace Planner

open Planner.Pddl

/--
The value returned for a state from which the goal is provably unreachable.  It
is a finite number, so heuristics stay `State → Nat` and no arithmetic in the
proofs has to deal with infinity.  Admissibility on such a state is vacuous —
there is no goal-reaching plan to underestimate — and consistency holds because
every heuristic that returns it does so on a successor-closed set of states.
-/
def deadEnd : Nat := 1 <<< 40

/-- A heuristic already specialised to one task. -/
structure Heuristic where
  name : String
  eval : State → Nat

/-- The heuristic that is zero everywhere. -/
def Heuristic.zero (name : String := "zero") : Heuristic :=
  { name, eval := fun _ => 0 }

/-! ### Reading a task's structure

These run once, when the heuristic is compiled.  They are linear scans over the
fact table, which is small; nothing here is on the per-state path.
-/

namespace Task

/-- The goal facts whose atom uses one of `preds`. -/
def goalFactsWith (t : Task) (preds : List Name) : Array Fact :=
  t.goal.filter fun f => preds.contains (t.factNames.getD f default).pred

/-- Every fact whose atom uses `pred`, paired with its atom. -/
def factsWith (t : Task) (pred : Name) : Array (Fact × GroundAtom) :=
  (t.factNames.zipIdx.filter fun (a, _) => a.pred == pred).map fun (a, i) => (i, a)

/-- The atoms of `pred` that hold in every state. -/
def staticWith (t : Task) (pred : Name) : Array GroundAtom :=
  t.staticAtoms.filter (·.pred == pred)

/-- The goal atoms that use `pred`. -/
def goalAtomsWith (t : Task) (pred : Name) : Array GroundAtom :=
  t.goalAtoms.filter (·.pred == pred)

/-- Objects whose declared type is `ty` or a subtype named in `tys`. -/
def objectsOfTypes (t : Task) (tys : List Name) : Array Name :=
  (t.objects.filter fun o => tys.contains o.type).map (·.name)

/-- All object names, in declaration order. -/
def objectNames (t : Task) : Array Name := t.objects.map (·.name)

end Task

/-! ### Counting -/

/-- How many of `facts` fail to hold in `s`.  The inner loop of every heuristic. -/
@[inline] def countMissing (facts : Array Fact) (s : State) : Nat :=
  facts.foldl (init := 0) fun acc f => if s.test f then acc else acc + 1


/-- One square's neighbours, added to the walk. -/
def reachPush (enterable : Nat → Bool) (st : Array Bool × Array Nat) (v : Nat) :
    Array Bool × Array Nat :=
  if !st.1.getD v false && enterable v && v < st.1.size then
    (st.1.setIfInBounds v true, st.2.push v)
  else st

/-- The walk itself, one queued square per step. -/
def reachLoop (adj : Array (Array Nat)) (enterable : Nat → Bool) :
    Nat → Array Bool → Array Nat → Nat → Array Bool
  | 0, seen, _, _ => seen
  | fuel + 1, seen, queue, head =>
      if head ≥ queue.size then seen
      else
        let st := (adj.getD (queue.getD head 0) #[]).foldl (init := (seen, queue))
          (reachPush enterable)
        reachLoop adj enterable fuel st.1 st.2 (head + 1)

/--
The squares reachable from a set of starting squares, walking only into squares
the caller admits.

Hoisted out of the floortile heuristic so that the lifted proof calls the same
function: the two sides then agree as soon as their three inputs do, with no
induction over the walk.
-/
def reachFrom (adj : Array (Array Nat)) (start : Array Nat)
    (enterable : Nat → Bool) : Array Bool :=
  let st := start.foldl (init := (Array.replicate adj.size false, (#[] : Array Nat)))
    (reachPush enterable)
  reachLoop adj enterable adj.size st.1 st.2 0

/-- The distinct elements of a list, keeping the first occurrence of each. -/
def distinct : List Nat → List Nat
  | [] => []
  | x :: rest => x :: (distinct rest).filter fun y => y != x

/-- How many of `facts` hold in `s`. -/
@[inline] def countHolding (facts : Array Fact) (s : State) : Nat :=
  facts.foldl (init := 0) fun acc f => if s.test f then acc + 1 else acc

/-- The largest of a list of independent lower bounds on the same actions. -/
@[inline] def maxOf (values : Array Nat) : Nat :=
  values.foldl (init := 0) max

/-- `a - b` as a demand that a supply has not met. -/
@[inline] def deficit (need supply : Nat) : Nat := need - supply

/-! ### The simple heuristic pattern

Every domain's *simple* heuristic is the maximum, over families of goal
predicates, of the number of unsatisfied goal facts in that family.  A family is
admissible and consistent exactly when no single action can make two of its goal
facts true at once, so the families are chosen per domain by reading the schemas'
add effects; nine domains need only one family, blocksworld needs three because
`stack` achieves a `clear` goal and an `on` goal together.
-/

/-- The maximum over families of the unsatisfied-goal count. -/
def maxMissingOf (name : String) (families : List (Array Fact)) : Heuristic :=
  let fams := families.toArray
  { name
    eval := fun s => fams.foldl (init := 0) fun acc fam => max acc (countMissing fam s) }

/-- The goal facts of each predicate family, in order. -/
def Task.families (t : Task) (preds : List (List Pddl.Name)) : List (Array Fact) :=
  preds.map t.goalFactsWith

/--
A family is *safe* when no operator can make two of its goal facts true at once.
That is what the consistency proof needs, and it is decidable, so the planner
checks it before using the heuristic: `Proofs/ExampleHeuristics/Base.lean` proves
admissibility from exactly this Boolean.

The check is a syntactic consequence of the domain — no schema in these domains
has two add effects of the same predicate — but it is verified against the
grounded operators of the task at hand rather than assumed.
-/
def Task.familySafe (t : Task) (family : Array Fact) : Bool :=
  decide family.toList.Nodup &&
    t.ops.all fun op => (family.filter (op.add.contains ·)).size ≤ 1

def Task.familiesSafe (t : Task) (families : List (Array Fact)) : Bool :=
  families.all t.familySafe

end Planner
