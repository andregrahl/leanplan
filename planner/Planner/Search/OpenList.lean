/-
The open list: buckets indexed by `f` and then by `h`.

A binary heap would work, but buckets are both faster and easier to reason
about, and they are what Fast Downward's A* uses.  `buckets[f][h]` is a stack of
node indices, `minF` is a lower bound on the smallest `f` present, and popping
means walking up from `minF` to the first non-empty bucket.  `minF` only ever
moves forward except when a push introduces a smaller `f`, so the walk is
amortised constant.

Within one `(f, h)` bucket the *last* node pushed is popped first.  Among states
that look equally good this dives towards the goal instead of fanning out, which
measurably cuts expansions; no tie-breaking rule can affect optimality, because
`Proofs/Search/AStar.lean` only ever uses that the popped entry has minimal `f`.
-/

namespace Planner

/-- One open-list entry: the priority pair and the node it refers to. -/
structure Entry where
  f : Nat
  h : Nat
  node : Nat
  deriving Inhabited, DecidableEq

/-- Buckets by `f`, then by `h`, of node indices. -/
structure OpenList where
  buckets : Array (Array (Array Nat))
  /-- Every entry present has `f` at least this. -/
  minF : Nat
  /-- How many entries are present. -/
  count : Nat
  deriving Inhabited

namespace OpenList

def empty : OpenList := { buckets := #[], minF := 0, count := 0 }

@[inline] def size (q : OpenList) : Nat := q.count

@[inline] def isEmpty (q : OpenList) : Bool := q.count == 0

/-- Grow `a` so that index `i` exists, filling with `pad`. -/
@[inline] def widen {α : Type} (a : Array α) (i : Nat) (pad : α) : Array α :=
  if i < a.size then a else a ++ Array.replicate (i + 1 - a.size) pad

/-- `Array.modify` is used throughout: it takes the element out before rebuilding
it, which keeps the nested arrays uniquely referenced and the update in place. -/
def push (q : OpenList) (e : Entry) : OpenList :=
  let buckets := widen q.buckets e.f #[]
  let buckets := buckets.modify e.f fun row =>
    (widen row e.h #[]).modify e.h (·.push e.node)
  { buckets
    -- `minF` only has to be a lower bound on the keys present; `pop?` raises it
    -- to the bucket it drained, so taking the minimum here costs at most one
    -- extra scan, on the very first pop.
    minF := min q.minF e.f
    count := q.count + 1 }

/-- The first `f` at or above `start` whose bucket holds something. -/
def firstNonEmpty (buckets : Array (Array (Array Nat))) (start : Nat) :
    Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
      if start ≥ buckets.size then none
      else if (buckets.getD start #[]).any (fun row => !row.isEmpty) then some start
      else firstNonEmpty buckets (start + 1) fuel

/-- The smallest `h` in a row that holds something. -/
def firstNonEmptyRow (row : Array (Array Nat)) : Nat → Nat → Option Nat
  | _, 0 => none
  | i, fuel + 1 =>
      if i ≥ row.size then none
      else if (row.getD i #[]).isEmpty then firstNonEmptyRow row (i + 1) fuel
      else some i

/-- Remove and return an entry of smallest `f`, and among those smallest `h`. -/
def pop? (q : OpenList) : Option (Entry × OpenList) :=
  match firstNonEmpty q.buckets q.minF (q.buckets.size + 1) with
  | none => none
  | some f =>
      match firstNonEmptyRow (q.buckets.getD f #[]) 0 ((q.buckets.getD f #[]).size + 1) with
      | none => none
      | some h =>
          match ((q.buckets.getD f #[]).getD h #[]).back? with
          | none => none
          | some node =>
              some ({ f, h, node },
                { buckets := q.buckets.modify f fun row => row.modify h (·.pop)
                  minF := f
                  count := q.count - 1 })

end OpenList

end Planner
