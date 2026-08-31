/- The one production A* engine over the task-compiled runtime representation. -/
import Planner.CompiledTask
import Planner.Search.AStar

namespace Planner

@[inline] def expandApplicableCompiled (t : CompiledTask) (heur : Heuristic) (id i : Nat)
    (node : Node) (s : Search) : Search :=
  let op := t.ops.getD i default
  let succ := op.apply node.state
  let g := node.g + op.logical.cost
  match s.best.get? succ with
  | some previous =>
      if g < previous then record heur id i succ g s
      else { s with generated := s.generated + 1 }
  | none => record heur id i succ g s

@[inline] def expandCandidateCompiled (t : CompiledTask) (heur : Heuristic) (id i : Nat)
    (node : Node) (s : Search) : Search :=
  let op := t.ops.getD i default
  if op.remainingPre.isEmpty || op.applicable node.state then
    expandApplicableCompiled t heur id i node s
  else s

def expandBucketCompiledFrom (t : CompiledTask) (heur : Heuristic) (id : Nat)
    (node : Node) (ids : Array Nat) : Nat → Nat → Search → Search
  | 0, _, s => s
  | fuel + 1, pos, s =>
      if pos < ids.size then
        let i := ids.getD pos 0
        expandBucketCompiledFrom t heur id node ids fuel (pos + 1)
            (expandCandidateCompiled t heur id i node s)
      else s

def expandWordCompiled (t : CompiledTask) (heur : Heuristic) (id : Nat)
    (node : Node) (base : Nat) : Nat → UInt64 → Search → Search
  | 0, _, s => s
  | fuel + 1, word, s =>
      if word == 0 then s
      else
        let bit := 64 - (fuel + 1)
        let s := if word &&& 1 != 0 then
          let fact := base + bit
          let ids := t.successors.byFact.getD fact #[]
          expandBucketCompiledFrom t heur id node ids ids.size 0 s
        else s
        expandWordCompiled t heur id node base fuel (word >>> 1) s

def expandWordsCompiledFrom (t : CompiledTask) (heur : Heuristic) (id : Nat)
    (node : Node) : Nat → Nat → Search → Search
  | 0, _, s => s
  | fuel + 1, wordIndex, s =>
      if wordIndex < node.state.words.size then
        let word := node.state.words.getD wordIndex 0
        let s := expandWordCompiled t heur id node (wordIndex * 64) 64 word s
        expandWordsCompiledFrom t heur id node fuel (wordIndex + 1) s
      else s

def expandCompiled (t : CompiledTask) (heur : Heuristic) (id : Nat)
    (node : Node) (s : Search) : Search :=
  let s := { s with expanded := s.expanded + 1 }
  let fallback := t.successors.fallback
  let s := expandBucketCompiledFrom t heur id node fallback fallback.size 0 s
  expandWordsCompiledFrom t heur id node node.state.words.size 0 s

def loopCompiled (t : CompiledTask) (heur : Heuristic) (checkpointInterval : Option Nat) :
    Nat → Search → Result
  | 0, s => { outcome := .outOfFuel, expanded := s.expanded,
              generated := s.generated, evaluated := s.evaluated, pruned := s.pruned }
  | fuel + 1, s =>
      match s.openList.pop? with
      | none => { outcome := .unsolvable, expanded := s.expanded,
                  generated := s.generated, evaluated := s.evaluated, pruned := s.pruned }
      | some (entry, rest) =>
          match s.nodes[entry.node]? with
          | none => loopCompiled t heur checkpointInterval fuel { s with openList := rest }
          | some node =>
              if s.best.getD node.state node.g < node.g then
                loopCompiled t heur checkpointInterval fuel { s with openList := rest }
              else if t.isGoal node.state then
                { outcome := .solved (extractPlan s.nodes entry.node) node.g
                  expanded := s.expanded, generated := s.generated, evaluated := s.evaluated
                  pruned := s.pruned }
              else
                let next := expandCompiled t heur entry.node node { s with openList := rest }
                let next := match checkpointInterval with
                  | some interval => traceExpansionCheckpoint interval next
                  | none => next
                loopCompiled t heur checkpointInterval fuel next

def astarCompiled (t : Task) (heur : Heuristic) (fuel : Nat)
    (checkpointInterval : Option Nat := none) : Result :=
  let compiled := compileTaskIdentity t
  let root := Node.root t
  let h := heur.eval root.state
  let start : Search :=
    { openList := OpenList.empty
      nodes := #[root]
      best := (Std.HashMap.emptyWithCapacity 1048576 : Std.HashMap State Nat).insert root.state 0
      expanded := 0, generated := 0, evaluated := 1, pruned := 0 }
  if h ≥ deadEnd then
    loopCompiled compiled heur checkpointInterval fuel { start with pruned := 1 }
  else
    loopCompiled compiled heur checkpointInterval fuel
      { start with openList := start.openList.push { f := h, h, node := 0 } }

end Planner
