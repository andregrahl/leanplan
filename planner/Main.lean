/-
Command-line entry point.

Mirrors pyperplan's `pyperplan.py`: read a domain and a problem, ground them, pick
a heuristic, run A*, print statistics and write the plan.

    planner [--heuristic NAME] [--plan-file FILE] DOMAIN.pddl PROBLEM.pddl

The statistics lines are deliberately shaped like Fast Downward's so that one
`parser.py` in the experiment can read all three planners.
-/
import Planner

open Planner
open Planner.Pddl

structure Options where
  heuristic : String := "blind"
  planFile : Option String := none
  expansionCheckpointInterval : Option Nat := none
  auditLimit : Option Nat := none
  auditShape : Bool := false
  checkCertificate : Bool := false
  domainFile : Option String := none
  problemFile : Option String := none

private def usage : String :=
  "usage: planner [--heuristic NAME] [--plan-file FILE] " ++
    "[--expansion-checkpoint-interval N] [--audit-consistency N] [--audit-shape] " ++
    "[--check-certificate] DOMAIN.pddl PROBLEM.pddl"

private def parseArgs : List String → Options → Except String Options
  | [], o => .ok o
  | "--heuristic" :: value :: rest, o => parseArgs rest { o with heuristic := value }
  | "-H" :: value :: rest, o => parseArgs rest { o with heuristic := value }
  | "--plan-file" :: value :: rest, o => parseArgs rest { o with planFile := some value }
  | "--expansion-checkpoint-interval" :: value :: rest, o =>
      match value.toNat? with
      | some n =>
          if n > 0 then
            parseArgs rest { o with expansionCheckpointInterval := some n }
          else .error s!"checkpoint interval must be positive\n{usage}"
      | none => .error s!"invalid checkpoint interval '{value}'\n{usage}"
  | "--audit-consistency" :: value :: rest, o =>
      match value.toNat? with
      | some n =>
          if n > 0 then parseArgs rest { o with auditLimit := some n }
          else .error s!"audit limit must be positive\n{usage}"
      | none => .error s!"invalid audit limit '{value}'\n{usage}"
  | "--audit-shape" :: rest, o => parseArgs rest { o with auditShape := true }
  | "--check-certificate" :: rest, o => parseArgs rest { o with checkCertificate := true }
  | arg :: rest, o =>
      if arg.startsWith "-" then .error s!"unknown option '{arg}'\n{usage}"
      else if o.domainFile.isNone then parseArgs rest { o with domainFile := some arg }
      else if o.problemFile.isNone then parseArgs rest { o with problemFile := some arg }
      else .error s!"unexpected argument '{arg}'\n{usage}"

/--
Peak resident memory, read from `/proc/self/status`.  Reported in Fast Downward's
wording so that one parser reads all three planners.  Lean's runtime reserves
about three gigabytes of *address space* it never touches, which makes an
`RLIMIT_AS` cap a poor description of what a run actually uses; this is the
number that describes it.
-/
private def peakMemoryKB : IO (Option Nat) := do
  try
    let status ← IO.FS.readFile "/proc/self/status"
    for line in status.splitOn "\n" do
      if line.startsWith "VmHWM:" then
        return (String.ofList (line.toList.filter Char.isDigit)).toNat?
    return none
  catch _ => return none

private def reportMemory : IO Unit := do
  match ← peakMemoryKB with
  | some kb => IO.println s!"Peak memory: {kb} KB"
  | none => pure ()

private def seconds (start stop : Nat) : String :=
  let micros := (stop - start) / 1000
  let frac := toString (micros % 1000000)
  s!"{micros / 1000000}.{"".pushn '0' (6 - frac.length) ++ frac}s"

/--
Walk up to `limit` reachable states and check the heuristic on each: zero at a
goal, and never more than one step ahead of a successor.  Consistency is what the
admissibility proofs rest on, and solving five benchmark tasks does not exercise
it — a heuristic can be inconsistent on states an optimal search never expands.
-/
private def auditConsistency (task : Task) (heur : Heuristic) (limit : Nat) : IO UInt32 := do
  let mut seen : Std.HashSet State := Std.HashSet.emptyWithCapacity 1024
  seen := seen.insert task.init
  let mut queue : Array State := #[task.init]
  let mut head := 0
  let mut checked := 0
  let mut steps := 0
  let mut breaches : Array String := #[]
  while head < queue.size && checked < limit do
    let s := queue[head]!
    head := head + 1
    checked := checked + 1
    let hs := heur.eval s
    if task.isGoal s && hs != 0 then
      breaches := breaches.push s!"goal state with h = {hs}"
    for op in task.ops do
      if op.applicable s then
        let s' := op.apply s
        let hs' := heur.eval s'
        steps := steps + 1
        if hs > op.cost + hs' then
          breaches := breaches.push
            s!"h = {hs} but ({op.name}) costs {op.cost} and reaches h = {hs'}"
        if !seen.contains s' then
          seen := seen.insert s'
          queue := queue.push s'
  IO.println s!"Audited {checked} state(s) and {steps} transition(s)."
  if breaches.isEmpty then
    IO.println "Consistent and goal-aware on every state audited."
    return 0
  else
    IO.println s!"Found {breaches.size} breach(es):"
    for b in breaches[0:8] do IO.println s!"  {b}"
    return 13

/--
The same walk, checking the four claims `Proofs/Domains/Satellite/Schema.lean`
makes about the heuristic's own counters rather than about the domain's
predicates.  Those four are the only fields of any domain's schema shape that are
not about the predicates, and an assumption nothing satisfies would make the
theorem that rests on it vacuous, so it is worth measuring.
-/
private def auditShape (task : Task) (name : String) (limit : Nat) : IO UInt32 := do
  match shapeSpecFor name task with
  | none =>
      IO.eprintln s!"no transition shape is registered for '{name}'"
      return 2
  | some spec =>
    let r := auditShapes task spec limit
    IO.println s!"Audited {r.states} state(s) and {r.transitions} transition(s)."
    for (n, c) in r.covered do IO.println s!"  {n}: {c}"
    if !r.leaks.isEmpty then
      IO.println s!"Found {r.leaks.size} transition(s) that left the guard:"
      let mut kinds : Std.HashMap String Nat := {}
      for b in r.leaks do
        let kind := (b.splitOn " ").headD b
        kinds := kinds.insert kind ((kinds.getD kind 0) + 1)
      for (k, n) in kinds.toList do IO.println s!"  {k}: {n}"
      return 14
    if r.uncovered.isEmpty then
      IO.println "Every transition is covered by a case of the shape."
      if spec.guard.isSome then
        IO.println "The guard is closed under every transition audited."
      return 0
    else
      IO.println s!"Found {r.uncovered.size} transition(s) no case covers:"
      let mut kinds : Std.HashMap String Nat := {}
      for b in r.uncovered do
        let kind := (b.splitOn " ").headD b
        kinds := kinds.insert kind ((kinds.getD kind 0) + 1)
      for (k, n) in kinds.toList do IO.println s!"  {k}: {n}"
      return 13

def main (args : List String) : IO UInt32 := do
  let options ← match parseArgs args {} with
    | .ok o => pure o
    | .error e => IO.eprintln e; return 2
  let some domainFile := options.domainFile | do IO.eprintln usage; return 2
  let some problemFile := options.problemFile | do IO.eprintln usage; return 2

  let t0 ← IO.monoNanosNow
  let domain ← match parseDomain (← IO.FS.readFile domainFile) >>= validateDomain with
    | .ok d => pure d
    | .error e => IO.eprintln s!"error in {domainFile}: {e}"; return 1
  let problem ← match parseProblem (← IO.FS.readFile problemFile) >>= validateProblem domain with
    | .ok p => pure p
    | .error e => IO.eprintln s!"error in {problemFile}: {e}"; return 1
  -- `IO.lazyPure` is opaque to the compiler, so grounding really happens here and
  -- the clock readings bracket the work they claim to measure.
  let relevance := (← IO.getEnv "PLANNER_NO_RELEVANCE").isNone
  let task ← IO.lazyPure fun _ => ground domain problem relevance
  let t1 ← IO.monoNanosNow
  IO.println s!"Translator facts: {task.numFacts}"
  IO.println s!"Translator operators: {task.ops.size}"
  IO.println s!"Translation time: {seconds t0 t1}"

  let heur ← match buildHeuristic options.heuristic domain problem relevance task with
    | .ok h => pure h
    | .error e => IO.eprintln e; return 1
  if options.checkCertificate then
    IO.println s!"Certificate passed for '{options.heuristic}'."
    return 0
  IO.println s!"Initial h value: {heur.eval task.init}"
  match options.auditLimit with
  | some limit =>
      if options.auditShape then
        return (← auditShape task options.heuristic limit)
      else
        return (← auditConsistency task heur limit)
  | none => pure ()
  -- Preserve setup timings if Lab interrupts the subsequent search.
  (← IO.getStdout).flush

  let result ← IO.lazyPure fun _ =>
    match options.expansionCheckpointInterval with
    | some interval => astarWithCheckpoints task heur defaultFuel interval
    | none => astar task heur defaultFuel
  let t2 ← IO.monoNanosNow

  match result.outcome with
  | .solved plan cost =>
      let steps := plan.map fun i => (task.ops.getD i default).name
      IO.println s!"Plan length: {steps.size} step(s)."
      IO.println s!"Plan cost: {cost}"
      IO.println s!"Expanded {result.expanded} state(s)."
      IO.println s!"Generated {result.generated} state(s)."
      IO.println s!"Evaluated {result.evaluated} state(s)."
      IO.println s!"Search time: {seconds t1 t2}"
      IO.println s!"Total time: {seconds t0 t2}"
      reportMemory
      IO.println "Solution found."
      match options.planFile with
      | some path => IO.FS.writeFile path (String.intercalate "\n" steps.toList ++ "\n")
      | none => for step in steps do IO.println step
      return 0
  | .unsolvable =>
      IO.println s!"Expanded {result.expanded} state(s)."
      IO.println s!"Generated {result.generated} state(s)."
      IO.println s!"Evaluated {result.evaluated} state(s)."
      IO.println s!"Search time: {seconds t1 t2}"
      IO.println s!"Total time: {seconds t0 t2}"
      reportMemory
      IO.println "Search stopped without finding a solution."
      return 12
  | .outOfFuel =>
      IO.eprintln "search exhausted its fuel"
      return 1
