/-
Name-to-heuristic dispatch.

Mirrors the `HEURISTICS` table in pyperplan's `pyperplan.py`.  `blind` works on
any task; every other name is domain-dependent and is refused on a task whose
domain does not match, so a heuristic is never used outside the domain its
admissibility proof is about.
-/
import Planner.ExampleHeuristics.Blind
import Planner.ExampleHeuristics.Certificate
import Planner.ExampleHeuristics.Blocksworld.Simple
import Planner.ExampleHeuristics.Blocksworld.Improved
import Planner.ExampleHeuristics.Blocksworld.Certificate
import Planner.ExampleHeuristics.Childsnack.Simple
import Planner.ExampleHeuristics.Childsnack.Improved
import Planner.ExampleHeuristics.Childsnack.Certificate
import Planner.ExampleHeuristics.Ferry.Simple
import Planner.ExampleHeuristics.Ferry.Improved
import Planner.ExampleHeuristics.Ferry.Certificate
import Planner.ExampleHeuristics.Floortile.Simple
import Planner.ExampleHeuristics.Floortile.Improved
import Planner.ExampleHeuristics.Floortile.Certificate
import Planner.ExampleHeuristics.Miconic.Simple
import Planner.ExampleHeuristics.Miconic.Improved
import Planner.ExampleHeuristics.Miconic.Certificate
import Planner.ExampleHeuristics.Rovers.Simple
import Planner.ExampleHeuristics.Rovers.Improved
import Planner.ExampleHeuristics.Rovers.Certificate
import Planner.ExampleHeuristics.Satellite.Simple
import Planner.ExampleHeuristics.Satellite.Improved
import Planner.ExampleHeuristics.Satellite.Certificate
import Planner.ExampleHeuristics.Sokoban.Simple
import Planner.ExampleHeuristics.Sokoban.Improved
import Planner.ExampleHeuristics.Sokoban.Certificate
import Planner.ExampleHeuristics.Spanner.Simple
import Planner.ExampleHeuristics.Spanner.Improved
import Planner.ExampleHeuristics.Spanner.Certificate
import Planner.ExampleHeuristics.Transport.Simple
import Planner.ExampleHeuristics.Transport.Improved
import Planner.ExampleHeuristics.Transport.Certificate

namespace Planner

/-- A heuristic that can be built for a task, with the domain it is proved for. -/
structure Registered where
  name : String
  /-- The domain this heuristic is proved for; `none` means domain-independent. -/
  domain : Option String
  build : Task → Heuristic
  /--
  The decidable certificate the admissibility proof depends on.  The planner
  refuses the heuristic when it fails, so a heuristic is never used on a task
  its proof does not cover.
  -/
  certificate : Pddl.Domain → Pddl.Problem → Bool → Task → Certificate :=
    fun _ _ _ _ => Certificate.accept

private def simpleCertificate (check : Task → Bool)
    (_d : Pddl.Domain) (_p : Pddl.Problem) (_rel : Bool) (t : Task) : Certificate :=
  Certificate.one "simple heuristic family safety" (check t)

/-- Everything the planner can be asked for. -/
def registry : List Registered :=
  [{ name := "blind", domain := none, build := blind },
    { name := "blocksworld-simple", domain := some "blocksworld",
      build := ExampleHeuristics.Blocksworld.simple,
      certificate := simpleCertificate ExampleHeuristics.Blocksworld.certified },
    { name := "blocksworld-improved", domain := some "blocksworld",
      build := ExampleHeuristics.Blocksworld.improved,
      certificate := ExampleHeuristics.Blocksworld.Certificate.check },
    { name := "childsnack-simple", domain := some "childsnack",
      build := ExampleHeuristics.Childsnack.simple,
      certificate := simpleCertificate ExampleHeuristics.Childsnack.certified },
    { name := "childsnack-improved", domain := some "childsnack",
      build := ExampleHeuristics.Childsnack.improved,
      certificate := ExampleHeuristics.Childsnack.Certificate.check },
    { name := "ferry-simple", domain := some "ferry",
      build := ExampleHeuristics.Ferry.simple,
      certificate := simpleCertificate ExampleHeuristics.Ferry.certified },
    { name := "ferry-improved", domain := some "ferry",
      build := ExampleHeuristics.Ferry.improved,
      certificate := ExampleHeuristics.Ferry.Certificate.check },
    { name := "floortile-simple", domain := some "floortile",
      build := ExampleHeuristics.Floortile.simple,
      certificate := simpleCertificate ExampleHeuristics.Floortile.certified },
    { name := "floortile-improved", domain := some "floortile",
      build := ExampleHeuristics.Floortile.improved,
      certificate := ExampleHeuristics.Floortile.Certificate.check },
    { name := "miconic-simple", domain := some "miconic",
      build := ExampleHeuristics.Miconic.simple,
      certificate := simpleCertificate ExampleHeuristics.Miconic.certified },
    { name := "miconic-improved", domain := some "miconic",
      build := ExampleHeuristics.Miconic.improved,
      certificate := ExampleHeuristics.Miconic.Certificate.check },
    { name := "rovers-simple", domain := some "rover",
      build := ExampleHeuristics.Rovers.simple,
      certificate := simpleCertificate ExampleHeuristics.Rovers.certified },
    { name := "rovers-improved", domain := some "rover",
      build := ExampleHeuristics.Rovers.improved,
      certificate := ExampleHeuristics.Rovers.Certificate.check },
    { name := "satellite-simple", domain := some "satellite",
      build := ExampleHeuristics.Satellite.simple,
      certificate := simpleCertificate ExampleHeuristics.Satellite.certified },
    { name := "satellite-improved", domain := some "satellite",
      build := ExampleHeuristics.Satellite.improved,
      certificate := ExampleHeuristics.Satellite.Certificate.check },
    { name := "sokoban-simple", domain := some "sokoban",
      build := ExampleHeuristics.Sokoban.simple,
      certificate := simpleCertificate ExampleHeuristics.Sokoban.certified },
    { name := "sokoban-improved", domain := some "sokoban",
      build := ExampleHeuristics.Sokoban.improved,
      certificate := ExampleHeuristics.Sokoban.Certificate.check },
    { name := "spanner-simple", domain := some "spanner",
      build := ExampleHeuristics.Spanner.simple,
      certificate := simpleCertificate ExampleHeuristics.Spanner.certified },
    { name := "spanner-improved", domain := some "spanner",
      build := ExampleHeuristics.Spanner.improved,
      certificate := ExampleHeuristics.Spanner.Certificate.check },
    { name := "transport-simple", domain := some "transport",
      build := ExampleHeuristics.Transport.simple,
      certificate := simpleCertificate ExampleHeuristics.Transport.certified },
    { name := "transport-improved", domain := some "transport",
      build := ExampleHeuristics.Transport.improved,
      certificate := ExampleHeuristics.Transport.Certificate.check },
  ]

/-- Build the named heuristic for `t`, or explain why it does not apply. -/
def buildHeuristic (name : String) (d : Pddl.Domain) (p : Pddl.Problem)
    (rel : Bool) (t : Task) : Except String Heuristic :=
  match registry.find? (·.name == name) with
  | none =>
      .error (s!"unknown heuristic '{name}'; available: " ++
        ", ".intercalate (registry.map (·.name)))
  | some entry =>
      match entry.domain with
      | some expectedDomain =>
          if expectedDomain != t.domainName then
            .error s!"heuristic '{name}' is proved for domain '{expectedDomain}', not '{t.domainName}'"
          else
            let certificate := entry.certificate d p rel t
            if !certificate.passes then
              .error (s!"heuristic '{name}' failed its proof certificate: " ++
                ", ".intercalate certificate.failures)
            else .ok (entry.build t)
      | none => .ok (entry.build t)

end Planner
