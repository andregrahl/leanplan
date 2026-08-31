/-
Parser for the supported PDDL fragment.

Mirrors pyperplan's `pddl/parser.py` together with the parts of `tree_visitor.py`
that build the AST.  Every construct outside the fragment produces a located
`Except` error; nothing is skipped silently.
-/
import Planner.Pddl.Lisp
import Planner.Pddl.Syntax

namespace Planner.Pddl

private def fail (msg : String) : Except String α := .error msg

/-- Every element of `values` must be an atom (used for typed lists and names). -/
private def atomsOnly (context : String) : List SExpr → Except String (List String)
  | [] => .ok []
  | .atom value :: rest => return value :: (← atomsOnly context rest)
  | .list _ :: _ => fail s!"unexpected nested expression in {context}"

/--
Parse a PDDL typed list: `a b - t1 c d - t2 e`.  Names before a `- type` marker
take that type; names left over at the end take `dflt` (`object` everywhere in
this fragment).
-/
private def typedList (context : String) (dflt : Name) (values : List SExpr) :
    Except String (List TypedName) := do
  let tokens ← atomsOnly context values
  let rec consume : List String → List String → List TypedName →
      Except String (List TypedName)
    | [], pending, acc => .ok (acc ++ pending.map ({ name := ·, type := dflt }))
    | "-" :: _, [], _ => fail s!"'-' with no preceding name in {context}"
    | ["-"], _, _ => fail s!"'-' with no following type in {context}"
    | "-" :: ty :: rest, pending, acc =>
        if ty == "(" || ty == ")" then fail s!"malformed type in {context}"
        else consume rest [] (acc ++ pending.map ({ name := ·, type := ty }))
    | name :: rest, pending, acc => consume rest (pending ++ [name]) acc
  consume tokens [] []

/-- `?x` is a variable, anything else is a constant of the domain. -/
private def toTerm (token : String) : Term :=
  if token.startsWith "?" then .var token else .const token

private def parseAtom (context : String) : SExpr → Except String Atom
  | .list values =>
      match values.toList with
      | .atom pred :: args => do
          let args ← atomsOnly context args
          .ok { pred, args := args.map toTerm }
      | _ => fail s!"malformed atom in {context}"
  | .atom "" => fail s!"empty atom in {context}"
  | .atom pred => .ok { pred, args := [] }

/--
Split a conjunction into its positive and negative atoms.  A bare atom counts as a
one-element conjunction, matching pyperplan.  `allowNeg` is false for
preconditions and goals, which must be positive in this fragment.
-/
private def parseConjunction (context : String) (allowNeg : Bool) :
    SExpr → Except String (List Atom × List Atom)
  | expr => do
    let parts : List SExpr :=
      match expr with
      | .list values =>
          match values.toList with
          | .atom "and" :: rest => rest
          | _ => [expr]
      | _ => [expr]
    let mut pos : List Atom := []
    let mut neg : List Atom := []
    for part in parts do
      match part with
      | .list #[.atom "not", inner] =>
          unless allowNeg do
            return (← fail s!"negative literal is outside the supported fragment in {context}")
          neg := neg ++ [← parseAtom context inner]
      | .list values =>
          match values.toList with
          | .atom "and" :: _ => return (← fail s!"nested 'and' in {context}")
          | .atom "or" :: _ => return (← fail s!"'or' is outside the supported fragment in {context}")
          | .atom "not" :: _ => return (← fail s!"malformed 'not' in {context}")
          | .atom "forall" :: _ => return (← fail s!"'forall' is outside the supported fragment in {context}")
          | .atom "exists" :: _ => return (← fail s!"'exists' is outside the supported fragment in {context}")
          | .atom "when" :: _ => return (← fail s!"conditional effects are outside the supported fragment in {context}")
          | .atom "=" :: _ => return (← fail s!"'=' is outside the supported fragment in {context}")
          | _ => pos := pos ++ [← parseAtom context part]
      | _ => pos := pos ++ [← parseAtom context part]
    .ok (pos, neg)

private def parsePredicate : SExpr → Except String Predicate
  | .list values =>
      match values.toList with
      | .atom name :: params => do
          .ok { name, params := ← typedList s!"predicate '{name}'" "object" params }
      | _ => fail "malformed predicate declaration"
  | .atom name => .ok { name, params := [] }

/-- Collect the `:keyword value` pairs of an `:action` body. -/
private def actionFields (name : Name) :
    List SExpr → List (String × SExpr) → Except String (List (String × SExpr))
  | [], acc => .ok acc
  | .atom key :: value :: rest, acc =>
      if acc.any (·.1 == key) then fail s!"duplicate '{key}' in action '{name}'"
      else actionFields name rest (acc ++ [(key, value)])
  | _, _ => fail s!"malformed field list in action '{name}'"

private def field? (fields : List (String × SExpr)) (key : String) : Option SExpr :=
  (fields.find? (·.1 == key)).map (·.2)

private def parseAction : List SExpr → Except String Action
  | .atom name :: body => do
      let fields ← actionFields name body []
      for (key, _) in fields do
        unless [":parameters", ":precondition", ":effect"].contains key do
          return (← fail s!"unsupported field '{key}' in action '{name}'")
      let params ← match field? fields ":parameters" with
        | some (.list values) => typedList s!"parameters of action '{name}'" "object" values.toList
        | some _ => fail s!"malformed :parameters of action '{name}'"
        | none => fail s!"action '{name}' has no :parameters"
      let (pre, preNeg) ← match field? fields ":precondition" with
        | some expr => parseConjunction s!"precondition of action '{name}'" false expr
        | none => .ok ([], [])
      unless preNeg.isEmpty do
        return (← fail s!"negative precondition in action '{name}'")
      let (add, del) ← match field? fields ":effect" with
        | some expr => parseConjunction s!"effect of action '{name}'" true expr
        | none => fail s!"action '{name}' has no :effect"
      .ok { name, params, pre, add, del, cost := 1 }
  | _ => fail "malformed action declaration"

private def parseDomainBody (name : Name) (sections : List SExpr) :
    Except String Domain := do
  let mut requirements : List Name := []
  let mut types : List TypeDecl := []
  let mut constants : List TypedName := []
  let mut predicates : List Predicate := []
  let mut actions : List Action := []
  let mut seen : List String := []
  for section_ in sections do
    let values ← match section_ with
      | .list values => pure values.toList
      | .atom other => fail s!"unexpected atom '{other}' at domain top level"
    match values with
    | .atom key :: rest =>
        if key != ":action" && seen.contains key then
          return (← fail s!"duplicate '{key}' section in domain '{name}'")
        seen := key :: seen
        match key with
        | ":requirements" => requirements ← atomsOnly ":requirements" rest
        | ":types" =>
            let decls ← typedList ":types" "object" rest
            types := decls.map fun d => { name := d.name, parent := d.type }
        | ":constants" => constants ← typedList ":constants" "object" rest
        | ":predicates" => predicates ← rest.mapM parsePredicate
        | ":action" => actions := actions ++ [← parseAction rest]
        | ":functions" => return (← fail "':functions' is outside the supported fragment")
        | ":derived" => return (← fail "':derived' is outside the supported fragment")
        | other => return (← fail s!"unsupported domain section '{other}'")
    | _ => return (← fail "malformed domain section")
  unless seen.contains ":predicates" do
    return (← fail s!"domain '{name}' has no :predicates section")
  .ok { name, requirements, types, constants, predicates, actions }

/-- Parse a PDDL domain file. -/
def parseDomain (source : String) : Except String Domain := do
  match ← parseSExpr source with
  | .list values =>
      match values.toList with
      | .atom "define" :: .list header :: sections =>
          match header.toList with
          | [.atom "domain", .atom name] => parseDomainBody name sections
          | _ => fail "expected '(define (domain <name>) ...)'"
      | _ => fail "expected '(define (domain <name>) ...)'"
  | .atom _ => fail "expected '(define (domain <name>) ...)'"

private def parseGroundAtom (context : String) (expr : SExpr) :
    Except String GroundAtom := do
  let atom ← parseAtom context expr
  let args ← atom.args.mapM fun
    | .const name => .ok name
    | .var name => fail s!"variable '{name}' in {context}"
  .ok { pred := atom.pred, args }

private def parseProblemBody (name domainName : Name) (sections : List SExpr) :
    Except String Problem := do
  let mut objects : List TypedName := []
  let mut init : List GroundAtom := []
  let mut goal : List GroundAtom := []
  let mut seen : List String := []
  for section_ in sections do
    let values ← match section_ with
      | .list values => pure values.toList
      | .atom other => fail s!"unexpected atom '{other}' at problem top level"
    match values with
    | .atom key :: rest =>
        if seen.contains key then
          return (← fail s!"duplicate '{key}' section in problem '{name}'")
        seen := key :: seen
        match key with
        | ":objects" => objects ← typedList ":objects" "object" rest
        | ":init" => init ← rest.mapM (parseGroundAtom ":init")
        | ":goal" =>
            match rest with
            | [expr] =>
                let (pos, neg) ← parseConjunction ":goal" false expr
                unless neg.isEmpty do
                  return (← fail "negative literal in :goal")
                goal ← pos.mapM fun atom => do
                  let args ← atom.args.mapM fun
                    | .const value => .ok value
                    | .var value => fail s!"variable '{value}' in :goal"
                  .ok { pred := atom.pred, args : GroundAtom }
            | _ => return (← fail "malformed :goal section")
        | ":metric" => return (← fail "':metric' is outside the supported fragment")
        | other => return (← fail s!"unsupported problem section '{other}'")
    | _ => return (← fail "malformed problem section")
  unless seen.contains ":goal" do
    return (← fail s!"problem '{name}' has no :goal section")
  .ok { name, domainName, objects, init, goal }

/-- Parse a PDDL problem file. -/
def parseProblem (source : String) : Except String Problem := do
  match ← parseSExpr source with
  | .list values =>
      match values.toList with
      | .atom "define" :: .list header :: sections =>
          match header.toList with
          | [.atom "problem", .atom name] =>
              match sections with
              | .list domainSection :: rest =>
                  match domainSection.toList with
                  | [.atom ":domain", .atom domainName] =>
                      parseProblemBody name domainName rest
                  | _ => fail "expected '(:domain <name>)' as the first problem section"
              | _ => fail "expected '(:domain <name>)' as the first problem section"
          | _ => fail "expected '(define (problem <name>) ...)'"
      | _ => fail "expected '(define (problem <name>) ...)'"
  | .atom _ => fail "expected '(define (problem <name>) ...)'"

end Planner.Pddl
