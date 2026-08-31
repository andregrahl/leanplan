/-
Static checks on a parsed domain and problem.

Mirrors the consistency checks pyperplan's `pddl/tree_visitor.py` performs while
building its AST.  Grounding and every proof downstream assume a validated pair,
so this is the single place where "is this really the supported fragment?" is
decided.
-/
import Planner.Pddl.Parser

namespace Planner.Pddl

/-- Requirement flags that do not change the semantics of this fragment. -/
def supportedRequirements : List Name :=
  [":strips", ":typing", ":equality", ":action-costs"]

def fail (msg : String) : Except String α := .error msg

/-- No name repeats.  Made visible so a proof can read what validation
established: `Proofs/Validation.lean` turns a passing check into `List.Nodup`. -/
def noDuplicates (context : String) (names : List Name) : Except String Unit :=
  let rec go : List Name → Except String Unit
    | [] => .ok ()
    | n :: rest => if rest.contains n then fail s!"duplicate {context} '{n}'" else go rest
  go names

/--
Follow `parent` links upwards.  Reaching `object` means the chain is well
founded; running out of fuel means it revisited a type, so the declaration is
cyclic.  `Domain.isSubtype` cannot be used for this — it answers `true` for
`object` immediately, by design, which is exactly the case a cycle check must
not short-circuit.
-/
private def resolvesToObject (d : Domain) : Nat → Name → Bool
  | 0, _ => false
  | fuel + 1, name =>
      if name == "object" then true
      else match d.findType? name with
        | some decl => resolvesToObject d fuel decl.parent
        | none => false

/-- Every declared type resolves to `object` without looping. -/
private def checkTypeHierarchy (d : Domain) : Except String Unit := do
  for decl in d.types do
    unless decl.parent == "object" || d.types.any (·.name == decl.parent) do
      return (← fail s!"type '{decl.name}' has undeclared parent '{decl.parent}'")
    unless resolvesToObject d (d.types.length + 1) decl.name do
      return (← fail s!"type '{decl.name}' is part of a cyclic hierarchy")

private def checkTypeDeclared (d : Domain) (context : String) (ty : Name) :
    Except String Unit :=
  if d.typeNames.contains ty then .ok ()
  else fail s!"undeclared type '{ty}' in {context}"

/-- An atom in a schema: known predicate, right arity, and every variable bound. -/
private def checkAtom (d : Domain) (context : String) (params : List TypedName)
    (atom : Atom) : Except String Unit := do
  match d.findPredicate? atom.pred with
  | none => fail s!"undeclared predicate '{atom.pred}' in {context}"
  | some p =>
      unless p.params.length == atom.args.length do
        return (← fail (s!"predicate '{atom.pred}' takes {p.params.length} argument(s) " ++
          s!"but is used with {atom.args.length} in {context}"))
      for (term, formal) in atom.args.zip p.params do
        match term with
        | .var v =>
            match params.find? (·.name == v) with
            | none => return (← fail s!"unbound variable '{v}' in {context}")
            | some actual =>
                unless d.isSubtype actual.type formal.type do
                  return (← fail (s!"variable '{v}' of type '{actual.type}' is not a " ++
                    s!"'{formal.type}' in {context}"))
        | .const c =>
            match d.constants.find? (·.name == c) with
            | none => return (← fail s!"undeclared constant '{c}' in {context}")
            | some actual =>
                unless d.isSubtype actual.type formal.type do
                  return (← fail (s!"constant '{c}' of type '{actual.type}' is not a " ++
                    s!"'{formal.type}' in {context}"))

/-- Check a parsed domain, returning it unchanged when it is in the fragment. -/
def validateDomain (d : Domain) : Except String Domain := do
  for req in d.requirements do
    unless supportedRequirements.contains req do
      return (← fail s!"requirement '{req}' is outside the supported fragment")
  checkTypeHierarchy d
  noDuplicates "type" (d.types.map (·.name))
  noDuplicates "constant" (d.constants.map (·.name))
  noDuplicates "predicate" (d.predicates.map (·.name))
  noDuplicates "action" (d.actions.map (·.name))
  for c in d.constants do
    checkTypeDeclared d s!"constant '{c.name}'" c.type
  for p in d.predicates do
    noDuplicates s!"parameter of predicate '{p.name}'" (p.params.map (·.name))
    for param in p.params do
      checkTypeDeclared d s!"predicate '{p.name}'" param.type
  for a in d.actions do
    noDuplicates s!"parameter of action '{a.name}'" (a.params.map (·.name))
    for param in a.params do
      checkTypeDeclared d s!"action '{a.name}'" param.type
    for atom in a.pre do checkAtom d s!"precondition of action '{a.name}'" a.params atom
    for atom in a.add do checkAtom d s!"add effect of action '{a.name}'" a.params atom
    for atom in a.del do checkAtom d s!"delete effect of action '{a.name}'" a.params atom
    unless a.cost > 0 do
      return (← fail s!"action '{a.name}' has cost zero")
  .ok d

/-- An atom in `:init` or `:goal`: known predicate, right arity, declared objects. -/
private def checkGroundAtom (d : Domain) (objects : List TypedName) (context : String)
    (atom : GroundAtom) : Except String Unit := do
  match d.findPredicate? atom.pred with
  | none => fail s!"undeclared predicate '{atom.pred}' in {context}"
  | some p =>
      unless p.params.length == atom.args.length do
        return (← fail (s!"predicate '{atom.pred}' takes {p.params.length} argument(s) " ++
          s!"but is used with {atom.args.length} in {context}"))
      for (arg, formal) in atom.args.zip p.params do
        match objects.find? (·.name == arg) with
        | none => return (← fail s!"undeclared object '{arg}' in {context}")
        | some actual =>
            unless d.isSubtype actual.type formal.type do
              return (← fail (s!"object '{arg}' of type '{actual.type}' is not a " ++
                s!"'{formal.type}' in {context}"))

/--
Check a parsed problem against its domain.  Domain constants are objects too, so
they are appended before the object checks, exactly as pyperplan's grounder does.
-/
def validateProblem (d : Domain) (p : Problem) : Except String Problem := do
  unless p.domainName == d.name do
    return (← fail (s!"problem '{p.name}' names domain '{p.domainName}' but the " ++
      s!"domain file declares '{d.name}'"))
  noDuplicates "object" (p.objects.map (·.name))
  for o in p.objects do
    checkTypeDeclared d s!"object '{o.name}'" o.type
    if d.constants.any (·.name == o.name) then
      return (← fail s!"object '{o.name}' shadows a domain constant")
  let objects := p.objects ++ d.constants
  for atom in p.init do checkGroundAtom d objects ":init" atom
  for atom in p.goal do checkGroundAtom d objects ":goal" atom
  .ok p

/-- The objects of a task: the problem's objects together with the domain's constants. -/
def allObjects (d : Domain) (p : Problem) : List TypedName :=
  p.objects ++ d.constants

end Planner.Pddl
