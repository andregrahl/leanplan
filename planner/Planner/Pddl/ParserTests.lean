/-
Tests for the PDDL reader.

Everything here is checked when the file is compiled, so a regression in the
tokenizer, the parser or the fragment checks breaks the build rather than
surfacing as a wrong plan.  The PDDL is inline, so the tests do not depend on the
benchmark tree.

The positive tests fix the shape of what is parsed; the negative tests fix what
is *rejected*, which matters more — silently accepting a construct outside the
fragment is how a planner ends up confidently returning a wrong answer.
-/
import Planner.Pddl.Validation

namespace Planner.Pddl.Tests

/-! ### Tokenizing -/

#guard tokenize "(a b)" == ["(", "a", "b", ")"]
#guard tokenize "(A B)" == ["(", "a", "b", ")"]          -- PDDL is case-insensitive
#guard tokenize "(a ; comment\n b)" == ["(", "a", "b", ")"]
#guard tokenize ";; only a comment" == []
#guard tokenize "" == []
#guard tokenize "(?x - block)" == ["(", "?x", "-", "block", ")"]

/-! ### A small well-formed domain -/

def gripper : String := "
(define (domain gripper)
  (:requirements :strips :typing)
  (:types room ball gripper)
  (:constants left right - gripper)
  (:predicates (at-robby ?r - room) (at ?b - ball ?r - room)
               (free ?g - gripper) (carry ?o - ball ?g - gripper))
  (:action move
    :parameters (?from - room ?to - room)
    :precondition (at-robby ?from)
    :effect (and (at-robby ?to) (not (at-robby ?from))))
  (:action pick
    :parameters (?obj - ball ?room - room ?g - gripper)
    :precondition (and (at ?obj ?room) (at-robby ?room) (free ?g))
    :effect (and (carry ?obj ?g) (not (at ?obj ?room)) (not (free ?g)))))
"

def gripperProblem : String := "
(define (problem gripper-2)
  (:domain gripper)
  (:objects rooma roomb - room ball1 ball2 - ball)
  (:init (at-robby rooma) (free left) (free right)
         (at ball1 rooma) (at ball2 rooma))
  (:goal (and (at ball1 roomb) (at ball2 roomb))))
"

/-- Extract a field of a successfully parsed value, or a stand-in on failure. -/
private def field {α β : Type} [Inhabited β] (r : Except α β) : β :=
  match r with
  | .ok v => v
  | .error _ => default

private def parsedDomain : Domain :=
  field (parseDomain gripper >>= validateDomain)

private def parsedProblem : Problem :=
  field (parseProblem gripperProblem >>= validateProblem parsedDomain)

#guard parsedDomain.name == "gripper"
#guard parsedDomain.types.length == 3
#guard parsedDomain.constants.length == 2
#guard parsedDomain.predicates.length == 4
#guard parsedDomain.actions.length == 2

-- `move` has one precondition, one add effect and one delete effect.
#guard (parsedDomain.findAction? "move").isSome
#guard ((parsedDomain.findAction? "move").getD default).params.length == 2
#guard ((parsedDomain.findAction? "move").getD default).pre.length == 1
#guard ((parsedDomain.findAction? "move").getD default).add.length == 1
#guard ((parsedDomain.findAction? "move").getD default).del.length == 1

-- A bare precondition is read as a one-element conjunction, as in pyperplan.
#guard ((parsedDomain.findAction? "pick").getD default).pre.length == 3
#guard ((parsedDomain.findAction? "pick").getD default).del.length == 2

-- Types declared without an explicit parent sit directly under `object`.
#guard parsedDomain.isSubtype "ball" "object"
#guard parsedDomain.isSubtype "ball" "ball"
#guard !parsedDomain.isSubtype "ball" "room"

#guard parsedProblem.name == "gripper-2"
#guard parsedProblem.domainName == "gripper"
#guard parsedProblem.objects.length == 4
#guard parsedProblem.init.length == 5
#guard parsedProblem.goal.length == 2

-- Domain constants count as objects of the task.
#guard (allObjects parsedDomain parsedProblem).length == 6

/-! ### What must be rejected

Each of these is outside the supported fragment, or plainly malformed.  A parser
that accepted them would let the planner search the wrong state space.
-/

private def failed {α β : Type} : Except α β → Bool
  | .error _ => true
  | .ok _ => false

private def rejected (source : String) : Bool :=
  failed (parseDomain source >>= validateDomain)

private def rejectedProblem (source : String) : Bool :=
  failed (parseProblem source >>= validateProblem parsedDomain)

private def wrap (body : String) : String :=
  "(define (domain d) (:predicates (p ?x) (q ?x)) " ++ body ++ ")"

#guard rejected (wrap "(:action a :parameters (?x) :precondition (not (p ?x)) :effect (q ?x))")
#guard rejected (wrap "(:action a :parameters (?x) :precondition (or (p ?x) (q ?x)) :effect (q ?x))")
#guard rejected (wrap "(:action a :parameters (?x) :precondition (forall (?y) (p ?y)) :effect (q ?x))")
#guard rejected (wrap "(:action a :parameters (?x) :precondition (p ?x) :effect (when (p ?x) (q ?x)))")
#guard rejected (wrap "(:action a :parameters (?x) :precondition (= ?x ?x) :effect (q ?x))")
-- an unbound variable in an effect
#guard rejected (wrap "(:action a :parameters (?x) :precondition (p ?x) :effect (q ?y))")
-- the wrong number of arguments
#guard rejected (wrap "(:action a :parameters (?x) :precondition (p ?x ?x) :effect (q ?x))")
-- an undeclared predicate
#guard rejected (wrap "(:action a :parameters (?x) :precondition (r ?x) :effect (q ?x))")
-- no effect at all
#guard rejected (wrap "(:action a :parameters (?x) :precondition (p ?x))")
-- a requirement outside the fragment
#guard rejected "(define (domain d) (:requirements :adl) (:predicates (p ?x)))"
-- numeric fluents
#guard rejected "(define (domain d) (:predicates (p ?x)) (:functions (f ?x)))"
-- a cyclic type hierarchy
#guard rejected "(define (domain d) (:types a - b b - a) (:predicates (p ?x)))"
-- duplicate declarations
#guard rejected "(define (domain d) (:predicates (p ?x) (p ?y)))"
-- no predicates section
#guard rejected "(define (domain d))"
-- unbalanced parentheses
#guard rejected "(define (domain d) (:predicates (p ?x))"

-- The problem must name the domain it belongs to.
#guard rejectedProblem "(define (problem p) (:domain other) (:objects) (:init) (:goal (at-robby rooma)))"
-- Goals must be positive.
#guard rejectedProblem
  "(define (problem p) (:domain gripper) (:objects rooma - room)
     (:init (at-robby rooma)) (:goal (not (at-robby rooma))))"
-- Objects must be declared.
#guard rejectedProblem
  "(define (problem p) (:domain gripper) (:objects) (:init (at-robby nowhere)) (:goal (free left)))"
-- Objects must not shadow a domain constant.
#guard rejectedProblem
  "(define (problem p) (:domain gripper) (:objects left - room) (:init) (:goal (free left)))"

end Planner.Pddl.Tests
