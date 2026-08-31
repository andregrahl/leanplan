/-
S-expression reader for PDDL sources.

Mirrors pyperplan's `pddl/lisp_parser.py`: PDDL is read as Lisp, comments run from
`;` to end of line, and parentheses are the only delimiters.  PDDL is
case-insensitive, so every token is lowercased here once and the rest of the
planner may compare names with `==`.
-/

namespace Planner.Pddl

/-- A Lisp datum: either an atom or a parenthesised list. -/
inductive SExpr where
  | atom (value : String)
  | list (values : Array SExpr)
  deriving Inhabited, Repr

namespace SExpr

def asAtom? : SExpr → Option String
  | .atom value => some value
  | .list _ => none

def asList? : SExpr → Option (Array SExpr)
  | .atom _ => none
  | .list values => some values

/-- Render an s-expression back to text.  Used for error messages only. -/
partial def render : SExpr → String
  | .atom value => value
  | .list values => "(" ++ " ".intercalate (values.toList.map render) ++ ")"

end SExpr

/-- Flush a pending token, if any, onto the reversed token list. -/
private def flush (pending : List Char) (tokens : List String) : List String :=
  if pending.isEmpty then tokens else String.ofList pending.reverse :: tokens

/--
Split PDDL source into tokens.  `inComment` skips to the next newline; `pending`
accumulates the characters of the token currently being read, in reverse.
-/
private def tokenizeAux :
    List Char → (inComment : Bool) → (pending : List Char) → (tokens : List String) →
      List String
  | [], _, pending, tokens => (flush pending tokens).reverse
  | c :: rest, true, pending, tokens =>
      if c = '\n' then tokenizeAux rest false pending tokens
      else tokenizeAux rest true pending tokens
  | c :: rest, false, pending, tokens =>
      if c = ';' then
        tokenizeAux rest true [] (flush pending tokens)
      else if c = '(' || c = ')' then
        tokenizeAux rest false [] (String.singleton c :: flush pending tokens)
      else if c.isWhitespace then
        tokenizeAux rest false [] (flush pending tokens)
      else
        tokenizeAux rest false (c.toLower :: pending) tokens

/-- Tokenize PDDL source.  Parentheses become their own tokens; names are lowercased. -/
def tokenize (source : String) : List String :=
  tokenizeAux source.toList false [] []

/-
Read one s-expression off the front of a token list, and read the elements of a
list until its closing parenthesis.  `fuel` bounds the recursion; callers pass the
token count, which strictly exceeds any possible nesting depth.
-/
mutual

private def readOne : (fuel : Nat) → List String → Except String (SExpr × List String)
  | 0, _ => .error "PDDL input is nested more deeply than it has tokens"
  | _ + 1, [] => .error "unexpected end of PDDL input"
  | fuel + 1, "(" :: rest => readMany fuel rest #[]
  | _ + 1, ")" :: _ => .error "unexpected ')'"
  | _ + 1, token :: rest => .ok (.atom token, rest)

private def readMany : (fuel : Nat) → List String → Array SExpr →
    Except String (SExpr × List String)
  | 0, _, _ => .error "PDDL input is nested more deeply than it has tokens"
  | _ + 1, [], _ => .error "unclosed '(' in PDDL input"
  | _ + 1, ")" :: rest, acc => .ok (.list acc, rest)
  | fuel + 1, tokens, acc => do
      let (value, rest) ← readOne fuel tokens
      readMany fuel rest (acc.push value)

end

/-- Parse a whole PDDL file as a single top-level s-expression. -/
def parseSExpr (source : String) : Except String SExpr := do
  let tokens := tokenize source
  let (value, rest) ← readOne (tokens.length + 1) tokens
  if rest.isEmpty then .ok value
  else .error "more than one top-level expression in PDDL input"

end Planner.Pddl
