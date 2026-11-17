/-
  Kernel computation on the original native pure-expression claim bytes.
  The Boolean constructors have the one interpretation in SemRBooleanClaim.
  Copyright 2026 Andrew Yates. Apache-2.0.
-/
import SemRBooleanClaim

namespace SemRBooleanClaim

private def whitespace (b : Nat) : Bool := b == 32 || b == 9 || b == 10 || b == 13
private def spaces (input : Bytes) : Bytes := input.dropWhile whitespace

private def token (expected input : Bytes) : Option Bytes :=
  if expected.isPrefixOf input then some (input.drop expected.length) else none

private def nameStart (b : Nat) : Bool :=
  (65 ≤ b && b ≤ 90) || (97 ≤ b && b ≤ 122) || b == 95 || (128 ≤ b && b < 256)
private def nameRest (b : Nat) : Bool := nameStart b || (48 ≤ b && b ≤ 57)

private def keyword (expected input : Bytes) : Option Bytes := do
  let rest ← token expected input
  if rest.head?.any nameRest then none else some rest

private def qualifiedName : Nat → Bytes → Option (Name × Bytes)
  | 0, _ => none
  | fuel + 1, first :: rest => do
      if !nameStart first then none else
        let (part, tail) := rest.span nameRest
        match token [58,58] tail with
        | none => some (first :: part, tail)
        | some afterScope => do
            let (suffix, tail) ← qualifiedName fuel afterScope
            some ((first :: part) ++ [58,58] ++ suffix, tail)
  | _ + 1, [] => none

private inductive TextValue where
  | boolean (value : Expr)
  | integer (value : IntExpr)

private inductive TextOperator where
  | boolean (op : Binary)
  | comparison (op : IntComparison)
  | integer (op : IntBinary)

private def TextOperator.apply : TextOperator → TextValue → TextValue → Option TextValue
  | .boolean op, .boolean left, .boolean right => some (.boolean (.binary op left right))
  | .comparison .eq, .boolean left, .boolean right =>
      some (.boolean (.binary .eq left right))
  | .comparison .ne, .boolean left, .boolean right =>
      some (.boolean (.binary .ne left right))
  | .comparison op, .integer left, .integer right =>
      some (.boolean (.intCompare op left right))
  | .integer op, .integer left, .integer right => some (.integer (.binary op left right))
  | _, _, _ => none

private def operator (level : Nat) (input : Bytes) : Option (TextOperator × Bytes) :=
  if level = 0 then (token [61,61,62] input).map (.boolean .implies, ·) else
  if level = 1 then (token [124,124] input).map (.boolean .or, ·) else
  if level = 2 then (token [38,38] input).map (.boolean .and, ·) else
  if level = 3 then
    if (token [61,61,62] input).isSome then none else
      match token [61,61] input with
      | some rest => some (.comparison .eq, rest)
      | none => (token [33,61] input).map (.comparison .ne, ·)
  else if level = 4 then
    match token [60,61] input with
    | some rest => some (.comparison .le, rest)
    | none => match token [62,61] input with
      | some rest => some (.comparison .ge, rest)
      | none => match token [60] input with
        | some rest => some (.comparison .lt, rest)
        | none => (token [62] input).map (.comparison .gt, ·)
  else if level = 5 then
    match token [43] input with
    | some rest => some (.integer .add, rest)
    | none => (token [45] input).map (.integer .sub, ·)
  else if level = 6 then (token [42] input).map (.integer .mul, ·)
  else none

private def boolAscription (input : Bytes) : Option Bytes :=
  match token [58] (spaces input) with
  | none => some input
  | some rest =>
      match keyword [98,111,111,108] (spaces rest) with
      | some tail => some tail
      | none => keyword [66,111,111,108] (spaces rest)

private def digit (b : Nat) : Bool := 48 ≤ b && b ≤ 57

mutual
  /-- Precedence and associativity are part of decoding the original bytes.
      Unsupported operators, binders and annotations have no successful path. -/
  private def parseExpr : Nat → List Name → List Name → Nat → Bytes →
      Option (TextValue × Bytes)
    | 0, _, _, _, _ => none
    | fuel + 1, booleans, integers, level, input => do
        if level < 7 then
          let (left, rest) ← parseExpr fuel booleans integers (level + 1) input
          parseTail fuel booleans integers level left rest
        else
          let input := spaces input
          if let some rest := token [33] input then
            let (.boolean value, rest) ← parseExpr fuel booleans integers 7 rest | none
            some (.boolean (.not value), rest)
          else if let some rest := token [45] input then
            let (.integer value, rest) ← parseExpr fuel booleans integers 7 rest | none
            some (.integer (.neg value), rest)
          else if let some rest := token [40] input then
            let (value, rest) ← parseExpr fuel booleans integers 0 rest
            let rest ← match value with
              | .boolean _ => boolAscription rest
              | .integer _ => some rest
            let rest ← token [41] (spaces rest)
            some (value, rest)
          else if let some rest := keyword [105,102] input then
            let (.boolean condition, rest) ← parseExpr fuel booleans integers 0 rest | none
            let rest ← token [123] (spaces rest)
            let (.boolean yes, rest) ← parseExpr fuel booleans integers 0 rest | none
            let rest ← token [125] (spaces rest)
            let rest ← keyword [101,108,115,101] (spaces rest)
            let rest ← token [123] (spaces rest)
            let (.boolean no, rest) ← parseExpr fuel booleans integers 0 rest | none
            let rest ← token [125] (spaces rest)
            some (.boolean (.ite condition yes no), rest)
          else if let some rest := keyword [116,114,117,101] input then
            some (.boolean (.literal true), rest)
          else if let some rest := keyword [102,97,108,115,101] input then
            some (.boolean (.literal false), rest)
          else if input.head?.any digit then
            let (digits, rest) := input.span digit
            let value := digits.foldl (fun n b => 10 * n + (b - 48)) 0
            some (.integer (.literal (Int.ofNat value)), rest)
          else
            let (name, rest) ← qualifiedName (input.length + 1) input
            if booleans.contains name then some (.boolean (.var name), rest)
            else if integers.contains name then some (.integer (.var name), rest)
            else none

  private def parseTail : Nat → List Name → List Name → Nat → TextValue → Bytes →
      Option (TextValue × Bytes)
    | 0, _, _, _, _, _ => none
    | fuel + 1, booleans, integers, level, left, input => do
        let input := spaces input
        match operator level input with
        | none => some (left, input)
        | some (op, rest) =>
            let (right, rest) ← parseExpr fuel booleans integers
              (if level = 0 then 0 else level + 1) rest
            let expression ← op.apply left right
            if level = 0 then some (expression, rest)
            else parseTail fuel booleans integers level expression rest
end

def freeNames : Expr → List Name
  | .literal _ => []
  | .var name => [name]
  | .intCompare _ left right => left.freeNames ++ right.freeNames
  | .not value => freeNames value
  | .binary _ left right => freeNames left ++ freeNames right
  | .ite condition yes no => freeNames condition ++ freeNames yes ++ freeNames no

/-- One sort-checked codec for original Boolean and mathematical-integer text.
    Cross-sort operations, unknown or duplicate names, and trailing bytes refuse.
    Arithmetic uses the existing IntExpr interpretation, never machine wrapping. -/
def decodeTypedText (fuel : Nat) (booleans integers : List Name) (input : Bytes) : Option Expr := do
  let names := booleans ++ integers
  if names.eraseDups.length != names.length || !(input.all (· < 256)) then none else
    let (.boolean expression, rest) ← parseExpr fuel booleans integers 0 input | none
    if !(spaces rest).isEmpty || !(freeNames expression).all names.contains then none else
      some expression

/-- The Boolean-only entry uses the same codec and retains its original API. -/
def decodeText (fuel : Nat) (names : List Name) (input : Bytes) : Option Expr :=
  decodeTypedText fuel names [] input

def checkedTypedText (fuel : Nat) (bytes : Bytes) (booleans integers : List Name)
    (env : TypedEnv) : Option Bool :=
  (decodeTypedText fuel booleans integers bytes).bind (evalTyped env.1 env.2)

theorem checked_typed_text_sound (fuel : Nat) (bytes : Bytes)
    (booleans integers : List Name) (env : TypedEnv) (value : Bool)
    (accepted : checkedTypedText fuel bytes booleans integers env = some value) :
    ∃ expression, decodeTypedText fuel booleans integers bytes = some expression ∧
      evalTyped env.1 env.2 expression = some value := by
  unfold checkedTypedText at accepted
  cases decoded : decodeTypedText fuel booleans integers bytes with
  | none => simp [decoded] at accepted
  | some expression => exact ⟨expression, rfl, by simpa [decoded] using accepted⟩

def checkedText (fuel : Nat) (bytes : Bytes) (names : List Name) (env : Env) : Option Bool :=
  (decodeText fuel names bytes).bind (eval env)

theorem checked_text_eval (fuel : Nat) (bytes : Bytes) (names : List Name)
    (expression : Expr) (env : Env)
    (decoded : decodeText fuel names bytes = some expression) :
    checkedText fuel bytes names env = eval env expression := by
  simp [checkedText, decoded]

/-- Successful original-text checks use precisely the expression decoded from
    those bytes, not an untrusted renamed or reprinted predicate. -/
theorem checked_text_sound (fuel : Nat) (bytes : Bytes) (names : List Name)
    (env : Env) (value : Bool)
    (accepted : checkedText fuel bytes names env = some value) :
    ∃ expression, decodeText fuel names bytes = some expression ∧
      eval env expression = some value := by
  unfold checkedText at accepted
  cases decoded : decodeText fuel names bytes with
  | none => simp [decoded] at accepted
  | some expression => exact ⟨expression, rfl, by simpa [decoded] using accepted⟩

end SemRBooleanClaim
