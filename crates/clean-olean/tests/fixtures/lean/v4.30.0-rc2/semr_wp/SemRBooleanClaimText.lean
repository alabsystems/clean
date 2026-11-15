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

private def operator (level : Nat) (input : Bytes) : Option (Binary × Bytes) :=
  if level = 0 then (token [61,61,62] input).map (Binary.implies, ·) else
  if level = 1 then (token [124,124] input).map (Binary.or, ·) else
  if level = 2 then (token [38,38] input).map (Binary.and, ·) else
  if level = 3 then
    if (token [61,61,62] input).isSome then none else
      match token [61,61] input with
      | some rest => some (.eq, rest)
      | none => (token [33,61] input).map (Binary.ne, ·)
  else none

private def boolAscription (input : Bytes) : Option Bytes :=
  match token [58] (spaces input) with
  | none => some input
  | some rest =>
      match keyword [98,111,111,108] (spaces rest) with
      | some tail => some tail
      | none => keyword [66,111,111,108] (spaces rest)

mutual
  /-- Precedence and associativity are part of decoding the original bytes.
      Unsupported operators, binders and annotations have no successful path. -/
  private def parseExpr : Nat → Nat → Bytes → Option (Expr × Bytes)
    | 0, _, _ => none
    | fuel + 1, level, input => do
        if level < 4 then
          let (left, rest) ← parseExpr fuel (level + 1) input
          parseTail fuel level left rest
        else
          let input := spaces input
          if let some rest := token [33] input then
            let (value, rest) ← parseExpr fuel 4 rest
            some (.not value, rest)
          else if let some rest := token [40] input then
            let (value, rest) ← parseExpr fuel 0 rest
            let rest ← boolAscription rest
            let rest ← token [41] (spaces rest)
            some (value, rest)
          else if let some rest := keyword [105,102] input then
            let (condition, rest) ← parseExpr fuel 0 rest
            let rest ← token [123] (spaces rest)
            let (yes, rest) ← parseExpr fuel 0 rest
            let rest ← token [125] (spaces rest)
            let rest ← keyword [101,108,115,101] (spaces rest)
            let rest ← token [123] (spaces rest)
            let (no, rest) ← parseExpr fuel 0 rest
            let rest ← token [125] (spaces rest)
            some (.ite condition yes no, rest)
          else if let some rest := keyword [116,114,117,101] input then
            some (.literal true, rest)
          else if let some rest := keyword [102,97,108,115,101] input then
            some (.literal false, rest)
          else
            let (name, rest) ← qualifiedName (input.length + 1) input
            some (.var name, rest)

  private def parseTail : Nat → Nat → Expr → Bytes → Option (Expr × Bytes)
    | 0, _, _, _ => none
    | fuel + 1, level, left, input => do
        let input := spaces input
        match operator level input with
        | none => some (left, input)
        | some (op, rest) =>
            let (right, rest) ← parseExpr fuel (if level = 0 then 0 else level + 1) rest
            let expression := Expr.binary op left right
            if level = 0 then some (expression, rest)
            else parseTail fuel level expression rest
end

def freeNames : Expr → List Name
  | .literal _ => []
  | .var name => [name]
  | .intCompare _ left right => left.freeNames ++ right.freeNames
  | .not value => freeNames value
  | .binary _ left right => freeNames left ++ freeNames right
  | .ite condition yes no => freeNames condition ++ freeNames yes ++ freeNames no

/-- Decode only a complete, bounded Boolean claim over the original binding
    names. Trailing bytes and unbound or duplicate names refuse. -/
def decodeText (fuel : Nat) (names : List Name) (input : Bytes) : Option Expr := do
  if names.eraseDups.length != names.length || !(input.all (· < 256)) then none else
    let (expression, rest) ← parseExpr fuel 0 input
    if !(spaces rest).isEmpty || !(freeNames expression).all names.contains then none else
      some expression

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
