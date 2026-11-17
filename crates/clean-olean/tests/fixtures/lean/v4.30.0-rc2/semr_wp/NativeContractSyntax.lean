/- Shared original-contract syntax and mathematical environments.
   This module has no program model or weakest-precondition calculus.
   Copyright 2026 Andrew Yates. Apache-2.0. -/
namespace SemRBooleanClaim

abbrev Bytes := List Nat
abbrev Name := Bytes
abbrev Env := List (Name × Bool)
abbrev IntEnv := List (Name × Int)
abbrev TypedEnv := Env × IntEnv

inductive IntBinary where
  | add | sub | mul
  deriving DecidableEq

def IntBinary.apply : IntBinary → Int → Int → Int
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b

inductive IntExpr where
  | literal (value : Int)
  | var (name : Name)
  | neg (value : IntExpr)
  | binary (op : IntBinary) (left right : IntExpr)
  deriving DecidableEq

def IntExpr.eval (env : IntEnv) : IntExpr → Option Int
  | .literal value => some value
  | .var name => (env.find? (fun row => row.1 == name)).map Prod.snd
  | .neg value => do pure (-(← value.eval env))
  | .binary op left right => do pure (op.apply (← left.eval env) (← right.eval env))

def IntExpr.freeNames : IntExpr → List Name
  | .literal _ => []
  | .var name => [name]
  | .neg value => value.freeNames
  | .binary _ left right => left.freeNames ++ right.freeNames

inductive IntComparison where
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq

def IntComparison.apply : IntComparison → Int → Int → Bool
  | .eq, a, b => a == b
  | .ne, a, b => a != b
  | .lt, a, b => a < b
  | .le, a, b => a ≤ b
  | .gt, a, b => a > b
  | .ge, a, b => a ≥ b

end SemRBooleanClaim
