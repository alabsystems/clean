/- Exact scalar claim data and native binding extraction. This is a claim
   interpretation, not a second program semantics.
   Copyright 2026 Andrew Yates. Apache-2.0. -/
import SemRNativeWPPlan

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

inductive Place where
  | param (index : Nat)
  | result (index : Nat)

inductive BoundValue where
  | boolean (value : Bool)
  | integer (value : Int)

/-- Reuse SemR's own exact type/range check. Initialized unsigned values are
    converted from arbitrary Nat residues, without a host-width conversion. -/
def boundValue (pointerBits : Nat) (expected : SemR.Ty) (value : SemR.Val) :
    Option BoundValue := do
  match SemR.expectTy pointerBits value expected with
  | .ok () =>
      match value with
      | .bool value => some (.boolean value)
      | .int ty raw => if ty.signed then none else some (.integer (Int.ofNat raw))
      | _ => none
  | _ => none

def typedEnv (rows : List (Name × BoundValue)) : TypedEnv :=
  rows.foldr (fun row env => match row.2 with
    | .boolean value => ((row.1, value) :: env.1, env.2)
    | .integer value => (env.1, (row.1, value) :: env.2)) ([], [])

abbrev EntryBinding := Nat × Name × SemR.Ty
abbrev ContractBinding := Name × Place × SemR.Ty

def entryTypedEnv (m : SemR.Module) (bindings : List EntryBinding)
    (core : SemR.Core) : Option TypedEnv := do
  if (bindings.map Prod.fst).eraseDups.length != bindings.length ||
      (bindings.map (fun row => row.2.1)).eraseDups.length != bindings.length then none else
    let rows ← bindings.mapM fun (id, name, ty) => do
      let value ← SemR.lookupEnv core.env id
      pure (name, ← boundValue m.pointerBits ty value)
    pure (typedEnv rows)

def contractTypedEnv (m : SemR.Module) (bindings : List ContractBinding)
    (inputs returned : List SemR.Val) : Option TypedEnv := do
  if (bindings.map Prod.fst).eraseDups.length != bindings.length then none else
    let rows ← bindings.mapM fun (name, place, ty) => do
      let value ← match place with
        | .param index => inputs[index]?
        | .result index => returned[index]?
      pure (name, ← boundValue m.pointerBits ty value)
    pure (typedEnv rows)

/-- Legacy Boolean APIs are wrappers over the same typed binding extraction. -/
def contractEnv (bindings : List (Name × Place)) (inputs : List Bool)
    (returned : Bool) : Option Env :=
  (contractTypedEnv { funcTys := [], enums := [], functions := [] }
    (bindings.map (fun (name, place) => (name, place, .bool)))
    (inputs.map SemR.Val.bool) [.bool returned]).map Prod.fst

def entryEnv (bindings : List (Nat × Name)) (core : SemR.Core) : Option Env :=
  (entryTypedEnv { funcTys := [], enums := [], functions := [] }
    (bindings.map (fun (id, name) => (id, name, .bool))) core).map Prod.fst

end SemRBooleanClaim
