-- Block 8 (trust-ir Semantics/Step.lean:75): term `match c` on the second
-- parameter, leading parameters that vary per member, `List C` owned twice
-- (`constFieldsAt` / `constLanesAt`).
inductive Ty where
  | I8 : Ty
  | I64 : Ty
  | F32 : Ty
  | Tuple : List Ty → Ty
  | Vector : Nat → Ty → Ty
def Ty.bitWidth : Ty → Option Nat
  | .I8 => some 8
  | .I64 => some 64
  | _ => none
inductive C where
  | int : Int → C
  | float : Nat → C
  | aggregate : List C → C
  | vector : List C → C
  | bool : Bool → C
inductive V where
  | int : Nat → Int → V
  | float : Nat → V
  | bool : Bool → V
  | aggregate : List V → V
  | vector : List V → V
def V.ofList : List C → List V := fun _ => []
def V.ofConst : C → V
  | .bool b => .bool b
  | _ => .aggregate []
def floatAt : Ty → Nat → Nat
  | .F32, f => f + 1
  | _, f => f

mutual
def constValueAt (ty : Ty) (c : C) : V :=
  match c with
  | .int i =>
    match ty.bitWidth with
    | some w => .int w i
    | none => .int 64 i
  | .float f => .float (floatAt ty f)
  | .aggregate cs =>
    match ty with
    | .Tuple tys =>
      if tys.length == cs.length then .aggregate (constFieldsAt tys cs)
      else V.ofConst (.aggregate cs)
    | _ => V.ofConst (.aggregate cs)
  | .vector cs =>
    match ty with
    | .Vector _ elemTy => .vector (constLanesAt elemTy cs)
    | _ => V.ofConst (.vector cs)
  | c => V.ofConst c

def constFieldsAt : List Ty → List C → List V
  | t :: ts, c :: cs => constValueAt t c :: constFieldsAt ts cs
  | _, cs => V.ofList cs

def constLanesAt (elemTy : Ty) : List C → List V
  | [] => []
  | c :: cs => constValueAt elemTy c :: constLanesAt elemTy cs
end
theorem v1 : constValueAt .I8 (.int 3) = .int 8 3 := rfl
theorem v2 : constValueAt (.Tuple [.I8, .F32]) (.aggregate [.int 1, .float 2]) =
    .aggregate [.int 8 1, .float 3] := rfl
theorem v3 : constValueAt (.Vector 2 .I64) (.vector [.int 5, .bool true]) =
    .vector [.int 64 5, .bool true] := rfl
