-- False twin of const_value_at.lean: the tuple lanes take their own types.
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
theorem v2_twin : constValueAt (.Tuple [.I8, .F32]) (.aggregate [.int 1, .float 2]) =
    .aggregate [.int 8 1, .float 2] := rfl
