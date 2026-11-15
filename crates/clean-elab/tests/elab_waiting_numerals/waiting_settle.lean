-- Lean 4.8.0 accepts this file (`lean <file>`, exit 0); each theorem states
-- the value Lean computes. See `tests/elab_waiting_numerals_e2e.rs`.
-- An application whose result is an open `outParam` (`xs[0]!`, `HAdd.hAdd 2 3`)
-- settles the waiting numerals where it stands; `binop%` notations, a ground
-- index and a ground instance do not (the `c` definitions). Inside a `binrel%`
-- relation (`=`, `<`, `==`) only what the relation itself holds settles; `!=`
-- and a plain application are no such barrier (the `r` definitions).
class Tag (α : Type) where
  tag : α → Nat
instance : Tag Nat := ⟨fun x => x⟩
instance : Tag Int := ⟨fun x => x.toNat + 100⟩
def xs : Array Nat := #[1, 2, 3]
def ys : List Nat := [1, 2, 3]
def oGet : Nat := let k := 5; Tag.tag (k - 7) + xs[0]! + Tag.tag (k : Int)
def oGetList : Nat := let k := 5; Tag.tag (k - 7) + ys[0]! + Tag.tag (k : Int)
def oGetLet : Nat := let k := 5; let j := xs[0]!; Tag.tag (k - 7) + Tag.tag (k : Int) + j
def oGetDo : Nat := Id.run do
  let k := 5
  let j := xs[1]!
  return Tag.tag (k - 7) + j + Tag.tag (k : Int)
def oGetRedex : Nat := (fun k => Tag.tag (k - 7) + xs[0]! + Tag.tag (k : Int)) 5
def oGetBind : Nat := Id.run do
  let k ← pure 5
  return Tag.tag (k - 7) + xs[0]! + Tag.tag (k : Int)
def oHAdd : Nat := let k := HAdd.hAdd 2 3; Tag.tag (k - 9) + Tag.tag (k : Int)
def oHPow : Nat := let k := HPow.hPow 2 3; Tag.tag (k - 9) + Tag.tag (k : Int)
def oHMulDo : Nat := Id.run do
  let k := HMul.hMul 2 3
  return Tag.tag (k - 9) + Tag.tag (k : Int)
def oHSubId : Nat := let k := id (HSub.hSub 9 3); Tag.tag (k - 9) + Tag.tag (k : Int)
def oInBody : Nat := let k := 5; Tag.tag (HAdd.hAdd k 1 - 9) + Tag.tag (k : Int)
def oUnrelatedDo : Nat := Id.run do
  let mut k := 5
  let _j := HAdd.hAdd (1 : Nat) 1
  return Tag.tag (k - 7) + Tag.tag (k : Int)
def oShl : Nat := let k := 1 <<< 2; Tag.tag (k - 9) + Tag.tag (k : Int)
def oLocalArg : Nat := let k := 5; let j := 6; Tag.tag (HAdd.hAdd (1 : Nat) k - 9) + Tag.tag (j - 7) + Tag.tag (j : Int)
def rEq : Nat := let k := 5; (if xs[0]! = 1 then Tag.tag (k - 7) else 0) + Tag.tag (k : Int)
def rLt : Nat := let k := 5; let _b := xs[0]! < 1; Tag.tag (k - 7) + Tag.tag (k : Int)
def rEqId : Nat := let k := id 5; (if xs[0]! = 1 then Tag.tag (k - 7) else 0) + Tag.tag (k : Int)
def rBeq : Nat := let k := 5; (if xs[0]! == 1 then Tag.tag (k - 7) else 0) + Tag.tag (k : Int)
def rBne : Nat := let k := 5; (if xs[0]! != 2 then Tag.tag (k - 7) else 0) + Tag.tag (k : Int)
def rApp : Nat := let k := 5; (if Nat.ble xs[0]! 1 then Tag.tag (k - 7) else 0) + Tag.tag (k : Int)
def oLambdaInputs : Nat := let k := 5; let g := fun x y => HAdd.hAdd x y; Tag.tag (k - 7) + Tag.tag (k : Int) + g 1 2
def cBinop : Nat := let k := 2 + 3; Tag.tag (k - 9) + Tag.tag (k : Int)
def cNatIdx : Nat := let k := 5; Tag.tag (k - 7) + xs[(0 : Nat)]! + Tag.tag (k : Int)
def cGround : Nat := let k := 5; let j := HAdd.hAdd (1 : Nat) (1 : Nat); Tag.tag (k - 7) + Tag.tag (k : Int) + j
def cAfter : Nat := let j := xs[0]!; let k := 5; Tag.tag (k - 7) + Tag.tag (k : Int) + j

theorem oGet_eq : oGet = 106 := rfl
theorem oGetList_eq : oGetList = 106 := rfl
theorem oGetLet_eq : oGetLet = 106 := rfl
theorem oGetDo_eq : oGetDo = 107 := rfl
theorem oGetRedex_eq : oGetRedex = 106 := rfl
theorem oGetBind_eq : oGetBind = 106 := rfl
theorem oHAdd_eq : oHAdd = 105 := rfl
theorem oHPow_eq : oHPow = 108 := rfl
theorem oHMulDo_eq : oHMulDo = 106 := rfl
theorem oHSubId_eq : oHSubId = 106 := rfl
theorem oInBody_eq : oInBody = 105 := rfl
theorem oUnrelatedDo_eq : oUnrelatedDo = 105 := rfl
theorem oShl_eq : oShl = 104 := rfl
theorem oLocalArg_eq : oLocalArg = 106 := rfl
theorem rEq_eq : rEq = 205 := rfl
theorem rLt_eq : rLt = 205 := rfl
theorem rEqId_eq : rEqId = 205 := rfl
theorem rBeq_eq : rBeq = 205 := rfl
theorem rBne_eq : rBne = 105 := rfl
theorem rApp_eq : rApp = 105 := rfl
theorem oLambdaInputs_eq : oLambdaInputs = 108 := rfl
theorem cBinop_eq : cBinop = 205 := rfl
theorem cNatIdx_eq : cNatIdx = 206 := rfl
theorem cGround_eq : cGround = 207 := rfl
theorem cAfter_eq : cAfter = 206 := rfl
