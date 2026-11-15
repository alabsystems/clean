-- Lean 4.8.0 accepts this file (`lean <file>`, exit 0); each theorem states
-- the value Lean computes. See `tests/elab_waiting_numerals_e2e.rs`.
class Tag (α : Type) where
  tag : α → Nat
instance : Tag Nat := ⟨fun x => x⟩
@[default_instance] instance : Tag Int := ⟨fun x => x.toNat + 100⟩
def dNum : Nat := let k := 5; Tag.tag k
def dId : Nat := let k := id 5; Tag.tag k
def dFnNat : Nat := let f := fun k => Tag.tag k; f (5 : Nat)
def dFnNum : Nat := let f := fun k => Tag.tag k; f 5
def dTwo : Nat := let f := fun k j => Tag.tag (j : Int) + Tag.tag k; f (5 : Nat) 7
def n : Nat := 5
def dVar : Nat := let f := fun k => Tag.tag k; f n
def dDo : Nat := Id.run do
  let k := 5
  return Tag.tag k
def dRedex : Nat := (fun k => Tag.tag k) 5
def dPinNat : Nat := let k := 5; Tag.tag k + Tag.tag (k : Nat)

theorem dNum_eq : dNum = 105 := rfl
theorem dId_eq : dId = 105 := rfl
theorem dFnNat_eq : dFnNat = 5 := rfl
theorem dFnNum_eq : dFnNum = 105 := rfl
theorem dTwo_eq : dTwo = 112 := rfl
theorem dVar_eq : dVar = 5 := rfl
theorem dDo_eq : dDo = 105 := rfl
theorem dRedex_eq : dRedex = 105 := rfl
theorem dPinNat_eq : dPinNat = 10 := rfl
