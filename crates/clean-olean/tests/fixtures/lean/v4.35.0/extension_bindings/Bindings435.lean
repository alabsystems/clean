prelude
import Init.Data.UInt.Basic

namespace Bindings435

def divAlias := Nat.div
def modAlias := Nat.mod
def charAlias := Char.ofNat

theorem divZero : Nat.div 37 0 = 0 := rfl
theorem modZero : Nat.mod 37 0 = 37 := rfl
theorem divLarge : Nat.div 1267650600228229401496703205395 3 =
    422550200076076467165567735131 := rfl
theorem modLarge : Nat.mod 1267650600228229401496703205395 3 = 2 := rfl
theorem divMax : Nat.div 340282366920938463463374607431768211455
    18446744073709551617 = 18446744073709551615 := rfl
theorem modMax : Nat.mod 340282366920938463463374607431768211455
    18446744073709551617 = 0 := rfl
theorem charSurrogate : Char.toNat (Char.ofNat 0xd800) = 0 := rfl
theorem charUpper : Char.toNat (Char.ofNat 0x10ffff) = 0x10ffff := rfl
theorem charBeyond : Char.toNat (Char.ofNat 0x110000) = 0 := rfl
theorem stringOrder : String.ofList
    (List.cons (Char.ofNat 97) (List.cons (Char.ofNat 98) List.nil)) = "ab" := rfl

#print axioms divZero
#print axioms modZero
#print axioms divLarge
#print axioms modLarge
#print axioms divMax
#print axioms modMax
#print axioms charSurrogate
#print axioms charUpper
#print axioms charBeyond
#print axioms stringOrder

end Bindings435
