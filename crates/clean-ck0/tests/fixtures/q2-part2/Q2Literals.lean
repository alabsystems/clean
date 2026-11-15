import Init

def q2BigNat : Nat := 10000000000000000000000000000000000000000
theorem q2BigNatSelf : q2BigNat = 10000000000000000000000000000000000000000 := rfl

theorem q2NatAdd : Nat.add 7 9 = 16 := rfl
theorem q2NatSub : Nat.sub 7 9 = 0 := rfl
theorem q2NatMul : Nat.mul 7 9 = 63 := rfl
theorem q2NatDiv : Nat.div 19 3 = 6 := rfl
theorem q2NatMod : Nat.mod 19 3 = 1 := rfl
theorem q2NatPow : Nat.pow 3 4 = 81 := rfl
theorem q2NatBeq : Nat.beq 7 9 = false := rfl
theorem q2NatBle : Nat.ble 7 9 = true := rfl
theorem q2NatGcd : Nat.gcd 48 18 = 6 := rfl
theorem q2NatLand : Nat.land 5 3 = 1 := rfl
theorem q2NatLor : Nat.lor 5 3 = 7 := rfl
theorem q2NatXor : Nat.xor 5 3 = 6 := rfl
theorem q2NatShiftLeft : Nat.shiftLeft 3 4 = 48 := rfl
theorem q2NatShiftRight : Nat.shiftRight 19 2 = 4 := rfl

theorem q2StringLiteral : "aλ🙂" = String.ofList [Char.ofNat 97, Char.ofNat 955, Char.ofNat 128578] := rfl

theorem q2ChoiceUse (α : Sort u) (h : Nonempty α) : Nonempty α := ⟨Classical.choice h⟩
theorem q2PropextUse (p q : Prop) (h : p ↔ q) : p = q := propext h
