namespace PublicMetadata
section
variable (p : Prop)
private theorem equationOwn (x : α) (hp : p) : ∀ n : Nat, x = x
 | 0 => rfl
 | n + 1 => by rfl
end
theorem equationNamed (n : Nat) : (3 : Nat) = 3 := equationOwn (p := True) (α := Nat) (x := 3) (hp := True.intro) n
end PublicMetadata
