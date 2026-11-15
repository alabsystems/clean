section
variable (p : Prop)
theorem own (x : α) (hp : p) : x = x := rfl
end
theorem use : (3 : Nat) = 3 := @own Nat True 3 True.intro
