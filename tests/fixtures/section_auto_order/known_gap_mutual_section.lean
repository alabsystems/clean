section
variable (p : Prop)
mutual
 theorem mutualOwn (x : α) (hp : p) : x = x := rfl
end
end
theorem use : (3 : Nat) = 3 := @mutualOwn True Nat 3 True.intro
