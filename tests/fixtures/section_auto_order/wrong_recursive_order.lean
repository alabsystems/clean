section
variable (p : Prop)
theorem recursiveOwn (x : α) (hp : p) : ∀ n : Nat, x = x
 | 0 => rfl
 | n + 1 => by exact @recursiveOwn α x hp n
end
theorem bad : (3 : Nat) = 3 := @recursiveOwn Nat True 3 True.intro 2
