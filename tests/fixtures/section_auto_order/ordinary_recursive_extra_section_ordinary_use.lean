section
variable (p : Prop)
def recOwn (x : α) (hp : p) : Nat → α
 | 0 => x
 | n + 1 => recOwn p x hp n
end
theorem use : recOwn True 3 True.intro 2 = 3 := rfl
