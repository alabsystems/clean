section
variable (p : Prop)
theorem bad (x : α) (hp : p) : ∀ n : Nat, x = x
  | 0 => rfl
  | n + 1 => by exact @bad x hp n
end
