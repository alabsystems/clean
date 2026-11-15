section
variable (p : α → Prop)
theorem bad (x : α) (y : β) (hp : p x) : ∀ n : Nat, y = y
  | 0 => rfl
  | n + 1 => by exact @bad x y hp n
end
