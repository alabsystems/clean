section
variable (p : α → Prop)
theorem bad (x : α) (hp : p x) : ∀ n : Nat, p x
  | 0 => hp
  | n + 1 => by exact @bad α x hp n
end
