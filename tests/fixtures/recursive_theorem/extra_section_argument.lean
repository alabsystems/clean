section
variable (p : Prop)
theorem bad (hp : p) : ∀ n : Nat, p
  | 0 => hp
  | n + 1 => by exact bad p hp n
end
