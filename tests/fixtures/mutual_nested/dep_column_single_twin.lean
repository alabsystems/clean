-- B4 twin: in the `n + 1` arm the hypothesis reads `isZ (n + 1) = true`,
-- not the goal `n + 1 = 0`.
def isZ : Nat → Bool
  | 0 => true
  | _ + 1 => false

theorem one_dep_twin : ∀ n : Nat, isZ n = true → n = 0
  | 0, _ => rfl
  | _ + 1, h => h
