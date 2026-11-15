unsafe theorem bad : ∀ n : Nat, n = n
  | 0 => rfl
  | n + 1 => by exact congrArg Nat.succ (bad n)
