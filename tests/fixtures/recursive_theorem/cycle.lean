theorem bad : ∀ n : Nat, False
  | 0 => by exact bad 0
  | n + 1 => by exact bad n
