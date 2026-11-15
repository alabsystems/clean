inductive Checked : List Nat → Prop where
  | mk {xs : List Nat} : xs.length = 0 → Checked xs

theorem checked_zero {xs : List Nat} (h : Checked xs) : xs.length = 0 := by
  cases h
  case mk h => exact h

theorem partial_nat (n : Nat) : n = n := by
  induction n
  case zero => rfl
  case succ ih => exact congrArg Nat.succ ih

theorem full_nat (n : Nat) : n = n := by
  induction n
  case zero => rfl
  case succ k ih => exact congrArg Nat.succ ih

theorem alternative_prefix (n : Nat) : n = n := by
  induction n with
  | zero => rfl
  | succ k =>
    rename_i ih
    exact congrArg Nat.succ ih

theorem earlier_field (x y : Nat) : x = x := by
  cases x
  case zero => rfl
  case succ =>
    cases y
    case zero h => exact congrArg Nat.succ (Eq.refl h)
    case succ h k => exact congrArg Nat.succ (Eq.refl h)
