-- B4 twin over two matched columns: `h : both (k + 1) 0 = true` is not the
-- goal `k + 1 = 0`.
def both : Nat → Nat → Bool
  | 0, 0 => true
  | _, _ => false

theorem both_zero_twin : ∀ (n i : Nat), both n i = true → n = 0
  | 0, _, _ => rfl
  | _ + 1, 0, h => h
  | _ + 1, _ + 1, h => Bool.noConfusion h
