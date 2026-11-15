-- Brick B4, class (88): an equation-form theorem whose LAST column is a
-- hypothesis typed by the earlier ones. Lean generalizes it into the
-- case split's motive, so in each arm `h` is about that arm's constructor.
def isZ : Nat → Bool
  | 0 => true
  | _ + 1 => false

theorem one_dep : ∀ n : Nat, isZ n = true → n = 0
  | 0, _ => rfl
  | _ + 1, h => absurd h (fun h' => Bool.noConfusion h')

theorem lead_param (k : Nat) : ∀ n : Nat, isZ n = true → n + k = k
  | 0, _ => Nat.zero_add k
  | _ + 1, h => absurd h (fun h' => Bool.noConfusion h')

def both : Nat → Nat → Bool
  | 0, 0 => true
  | _, _ => false

theorem both_zero : ∀ (n i : Nat), both n i = true → n = 0
  | 0, _, _ => rfl
  | _ + 1, 0, h => Bool.noConfusion h
  | _ + 1, _ + 1, h => Bool.noConfusion h
