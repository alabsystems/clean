def polyPick {α : Type u} : List α → Nat → Option α
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: xs, i + 1 => polyPick xs i

theorem polyPick_step {α : Type u} (x : α) (xs : List α) (i : Nat)
    (h : polyPick xs i = none) : polyPick (x :: xs) (Nat.succ i) = none := by
  simp only [polyPick, h]

theorem polyPick_levels (x : Nat) (X : Type u) :
    polyPick [x] 0 = some x ∧ polyPick [X] 0 = some X := by
  constructor <;> simp only [polyPick]
