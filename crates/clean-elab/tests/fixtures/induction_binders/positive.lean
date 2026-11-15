theorem implicitIH (n : Nat) {i : Nat} (h : i = 0) : i = 0 := by
  induction n generalizing i with
  | zero => exact h
  | succ n ih => exact ih h

theorem explicitIH (n : Nat) (i : Nat) (h : i = 0) : i = 0 := by
  induction n generalizing i with
  | zero => exact h
  | succ n ih => exact ih i h

theorem strictIH (n : Nat) ⦃i : Nat⦄ (h : i = 0) : i = 0 := by
  induction n generalizing i with
  | zero => exact h
  | succ n ih => exact ih h

theorem introducedIH (n : Nat) : ∀ {i : Nat}, i = 0 → i = 0 := by
  intro i h
  induction n generalizing i with
  | zero => exact h
  | succ n ih => exact ih h


theorem lambdaIH (n : Nat) : ∀ {i : Nat}, i = 0 → i = 0 := fun {i} h => by
  induction n generalizing i with
  | zero => exact h
  | succ n ih => exact ih h

theorem substitutedIH (k n : Nat) (e : n = 0) {i : n = 0} (h : i = i) : i = i := by
  subst n
  induction k generalizing i with
  | zero => exact h
  | succ k ih => exact ih h
