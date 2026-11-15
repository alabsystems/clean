-- Gap G23 brick B3: the Lean 4.8 core lemmas trust-ir's proofs name in simp
-- (judge j9, k8): Bool.and_eq_true, decide_eq_true_eq, Option.isSome_iff_exists.
theorem p1 (a b : Bool) (h : (a && b) = true) : a = true := by
  simp only [Bool.and_eq_true] at h
  exact h.1
theorem p2 (a b : Bool) : ((a && b) = true) = (a = true ∧ b = true) := Bool.and_eq_true a b
theorem o1 (x : Option Nat) (h : x.isSome = true) : ∃ y, x = some y := Option.isSome_iff_exists.mp h
theorem o4 (p : Prop) [Decidable p] (h : decide p = true) : p := by
  simp only [decide_eq_true_eq] at h
  exact h
