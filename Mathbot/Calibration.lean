/-!
Executable R0 calibration fixtures.

These are intentionally small. Their role is to prove that the local Lean/Lake
path, target manifest, and Rust audit runner can distinguish verified positive
fixtures from expected-failing negative controls.
-/

set_option autoImplicit false

namespace Mathbot.Calibration

theorem c1_tiny_farkas_replay (x : Nat) (h : 1 ≤ x) : 0 ≤ x := by
  exact Nat.le_trans (Nat.zero_le 1) h

theorem c2_one_step_induction
    (P : Nat → Prop) (h0 : P 0) (hstep : ∀ n, P n → P (n + 1)) : P 1 := by
  exact hstep 0 h0

theorem c3_xor_parity_unsat (b : Bool) (h0 : b = false) (h1 : b = true) : False := by
  cases b <;> simp at h0 h1

end Mathbot.Calibration
