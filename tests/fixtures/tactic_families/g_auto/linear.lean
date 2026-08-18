import Init

-- G-AUTO family fixture: `linarith` (10 probes) + `nlinarith` (2 probes).
-- Includes the non-unit coefficient frontier row (RC-C) and Int rows.

theorem canary_env_g_auto_linear (as : List Nat) : as.reverse.reverse = as :=
  List.reverse_reverse as

theorem p_auto_linarith_01 (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by linarith
theorem p_auto_linarith_02 (a b : Nat) (h : a < b) : a ≤ b := by linarith
theorem p_auto_linarith_03 (a b : Nat) (h : a + 2 ≤ b) : a < b := by linarith
theorem p_auto_linarith_04 (a : Nat) (h : 2 * a ≤ 4) : a ≤ 2 := by linarith
theorem p_auto_linarith_05 (a b c : Nat) (h1 : a ≤ b) (h2 : b < c) : a < c := by linarith
theorem p_auto_linarith_06 (a : Nat) (h1 : a < 3) (h2 : 3 < a) : False := by linarith
theorem p_auto_linarith_07 (a b : Int) (h : a ≤ b) : a - 1 ≤ b := by linarith
theorem p_auto_linarith_08 (a b : Int) (h1 : a < b) (h2 : b < a) : False := by linarith
theorem p_auto_linarith_09 (a b c : Nat) (h1 : a < b) (h2 : b ≤ c) : a < c := by linarith
theorem p_auto_linarith_10 (a b : Nat) (h : a ≤ b) : a ≤ b + 1 := by linarith
theorem p_auto_nlinarith_01 (a : Nat) : 0 ≤ a * a := by nlinarith
theorem p_auto_nlinarith_02 (a b : Nat) (h : a ≤ b) : a * a ≤ b * b := by nlinarith
