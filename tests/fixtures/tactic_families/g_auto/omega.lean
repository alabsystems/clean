import Init

-- G-AUTO family fixture: `omega` (20 probes).
-- Mix follows the 2026-07-29 measurement: transitivity chains, the Nat
-- subtraction family (sub_add_cancel / add_sub_cancel shapes), the non-unit
-- coefficient frontier (RC-C), `≠`-position rows, and Int rows.

theorem canary_env_g_auto_omega (as : List Nat) : as.reverse.reverse = as :=
  List.reverse_reverse as

theorem p_auto_omega_01 (a b c : Nat) (h1 : a < b) (h2 : b < c) : a < c := by omega
theorem p_auto_omega_02 (a b : Nat) (h : b ≤ a) : b + (a - b) = a := by omega
theorem p_auto_omega_03 (a b : Nat) : (a + b) - a = b := by omega
theorem p_auto_omega_04 (a : Nat) : a - a = 0 := by omega
theorem p_auto_omega_05 (a b : Nat) : a - b ≤ a := by omega
theorem p_auto_omega_06 (a : Nat) : a - 0 = a := by omega
theorem p_auto_omega_07 (a b : Nat) : a + b - b = a := by omega
theorem p_auto_omega_08 (a : Nat) : 0 + a = a := by omega
theorem p_auto_omega_09 (a : Nat) (h : 2 * a ≤ 4) : a ≤ 2 := by omega
theorem p_auto_omega_10 (a b : Nat) (h : a + 1 ≤ b) : a < b := by omega
theorem p_auto_omega_11 (a b : Nat) (h1 : a ≠ b) (h2 : a ≤ b) : a < b := by omega
theorem p_auto_omega_12 (a b : Int) (h : a ≤ b) : a - 1 ≤ b := by omega
theorem p_auto_omega_13 (a : Int) : a + 0 = a := by omega
theorem p_auto_omega_14 (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by omega
theorem p_auto_omega_15 (a : Nat) (h : a + 1 ≤ 0) : False := by omega
theorem p_auto_omega_16 (a : Nat) : a < a + 1 := by omega
theorem p_auto_omega_17 (a b : Nat) (h : a + b = 0) : a = 0 := by omega
theorem p_auto_omega_18 (a : Nat) (h1 : a ≤ 5) (h2 : 5 ≤ a) : a = 5 := by omega
theorem p_auto_omega_19 (a : Nat) (h : 3 < a) : 4 ≤ a := by omega
theorem p_auto_omega_20 (a b : Nat) (h : a = b + 2) : b < a := by omega
