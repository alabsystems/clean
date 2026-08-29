import Init

-- G-AUTO family fixture: `linarith` (10 probes) + `nlinarith` (2 probes).
-- Includes the non-unit coefficient frontier row (RC-C) and Int rows.

-- Environment canary. BOTH facts are absent from Clean's builtin/stub prelude and
-- present in real Init, so this declaration fails unless `import Init` genuinely
-- loaded. Its discriminating power is re-proved on every run rather than assumed
-- (family_gate.py --canary-check); the previous single-fact canary
-- `List.reverse_reverse` was silently disarmed on 2026-08-23 by 3df6e4aad, which
-- registered a kernel-proved copy of it INTO the builtin prelude.
theorem canary_env_g_auto_linear (as bs : List Nat) (n m : Nat) :
    (as ++ bs).reverse = bs.reverse ++ as.reverse ∧ n.succ - m.succ = n - m :=
  And.intro (List.reverse_append as bs) (Nat.succ_sub_succ_eq_sub n m)

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
