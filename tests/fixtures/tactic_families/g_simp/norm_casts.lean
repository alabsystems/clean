import Init

-- G-SIMP family fixture: the simp-family normalization tokens —
-- `norm_num` (10) + `push_cast` (5) + `field_simp` (5), per the §3 simp
-- family token list. norm_num also appears in the automation family (the
-- 2026-07-29 plan lists it in both); comparison stays family-count-level.
-- Rows with lemma/hypothesis arguments are RC-I argument-surface rows.

theorem canary_env_g_simp_norm_casts (as : List Nat) : as.reverse.reverse = as :=
  List.reverse_reverse as

theorem p_simp_norm_num_01 : (2 : Nat) + 2 = 4 := by norm_num
theorem p_simp_norm_num_02 : (10 : Nat) * 10 = 100 := by norm_num
theorem p_simp_norm_num_03 : (2 : Nat) ≤ 3 := by norm_num
theorem p_simp_norm_num_04 : ¬((3 : Nat) = 4) := by norm_num
theorem p_simp_norm_num_05 (a : Nat) (h : a = 3) : a + 1 = 4 := by norm_num [h]
theorem p_simp_norm_num_06 : (7 : Nat) - 3 = 4 := by norm_num
theorem p_simp_norm_num_07 : (2 : Int) + 2 = 4 := by norm_num
theorem p_simp_norm_num_08 : (1 : Int) < 2 := by norm_num
theorem p_simp_norm_num_09 : (6 : Nat) / 2 = 3 := by norm_num
theorem p_simp_norm_num_10 : (2 : Nat) ^ 4 = 16 := by norm_num

theorem p_simp_push_cast_01 (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by push_cast
theorem p_simp_push_cast_02 (a b : Nat) (h : (a : Int) + (b : Int) = 5) : ((a + b : Nat) : Int) = 5 := by
  push_cast
  exact h
theorem p_simp_push_cast_03 (a : Nat) : ((a * 2 : Nat) : Int) = (a : Int) * 2 := by push_cast
theorem p_simp_push_cast_04 (a b : Nat) (h : ((a + b : Nat) : Int) = 5) : (a : Int) + (b : Int) = 5 := by
  push_cast at h
  exact h
theorem p_simp_push_cast_05 (a : Nat) : ((a + 0 : Nat) : Int) = (a : Int) := by push_cast

theorem p_simp_field_simp_01 (a b : Nat) (h : b ≠ 0) : a * b / b = a := by field_simp
theorem p_simp_field_simp_02 (a : Nat) (h : a ≠ 0) : a / a = 1 := by field_simp
theorem p_simp_field_simp_03 (a : Nat) : a / 1 = a := by field_simp
theorem p_simp_field_simp_04 (a b : Nat) (hb : b ≠ 0) : (a * b) / b + 0 = a := by field_simp
theorem p_simp_field_simp_05 (a b c : Nat) (hc : c ≠ 0) (h : a * c / c = b) : a = b := by
  field_simp at h
  exact h
