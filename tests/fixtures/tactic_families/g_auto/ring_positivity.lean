import Init

-- G-AUTO family fixture: `ring` (4) + `positivity` (6) + `gcongr` (4).
-- positivity was 0/6 on 2026-07-29 (registered stub, RC-M/T15); gcongr was
-- 0/4 (RC-N, side-goal discharge landed 2026-08-06). These rows measure
-- whether those landed fixes moved the family.

theorem canary_env_g_auto_ring_positivity (as : List Nat) : as.reverse.reverse = as :=
  List.reverse_reverse as

theorem p_auto_ring_01 (a b : Nat) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring
theorem p_auto_ring_02 (a : Nat) : 0 + a = a := by ring
theorem p_auto_ring_03 (a b : Nat) : a + b = b + a := by ring
theorem p_auto_ring_04 (a b c : Nat) : a * (b + c) = a * b + a * c := by ring
theorem p_auto_positivity_01 : (0 : Nat) < 1 := by positivity
theorem p_auto_positivity_02 (n : Nat) : 0 ≤ n := by positivity
theorem p_auto_positivity_03 (n : Nat) : 0 < n + 1 := by positivity
theorem p_auto_positivity_04 (n : Nat) : 0 ≤ n * n := by positivity
theorem p_auto_positivity_05 (a b : Nat) (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by positivity
theorem p_auto_positivity_06 (n : Nat) : 0 ≤ n + 3 := by positivity
theorem p_auto_gcongr_01 (a b : Nat) (h : a ≤ b) : a + 1 ≤ b + 1 := by gcongr
theorem p_auto_gcongr_02 (a b c : Nat) (h : a ≤ b) : a + c ≤ b + c := by gcongr
theorem p_auto_gcongr_03 (a b c : Nat) (h : a ≤ b) : c + a ≤ c + b := by gcongr
theorem p_auto_gcongr_04 (a b c d : Nat) (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d := by gcongr
