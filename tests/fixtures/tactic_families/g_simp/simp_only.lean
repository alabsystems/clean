import Init

-- G-SIMP family fixture: `simp only [<imported lemma>]` (25 probes).
-- Rows 01-15 use MONOMORPHIC imported lemmas (the class measured working on
-- 2026-07-29, e.g. `simp only [Bool.and_self_left]` PASSED under import
-- Init). Rows 16-25 use UNIVERSE-POLYMORPHIC imported lemmas — the RC-E
-- class (1/10 before the fix in 7936e3c17, 7/10 after) and the designated
-- G-SIMP teeth rows: restoring the hardcoded `u_simp` level in
-- crates/clean-elab/src/tactic/simp/expr.rs (`lemma_levels`) must flip ≥3
-- of them back to NoProgress (see scripts/tactic_parity/TEETH.md).

theorem canary_env_g_simp_only (as : List Nat) : as.reverse.reverse = as :=
  List.reverse_reverse as

theorem p_simp_only_01 (a b : Bool) : (a && (a && b)) = (a && b) := by simp only [Bool.and_self_left]
theorem p_simp_only_02 (n : Nat) : n + 0 = n := by simp only [Nat.add_zero]
theorem p_simp_only_03 (n : Nat) : 0 + n = n := by simp only [Nat.zero_add]
theorem p_simp_only_04 (n : Nat) : n * 1 = n := by simp only [Nat.mul_one]
theorem p_simp_only_05 (n : Nat) : 1 * n = n := by simp only [Nat.one_mul]
theorem p_simp_only_06 (n : Nat) : n - 0 = n := by simp only [Nat.sub_zero]
theorem p_simp_only_07 (n : Nat) : Nat.succ n = n + 1 := by simp only [Nat.succ_eq_add_one]
theorem p_simp_only_08 (a b c : Nat) : a + b + c = a + (b + c) := by simp only [Nat.add_assoc]
theorem p_simp_only_09 (a b : Nat) : a + b = b + a := by simp only [Nat.add_comm]
theorem p_simp_only_10 (b : Bool) : (b && true) = b := by simp only [Bool.and_true]
theorem p_simp_only_11 (b : Bool) : (true && b) = b := by simp only [Bool.true_and]
theorem p_simp_only_12 (b : Bool) : (b || false) = b := by simp only [Bool.or_false]
theorem p_simp_only_13 (b : Bool) : (false || b) = b := by simp only [Bool.false_or]
theorem p_simp_only_14 (b : Bool) : (!!b) = b := by simp only [Bool.not_not]
theorem p_simp_only_15 (b : Bool) : (b && b) = b := by simp only [Bool.and_self]
theorem p_simp_only_16 (as : List Nat) : as.reverse.reverse = as := by simp only [List.reverse_reverse]
theorem p_simp_only_17 (as : List Nat) : as.reverse.length = as.length := by simp only [List.length_reverse]
theorem p_simp_only_18 (as : List Nat) : as ++ [] = as := by simp only [List.append_nil]
theorem p_simp_only_19 (as : List Nat) : [] ++ as = as := by simp only [List.nil_append]
theorem p_simp_only_20 (as bs : List Nat) : (as ++ bs).length = as.length + bs.length := by simp only [List.length_append]
theorem p_simp_only_21 (f : Nat → Nat) (as : List Nat) : (as.map f).length = as.length := by simp only [List.length_map]
theorem p_simp_only_22 (f : Nat → Nat) (as bs : List Nat) : (as ++ bs).map f = as.map f ++ bs.map f := by simp only [List.map_append]
theorem p_simp_only_23 (as bs : List Nat) : (as ++ bs).reverse = bs.reverse ++ as.reverse := by simp only [List.reverse_append]
theorem p_simp_only_24 (as bs cs : List Nat) : as ++ bs ++ cs = as ++ (bs ++ cs) := by simp only [List.append_assoc]
theorem p_simp_only_25 (a : Nat) (as : List Nat) : [a] ++ as = a :: as := by simp only [List.singleton_append]
