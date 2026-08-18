import Init

-- G-AUTO family fixture: `norm_num` (15 probes).
-- Rows 01/05/06 are the designated RC-A teeth rows: reverting the
-- `use super::decide::eval_decide as decide;` import in
-- crates/clean-elab/src/tactic/norm_num.rs back to `super::smt::decide`
-- flips them to `SmtFailed { tactic: "decide", detail: "found counterexample
-- — goal is not valid" }` (see scripts/tactic_parity/TEETH.md).

theorem canary_env_g_auto_norm_num (as : List Nat) : as.reverse.reverse = as :=
  List.reverse_reverse as

theorem p_auto_norm_num_01 : (2 : Nat) ≤ 3 := by norm_num
theorem p_auto_norm_num_02 : (2 : Nat) + 2 = 4 := by norm_num
theorem p_auto_norm_num_03 : (3 : Nat) * 4 = 12 := by norm_num
theorem p_auto_norm_num_04 : (10 : Nat) - 4 = 6 := by norm_num
theorem p_auto_norm_num_05 : ¬((3 : Nat) = 4) := by norm_num
theorem p_auto_norm_num_06 : (0 : Nat) < 1 := by norm_num
theorem p_auto_norm_num_07 : (1 : Nat) + 1 < 4 := by norm_num
theorem p_auto_norm_num_08 : (12 : Nat) / 4 = 3 := by norm_num
theorem p_auto_norm_num_09 : (2 : Nat) ^ 3 = 8 := by norm_num
theorem p_auto_norm_num_10 (a : Nat) (h : a = 2) : a + 2 = 4 := by norm_num [h]
theorem p_auto_norm_num_11 : (100 : Nat) * 0 = 0 := by norm_num
theorem p_auto_norm_num_12 : (0 : Nat) + 37 = 37 := by norm_num
theorem p_auto_norm_num_13 : (5 : Nat) ≠ 7 := by norm_num
theorem p_auto_norm_num_14 : ((2 : Nat) + 3) * 4 = 20 := by norm_num
theorem p_auto_norm_num_15 : (1 : Int) + 1 = 2 := by norm_num
