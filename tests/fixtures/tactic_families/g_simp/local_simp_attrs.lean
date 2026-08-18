import Init

-- G-SIMP family fixture: in-file `@[simp]` attribute lemmas (10 probes).
-- The 2026-07-29 measurement found in-file `@[simp]` lemmas picked up
-- immediately (the discriminator that isolated RC-B). Rows 04/05/10 are the
-- RC-J conditional-rewriting class (premise discharge landed 2026-08-02,
-- commit 68b867935). The four `ls*` declarations are helpers, not probes.

theorem canary_env_g_simp_local_attrs (as : List Nat) : as.reverse.reverse = as :=
  List.reverse_reverse as

/-- Helper (not a probe): definition unfolded by the local simp set. -/
def lsf (n : Nat) : Nat := n + 1

@[simp] theorem lsf_eq (n : Nat) : lsf n = n + 1 := rfl

@[simp] theorem ls_cond (a b : Nat) (h : b ≤ a) : a - b + b = a := Nat.sub_add_cancel h

theorem ls_plain (n : Nat) : lsf n = n + 1 := rfl

theorem p_simp_local_01 : lsf 3 = 4 := by simp
theorem p_simp_local_02 (n : Nat) : lsf n = n + 1 := by simp
theorem p_simp_local_03 (n : Nat) : lsf (lsf n) = n + 1 + 1 := by simp
theorem p_simp_local_04 (a b : Nat) (h : b ≤ a) : a - b + b = a := by simp [h]
theorem p_simp_local_05 (a b : Nat) (h : b ≤ a) : a - b + b = a := by simp only [ls_cond, h]
theorem p_simp_local_06 (n : Nat) : lsf n = n + 1 := by simp only [ls_plain]
theorem p_simp_local_07 (l : List Nat) : (l.map lsf).length = l.length := by simp
theorem p_simp_local_08 : lsf 0 = 1 := by simp
theorem p_simp_local_09 (n : Nat) (h : lsf n = 5) : n + 1 = 5 := by
  simp at h
  exact h
theorem p_simp_local_10 (a : Nat) : a - a + a = a := by simp
