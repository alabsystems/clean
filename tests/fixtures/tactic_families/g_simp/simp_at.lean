import Init

-- G-SIMP family fixture: `simp at h` / `simp at *` (12) + `simp_all` (10).
-- Row 21 (`simp_all only [...]`) is an RC-I argument-surface row.

-- Environment canary. BOTH facts are absent from Clean's builtin/stub prelude and
-- present in real Init, so this declaration fails unless `import Init` genuinely
-- loaded. Its discriminating power is re-proved on every run rather than assumed
-- (family_gate.py --canary-check); the previous single-fact canary
-- `List.reverse_reverse` was silently disarmed on 2026-08-23 by 3df6e4aad, which
-- registered a kernel-proved copy of it INTO the builtin prelude.
theorem canary_env_g_simp_at (as bs : List Nat) (n m : Nat) :
    (as ++ bs).reverse = bs.reverse ++ as.reverse ∧ n.succ - m.succ = n - m :=
  And.intro (List.reverse_append as bs) (Nat.succ_sub_succ_eq_sub n m)

theorem p_simp_at_01 (a : Nat) (h : a + 0 = 5) : a = 5 := by
  simp at h
  exact h

theorem p_simp_at_02 (a : Nat) (h : 0 + a = 5) : a = 5 := by
  simp at h
  exact h

theorem p_simp_at_03 (a : Nat) (h : a * 1 = 5) : a = 5 := by
  simp at h
  exact h

theorem p_simp_at_04 (l : List Nat) (h : l ++ [] = [1]) : l = [1] := by
  simp at h
  exact h

theorem p_simp_at_05 (p : Prop) (h : p ∧ True) : p := by
  simp at h
  exact h

theorem p_simp_at_06 (a : Bool) (h : (a && true) = false) : a = false := by
  simp at h
  exact h

theorem p_simp_at_07 (a : Nat) (h : a + 0 = 5) (h2 : a = 5 → a < 6) : a < 6 := by
  simp at h
  exact h2 h

theorem p_simp_at_08 (a b : Nat) (h1 : a + 0 = b) (h2 : b + 0 = 3) : a = 3 := by
  simp at h1 h2
  exact Eq.trans h1 h2

theorem p_simp_at_09 (a : Nat) (h : a + 0 = 2) : a + 0 = 2 := by
  simp at *
  exact h

theorem p_simp_at_10 (a : Nat) (h : ¬(a + 0 = a)) : False := by
  simp at h

theorem p_simp_at_11 (l : List Nat) (h : l.reverse.reverse = [2]) : l = [2] := by
  simp at h
  exact h

theorem p_simp_at_12 (a : Nat) (h : (if True then a else 0) = 3) : a = 3 := by
  simp at h
  exact h

theorem p_simp_all_01 (a : Nat) (h : a + 0 = 5) : a = 5 := by simp_all
theorem p_simp_all_02 (p q : Prop) (hp : p) (h : p → q) : q := by simp_all
theorem p_simp_all_03 (a b : Nat) (h1 : a + 0 = b) (h2 : b = 3) : a = 3 := by simp_all
theorem p_simp_all_04 (p : Prop) (h : p ∧ True) : p := by simp_all
theorem p_simp_all_05 (a : Bool) (h : (a && true) = true) : a = true := by simp_all
theorem p_simp_all_06 (l : List Nat) (h : l ++ [] = []) : l = [] := by simp_all
theorem p_simp_all_07 (p q : Prop) (hpq : p ∧ q) : q := by simp_all
theorem p_simp_all_08 (a : Nat) (h1 : a = 2) (h2 : a + 0 = 2) : True := by simp_all
theorem p_simp_all_09 (a : Nat) (h : a + 0 = 5) : a = 5 := by simp_all only [Nat.add_zero]
theorem p_simp_all_10 (p : Prop) (h : ¬p) (hp : p) : False := by simp_all
