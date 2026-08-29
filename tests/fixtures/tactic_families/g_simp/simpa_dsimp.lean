import Init

-- G-SIMP family fixture: `simpa` (10) + `dsimp` (10).
-- dsimp rows include the RC-F finisher class (dsimp must close a goal that
-- becomes reflexive after definitional simplification — T4).

-- Environment canary. BOTH facts are absent from Clean's builtin/stub prelude and
-- present in real Init, so this declaration fails unless `import Init` genuinely
-- loaded. Its discriminating power is re-proved on every run rather than assumed
-- (family_gate.py --canary-check); the previous single-fact canary
-- `List.reverse_reverse` was silently disarmed on 2026-08-23 by 3df6e4aad, which
-- registered a kernel-proved copy of it INTO the builtin prelude.
theorem canary_env_g_simp_simpa_dsimp (as bs : List Nat) (n m : Nat) :
    (as ++ bs).reverse = bs.reverse ++ as.reverse ∧ n.succ - m.succ = n - m :=
  And.intro (List.reverse_append as bs) (Nat.succ_sub_succ_eq_sub n m)

theorem p_simpa_01 (a : Nat) (h : a + 0 = 5) : a = 5 := by simpa using h
theorem p_simpa_02 (a : Nat) (h : a = 5) : a + 0 = 5 := by simpa
theorem p_simpa_03 (p : Prop) (h : p ∧ True) : p := by simpa using h
theorem p_simpa_04 (l : List Nat) (h : l ++ [] = [1]) : l = [1] := by simpa using h
theorem p_simpa_05 (a : Bool) (h : (a && true) = true) : a = true := by simpa using h
theorem p_simpa_06 (a : Nat) (h : 0 + a = 5) : a = 5 := by simpa using h
theorem p_simpa_07 (p q : Prop) (h : (True ∧ p) ∧ q) : p ∧ q := by simpa using h
theorem p_simpa_08 (n : Nat) (h : n * 1 = 7) : n = 7 := by simpa using h
theorem p_simpa_09 (l : List Nat) (h : l.reverse.reverse = [3]) : l = [3] := by simpa using h
theorem p_simpa_10 (a : Nat) : a + 0 = a := by simpa

theorem p_dsimp_01 : ((fun x : Nat => x) 5) = 5 := by dsimp
theorem p_dsimp_02 (n : Nat) : (fun x : Nat => x + 0) n = n + 0 := by dsimp
theorem p_dsimp_03 (n : Nat) : id n = n := by dsimp only [id]
theorem p_dsimp_04 (p : Prop) (h : p) : id p := by
  dsimp only [id]
  exact h
theorem p_dsimp_05 : ((fun (a b : Nat) => a + b) 2 3) = 5 := by dsimp
theorem p_dsimp_06 (n : Nat) : (let m := n; m + 0) = n + 0 := by dsimp
theorem p_dsimp_07 (n : Nat) : ((fun x : Nat => x) ∘ (fun x : Nat => x)) n = n := by dsimp [Function.comp]
theorem p_dsimp_08 : (2 : Nat) + 3 = 5 := by dsimp
theorem p_dsimp_09 (n : Nat) : (n, 3).1 = n := by dsimp
theorem p_dsimp_10 (n : Nat) : (fun x : Nat => (fun y : Nat => x + y)) 2 3 = 2 + 3 := by dsimp
