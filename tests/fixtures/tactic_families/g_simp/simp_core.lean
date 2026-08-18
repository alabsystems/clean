import Init

-- G-SIMP family fixture: bare `simp` (30 probes).
-- Reconstruction of the 2026-07-29 simp family
-- (docs/plans/TACTICS_TO_100_2026-07-29.md §3, 127 probe declarations) at
-- FAMILY-COUNT level, not probe-identical. Covers the shapes the July run
-- measured as working (arith normalization, rewriting under binders, inside
-- `List.map`, under `∀`, funext, congruence) plus the imported-lemma frontier
-- (`l ++ [] = l`, `l.reverse.reverse = l` need the imported `@[simp]` set —
-- RC-B — or a universe-polymorphic builtin route — RC-E).

theorem canary_env_g_simp_core (as : List Nat) : as.reverse.reverse = as :=
  List.reverse_reverse as

theorem p_simp_core_01 (n : Nat) : n + 0 = n := by simp
theorem p_simp_core_02 (n : Nat) : 0 + n = n := by simp
theorem p_simp_core_03 (n : Nat) : n * 1 = n := by simp
theorem p_simp_core_04 (n : Nat) : 1 * n = n := by simp
theorem p_simp_core_05 (n : Nat) : n + 0 + 0 = n := by simp
theorem p_simp_core_06 : (fun x : Nat => x + 0) = (fun x : Nat => x) := by simp
theorem p_simp_core_07 : ∀ n : Nat, n + 0 = n := by simp
theorem p_simp_core_08 (l : List Nat) : l.map (fun x => x + 0) = l.map (fun x => x) := by simp
theorem p_simp_core_09 (l : List Nat) : l ++ [] = l := by simp
theorem p_simp_core_10 (l : List Nat) : [] ++ l = l := by simp
theorem p_simp_core_11 (a : Bool) : (a && true) = a := by simp
theorem p_simp_core_12 (a : Bool) : (true && a) = a := by simp
theorem p_simp_core_13 (a : Bool) : (a || false) = a := by simp
theorem p_simp_core_14 (a : Bool) : (false || a) = a := by simp
theorem p_simp_core_15 (a : Bool) : (a && a) = a := by simp
theorem p_simp_core_16 (a b : Nat) : (if True then a else b) = a := by simp
theorem p_simp_core_17 (a b : Nat) : (if False then a else b) = b := by simp
theorem p_simp_core_18 : ([1, 2, 3] : List Nat).length = 3 := by simp
theorem p_simp_core_19 (a : Nat) (h : a = 5) : a + 0 = 5 := by simp [h]
theorem p_simp_core_20 : (some 3 : Option Nat).isSome = true := by simp
theorem p_simp_core_21 (p : Prop) : (True ∧ p) ↔ p := by simp
theorem p_simp_core_22 (p : Prop) : (p ∨ False) ↔ p := by simp
theorem p_simp_core_23 (p : Prop) : (p ∧ False) ↔ False := by simp
theorem p_simp_core_24 (l : List Nat) : l.reverse.reverse = l := by simp
theorem p_simp_core_25 (n : Nat) : (n = n) ↔ True := by simp
theorem p_simp_core_26 (n : Nat) : n - 0 = n := by simp
theorem p_simp_core_27 (l : List Nat) (a : Nat) : (a :: l).length = l.length + 1 := by simp
theorem p_simp_core_28 (f : Nat → Nat) (l : List Nat) : (l.map f).length = l.length := by simp
theorem p_simp_core_29 (p : Prop) (hp : p) : p ∧ True := by simp [hp]
theorem p_simp_core_30 (a b : Bool) : (a && (a && b)) = (a && b) := by simp
