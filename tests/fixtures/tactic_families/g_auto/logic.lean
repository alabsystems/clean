import Init

-- G-AUTO family fixture: `aesop` (18 probes) + `tauto` (16 probes).
-- Propositional/structural goals per the 2026-07-29 family description
-- (aesop 15/19, tauto 9/16 measured then). Classical rows (`p ∨ ¬p`,
-- `¬¬p → p`) are deliberate frontier rows.

theorem canary_env_g_auto_logic (as : List Nat) : as.reverse.reverse = as :=
  List.reverse_reverse as

theorem p_auto_aesop_01 (p : Prop) (h : p) : p := by aesop
theorem p_auto_aesop_02 (p q : Prop) (h : p ∧ q) : q ∧ p := by aesop
theorem p_auto_aesop_03 (p q : Prop) (h : p ∨ q) : q ∨ p := by aesop
theorem p_auto_aesop_04 (p q : Prop) (hp : p) (hq : q) : p ∧ q := by aesop
theorem p_auto_aesop_05 (p q : Prop) (h : p → q) (hp : p) : q := by aesop
theorem p_auto_aesop_06 (p : Prop) : p → p := by aesop
theorem p_auto_aesop_07 (p q r : Prop) (h1 : p → q) (h2 : q → r) : p → r := by aesop
theorem p_auto_aesop_08 (p : Prop) (h : p ∧ ¬p) : False := by aesop
theorem p_auto_aesop_09 : True := by aesop
theorem p_auto_aesop_10 : ¬False := by aesop
theorem p_auto_aesop_11 (p q : Prop) (h : ¬(p ∨ q)) : ¬p := by aesop
theorem p_auto_aesop_12 : ∃ n : Nat, n = 1 := by aesop
theorem p_auto_aesop_13 (p : Nat → Prop) (h : ∀ n, p n) : p 3 := by aesop
theorem p_auto_aesop_14 (p q : Prop) (h : p ↔ q) (hp : p) : q := by aesop
theorem p_auto_aesop_15 (a b : Nat) (h : a = b) : b = a := by aesop
theorem p_auto_aesop_16 (xs : List Nat) (h : xs = []) : xs.length = 0 := by aesop
theorem p_auto_aesop_17 (o : Option Nat) (h : o = none) : o.isNone = true := by aesop
theorem p_auto_aesop_18 (p q r : Prop) (h : p ∧ (q ∧ r)) : (p ∧ q) ∧ r := by aesop
theorem p_auto_tauto_01 (p : Prop) : p → p := by tauto
theorem p_auto_tauto_02 (p q : Prop) : p ∧ q → p := by tauto
theorem p_auto_tauto_03 (p q : Prop) : p ∧ q → q := by tauto
theorem p_auto_tauto_04 (p : Prop) : ¬(p ∧ ¬p) := by tauto
theorem p_auto_tauto_05 (p q : Prop) : (p → q) → ¬q → ¬p := by tauto
theorem p_auto_tauto_06 (p : Prop) : p ∨ ¬p := by tauto
theorem p_auto_tauto_07 (p : Prop) : p → ¬¬p := by tauto
theorem p_auto_tauto_08 (p : Prop) : ¬¬p → p := by tauto
theorem p_auto_tauto_09 (p q : Prop) : (p ∨ q) → (q ∨ p) := by tauto
theorem p_auto_tauto_10 (p q : Prop) : (p ∧ q) ↔ (q ∧ p) := by tauto
theorem p_auto_tauto_11 (p q r : Prop) : (p → q ∧ r) → (p → q) := by tauto
theorem p_auto_tauto_12 (p : Prop) : False → p := by tauto
theorem p_auto_tauto_13 (p : Prop) : p → True := by tauto
theorem p_auto_tauto_14 (p q : Prop) : (p ↔ q) → (p → q) := by tauto
theorem p_auto_tauto_15 (p q : Prop) : ((p ∨ q) ∧ ¬p) → q := by tauto
theorem p_auto_tauto_16 (p q : Prop) : (p → q) ∨ (q → p) := by tauto
