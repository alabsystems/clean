import Init

-- G-AUTO family fixture: `grind` (14) + `cc` (2) + search tactics
-- `exact?` / `apply?` / `rw?` / `library_search` (10).
-- grind rows probe congruence closure (multi-arg, ∨-elimination, ¬¬,
-- definitional unfolding via the helper def); the search rows reproduce the
-- RC-O class (`a = a` with 93k constants loaded failed 2026-07-29).

theorem canary_env_g_auto_closure_search (as : List Nat) : as.reverse.reverse = as :=
  List.reverse_reverse as

/-- Helper for the grind definitional-unfolding probe (not a probe row). -/
def gsDouble (n : Nat) : Nat := n + n

theorem p_auto_grind_01 (f : Nat → Nat) (a b : Nat) (h : a = b) : f a = f b := by grind
theorem p_auto_grind_02 (f : Nat → Nat → Nat) (a b c : Nat) (h : a = b) : f a c = f b c := by grind
theorem p_auto_grind_03 (f : Nat → Nat) (a b : Nat) (h1 : a = b) (h2 : f b = 0) : f a = 0 := by grind
theorem p_auto_grind_04 (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by grind
theorem p_auto_grind_05 (f : Nat → Nat) (a b : Nat) (h : a = b) : f (f a) = f (f b) := by grind
theorem p_auto_grind_06 (p q : Prop) (h : p ∨ q) (hnp : ¬p) : q := by grind
theorem p_auto_grind_07 (p : Prop) (h : ¬¬p) : p := by grind
theorem p_auto_grind_08 (a b : Nat) (h : a = b) : b = a := by grind
theorem p_auto_grind_09 (f g : Nat → Nat) (a : Nat) (h : f = g) : f a = g a := by grind
theorem p_auto_grind_10 : gsDouble 2 = 4 := by grind
theorem p_auto_grind_11 (p q : Prop) (hp : p) (h : p → q) : q := by grind
theorem p_auto_grind_12 (f : Nat → Nat → Nat) (a b c d : Nat) (h1 : a = b) (h2 : c = d) : f a c = f b d := by grind
theorem p_auto_grind_13 (a : Nat) (h : a = 3) : a + 1 = 4 := by grind
theorem p_auto_grind_14 (p : Prop) (h : p ∧ True) : p := by grind
theorem p_auto_cc_01 (f : Nat → Nat) (a b c : Nat) (h1 : a = b) (h2 : b = c) : f a = f c := by cc
theorem p_auto_cc_02 (f g : Nat → Nat) (a b : Nat) (h1 : f = g) (h2 : a = b) : f a = g b := by cc
theorem p_auto_search_01 (a : Nat) : a = a := by exact?
theorem p_auto_search_02 (a : Nat) : a ≤ a := by exact?
theorem p_auto_search_03 (p : Prop) (h : p) : p := by exact?
theorem p_auto_search_04 (n : Nat) : n + 0 = n := by exact?
theorem p_auto_search_05 (n : Nat) : 0 + n = n := by exact?
theorem p_auto_search_06 (a : Nat) : a = a := by apply?
theorem p_auto_search_07 (n : Nat) : n ≤ n + 1 := by apply?
theorem p_auto_search_08 (as : List Nat) : as ++ [] = as := by rw?
theorem p_auto_search_09 (n : Nat) : n + 0 = n := by rw?
theorem p_auto_search_10 (a : Nat) : a = a := by library_search
