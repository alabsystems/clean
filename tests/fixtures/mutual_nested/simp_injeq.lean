-- Gap G70: Lean's `C.injEq` simp lemmas turn an equation between two
-- applications of one constructor into its fields' equations.
theorem inj_option_pair (a b : Int) (h : some (0, a) = some (0, b)) : a = b := by
  simp at h
  exact h

theorem inj_pair (a b : Nat) (h : (a, 1) = (b, 1)) : a = b := by
  simp at h
  exact h

inductive C where
  | int : Int → C
  | agg : List C → C

theorem inj_goal (a b : Int) (h : a = b) : C.int a = C.int b := by
  simp
  exact h
