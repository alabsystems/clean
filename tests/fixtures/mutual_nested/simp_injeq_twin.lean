-- G70 twin: injectivity gives `a = b`, not `a = b + 1`.
theorem inj_twin (a b : Int) (h : some (0, a) = some (0, b)) : a = b + 1 := by
  simp at h
  exact h
