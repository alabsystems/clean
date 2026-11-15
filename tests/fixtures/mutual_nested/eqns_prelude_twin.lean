-- Twin of eqns_prelude.lean: `decide p = false` is not rewritten to `p`.
theorem o4f (p : Prop) [Decidable p] (h : decide p = false) : p := by
  simp only [decide_eq_true_eq] at h
  exact h
