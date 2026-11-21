theorem split_dependent (p : Prop) [Decidable p]
  (h : if p then True else False) (k : h = h) : p := by
  split at h <;> simp_all
