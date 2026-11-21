theorem split_hyp (p : Prop) [Decidable p]
  (h : if p then True else False) : p := by
  split at h <;> simp_all
