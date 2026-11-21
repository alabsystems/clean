theorem split_wrong_location (p : Prop) [Decidable p] (h : True) :
  (if p then True else True) := by
  split at h <;> trivial
