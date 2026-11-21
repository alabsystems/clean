theorem split_match_bound
    (h : ∀ b : Bool, match b with | false => True | true => True) : True := by
  split at h <;> trivial
