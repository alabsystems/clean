theorem split_match_dependent (b : Bool)
    (h : match b with | false => False | true => True) (k : h = h) : b = true := by
  split at h <;> simp_all
