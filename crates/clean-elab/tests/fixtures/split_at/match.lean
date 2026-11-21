theorem split_match (b : Bool)
    (h : match b with | false => False | true => True) : b = true := by
  split at h <;> simp_all
