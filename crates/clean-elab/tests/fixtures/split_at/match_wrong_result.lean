theorem split_match_wrong_result (b : Bool)
    (h : match b with | false => False | true => True) : b = false := by
  split at h <;> simp_all
