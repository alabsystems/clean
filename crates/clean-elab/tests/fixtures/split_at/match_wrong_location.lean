theorem split_match_wrong_location (b : Bool) (h : True) :
    match b with | false => True | true => True := by
  split at h <;> trivial
