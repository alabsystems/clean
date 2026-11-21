structure SplitPair where
  flag : Bool
  payload : Nat

theorem split_match_projection (node : SplitPair)
    (h : match node.flag with | false => False | true => True) : node.flag = true := by
  split at h <;> simp_all
