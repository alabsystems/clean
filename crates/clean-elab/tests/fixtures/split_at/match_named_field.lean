inductive SplitNamed where
  | mk (flag : Bool)
  | other

theorem split_match_named_field (node : SplitNamed)
    (mk_0 : match node with | .mk flag => flag = true | .other => False) :
    match node with | .mk flag => flag = true | .other => False := by
  split at mk_0 <;> exact mk_0
