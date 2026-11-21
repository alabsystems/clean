inductive SplitNamedWrong where
  | mk (flag : Bool)
  | other

theorem split_match_named_field_wrong (node : SplitNamedWrong)
    (mk_0 : match node with | .mk flag => flag = true | .other => False) :
    match node with | .mk flag => flag = false | .other => False := by
  split at mk_0 <;> exact mk_0
