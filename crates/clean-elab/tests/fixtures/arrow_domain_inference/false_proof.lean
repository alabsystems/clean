inductive EmptyList : List Nat → Prop where
  | intro {xs} : xs.length = 0 → EmptyList xs
def falseProof : EmptyList [1] := EmptyList.intro rfl
