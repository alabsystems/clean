inductive BadDomain : List Nat → Prop where
  | intro {xs} : xs.length → BadDomain xs
