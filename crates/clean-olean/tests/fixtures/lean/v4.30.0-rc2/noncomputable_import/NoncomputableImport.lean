prelude

inductive EligibilityLeaf where
  | value

noncomputable def blocked (x : EligibilityLeaf) : EligibilityLeaf := x

def ordinary (x : EligibilityLeaf) : EligibilityLeaf := x
