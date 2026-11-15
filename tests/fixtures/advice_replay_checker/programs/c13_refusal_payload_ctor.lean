inductive Rule where
  | beta
  | addLit

inductive Refusal where
  | outOfFuel : Nat → Refusal
  | ruleDoesNotApply : Nat → Rule → Refusal
  | mismatch : Refusal

def Rule.name : Rule → String
  | .beta => "beta"
  | .addLit => "addLit"

def Refusal.render : Refusal → String
  | .outOfFuel i => "out of fuel at step " ++ toString i
  | .ruleDoesNotApply i r => "step " ++ toString i ++ ": " ++ r.name ++ " does not apply"
  | .mismatch => "replayed term is not the claim"

def main : IO Unit := do
  IO.println (Refusal.outOfFuel 3).render
  IO.println (Refusal.ruleDoesNotApply 0 .addLit).render
  IO.println Refusal.mismatch.render
