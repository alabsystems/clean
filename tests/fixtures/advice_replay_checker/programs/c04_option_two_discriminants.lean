inductive Rule where
  | beta
  | succLit
  | addLit

inductive Tm where
  | lit : Nat → Tm
  | succ : Tm → Tm
  | add : Tm → Tm → Tm

def contract : Rule → Tm → Option Tm
  | .succLit, .succ (.lit n) => some (.lit (n + 1))
  | .addLit, .add (.lit m) (.lit n) => some (.lit (m + n))
  | _, _ => none

def show' : Option Tm → String
  | some (.lit n) => "lit " ++ toString n
  | some _ => "other"
  | none => "none"

def main : IO Unit := do
  IO.println (show' (contract .succLit (.succ (.lit 41))))
  IO.println (show' (contract .addLit (.add (.lit 40) (.lit 2))))
  IO.println (show' (contract .beta (.lit 1)))
  IO.println (show' (contract .addLit (.succ (.lit 1))))
