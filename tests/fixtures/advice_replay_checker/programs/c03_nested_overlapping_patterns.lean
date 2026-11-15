inductive Tm where
  | var : Nat → Tm
  | app : Tm → Tm → Tm
  | lam : Tm → Tm
  | lit : Nat → Tm
  | succ : Tm → Tm

def Tm.isNormal : Tm → Bool
  | .var _ => true
  | .app (.lam _) _ => false
  | .app f a => Tm.isNormal f && Tm.isNormal a
  | .lam b => Tm.isNormal b
  | .lit _ => true
  | .succ (.lit _) => false
  | .succ a => Tm.isNormal a

def main : IO Unit := do
  IO.println (toString (Tm.isNormal (.app (.var 0) (.lit 1))))
  IO.println (toString (Tm.isNormal (.app (.lam (.var 0)) (.lit 1))))
  IO.println (toString (Tm.isNormal (.lam (.succ (.lit 1)))))
  IO.println (toString (Tm.isNormal (.lam (.succ (.var 1)))))
