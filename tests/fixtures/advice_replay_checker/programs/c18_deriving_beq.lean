inductive Tm where
  | var : Nat → Tm
  | app : Tm → Tm → Tm
  | lam : Tm → Tm
  deriving BEq

def main : IO Unit := do
  IO.println (toString (Tm.app (.lam (.var 0)) (.var 1) == Tm.app (.lam (.var 0)) (.var 1)))
  IO.println (toString (Tm.app (.lam (.var 0)) (.var 1) == Tm.app (.lam (.var 0)) (.var 2)))
