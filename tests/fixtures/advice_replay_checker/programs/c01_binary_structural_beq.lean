inductive Tm where
  | var : Nat → Tm
  | app : Tm → Tm → Tm
  | lam : Tm → Tm
  | lit : Nat → Tm

def Tm.beq : Tm → Tm → Bool
  | .var i, .var j => i == j
  | .app f a, .app g b => Tm.beq f g && Tm.beq a b
  | .lam b, .lam c => Tm.beq b c
  | .lit m, .lit n => m == n
  | _, _ => false

def main : IO Unit := do
  IO.println (toString (Tm.beq (.app (.lam (.var 0)) (.lit 5)) (.app (.lam (.var 0)) (.lit 5))))
  IO.println (toString (Tm.beq (.app (.lam (.var 0)) (.lit 5)) (.app (.lam (.var 1)) (.lit 5))))
  IO.println (toString (Tm.beq (.lit 5) (.var 5)))
