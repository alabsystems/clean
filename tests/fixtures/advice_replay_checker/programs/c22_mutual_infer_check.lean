inductive Tm where
  | lit : Nat → Tm
  | neg : Tm → Tm
  | pair : Tm → Tm → Tm

mutual
def evenDepth : Tm → Bool
  | .lit _ => true
  | .neg a => oddDepth a
  | .pair a b => oddDepth a && oddDepth b
def oddDepth : Tm → Bool
  | .lit _ => false
  | .neg a => evenDepth a
  | .pair a b => evenDepth a && evenDepth b
end

def main : IO Unit := do
  IO.println (toString (evenDepth (.neg (.neg (.lit 1)))))
  IO.println (toString (evenDepth (.pair (.neg (.lit 1)) (.lit 2))))
  IO.println (toString (oddDepth (.pair (.lit 1) (.lit 2))))
