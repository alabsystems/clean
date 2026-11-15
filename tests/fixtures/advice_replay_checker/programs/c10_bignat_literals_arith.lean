def two64 : Nat := 18446744073709551616

inductive Tm where
  | lit : Nat → Tm
  | add : Tm → Tm → Tm

def eval : Tm → Nat
  | .lit n => n
  | .add a b => eval a + eval b

def main : IO Unit := do
  IO.println (toString (eval (.add (.lit two64) (.add (.lit two64) (.lit 7)))))
  IO.println (toString (18446744073709551615 + 1 == two64))
  IO.println (toString (eval (.add (.lit two64) (.lit two64)) == 36893488147419103233))
  IO.println (toString (two64 - 1))
  IO.println (toString ((two64 - 1) * (two64 - 1)))
  IO.println (toString ((two64 - 1) * (two64 - 1) / two64))
  IO.println (toString ((two64 + 5) % 1000))
