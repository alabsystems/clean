def safeDiv (a b : Nat) : Except String Nat :=
  if b == 0 then .error "div by zero" else .ok (a / b)

def show' : Except String Nat → String
  | .ok v => "ok " ++ toString v
  | .error e => "error " ++ e

def main : IO Unit := do
  IO.println (show' (safeDiv 10 2))
  IO.println (show' (safeDiv 1 0))
