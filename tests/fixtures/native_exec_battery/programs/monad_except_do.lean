def step (x : Nat) : Except String Nat :=
  if x > 3 then .error "too big" else .ok (x + 1)

def run2 (x : Nat) : Except String Nat := do
  let a ← step x
  let b ← step a
  pure (a + b)

def show' : Except String Nat → String
  | .ok v => "ok " ++ toString v
  | .error e => "error " ++ e

def main : IO Unit := do
  IO.println (show' (run2 1))
  IO.println (show' (run2 3))
