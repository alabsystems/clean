def check (a b : Nat) : Except String Nat := do
  let s ← (if a == 0 then Except.error "zero" else Except.ok (a + b))
  if !(s == 5) then
    throw "mismatch"
  if s < b then
    throw "unreachable"
  pure s

def show' : Except String Nat → String
  | .ok v => "ok " ++ toString v
  | .error e => "error " ++ e

def main : IO Unit := do
  IO.println (show' (check 2 3))
  IO.println (show' (check 2 4))
  IO.println (show' (check 0 5))
