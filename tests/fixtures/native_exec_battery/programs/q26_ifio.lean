def check (n : Nat) : IO Unit :=
  if n % 2 == 0 then IO.println s!"{n} even" else IO.println s!"{n} odd"

def main : IO Unit := do
  check 3
  check 4
