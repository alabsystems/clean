partial def collatz (n : Nat) (steps : Nat) : Nat :=
  if n == 1 then steps
  else if n % 2 == 0 then collatz (n / 2) (steps + 1)
  else collatz (3 * n + 1) (steps + 1)

def main : IO Unit := do
  IO.println (collatz 27 0)
