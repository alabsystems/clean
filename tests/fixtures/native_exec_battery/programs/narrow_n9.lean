def loop : Nat → IO Unit
  | 0 => pure ()
  | n + 1 => do
    IO.println (toString n)
    loop n

def main : IO Unit := loop 3
