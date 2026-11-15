def loop : Nat → IO Unit
  | 0 => IO.println "base"
  | n + 1 => do
    IO.println (toString n)
    loop n

def main : IO Unit := loop 2
