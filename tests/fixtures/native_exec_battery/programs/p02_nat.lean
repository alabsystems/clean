def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

def main : IO Unit := do
  IO.println (toString (fib 25))
  IO.println (toString (fact 20))
  IO.println (toString (fact 30))
  IO.println (toString (2 ^ 64))
  IO.println (toString (fact 40))
  IO.println (toString (2 ^ 200))
