def sumTo (n : Nat) : Nat :=
  go n 0
where
  go : Nat → Nat → Nat
    | 0, acc => acc
    | k + 1, acc => go k (acc + k + 1)

def main : IO Unit :=
  IO.println (toString (sumTo 100))
