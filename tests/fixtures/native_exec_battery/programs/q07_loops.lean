def sumTo (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [0:n] do
    s := s + i
  return s

def sumList (xs : List Nat) : Nat := Id.run do
  let mut s := 0
  for x in xs do
    s := s + x
  return s

def main : IO Unit := do
  IO.println (toString (sumTo 10))
  IO.println (toString (sumList [1, 2, 3, 4]))
