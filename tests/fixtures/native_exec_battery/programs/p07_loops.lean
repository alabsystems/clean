def sumTo (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [0:n] do
    s := s + i
  return s

def main : IO Unit := do
  IO.println (sumTo 10)
  let mut i := 0
  let mut acc := ""
  while i < 5 do
    acc := acc ++ toString i
    i := i + 1
  IO.println acc
  for x in ["p", "q", "r"] do
    IO.println x
  let mut found := 0
  for j in [1, 2, 3, 4, 5, 6] do
    if j % 2 == 0 then continue
    if j > 4 then break
    found := found + j
  IO.println found
  for a in [1, 2] do
    for b in [10, 20] do
      IO.println (a * b)
