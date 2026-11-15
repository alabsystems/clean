def firstOdds : Nat := Id.run do
  let mut found := 0
  for j in [1, 2, 3, 4, 5, 6] do
    if j % 2 == 0 then continue
    if j > 4 then break
    found := found + j
  return found

def main : IO Unit := IO.println (toString firstOdds)
