def countUp : Nat := Id.run do
  let mut i := 0
  let mut acc := 0
  while i < 5 do
    acc := acc + i
    i := i + 1
  return acc

def main : IO Unit := IO.println (toString countUp)
