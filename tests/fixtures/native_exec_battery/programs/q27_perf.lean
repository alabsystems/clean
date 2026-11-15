def build (n : Nat) : Array Nat := Id.run do
  let mut a : Array Nat := #[]
  for i in [0:n] do
    a := a.push i
  return a

def main : IO Unit := IO.println (toString (build 20000).size)
