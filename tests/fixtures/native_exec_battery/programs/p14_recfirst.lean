structure P2 where
  a : Nat
  b : Nat
def recFirst : P2 → Nat → Nat
  | ⟨x, _⟩, 0 => x
  | ⟨x, y⟩, n + 1 => recFirst ⟨y, x⟩ n

def main : IO Unit := do
  IO.println (recFirst ⟨3, 4⟩ 0)
  IO.println (recFirst ⟨3, 4⟩ 1)
  IO.println (recFirst ⟨3, 4⟩ 2)
