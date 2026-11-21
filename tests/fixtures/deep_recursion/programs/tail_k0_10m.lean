/-!
X4 deep-recursion regression: a self tail call whose recursive function takes
no argument besides the counter (`k = 0`), 10⁷ steps.
-/

def down : Nat → Bool
  | 0 => true
  | n + 1 => down n

def main : IO Unit := do
  IO.println (toString (down 10000000))
  IO.println (toString (down 3))
