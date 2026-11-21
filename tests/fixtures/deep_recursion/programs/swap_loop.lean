/-!
X4 deep-recursion regression: a self tail call that passes its parameters
permuted (`swapLoop n b a`), so the loop's back edge assigns them in
parallel. 10⁶ + 1 steps.
-/

def swapLoop : Nat → Nat → Nat → Nat
  | 0, a, _ => a
  | n + 1, a, b => swapLoop n b a

def rotLoop : Nat → String → String → String → String
  | 0, a, b, c => a ++ b ++ c
  | n + 1, a, b, c => rotLoop n b c a

def main : IO Unit := do
  IO.println (toString (swapLoop 1000001 1 2))
  IO.println (toString (swapLoop 1000000 1 2))
  IO.println (rotLoop 1000001 "x" "y" "z")
  IO.println (rotLoop 4 "x" "y" "z")
