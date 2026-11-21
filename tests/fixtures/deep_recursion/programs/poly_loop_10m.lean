/-!
X4 deep-recursion regression: a polymorphic self tail call, whose loop passes
its erased type argument back to itself, 10⁷ steps.
-/

def polyLoop {α : Type} (x : α) : Nat → List α → List α
  | 0, acc => x :: acc
  | n + 1, acc => polyLoop x n (if n < 2 then x :: acc else acc)

def main : IO Unit := do
  IO.println (toString (polyLoop "s" 10000000 []))
  IO.println (toString (polyLoop 7 5 []))
