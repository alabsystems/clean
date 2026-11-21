/-!
X4 deep-recursion regression: a structural mutual block whose members call
each other in tail position, 10⁷ steps. Clean compiles the block to one
recursive function with a selector, so the calls between members are self
tail calls and the cycle is a loop. Lean compiles each member separately.
-/

mutual
def isEven : Nat → Bool
  | 0 => true
  | n + 1 => isOdd n
def isOdd : Nat → Bool
  | 0 => false
  | n + 1 => isEven n
end

def main : IO Unit := do
  IO.println (toString (isEven 10000000))
  IO.println (toString (isOdd 10000001))
  IO.println (toString (isEven 7))
