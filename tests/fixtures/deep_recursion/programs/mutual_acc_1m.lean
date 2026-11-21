/-!
X4 deep-recursion regression: a structural mutual block of two-argument
members that call each other in tail position, 10⁶ steps (c36's shape: a
function-typed `PProd` motive). Clean compiles the block to one recursive
function with a selector, so the calls between members are self tail calls
and the cycle is a loop. Lean compiles each member separately and has no
mutual tail calls.
-/

mutual
def evenAcc : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => oddAcc n (acc + 1)
def oddAcc : Nat → Nat → Nat
  | 0, acc => acc + 1000000000
  | n + 1, acc => evenAcc n (acc + 2)
end

def main : IO Unit := do
  IO.println (toString (evenAcc 1000000 0))
  IO.println (toString (oddAcc 1000001 0))
  IO.println (toString (evenAcc 7 0))
