/-!
X4 regression: a pure induction hypothesis used twice is computed once per
level (sharing is a lowering decision, so it holds at every optimisation
level). Run unshared, the 60 levels below would take 2⁶⁰ calls.
-/

def f : Nat → Nat
  | 0 => 1
  | n + 1 => f n + f n

def main : IO Unit := do
  IO.println (toString (f 60))
  IO.println (toString (f 4))
