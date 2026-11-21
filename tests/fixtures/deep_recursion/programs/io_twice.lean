/-!
X4 regression: an action induction hypothesis used twice runs twice (no
sharing of effects), at every optimisation level.
-/

def twice : Nat → IO Unit
  | 0 => IO.println "leaf"
  | n + 1 => do
    twice n
    IO.println s!"node {n}"
    twice n

def main : IO Unit := twice 3
