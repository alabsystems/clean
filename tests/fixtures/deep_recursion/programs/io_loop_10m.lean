/-!
X4 deep-recursion regression: a structurally recursive `IO` loop, 10⁷ steps,
printing every 2·10⁶th step.
-/

def ioLoop : Nat → IO Unit
  | 0 => IO.println "done"
  | n + 1 => do
    if n % 2000000 == 0 then IO.println (toString n)
    ioLoop n

def main : IO Unit := ioLoop 10000000
