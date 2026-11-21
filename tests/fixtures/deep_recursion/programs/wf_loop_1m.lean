/-!
X4 deep-recursion regression: well-founded recursion (`termination_by`) whose
step makes the recursive call in tail position, 10⁶ steps.
-/

def wfLoop (n acc : Nat) : Nat :=
  if h : n = 0 then acc else wfLoop (n - 1) (acc + 2)
termination_by n

def main : IO Unit := do
  IO.println (toString (wfLoop 1000000 0))
  IO.println (toString (wfLoop 3 1))
