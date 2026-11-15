def counter : StateM Nat Unit := do
  modify (· + 1)
  modify (· * 10)

def safeDiv (a b : Nat) : Except String Nat :=
  if b == 0 then .error "div by zero" else .ok (a / b)

def compute : ExceptT String (StateM Nat) Nat := do
  let s ← get
  if s > 100 then throw "too big"
  set (s + 5)
  return s * 2

def main : IO Unit := do
  let ((), s) := counter.run 4
  IO.println s
  IO.println (repr (safeDiv 10 2))
  IO.println (repr (safeDiv 1 0))
  let (r, s2) := (compute.run).run 7
  IO.println (repr r)
  IO.println s2
