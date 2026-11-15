def greet (n : Nat) : IO Unit := do
  match n with
  | 0 => IO.println "zero"
  | _ => IO.println "nonzero"
  IO.println "after"

def main : IO Unit := do
  greet 0
  greet 1
