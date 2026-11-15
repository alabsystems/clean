def greet (n : Nat) : IO Unit :=
  match n with
  | 0 => IO.println "zero"
  | _ => IO.println "nonzero"

def main : IO Unit := do
  greet 0
  greet 1
