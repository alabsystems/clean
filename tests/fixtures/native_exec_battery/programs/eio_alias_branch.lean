abbrev M := IO

def g (c : Bool) : M Unit :=
  (fun (x : M Unit) => x) (if c then IO.println "a" else IO.println "b")

def main : IO Unit := do
  g true
  g false
