def twice (a : IO Unit) : IO Unit := do
  a
  a

def main : IO Unit := twice (IO.println "x")
