def r : List PUnit.{1} := [PUnit.unit, PUnit.unit]
def main : IO Unit := IO.println (toString r.length)
