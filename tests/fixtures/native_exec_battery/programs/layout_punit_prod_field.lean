def p : PUnit.{1} × Nat := (PUnit.unit, 5)
def main : IO Unit := IO.println (toString p.2)
