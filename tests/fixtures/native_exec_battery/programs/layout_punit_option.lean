def q : Option PUnit.{1} := some PUnit.unit
def main : IO Unit := IO.println (match q with | some _ => "some" | none => "none")
