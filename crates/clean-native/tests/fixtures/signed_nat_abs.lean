def absValue (z : Int) : Nat := Int.natAbs z
def main (args : List String) : IO Unit := do
  IO.println (toString (absValue (Int.ofNat args.length)))
  IO.println (toString (absValue (Int.negSucc args.length)))
