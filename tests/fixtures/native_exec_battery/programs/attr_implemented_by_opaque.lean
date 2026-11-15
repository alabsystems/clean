-- `opaque` has no usable body; `implemented_by` gives it one at run time.
def fastO (n : Nat) : Nat := n + 1

@[implemented_by fastO]
opaque op (n : Nat) : Nat

def main : IO Unit := IO.println (toString (op 1))
