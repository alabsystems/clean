def fast (n : Nat) : Nat := n + 1

@[implemented_by fast]
def slow (n : Nat) : Nat := n + 2

def main : IO Unit := IO.println (toString (slow 1))
