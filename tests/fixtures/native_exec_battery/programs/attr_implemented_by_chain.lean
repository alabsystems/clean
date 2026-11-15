-- A chain: `slowest` runs `middle`, which runs `fastest`.
def fastest (n : Nat) : Nat := n * 10

@[implemented_by fastest]
def middle (n : Nat) : Nat := n + 7

@[implemented_by middle]
def slowest (n : Nat) : Nat := n + 5

def main : IO Unit := IO.println (toString (slowest 1))
