-- A call and a function value: compiled code runs `fast` for both, `2` and `11`;
-- the kernel keeps `slow`.
def fast (n : Nat) : Nat := n + 1

@[implemented_by fast]
def slow (n : Nat) : Nat := n + 2

def apply (f : Nat → Nat) (n : Nat) : Nat := f n

def main : IO Unit := do
  IO.println (toString (slow 1))
  IO.println (toString (apply slow 10))
