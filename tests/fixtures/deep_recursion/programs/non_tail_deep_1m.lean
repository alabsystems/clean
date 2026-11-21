/-!
X4 negative control (N1): a NON-tail self call (`deep n + 1`) stays a call,
so 10⁶ levels need about as many frames. Clean's compiled program on an
8 MiB main thread overflows its stack, as Lean's does with
`LEAN_MAIN_USE_THREAD=0`.
-/

def deep : Nat → Nat
  | 0 => 0
  | n + 1 => deep n + 1

def main : IO Unit := do
  IO.println (toString (deep 3))
  IO.println (toString (deep 1000000))
