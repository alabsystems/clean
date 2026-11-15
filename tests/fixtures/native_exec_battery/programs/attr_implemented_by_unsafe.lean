-- An `unsafe` implementation: Lean runs it, `2`. Clean compiles no unsafe
-- code, so the build is refused by name (a known, fail-closed divergence).
unsafe def fastU (n : Nat) : Nat := n + 1
@[implemented_by fastU]
def slowU (n : Nat) : Nat := n + 2
def main : IO Unit := IO.println (toString (slowU 1))
