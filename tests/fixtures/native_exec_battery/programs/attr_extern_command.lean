-- `attribute [extern]` after the declaration: Lean compiled `bump`'s body
-- when it was added and prints `2`. Clean refuses every reached `@[extern]`
-- declaration with a body (a known, fail-closed divergence).
def bump (n : Nat) : Nat := n + 1
attribute [extern "clean_no_such_sym"] bump
def main : IO Unit := IO.println (toString (bump 1))
