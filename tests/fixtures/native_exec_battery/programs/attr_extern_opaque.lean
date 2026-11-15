-- A bodiless `@[extern]` declaration: Lean calls the symbol and `lean --run`
-- stops with rc 1 when it is absent. Clean binds no user extern symbol.
@[extern "clean_no_such_sym"]
opaque bumpO (n : Nat) : Nat
def main : IO Unit := IO.println (toString (bumpO 1))
