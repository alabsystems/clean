module

import all StableFixture.Defs

theorem checked : (0 : Nat) = 0 := StableFixture.zeroRefl

public def main : IO UInt32 := do
  IO.println (StableFixture.addOffset (StableFixture.twice 20))
  pure 17
