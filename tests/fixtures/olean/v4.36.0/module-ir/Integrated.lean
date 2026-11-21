module

import all StableFixture.Defs

theorem checked : (0 : Nat) = 0 := StableFixture.zeroRefl
theorem metaChecked : (stable_witness% 17 : Nat) = 73 := rfl

public def main : IO UInt32 := do
  IO.println (StableFixture.addOffset (StableFixture.twice (stable_witness% 17)))
  pure 17
