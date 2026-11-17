module

import StableFixture.Defs

theorem metaChecked : (stable_witness% 17 : Nat) = 73 := rfl
#eval (stable_witness% 18 : Nat)
