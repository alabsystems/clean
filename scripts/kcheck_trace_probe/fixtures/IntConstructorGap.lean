prelude
import Init.Data.Int.Basic

-- This accepted equality isolates the printed pair in the Init trace gap.
example : Int.ofNat (Nat.succ 0) = Int.ofNat 1 := rfl
