def out (label : String) (value : Nat) : IO Unit := IO.println (label ++ "=" ++ toString value)
def main : IO Unit := do
  let n := (1 : Nat) <<< 2048
  out "2048_bit" n
  out "2048_to_0" (n >>> 2048)
  out "2048_to_1" (n >>> 2047)
  out "2048_to_negative" (n >>> 2049)
  out "carry_32_limbs" ((n - 1) + 1)
  out "borrow_32_limbs" (n - 1)
  out "mul_cross_32" (((1 : Nat) <<< 1024) * ((1 : Nat) <<< 1024))
  out "div_cross_32" ((n + 17) / ((1 : Nat) <<< 1024))
  out "mod_cross_32" ((n + 17) % ((1 : Nat) <<< 1024))
  out "and_mask_32" ((n + 17) &&& (n - 1))
  out "alias_32" (n + n)
