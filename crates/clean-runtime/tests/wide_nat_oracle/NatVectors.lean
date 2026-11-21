def a : Nat := 0x1_0000000000000001_0000000000000001_0000000000000011
def b : Nat := 0x2_0000000000000001_0000000000000020
def c : Nat := 0x2_0000000000000003
def out (label : String) (value : Nat) : IO Unit := IO.println (label ++ "=" ++ toString value)
def flag (label : String) (value : Bool) : IO Unit := IO.println (label ++ "=" ++ toString value)
@[noinline] def power (base exponent : Nat) : Nat := Nat.pow base exponent

def vectors : IO Unit := do
  out "a" a
  out "b" b
  out "max128+1" ((0xffffffffffffffff_ffffffffffffffff : Nat) + 1)
  out "add" (a + b)
  out "add_self" (a + a)
  out "sub" (a - b)
  out "sub_sat" (b - a)
  out "mul" (a * b)
  out "mul_0" (a * 0)
  out "pow_zero_zero" (power 0 0)
  out "pow_wide_zero" (power a 0)
  out "pow_wide_one" (power a 1)
  out "pow_wide_three" (power a 3)
  out "pow_cross_limb" (power 2 65)
  out "pow_zero_oversized" (power 0 b)
  out "pow_one_oversized" (power 1 b)
  out "pow_one_at_limit" (power 1 0xffffffff)
  flag "pow_large_scalar" (power 2 4194305 == (1 <<< 4194305))
  flag "pow_large_heap" (power (1 <<< 130) 32265 == (1 <<< 4194450))
  out "div_wide" (a / b)
  out "mod_wide" (a % b)
  out "div_mid" (a / c)
  out "mod_mid" (a % c)
  out "div_word" (a / 3)
  out "mod_word" (a % 3)
  out "div_zero" (a / 0)
  out "mod_zero" (a % 0)
  out "div_larger" (b / a)
  out "mod_larger" (b % a)
  out "div_equal" (a / a)
  out "mod_equal" (a % a)
  out "and" (a &&& b)
  out "or" (a ||| b)
  out "xor" (a ^^^ b)
  out "xor_self" (a ^^^ a)
  out "right_63" (a >>> 63)
  out "right_64" (a >>> 64)
  out "right_65" (a >>> 65)
  out "right_128" (a >>> 128)
  out "right_192" (a >>> 192)
  out "right_193" (a >>> 193)
  out "right_huge" (a >>> b)
  out "left_63" (a <<< 63)
  out "left_64" (a <<< 64)
  out "left_65" (a <<< 65)
  out "left_129" (a <<< 129)
  flag "eq_wide" (a == a)
  flag "ne_wide" (a == b)
  flag "le_wide" (decide (b ≤ a))
  flag "gt_wide" (decide (a < b))
  flag "test_bit_192" (a.testBit 192)
  flag "test_bit_huge" (a.testBit b)
  out "uint8" (UInt8.ofNat (a + 0x1234)).toNat
  out "uint16" (UInt16.ofNat (a + 0x12345)).toNat
  out "uint32" (UInt32.ofNat (a + 0x123456789)).toNat
  out "uint64" (UInt64.ofNat (a + 0x123456789abcdef01)).toNat
  out "usize" (USize.ofNat (a + 0x123456789abcdef01)).toNat
  flag "int_signed_pos_cmp" (decide ((Int.ofNat a) > Int.ofNat b))
  flag "int_signed_neg_cmp" (decide ((-(Int.ofNat a)) < -(Int.ofNat b)))
  flag "int_signed_neg_eq" ((-(Int.ofNat a)) == -(Int.ofNat a))

def main : List String → IO Unit
  | [] => vectors
  | ["pow-exponent-cutoff"] => IO.println (power 2 0x100000000)
  | ["pow-aliased-oversized"] =>
    let wide := 0x1_0000000000000000_0000000000000005
    IO.println (power wide wide)
  | _ => throw (IO.userError "unknown Nat vector mode")
