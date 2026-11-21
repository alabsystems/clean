-- `UInt64.ofNat` and `UInt32.ofNat` wrap a Nat at or above 2^128 modulo
-- 2^64 and 2^32; the products are computed at run time, not folded.
def two64 : Nat := 18446744073709551616

def main : IO Unit := do
  let wide := two64 * two64 * 3 + 4294967303
  IO.println (toString (UInt64.ofNat wide))
  IO.println (toString (UInt32.ofNat wide))
  IO.println (toString (UInt64.ofNat (wide * two64 + 18446744073709551615)))
  IO.println (toString wide)
