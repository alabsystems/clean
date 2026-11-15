section
variable (offset : Nat)
def shifted (x : α) (n : Nat) : Nat := offset + n
def shiftedRec (x : α) : Nat → Nat
 | 0 => offset
 | n + 1 => shiftedRec x n + 1
end
def main (args : List String) : IO Unit := do
  IO.println (toString (@shifted args.length Bool true 3))
  IO.println (toString (@shiftedRec args.length Bool true 2))
