/-!
R4 item (vii): advice tokens decoded from a `ByteArray`. The decoder is
structurally recursive on a counter, reads one byte per call by index, and
refuses a byte that names no token.
-/

inductive Tok where
  | core
  | stop
  | same
  | both

def Tok.name : Tok → String
  | .core => "core"
  | .stop => "stop"
  | .same => "same"
  | .both => "both"

def tokOfByte (b : UInt8) : Option Tok :=
  match b.toNat with
  | 0 => some .core
  | 1 => some .stop
  | 2 => some .same
  | 3 => some .both
  | _ => none

/-- Decode at most `fuel` bytes from `pos`; an error is the position of the first byte that names no token. -/
def decode (bs : ByteArray) : Nat → Nat → List Tok → Except Nat (List Tok)
  | 0, _, acc => .ok acc.reverse
  | fuel + 1, pos, acc =>
    if pos < bs.size then
      match tokOfByte (bs.get! pos) with
      | some t => decode bs fuel (pos + 1) (t :: acc)
      | none => .error pos
    else .ok acc.reverse

def names : List Tok → String
  | [] => ""
  | t :: ts => " " ++ t.name ++ names ts

def verdict (r : Except Nat (List Tok)) : String :=
  match r with
  | .ok ts => "ACCEPT" ++ names ts
  | .error p => s!"REFUSE byte at {p} names no token"

def main : IO Unit := do
  let good := ByteArray.mk #[3, 0, 0, 1, 0, 1, 1, 2]
  IO.println s!"size={good.size}"
  IO.println (verdict (decode good good.size 0 []))
  IO.println (verdict (decode (ByteArray.mk #[3, 0, 9, 1]) 4 0 []))
  IO.println (verdict (decode good 3 0 []))
