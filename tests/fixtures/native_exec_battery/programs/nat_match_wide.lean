def isZero : Nat → Bool
  | 0 => true
  | _ => false

def predOr : Nat → Nat
  | 0 => 0
  | n + 1 => n

def countDown : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => countDown n (acc + 1)

def main : IO Unit := do
  IO.println (toString (countDown 300 0))
  IO.println s!"{isZero (2 ^ 63)} {isZero (2 ^ 64)} {predOr (2 ^ 64) == 2 ^ 64 - 1}"
  for n in [0, 1, 255, 256, 300, 512, 65536, 4294967295, 4294967296, 8589934592, 9223372036854775807] do
    IO.println s!"{n} {isZero n} {predOr n}"
