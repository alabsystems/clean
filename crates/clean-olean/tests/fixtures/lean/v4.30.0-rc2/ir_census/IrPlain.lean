/-!
IR census fixture: a NON-`module` file, so every IR declaration stays in its
`.olean` (no `.olean.server`/`.olean.private`, no `.ir`). Each definition
exercises a different IR construct; the census test decodes all of them and
compares counts and renderings with the pinned toolchain's own oracle.
-/

def plainAdd (a b : Nat) : Nat := a + b

def plainStr (n : Nat) : String := s!"n = {n}\n\t\"q\" \\ é"

def bigLit : Nat := 123456789012345678901234567890123456789

def u64Lit : UInt64 := 18446744073709551615

structure Pt where
  x : UInt64
  y : UInt8
  flag : Bool
  size : USize
  name : String

def Pt.bump (p : Pt) : Pt := { p with x := p.x + 1, flag := !p.flag, size := p.size + 1 }

partial def collatz (n steps : Nat) : Nat :=
  if n ≤ 1 then steps
  else if n % 2 == 0 then collatz (n / 2) (steps + 1)
  else collatz (3 * n + 1) (steps + 1)

inductive Shape where
  | circle (r : Float)
  | rect (w h : Float)
  | empty

def Shape.area : Shape → Float
  | .circle r => 3.14 * r * r
  | .rect w h => w * h
  | .empty => 0

@[extern "irplain_native"] opaque nativeFn (x : @& Array Nat) : UInt32

def implFn (x : Nat) : Nat := x * 2

@[implemented_by implFn] def specFn (x : Nat) : Nat := x + x

initialize plainRef : IO.Ref Nat ← IO.mkRef 7

def useClosure (xs : List Nat) (k : Nat) : List Nat := xs.map (· + k)

def loopArr (a : Array Nat) : Nat := Id.run do
  let mut s := 0
  for x in a do
    s := s + x
  return s

def pairUp (a : Nat) (b : String) : Nat × String := (a + 1, b ++ "!")
