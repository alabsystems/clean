prelude
import Init.Prelude

/-! A module whose compiled code differs from its kernel meaning. -/

def implFast (n : Nat) : Nat := Nat.add n 1

@[implemented_by implFast]
def implSlow (n : Nat) : Nat := Nat.add n 2

def implCaller (n : Nat) : Nat := Nat.mul (implSlow n) 10

def chainEnd (n : Nat) : Nat := Nat.add n 7

@[implemented_by chainEnd]
def chainMid (n : Nat) : Nat := Nat.add n 8

@[implemented_by chainMid]
def chainHead (n : Nat) : Nat := Nat.add n 9

unsafe def unsafeFast (n : Nat) : Nat := Nat.add n 100

@[implemented_by unsafeFast]
def unsafeSlow (n : Nat) : Nat := Nat.add n 200

@[extern "clean_implby_fixture_no_such_symbol"]
def externBody (n : Nat) : Nat := Nat.add n 3

def plainLib (n : Nat) : Nat := Nat.add n 5
