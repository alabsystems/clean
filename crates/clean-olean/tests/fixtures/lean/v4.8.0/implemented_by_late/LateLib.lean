prelude
import Init.Prelude

/-! A late `attribute [implemented_by]` after code that reaches the declaration. -/

def lateFast (n : Nat) : Nat := Nat.add n 1

def lateSlow (n : Nat) : Nat := Nat.add n 2

def lateCaller (n : Nat) : Nat := Nat.mul (lateSlow n) 10

attribute [implemented_by lateFast] lateSlow

def lateAfter (n : Nat) : Nat := Nat.mul (lateSlow n) 10
