prelude
import Init.Prelude

/-! A late binding of a `@[macro_inline]` declaration: Lean keeps no IR for it, and the
earlier caller expanded its body. -/

def macroFast (n : Nat) : Nat := Nat.add n 1

@[macro_inline] def macroSlow (n : Nat) : Nat := Nat.add n 2

def macroCaller (n : Nat) : Nat := Nat.mul (macroSlow n) 10

attribute [implemented_by macroFast] macroSlow
