prelude
import Init.Prelude

/-! A late binding of an `@[inline]` declaration: the earlier caller inlined its body, so its
IR calls neither declaration. -/

def inlineFast (n : Nat) : Nat := Nat.add n 1

@[inline] def inlineSlow (n : Nat) : Nat := Nat.add n 2

def inlineCaller (n : Nat) : Nat := Nat.mul (inlineSlow n) 10

attribute [implemented_by inlineFast] inlineSlow
