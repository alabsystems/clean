prelude
import Init.Prelude

/-! Bindings whose declaration's own code Lean never runs after them: a late binding of a
`@[noinline]` declaration nothing in the module calls, and a recursive declaration bound on
itself, whose compiled recursion calls the implementation. -/

def okFast (n : Nat) : Nat := Nat.add n 1

@[noinline] def okSlow (n : Nat) : Nat := Nat.add n 2

attribute [implemented_by okFast] okSlow

@[noinline] def recFast (n : Nat) : Nat := Nat.mul n 3

@[implemented_by recFast]
def recSlow : Nat → Nat
  | 0 => 0
  | Nat.succ n => Nat.add (recSlow n) 2

def recCaller (n : Nat) : Nat := Nat.mul (recSlow n) 10
