prelude
import Init.Prelude

/-! An axiom bound on its declaration. Lean runs the implementation wherever the axiom is
called: `axCaller 1` prints `20`. A `module`'s public part exports a definition or opaque whose
body it does not expose as an axiom too (pinned `Lean.Attributes`'
`mkAttributeImplOfConstant`). -/

def axFast (n : Nat) : Nat := Nat.add n 1

@[implemented_by axFast] axiom axSlow : Nat → Nat

def axCaller (n : Nat) : Nat := Nat.mul (axSlow n) 10
