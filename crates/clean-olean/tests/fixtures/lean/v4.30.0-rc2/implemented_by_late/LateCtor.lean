prelude
import Init.Prelude

/-! Constructors bound by the command form. Lean compiles a constructor structurally and never
runs such a binding: `ctorUse 1` and `tUse 1` print `1`, in this module and in an importer
(`pf` and `tf` would give `11` and `101`). -/

structure P where
  a : Nat

def pf (a : Nat) : P := P.mk (Nat.add a 10)

attribute [implemented_by pf] P.mk

def ctorUse (n : Nat) : Nat := (P.mk n).a

inductive T where
  | leaf : Nat → T

def tf (n : Nat) : T := T.leaf (Nat.add n 100)

attribute [implemented_by tf] T.leaf

def tget : T → Nat
  | T.leaf n => n

def tUse (n : Nat) : Nat := tget (T.leaf n)
