/- Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0 -/
prelude
import Init.Core

/-!
The base of the meaning digest's mutation controls
(`crates/clean-olean/tests/meaning_digest.rs`). Each sibling module is this
file with one change, marked `-- MUTATION` there. `Tm.instAll` recurses
structurally on a list argument, as `KCheckSpec.Term.instPis` does, so pinned
Lean stores its body in the auxiliary `Tm.instAll._f` and its own value is a
`List.brecOn` wrapper. The module imports `Init.Core` alone, so a load is
small.
-/
namespace MD

inductive Tm where
  | leaf (n : Nat)
  | pi (body : Tm)

namespace Tm

def shift (k : Nat) : Tm → Tm
  | .leaf n => .leaf (n + k)
  | .pi b => .pi (b.shift k)

def instAll : Tm → List Nat → Tm
  | .pi B, a :: as => (B.shift a).instAll as
  | t, _ => t

end Tm

/-- A definition that reaches `Tm.instAll`. -/
def Reaches (t : Tm) : Prop := t.instAll (0 :: .nil) = t

/-- A theorem that reaches `Tm.instAll` through `Reaches`. -/
theorem reaches_leaf : Reaches (.leaf 0) := rfl

/-- The relation a soundness-shaped theorem names, decided by evaluation. -/
def SemLE (a b : Nat) : Prop := Nat.ble a b = true

theorem leq_sound : SemLE 0 1 := rfl

/-- Reaches nothing any mutation changes. -/
def Unrelated : Prop := ∀ n : Nat, n = n

end MD
