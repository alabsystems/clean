/- Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0 -/
prelude
import Init.Core

/-!
A mutation control of the meaning digest
(`crates/clean-olean/tests/meaning_digest.rs`): `MeaningDigestBase.lean` with
`SemLE`, the relation `leq_sound` names,
weakened and the proof unchanged, marked `-- MUTATION`.
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
def SemLE (a b : Nat) : Prop := Nat.ble a (b + 1) = true -- MUTATION

theorem leq_sound : SemLE 0 1 := rfl

/-- Reaches nothing any mutation changes. -/
def Unrelated : Prop := ∀ n : Nat, n = n

end MD
