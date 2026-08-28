-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
--
-- Lean 4's BINDER ANNOTATION UPDATE form of `variable`, distilled from
-- Mathlib/Logic/Basic.lean `section ite` (v4.30.0-rc2):
--
--   820  variable {α : Sort*} {σ : α → Sort*} {P Q R : Prop} [Decidable P]
--          {a b c : α} {A : P → α} {B : ¬P → α}
--   874  variable (P Q a b)        -- <- makes the ALREADY-DECLARED P Q a b explicit
--   929  variable {P Q}            -- <- puts P Q back to implicit
--
-- A bracketed binder written with NO type ascription is not a declaration:
-- Lean re-binds the already-declared section variable at a new annotation,
-- KEEPING its declared type and its position in the telescope
-- (`Lean/Elab/Command.lean`, `replaceBinderAnnotation`).
--
-- Ground truth, measured with lean 4.33.1 on 2026-08-23:
--   bavu_explicit : ∀ (P : Prop) [Decidable P] (a : Nat), P → P ∧ a = a
--   bavu_ite      : ∀ (P : Prop) [inst : Decidable P] (a b : Nat),
--                     (if P then a else b) = if P then a else b
--   bavu_implicit : ∀ {P : Prop} [Decidable P] (a : Nat), P → P ∧ a = a
section
variable {P Q R : Prop} [Decidable P] {a b : Nat}

variable (P Q a b)

theorem bavu_explicit (h : P) : P ∧ a = a := ⟨h, rfl⟩

theorem bavu_ite : (if P then a else b) = (if P then a else b) := rfl

variable {P Q}

theorem bavu_implicit (h : P) : P ∧ a = a := ⟨h, rfl⟩
end

-- The re-binding is SECTION-SCOPED: `variable (P)` inside `Inner` re-annotates
-- the variable `Outer` declared, and `end Inner` puts it back. Truncating the
-- accumulated telescope cannot undo that on its own — the mutated entry lives
-- below the section marker.
--
-- Ground truth, measured with lean 4.33.1 on 2026-08-23:
--   bavu_inner : ∀ (P : Prop), P → P
--   bavu_outer : ∀ {P : Prop}, P → P
section Outer
variable {P : Prop}

section Inner
variable (P)

theorem bavu_inner (h : P) : P := h

end Inner

theorem bavu_outer (h : P) : P := h

end Outer
