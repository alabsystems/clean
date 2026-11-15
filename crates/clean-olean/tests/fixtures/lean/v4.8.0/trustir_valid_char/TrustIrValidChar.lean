-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Fixture: trust-ir's `validChar` block, copied verbatim from
-- `lean/trust_ir-semantics/TrustIr/Basic.lean` at trust-ir 524d8ded (lines
-- 417-451, inside `namespace TrustIr`). Compiled with Lean 4.8.0; see README.md.

namespace TrustIr

def validChar (v : Nat) : Prop :=
  v < 0x110000 ∧ ¬(0xD800 ≤ v ∧ v ≤ 0xDFFF)

instance (v : Nat) : Decidable (validChar v) := by
  unfold validChar; infer_instance

/-- Every `u8` is a Unicode scalar value, so the ONE admitted computed
    `Char` origin — `zext u8 -> char`, subset v4 condition 6 — establishes
    [`validChar`] by construction. This is the theorem the condition rests
    on: no range check is needed on that edge. -/
theorem validChar_of_lt_256 {v : Nat} (h : v < 256) : validChar v := by
  refine ⟨by omega, ?_⟩
  rintro ⟨hlo, -⟩
  omega

/-- The mutation control: the first surrogate is NOT a valid `char`, so a
    `Char` constant of `0xD800` is refused. A model that dropped the
    surrogate conjunct from [`validChar`] would accept it. -/
theorem not_validChar_surrogate : ¬ validChar 0xD800 := by
  rintro ⟨-, hsur⟩
  exact hsur ⟨by omega, by omega⟩

/-- The other mutation control: `0x110000` is one past the last code point.
    A model that dropped the range conjunct would accept it. -/
theorem not_validChar_above_max : ¬ validChar 0x110000 := by
  rintro ⟨hlt, -⟩
  omega

/-- The `Char` carrier is 32 bits wide, so [`validChar`] is a STRICTLY
    stronger property than "fits the carrier": the carrier admits values the
    type does not. -/
theorem validChar_lt_two_pow_32 {v : Nat} (h : validChar v) : v < 2 ^ 32 := by
  have := h.1
  omega


end TrustIr
