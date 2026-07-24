/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

INVENTION WAVE 5 — `auto1_symm_euler_pair_modEq`
(elementary number theory: the SYMMETRIC EULER-PAIR CONGRUENCE).

────────────────────────────────────────────────────────────────────────────
THE THEOREM
────────────────────────────────────────────────────────────────────────────
For coprime positive naturals `a, b`:

    a ^ φ(b)  +  b ^ φ(a)   ≡   1   [MOD a * b]

where `φ = Nat.totient` is Euler's totient.  This is the *two-sided* companion of
Euler's theorem `Nat.ModEq.pow_totient` (`x ^ φ n ≡ 1 [MOD n]` for `Coprime x n`).

WHY IT IS TRUE (and the proof skeleton)
  • mod a :  `a ^ φ(b) ≡ 0` because `φ(b) ≥ 1` (b > 0) so `a ∣ a ^ φ(b)`, and
             `b ^ φ(a) ≡ 1` is Euler's theorem with `Coprime b a`.
             Hence the sum `≡ 0 + 1 = 1  [MOD a]`.
  • mod b :  symmetric — `b ^ φ(a) ≡ 0`, `a ^ φ(b) ≡ 1`, sum `≡ 1  [MOD b]`.
  • CRT   :  since `Coprime a b`, agreement mod a AND mod b lifts to mod a*b
             (`Nat.modEq_and_modEq_iff_modEq_mul`).

────────────────────────────────────────────────────────────────────────────
NOVELTY
────────────────────────────────────────────────────────────────────────────
Mathlib has Euler's theorem in two forms (`ZMod.pow_totient`,
`Nat.ModEq.pow_totient`) and the CRT bridge (`Nat.modEq_and_modEq_iff_modEq_mul`),
but it does NOT state the symmetric *pair* congruence `a^φ(b) + b^φ(a) ≡ 1`.
A grep of `.lake/packages/mathlib/Mathlib` for `pow_totient.*pow_totient` and
`totient.*+.*totient` finds no lemma adding two cross-totient powers; the only
match is an unrelated inductive `_root_` bound inside `Data/Nat/Totient.lean`.
This is a genuinely new composed identity, not a restatement of any single lemma.

Foundational: axioms ⊆ {propext, Classical.choice, Quot.sound} (Euler's theorem
routes through `ZMod` group theory, which uses Classical.choice; no `sorryAx`,
no `native_decide`, no new axiom).
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Totient

namespace Crownproof.InventionWave5

open Nat

/-- **Symmetric Euler-pair congruence.**  For coprime positive naturals `a` and
`b`, the cross totient powers sum to one modulo their product:
`a ^ φ(b) + b ^ φ(a) ≡ 1 [MOD a * b]`.

This is the two-sided companion of the Fermat–Euler theorem
`Nat.ModEq.pow_totient`: each summand is `≡ 0` to one modulus and `≡ 1` to the
other, so by the Chinese Remainder Theorem the sum is `≡ 1` to the product. -/
theorem auto1_symm_euler_pair_modEq
    {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b) :
    a ^ φ b + b ^ φ a ≡ 1 [MOD a * b] := by
  -- φ a and φ b are positive (a, b > 0), so a ∣ a^φ(b) and b ∣ b^φ(a).
  have hφa : 0 < φ a := Nat.totient_pos.mpr ha
  have hφb : 0 < φ b := Nat.totient_pos.mpr hb
  -- a^φ(b) ≡ 0 [MOD a]  (a divides a^φ(b) since the exponent is ≥ 1).
  have h_a0 : a ^ φ b ≡ 0 [MOD a] := by
    have : a ∣ a ^ φ b := dvd_pow_self a hφb.ne'
    simpa [Nat.modEq_zero_iff_dvd] using this
  -- b^φ(a) ≡ 0 [MOD b].
  have h_b0 : b ^ φ a ≡ 0 [MOD b] := by
    have : b ∣ b ^ φ a := dvd_pow_self b hφa.ne'
    simpa [Nat.modEq_zero_iff_dvd] using this
  -- Euler's theorem, both orientations.
  have h_ba : b ^ φ a ≡ 1 [MOD a] := Nat.ModEq.pow_totient hab.symm
  have h_ab : a ^ φ b ≡ 1 [MOD b] := Nat.ModEq.pow_totient hab
  -- mod a : sum ≡ 0 + 1 = 1.
  have mod_a : a ^ φ b + b ^ φ a ≡ 1 [MOD a] := by
    have := h_a0.add h_ba
    simpa using this
  -- mod b : sum ≡ 1 + 0 = 1.
  have mod_b : a ^ φ b + b ^ φ a ≡ 1 [MOD b] := by
    have := h_ab.add h_b0
    simpa using this
  -- CRT: agreement mod a and mod b ⟹ agreement mod a*b (a, b coprime).
  exact (Nat.modEq_and_modEq_iff_modEq_mul hab).mp ⟨mod_a, mod_b⟩

end Crownproof.InventionWave5
