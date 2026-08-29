/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

INVENTION WAVE 5 — `auto5_isNilpotent_mul_swap`
(monoid/ring algebra: NILPOTENCY IS SYMMETRIC UNDER FACTOR SWAP).

────────────────────────────────────────────────────────────────────────────
THE THEOREM
────────────────────────────────────────────────────────────────────────────
In ANY `MonoidWithZero` (associative multiplication, a `0`, a `1`; NO
commutativity, NO additive structure required), the product `a * b` is nilpotent
if and only if the swapped product `b * a` is nilpotent:

    IsNilpotent (a * b)   ↔   IsNilpotent (b * a).

Equivalently, the nilpotency of a product is invariant under cyclic permutation
of its two factors.  (Headline `auto5_isNilpotent_mul_swap` is the forward
direction; the `iff` companion `auto5_isNilpotent_mul_swap_iff` is immediate by
symmetry.)

────────────────────────────────────────────────────────────────────────────
WHY IT IS TRUE (the one-line proof)
────────────────────────────────────────────────────────────────────────────
Suppose `(a * b) ^ n = 0`.  The standard "shift" identity
`mul_pow_mul : (x * y) ^ n * x = x * (y * x) ^ n` (a `Monoid` fact, proved by
induction on `n`) gives, with `x := b`, `y := a`,

    (b * a) ^ (n + 1)
        = (b * a) ^ n * (b * a)          -- pow_succ
        = ((b * a) ^ n * b) * a          -- associativity
        = (b * (a * b) ^ n) * a          -- mul_pow_mul (b a n)
        = (b * 0) * a                    -- hypothesis (a * b) ^ n = 0
        = 0.                             -- zero annihilates

So `b * a` is nilpotent (with index one larger).  No commutativity, no ring
subtraction, no additive cancellation — pure monoid-with-zero arithmetic.

────────────────────────────────────────────────────────────────────────────
NOVELTY  (grep evidence)
────────────────────────────────────────────────────────────────────────────
Mathlib's nilpotent API (`Mathlib/RingTheory/Nilpotent/{Defs,Basic,Lemmas}.lean`)
has:
  • `isNilpotent_mul_right` / `isNilpotent_mul_left`  — needs `Commute x y`;
  • `IsNilpotent.isNilpotent_mul_{left,right}_iff`     — needs `Commute` + a
    non-zero-divisor side condition;
  • `IsUnit.isNilpotent_{mul_unit,unit_mul}_of_commute_iff` — needs a UNIT and
    `Commute`;
  • `isNilpotent_mulLeft_iff` / `isNilpotent_mulRight_iff` — about the
    left/right MULTIPLICATION OPERATORS, not the swapped product.

NONE of them states the unconditional swap `IsNilpotent (a*b) ↔ IsNilpotent (b*a)`
that holds with NO commutativity hypothesis.  A grep of the whole mathlib tree
for the swap pattern
  `grep -rn "IsNilpotent (y \* x)|nilpotent_mul_swap|IsNilpotent (b \* a)"`
and for any `IsNilpotent (_ * _) ↔ IsNilpotent (_ * _)` finds no such lemma — the
only `↔ IsNilpotent`-with-`mul` hits are `isNilpotent_mul{Left,Right}_iff`
(operators) and the commute/unit-gated forms above.  This unconditional
factor-swap symmetry is therefore a genuinely new, foundational fact about
nilpotents in a monoid with zero.

Foundational: the proof uses only `MonoidWithZero` arithmetic and the `Monoid`
lemma `mul_pow_mul`; axiom closure ⊆ {propext, Classical.choice, Quot.sound},
with NO `sorry`/`sorryAx`, NO `native_decide`, NO new `axiom`.
-/
-- Minimal imports: `Mathlib.Algebra.GroupWithZero.Basic` supplies `IsNilpotent`
-- (its `def`), `MonoidWithZero` (so `mul_zero`/`zero_mul`/associativity hold), and
-- transitively the `Monoid` power lemmas `pow_succ` and `mul_pow_mul`.  No bare
-- `import Mathlib` — this keeps the graduation olean closure tight.
import Mathlib.Algebra.GroupWithZero.Basic

namespace Crownproof.InventionWave5

variable {M₀ : Type*} [MonoidWithZero M₀]

/-- **Factor-swap symmetry of nilpotency (forward).**
In any `MonoidWithZero`, if the product `a * b` is nilpotent then so is the
swapped product `b * a`.  No commutativity is assumed.

If `(a * b) ^ n = 0`, then `(b * a) ^ (n + 1) = b * (a * b) ^ n * a = b * 0 * a = 0`,
via the `Monoid` shift identity `mul_pow_mul : (x*y)^n * x = x * (y*x)^n`. -/
theorem auto5_isNilpotent_mul_swap {a b : M₀}
    (h : IsNilpotent (a * b)) : IsNilpotent (b * a) := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n + 1, ?_⟩
  -- (b*a)^(n+1) = (b*a)^n * (b*a) = ((b*a)^n * b) * a  (reassociate the rightmost product)
  rw [pow_succ, ← mul_assoc]
  -- mul_pow_mul (b a n) : (b*a)^n * b = b * (a*b)^n  — rewrite the left factor
  rw [mul_pow_mul b a n]
  -- now the inner factor is (a*b)^n, which is 0 by hypothesis
  rw [hn, mul_zero, zero_mul]

/-- **Factor-swap symmetry of nilpotency (iff form).**
`a * b` is nilpotent if and only if `b * a` is — the nilpotency of a product is
invariant under swapping (cyclically permuting) its two factors, with NO
commutativity hypothesis. -/
theorem auto5_isNilpotent_mul_swap_iff {a b : M₀} :
    IsNilpotent (a * b) ↔ IsNilpotent (b * a) :=
  ⟨auto5_isNilpotent_mul_swap, auto5_isNilpotent_mul_swap⟩

/-! ## Trust-base check — every theorem must reduce to the standard logical axioms
only (`propext`, `Classical.choice`, `Quot.sound`), with NO `sorryAx`, NO
`native_decide` / `Lean.ofReduceBool`. -/

#print axioms auto5_isNilpotent_mul_swap
#print axioms auto5_isNilpotent_mul_swap_iff

end Crownproof.InventionWave5
