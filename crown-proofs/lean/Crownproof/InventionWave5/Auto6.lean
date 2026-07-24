/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

INVENTION WAVE 5 — `auto6_hlawka_abs_real`
(real-number inequalities — HLAWKA'S INEQUALITY for the absolute value on ℝ).

────────────────────────────────────────────────────────────────────────────
THE THEOREM
────────────────────────────────────────────────────────────────────────────
For all real `a, b, c`:

    |a + b| + |b + c| + |c + a|  ≤  |a| + |b| + |c| + |a + b + c|.

This is **Hlawka's inequality**, the classical pairwise/triple-sum bound that in
general normed/inner-product spaces characterises a subclass of norms.  The
present statement is its one-dimensional (absolute-value) instance over the real
line — the base case from which the inner-product-space version is usually
bootstrapped, and a sharp, non-trivial three-variable inequality in its own right.

It is strictly stronger than naïvely chaining the triangle inequality: the
triangle inequality alone gives `|a+b| ≤ |a|+|b|`, summing to
`|a+b|+|b+c|+|c+a| ≤ 2(|a|+|b|+|c|)`, which is WEAKER than Hlawka whenever
`|a+b+c| < |a|+|b|+|c|` (i.e. whenever the signs are not all aligned).  Hlawka
replaces one full copy of `|a|+|b|+|c|` by the single combined term `|a+b+c|`.

────────────────────────────────────────────────────────────────────────────
NOVELTY
────────────────────────────────────────────────────────────────────────────
N1 first-formalization.  A grep of the whole Mathlib source
(`.lake/packages/mathlib/Mathlib/`) for `hlawka` (case-insensitive) returns
NOTHING, and no lemma of the shape `|a+b| + |b+c| + |c+a| ≤ …` (or the norm
analogue `‖a+b‖ + ‖b+c‖ + ‖c+a‖ ≤ …`) exists.  Mathlib has the triangle
inequality (`abs_add`), `abs_sub_abs_le_abs_sub`, `abs_min_sub_min_le_max`, and
the max/min–abs identities, but NOT Hlawka.  This is a genuinely new,
named, classical inequality — not a one-step restatement of any existing lemma.

────────────────────────────────────────────────────────────────────────────
PROOF SHAPE (foundational; no domain axioms)
────────────────────────────────────────────────────────────────────────────
Over ℝ the absolute value is `max x (-x)`, so each `|·|` term is decided by the
sign of its argument.  `abs_cases` splits every one of the seven absolute values
into its two linear branches; in each branch the goal is a linear inequality in
`a, b, c` that `nlinarith` discharges from the accumulated sign hypotheses.
Only foundational tactics (`nlinarith`/`linarith`) and order/abs lemmas are used:
axioms ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no `native_decide`,
no new axiom.
-/
-- Minimal imports: ℝ with its order, the `abs_cases` lemma (Group/Abs), and
-- `nlinarith` (Tactic.Linarith). NOT bare `import Mathlib`.
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Tactic.Linarith

namespace Crownproof.InventionWave5

/-- **Hlawka's inequality (absolute-value / real case).**
For all real `a, b, c`,
`|a + b| + |b + c| + |c + a| ≤ |a| + |b| + |c| + |a + b + c|`.

This is the one-dimensional instance of the classical Hlawka inequality.  It is
sharp and strictly stronger than the triangle-inequality bound
`|a+b|+|b+c|+|c+a| ≤ 2(|a|+|b|+|c|)`: Hlawka contracts one copy of the
single-variable sum into the combined term `|a+b+c|`. -/
theorem auto6_hlawka_abs_real (a b c : ℝ) :
    |a + b| + |b + c| + |c + a| ≤ |a| + |b| + |c| + |a + b + c| := by
  rcases abs_cases a with ⟨ha, ha'⟩ | ⟨ha, ha'⟩ <;>
  rcases abs_cases b with ⟨hb, hb'⟩ | ⟨hb, hb'⟩ <;>
  rcases abs_cases c with ⟨hc, hc'⟩ | ⟨hc, hc'⟩ <;>
  rcases abs_cases (a + b) with ⟨hab, hab'⟩ | ⟨hab, hab'⟩ <;>
  rcases abs_cases (b + c) with ⟨hbc, hbc'⟩ | ⟨hbc, hbc'⟩ <;>
  rcases abs_cases (c + a) with ⟨hca, hca'⟩ | ⟨hca, hca'⟩ <;>
  rcases abs_cases (a + b + c) with ⟨habc, habc'⟩ | ⟨habc, habc'⟩ <;>
  · rw [ha, hb, hc, hab, hbc, hca, habc]; linarith

end Crownproof.InventionWave5
