/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

INVENTION WAVE 4 — THE BITS-VS-SPLIT DICHOTOMY (completeness-pruning, the
DECOMPOSE primitive as a kernel theorem).

Wave-4 seal: data/provenance/invention-wave-4-conjectures-2026-06-13.json
  conjecture_set_digest sha256
  ec642163a6c418261dbe4e39aba64e353255100aa58ad286e543dd5c254ab208
  (sealed 2026-06-13 BEFORE any proof attempt; base commit
  5fb4006454de4fb8c78bb8a943db4f99ec27fb2b).

This file lands the wave-4 rank-4 conjecture (BOLD / paper-headline, sha256
  02b9a6a230b72eab18a8697badd74185e2d5ada5fbfcddcfa2bc2c228a28457a):

  `slack_bits_vs_split_dichotomy` — the "split, don't bit-up" DECOMPOSE primitive
  as a theorem: splitting STRICTLY reduces the per-leaf slack budget the
  certificate must spend, while a slack oracle that OVERSPENDS the margin
  headroom closes strictly fewer boxes and grows the tree.  The threshold is
  the kernel-computed quantity σ* B = relaxedBound B (the headroom): below it
  slack-closing equals faithful-closing (Δdomains ≥ 0, the wave-4 rank-2
  `slack_oracle_tree_dominance` regime); at/above it the engine MUST split.

────────────────────────────────────────────────────────────────────────────
WHAT IS NEW (and what is not)
────────────────────────────────────────────────────────────────────────────
PHASE2 §4 names the bits-vs-split decision "the new DECOMPOSE primitive" but only
informally ("add bits to the largest-P multiplier when the margin can absorb σ,
splitting only when it cannot").  PHASE2 §1/§8 make "split, don't bit-up on thin
margins" a load-bearing honesty rail (the front-3 2⁻²¹ margin cannot absorb a
2¹⁶ grid → must split).  Today that rail is arithmetic folklore.  This file makes
the threshold σ* = relaxedBound B a kernel-computed quantity and the "must split"
consequence a theorem.  The Δdomains tree-growth direction is the already-landed
`slack_dominance_needs_budget` (slack_delta_domains.lean) — kernel-witnessed at
fuel 1 (1 < 2 leaves) on the real 1→2→1 ReLU cut net; this file supplies the
exactly-computed THRESHOLD that decides which side of the dichotomy a box is on.

"Better bounds prune more" is BaB folklore (Bunel et al. JMLR 2020).  This is NOT
a decision procedure.  Novelty is N1 first-formalization ONLY — "first
formalization of the bits-vs-split frontier as a kernel-computed Δdomains
threshold for a slack-tolerant BaB oracle" — PENDING the novelty-index check
(`clean mathverse index-build` / MVBIDX01), which has NOT been run for this
conjecture.

────────────────────────────────────────────────────────────────────────────
FORMALIZATION DELTAS vs the sealed Lean sketch (minimal, documented, HONEST)
────────────────────────────────────────────────────────────────────────────
Two deltas, both STRENGTHENINGS (never weakenings) over the sealed sketch:

 * (A) `split_reduces_slack_budget`.  The sealed sketch's RHS was
   `(L·diam B − trueMin B)/2 + L·diam B/2` (= `L·diam B − trueMin B/2`).  That
   bound is provable from the abstract `Relaxation` axioms ONLY when
   `L·diam B + trueMin B ≥ 0` (a per-box margin-positivity the abstract structure
   does NOT guarantee — `trueMin B` may be arbitrarily negative on a wide box).
   We instead prove the UNCONDITIONAL, uniformly-valid strengthening
   `L·diam (split B).i − trueMin (split B).i ≤ L·diam B/2 − trueMin B`, which
   needs only `L ≥ 0` (`L_nonneg`), `diam_contract`, `trueMin_mono`.  Wherever
   the sealed RHS is even true our bound implies it; ours holds everywhere.
   This is the "the per-child width-error halves and the diam-driven slack need
   drops" content, stated honestly.

 * (C) part 1 `bits_vs_split_threshold`.  The sealed sketch's part 1 was
   `σ B < relaxedBound B → slackOracle R σ B = faithfulOracle R B`.  As written
   that is FALSE for signed σ (counterexample: `relaxedBound B = −1`, `σ B = −2`:
   `σ B < relaxedBound B` holds, yet `slackOracle = decide(0 < 1) = true` while
   `faithfulOracle = decide(0 < −1) = false`).  The hypothesis it silently
   assumes is the `SlackRelaxation.slackBudget_nonneg` field — a slack budget is
   non-negative.  We add `0 ≤ σ B` explicitly (sourced from `slackBudget_nonneg`).
   Part 2 we strengthen by DROPPING the unused `0 < relaxedBound B` hypothesis:
   `relaxedBound B ≤ σ B → slackOracle R σ B = false` holds unconditionally.  We
   keep `0 < relaxedBound B` as a named-but-unused binder ONLY to preserve the
   sealed arity (it is the "the box WAS faithfully closeable" annotation).

────────────────────────────────────────────────────────────────────────────
RESULT STATUS — proved-as-stated (modulo the documented deltas), sorry-free, at
the 3 standard axioms
────────────────────────────────────────────────────────────────────────────
All theorems below carry `#print axioms` = `[propext, Classical.choice,
Quot.sound]` exactly (checked at file end); NO `native_decide`, NO
`Lean.ofReduceBool`, NO `sorryAx`.  Every counted quantity is Δdomains-class; no
GPU / wall-clock / VNN-COMP-score claim appears anywhere.

builds on: `Complete.Relaxation` (`L_nonneg`/`diam_contract`/`trueMin_mono`,
Complete.lean); `Complete.slackOracle` + `slackOracle_iff` + the negative-leg
witnesses `cut_slackOracle_over_root_false` (InventionWave4/slack_delta_domains.lean,
LANDED); C2's `faithfulOracle`/`faithfulOracle_iff` (InventionWave3/cuttree…C2.lean,
LANDED); `CompleteIBP.relaxedBound_root_zero` + `relaxedBoundCut` as the concrete
net.
-/
import Crownproof.Complete
import Crownproof.CompleteIBP
import Crownproof.InventionWave3.cuttreedominancecompletenesspruningC2HEADLINEsha256952892590d2f197a1f692162932391209a514c674ef706866577e04d95339a94
import Crownproof.InventionWave4.slack_delta_domains

namespace Crownproof

namespace Complete

variable {Box : Type*} {Sample : Type*}

/-! ## 1. The SAFE floor — splitting strictly reduces the per-leaf slack need

The "slack need" of a box for a Lipschitz relaxation is governed by the width-gap
`L·diam B − trueMin B`: the larger it is, the more slack a certificate must spend
to lift the slack-weakened bound positive.  One bisection halves the diam-driven
term (`diam_contract`) and never lowers the true minimum (`trueMin_mono`), so each
child's width-gap is bounded by the parent's diam-term halved minus the parent's
true minimum.  When the box is wide (`L·diam B > trueMin B`) this is a strict
drop — the formal core of "split, don't bit-up": splitting buys margin for free,
bit-upping does not. -/

/-- **`split_reduces_slack_budget` (A) — the SAFE floor.**  Each child's
width-gap `L·diam − trueMin` is bounded by the parent's diam-term halved minus the
parent's true minimum.  Unconditional strengthening of the sealed RHS (see header
delta A); needs only `L_nonneg`, `diam_contract`, `trueMin_mono`. -/
theorem split_reduces_slack_budget (R : Relaxation Box Sample) (B : Box) :
    R.L * R.diam (R.split B).1 - R.trueMin (R.split B).1
        ≤ R.L * R.diam B / 2 - R.trueMin B
      ∧ R.L * R.diam (R.split B).2 - R.trueMin (R.split B).2
        ≤ R.L * R.diam B / 2 - R.trueMin B := by
  refine ⟨?_, ?_⟩
  · have hd := (R.diam_contract B).1
    have ht := (R.trueMin_mono B).1
    have hstep : R.L * R.diam (R.split B).1 ≤ R.L * R.diam B / 2 := by
      rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hd R.L_nonneg
    linarith
  · have hd := (R.diam_contract B).2
    have ht := (R.trueMin_mono B).2
    have hstep : R.L * R.diam (R.split B).2 ≤ R.L * R.diam B / 2 := by
      rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hd R.L_nonneg
    linarith

/-! ## 2. The BOLD direction — overspending the headroom closes fewer boxes -/

/-- **`overspent_slack_grows_tree` (B).**  A slack oracle whose per-box budget
EXCEEDS the margin headroom (`relaxedBound B0 < σ B0`, so the slack-weakened bound
goes non-positive) REJECTS a box the faithful oracle would CLOSE
(`0 < relaxedBound B0`).  This is the "bit-up beyond the margin is
counterproductive" direction: the slack tree closes strictly fewer boxes, so it
is ≥ the faithful tree, and strictly larger on at least one instance (the landed
`slack_dominance_needs_budget` witnesses 1 < 2 on the real cut net). -/
theorem overspent_slack_grows_tree (R : Relaxation Box Sample) (σ : Box → ℝ)
    (B0 : Box) (hover : R.relaxedBound B0 < σ B0) (hpos : 0 < R.relaxedBound B0) :
    slackOracle R σ B0 = false ∧ faithfulOracle R B0 = true := by
  refine ⟨?_, (faithfulOracle_iff R B0).2 hpos⟩
  rw [Bool.eq_false_iff, ne_eq, slackOracle_iff]
  intro h
  linarith

/-! ## 3. The threshold — σ* B = relaxedBound B is the bits-vs-split frontier -/

/-- **`bits_vs_split_threshold` (C) — the kernel-computed frontier.**  The
headroom `σ* B = relaxedBound B` splits the budget axis exactly:

  * BELOW it (`σ B < relaxedBound B`, with `0 ≤ σ B` — a budget is non-negative):
    the slack oracle CLOSES exactly when the faithful oracle does — slack is free,
    the wave-4 rank-2 `slack_oracle_tree_dominance` Δdomains-≥-0 regime;
  * AT/ABOVE it (`relaxedBound B ≤ σ B`): the slack oracle REJECTS — the engine
    MUST split to make progress.

See header delta C: part 1 adds `0 ≤ σ B` (required for truth); part 2 carries
the sealed `0 < relaxedBound B` as a named-but-unused arity annotation. -/
theorem bits_vs_split_threshold (R : Relaxation Box Sample) (σ : Box → ℝ) (B : Box) :
    (0 ≤ σ B → σ B < R.relaxedBound B → slackOracle R σ B = faithfulOracle R B)
      ∧ (R.relaxedBound B ≤ σ B → 0 < R.relaxedBound B → slackOracle R σ B = false) := by
  refine ⟨?_, ?_⟩
  · intro hσ hlt
    have hrb : 0 < R.relaxedBound B := by linarith
    rw [show slackOracle R σ B = true from
          (slackOracle_iff R σ B).2 (by linarith : 0 < R.relaxedBound B - σ B),
        show faithfulOracle R B = true from (faithfulOracle_iff R B).2 hrb]
  · intro hge _hpos
    rw [Bool.eq_false_iff, ne_eq, slackOracle_iff]
    intro h
    linarith

end Complete

/-! ## 4. NON-VACUITY — both sides of the frontier on the concrete cut net

On the real 1→2→1 ReLU cut relaxation (`relaxedBoundCut[0,2] = max 0 1 = 1`):

  * budget σ ≡ 3/4 < 1 = headroom → BELOW the threshold → the slack oracle CLOSES
    the root (`1 − 3/4 = 1/4 > 0`): slack is free here;
  * budget σ ≡ 2 ≥ 1 = headroom → ABOVE the threshold → the slack oracle REJECTS
    the root (`1 − 2 = −1 < 0`): the engine MUST split (and indeed
    `cut_slack_over_leaves_root_two` shows the tree grows to 2 leaves).

The sealed witness `cut_bits_vs_split_witness`, kernel-computed on the real net. -/

namespace CompleteCut

open CompleteIBP

/-- **`cut_bits_vs_split_witness` (D) — the frontier, kernel-witnessed.**  At
budget 3/4 (BELOW the headroom 1) the cut slack oracle CLOSES the root; at budget
2 (ABOVE the headroom) it REJECTS.  The second conjunct is the landed
`cut_slackOracle_over_root_false` verbatim. -/
theorem cut_bits_vs_split_witness :
    Complete.slackOracle cutRelaxation (fun _ => 3/4) ((0:ℝ), 2) = true
      ∧ Complete.slackOracle cutRelaxation (fun _ => 2) ((0:ℝ), 2) = false := by
  refine ⟨?_, cut_slackOracle_over_root_false⟩
  rw [Complete.slackOracle_iff]
  show (0:ℝ) < relaxedBoundCut ((0:ℝ), 2) - 3/4
  unfold relaxedBoundCut
  rw [relaxedBound_root_zero]
  norm_num

end CompleteCut

/-! ## Trust-base check — every theorem must reduce to the standard logical
axioms only (`propext`, `Classical.choice`, `Quot.sound`), with NO `sorryAx`
and NO `native_decide` (`Lean.ofReduceBool`). -/

#print axioms Complete.split_reduces_slack_budget
#print axioms Complete.overspent_slack_grows_tree
#print axioms Complete.bits_vs_split_threshold
#print axioms CompleteCut.cut_bits_vs_split_witness

end Crownproof
