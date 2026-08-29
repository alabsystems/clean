/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

INVENTION WAVE 4 — SLACK-ORACLE BaB (completeness-pruning, slack-certificate
oracle extension of the landed C1+C2 substrate).

Wave-4 seal: data/provenance/invention-wave-4-conjectures-2026-06-13.json
  conjecture_set_digest sha256
  ec642163a6c418261dbe4e39aba64e353255100aa58ad286e543dd5c254ab208
  (sealed 2026-06-13 BEFORE any proof attempt; base commit
  5fb4006454de4fb8c78bb8a943db4f99ec27fb2b).

This file lands the SLACK-ORACLE lane's two SAFE/HEADLINE legs:

  * conjecture-2 (rank 1, SAFE anchor, sha256
    6094f1a529bf1ee836f543e5dc75fd3b648e9f51900391e5a1e0b2f5f7a37821):
    `slack_delta_domains_exact` + `slack_box_safe_of_leaves` — the exact
    Δdomains identity and whole-box safety composition carry to slack-closed
    leaves.

  * conjecture-1 (rank 2, the headline edge-closer, sha256
    e8a100ccf9c8c9c1266b19f5d77753cafe367bbfff076a3f341029ffa222d55f):
    `slack_oracle_tree_dominance` — budgeted slack oracles dominate under the
    budget-coherence condition (slack spent ≤ margin gained), CLOSING the exact
    edge wave-3's `cut_tree_dominance` rail (2) explicitly scoped OUT.

────────────────────────────────────────────────────────────────────────────
THE NAMED-OUT EDGE THIS LANE CLOSES
────────────────────────────────────────────────────────────────────────────
Wave-3's `cut_tree_dominance` file (completeness-pruning C2 HEADLINE) states,
verbatim, rail (2):

  "The slack / VR2S variant — where the oracle accepts on a slackened margin —
   needs the slack budget on the tight side ≤ the margin gain
   (`SlackFarkas.slack_farkas`) … It is the hard edge and is NOT attempted."

A slack-tolerant oracle is NOT bound-monotone: a tighter bound that costs a
slack budget σ can FAIL the headroom check σ < margin and close FEWER boxes, so
`OracleLE` can fail and the tree can GROW.  `adaptive_tree_dominance` therefore
does NOT apply verbatim.  The mathematical content of this lane is the
BUDGET-COHERENCE condition

      σ_tight B ≤ (relaxedBound_tight B − relaxedBound_loose B) + σ_loose B

(slack spent on the tight side ≤ the bound improvement it buys, plus the loose
side's own slack) under which the slack-weakened tight bound pointwise dominates
the slack-weakened loose bound — so `OracleLE` is RESTORED and
`adaptive_tree_dominance` fires verbatim.  Where budget-coherence FAILS the
dominance is genuinely FALSE; that negative direction is proved in-tree
(`slack_dominance_needs_budget`), NOT hidden.

────────────────────────────────────────────────────────────────────────────
RESULT STATUS — proved-as-stated, sorry-free, at the 3 standard axioms
────────────────────────────────────────────────────────────────────────────
All theorems below carry `#print axioms` = `[propext, Classical.choice,
Quot.sound]` exactly (checked at file end); NO `native_decide`, NO
`Lean.ofReduceBool`, NO `sorryAx`.  Every counted quantity is Δdomains-class
(leaf-list length, `prunedCount`); no GPU / wall-clock / VNN-COMP-score claim
appears anywhere.

────────────────────────────────────────────────────────────────────────────
FORMALIZATION DELTAS vs the sealed Lean sketch (minimal, documented)
────────────────────────────────────────────────────────────────────────────
The sealed `lean_statement_sketch` fields are reproduced faithfully.  Deltas:

 * `slackOracle` is defined with `Classical.propDecidable` exactly as the sketch
   wrote it (`@decide (0 < R.relaxedBound B - sigma B) (Classical.propDecidable _)`).
   `Classical.choice` is already in the trust base (it is what the wave-3
   `faithfulOracle` uses), so no new axiom is introduced.

 * `slackOracle_zero` is stated as `slackOracle R (fun _ => 0) = faithfulOracle R`
   exactly as sealed; proved by `funext` + `sub_zero` (the sketch's route).

 * The negative leg `slack_dominance_needs_budget` is proved with the CLEANEST
   in-tree witness: `Rl = Rt = CompleteCut.cutRelaxation` (so `hsplit`/`hbound`
   are `rfl`/`le_refl`), `sl = fun _ => 0` (closes the root, 1 leaf) and
   `st = fun _ => 2` (OVERSPENT — `relaxedBoundCut[0,2] = 1 < 2`, fails headroom,
   so the root splits into 2 leaves at fuel 1).  This is the sketch's own
   "mirror-image of cut_delta_domains_pos … kernel-computed at fuel 1" route,
   specialised to a single relaxation so the bound hypothesis is `le_refl` — a
   STRICTER (more honest) witness than two different relaxations, since it
   isolates the slack overspend as the sole cause of tree growth.  Documented
   here, claimed nowhere as the general statement.

 * `slack_box_safe_of_leaves` is `adaptive_box_safe_of_leaves`
   (`adaptive…C1.lean:286`) verbatim with `R.decides` → `R.decides_slack` and
   `OracleSound` → `SlackOracleSound`, via a `SlackRelaxation extends Relaxation`
   carrying `slackBudget`/`slackBudget_nonneg`/`decides_slack` exactly as sealed.

────────────────────────────────────────────────────────────────────────────
HONESTY RAILS (carried from the seal)
────────────────────────────────────────────────────────────────────────────
 * Novelty is N1 first-formalization ONLY — "first formalization of Δdomains
   monotonicity for a slack-tolerant (bounded-bitwidth) BaB oracle under the
   slack ≤ margin-gain budget condition", and "first formalization of
   slack-leaf-composable Δdomains accounting" — PENDING the novelty-index check
   (`clean mathverse index-build` / MVBIDX01), which has NOT been run for these
   conjectures.  "Better bounds prune more" is BaB folklore (Bunel et al. JMLR
   2020).  NOT a "decision procedure" (W4 gate).

 * `BudgetCoherent` is STATED, never hidden — without it the dominance is FALSE
   (`slack_dominance_needs_budget` proves this in-tree).

 * `decides_slack`'s premise binding — that the abstract `slackBudget B` IS the
   emitted certificate's residual — is an Obligations-level assumed-as-premise
   edge (the trusted slack-emission interface), stated as a `SlackRelaxation`
   structure field, NOT proven here.  This mirrors how wave-3 `spec_inherit`
   states its margin-binding is trusted.

 * `decides_slack`'s SEMANTIC justification (a slack-weakened bound is still a
   sound lower bound) is the in-tree `SlackFarkas.slack_farkas` headroom
   contract σ < margin (`SlackCertZ.checkSlackEntailmentZ`) — the runtime slack
   leaf check this abstract field models.

builds on: C1's `adaptiveLeaves` + `OracleSound` + `adaptive_box_safe_of_leaves`
+ `adaptive_mem_leaf` + `delta_domains_exact` + `prunedCount`
(InventionWave2/…C1.lean, LANDED); C2's `OracleLE` + `adaptive_tree_dominance` +
`faithfulOracle`/`faithfulOracle_iff` + `CompleteCut.cutRelaxation` /
`relaxedBoundCut` / `cut_faithful_root_true` (InventionWave3/cuttree…C2.lean,
LANDED); `Complete.Relaxation` fixed split/relaxedBound fields (Complete.lean:98);
`CompleteIBP.f_bounds`/`margin_pos`/`relaxedBound_root_zero` (CompleteIBP.lean) as
the concrete net.
-/
import Crownproof.Complete
import Crownproof.CompleteIBP
import Crownproof.InventionWave2.adaptivebabsizecompletenesspruningC1
import Crownproof.InventionWave3.cuttreedominancecompletenesspruningC2HEADLINEsha256952892590d2f197a1f692162932391209a514c674ef706866577e04d95339a94

namespace Crownproof

namespace Complete

variable {Box : Type*} {Sample : Type*}

/-! ## 1. The budgeted slack oracle

`slackOracle R σ B` closes a box iff the SLACK-WEAKENED bound is still strictly
positive: `0 < relaxedBound B − σ B`, where `σ B ≥ 0` is the per-box slack
budget the certificate spends (low-bitwidth dyadic multipliers, σ charged
against the margin — the VR2S / slack-Farkas certificate form).  At `σ = 0` it
collapses to the wave-3 `faithfulOracle`.  Classically decidable; `Classical.choice`
is already in the trust base (wave-3 `faithfulOracle` uses the same device). -/

/-- **Budgeted slack oracle.**  Close `B` iff the slack-weakened bound is still
strictly positive. -/
noncomputable def slackOracle (R : Relaxation Box Sample) (σ : Box → ℝ) (B : Box) : Bool :=
  @decide (0 < R.relaxedBound B - σ B) (Classical.propDecidable _)

theorem slackOracle_iff (R : Relaxation Box Sample) (σ : Box → ℝ) (B : Box) :
    slackOracle R σ B = true ↔ 0 < R.relaxedBound B - σ B := by
  unfold slackOracle
  rw [decide_eq_true_iff]

/-- At zero budget the slack oracle IS the faithful oracle (the wave-3 exact
oracle).  `funext` + `sub_zero`. -/
theorem slackOracle_zero (R : Relaxation Box Sample) :
    slackOracle R (fun _ => 0) = faithfulOracle R := by
  funext B
  unfold slackOracle faithfulOracle
  rw [sub_zero]

/-! ## 2. Budget coherence and the OracleLE supplier (headline edge-closer)

`BudgetCoherent Rl Rt sl st` : on every box, the tight relaxation's slack budget
is bounded by the bound improvement it buys plus the loose side's own slack —
the exact "slack budget on the tight side ≤ the margin gain" condition wave-3
named when it scoped this edge OUT.  Under it the slack-weakened tight bound
pointwise dominates the slack-weakened loose bound, so `OracleLE` holds and
`adaptive_tree_dominance` fires verbatim. -/

/-- **Budget coherence.**  `σ_tight B ≤ (rb_tight B − rb_loose B) + σ_loose B`
for every box — slack spent on the tight side ≤ the bound it buys + loose slack. -/
def BudgetCoherent (Rl Rt : Relaxation Box Sample) (sl st : Box → ℝ) : Prop :=
  ∀ B, st B ≤ (Rt.relaxedBound B - Rl.relaxedBound B) + sl B

/-- **The OracleLE supplier — the only real content (a 3-line `linarith`).**
Under budget coherence the slack-weakened tight bound dominates the slack-weakened
loose bound, so whatever the loose slack oracle closes, the tight one closes. -/
theorem slack_oracle_le_of_budget (Rl Rt : Relaxation Box Sample) (sl st : Box → ℝ)
    (hbudget : BudgetCoherent Rl Rt sl st) :
    OracleLE (slackOracle Rl sl) (slackOracle Rt st) := by
  intro B h
  rw [slackOracle_iff] at h ⊢
  have hb := hbudget B
  linarith

/-- **`slack_oracle_tree_dominance` — THE HEADLINE EDGE-CLOSER.**  For two
relaxations over the SAME box geometry sharing the split rule (`hsplit`), with
budget coherence (`hbudget` — slack ≤ margin-gain), the budgeted slack oracle of
the tight relaxation's adaptive tree is a pruned subtree of the loose one at
every fuel/box:

      (adaptiveLeaves Rt (slackOracle Rt st) d B).length
        ≤ (adaptiveLeaves Rl (slackOracle Rl sl) d B).length,

i.e. Δdomains(slack-cut) ≥ 0 — turning wave-3's excluded slack/VR2S case into a
discharged hypothesis.  A ONE-LINE application of the landed
`adaptive_tree_dominance` with the supplied `OracleLE` — NO new induction. -/
theorem slack_oracle_tree_dominance (Rl Rt : Relaxation Box Sample) (sl st : Box → ℝ)
    (hsplit : Rl.split = Rt.split)
    (hbudget : BudgetCoherent Rl Rt sl st) (d : ℕ) (B : Box) :
    (adaptiveLeaves Rt (slackOracle Rt st) d B).length
      ≤ (adaptiveLeaves Rl (slackOracle Rl sl) d B).length :=
  adaptive_tree_dominance Rl Rt (slackOracle Rl sl) (slackOracle Rt st)
    hsplit (slack_oracle_le_of_budget Rl Rt sl st hbudget) d B

/-! ## 3. Slack soundness and the safety composition (SAFE anchor)

A slack oracle closes a box on the slack-weakened bound `0 < relaxedBound B − σ B`,
which does NOT imply `0 < relaxedBound B` — so the exact `OracleSound` /
`R.decides` composition of C1 does not apply.  `SlackOracleSound` is the matching
soundness predicate; `SlackRelaxation` carries the `decides_slack` bridge
(the trusted slack-emission interface: a positive slack-weakened bound on a box
proves the property on every point of that box — the abstract model of the
`SlackCertZ.checkSlackEntailmentZ` headroom-σ<margin runtime check). -/

/-- **Slack oracle soundness.**  The oracle only closes boxes whose
slack-weakened bound is strictly positive. -/
def SlackOracleSound (R : Relaxation Box Sample) (σ : Box → ℝ) (closes : Box → Bool) : Prop :=
  ∀ B, closes B = true → 0 < R.relaxedBound B - σ B

/-- A `Relaxation` augmented with the slack-leaf-decision interface.  `slackBudget`
is the per-box slack a slack-tolerant certificate spends; `decides_slack` is the
trusted bridge that a positive slack-weakened bound certifies safety on the box
(modelling `SlackCertZ.checkSlackEntailmentZ`, whose soundness bottoms out in
`SlackFarkas.slack_farkas`).  The premise binding (`slackBudget B` IS the emitted
certificate's residual) is an Obligations-level assumed-as-premise edge — a
structure field, STATED not proven. -/
structure SlackRelaxation (Box : Type*) (Sample : Type*) extends Relaxation Box Sample where
  slackBudget        : Box → ℝ
  slackBudget_nonneg : ∀ B, 0 ≤ slackBudget B
  decides_slack      : ∀ B, 0 < relaxedBound B - slackBudget B → ∀ s, mem B s → safe s

/-- **`slack_box_safe_of_leaves` — the SAFE-anchor safety composition.**  A
slack-sound oracle whose every adaptive leaf is closed composes to whole-box
safety through `adaptive_mem_leaf` + `SlackOracleSound` + `R.decides_slack` —
`adaptive_box_safe_of_leaves` (C1) verbatim with `R.decides` → `R.decides_slack`
and `OracleSound` → `SlackOracleSound`.  This is the leg that lets ANY
slack-oracle Δdomains result certify a SAFE verdict, not just count leaves. -/
theorem slack_box_safe_of_leaves (R : SlackRelaxation Box Sample) (closes : Box → Bool)
    (hs : SlackOracleSound R.toRelaxation R.slackBudget closes) (d : ℕ) (B : Box)
    (hleaf : ∀ C ∈ adaptiveLeaves R.toRelaxation closes d B, closes C = true) :
    ∀ s, R.mem B s → R.safe s := by
  intro s hms
  obtain ⟨C, hCmem, hCs⟩ := adaptive_mem_leaf R.toRelaxation closes d B s hms
  exact R.decides_slack C (hs C (hleaf C hCmem)) s hCs

/-! ## 4. The exact Δdomains identity carries to slack-closed leaves (SAFE anchor)

`delta_domains_exact` (C1) is already universally quantified over the oracle —
it is purely combinatorial in `closes`, independent of WHY a box closes — so it
specialises to `slackOracle` for FREE.  A whole-run BaB tree that mixes exact and
slack leaves still has length + pruned = 2^d, kernel-checked. -/

/-- **`slack_delta_domains_exact` — the exact Δdomains identity for slack leaves.**
A ONE-LINE specialisation of the oracle-universal C1 `delta_domains_exact`:

      (adaptiveLeaves R (slackOracle R σ) d B).length
        + prunedCount R (slackOracle R σ) d B = 2 ^ d. -/
theorem slack_delta_domains_exact (R : Relaxation Box Sample) (σ : Box → ℝ)
    (d : ℕ) (B : Box) :
    (adaptiveLeaves R (slackOracle R σ) d B).length
      + prunedCount R (slackOracle R σ) d B = 2 ^ d :=
  delta_domains_exact R (slackOracle R σ) d B

end Complete

/-! ## 5. NON-VACUITY — the slack oracle on the concrete cut relaxation

The cut relaxation of the real 1→2→1 ReLU net (`CompleteCut.cutRelaxation`,
`relaxedBoundCut[0,2] = max 0 1 = 1`).  A slack budget σ ≡ 1/4 at the root still
leaves `1 − 1/4 = 3/4 > 0`, so the slack oracle CLOSES the root in 1 leaf with
positive headroom: Δdomains = prunedCount = 2^d − 1 > 0 — the SAFE-anchor's
kernel-witnessed non-vacuity. -/

namespace CompleteCut

open CompleteIBP

/-- The CUT slack oracle with budget σ ≡ 1/4 ACCEPTS the root `[0,2]`:
`relaxedBoundCut[0,2] − 1/4 = 1 − 1/4 = 3/4 > 0`.  Analogue of
`cut_faithful_root_true` with positive slack spent inside the margin headroom. -/
theorem cut_slackOracle_root_true :
    Complete.slackOracle cutRelaxation (fun _ => 1/4) ((0:ℝ), 2) = true := by
  rw [Complete.slackOracle_iff]
  show (0:ℝ) < relaxedBoundCut ((0:ℝ), 2) - 1/4
  unfold relaxedBoundCut
  rw [relaxedBound_root_zero]
  norm_num

/-- The slack tree at fuel 1 on the root is EXACTLY 1 leaf `[[0,2]]`: the slack
oracle closes the root (headroom 3/4 > 0), so it is never split. -/
theorem cut_slack_leaves_root_one :
    Complete.adaptiveLeaves cutRelaxation
        (Complete.slackOracle cutRelaxation (fun _ => 1/4)) 1 ((0:ℝ), 2)
      = [((0:ℝ), 2)] := by
  simp only [Complete.adaptiveLeaves, cut_slackOracle_root_true, if_true]

/-- **Non-vacuity, kernel-witnessed: Δdomains = prunedCount = 1 > 0 at fuel 1.**
The slack oracle (budget 1/4, spent inside the 3/4 headroom) closes the root, so
1 of the 2 uniform fuel-1 domains is pruned — `slack_delta_domains_exact`
instantiated and evaluated on the real net. -/
theorem cut_slack_delta_domains_pos :
    0 < Complete.prunedCount cutRelaxation
          (Complete.slackOracle cutRelaxation (fun _ => 1/4)) 1 ((0:ℝ), 2) := by
  have h := Complete.slack_delta_domains_exact cutRelaxation (fun _ => 1/4) 1 ((0:ℝ), 2)
  rw [cut_slack_leaves_root_one] at h
  norm_num at h
  omega

/-! ### The negative leg — budget coherence is LOAD-BEARING

Where budget coherence FAILS the dominance is genuinely FALSE.  Witness (the
cleanest possible, isolating slack as the sole cause): a SINGLE relaxation
`cutRelaxation` (so the split rule and the bound are identical — `hsplit` by
`rfl`, `hbound` by `le_refl`) with two budgets.  `sl ≡ 0` closes the root
(`relaxedBoundCut[0,2] = 1 > 0`), 1 leaf.  `st ≡ 2` OVERSPENDS the headroom
(`1 − 2 = −1 < 0`), so the root splits into 2 leaves at fuel 1.  `1 < 2`: the
"tighter side" (here equal-bound but slack-overspending) tree is STRICTLY
LARGER — exactly the non-monotonicity wave-3 named.  Budget coherence is the
hypothesis that rules this out. -/

/-- The zero-budget slack oracle ACCEPTS the root (it IS the faithful oracle
there: `relaxedBoundCut[0,2] = 1 > 0`). -/
theorem cut_slackOracle_zero_root_true :
    Complete.slackOracle cutRelaxation (fun _ => 0) ((0:ℝ), 2) = true := by
  rw [Complete.slackOracle_iff]
  show (0:ℝ) < relaxedBoundCut ((0:ℝ), 2) - 0
  unfold relaxedBoundCut
  rw [relaxedBound_root_zero]
  norm_num

/-- The overspent (budget 2) slack oracle REJECTS the root: `1 − 2 = −1 < 0`,
the budget exceeds the entire margin headroom. -/
theorem cut_slackOracle_over_root_false :
    Complete.slackOracle cutRelaxation (fun _ => 2) ((0:ℝ), 2) = false := by
  rw [Bool.eq_false_iff, ne_eq, Complete.slackOracle_iff]
  show ¬ (0:ℝ) < relaxedBoundCut ((0:ℝ), 2) - 2
  unfold relaxedBoundCut
  rw [relaxedBound_root_zero]
  norm_num

/-- The zero-budget slack tree at fuel 1 on the root: 1 leaf `[[0,2]]`. -/
theorem cut_slack_zero_leaves_root_one :
    Complete.adaptiveLeaves cutRelaxation
        (Complete.slackOracle cutRelaxation (fun _ => 0)) 1 ((0:ℝ), 2)
      = [((0:ℝ), 2)] := by
  simp only [Complete.adaptiveLeaves, cut_slackOracle_zero_root_true, if_true]

/-- The overspent slack tree at fuel 1 on the root: 2 leaves `[[0,1],[1,2]]`
(root rejected, both children un-expanded at fuel 1). -/
theorem cut_slack_over_leaves_root_two :
    Complete.adaptiveLeaves cutRelaxation
        (Complete.slackOracle cutRelaxation (fun _ => 2)) 1 ((0:ℝ), 2)
      = [((0:ℝ), 1), ((1:ℝ), 2)] := by
  rw [Complete.adaptiveLeaves, cut_slackOracle_over_root_false]
  simp only [Bool.false_eq_true, if_false]
  show Complete.adaptiveLeaves cutRelaxation
        (Complete.slackOracle cutRelaxation (fun _ => 2)) 0
        (cutRelaxation.split ((0:ℝ), 2)).1
      ++ Complete.adaptiveLeaves cutRelaxation
        (Complete.slackOracle cutRelaxation (fun _ => 2)) 0
        (cutRelaxation.split ((0:ℝ), 2)).2
      = [((0:ℝ), 1), ((1:ℝ), 2)]
  simp only [Complete.adaptiveLeaves, cutRelaxation, split]
  norm_num

/-- **`slack_dominance_needs_budget` — budget coherence is LOAD-BEARING.**
There exist two relaxations (here the SAME `cutRelaxation`, isolating slack as
the sole cause) sharing the split and with the loose bound ≤ the tight bound,
whose slack-budgeted adaptive trees satisfy `count_loose < count_tight`: WITHOUT
budget coherence the slack-tolerant dominance is FALSE.  This is the negative
direction wave-3 named when it scoped the edge OUT — proved in-tree, kernel-
witnessed at fuel 1 (1 < 2), NOT asserted. -/
theorem slack_dominance_needs_budget :
    ∃ (Rl Rt : Complete.Relaxation Box ℝ) (sl st : Box → ℝ) (d : ℕ) (B : Box),
      Rl.split = Rt.split ∧
      (∀ B, Rl.relaxedBound B ≤ Rt.relaxedBound B) ∧
      (Complete.adaptiveLeaves Rl (Complete.slackOracle Rl sl) d B).length
        < (Complete.adaptiveLeaves Rt (Complete.slackOracle Rt st) d B).length := by
  refine ⟨cutRelaxation, cutRelaxation, (fun _ => 0), (fun _ => 2), 1, ((0:ℝ), 2),
    rfl, fun _ => le_refl _, ?_⟩
  rw [cut_slack_zero_leaves_root_one, cut_slack_over_leaves_root_two]
  norm_num

end CompleteCut

/-! ## Trust-base check — every theorem must reduce to the standard logical
axioms only (`propext`, `Classical.choice`, `Quot.sound`), with NO `sorryAx`
and NO `native_decide` (`Lean.ofReduceBool`). -/

#print axioms Complete.slackOracle_iff
#print axioms Complete.slackOracle_zero
#print axioms Complete.slack_oracle_le_of_budget
#print axioms Complete.slack_oracle_tree_dominance
#print axioms Complete.slack_box_safe_of_leaves
#print axioms Complete.slack_delta_domains_exact
#print axioms CompleteCut.cut_slackOracle_root_true
#print axioms CompleteCut.cut_slack_leaves_root_one
#print axioms CompleteCut.cut_slack_delta_domains_pos
#print axioms CompleteCut.cut_slackOracle_zero_root_true
#print axioms CompleteCut.cut_slackOracle_over_root_false
#print axioms CompleteCut.cut_slack_zero_leaves_root_one
#print axioms CompleteCut.cut_slack_over_leaves_root_two
#print axioms CompleteCut.slack_dominance_needs_budget

end Crownproof
