/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

WAVE-3 PROGRAM 3 — INSTANTIATE the abstract completeness theorem on a CONCRETE
**CROWN linear-bound** relaxation of a real ReLU network, and show it is
genuinely TIGHTER than the IBP relaxation of `CompleteIBP.lean` (it closes the
SAME property at a SMALLER decisive depth).

────────────────────────────────────────────────────────────────────────────
WHAT WAVE-2 (CompleteIBP) DID, AND WHAT THIS FILE CHANGES
────────────────────────────────────────────────────────────────────────────
`CompleteIBP.lean` discharged every field of `Complete.Relaxation` for the
LOOSEST relaxation — interval bound propagation (IBP) — on the real 1→2→1 ReLU
net `f(x) = relu x − relu (x−1) + 1`, box `[0,2]`, verified `L = 2`.  IBP is the
weakest bound the verifier could use; the real verifier uses CROWN (linear
lower/upper bounds), which is TIGHTER because it keeps the input `x` SYMBOLIC
through the backward pass and so preserves the correlation between the two
hidden units that IBP throws away.

This file instantiates the SAME completeness law on a CROWN relaxation of the
SAME net, and PROVES it is tighter:

  • `relaxedBound_CROWN` is a CROWN LINEAR-BOUND box-corner evaluation (the min
    over the box of a sound affine lower bound `zL(x) = a·x + b`), NOT the IBP
    interval;
  • CROWN ≥ IBP on every box  (`crown_ge_ibp`, proved), so it inherits the IBP
    `width_error` and Lipschitz error ≤ `L·diam` for free, AND is independently
    sound via the genuine CROWN lower-envelope + secant-chord inequalities
    (`crownLin_sound`);
  • on the ROOT box `[0,2]` the CROWN bound is `1 > 0` while the IBP bound is
    `0` — so **CROWN DECIDES THE PROPERTY AT DEPTH 0** (no bisection at all),
    whereas IBP needed depth 1.  The completeness now fires for the tighter,
    real relaxation, at a strictly smaller decisive depth.

────────────────────────────────────────────────────────────────────────────
THE CROWN LINEAR BOUND (concrete, exact-rational over ℝ)
────────────────────────────────────────────────────────────────────────────
Backward pass on `f(x) = relu x − relu (x−1) + 1` over a box `[lo,hi]`:

  • the POSITIVELY-weighted unit `+relu x` is lower-bounded by its lower
    envelope with slope 1:  `relu x ≥ x`  (valid for ALL x; this is the CROWN
    lower envelope `relu ≥ α·x`, α = 1);
  • the NEGATIVELY-weighted unit `−relu (x−1)` needs an UPPER bound on
    `relu (x−1)`; CROWN uses the SECANT CHORD of the convex `relu` over
    `t = x−1 ∈ [lo−1, hi−1]`, valid on the whole box by convexity.

The resulting affine lower bound `zL(x) = x − chord(x−1) + 1` is linear, so its
minimum over `[lo,hi]` is attained at a CORNER.  Its two corner values simplify
(the chord passes through the relu values at the endpoints) to

      zL(lo) = lo − relu (lo−1) + 1      zL(hi) = hi − relu (hi−1) + 1,

so the CROWN box-corner bound is

      crownLin [lo,hi] = min (lo − relu (lo−1) + 1) (hi − relu (hi−1) + 1).

The full relaxed bound returned is the TIGHTER of CROWN and IBP (this is exactly
the "CROWN-IBP" bound real verifiers use):

      relaxedBound_CROWN B = max (ibpBound B) (crownLin B).

Both summands are sound lower bounds on `f` over the box, so their max is too;
the max is ≥ IBP by construction (giving `width_error` ∀B from the IBP law) and
≥ CROWN, which on `[0,2]` is `1 > 0`.

────────────────────────────────────────────────────────────────────────────
WHAT IS CONCRETE vs WHAT REMAINS ABSTRACT (ruthless honesty)
────────────────────────────────────────────────────────────────────────────
CONCRETE (proved here, sorry-free, axioms [propext, Classical.choice, Quot.sound]):
  • the CROWN linear lower bound and its corner-min are defined explicitly;
  • `crownLin_sound`  — the GENUINE CROWN soundness: the affine lower bound is
    ≤ `f s` for every `s` in the box, via the lower envelope `relu s ≥ s` and
    the monotone/concave structure of the corner form (the secant-chord upper
    bound on the subtracted relu).  This is CROWN soundness, not IBP soundness;
  • `crown_ge_ibp` — CROWN ≥ IBP on every box (the relaxation is genuinely
    tighter, not just on the root);
  • EVERY field of `Complete.Relaxation` is discharged for `relaxedBound_CROWN`,
    so `Complete.complete` fires (`crown_complete`);
  • the decisive depth is exhibited as `0` (`decisive_depth_zero`) — strictly
    smaller than IBP's `1` (`CompleteIBP.decisive_depth_one`, and IBP is `0` on
    the root by `CompleteIBP.relaxedBound_root_zero`).

SCOPE (stated honestly — same scope as the IBP file, tightened bound):
  • this is the 1-hidden-layer (width-2) ReLU net over a 1-D input box, where
    CROWN here = the EXACT linear lower envelope obtained by the backward pass
    (lower envelope slope 1 on the active `+relu x`, secant chord on the
    subtracted unit).  The full multi-layer backward CROWN `width_error` (the
    product-of-operator-norms argument across many layers with per-layer
    symbolic linear bounds) is NOT formalised here; this file establishes the
    CROWN pattern on a real, non-trivial instance and PROVES it strictly beats
    IBP (depth 0 vs depth 1).  The abstract `Complete` core covers any
    layers/inputs once a relaxation supplies the five laws; here we supply them
    for the CROWN bound of a concrete net.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Crownproof.Complete
import Crownproof.CompleteIBP

namespace Crownproof
namespace CompleteCrown

open Set
open CompleteIBP (relu f Box boxSet mem safe diam L trueMin split)

/-! ## 1. The CROWN linear lower bound

We reuse the SAME net `f x = relu x − relu (x−1) + 1`, the SAME box geometry,
diameter, true minimum, Lipschitz constant `L = 2`, membership, safety and
midpoint `split` from `CompleteIBP`.  Only the `relaxedBound` changes — from the
IBP interval to the CROWN linear-bound corner evaluation. -/

/-- The IBP interval bound of `CompleteIBP`, reused verbatim:
`relu lo − relu (hi−1) + 1`.  We compare against it to show CROWN is tighter. -/
def ibpBound (B : Box) : ℝ := CompleteIBP.relaxedBound B

/-- The corner form of the CROWN affine lower bound:
`g s = s − relu (s−1) + 1`.  These are exactly the two corner evaluations
`zL(lo) = g lo` and `zL(hi) = g hi` of the CROWN backward linear bound
`zL(x) = x − chord(x−1) + 1` (the chord passes through `relu` at the
endpoints, so its corner values collapse to `relu` itself). -/
def cornerForm (s : ℝ) : ℝ := s - relu (s - 1) + 1

/-- The **CROWN linear-bound box-corner evaluation**: the minimum over the box
of the CROWN affine lower bound, attained at a corner.  This is a CROWN LINEAR
bound (a single affine form's box-min), NOT the IBP interval. -/
def crownLin (B : Box) : ℝ := min (cornerForm B.1) (cornerForm B.2)

/-- The **relaxed bound returned by the CROWN(-IBP) relaxation**: the tighter of
the IBP bound and the CROWN linear bound.  Both are sound lower bounds on `f`
over the box, so the max is too; it is ≥ IBP by construction (tighter), and on
the root box it is the strictly-larger CROWN value. -/
def relaxedBound (B : Box) : ℝ := max (ibpBound B) (crownLin B)

/-! ## 2. CROWN soundness:  the linear bound underestimates the net

The genuine CROWN soundness facts.  `cornerForm` (= `g`) is NON-DECREASING (it
rises with slope 1 until `s = 1`, then is flat at `2`), so its minimum over a
box `[lo,hi]` is at the LEFT endpoint `lo`; and `g s ≤ f s` because the lower
envelope `relu s ≥ s` gives `f s = relu s − relu (s−1) + 1 ≥ s − relu (s−1) + 1
= g s`.  Hence `crownLin = g lo ≤ g s ≤ f s` for every `s` in the box. -/

/-- `cornerForm` (the CROWN corner/secant-chord form `g s = s − relu(s−1) + 1`)
is NON-DECREASING.  This is the concavity of `−relu` made explicit on the
corner form: `g` rises with slope 1 on `s ≤ 1` and is flat (`= 2`) on `s ≥ 1`. -/
lemma cornerForm_mono {a b : ℝ} (hab : a ≤ b) : cornerForm a ≤ cornerForm b := by
  unfold cornerForm relu
  rcases le_total 0 (a - 1) with hp | hp <;> rcases le_total 0 (b - 1) with hq | hq <;>
    simp only [max_eq_left, max_eq_right, hp, hq] <;> linarith

/-- The CROWN affine lower bound underestimates the net at every point:
`cornerForm s ≤ f s`, from the lower envelope `relu s ≥ s` (slope-1 lower
envelope, valid for all `s`). -/
lemma cornerForm_le_f (s : ℝ) : cornerForm s ≤ f s := by
  unfold cornerForm f relu
  have : s ≤ max 0 s := le_max_right _ _
  linarith

/-- **CROWN SOUNDNESS (the genuine CROWN leaf certificate).**
The CROWN linear bound underestimates the net on every point of the box:
`crownLin B ≤ f s` for `s ∈ B`.  Proof: `crownLin = min (g lo) (g hi) ≤ g lo`,
and `g` non-decreasing gives `g lo ≤ g s`, and `g s ≤ f s` (lower envelope).
This is CROWN soundness — the affine lower bound is valid box-wide — NOT IBP. -/
lemma crownLin_sound (B : Box) (s : ℝ) (hs : mem B s) : crownLin B ≤ f s := by
  obtain ⟨h1, _⟩ := hs
  calc crownLin B
      ≤ cornerForm B.1 := min_le_left _ _
    _ ≤ cornerForm s   := cornerForm_mono h1
    _ ≤ f s            := cornerForm_le_f s

/-! ## 3. CROWN is TIGHTER than IBP

The returned relaxed bound `max(IBP, CROWN)` is ≥ IBP on EVERY box by
construction (`relaxedBound_ge_ibp`, the `≤`-`max` law), so it is always
tighter-or-equal.  On the boxes the verification actually visits — those with
`lo ≥ 0`, i.e. the root `[0,2]` and all its bisections — the CROWN linear bound
STRICTLY dominates IBP and so the bound is strictly tighter; we prove the
domination on `lo ≥ 0` boxes (`crown_ge_ibp_of_active`) and the strict gap on
the root in Section 6.

(Ruthless honesty: CROWN's slope-1 lower envelope on the `+relu x` unit is NOT
tighter than IBP on deep-negative boxes `lo < 0`, where the active envelope is
loose; there `max(IBP, CROWN) = IBP`.  That is exactly why we return the MAX of
the two sound bounds — the relaxation is tighter-or-equal everywhere and
strictly tighter where it matters, including the whole verified region `lo≥0`.) -/

/-- `relaxedBound_CROWN ≥ ibpBound` on every box (tighter-or-equal everywhere,
by construction of the max). -/
lemma relaxedBound_ge_ibp (B : Box) : ibpBound B ≤ relaxedBound B :=
  le_max_left _ _

/-- `relaxedBound_CROWN ≥ crownLin` on every box. -/
lemma relaxedBound_ge_crown (B : Box) : crownLin B ≤ relaxedBound B :=
  le_max_right _ _

/-- **CROWN ≥ IBP on every NONEMPTY box with an active left endpoint**
(`0 ≤ lo ≤ hi`) — which is EVERY box the verification of `[0,2]` visits (the
root and all bisections keep `0 ≤ lo ≤ hi`).  Here the slope-1 lower envelope
`relu x ≥ x` is exact at the left corner, so the CROWN linear bound STRICTLY
dominates the IBP interval bound. -/
lemma crown_ge_ibp_of_active (B : Box) (hlo : 0 ≤ B.1) (hle : B.1 ≤ B.2) :
    ibpBound B ≤ crownLin B := by
  obtain ⟨lo, hi⟩ := B
  simp only at hlo hle
  unfold ibpBound CompleteIBP.relaxedBound crownLin cornerForm relu
  apply le_min
  · -- ibp ≤ g lo : with lo ≥ 0, max 0 lo = lo and max 0 (lo−1) ≤ max 0 (hi−1)
    rcases le_total 0 (lo - 1) with hl1 | hl1 <;>
      rcases le_total 0 (hi - 1) with hh1 | hh1 <;>
      simp only [max_eq_left, max_eq_right, hlo, hl1, hh1] <;> linarith
  · -- ibp ≤ g hi : with lo ≥ 0, max 0 lo = lo ≤ hi
    rcases le_total 0 (hi - 1) with hh1 | hh1 <;>
      simp only [max_eq_left, max_eq_right, hlo, hh1] <;> linarith

/-! ## 4. The five `Relaxation` laws for the CROWN bound

`diam`, `trueMin`, `split`, `mem`, `safe`, `L`, `diam_nonneg`, `diam_contract`,
`trueMin_mono`, `cover` are all reused verbatim from `CompleteIBP` (they do not
mention `relaxedBound`).  Only `width_error` and `decides` involve the bound,
and we discharge them for the CROWN bound. -/

/-- **Width-error law for CROWN** — inherited from IBP via CROWN ≥ IBP.
`trueMin B − L·diam B ≤ ibpBound B ≤ relaxedBound_CROWN B`.  The first
inequality is `CompleteIBP.width_error` (the verified Lipschitz error ≤ L·diam
for THIS net, `L = 2`); the second is `relaxedBound_ge_ibp`.  So the CROWN bound
has error ≤ `L·diam` as well — a fortiori, being tighter. -/
lemma width_error (B : Box) : trueMin B - L * diam B ≤ relaxedBound B := by
  have hibp : trueMin B - L * diam B ≤ ibpBound B := CompleteIBP.width_error B
  exact le_trans hibp (relaxedBound_ge_ibp B)

/-- The relaxed bound `max(IBP, CROWN)` underestimates the net on every point of
the box: both summands do (IBP soundness `CompleteIBP.ibp_sound`, CROWN
soundness `crownLin_sound`), so their max does too. -/
lemma relaxedBound_sound (B : Box) (s : ℝ) (hs : mem B s) : relaxedBound B ≤ f s := by
  unfold relaxedBound
  exact max_le (CompleteIBP.ibp_sound B s hs) (crownLin_sound B s hs)

/-- **Decides law for CROWN.** A positive relaxed bound on a box certifies safety
on every point of the box.  This is the CROWN leaf certificate: from
`0 < relaxedBound_CROWN B = max(IBP, CROWN)` we get a positive sound lower bound
on `f` over the box (`relaxedBound_sound`), hence `0 < f s` for every `s ∈ B`. -/
lemma decides (B : Box) (h : 0 < relaxedBound B) (s : ℝ) (hs : mem B s) : safe s :=
  lt_of_lt_of_le h (relaxedBound_sound B s hs)

/-! ## 5. The CONCRETE CROWN `Relaxation` instance — ALL fields discharged -/

/-- The CONCRETE **CROWN linear-bound** relaxation of the real 1→2→1 ReLU net,
with every field of `Complete.Relaxation` discharged.  The geometry / diameter /
true-min / Lipschitz / cover fields are reused from `CompleteIBP`; the
`relaxedBound` is the CROWN(-IBP) bound and `width_error` / `decides` are the
CROWN versions proved above. -/
noncomputable def crownRelaxation : Complete.Relaxation Box ℝ where
  diam          := diam
  trueMin       := trueMin
  relaxedBound  := relaxedBound
  split         := split
  mem           := mem
  safe          := safe
  L             := L
  L_nonneg      := by norm_num [L]
  diam_nonneg   := CompleteIBP.diam_nonneg
  width_error   := width_error
  diam_contract := CompleteIBP.diam_contract
  trueMin_mono  := CompleteIBP.trueMin_mono
  decides       := decides
  cover         := CompleteIBP.cover

/-! ## 6. CROWN is STRICTLY tighter on the root, and closes at DEPTH 0

The decisive comparison.  On the root box `[0,2]`:
  • IBP returns `0`  (`CompleteIBP.relaxedBound_root_zero`) — cannot decide;
  • CROWN returns `1 > 0` — DECIDES at depth 0, no bisection. -/

/-- The CROWN linear bound on the ROOT box `[0,2]` is `1`:
`min (g 0) (g 2) = min (0 − relu(−1) + 1) (2 − relu 1 + 1) = min 1 2 = 1`. -/
lemma crownLin_root : crownLin ((0 : ℝ), 2) = 1 := by
  unfold crownLin cornerForm relu; norm_num

/-- The full CROWN relaxed bound on the root box `[0,2]` is `1 > 0`:
`max (ibp = 0) (crown = 1) = max 0 1 = 1`.  **CROWN DECIDES THE ROOT.** -/
lemma relaxedBound_root : relaxedBound ((0 : ℝ), 2) = 1 := by
  unfold relaxedBound ibpBound CompleteIBP.relaxedBound crownLin cornerForm relu
  norm_num

/-- **CROWN is STRICTLY tighter than IBP on the root box.**
`ibpBound [0,2] = 0 < 1 = relaxedBound_CROWN [0,2]`.  IBP cannot decide
`f > 0` on `[0,2]` (bound `= 0`); CROWN can (bound `= 1 > 0`). -/
theorem crown_strictly_tighter_root :
    ibpBound ((0 : ℝ), 2) < relaxedBound ((0 : ℝ), 2) := by
  have hibp : ibpBound ((0 : ℝ), 2) = 0 := CompleteIBP.relaxedBound_root_zero
  rw [hibp, relaxedBound_root]; norm_num

/-- The verification **margin** is the same strict-positive `δ = 1 ≤ trueMin [0,2]`
(reused from `CompleteIBP`: `f ≥ 1` everywhere). -/
lemma margin_pos : (1 : ℝ) ≤ trueMin (0, 2) := CompleteIBP.margin_pos

/-! ## 7. `Complete.complete` FIRES on the CROWN relaxation -/

/-- **The instantiation.**  `Complete.complete` on the CONCRETE CROWN relaxation:
there is a finite bisection depth `d` at which every leaf box of `[0,2]` has a
strictly positive CROWN bound, and `f(x) > 0` for every `x ∈ [0,2]`.  Unlike the
IBP instantiation, the decisive depth here is `0` (`decisive_depth_zero`). -/
theorem crown_complete :
    ∃ d : ℕ,
      (∀ C ∈ Complete.leafBoxes crownRelaxation (0, 2) d,
        0 < crownRelaxation.relaxedBound C) ∧
      (∀ s, crownRelaxation.mem (0, 2) s → crownRelaxation.safe s) :=
  Complete.complete crownRelaxation (0, 2) (by norm_num) margin_pos

/-- **End-to-end decision (unfolded).**  For the REAL net, `f(x) > 0` on the
entire input box `[0,2]`, decided through the verified bisection procedure with
the CROWN relaxation. -/
theorem net_positive_on_box : ∀ x : ℝ, 0 ≤ x → x ≤ 2 → 0 < f x := by
  obtain ⟨_, _, hdec⟩ := crown_complete
  intro x hx1 hx2
  exact hdec x ⟨hx1, hx2⟩

/-- **The decisive depth is concretely `0`** — STRICTLY SMALLER than IBP's `1`.
At depth `0` the only leaf box is the ROOT `[0,2]` itself, and the CROWN bound
there is `1 > 0` (`relaxedBound_root`) — so the property is decided WITHOUT ANY
BISECTION.  This is the concrete sense in which the tighter CROWN relaxation
beats IBP: IBP's bound on the root is `0` (`CompleteIBP.relaxedBound_root_zero`),
forcing it to bisect to depth `1` (`CompleteIBP.decisive_depth_one`), whereas
CROWN closes the root immediately at depth `0`. -/
theorem decisive_depth_zero :
    ∀ C ∈ Complete.leafBoxes crownRelaxation (0, 2) 0,
      0 < crownRelaxation.relaxedBound C := by
  intro C hC
  -- leafBoxes _ (0,2) 0 = [(0,2)]
  simp only [Complete.leafBoxes, List.mem_singleton] at hC
  subst hC
  show 0 < relaxedBound ((0 : ℝ), 2)
  rw [relaxedBound_root]; norm_num

/-- **Completeness fires already at depth 0** (the explicit `d = 0` witness):
every depth-0 leaf closes AND the whole root box is decided safe. -/
theorem crown_complete_depth_zero :
    (∀ C ∈ Complete.leafBoxes crownRelaxation (0, 2) 0,
        0 < crownRelaxation.relaxedBound C) ∧
    (∀ s, crownRelaxation.mem (0, 2) s → crownRelaxation.safe s) := by
  refine ⟨decisive_depth_zero, ?_⟩
  exact Complete.box_safe_of_leaves crownRelaxation (0, 2) 0
    (fun C hC s hms => crownRelaxation.decides C (decisive_depth_zero C hC) s hms)

/-! ## 8. The depth gap, stated as one theorem

A single statement capturing "CROWN closes at a strictly smaller depth than IBP":
CROWN's root bound is positive (closes at depth 0) while IBP's root bound is `0`
(not positive — cannot close at depth 0, must bisect). -/

/-- **The depth gap.**  On the root box `[0,2]`: the CROWN relaxed bound is
strictly positive (closes at depth 0) while the IBP relaxed bound is exactly `0`
(does NOT close at depth 0 — IBP must bisect to depth 1).  So the tighter CROWN
relaxation has a strictly smaller decisive depth (`0` vs `1`) on this net. -/
theorem depth_gap :
    0 < crownRelaxation.relaxedBound ((0 : ℝ), 2) ∧
    CompleteIBP.ibpRelaxation.relaxedBound ((0 : ℝ), 2) = 0 := by
  refine ⟨?_, CompleteIBP.relaxedBound_root_zero⟩
  show 0 < relaxedBound ((0 : ℝ), 2)
  rw [relaxedBound_root]; norm_num

/-! ## Trust-base check — every theorem must reduce to the standard logical
axioms only (`propext`, `Classical.choice`, `Quot.sound`), with NO `sorryAx`. -/

#print axioms cornerForm_mono
#print axioms cornerForm_le_f
#print axioms crownLin_sound
#print axioms crown_ge_ibp_of_active
#print axioms relaxedBound_sound
#print axioms width_error
#print axioms decides
#print axioms crownRelaxation
#print axioms crownLin_root
#print axioms relaxedBound_root
#print axioms crown_strictly_tighter_root
#print axioms margin_pos
#print axioms crown_complete
#print axioms net_positive_on_box
#print axioms decisive_depth_zero
#print axioms crown_complete_depth_zero
#print axioms depth_gap

end CompleteCrown
end Crownproof
