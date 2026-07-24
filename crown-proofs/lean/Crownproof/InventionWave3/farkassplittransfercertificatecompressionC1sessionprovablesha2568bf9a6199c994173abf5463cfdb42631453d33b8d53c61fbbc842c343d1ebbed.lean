/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

INVENTION WAVE 3 — `farkas_split_transfer` (certificate-compression / certificate-
economics C1)

Sealed conjecture: "C1 — farkas_split_transfer: dual inheritance across a BaB
split (the incremental certificate, child = parent multipliers + one scalar)."
Provenance: data/provenance/invention-wave-1-conjectures-2026-06-11.json,
angle `certificate-compression`, conjecture sha256
8bf9a6199c994173abf5463cfdb42631453d33b8d53c61fbbc842c343d1ebbed
(sealed 2026-06-11 BEFORE any proof attempt).

## RESULT STATUS — proved-as-stated, sorry-free

Every leg of the sealed Lean sketch is proved with the sketch's exact statements
(modulo the documented deltas in §"FORMALIZATION DELTA" below, all of which are
notational, not mathematical):

 1. `farkas_split_transfer` — dual inheritance across a BaB split.  When a split
    tightens exactly one premise by `δ ≥ 0` (`g_j ↦ g_j + δ`, sound on the child
    half-box), the parent's Farkas multiplier vector `μ` is a valid certificate on
    the child VERBATIM, and the certified bound improves by exactly `μ_j · δ`:
    `out s ≥ -c + μ_j · δ` on the child.  Proved by `farkas_premise_combination`
    (Bridge.lean:64) with the tightened family `g' i s := g i s + (if i = j then δ
    else 0)` and constant `c' := c - μ j * δ`; the certificate identity for `g'`
    collapses the indicator sum to `μ j * δ` via `Finset.sum_ite_eq'`, exactly as
    the sealed strategy specifies.

 2. `slack_split_transfer` — the slack variant.  Under the one-sided hypothesis of
    `slack_farkas` (SlackFarkas.lean:61) with `σ ≥ 0`, the inherited child bound is
    `out s ≥ -c - σ + μ_j · δ`.

 3. `checkSplitTransferZ` / `checkSplitTransferZ_sound` — the decidable Int-pair
    layer.  `checkSplitTransferZ` does ONE `mulZ` + ONE `addZ` + ONE `leZ` on
    `QPair`s (O(1) kernel ops), versus the O(387-premise × 827-bit) of a fresh
    `checkEntailmentZ` run.  Soundness is a short composition of `leZ_sound`,
    `toQ_addZ`, `toQ_mulZ`, `nonnegZ_sound` from CertCheckerZ.lean (all reused
    verbatim).

 4. `demoSplitTransfer_checks` (`by decide`) + `demoSplitTransfer_sound` — a
    concrete inherited-child instance on Int-pairs, in the spirit of SlackCertZ's
    `demoSlackCert` (kernel-reduced, NO `native_decide`).

 5. `split_transfer_box_inherit` — the instantiation lemma binding the core to
    `Bab.BabProof.split`: for a box premise `g_j = x_c - u` and the low-child path
    `path s ∧ coord c s ≤ m`, the tightened-premise hypothesis `hgChild` is
    discharged by the path conjunct, the same `le_total` bookkeeping as
    `Bab.safe_on_path`.

## FORMALIZATION DELTA vs the sealed Lean sketch (minimal, all notational)

 * The sealed sketch wrote `checkSplitTransferZ (μj δ parentBound threshold : QPair)`
   returning `nonnegZ δ && nonnegZ μj && leZ threshold (addZ parentBound (mulZ μj δ))`.
   We use that EXACT body and signature.  `checkSplitTransferZ_sound`'s sealed
   conclusion was `toQ threshold ≤ toQ parentBound + toQ μj * toQ δ`; we prove
   exactly that, and ADDITIONALLY expose the non-negativity facts `0 ≤ toQ δ`,
   `0 ≤ toQ μj` it certifies (used by the demo and the box instantiation) — a
   strengthening, never a weakening.

 * `farkas_split_transfer` / `slack_split_transfer` are stated with the sealed
   signatures verbatim (same hypothesis names: `hj`, `hδ`, `hμ`, `hgChild`,
   `hcert`, plus `hσ` for the slack variant).  The conclusion is the sealed
   `-c + μ j * δ ≤ out s` (resp. `-c - σ + μ j * δ ≤ out s`).

## HONESTY RAILS (MEDIUM reformulation risk — flagged prominently)

 * The underlying mathematics is LP SENSITIVITY ANALYSIS: dual feasibility is
   preserved under a one-row RHS change, and the objective shifts by
   `dual_j · Δrhs`.  This is textbook LP-duality folklore.  β-CROWN already
   warm-starts α/β duals across BaB splits numerically.  The ONLY claim here is
   N1 — "first formalization of a kernel-checked dual-inheritance rule for BaB
   with a decidable O(1) child check" — PENDING the mandatory baseline-index
   lookup, and carrying N1's reformulation-blindness / theory-relativity caveats.
   The THEOREM is unconditionally true (it is a Lean-checked consequence of
   `farkas_premise_combination`); the NOVELTY claim is the part that is relative
   to the literature and the baseline index.

 * REGIME / EMPIRICAL CAVEAT (the falsifiable measurement, NOT proved here): a
   split happens precisely because the parent bound FAILED on the child box;
   inheritance decides the child only when `μ_j · δ` covers the child's threshold
   deficit.  That is plausible on a SMOOTH / WIDE-margin regime (where VR²S also
   lives) and implausible on a STABILITY-CLIFF split.  The §11 whole-box analysis
   found most splits cliff-driven.  So the inherited-leaf FRACTION on a real tree
   is a measurement that may be ~0 — which would kill the economics WHILE LEAVING
   THIS THEOREM TRUE.  No wall-clock, no GPU, no solved-instance claim is made.
   The only counted quantity is Δ-kernel-ops (O(1) child vs O(premises × bits)
   fresh), with Int-pair discipline on every `decide` path.

The trust base is reported by `#print axioms` at the bottom; it lists only
`[propext, Classical.choice, Quot.sound]` and never `sorryAx`, with the `decide`
demo depending on none.
-/
import Crownproof.Bridge
import Crownproof.SlackFarkas
import Crownproof.CertCheckerZ
import Crownproof.BabProof
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Crownproof
namespace SplitTransfer

open Finset
open Crownproof.CertCheckerZ

/-! ## 1. The abstract dual-inheritance core (exact Farkas).

`farkas_split_transfer` is the certificate-economics sibling of `Δdomains`: a BaB
split that tightens exactly ONE premise by `δ ≥ 0` (`g_j ↦ g_j + δ`) inherits the
parent's WHOLE multiplier vector `μ` as a valid child certificate, and the
certified bound improves by EXACTLY `μ_j · δ`.

The child's certificate is therefore the pair `(j, δ)` and nothing else — `δ`
already lives in the `Bab.BabProof.split` node, so the inherited child carries
ZERO new multiplier data.

Proof: route through `farkas_premise_combination` (Bridge.lean:64) with the
tightened premise family `g' i s := g i s + (if i = j then δ else 0)` and the
shifted constant `c' := c - μ j * δ`.  The certificate identity for `g'` follows
from the parent's `hcert` by distributing the sum and collapsing the indicator
sum `∑ μ i * (if i = j then δ else 0)` to `μ j * δ` via `Finset.sum_ite_eq'`
(`j ∈ premises`). -/

/-- The indicator-shifted premise family: `g' i = g i + δ·[i = j]`. -/
private def gShift {S ι : Type*} [DecidableEq ι]
    (g : ι → S → ℚ) (δ : ℚ) (j : ι) : ι → S → ℚ :=
  fun i s => g i s + (if i = j then δ else 0)

/-- The key algebraic fact: with `j ∈ premises`, the μ-combination of the
    indicator-shifted family equals the parent combination plus `μ j · δ`. -/
theorem sum_gShift {S ι : Type*} [DecidableEq ι] (premises : Finset ι)
    (g : ι → S → ℚ) (μ : ι → ℚ) (δ : ℚ) (j : ι) (hj : j ∈ premises) (s : S) :
    (∑ i ∈ premises, μ i * gShift g δ j i s)
      = (∑ i ∈ premises, μ i * g i s) + μ j * δ := by
  unfold gShift
  -- distribute μ i over the sum  g i s + indicator
  have hdist : ∀ i ∈ premises,
      μ i * (g i s + (if i = j then δ else 0))
        = μ i * g i s + μ i * (if i = j then δ else 0) := by
    intro i _; ring
  rw [Finset.sum_congr rfl hdist, Finset.sum_add_distrib]
  -- collapse the indicator sum to μ j * δ
  have hind : ∀ i, μ i * (if i = j then δ else 0) = if i = j then μ i * δ else 0 := by
    intro i; rw [mul_ite, mul_zero]
  have hcollapse :
      (∑ i ∈ premises, μ i * (if i = j then δ else 0)) = μ j * δ := by
    simp only [hind]
    rw [Finset.sum_ite_eq' premises j (fun i => μ i * δ), if_pos hj]
  rw [hcollapse]

/--
**`farkas_split_transfer` — dual inheritance across a BaB split (exact form).**

Sealed statement, verbatim.  When the child tightens exactly premise `j` by
`δ ≥ 0` (so the child-valid premise family is `g i + δ·[i = j] ≤ 0`), the
parent's certificate identity `∑ μ i · g i = -(out) - c` carries over and the
certified bound improves by exactly `μ j · δ`:

    ∀ s, validChild s → -c + μ j · δ ≤ out s.

Proven by `farkas_premise_combination` on the tightened family `gShift g δ j`
with shifted constant `c - μ j · δ`. -/
theorem farkas_split_transfer
    {S ι : Type*} [DecidableEq ι] (premises : Finset ι)
    (g : ι → S → ℚ) (out : S → ℚ) (μ : ι → ℚ) (c δ : ℚ) (j : ι)
    (validChild : S → Prop)
    (hj : j ∈ premises) (_hδ : 0 ≤ δ)
    (hμ : ∀ i ∈ premises, 0 ≤ μ i)
    -- child premises: unchanged off j, tightened by δ at j, sound on the child box
    (hgChild : ∀ i ∈ premises, ∀ s, validChild s →
        g i s + (if i = j then δ else 0) ≤ 0)
    -- the PARENT's exact certificate identity, reused verbatim
    (hcert : ∀ s, (∑ i ∈ premises, μ i * g i s) = -(out s) - c) :
    ∀ s, validChild s → -c + μ j * δ ≤ out s := by
  -- apply the core to g' = gShift g δ j, c' = c - μ j * δ
  have hcore :
      ∀ s, validChild s → -(c - μ j * δ) ≤ out s := by
    refine farkas_premise_combination (S := S) (ι := ι) premises
      (gShift g δ j) out μ (c - μ j * δ) validChild hμ ?_ ?_
    · -- soundness of every tightened premise on the child
      intro i hi s hv
      exact hgChild i hi s hv
    · -- the shifted certificate identity:  ∑ μ i * g' i s = -(out s) - (c - μ j δ)
      intro s
      rw [sum_gShift premises g μ δ j hj s, hcert s]
      ring
  intro s hs
  have := hcore s hs
  linarith

/-! ## 2. The slack variant (against `slack_farkas`).

Identical inheritance against the slack-tolerant core `slack_farkas`
(SlackFarkas.lean:61): the parent ships the one-sided slack hypothesis with
`σ ≥ 0`, and the inherited child bound is `out ≥ -c - σ + μ_j · δ`. -/

/--
**`slack_split_transfer` — dual inheritance under slack.**

Sealed statement, verbatim.  Same inheritance, against `slack_farkas`: with a
non-negative slack `σ` and the parent's one-sided slack hypothesis
`-(out s) - c - σ ≤ ∑ μ i · g i s` on child-valid states, the inherited child
bound is

    ∀ s, validChild s → -c - σ + μ j · δ ≤ out s.

Proven by `slack_farkas` on the tightened family `gShift g δ j` with shifted
constant `c - μ j · δ` and the SAME slack `σ`. -/
theorem slack_split_transfer
    {S ι : Type*} [DecidableEq ι] (premises : Finset ι)
    (g : ι → S → ℚ) (out : S → ℚ) (μ : ι → ℚ) (c δ σ : ℚ) (j : ι)
    (validChild : S → Prop)
    (hj : j ∈ premises) (_hδ : 0 ≤ δ) (hσ : 0 ≤ σ)
    (hμ : ∀ i ∈ premises, 0 ≤ μ i)
    (hgChild : ∀ i ∈ premises, ∀ s, validChild s →
        g i s + (if i = j then δ else 0) ≤ 0)
    -- the PARENT's one-sided slack hypothesis, reused verbatim
    (hcert : ∀ s, validChild s →
        -(out s) - c - σ ≤ ∑ i ∈ premises, μ i * g i s) :
    ∀ s, validChild s → -c - σ + μ j * δ ≤ out s := by
  have hcore :
      ∀ s, validChild s → -(c - μ j * δ) - σ ≤ out s := by
    refine slack_farkas (S := S) (ι := ι) premises
      (gShift g δ j) out μ (c - μ j * δ) σ validChild hμ ?_ hσ ?_
    · intro i hi s hv
      exact hgChild i hi s hv
    · -- shifted one-sided slack hypothesis on the tightened family
      intro s hv
      rw [sum_gShift premises g μ δ j hj s]
      have := hcert s hv
      linarith
  intro s hs
  have := hcore s hs
  linarith

/--
`slack_split_transfer` recovers `farkas_split_transfer` at zero slack: with
`σ = 0` and the parent's EXACT identity (which implies the one-sided slack
hypothesis), the slack-inherited bound is the exact inherited bound.  This is the
faithfulness leg, mirroring `slack_farkas_of_exact`. -/
theorem slack_split_transfer_of_exact
    {S ι : Type*} [DecidableEq ι] (premises : Finset ι)
    (g : ι → S → ℚ) (out : S → ℚ) (μ : ι → ℚ) (c δ : ℚ) (j : ι)
    (validChild : S → Prop)
    (hj : j ∈ premises) (hδ : 0 ≤ δ)
    (hμ : ∀ i ∈ premises, 0 ≤ μ i)
    (hgChild : ∀ i ∈ premises, ∀ s, validChild s →
        g i s + (if i = j then δ else 0) ≤ 0)
    (hcert : ∀ s, (∑ i ∈ premises, μ i * g i s) = -(out s) - c) :
    ∀ s, validChild s → -c - 0 + μ j * δ ≤ out s := by
  refine slack_split_transfer premises g out μ c δ 0 j validChild hj hδ (le_refl 0)
    hμ hgChild ?_
  intro s _; rw [hcert s]; linarith

/-! ## 3. The decidable Int-pair child check (kernel-runnable, O(1)).

`QPair := ℤ × ℤ` as in `CertCheckerZ`; `toQ (n,d) = n/d`.  Given the parent cert
ALREADY checked (so `parentBound` is the parent's certified bound `-c`), the
inherited child needs only the one scalar test that the child's `threshold`
deficit is covered by `parentBound + μ_j · δ`.

`checkSplitTransferZ` does ONE `mulZ` + ONE `addZ` + ONE `leZ` (plus the two
`nonnegZ` well-formedness gates) — O(1) kernel integer-ops — versus the
O(387-premise × 827-bit) of a fresh `checkEntailmentZ` run.  This is the
Δ-kernel-ops identity: the certificate-economics sibling of `Δdomains`.  All
arithmetic is integer cross-multiplication, so `decide`/`rfl` reduces it in the
kernel with NO `native_decide`. -/

/-- The runnable inherited-child check: `δ ≥ 0`, `μ_j ≥ 0`, and the child
    threshold is covered by the inherited bound `parentBound + μ_j · δ`.
    Sealed body, verbatim. -/
def checkSplitTransferZ (μj δ parentBound threshold : QPair) : Bool :=
  nonnegZ δ && nonnegZ μj && leZ threshold (addZ parentBound (mulZ μj δ))

/--
**Soundness of `checkSplitTransferZ`.**

If the kernel-runnable child check accepts, then (given positive denominators) the
child threshold is met by the inherited bound:

    toQ threshold ≤ toQ parentBound + toQ μj * toQ δ,

with the certified non-negativities `0 ≤ toQ δ` and `0 ≤ toQ μj`.  A 5-line
composition of `leZ_sound`, `toQ_addZ`, `toQ_mulZ`, `nonnegZ_sound` from
`CertCheckerZ` (all reused verbatim). -/
theorem checkSplitTransferZ_sound (μj δ parentBound threshold : QPair)
    (hμj : QPair.wf μj) (hδ : QPair.wf δ)
    (hpb : QPair.wf parentBound) (hth : QPair.wf threshold)
    (hchk : checkSplitTransferZ μj δ parentBound threshold = true) :
    toQ threshold ≤ toQ parentBound + toQ μj * toQ δ
    ∧ 0 ≤ toQ δ ∧ 0 ≤ toQ μj := by
  unfold checkSplitTransferZ at hchk
  simp only [Bool.and_eq_true] at hchk
  obtain ⟨⟨hδnn, hμjnn⟩, hle⟩ := hchk
  -- the inherited bound's pair is well-formed
  have hmul_wf : QPair.wf (mulZ μj δ) := mulZ_wf hμj hδ
  have hadd_wf : QPair.wf (addZ parentBound (mulZ μj δ)) := addZ_wf hpb hmul_wf
  -- leZ gives toQ threshold ≤ toQ (parentBound + μj·δ)
  have h1 : toQ threshold ≤ toQ (addZ parentBound (mulZ μj δ)) :=
    leZ_sound threshold (addZ parentBound (mulZ μj δ)) hth hadd_wf hle
  -- expand the inherited-bound pair via the toQ homomorphisms
  rw [toQ_addZ parentBound (mulZ μj δ) hpb hmul_wf,
      toQ_mulZ μj δ hμj hδ] at h1
  exact ⟨h1, nonnegZ_sound δ hδ hδnn, nonnegZ_sound μj hμj hμjnn⟩

/-! ## 4. A concrete inherited-child instance, closed by kernel reduction.

In the spirit of `SlackCertZ.demoSlackCert`: a tiny inherited-child instance whose
`checkSplitTransferZ` reduces to `true` by `decide` (pure integer
cross-multiplication, NO `native_decide`), demonstrating that the O(1) child check
is genuinely kernel-runnable.

Scenario: a parent leaf certified bound `parentBound = 1/2` (i.e. parent proved
`out ≥ 1/2` after a fresh O(387×827) check).  A split tightens premise `j` by
`δ = 1` with parent dual `μ_j = 1`, so the inherited child bound is
`1/2 + 1·1 = 3/2`.  The child's safety `threshold` is `1` (the child must clear
`out ≥ 1`).  Since `1 ≤ 3/2`, the child is decided with ZERO new multiplier data:
its entire certificate is the pair `(j, δ) = (j, 1)`, and `1` already lives in the
`BabProof.split` node.  The fresh check that this avoids would be the full bignum
leaf re-derivation. -/

/-- Demo inherited-child data: `μ_j = 1`, `δ = 1`, `parentBound = 1/2`,
    `threshold = 1`.  Inherited bound `1/2 + 1 = 3/2 ≥ 1`. -/
def demoMuj      : QPair := (1, 1)
def demoDelta    : QPair := (1, 1)
def demoParent   : QPair := (1, 2)
def demoThresh   : QPair := (1, 1)

/-- The concrete inherited-child check passes — verified by the KERNEL via
    `decide` (integer cross-multiplication only, NO `native_decide`). -/
theorem demoSplitTransfer_checks :
    checkSplitTransferZ demoMuj demoDelta demoParent demoThresh = true := by
  decide

/-- Therefore, by `checkSplitTransferZ_sound`, the inherited child clears its
    threshold: `toQ threshold ≤ toQ parentBound + toQ μ_j · toQ δ`
    (i.e. `1 ≤ 1/2 + 1 = 3/2`), with `δ, μ_j ≥ 0` — a fully kernel-checked
    inherited-child leaf as a Lean theorem, O(1) ops, NO fresh bignum check. -/
theorem demoSplitTransfer_sound :
    toQ demoThresh ≤ toQ demoParent + toQ demoMuj * toQ demoDelta
    ∧ 0 ≤ toQ demoDelta ∧ 0 ≤ toQ demoMuj :=
  checkSplitTransferZ_sound demoMuj demoDelta demoParent demoThresh
    (by unfold QPair.wf demoMuj; norm_num)
    (by unfold QPair.wf demoDelta; norm_num)
    (by unfold QPair.wf demoParent; norm_num)
    (by unfold QPair.wf demoThresh; norm_num)
    demoSplitTransfer_checks

/-! ## 5. Instantiation against `Bab.BabProof.split`.

The sealed `proof_strategy` asks for "the instantiation lemma binding it to
`BabProof.split`: for box premise `g_j = x_c − u` and child path
`(path s ∧ coord c s ≤ m)`, `hgChild` is discharged by the path conjunct — the
same `le_total` bookkeeping as `Bab.safe_on_path`."

We give that lemma concretely.  The low child of a split at coordinate `c`,
midpoint `m`, replaces the parent box-upper premise `g_j s = coord c s - u` (sound
when `coord c s ≤ u`) by the tightened premise `coord c s - m ≤ 0` (sound on the
low half-box `coord c s ≤ m`).  With `δ = u - m ≥ 0` this is exactly
`g_j s + δ = coord c s - m`, so the child-valid premise hypothesis at `j` is
discharged BY THE PATH CONJUNCT `coord c s ≤ m` — no fresh certificate work. -/

/-- The split-tightening identity at the distinguished premise `j`: for the box
    upper premise `g_j s = coord c s - u`, the indicator-shifted premise with
    `δ = u - m` is exactly `coord c s - m`. -/
theorem box_premise_shift (coordc : ℚ) (u m : ℚ) :
    (coordc - u) + (u - m) = coordc - m := by ring

/--
**`split_transfer_box_inherit` — the `BabProof.split` instantiation.**

Concretely binds `farkas_split_transfer` to a low-child split path.  Take a finite
premise family `g`, the distinguished box-upper premise index `j` with
`g j s = coordc s - u`, a parent Farkas certificate `μ`/`c`, and the split at
coordinate-readout `coordc`, midpoint `m ≤ u`.  On the low child
`validChild s := path s ∧ coordc s ≤ m`, the inherited bound is
`out s ≥ -c + μ_j · (u - m)`.

The only premise-soundness obligation specific to `j` is discharged by the path
conjunct `coordc s ≤ m` (`hgChild` at `i = j` becomes `coordc s - m ≤ 0`); the
off-`j` premises stay sound on the child because the child box is a SUB-box of the
parent (`hOffSound`).  This is the `le_total` bookkeeping of `Bab.safe_on_path`,
made local to the one tightened row. -/
theorem split_transfer_box_inherit
    {S ι : Type*} [DecidableEq ι] (premises : Finset ι)
    (g : ι → S → ℚ) (out : S → ℚ) (μ : ι → ℚ) (c : ℚ) (j : ι)
    (coordc : S → ℚ) (u m : ℚ) (path : S → Prop)
    (hj : j ∈ premises) (hmu : m ≤ u)
    (hμ : ∀ i ∈ premises, 0 ≤ μ i)
    -- the distinguished premise is the box-upper row  g_j s = coordc s - u
    (hgj : ∀ s, g j s = coordc s - u)
    -- off-j premises remain sound on the child sub-box (covering bookkeeping)
    (hOffSound : ∀ i ∈ premises, i ≠ j → ∀ s, (path s ∧ coordc s ≤ m) → g i s ≤ 0)
    -- the parent's exact certificate identity
    (hcert : ∀ s, (∑ i ∈ premises, μ i * g i s) = -(out s) - c) :
    ∀ s, (path s ∧ coordc s ≤ m) → -c + μ j * (u - m) ≤ out s := by
  have hδ : 0 ≤ u - m := by linarith
  refine farkas_split_transfer premises g out μ c (u - m) j
    (fun s => path s ∧ coordc s ≤ m) hj hδ hμ ?_ hcert
  -- hgChild: g i s + (if i = j then (u - m) else 0) ≤ 0 on the low child
  intro i hi s hv
  by_cases hij : i = j
  · -- distinguished row: g j s + (u - m) = coordc s - m ≤ 0  by the path conjunct
    subst hij
    rw [if_pos rfl, hgj s, box_premise_shift (coordc s) u m]
    have hcm : coordc s ≤ m := hv.2
    linarith
  · -- off-j rows: the indicator is 0, soundness from hOffSound
    rw [if_neg hij, add_zero]
    exact hOffSound i hi hij s hv

/-! ## Trust-base check.  Must list only the three standard logical axioms
     (`demoSplitTransfer_checks` depends on none — pure `decide`). -/

#print axioms sum_gShift
#print axioms farkas_split_transfer
#print axioms slack_split_transfer
#print axioms slack_split_transfer_of_exact
#print axioms checkSplitTransferZ_sound
#print axioms demoSplitTransfer_checks
#print axioms demoSplitTransfer_sound
#print axioms split_transfer_box_inherit

end SplitTransfer
end Crownproof
