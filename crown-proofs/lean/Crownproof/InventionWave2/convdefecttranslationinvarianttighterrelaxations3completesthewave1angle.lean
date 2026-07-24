/-
  INVENTION WAVE 2 — `conv_defect_translation_invariant`
  (tighter-relaxations #3 — completes the wave-1 angle).

  Sealed conjecture record: `data/provenance/invention-wave-1-conjectures-2026-06-11.json`
  (set sha256 00b2f585d355e1b4abc2eb2ab6722dd1375ff65619a905d722da5c7cd4b6e8b4),
  angle tighter-relaxations, conjecture "conv_defect_translation_invariant —
  conv weight sharing makes the coupling gap position-invariant: one verified
  defect computation certifies O(H·W) cut sites", per-conjecture sha256
  ee9d0d1b8210e9a08f8a9976f845bc9babcdbc124db2a5bab82d07a8fd99db67.
  Its sealed prerequisite ("depends on Conjecture 2 landing first") is
  satisfied: `coordDefect` / `uzExact` / `gap_closed_form` landed in wave 1
  (`Crownproof/InventionWave1/gapclosedformgapposiffsigndisagree.lean`).

  ## What this file proves, sorry-free

  1. `coordDefect_perm_invariant` — THE ENGINE, verbatim from the sealed
     sketch: the wave-1 coupling defect `coordDefect` is invariant under
     precomposition of all rows with any radius-preserving permutation of the
     input coordinates.  Pure `Fintype.sum_equiv` reindexing: the inner
     `∑ i ∈ S` commutes pointwise with the reindexing, and the box centers
     never enter `coordDefect` at all.

  2. The conv instance.  `tapsAt` places a kernel's taps at shifted indices
     (zero elsewhere); `convRows w w2 δ t` is the channel pair (taps of `w`
     at position `t`, taps of `w2` at position `t + δ`) — the §9.1
     conv-as-sparse-affine / im2col row semantics.  `convShift n t t'`
     exhibits the translation `t' → t` as an explicit permutation of `Fin n`
     (the cyclic shift `Equiv.addLeft ((t : Fin n) - (t' : Fin n))`), and
     `convRows_convShift` proves the translated rows are exactly the
     original rows precomposed with it (`hfit` keeps both placements in
     range).  Main theorem `conv_defect_translation_invariant`: for any box
     whose per-coordinate WIDTH is invariant under the shift (`hwidth`), the
     defect of the pair at position `t'` equals the defect at position `t`,
     on every pattern `S`.  Corollaries: `conv_pair_defect_center_free`
     (uniform radius `ε`, ARBITRARY box centers — formalizing "the box
     centers never enter the defect") and `conv_pair_gap_position_invariant`
     (the sealed sketch's literal shape, `[-ε, ε]^n` box).

  3. The conditional GAP corollary (the sealed informal statement's second
     half): `conv_pair_gap_translation_invariant` — in the regime where
     `gap_closed_form`'s min is attained at `defect_univ` (hypotheses
     `hregime`/`hregime'`, exactly the sealed risk-note's
     "defect_univ ≤ min over S of off-pattern mass + defect_S" on both
     sides), the EXACT wave-1 gap itself is translation-invariant.
     `conv_pair_gap_translation_invariant_exact` re-exports it through
     wave-2 target #5's carrier reconciliation
     (`gapModule_patternSup_exact`): the bound the invariant gap is measured
     against is the EXACT joint-cut supremum (`IsGreatest`), so the result
     formally reads "the gap to the exact bound is position-invariant".

  4. Demo on REAL constants: the metaroom-4cnn conv2 channel pair
     (43310, 48685) of `MetaroomConvPair.lean` (15-dim receptive field,
     exact-rational CROWN upper-bound rows, spec_idx_2 box).  The pair's real
     per-coordinate box bounds are themselves spatially periodic with period
     5 (the stride pattern of the receptive field) — verifiable from the
     transcribed rationals.  We place the 15-tap rows at flat positions 0
     and 5 of a 20-dim ambient whose box extends that real period-5 pattern,
     discharge the radius-preservation hypothesis by `norm_num` on the exact
     rationals, and conclude the two positions share their defect on every
     pattern (`metaroom_conv2_defect_translation_invariant`).  Bonus:
     `metaroom_conv2_defect_pos` proves the shared defect is strictly
     positive at position 0 (sign-disagreement at coordinate 0:
     `(5004725/16777216) · (-683851/4194304) < 0` — wave-1's syntactic
     criterion), and `metaroom_conv2_defect_pos_shifted` transfers it to
     position 5 through the invariance theorem: ONE verified defect
     computation certifies both sites of the family.

  ## Counted-work reading (prose only — nothing here is a runtime claim)

  Translation invariance means every (channel-pair, offset) family shares
  one defect value across its O(H·W) spatial sites, so the cut-candidate
  scan collapses from O((H·W·C)²) per-pair probes to O(C²·K²) kernel-overlap
  defect evaluations per layer.  That is a counted-work statement in the
  docs' Δdomains sense; actual Δdomains and all wall-clock/GPU/VNN-COMP
  quantities remain measured-only and are NOT claimed here.

  ## Faithfulness delta vs the sealed lean_statement_sketch

  * `coordDefect_perm_invariant`: as sketched (namespace
    `Crownproof.InventionWave2`, wave-1 carriers referenced by their
    landed qualified names `InventionWave1.coordDefect` etc.).
  * `convRows`: the sketch left the tap-placement carrier unspecified
    ("taps-at-shifted-indices (zero elsewhere)"); defined here as
    `tapsAt` via an indicator sum, with the placement-fit hypothesis made
    explicit (`hfit : t + δ + K ≤ n`, `hfit' : t' + δ + K ≤ n` — the
    sketch's elided `hfit : …`).
  * `conv_pair_gap_position_invariant`: the sketch's undefined `convCC` is
    pinned to the canonical unit weights `![1, 1]` (matching the real
    MetaroomConvPair usage); the general-`cc` statement is
    `conv_defect_translation_invariant`.  The sketch's `uXl ε`/`uXu ε` are
    defined here as the `[-ε, ε]^n` box; `hε : 0 < ε` is carried verbatim
    from the sketch although the equality does not need it (same protocol
    as wave-1's carried `hcc`).  The sketch names this theorem "gap" while
    stating the DEFECT equality; both are provided — the defect form under
    the sketch's name and shape, the genuine gap form as
    `conv_pair_gap_translation_invariant` under the sealed regime
    hypothesis.
  * The intercepts `r` are position-independent in the gap corollary —
    faithful to conv semantics (biases are per-channel, shared across
    spatial sites).
  * The sealed informal statement's intermediate "gap lower bound
    min(defect_univ, cc_i·uz_i)" is subsumed by wave-1's finer `inf'`
    closed form and is not separately restated.

  ## Honesty (novelty-tier standard, all three sealed risk rails carried)

  * (a) NOT a standalone "equivariance by reindexing" result: the gap-level
    theorems are stated as load-bearing corollaries of the VERIFIED wave-1
    `gap_closed_form`, re-grounded against the EXACT bound through wave-2
    target #5's reconciliation.  The bookkeeping lemma is the engine, not
    the claim.
  * (b) Exact invariance holds only for position pairs whose receptive
    fields see equal radii — stated as the `hwidth` hypothesis.  Full-image
    eps-balls satisfy it everywhere (`conv_pair_defect_center_free`,
    `conv_pair_gap_position_invariant`); metaroom-style specs satisfy it
    only on the perturbed support (the demo's period-5 box is the periodic
    extension of the REAL receptive-field bounds, and the demo's two
    placements both lie inside it).
  * (c) This proves position-invariance at a LAYER.  It does NOT prove the
    unreproduced §9 probe claim of no decay across conv DEPTH — depth
    enters through the zU rows and stays measured-only.
  * N1 at most — FIRST FORMALIZATION claim only, pending the literature
    index check.  Conv weight-sharing equivariance is classical; the value
    claimed is the machine-checked transport of the wave-1 closed-form gap
    along it.  Zero VNN-COMP scored points; theory contribution only.

  All `#print axioms` below must report exactly
  `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no extras,
  no `native_decide` anywhere.
-/

import Crownproof.InventionWave1.gapclosedformgapposiffsigndisagree
import Crownproof.InventionWave2.Gapmodulecarrierreconciliationowedwave1followuptarget5
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs

namespace Crownproof
namespace InventionWave2

open Finset

/- The `ℕ → Fin n` cast and the `Fin n` ring structure are scoped instances
in Mathlib (`Fin.CommRing`); we open them for the cyclic-shift arithmetic,
following Mathlib's own usage pattern for such lemmas. -/
open scoped Fin.CommRing

/-! ## 1.  The engine: `coordDefect` is invariant under radius-preserving
coordinate permutations (verbatim the sealed sketch).  The box CENTERS never
enter: only widths are constrained, and only up to the permutation. -/

/-- **`coordDefect_perm_invariant` (sealed sketch, verbatim).**  Precomposing
all rows with a permutation `σ` of the input coordinates and matching the
per-coordinate box widths along `σ` leaves the wave-1 coupling defect
unchanged, on every pattern `S`.  Pure `Fintype.sum_equiv` reindexing — the
inner `∑ i ∈ S` commutes pointwise with the reindexing. -/
theorem coordDefect_perm_invariant {n k : ℕ}
    (cc : Fin k → ℚ) (p p' : Fin k → Fin n → ℚ)
    (xl xu xl' xu' : Fin n → ℚ) (σ : Equiv.Perm (Fin n))
    (hshift : ∀ i j, p' i j = p i (σ j))
    (hrad : ∀ j, xu' j - xl' j = xu (σ j) - xl (σ j))
    (S : Finset (Fin k)) :
    InventionWave1.coordDefect cc p' xl' xu' S
      = InventionWave1.coordDefect cc p xl xu S := by
  unfold InventionWave1.coordDefect
  refine Fintype.sum_equiv σ _ _ fun j => ?_
  simp only [hshift, hrad]

/-! ## 2.  The conv instance: kernel taps at shifted indices, translation as
an explicit permutation. -/

/-- Kernel taps placed at shifted indices, zero elsewhere: coordinate
`t + a` carries tap `w a`; coordinates outside the window `[t, t + K)`
carry `0`.  (The §9.1 im2col row of a 1-D conv at position `t`.) -/
def tapsAt (n : ℕ) {K : ℕ} (w : Fin K → ℚ) (t : ℕ) : Fin n → ℚ :=
  fun j => ∑ a : Fin K, if (j : ℕ) = t + (a : ℕ) then w a else 0

/-- The conv channel pair at spatial offset `δ` and position `t`: row 0 is
kernel `w` at `t`, row 1 is kernel `w2` at `t + δ`. -/
def convRows (n : ℕ) {K : ℕ} (w w2 : Fin K → ℚ) (δ t : ℕ) : Fin 2 → Fin n → ℚ :=
  ![tapsAt n w t, tapsAt n w2 (t + δ)]

/-- Spatial translation `t' → t` as an explicit permutation of the input
coordinates: the cyclic shift by `(t : Fin n) - (t' : Fin n)`. -/
def convShift (n : ℕ) [NeZero n] (t t' : ℕ) : Equiv.Perm (Fin n) :=
  Equiv.addLeft ((t : Fin n) - (t' : Fin n))

theorem convShift_apply {n : ℕ} [NeZero n] (t t' : ℕ) (j : Fin n) :
    convShift n t t' j = ((t : Fin n) - (t' : Fin n)) + j := rfl

/-- The shift depends only on the translation, not the absolute positions:
shifting both windows by a common offset `δ` gives the same permutation. -/
theorem convShift_offset {n : ℕ} [NeZero n] (t t' δ : ℕ) :
    convShift n (t + δ) (t' + δ) = convShift n t t' := by
  unfold convShift
  congr 1
  push_cast
  ring

/-- **Window mapping.**  As long as both windows fit (`t + c < n`,
`t' + c < n`), the shift maps the `t'`-window pointwise onto the
`t`-window: `(convShift n t t' j : ℕ) = t + c ↔ (j : ℕ) = t' + c`.
In particular coordinates OUTSIDE the `t'`-window land outside the
`t`-window — no tap is gained or lost to wraparound. -/
theorem convShift_window_val {n : ℕ} [NeZero n] {t t' c : ℕ}
    (hc : t + c < n) (hc' : t' + c < n) (j : Fin n) :
    ((convShift n t t' j : Fin n) : ℕ) = t + c ↔ (j : ℕ) = t' + c := by
  constructor
  · intro h
    have h1 : ((t : Fin n) - (t' : Fin n)) + j = ((t + c : ℕ) : Fin n) := by
      rw [← convShift_apply]
      exact Fin.ext (h.trans (Fin.val_cast_of_lt hc).symm)
    have h2 : j = ((t + c : ℕ) : Fin n) - ((t : Fin n) - (t' : Fin n)) :=
      eq_sub_of_add_eq' h1
    have hj : j = ((t' + c : ℕ) : Fin n) := by
      rw [h2]
      push_cast
      ring
    rw [hj, Fin.val_cast_of_lt hc']
  · intro h
    have hj : j = ((t' + c : ℕ) : Fin n) :=
      Fin.ext (h.trans (Fin.val_cast_of_lt hc').symm)
    have hF : convShift n t t' j = ((t + c : ℕ) : Fin n) := by
      rw [convShift_apply, hj]
      push_cast
      ring
    rw [hF, Fin.val_cast_of_lt hc]

/-- A translated tap row is the original tap row precomposed with the
shift: `tapsAt w t' = (tapsAt w t) ∘ (convShift n t t')`, termwise via the
window-mapping iff. -/
theorem tapsAt_convShift {n K : ℕ} [NeZero n] (w : Fin K → ℚ) (t t' : ℕ)
    (hfit : t + K ≤ n) (hfit' : t' + K ≤ n) (j : Fin n) :
    tapsAt n w t' j = tapsAt n w t (convShift n t t' j) := by
  unfold tapsAt
  refine Finset.sum_congr rfl fun a _ => ?_
  have ha : (a : ℕ) < K := a.isLt
  exact if_congr
    (convShift_window_val (by omega) (by omega) j).symm rfl rfl

/-- The translated conv PAIR is the original pair precomposed with the
shift (row 1's offset window rides along: `convShift` is offset-invariant). -/
theorem convRows_convShift {n K : ℕ} [NeZero n] (w w2 : Fin K → ℚ)
    (δ t t' : ℕ) (hfit : t + δ + K ≤ n) (hfit' : t' + δ + K ≤ n)
    (i : Fin 2) (j : Fin n) :
    convRows n w w2 δ t' i j = convRows n w w2 δ t i (convShift n t t' j) := by
  fin_cases i
  · show tapsAt n w t' j = tapsAt n w t (convShift n t t' j)
    exact tapsAt_convShift w t t' (by omega) (by omega) j
  · show tapsAt n w2 (t' + δ) j = tapsAt n w2 (t + δ) (convShift n t t' j)
    rw [← convShift_offset t t' δ]
    exact tapsAt_convShift w2 (t + δ) (t' + δ) (by omega) (by omega) j

/-! ## 3.  Main theorem and box-shape corollaries. -/

/-- **`conv_defect_translation_invariant` (main theorem).**  For a conv
channel pair over any box whose per-coordinate width is invariant under the
translation shift (`hwidth` — the sealed risk-note's equal-radii condition,
honesty rail (b)), the wave-1 coupling defect at position `t'` equals the
defect at position `t`, on EVERY pattern `S`.  One verified defect
computation therefore certifies every spatial site of the
(channel-pair, offset) family whose receptive fields see equal radii. -/
theorem conv_defect_translation_invariant {n K : ℕ} [NeZero n]
    (cc : Fin 2 → ℚ) (w w2 : Fin K → ℚ) (δ t t' : ℕ) (xl xu : Fin n → ℚ)
    (hfit : t + δ + K ≤ n) (hfit' : t' + δ + K ≤ n)
    (hwidth : ∀ j, xu j - xl j
      = xu (convShift n t t' j) - xl (convShift n t t' j))
    (S : Finset (Fin 2)) :
    InventionWave1.coordDefect cc (convRows n w w2 δ t') xl xu S
      = InventionWave1.coordDefect cc (convRows n w w2 δ t) xl xu S :=
  coordDefect_perm_invariant cc (convRows n w w2 δ t) (convRows n w w2 δ t')
    xl xu xl xu (convShift n t t')
    (convRows_convShift w w2 δ t t' hfit hfit') hwidth S

/-- Uniform radius, ARBITRARY centers: on any box `[c - ε, c + ε]`
(coordinate-wise, any center function `c`), the defect is position-invariant
— formalizing the sealed statement's "not the image content (the box centers
never enter defect)".  Full-image eps-ball specs satisfy this everywhere. -/
theorem conv_pair_defect_center_free {n K : ℕ} [NeZero n]
    (cc : Fin 2 → ℚ) (w w2 : Fin K → ℚ) (δ t t' : ℕ)
    (c : Fin n → ℚ) (ε : ℚ)
    (hfit : t + δ + K ≤ n) (hfit' : t' + δ + K ≤ n) (S : Finset (Fin 2)) :
    InventionWave1.coordDefect cc (convRows n w w2 δ t')
        (fun j => c j - ε) (fun j => c j + ε) S
      = InventionWave1.coordDefect cc (convRows n w w2 δ t)
        (fun j => c j - ε) (fun j => c j + ε) S :=
  conv_defect_translation_invariant cc w w2 δ t t' _ _ hfit hfit'
    (fun j => by ring) S

/-- The sealed sketch's `uXl ε`: the `[-ε, ε]^n` box, lower bounds. -/
def uXl (n : ℕ) (ε : ℚ) : Fin n → ℚ := fun _ => -ε

/-- The sealed sketch's `uXu ε`: the `[-ε, ε]^n` box, upper bounds. -/
def uXu (n : ℕ) (ε : ℚ) : Fin n → ℚ := fun _ => ε

/-- The sealed sketch's `convCC`, pinned to the canonical unit cut weights
(the real MetaroomConvPair usage `cc1 = cc2 = 1`). -/
def convCC : Fin 2 → ℚ := ![1, 1]

/-- **Sealed-sketch shape, verbatim carriers.**  On the uniform eps-ball
`[-ε, ε]^n`, the defect of the conv pair on the full pattern is invariant
under spatial translation.  (`hε` is carried from the sealed sketch; the
equality itself does not need it — wave-1's carried-`hcc` protocol.) -/
theorem conv_pair_gap_position_invariant {n K : ℕ} [NeZero n]
    (w w2 : Fin K → ℚ) (δ t t' : ℕ) (ε : ℚ) (hε : 0 < ε)
    (hfit : t + δ + K ≤ n) (hfit' : t' + δ + K ≤ n) :
    InventionWave1.coordDefect convCC (convRows n w w2 δ t)
        (uXl n ε) (uXu n ε) Finset.univ
      = InventionWave1.coordDefect convCC (convRows n w w2 δ t')
        (uXl n ε) (uXu n ε) Finset.univ :=
  (conv_defect_translation_invariant convCC w w2 δ t t' (uXl n ε) (uXu n ε)
    hfit hfit' (fun _ => rfl) Finset.univ).symm

/-! ## 4.  The conditional gap corollary: in the regime where the closed-form
min is attained at `defect_univ`, the EXACT gap itself is
translation-invariant — built directly on the verified wave-1
`gap_closed_form` (honesty rail (a): a load-bearing corollary, not a
standalone reindexing result). -/

/-- If the closed-form min is attained at the full pattern (`hreg` — the
sealed regime hypothesis), the wave-1 `inf'` collapses to `defect_univ`. -/
theorem gap_inf'_eq_defect_univ {n k : ℕ} (cc : Fin k → ℚ)
    (p : Fin k → Fin n → ℚ) (r : Fin k → ℚ) (xl xu : Fin n → ℚ)
    (hreg : ∀ S ∈ (Finset.univ : Finset (Fin k)).powerset,
      InventionWave1.coordDefect cc p xl xu Finset.univ
        ≤ (∑ i ∈ Sᶜ, cc i * InventionWave1.uzExact p r xl xu i)
          + InventionWave1.coordDefect cc p xl xu S) :
    Finset.univ.powerset.inf' ⟨∅, Finset.empty_mem_powerset _⟩
        (fun S => (∑ i ∈ Sᶜ, cc i * InventionWave1.uzExact p r xl xu i)
                  + InventionWave1.coordDefect cc p xl xu S)
      = InventionWave1.coordDefect cc p xl xu Finset.univ := by
  apply le_antisymm
  · refine le_trans
      (Finset.inf'_le _ (Finset.mem_powerset_self _)) (le_of_eq ?_)
    rw [Finset.compl_univ, Finset.sum_empty, zero_add]
  · exact Finset.le_inf' _ _ hreg

/-- **Conditional gap invariance (the sealed statement's second half).**
In the comfortably-unstable regime where `gap_closed_form`'s min is attained
at `defect_univ` at BOTH positions (`hregime`, `hregime'` — the sealed
risk-note's explicit regime hypothesis), the exact gap between the decoupled
bound and the joint-cut pattern-sup is invariant under spatial translation
of the conv pair.  The intercepts `r` are shared across positions (conv
biases are per-channel). -/
theorem conv_pair_gap_translation_invariant {n K : ℕ} [NeZero n]
    (cc : Fin 2 → ℚ) (w w2 : Fin K → ℚ) (r : Fin 2 → ℚ) (δ t t' : ℕ)
    (xl xu : Fin n → ℚ)
    (hfit : t + δ + K ≤ n) (hfit' : t' + δ + K ≤ n)
    (hwidth : ∀ j, xu j - xl j
      = xu (convShift n t t' j) - xl (convShift n t t' j))
    (hcc : ∀ i, 0 < cc i) (hbox : ∀ j, xl j ≤ xu j)
    (hunst : ∀ i, 0 < InventionWave1.uzExact (convRows n w w2 δ t) r xl xu i)
    (hunst' : ∀ i, 0 < InventionWave1.uzExact (convRows n w w2 δ t') r xl xu i)
    (hregime : ∀ S ∈ (Finset.univ : Finset (Fin 2)).powerset,
      InventionWave1.coordDefect cc (convRows n w w2 δ t) xl xu Finset.univ
        ≤ (∑ i ∈ Sᶜ, cc i
              * InventionWave1.uzExact (convRows n w w2 δ t) r xl xu i)
          + InventionWave1.coordDefect cc (convRows n w w2 δ t) xl xu S)
    (hregime' : ∀ S ∈ (Finset.univ : Finset (Fin 2)).powerset,
      InventionWave1.coordDefect cc (convRows n w w2 δ t') xl xu Finset.univ
        ≤ (∑ i ∈ Sᶜ, cc i
              * InventionWave1.uzExact (convRows n w w2 δ t') r xl xu i)
          + InventionWave1.coordDefect cc (convRows n w w2 δ t') xl xu S) :
    (∑ i, cc i * relu (InventionWave1.uzExact (convRows n w w2 δ t') r xl xu i))
        - Finset.univ.powerset.sup' ⟨∅, Finset.empty_mem_powerset _⟩
            (InventionWave1.patternBound cc (convRows n w w2 δ t') r xl xu)
      = (∑ i, cc i * relu (InventionWave1.uzExact (convRows n w w2 δ t) r xl xu i))
        - Finset.univ.powerset.sup' ⟨∅, Finset.empty_mem_powerset _⟩
            (InventionWave1.patternBound cc (convRows n w w2 δ t) r xl xu) := by
  rw [InventionWave1.gap_closed_form cc (convRows n w w2 δ t') r xl xu
        hcc hbox hunst',
      InventionWave1.gap_closed_form cc (convRows n w w2 δ t) r xl xu
        hcc hbox hunst,
      gap_inf'_eq_defect_univ cc (convRows n w w2 δ t') r xl xu hregime',
      gap_inf'_eq_defect_univ cc (convRows n w w2 δ t) r xl xu hregime]
  exact conv_defect_translation_invariant cc w w2 δ t t' xl xu
    hfit hfit' hwidth Finset.univ

/-- **The exactness re-export (through wave-2 target #5's reconciliation).**
Under the same hypotheses, BOTH pattern-sups the invariant gap is measured
against are the EXACT joint-cut suprema over the box (`IsGreatest` — the
target-#5 transport of `multiReluCut_box_exact`), AND the gap is
translation-invariant.  This is the formal "the gap to the EXACT bound is
position-invariant" reading of the sealed conjecture. -/
theorem conv_pair_gap_translation_invariant_exact {n K : ℕ} [NeZero n]
    (cc : Fin 2 → ℚ) (w w2 : Fin K → ℚ) (r : Fin 2 → ℚ) (δ t t' : ℕ)
    (xl xu : Fin n → ℚ)
    (hfit : t + δ + K ≤ n) (hfit' : t' + δ + K ≤ n)
    (hwidth : ∀ j, xu j - xl j
      = xu (convShift n t t' j) - xl (convShift n t t' j))
    (hcc : ∀ i, 0 < cc i) (hbox : ∀ j, xl j ≤ xu j)
    (hunst : ∀ i, 0 < InventionWave1.uzExact (convRows n w w2 δ t) r xl xu i)
    (hunst' : ∀ i, 0 < InventionWave1.uzExact (convRows n w w2 δ t') r xl xu i)
    (hregime : ∀ S ∈ (Finset.univ : Finset (Fin 2)).powerset,
      InventionWave1.coordDefect cc (convRows n w w2 δ t) xl xu Finset.univ
        ≤ (∑ i ∈ Sᶜ, cc i
              * InventionWave1.uzExact (convRows n w w2 δ t) r xl xu i)
          + InventionWave1.coordDefect cc (convRows n w w2 δ t) xl xu S)
    (hregime' : ∀ S ∈ (Finset.univ : Finset (Fin 2)).powerset,
      InventionWave1.coordDefect cc (convRows n w w2 δ t') xl xu Finset.univ
        ≤ (∑ i ∈ Sᶜ, cc i
              * InventionWave1.uzExact (convRows n w w2 δ t') r xl xu i)
          + InventionWave1.coordDefect cc (convRows n w w2 δ t') xl xu S) :
    IsGreatest
      {v : ℚ | ∃ x, (∀ j, xl j ≤ x j ∧ x j ≤ xu j) ∧
        v = ∑ i, cc i * relu (linVal (convRows n w w2 δ t i) x (r i))}
      (Finset.univ.powerset.sup' ⟨∅, Finset.empty_mem_powerset _⟩
        (InventionWave1.patternBound cc (convRows n w w2 δ t) r xl xu))
    ∧ IsGreatest
      {v : ℚ | ∃ x, (∀ j, xl j ≤ x j ∧ x j ≤ xu j) ∧
        v = ∑ i, cc i * relu (linVal (convRows n w w2 δ t' i) x (r i))}
      (Finset.univ.powerset.sup' ⟨∅, Finset.empty_mem_powerset _⟩
        (InventionWave1.patternBound cc (convRows n w w2 δ t') r xl xu))
    ∧ (∑ i, cc i * relu (InventionWave1.uzExact (convRows n w w2 δ t') r xl xu i))
        - Finset.univ.powerset.sup' ⟨∅, Finset.empty_mem_powerset _⟩
            (InventionWave1.patternBound cc (convRows n w w2 δ t') r xl xu)
      = (∑ i, cc i * relu (InventionWave1.uzExact (convRows n w w2 δ t) r xl xu i))
        - Finset.univ.powerset.sup' ⟨∅, Finset.empty_mem_powerset _⟩
            (InventionWave1.patternBound cc (convRows n w w2 δ t) r xl xu) :=
  ⟨gapModule_patternSup_exact cc (convRows n w w2 δ t) r xl xu
      (fun i => le_of_lt (hcc i)) hbox,
   gapModule_patternSup_exact cc (convRows n w w2 δ t') r xl xu
      (fun i => le_of_lt (hcc i)) hbox,
   conv_pair_gap_translation_invariant cc w w2 r δ t t' xl xu hfit hfit'
      hwidth hcc hbox hunst hunst' hregime hregime'⟩

/-! ## 5.  Demo on REAL constants: the metaroom-4cnn conv2 pair
(43310, 48685) of `MetaroomConvPair.lean` — 15-dim receptive field,
exact-rational CROWN rows (transcribed verbatim from the verified
`metaroom_conv2_43310_48685_cut`, lines 44–60), spec_idx_2 box.

The pair's REAL per-coordinate bounds are spatially periodic with period 5:
coordinates {0,5,10}, {1,6,11}, {2,7,12}, {3,8,13}, {4,9,14} share their
bounds — the stride pattern of the receptive field.  The demo ambient is a
20-dim periodic extension of those real bounds; the 15-tap rows are placed
at flat positions 0 and 5, both inside range (honesty rail (b): equal radii
on both receptive fields, here discharged by `norm_num` on the exact
rationals via the period-5 structure). -/

/-- zU row of neuron 43310 (channel A), exact rationals from
`MetaroomConvPair.lean`. -/
def mW1 : Fin 15 → ℚ :=
  ![5004725/16777216, 779161/4194304, 0, 6924405/16777216, 956603/16777216,
    -5376091/4194304, -14389793/8388608, 0, -1750627/4194304, -697623/1048576,
    2075419/4194304, 6478939/16777216, 0, 1380187/4194304, 2282459/8388608]

/-- zU row of neuron 48685 (channel B), exact rationals from
`MetaroomConvPair.lean`. -/
def mW2 : Fin 15 → ℚ :=
  ![-683851/4194304, -5398547/16777216, -125157/4194304, -1803669/16777216,
    -1763459/16777216, 20339129/16777216, 13827839/16777216, 1816101/8388608,
    529233/2097152, 1953279/8388608, -20690509/16777216, -10672815/16777216,
    182601/16777216, -1349535/16777216, 861829/16777216]

/-- Unit cut weights (`cc1 = cc2 = 1`, the real MetaroomConvPair usage). -/
def mCC : Fin 2 → ℚ := ![1, 1]

/-- Lower bounds: the REAL period-5 bound pattern of the metaroom
receptive-field box (`MetaroomConvPair.lean` lines 44–58), keyed by
`coordinate mod 5`. -/
def mLo (m : ℕ) : ℚ :=
  if m % 5 = 0 then 5931007/16777216
  else if m % 5 = 1 then 4341759/16777216
  else if m % 5 = 2 then 113/256
  else if m % 5 = 3 then 6172671/16777216
  else 1967/4096

/-- Upper bounds, same real period-5 pattern. -/
def mHi (m : ℕ) : ℚ :=
  if m % 5 = 0 then 13099009/16777216
  else if m % 5 = 1 then 13074433/16777216
  else if m % 5 = 2 then 9740289/16777216
  else if m % 5 = 3 then 12550145/16777216
  else 10854401/16777216

/-- The 20-dim demo ambient box: periodic extension of the real bounds. -/
def mXl : Fin 20 → ℚ := fun j => mLo (j : ℕ)

/-- The 20-dim demo ambient box, upper bounds. -/
def mXu : Fin 20 → ℚ := fun j => mHi (j : ℕ)

theorem metaroom_box (j : Fin 20) : mXl j ≤ mXu j := by
  simp only [mXl, mXu, mLo, mHi]
  split_ifs <;> norm_num

/-- The demo shift (positions 0 and 5) moves coordinates by 15 mod 20 —
which preserves `coordinate mod 5`, hence the period-5 real bounds. -/
theorem metaroom_shift_val_mod (j : Fin 20) :
    ((convShift 20 0 5 j : Fin 20) : ℕ) % 5 = (j : ℕ) % 5 := by
  have h1 : ((convShift 20 0 5 j : Fin 20) : ℕ)
      = (((((0 : ℕ) : Fin 20) - ((5 : ℕ) : Fin 20)) : Fin 20).val + (j : ℕ)) % 20 := by
    rw [convShift_apply]
    exact Fin.val_add _ _
  have h2 : ((((0 : ℕ) : Fin 20) - ((5 : ℕ) : Fin 20)) : Fin 20).val = 15 := by
    decide
  have hj : (j : ℕ) < 20 := j.isLt
  rw [h1, h2]
  omega

/-- Radius preservation for the demo: the real period-5 widths are invariant
under the demo shift (discharged through the period-5 structure — exact
rationals, no measurement). -/
theorem metaroom_width_shift (j : Fin 20) :
    mXu j - mXl j
      = mXu (convShift 20 0 5 j) - mXl (convShift 20 0 5 j) := by
  have h5 := metaroom_shift_val_mod j
  simp only [mXl, mXu, mLo, mHi, h5]

/-- **Demo headline: two spatial positions of the REAL metaroom conv2 pair
share their coupling defect**, on every pattern `S` — by the general
translation-invariance theorem, with every hypothesis discharged by
`norm_num` on the transcribed exact rationals. -/
theorem metaroom_conv2_defect_translation_invariant (S : Finset (Fin 2)) :
    InventionWave1.coordDefect mCC (convRows 20 mW1 mW2 0 5) mXl mXu S
      = InventionWave1.coordDefect mCC (convRows 20 mW1 mW2 0 0) mXl mXu S :=
  conv_defect_translation_invariant mCC mW1 mW2 0 0 5 mXl mXu
    (by norm_num) (by norm_num) metaroom_width_shift S

theorem mCC_pos : ∀ i, 0 < mCC i := by
  intro i
  fin_cases i <;> norm_num [mCC]

/-- The shared defect is strictly POSITIVE at position 0: coordinate 0 is
pulled in opposite directions by the two channels
(`mW1 0 · mW2 0 = (5004725/16777216)·(-683851/4194304) < 0` — wave-1's
syntactic sign criterion), and the real box is non-degenerate there. -/
theorem metaroom_conv2_defect_pos :
    0 < InventionWave1.coordDefect mCC (convRows 20 mW1 mW2 0 0)
          mXl mXu Finset.univ := by
  unfold InventionWave1.coordDefect
  apply Finset.sum_pos'
  · intro j _
    apply mul_nonneg
    · exact InventionWave1.coord_term_nonneg mCC
        (fun i => convRows 20 mW1 mW2 0 0 i j)
        (fun i => le_of_lt (mCC_pos i)) Finset.univ
    · have := metaroom_box j
      linarith
  · refine ⟨0, Finset.mem_univ _, ?_⟩
    apply mul_pos
    · refine (InventionWave1.coord_term_pos_iff mCC
        (fun i => convRows 20 mW1 mW2 0 0 i 0) mCC_pos).mpr ⟨0, 1, ?_⟩
      have h0 : convRows 20 mW1 mW2 0 0 0 (0 : Fin 20)
          = 5004725/16777216 := by
        norm_num [convRows, tapsAt, Fin.sum_univ_succ, mW1]
      have h1 : convRows 20 mW1 mW2 0 0 1 (0 : Fin 20)
          = -683851/4194304 := by
        norm_num [convRows, tapsAt, Fin.sum_univ_succ, mW2]
      show convRows 20 mW1 mW2 0 0 0 (0 : Fin 20)
          * convRows 20 mW1 mW2 0 0 1 (0 : Fin 20) < 0
      rw [h0, h1]
      norm_num
    · have hu : mXu (0 : Fin 20) = 13099009/16777216 := by
        norm_num [mXu, mHi]
      have hl : mXl (0 : Fin 20) = 5931007/16777216 := by
        norm_num [mXl, mLo]
      rw [hu, hl]
      norm_num

/-- ONE verified defect computation certifies BOTH sites: positivity at the
translated position 5 follows from positivity at position 0 through the
invariance theorem — no second per-coordinate computation. -/
theorem metaroom_conv2_defect_pos_shifted :
    0 < InventionWave1.coordDefect mCC (convRows 20 mW1 mW2 0 5)
          mXl mXu Finset.univ := by
  rw [metaroom_conv2_defect_translation_invariant Finset.univ]
  exact metaroom_conv2_defect_pos

/-
  Expected output of every `#print axioms` below (verified via `lake build`):

    '…' depends on axioms: [propext, Classical.choice, Quot.sound]

  No `sorryAx`, no domain-specific axioms, no `Lean.ofReduceBool`
  (no `native_decide`).
-/
#print axioms coordDefect_perm_invariant
#print axioms convShift_offset
#print axioms convShift_window_val
#print axioms tapsAt_convShift
#print axioms convRows_convShift
#print axioms conv_defect_translation_invariant
#print axioms conv_pair_defect_center_free
#print axioms conv_pair_gap_position_invariant
#print axioms gap_inf'_eq_defect_univ
#print axioms conv_pair_gap_translation_invariant
#print axioms conv_pair_gap_translation_invariant_exact
#print axioms metaroom_box
#print axioms metaroom_shift_val_mod
#print axioms metaroom_width_shift
#print axioms metaroom_conv2_defect_translation_invariant
#print axioms mCC_pos
#print axioms metaroom_conv2_defect_pos
#print axioms metaroom_conv2_defect_pos_shifted

end InventionWave2
end Crownproof
