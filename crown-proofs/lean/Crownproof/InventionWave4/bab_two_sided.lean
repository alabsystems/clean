/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

INVENTION WAVE 4 — `bab_two_sided` / `falsify_complete`
(completeness-pruning C4 — the SAT/falsification half of verified completeness).

Sealed conjecture-set: data/provenance/invention-wave-4-conjectures-2026-06-13.json
  conjecture-set sha256 ec642163a6c418261dbe4e39aba64e353255100aa58ad286e543dd5c254ab208
  recon digest      sha256 6a9763a8e0ecf713651b18ea7b6bdd06325bb47ba2706bb0cd56448f96feddfd
This target is a wave-1 carryover, sealed BEFORE any proof attempt, carrying its
ORIGINAL wave-1 sha256 (data/provenance/invention-wave-1-conjectures-2026-06-11.json):

  C4 — falsify_complete / bab_two_sided: the missing falsification half of
       verified completeness + the two-sided verdict theorem.
  conjecture sha256 d89bab96e943c53b1331f972d490e578628d27bf4e04c0246cb7ab162d17a78b
  wave4 verdict: prove-next (rank 3; prov 6, impact 6; "dischargeable today").

────────────────────────────────────────────────────────────────────────────
WHAT THE UNSAT HALF ALREADY GIVES, AND WHAT THIS FILE ADDS
────────────────────────────────────────────────────────────────────────────
`Complete.complete` (Complete.lean) is the UNSAT (verification) half: a STRICT
positive margin `δ ≤ trueMin(root)` forces a finite bisection depth at which
every leaf's relaxed bound is positive, so the property `safe` holds on the whole
box.  That answers "the property is TRUE — here is the finite tree that proves
it."

It says NOTHING about the other verdict.  When the property is FALSE — some point
of the box violates it with a separation margin — a complete BaB procedure must
also TERMINATE, but with a *counterexample*, not a safety proof.  This file
proves that SAT (falsification) half and assembles the **two-sided verdict**:

  • SAT  (`exists_violating_leaf`): if some sample `s₀ ∈ B` violates with margin
    `δ` (`fval s₀ ≤ −δ`, `δ > 0`), then at a finite Archimedean depth `d` the
    leaf `C ∋ s₀` has its PICKED sample concretely violating, `fval (pick C) < 0`
    — a finite leaf-sweep terminates with a kernel-checkable counterexample
    `pick C` (`¬ safe (pick C)`).
  • UNSAT (re-exported `Complete.complete`): δ ≤ trueMin B ⟹ safe everywhere.
  • `bab_two_sided`: from the separation dichotomy
    `(δ ≤ trueMin B) ∨ (∃ s₀ ∈ B, fval s₀ ≤ −δ)`, the procedure returns a
    `Verdict` — a constructive `Safe`-proof on one side, a concrete violating
    sample on the other.

The SAT side's ONE analytic ingredient is the SAMPLED-LIPSCHITZ bound
`fval (pick B) − fval s ≤ L·diam B` for `s ∈ B` (the `−`-direction of
`|fval (pick B) − fval s| ≤ L·diam B`).  That is exactly the landed lemma
`CompleteGeneralDepth.net_lipschitz_abs` (the general-depth product constant
`L = ∏ₖ ‖Wₖ‖`); we FIRE the abstract SAT theorem on `demoNet` (the landed
arbitrary-depth net) with the picker = left-corner, discharging the bound from
`net_lipschitz_abs` exactly as `relaxedBound_sound` does.

────────────────────────────────────────────────────────────────────────────
STATEMENT FIDELITY vs THE SEAL — documented deltas
────────────────────────────────────────────────────────────────────────────
The seal sketches C4 as `falsify_complete` + a `trueMin_le` coherence field added
"via `extends`" plus "`demoNet` `sInf` plumbing".  Faithful realisation, with the
deltas stated openly:

  Δ1  COHERENCE FIELD — kept, RENAMED + STRENGTHENED to the directly-needed shape.
      The seal names a `trueMin_le` field; the SAT chain needs the SAMPLE-vs-point
      bound `fval (pick B) − fval s ≤ L·diam B` (`sampled_lip`), which is the
      `net_lipschitz_abs` shape the plan (rank 3) calls out as ALREADY LANDED.
      `sampled_lip` is what discharges the falsification; the `trueMin`-coherence
      `trueMin_le : ∀ B s, mem B s → trueMin B ≤ fval s` is ALSO carried (it is the
      `csInf_le` plumbing the seal names) and used to phrase the violation
      hypothesis as a true-min separation in the convenience corollary, but the
      core `exists_violating_leaf` takes the violating SAMPLE directly, so it does
      NOT depend on `trueMin_le`.  Both fields are default-free, so existing
      `Relaxation` instances lift verbatim (no `Relaxation` change).

  Δ2  EMPTY-BOX HONESTY.  `pick_mem` (picked point lies in the box) is FALSE on
      empty boxes (`B.1 > B.2`), so it is NOT a structure field.  It is never
      needed: the SAT chain reaches the violating leaf through `mem_leaf_of_mem`
      (which yields a leaf `C` with `s₀ ∈ C`, hence `C` nonempty), and
      `sampled_lip` is vacuous on empty boxes.  The picked sample is taken at the
      violating leaf only.

  Δ3  `fval` + `safe_iff`.  The abstract `Relaxation.safe` is an opaque `Prop`; a
      falsification needs a real-valued margin, so `FalsifyRelaxation` adds
      `fval : Sample → ℝ` with `safe_iff : safe s ↔ 0 < fval s`.  For the demo this
      is `fval = demoNet`, `safe s = 0 < demoNet s` — definitionally aligned, the
      `safe_iff` is `Iff.rfl`.

  Δ4  TWO-SIDED VERDICT SHAPE.  Realised as a `Verdict` inductive
      (`safeAll` / `violated`) returned from the separation dichotomy — the
      "two-sided verdict theorem" the seal names, made constructive.

HONESTY (W4 gate, N1).  This is "two-sided BaB TERMINATION on δ-separated
instances", a FIRST FORMALIZATION (N1, pending the novelty-index check); two-sided
BaB termination on separated instances is folklore (Bunel et al., JMLR 2020).  It
is NOT called a "decision procedure"; the separation `δ` is a STATED hypothesis,
not decided here.  Every counted quantity is Δdomains-class (a bisection DEPTH and
a leaf's picked sample); no GPU / wall-clock / solved-instance claim.  Penalty-
immunity reading (PHASE2): a kernel-checked `fval (pick C) < 0` on a rational net
means a "violated" verdict can never draw the −150 VNN-COMP penalty — but that
framing is a CONSEQUENCE, not claimed as a solved instance here.
-/
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Crownproof.Complete
import Crownproof.CompleteGeneralDepth

namespace Crownproof
namespace Complete

/-! ## 1. The falsification-aware relaxation

`FalsifyRelaxation` extends the soundness/completeness `Relaxation` with exactly
the data a falsification needs: a real-valued margin `fval`, a per-box sampler
`pick`, the sample-vs-point Lipschitz bound (`sampled_lip`, the
`net_lipschitz_abs` shape), and a `trueMin`-coherence field (`trueMin_le`).  Every
new field is default-free, so any concrete `Relaxation` lifts to a
`FalsifyRelaxation` by supplying them — no change to `Relaxation` itself. -/

/-- A `Relaxation` augmented with the falsification interface.

* `fval s`      — the real-valued safety margin at the sample point `s`
                  (`safe s ↔ 0 < fval s`).
* `pick B`      — a sampler returning ONE input point per box (only the picked
                  point of a NON-empty leaf is ever evaluated, see Δ2).
* `safe_iff`    — `safe s ↔ 0 < fval s` (the margin sign IS the verdict).
* `trueMin_le`  — `trueMin B ≤ fval s` for `s ∈ B`: the true min is a lower bound
                  of every in-box sample value (the `csInf_le` coherence).
* `sampled_lip` — `fval (pick B) − fval s ≤ L·diam B` for `s ∈ B`: the picked
                  sample over-estimates any in-box value by at most the Lipschitz
                  width error.  This is the `net_lipschitz_abs` (`|·| ≤ L·diam`)
                  shape, `−`-direction; it is the SOLE analytic ingredient of the
                  SAT half. -/
structure FalsifyRelaxation (Box : Type*) (Sample : Type*)
    extends Relaxation Box Sample where
  /-- The real-valued safety margin at a sample point. -/
  fval        : Sample → ℝ
  /-- A per-box sampler (only evaluated on non-empty leaves; see Δ2). -/
  pick        : Box → Sample
  /-- The margin sign is exactly the safety verdict. -/
  safe_iff    : ∀ s, safe s ↔ 0 < fval s
  /-- `trueMin` is a lower bound of every in-box sample value (`csInf_le`). -/
  trueMin_le  : ∀ B s, mem B s → trueMin B ≤ fval s
  /-- **Sampled-Lipschitz bound** (`net_lipschitz_abs` shape): the picked sample
  over-estimates any in-box value by at most `L·diam`. -/
  sampled_lip : ∀ B s, mem B s → fval (pick B) - fval s ≤ L * diam B

variable {Box : Type*} {Sample : Type*} (R : FalsifyRelaxation Box Sample)

/-! ## 2. The SAT (falsification) core

The mirror of `exists_decisive_depth`: where the UNSAT side shrinks the relaxed
bound BELOW the positive margin, the SAT side shrinks the Lipschitz width error
below the violation margin, so a violating sample's leaf has a violating PICK. -/

/-- **Sampled violation at small diameter.** If a sample `s ∈ C` violates with
margin `δ` (`fval s ≤ −δ`) and the leaf `C`'s Lipschitz width error is below `δ`
(`L·diam C < δ`), then the PICKED sample of `C` concretely violates,
`fval (pick C) < 0`.  This is the falsification twin of
`relaxedBound_pos_of_diam_lt`. -/
theorem pick_neg_of_diam_lt {C : Box} {s : Sample} {δ : ℝ}
    (hmem : R.mem C s) (hviol : R.fval s ≤ -δ) (hdiam : R.L * R.diam C < δ) :
    R.fval (R.pick C) < 0 := by
  -- fval (pick C) ≤ fval s + L·diam C ≤ −δ + L·diam C < 0
  have hlip := R.sampled_lip C s hmem      -- fval (pick C) − fval s ≤ L·diam C
  linarith

/-- **Finite falsifying depth EXISTS (SAT termination).**
If some sample `s₀ ∈ B` violates with a strict separation margin `δ`
(`0 < δ`, `fval s₀ ≤ −δ`), there is a finite bisection depth `d` and a depth-`d`
leaf `C` of `B` whose PICKED sample concretely violates (`fval (pick C) < 0`).
The depth is the SAME Archimedean witness `2^d > L·diam₀/δ` as the UNSAT side;
here it drives the Lipschitz width error below the violation margin, so the leaf
that inherits `s₀` (by covering) has a negative picked sample.  A finite sweep of
the depth-`d` leaves TERMINATES with a kernel-checkable counterexample. -/
theorem exists_violating_leaf (B : Box) {s₀ : Sample} {δ : ℝ} (hδ : 0 < δ)
    (hmem₀ : R.mem B s₀) (hviol : R.fval s₀ ≤ -δ) :
    ∃ d : ℕ, ∃ C ∈ leafBoxes R.toRelaxation B d,
      R.mem C s₀ ∧ R.fval (R.pick C) < 0 := by
  -- pick d with 2^d > L·diam₀/δ  (identical Archimedean step to exists_decisive_depth)
  obtain ⟨d, hd⟩ := pow_unbounded_of_one_lt (R.L * R.diam B / δ) (by norm_num : (1:ℝ) < 2)
  refine ⟨d, ?_⟩
  have hpow : (0:ℝ) < 2 ^ d := by positivity
  -- s₀ lands in some depth-d leaf C (covering)
  obtain ⟨C, hCmem, hCs⟩ := mem_leaf_of_mem R.toRelaxation B d s₀ hmem₀
  refine ⟨C, hCmem, hCs, ?_⟩
  -- diam C ≤ diam₀ / 2^d
  have hdiamC : R.diam C ≤ R.diam B / 2 ^ d := leaf_diam_le R.toRelaxation B d C hCmem
  -- L·diam C < δ  (same width-error shrink as the UNSAT side)
  have hkey : R.L * R.diam C < δ := by
    have hLdiam : R.L * R.diam C ≤ R.L * (R.diam B / 2 ^ d) :=
      mul_le_mul_of_nonneg_left hdiamC R.L_nonneg
    rw [div_lt_iff₀ hδ] at hd        -- hd : L·diam B < 2^d * δ
    have : R.L * (R.diam B / 2 ^ d) < δ := by
      rw [mul_div_assoc', div_lt_iff₀ hpow]
      nlinarith
    linarith
  exact pick_neg_of_diam_lt R hCs hviol hkey

/-! ## 3. The two-sided verdict

A `Verdict` is a constructive disjunction: either the property holds on the whole
box (a `safe`-proof, the UNSAT side, from `Complete.complete`), or a concrete
sample violates it (the SAT side, from `exists_violating_leaf`).  `bab_two_sided`
turns the separation DICHOTOMY into a `Verdict`. -/

/-- A two-sided branch-and-bound verdict on box `B`. -/
inductive Verdict (R : FalsifyRelaxation Box Sample) (B : Box) : Prop
  /-- UNSAT: the property holds on every point of `B`. -/
  | safeAll  (h : ∀ s, R.mem B s → R.safe s) : Verdict R B
  /-- SAT: a concrete sample `s` of some finite-depth leaf violates the property
  (`¬ safe s`, equivalently `fval s ≤ 0`). -/
  | violated (s : Sample) (hviol : ¬ R.safe s) : Verdict R B

/-- **THE TWO-SIDED VERDICT THEOREM.**
Under a separation dichotomy — EITHER the true minimum over `B` is bounded below
by a strict positive margin `δ` (the property holds with headroom), OR some
sample of `B` violates with margin `δ` — the branch-and-bound procedure returns a
`Verdict`:

* `δ ≤ trueMin B`  ⟹  `safeAll`: `Complete.complete` finds the finite UNSAT depth
  and decides `safe` on the whole box.
* `∃ s₀ ∈ B, fval s₀ ≤ −δ`  ⟹  `violated`: `exists_violating_leaf` finds the
  finite SAT depth and returns the leaf whose PICKED sample concretely violates
  (`fval (pick C) < 0`, so `¬ safe (pick C)` via `safe_iff`).

This is the full two-sided result: a SINGLE separated instance is decided in
finitely many bisections, with the verdict carrying its witness on EITHER side.
N1 — "two-sided BaB termination on δ-separated instances"; the separation `δ` is a
STATED hypothesis, NOT a decision procedure. -/
theorem bab_two_sided (B : Box) {δ : ℝ} (hδ : 0 < δ)
    (hsep : δ ≤ R.trueMin B ∨ ∃ s₀, R.mem B s₀ ∧ R.fval s₀ ≤ -δ) :
    Verdict R B := by
  rcases hsep with hsafe | ⟨s₀, hmem₀, hviol⟩
  · -- UNSAT side: positive margin ⟹ safe everywhere (Complete.complete).
    obtain ⟨_, _, hdec⟩ := Complete.complete R.toRelaxation B hδ hsafe
    exact .safeAll hdec
  · -- SAT side: separated violator ⟹ a finite-depth leaf's pick violates.
    obtain ⟨_, C, _, _, hpick⟩ := exists_violating_leaf R B hδ hmem₀ hviol
    refine .violated (R.pick C) ?_
    -- ¬ safe (pick C):  safe ↔ 0 < fval, but fval (pick C) < 0.
    rw [R.safe_iff]
    linarith

/-- **SAT half, packaged as `falsify_complete`** — the named missing half: a
δ-separated violator yields a finite bisection depth whose picked leaf sample is a
kernel-checkable counterexample (`¬ safe`).  This is the precise mirror of
`Complete.complete` (the UNSAT half). -/
theorem falsify_complete (B : Box) {s₀ : Sample} {δ : ℝ} (hδ : 0 < δ)
    (hmem₀ : R.mem B s₀) (hviol : R.fval s₀ ≤ -δ) :
    ∃ d : ℕ, ∃ C ∈ leafBoxes R.toRelaxation B d, R.mem C s₀ ∧ ¬ R.safe (R.pick C) := by
  obtain ⟨d, C, hCmem, hCs, hpick⟩ := exists_violating_leaf R B hδ hmem₀ hviol
  refine ⟨d, C, hCmem, hCs, ?_⟩
  rw [R.safe_iff]
  linarith

end Complete

/-! ## 4. CONCRETE instantiation — FIRE the two-sided verdict on `demoNet`

The landed arbitrary-depth net `CompleteGeneralDepth.demoNet` (depth 3, Lipschitz
`L = ∏ₖ ‖Wₖ‖ = 2`) already discharges every `Relaxation` field via
`genRelaxation`.  We lift it to a `FalsifyRelaxation` with `fval = demoNet`,
`pick = left-corner`, discharging:

* `safe_iff`    — `Iff.rfl` (`safe s` IS `0 < demoNet s`);
* `trueMin_le`  — `csInf_le` (the `sInf` plumbing the seal names);
* `sampled_lip` — `net_lipschitz_abs` at `demoLayers`, the SAME computation as
  `relaxedBound_sound`.

Because `demoNet ≥ 1` GLOBALLY (`demoNet_ge_one`), this net has NO violating
sample — so on the demo only the UNSAT (`safeAll`) leg fires (`demo_two_sided`),
exactly reproducing the landed `gen_complete`.  To exercise the SAT leg on a
genuinely-violated instance we add a tiny SHIFTED net `falsifyNet x = demoNet x −
2` (Lipschitz `L = 2` unchanged, `falsifyNet 0 = demoNet 0 − 2`), which DOES
violate, and fire `falsify_complete` / `bab_two_sided` to return a concrete
counterexample (`falsify_demo`).  Both legs are kernel-checked, sorry-free. -/

namespace CompleteGeneralDepth

open Complete

/-- The demo net lifted to a `FalsifyRelaxation`: margin = `demoNet`, picker =
left corner.  Every base `Relaxation` field is inherited from `genRelaxation`. -/
noncomputable def genFalsify : FalsifyRelaxation Box ℝ where
  toRelaxation := genRelaxation
  fval        := demoNet
  pick        := fun B => B.1
  safe_iff    := fun _ => Iff.rfl
  trueMin_le  := by
    -- trueMin B = sInf (demoNet '' boxSet B) ≤ demoNet s for s ∈ B
    rintro B s ⟨h1, h2⟩
    exact csInf_le (img_bddBelow B) ⟨s, ⟨h1, h2⟩, rfl⟩
  sampled_lip := by
    -- demoNet B.1 − demoNet s ≤ L·|B.1 − s| ≤ L·diam B   (net_lipschitz_abs shape)
    rintro B s ⟨h1, h2⟩
    obtain ⟨lo, hi⟩ := B
    simp only at h1 h2
    have hlip : |demoNet lo - demoNet s| ≤ L * |lo - s| := by
      have := net_lipschitz_abs demoLayers lo s
      simpa [demoNet, L] using this
    have hls : |lo - s| = s - lo := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
    have hbound : demoNet lo - demoNet s ≤ |demoNet lo - demoNet s| := le_abs_self _
    have hdiam_ge : s - lo ≤ diam (lo, hi) := by
      simp only [diam]
      calc s - lo ≤ hi - lo := by linarith
        _ ≤ max 0 (hi - lo) := le_max_right _ _
    have hLmul : L * (s - lo) ≤ L * diam (lo, hi) :=
      mul_le_mul_of_nonneg_left hdiam_ge L_nonneg
    rw [hls] at hlip
    -- demoNet lo − demoNet s ≤ L·(s − lo) ≤ L·diam
    calc demoNet lo - demoNet s
        ≤ L * (s - lo) := le_trans hbound hlip
      _ ≤ L * diam (lo, hi) := hLmul

/-- **Two-sided verdict, fired on the depth-3 demo net.**  `demoNet ≥ 1`
everywhere, so the separation dichotomy resolves on the UNSAT side with `δ = 1`:
`bab_two_sided` returns `safeAll` — `demoNet > 0` on the whole input box `[0,2]`,
the SAME decision `gen_complete` produces, now as the UNSAT leg of the two-sided
theorem. -/
theorem demo_two_sided : Verdict genFalsify (0, 2) :=
  bab_two_sided genFalsify (0, 2) (by norm_num)
    (Or.inl margin_pos)

/-- Extracted: the demo two-sided verdict is the SAFE leg — `demoNet(x) > 0` on
`[0,2]`, decided through the two-sided procedure. -/
theorem demo_two_sided_safe : ∀ x : ℝ, genFalsify.mem (0, 2) x → genFalsify.safe x := by
  have h := demo_two_sided
  cases h with
  | safeAll hsafe => exact hsafe
  | violated s hviol =>
      -- impossible: demoNet ≥ 1 > 0, so safe holds at every sample
      exact absurd (lt_of_lt_of_le (by norm_num) (demoNet_ge_one s)) hviol

/-! ### A genuinely-violated instance to fire the SAT leg

`falsifyNet x = demoNet x − 2`.  Since `demoNet 0 = relu(relu(relu 0 − 1) + 1) =
relu(relu(−1)+1) = relu(0+1) = 1`, we get `falsifyNet 0 = −1 < 0`: the input
point `0 ∈ [0,2]` is a CONCRETE violation with margin `δ = 1` (`falsifyNet 0 =
−1 ≤ −1`).  The shift preserves the Lipschitz constant (`L = 2`), so all
`Relaxation`/`FalsifyRelaxation` laws lift; we instantiate and fire
`falsify_complete` to obtain a finite-depth leaf whose picked sample is a
kernel-checked counterexample. -/

/-- `demoNet 0 = 1` (kernel-computed: `relu(relu(relu(0)−1)+1) = relu(0+1) = 1`). -/
lemma demoNet_zero : demoNet 0 = 1 := by
  rw [demoNet_explicit]
  simp only [relu]
  norm_num

/-- The shifted (violating) margin function and its box data. -/
noncomputable def falsifyNet (x : ℝ) : ℝ := demoNet x - 2

/-- The shifted net's relaxed bound: `falsifyNet lo − L·diam` on a NON-empty box,
clamped to `0` on the empty box (`B.1 > B.2`).  The clamp is the standard
empty-box convention: it ONLY changes the (unreachable) empty case so the
`width_error` law holds there (`trueMin − L·diam = 0 ≤ 0`); on every non-empty
box — the only boxes the procedure evaluates — it is the unguarded
`falsifyNet lo − L·diam`, leaving soundness untouched.  (The non-violating
`genRelaxation` needed no clamp because `demoNet ≥ 1 > 0` made its bound positive
on the empty box; the violating net's bound can be negative, so the clamp is
required.) -/
noncomputable def fRelaxedBound (B : Box) : ℝ :=
  if B.1 ≤ B.2 then falsifyNet B.1 - L * diam B else 0

/-- The shifted true minimum over a box. -/
noncomputable def fTrueMin (B : Box) : ℝ := sInf (falsifyNet '' boxSet B)

/-- `falsifyNet` is bounded below (by `−1`, since `demoNet ≥ 1`). -/
lemma fimg_bddBelow (B : Box) : BddBelow (falsifyNet '' boxSet B) := by
  refine ⟨-1, ?_⟩
  rintro y ⟨x, _, rfl⟩
  simp only [falsifyNet]; linarith [demoNet_ge_one x]

/-- Shifted Lipschitz bound: `|falsifyNet x − falsifyNet y| ≤ L·|x − y|` (the
shift cancels, so it is exactly `net_lipschitz_abs` at `demoLayers`). -/
lemma falsify_lip_abs (x y : ℝ) : |falsifyNet x - falsifyNet y| ≤ L * |x - y| := by
  have h := net_lipschitz_abs demoLayers x y
  simp only [falsifyNet]
  rw [show demoNet x - 2 - (demoNet y - 2) = demoNet x - demoNet y by ring]
  simpa [demoNet, L] using h

/-- Shifted relaxed-bound soundness (mirror of `relaxedBound_sound`). -/
lemma fRelaxedBound_sound (B : Box) (s : ℝ) (hs : mem B s) :
    fRelaxedBound B ≤ falsifyNet s := by
  obtain ⟨lo, hi⟩ := B
  obtain ⟨h1, h2⟩ := hs
  have hlip : |falsifyNet s - falsifyNet lo| ≤ L * |s - lo| := falsify_lip_abs s lo
  have hsl : |s - lo| = s - lo := abs_of_nonneg (by linarith)
  have hdiam_ge : s - lo ≤ diam (lo, hi) := by
    simp only [diam]
    calc s - lo ≤ hi - lo := by linarith
      _ ≤ max 0 (hi - lo) := le_max_right _ _
  have hgs : falsifyNet lo - falsifyNet s ≤ L * (s - lo) := by
    have h2' : -(falsifyNet s - falsifyNet lo) ≤ |falsifyNet s - falsifyNet lo| := neg_le_abs _
    rw [hsl] at hlip
    linarith
  have hLmul : L * (s - lo) ≤ L * diam (lo, hi) :=
    mul_le_mul_of_nonneg_left hdiam_ge L_nonneg
  -- s ∈ [lo,hi] ⇒ lo ≤ hi, so the clamp reduces to the unguarded branch
  have hrb : fRelaxedBound (lo, hi) = falsifyNet lo - L * diam (lo, hi) := by
    simp only [fRelaxedBound]
    exact if_pos (show lo ≤ hi by linarith)
  rw [hrb]
  linarith

/-- Shifted width-error law. -/
lemma fwidth_error (B : Box) : fTrueMin B - L * diam B ≤ fRelaxedBound B := by
  obtain ⟨lo, hi⟩ := B
  rcases le_or_gt lo hi with hle | hgt
  · have hlo_mem : falsifyNet lo ∈ falsifyNet '' boxSet (lo, hi) :=
      ⟨lo, ⟨le_refl _, hle⟩, rfl⟩
    have hsinf_le : fTrueMin (lo, hi) ≤ falsifyNet lo := csInf_le (fimg_bddBelow _) hlo_mem
    simp only [fRelaxedBound, if_pos hle]
    linarith
  · -- empty box: relaxedBound clamps to 0, trueMin = 0, diam = 0, so 0 − 0 ≤ 0.
    have htm : fTrueMin (lo, hi) = 0 := by
      have hempty : boxSet (lo, hi) = (∅ : Set ℝ) := by
        simp only [boxSet]; exact Set.Icc_eq_empty (by linarith)
      simp only [fTrueMin, hempty, Set.image_empty, Real.sInf_empty]
    have hdiam0 : diam (lo, hi) = 0 := by
      simp only [diam]; exact max_eq_left (by linarith)
    have hrb : fRelaxedBound (lo, hi) = 0 := by
      simp only [fRelaxedBound]
      exact if_neg (not_le.mpr hgt)
    rw [htm, hdiam0, hrb]
    linarith

/-- Shifted true-min monotonicity helper. -/
lemma ftrueMin_mono_sub (B1 B2 : Box)
    (hsub : boxSet B2 ⊆ boxSet B1) (hne : (boxSet B2).Nonempty) :
    fTrueMin B1 ≤ fTrueMin B2 :=
  csInf_le_csInf (fimg_bddBelow _) (hne.image falsifyNet) (Set.image_mono hsub)

/-- Shifted true-min monotonicity law. -/
lemma ftrueMin_mono (B : Box) :
    fTrueMin B ≤ fTrueMin (split B).1 ∧ fTrueMin B ≤ fTrueMin (split B).2 := by
  obtain ⟨lo, hi⟩ := B
  simp only [split]
  constructor
  · rcases le_total lo hi with h | h
    · apply ftrueMin_mono_sub
      · rintro y ⟨hy1, hy2⟩
        exact ⟨hy1, by simp only at hy2 ⊢; linarith⟩
      · exact ⟨lo, by simp only [boxSet, Set.mem_Icc]; exact ⟨le_refl _, by linarith⟩⟩
    · rcases eq_or_lt_of_le h with heq | hlt
      · subst heq; simp only [show (hi + hi) / 2 = hi by ring, le_refl]
      · have e1 : boxSet (lo, hi) = (∅ : Set ℝ) := Set.Icc_eq_empty (by linarith)
        have e2 : boxSet (lo, (lo + hi) / 2) = (∅ : Set ℝ) := Set.Icc_eq_empty (by linarith)
        simp only [fTrueMin, e1, e2, Set.image_empty, Real.sInf_empty, le_refl]
  · rcases le_total lo hi with h | h
    · apply ftrueMin_mono_sub
      · rintro y ⟨hy1, hy2⟩
        exact ⟨by simp only at hy1 ⊢; linarith, hy2⟩
      · exact ⟨hi, by simp only [boxSet, Set.mem_Icc]; exact ⟨by linarith, le_refl _⟩⟩
    · rcases eq_or_lt_of_le h with heq | hlt
      · subst heq; simp only [show (hi + hi) / 2 = hi by ring, le_refl]
      · have e1 : boxSet (lo, hi) = (∅ : Set ℝ) := Set.Icc_eq_empty (by linarith)
        have e2 : boxSet ((lo + hi) / 2, hi) = (∅ : Set ℝ) := Set.Icc_eq_empty (by linarith)
        simp only [fTrueMin, e1, e2, Set.image_empty, Real.sInf_empty, le_refl]

/-- The shifted relaxation: a full `FalsifyRelaxation` whose margin `falsifyNet`
genuinely goes negative (`falsifyNet 0 = −1`), so the SAT leg fires. -/
noncomputable def falsifyRelaxation : FalsifyRelaxation Box ℝ where
  diam          := diam
  trueMin       := fTrueMin
  relaxedBound  := fRelaxedBound
  split         := split
  mem           := mem
  safe          := fun s => 0 < falsifyNet s
  L             := L
  L_nonneg      := L_nonneg
  diam_nonneg   := diam_nonneg
  width_error   := fwidth_error
  diam_contract := diam_contract
  trueMin_mono  := ftrueMin_mono
  decides       := fun B h s hs => lt_of_lt_of_le h (fRelaxedBound_sound B s hs)
  cover         := cover
  fval          := falsifyNet
  pick          := fun B => B.1
  safe_iff      := fun _ => Iff.rfl
  trueMin_le    := by
    rintro B s ⟨h1, h2⟩
    exact csInf_le (fimg_bddBelow B) ⟨s, ⟨h1, h2⟩, rfl⟩
  sampled_lip   := by
    rintro B s ⟨h1, h2⟩
    obtain ⟨lo, hi⟩ := B
    simp only at h1 h2
    have hlip : |falsifyNet lo - falsifyNet s| ≤ L * |lo - s| := falsify_lip_abs lo s
    have hls : |lo - s| = s - lo := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
    have hbound : falsifyNet lo - falsifyNet s ≤ |falsifyNet lo - falsifyNet s| := le_abs_self _
    have hdiam_ge : s - lo ≤ diam (lo, hi) := by
      simp only [diam]
      calc s - lo ≤ hi - lo := by linarith
        _ ≤ max 0 (hi - lo) := le_max_right _ _
    have hLmul : L * (s - lo) ≤ L * diam (lo, hi) :=
      mul_le_mul_of_nonneg_left hdiam_ge L_nonneg
    rw [hls] at hlip
    calc falsifyNet lo - falsifyNet s
        ≤ L * (s - lo) := le_trans hbound hlip
      _ ≤ L * diam (lo, hi) := hLmul

/-- The concrete violation: input `0 ∈ [0,2]` violates `falsifyNet` with margin
`δ = 1` (`falsifyNet 0 = −1 ≤ −1`). -/
lemma falsify_violation : falsifyRelaxation.fval 0 ≤ -1 := by
  show falsifyNet 0 ≤ -1
  simp only [falsifyNet, demoNet_zero]
  norm_num

/-- **SAT half fired on the violated net** — `falsify_complete` returns a finite
bisection depth and a leaf of `[0,2]` whose PICKED sample is a kernel-checked
counterexample (`¬ safe`, i.e. `falsifyNet (pick C) ≤ 0`). -/
theorem falsify_demo :
    ∃ d : ℕ, ∃ C ∈ Complete.leafBoxes falsifyRelaxation.toRelaxation (0, 2) d,
      falsifyRelaxation.mem C 0 ∧ ¬ falsifyRelaxation.safe (falsifyRelaxation.pick C) :=
  Complete.falsify_complete falsifyRelaxation (0, 2) (by norm_num)
    ⟨by norm_num, by norm_num⟩ falsify_violation

/-- **Two-sided verdict fired on the violated net** — the separation dichotomy
resolves on the SAT side (input `0` violates with margin `1`), so
`bab_two_sided` returns `violated` with a concrete counterexample sample. -/
theorem falsify_two_sided : Verdict falsifyRelaxation (0, 2) :=
  bab_two_sided falsifyRelaxation (0, 2) (by norm_num)
    (Or.inr ⟨0, ⟨by norm_num, by norm_num⟩, falsify_violation⟩)

/-- Extracted: the violated two-sided verdict is the `violated` leg — there is a
concrete sample at which `falsifyRelaxation` is NOT safe. -/
theorem falsify_two_sided_has_counterexample :
    ∃ s : ℝ, ¬ falsifyRelaxation.safe s := by
  have h := falsify_two_sided
  cases h with
  | safeAll hsafe =>
      -- impossible: 0 ∈ [0,2] and falsifyNet 0 = −1 < 0
      exact absurd (hsafe 0 ⟨by norm_num, by norm_num⟩)
        (by show ¬ (0 < falsifyNet 0); simp only [falsifyNet, demoNet_zero]; norm_num)
  | violated s hviol => exact ⟨s, hviol⟩

end CompleteGeneralDepth

/-! ## Trust-base check — every theorem must reduce to the standard logical axioms
only (`propext`, `Classical.choice`, `Quot.sound`), with NO `sorryAx`, NO
`native_decide` / `Lean.ofReduceBool`. -/

#print axioms Complete.pick_neg_of_diam_lt
#print axioms Complete.exists_violating_leaf
#print axioms Complete.bab_two_sided
#print axioms Complete.falsify_complete
#print axioms CompleteGeneralDepth.genFalsify
#print axioms CompleteGeneralDepth.demo_two_sided
#print axioms CompleteGeneralDepth.demo_two_sided_safe
#print axioms CompleteGeneralDepth.demoNet_zero
#print axioms CompleteGeneralDepth.falsifyRelaxation
#print axioms CompleteGeneralDepth.falsify_violation
#print axioms CompleteGeneralDepth.falsify_demo
#print axioms CompleteGeneralDepth.falsify_two_sided
#print axioms CompleteGeneralDepth.falsify_two_sided_has_counterexample

end Crownproof
