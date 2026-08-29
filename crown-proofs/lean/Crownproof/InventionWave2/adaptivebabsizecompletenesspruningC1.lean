/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

INVENTION WAVE 2 — `adaptive_bab_size` (completeness-pruning C1)

Sealed conjecture: "C1 — adaptive_bab_size: verified early-termination tree
with theorem-backed leaf count and exact Δdomains identity (SAFE: provable
in a session)."
Provenance: data/provenance/invention-wave-1-conjectures-2026-06-11.json,
angle `completeness-pruning`, conjecture sha256
b93b324259783037f0496cd7304cc6e0100fa2f578f582eebed600898c0ed09b
(sealed 2026-06-11 BEFORE any proof attempt).

## RESULT STATUS — proved-as-stated, sorry-free

All four theorem legs of the sealed Lean sketch are proved, with the sketch's
exact statements:

 1. `Complete.adaptive_length_le` — the adaptive leaf list has length ≤ 2^d
    (leg (i), the a-priori tree-size bound).  Made literal against the uniform
    tree by `Complete.leafBoxes_length` ((leafBoxes R B d).length = 2^d) and
    `Complete.adaptive_length_le_leafBoxes` (never worse than
    `Complete.leafBoxes`, the sealed phrasing).
 2. `Complete.adaptive_mem_leaf` — covering: every sample of the root box lands
    in some adaptive leaf (leg (i), "sub-cover"; the `R.cover` case split of
    `Complete.mem_leaf_of_mem` reused verbatim with one extra if-split).
 3. `Complete.adaptive_complete` — under the SAME δ-margin hypothesis as
    `Complete.complete`, with an oracle that is sound (`OracleSound`) and
    complete (`OracleComplete`), there is a finite depth at which EVERY
    adaptive leaf is closed by the oracle, the leaf count is ≤ 2^d, and root
    safety composes through the adaptive twin of `Complete.box_safe_of_leaves`
    (`Complete.adaptive_box_safe_of_leaves`) — leg (ii).
 4. `Complete.delta_domains_exact` — the exact Δdomains identity, stated
    ADDITIVELY:  (adaptiveLeaves R closes d B).length + prunedCount R closes d B
    = 2^d — leg (iii).  The program's only sanctioned metric (Δdomains, exactly
    counted) is here a kernel-checked identity, not a measurement.

Concrete instance (the sealed `builds_on` demo): `CompleteIBP.ibpRelaxation`
with the oracle `ibpCloses B = decide (0 < relaxedBound B)` (classically
decidable, sound AND complete by construction).  On the real 1→2→1 ReLU net:
  * `CompleteIBP.ibpCloses_root_false` — the oracle genuinely REJECTS the root
    box [0,2] (IBP is loose there: `relaxedBound_root_zero`), so the adaptive
    tree really splits — the firing is non-vacuous;
  * `CompleteIBP.ibp_adaptive_complete` — the abstract theorem fires end-to-end;
  * `CompleteIBP.ibp_adaptiveLeaves_two` — at fuel 2 the adaptive leaf list is
    EXACTLY [[0,1], [1,2]] (both children close at depth 1);
  * `CompleteIBP.ibp_delta_domains_two` — Δdomains = prunedCount = 2 exactly:
    2 adaptive leaves + 2 pruned = 4 = 2² uniform leaves, kernel-checked.

## FORMALIZATION DELTA vs the sealed Lean sketch (minimal, documented)

 * `prunedCount` is defined EXACTLY as the sketch wrote it, including the
   `2 ^ (d + 1) - 1` ℕ-subtraction in the early-close branch.  The sealed
   "stated additively (no ℕ subtraction)" discipline applies to the IDENTITY
   (`delta_domains_exact`), which is additive; inside the definition the
   subtraction is exact (1 ≤ 2^(d+1)), so no truncation occurs — the proof
   discharges the closed case with `0 < 2^(d+1)` + `omega`.
 * `adaptive_exists_decisive_depth` re-runs the Archimedean arithmetic of
   `Complete.exists_decisive_depth` rather than invoking it: an early-closed
   adaptive leaf lives at depth < d, so it is NOT a member of
   `leafBoxes R B d` and the original lemma cannot be applied as-is.  The
   per-leaf dichotomy `adaptive_leaf_closes_or_deep` (closed, or full-depth
   with the SAME diam/trueMin inheritance as `leaf_diam_le`/`leaf_trueMin_ge`)
   supplies the inheritance instead; the arithmetic core is copied verbatim.
   This is the sketch's own "actually simpler: prove diam/trueMin inheritance
   directly for adaptiveLeaves" route.
 * Informal leg (iv) ("each early-closed node carries the SAME certificate
   kind the leaves carry … one kernel-checkable object via the BabProof
   recursor") has no theorem in the sealed Lean sketch.  At this file's
   abstraction level it is carried by the single uniform oracle: in
   `adaptive_complete` EVERY leaf — early-closed or full-depth — discharges
   the one obligation `closes C = true`, and `adaptive_box_safe_of_leaves`
   composes exactly those uniform certificates (mirroring the oracle
   discipline of `BabProof.checkLeafCert`/`checkLeafSafe`).  A literal
   `BabProof`-recursor packaging (inline integer-pair `LeafCert`s) is NOT
   attempted here: bridging the abstract `Relaxation` box type to QPair
   margins is outside the sealed sketch.  HONEST SCOPE, no claim made.
 * Reconciliation extras (additions, not weakenings): for the never-closing
   oracle the adaptive tree IS the uniform tree
   (`adaptiveLeaves_false_eq_leafBoxes`) and nothing is pruned
   (`prunedCount_false`) — Δdomains = 0 degenerates correctly.

## HONESTY RAILS (per the sealed risk notes)

 * This is an **adaptive tree-size theorem**, NEVER a "decision procedure"
   (W4 gate closed): `width_error` / `diam_contract` / `trueMin_mono` /
   `decides` remain `Relaxation` structure-field hypotheses, and the δ-margin
   is a hypothesis; instantiation for real backward CROWN is not claimed.
 * The depth bound d* ≥ log₂(L·diam₀/δ) is FOLKLORE complexity analysis
   (the Bunel et al. JMLR 2020 line treats BaB termination informally;
   Lipschitz global optimization has the same counting).  Novelty claim is
   strictly **first formalization — N1-novel, pending index check**; no new
   mathematics is claimed.
 * No GPU / wall-clock / VNN-COMP scoring claims.  The only metric touched is
   Δdomains, exactly counted — and the point of this file is precisely that
   it is now a kernel-checked identity.
-/
import Crownproof.Complete
import Crownproof.CompleteIBP

namespace Crownproof

namespace Complete

variable {Box : Type*} {Sample : Type*} (R : Relaxation Box Sample)

/-! ## 1. The adaptive bisection tree

`adaptiveLeaves closes d B` — a box becomes a leaf as soon as the certificate
oracle `closes` accepts it; otherwise it is bisected, up to fuel `d`.  At fuel
`0` the surviving box is a (full-depth) leaf regardless of the oracle.  This is
the early-termination twin of `leafBoxes` (which is the `closes = fun _ =>
false` special case, proved below). -/

/-- Adaptive bisection: close a box as soon as the certificate oracle accepts. -/
def adaptiveLeaves (closes : Box → Bool) : ℕ → Box → List Box
  | 0, B => [B]
  | d + 1, B =>
      if closes B then [B]
      else adaptiveLeaves closes d (R.split B).1 ++ adaptiveLeaves closes d (R.split B).2

/-- **Oracle soundness** — the oracle only accepts boxes whose relaxed bound is
strictly positive (the exact guarantee a CROWN/Farkas leaf certificate check
provides; mirrors `BabProof.checkLeafCert`'s acceptance discipline). -/
def OracleSound (closes : Box → Bool) : Prop :=
  ∀ B, closes B = true → 0 < R.relaxedBound B

/-- **Oracle completeness** — the oracle accepts every box whose relaxed bound
is strictly positive (the check does not miss a valid certificate). -/
def OracleComplete (closes : Box → Bool) : Prop :=
  ∀ B, 0 < R.relaxedBound B → closes B = true

/-! ## 2. Leaf count: the uniform tree is exactly `2^d`, the adaptive tree never
worse — leg (i) of the sealed statement. -/

/-- The uniform depth-`d` bisection has EXACTLY `2^d` leaves. -/
theorem leafBoxes_length (B : Box) (d : ℕ) :
    (leafBoxes R B d).length = 2 ^ d := by
  induction d generalizing B with
  | zero => simp [leafBoxes]
  | succ d ih =>
      simp only [leafBoxes, List.length_append, ih]
      rw [pow_succ]
      omega

/-- **Adaptive tree-size bound (leg (i)).**  The adaptive leaf list has length
at most `2^d`, for EVERY oracle — early closing can only shrink the tree. -/
theorem adaptive_length_le (closes : Box → Bool) (d : ℕ) (B : Box) :
    (adaptiveLeaves R closes d B).length ≤ 2 ^ d := by
  induction d generalizing B with
  | zero => simp [adaptiveLeaves]
  | succ d ih =>
      by_cases h : closes B = true
      · simp only [adaptiveLeaves, if_pos h, List.length_singleton]
        have hp : 0 < 2 ^ (d + 1) := by positivity
        omega
      · simp only [adaptiveLeaves, if_neg h, List.length_append]
        have h1 := ih (R.split B).1
        have h2 := ih (R.split B).2
        rw [pow_succ]
        omega

/-- The sealed phrasing "never worse than `Complete.leafBoxes`", literal. -/
theorem adaptive_length_le_leafBoxes (closes : Box → Bool) (d : ℕ) (B : Box) :
    (adaptiveLeaves R closes d B).length ≤ (leafBoxes R B d).length := by
  rw [leafBoxes_length]
  exact adaptive_length_le R closes d B

/-- Reconciliation: with the never-closing oracle, the adaptive tree IS the
uniform tree — `adaptiveLeaves` strictly generalises `leafBoxes`. -/
theorem adaptiveLeaves_false_eq_leafBoxes (d : ℕ) (B : Box) :
    adaptiveLeaves R (fun _ => false) d B = leafBoxes R B d := by
  induction d generalizing B with
  | zero => rfl
  | succ d ih => simp [adaptiveLeaves, leafBoxes, ih]

/-! ## 3. Covering: the adaptive leaves cover the root box — the `R.cover` case
split of `mem_leaf_of_mem`, with one extra if-split for the early-closed node. -/

/-- **Covering (leg (i), "sub-cover").**  Every point of `B` lies in some
adaptive leaf. -/
theorem adaptive_mem_leaf (closes : Box → Bool) (d : ℕ) (B : Box) :
    ∀ s, R.mem B s → ∃ C ∈ adaptiveLeaves R closes d B, R.mem C s := by
  induction d generalizing B with
  | zero =>
      intro s hs
      exact ⟨B, by simp [adaptiveLeaves], hs⟩
  | succ d ih =>
      intro s hs
      by_cases h : closes B = true
      · exact ⟨B, by simp [adaptiveLeaves, h], hs⟩
      · rcases R.cover B s hs with hL | hR
        · obtain ⟨C, hCmem, hCs⟩ := ih (R.split B).1 s hL
          exact ⟨C, by
            simp only [adaptiveLeaves, if_neg h, List.mem_append]
            exact Or.inl hCmem, hCs⟩
        · obtain ⟨C, hCmem, hCs⟩ := ih (R.split B).2 s hR
          exact ⟨C, by
            simp only [adaptiveLeaves, if_neg h, List.mem_append]
            exact Or.inr hCmem, hCs⟩

/-! ## 4. The per-leaf dichotomy: closed, or full-depth with inherited
diam/trueMin — the adaptive twin of `leaf_diam_le` + `leaf_trueMin_ge`.

An early-closed adaptive leaf sits at depth < d, so it does NOT satisfy the
depth-`d` diameter bound — but it does not need to: it is closed.  A surviving
leaf reached fuel 0 through d unclosed splits, so it inherits exactly what a
uniform depth-`d` leaf inherits. -/

/-- Every adaptive leaf is either oracle-closed, or a full-depth leaf carrying
the `leaf_diam_le`/`leaf_trueMin_ge` inheritance. -/
theorem adaptive_leaf_closes_or_deep (closes : Box → Bool) (d : ℕ) (B : Box) :
    ∀ C ∈ adaptiveLeaves R closes d B,
      closes C = true ∨
        (R.diam C ≤ R.diam B / 2 ^ d ∧ R.trueMin B ≤ R.trueMin C) := by
  induction d generalizing B with
  | zero =>
      intro C hC
      simp only [adaptiveLeaves, List.mem_singleton] at hC
      subst hC
      exact Or.inr ⟨by simp, le_refl _⟩
  | succ d ih =>
      intro C hC
      by_cases h : closes B = true
      · simp only [adaptiveLeaves, if_pos h, List.mem_singleton] at hC
        subst hC
        exact Or.inl h
      · simp only [adaptiveLeaves, if_neg h, List.mem_append] at hC
        have hpos : (0 : ℝ) < 2 ^ d := by positivity
        rcases hC with hC | hC
        · rcases ih (R.split B).1 C hC with hcl | ⟨hdiam, hmin⟩
          · exact Or.inl hcl
          · refine Or.inr ⟨?_, le_trans (R.trueMin_mono B).1 hmin⟩
            have h2 := (R.diam_contract B).1
            have hstep : R.diam C ≤ (R.diam B / 2) / 2 ^ d :=
              le_trans hdiam (by
                apply div_le_div_of_nonneg_right h2 (le_of_lt hpos))
            calc R.diam C ≤ (R.diam B / 2) / 2 ^ d := hstep
              _ = R.diam B / 2 ^ (d + 1) := by ring
        · rcases ih (R.split B).2 C hC with hcl | ⟨hdiam, hmin⟩
          · exact Or.inl hcl
          · refine Or.inr ⟨?_, le_trans (R.trueMin_mono B).2 hmin⟩
            have h2 := (R.diam_contract B).2
            have hstep : R.diam C ≤ (R.diam B / 2) / 2 ^ d :=
              le_trans hdiam (by
                apply div_le_div_of_nonneg_right h2 (le_of_lt hpos))
            calc R.diam C ≤ (R.diam B / 2) / 2 ^ d := hstep
              _ = R.diam B / 2 ^ (d + 1) := by ring

/-! ## 5. Adaptive completeness — leg (ii) -/

/-- **Adaptive decisive depth.**  With a complete oracle and the same δ-margin
hypothesis as `Complete.complete`, at the Archimedean depth EVERY adaptive leaf
is oracle-closed: early-closed leaves by definition, full-depth leaves because
their inherited diameter makes the relaxed bound positive
(`relaxedBound_pos_of_diam_lt`) and the oracle does not miss it. -/
theorem adaptive_exists_decisive_depth (closes : Box → Bool)
    (hc : OracleComplete R closes) (B : Box) {δ : ℝ} (hδ : 0 < δ)
    (hmin : δ ≤ R.trueMin B) :
    ∃ d : ℕ, ∀ C ∈ adaptiveLeaves R closes d B, closes C = true := by
  -- pick d with 2^d > L·diam₀/δ (same Archimedean witness as
  -- `exists_decisive_depth`; re-run rather than invoked — see header delta)
  obtain ⟨d, hd⟩ := pow_unbounded_of_one_lt (R.L * R.diam B / δ) (by norm_num : (1:ℝ) < 2)
  refine ⟨d, ?_⟩
  intro C hC
  rcases adaptive_leaf_closes_or_deep R closes d B C hC with hcl | ⟨hdiamC, hminBC⟩
  · exact hcl
  · have hpow : (0:ℝ) < 2 ^ d := by positivity
    have hminC : δ ≤ R.trueMin C := le_trans hmin hminBC
    have hkey : R.L * R.diam C < δ := by
      have hLdiam : R.L * R.diam C ≤ R.L * (R.diam B / 2 ^ d) :=
        mul_le_mul_of_nonneg_left hdiamC R.L_nonneg
      rw [div_lt_iff₀ hδ] at hd        -- hd : L·diam B < 2^d * δ
      have : R.L * (R.diam B / 2 ^ d) < δ := by
        rw [mul_div_assoc', div_lt_iff₀ hpow]
        nlinarith
      linarith
    exact hc C (relaxedBound_pos_of_diam_lt R hminC hkey)

/-- **Adaptive covering + composition** — the adaptive twin of
`box_safe_of_leaves`: ONE uniform per-leaf obligation (`closes C = true`, the
same certificate kind at every leaf, early-closed or full-depth) composes into
whole-box safety through `adaptive_mem_leaf` + `OracleSound` + `R.decides`. -/
theorem adaptive_box_safe_of_leaves (closes : Box → Bool)
    (hs : OracleSound R closes) (d : ℕ) (B : Box)
    (hleaf : ∀ C ∈ adaptiveLeaves R closes d B, closes C = true) :
    ∀ s, R.mem B s → R.safe s := by
  intro s hms
  obtain ⟨C, hCmem, hCs⟩ := adaptive_mem_leaf R closes d B s hms
  exact R.decides C (hs C (hleaf C hCmem)) s hCs

/-- **ADAPTIVE COMPLETENESS (leg (ii))** — under the SAME δ-margin hypothesis as
`Complete.complete`, with a sound and complete certificate oracle, there is a
finite depth at which the adaptive tree has ALL leaves oracle-closed, at most
`2^d` of them, and the root box is decided safe through the same covering
composition the uniform tree uses. -/
theorem adaptive_complete (closes : Box → Bool)
    (hs : OracleSound R closes) (hc : OracleComplete R closes)
    (B : Box) {δ : ℝ} (hδ : 0 < δ) (hmin : δ ≤ R.trueMin B) :
    ∃ d : ℕ,
      (∀ C ∈ adaptiveLeaves R closes d B, closes C = true) ∧
      (adaptiveLeaves R closes d B).length ≤ 2 ^ d ∧
      (∀ s, R.mem B s → R.safe s) := by
  obtain ⟨d, hclose⟩ := adaptive_exists_decisive_depth R closes hc B hδ hmin
  exact ⟨d, hclose, adaptive_length_le R closes d B,
    adaptive_box_safe_of_leaves R closes hs d B hclose⟩

/-! ## 6. The exact Δdomains identity — leg (iii)

`prunedCount` counts, node by node, the uniform-tree leaves an early close
saves: a node closed with remaining fuel `d+1` replaces its `2^(d+1)`-leaf
subtree by ONE leaf, saving `2^(d+1) − 1`.  The subtraction in the definition
is exact (`1 ≤ 2^(d+1)`); the IDENTITY is additive, exactly as sealed. -/

/-- Saved-leaf count of the adaptive tree (the sealed
`Σ_{early-closed node at depth k} (2^(d−k) − 1)`, computed recursively). -/
def prunedCount (closes : Box → Bool) : ℕ → Box → ℕ
  | 0, _ => 0
  | d + 1, B =>
      if closes B then 2 ^ (d + 1) - 1
      else prunedCount closes d (R.split B).1 + prunedCount closes d (R.split B).2

/-- Reconciliation: the never-closing oracle prunes nothing — Δdomains = 0. -/
theorem prunedCount_false (d : ℕ) (B : Box) :
    prunedCount R (fun _ => false) d B = 0 := by
  induction d generalizing B with
  | zero => rfl
  | succ d ih => simp [prunedCount, ih]

/-- **EXACT Δdomains IDENTITY (leg (iii)).**  Adaptive leaves + pruned leaves
= `2^d`, the uniform leaf count — for EVERY oracle, EVERY box, EVERY fuel.
Δdomains (the program's only sanctioned metric) is a kernel-checked identity:
the closed node at fuel `d+1` contributes `1 + (2^(d+1) − 1)`; the open node
splits `2^d + 2^d`. -/
theorem delta_domains_exact (closes : Box → Bool) (d : ℕ) (B : Box) :
    (adaptiveLeaves R closes d B).length + prunedCount R closes d B = 2 ^ d := by
  induction d generalizing B with
  | zero => simp [adaptiveLeaves, prunedCount]
  | succ d ih =>
      by_cases h : closes B = true
      · simp only [adaptiveLeaves, prunedCount, if_pos h, List.length_singleton]
        have hp : 0 < 2 ^ (d + 1) := by positivity
        omega
      · simp only [adaptiveLeaves, prunedCount, if_neg h, List.length_append]
        have h1 := ih (R.split B).1
        have h2 := ih (R.split B).2
        rw [pow_succ]
        omega

end Complete

/-! ## 7. CONCRETE INSTANCE — the oracle on the real IBP relaxation

`CompleteIBP.ibpRelaxation` is the fully-discharged `Relaxation` of the real
1→2→1 ReLU net on [0,2].  The certificate oracle is the canonical one: accept
exactly when the IBP relaxed bound is strictly positive.  It is sound AND
complete BY CONSTRUCTION (classical `decide`), the oracle discipline of
`BabProof.checkLeafCert` at this abstraction level.  The firing is non-vacuous:
the oracle genuinely rejects the root box (IBP is loose there), so the adaptive
tree really splits, and at fuel 2 the saving is EXACTLY 2 domains. -/

namespace CompleteIBP

/-- The concrete certificate oracle: accept a box iff its IBP relaxed bound is
strictly positive (classically decidable; `noncomputable` like the relaxation
itself — this is a PROOF-side oracle, not a runtime claim). -/
noncomputable def ibpCloses (B : Box) : Bool :=
  @decide (0 < relaxedBound B) (Classical.propDecidable _)

/-- The oracle is SOUND: it only accepts positively-bounded boxes. -/
theorem ibpCloses_sound : Complete.OracleSound ibpRelaxation ibpCloses := by
  intro B h
  unfold ibpCloses at h
  exact of_decide_eq_true h

/-- The oracle is COMPLETE: it accepts every positively-bounded box. -/
theorem ibpCloses_complete : Complete.OracleComplete ibpRelaxation ibpCloses := by
  intro B h
  unfold ibpCloses
  exact decide_eq_true h

/-- The oracle REJECTS the root box `[0,2]` (IBP returns exactly `0` there,
`relaxedBound_root_zero`) — the adaptive tree genuinely splits at the root. -/
theorem ibpCloses_root_false : ibpCloses ((0:ℝ), 2) = false := by
  unfold ibpCloses
  exact decide_eq_false (by rw [relaxedBound_root_zero]; exact lt_irrefl 0)

/-- The oracle accepts the left depth-1 child `[0,1]` (`relaxedBound_left`). -/
theorem ibpCloses_left : ibpCloses ((0:ℝ), 1) = true := by
  unfold ibpCloses
  exact decide_eq_true relaxedBound_left

/-- The oracle accepts the right depth-1 child `[1,2]` (`relaxedBound_right`). -/
theorem ibpCloses_right : ibpCloses ((1:ℝ), 2) = true := by
  unfold ibpCloses
  exact decide_eq_true relaxedBound_right

/-- **Adaptive completeness FIRES on the concrete net** — δ = 1, the same
margin `Complete.complete` uses in `ibp_complete`. -/
theorem ibp_adaptive_complete :
    ∃ d : ℕ,
      (∀ C ∈ Complete.adaptiveLeaves ibpRelaxation ibpCloses d ((0:ℝ), 2),
        ibpCloses C = true) ∧
      (Complete.adaptiveLeaves ibpRelaxation ibpCloses d ((0:ℝ), 2)).length ≤ 2 ^ d ∧
      (∀ s, ibpRelaxation.mem ((0:ℝ), 2) s → ibpRelaxation.safe s) :=
  Complete.adaptive_complete ibpRelaxation ibpCloses ibpCloses_sound
    ibpCloses_complete ((0:ℝ), 2) (by norm_num) margin_pos

/-- **The adaptive tree at fuel 2, computed exactly**: the root splits (oracle
rejects), both depth-1 children close — the leaf list is exactly
`[[0,1], [1,2]]`.  The uniform fuel-2 tree has 4 leaves. -/
theorem ibp_adaptiveLeaves_two :
    Complete.adaptiveLeaves ibpRelaxation ibpCloses 2 ((0:ℝ), 2)
      = [((0:ℝ), 1), ((1:ℝ), 2)] := by
  simp [Complete.adaptiveLeaves, ibpRelaxation, split,
    ibpCloses_root_false, ibpCloses_left, ibpCloses_right]

/-- **Δdomains = 2, exactly, kernel-checked**: at fuel 2 the adaptive tree
prunes exactly 2 of the 4 uniform domains (2 leaves + 2 pruned = 2²) — the
identity `delta_domains_exact` instantiated and evaluated on the real net. -/
theorem ibp_delta_domains_two :
    Complete.prunedCount ibpRelaxation ibpCloses 2 ((0:ℝ), 2) = 2 := by
  have h := Complete.delta_domains_exact ibpRelaxation ibpCloses 2 ((0:ℝ), 2)
  rw [ibp_adaptiveLeaves_two] at h
  norm_num at h
  omega

end CompleteIBP

/-! ## Trust-base check — every theorem must reduce to the standard logical
axioms only (`propext`, `Classical.choice`, `Quot.sound`), with NO `sorryAx`
and NO `native_decide` (`Lean.ofReduceBool`). -/

#print axioms Complete.leafBoxes_length
#print axioms Complete.adaptive_length_le
#print axioms Complete.adaptive_length_le_leafBoxes
#print axioms Complete.adaptiveLeaves_false_eq_leafBoxes
#print axioms Complete.adaptive_mem_leaf
#print axioms Complete.adaptive_leaf_closes_or_deep
#print axioms Complete.adaptive_exists_decisive_depth
#print axioms Complete.adaptive_box_safe_of_leaves
#print axioms Complete.adaptive_complete
#print axioms Complete.prunedCount_false
#print axioms Complete.delta_domains_exact
#print axioms CompleteIBP.ibpCloses_sound
#print axioms CompleteIBP.ibpCloses_complete
#print axioms CompleteIBP.ibpCloses_root_false
#print axioms CompleteIBP.ibp_adaptive_complete
#print axioms CompleteIBP.ibp_adaptiveLeaves_two
#print axioms CompleteIBP.ibp_delta_domains_two

end Crownproof
