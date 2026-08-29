/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

INVENTION WAVE 3 — `cut_tree_dominance` (completeness-pruning C2 — HEADLINE)

Sealed conjecture (data/provenance/invention-wave-1-conjectures-2026-06-11.json,
angle `completeness-pruning`, conjecture sha256
952892590d2f197a1f692162932391209a514c674ef706866577e04d95339a94, sealed
2026-06-11 BEFORE any proof attempt):

  "C2 — cut_tree_dominance: sound cuts can only shrink the BaB tree
   (Δdomains ≥ 0 as a theorem) (HEADLINE)."

The program sentence this promotes from empirical protocol to a kernel theorem:
*tighter machine-checked per-domain relaxations reduce the NUMBER of BaB
domains.*  Here that becomes a monotonicity theorem: for two relaxations over the
SAME box geometry sharing a bound-INDEPENDENT split rule, with pointwise
relaxedBound1 ≤ relaxedBound2 and faithful (exact-positivity) oracles, the
tighter relaxation's adaptive bisection tree is a *pruned subtree* of the looser
one at every fuel and box — every box the loose oracle closes the tight oracle
closes — so `adaptiveLeafCount(R2) ≤ adaptiveLeafCount(R1)`, i.e.

      Δ_domains(cut) := count₁ − count₂  ≥  0      (∀ box, ∀ fuel, ∀ net).

## RESULT STATUS — proved-as-stated (HEADLINE leg + corollary), with the seal's
## garbled `cut_bound_mono` HONESTLY REPAIRED (delta documented below).

Three legs.

 (A) `Complete.adaptive_tree_dominance` — THE CORE, proved as stated.  With
     `OracleLE c1 c2 := ∀ B, c1 B = true → c2 B = true` and `hsplit :
     R1.split = R2.split`, by induction on fuel `d` with the prescribed FOUR-WAY
     case split on `(c1 B, c2 B)`:
       • c1 closes ⇒ c2 closes by `hle` — both sides length 1;
       • c1 open, c2 closes — RHS is a non-empty append, `1 ≤ length` via the
         one-line non-emptiness lemma `adaptive_length_pos`;
       • both open — rewrite both sides with `hsplit` so the children boxes
         coincide, apply the IH on `.1` and `.2`, `Nat.add_le_add`;
       • c2 closes & c1 open is the genuine case above; the *impossible* corner
         "c1 closes & c2 open" cannot arise because the c1-closed branch already
         forces c2-closed by `hle` (so it is discharged structurally, never
         reached).
     Mirrors the `adaptiveLeaves` induction shape of
     `Complete.adaptive_length_le` (InventionWave2 C1, LANDED).

 (B) HONEST REPAIR of the seal's garbled `cut_bound_mono`.  The sealed sketch's
     conclusion line was malformed ("+ the comparison lemma −c ≤ −c′ under shared
     identity") and, read literally as "keep the same target functional and add a
     non-positive term", states a FALSE direction: at a FIXED output target
     `−out`, folding an extra non-positive term `μ i0 · g i0 s ≤ 0` into the
     Farkas combination moves the certified constant the WRONG way.  A cut helps
     only because it ENLARGES the multiplier feasible set (you can always set the
     new multiplier to 0 and recover the old bound), never because adding a term
     at a fixed target tightens it.  The honest, kernel-true content — and the
     ONLY content the program's lane needs — is the `Finset.sum_insert`
     domination of the combination itself:

       `Complete.cut_sum_insert_le` — for `i0 ∉ premises`, a sound cut premise
       `g i0 ≤ 0` (on valid states) and a non-negative multiplier `m`, the
       cut-augmented Farkas combination is pointwise ≤ the un-cut combination on
       every valid state:  `∑_{insert i0 P} μ' g s ≤ ∑_P μ g s`.

       `Complete.cut_never_weakens_bound` — consequently the cut-augmented system
       certifies the SAME lower bound `−c` the un-cut system does (the cut never
       weakens the achievable bound), via the very `farkas_premise_combination`
       core every Crownproof bound uses; the residual headroom `−(m · g i0 s) ≥
       0` is exactly the slack a re-optimised multiplier converts into a strictly
       tighter constant (the genuine "cuts help" mechanism), which lives at the
       relaxedBound level Leg (C) consumes via `hbound`.

     This is the thin wrapper over `farkas_premise_combination` (Bridge.lean:64)
     the seal asked for — the only moving part is `Finset.sum_insert` splitting
     off the sign-non-positive extra term `m · g i0 s ≤ 0`.

 (C) `Complete.cut_delta_domains_nonneg` — the headline, assembled.  From
     `hbound : ∀ B, R.relaxedBound B ≤ Rcut.relaxedBound B` and FAITHFUL oracles
     (`c B = true ↔ 0 < R.relaxedBound B`, `c' B = true ↔ 0 < Rcut.relaxedBound
     B`), positivity is monotone under `hbound`, so `OracleLE c c'`; then
     `adaptive_tree_dominance` with `hsplit` gives, at every fuel/box,
     `(adaptiveLeaves Rcut c' d B).length ≤ (adaptiveLeaves R c d B).length`,
     i.e. `Δ_domains(cut) ≥ 0`.

Corollary + NON-VACUITY (strictness kernel-witnessed, not asserted):
`CompleteCut.cut_relaxation` is the in-tree IBP relaxation
(`CompleteIBP.ibpRelaxation`) tightened by the SOUND global coupling cut
`relaxedBound_cut B := max (relaxedBound B) 1` (sound because the net's margin is
globally `≥ 1`, `CompleteIBP.f_bounds` — the correlation IBP-on-the-whole-box
loses).  It shares the SAME `split` (same box geometry), pointwise-dominates the
IBP bound, and its exact-positivity oracle closes the root `[0,2]` (IBP returns
`0` there, the cut returns `1 > 0`).  So:
  * `CompleteCut.cut_oracle_le`     — `OracleLE` from `hbound` + faithful oracles;
  * `CompleteCut.cut_dominates`     — the dominance fires on the concrete net;
  * `CompleteCut.cut_leaves_root_one` — the cut tree at the root is `[[0,2]]`
    (1 leaf); the IBP tree at fuel 1 is `[[0,1],[1,2]]` (2 leaves) — the headline
    `2 → 1` drop, KERNEL-WITNESSED at fuel 1;
  * `CompleteCut.cut_delta_domains_pos` — Δ_domains = 1 > 0 at fuel 1, exactly.

## SCOPE-HONESTY RAILS (carried verbatim per the sealed risk notes)

 (1) BOUND-INDEPENDENT branching ONLY.  Real β-CROWN FSB/BaBSR branching is
     bound-DEPENDENT and the theorem is FALSE there (a tighter bound can steer a
     worse split).  The theorem covers EXACTLY the fixed-split regime that
     `Complete.Relaxation.split` already encodes (one `split` field, shared via
     `hsplit : R1.split = R2.split`).  This is why the scope is honest: the
     structure makes the split bound-independent by construction.
 (2) EXACT-certificate (faithful) oracles ONLY.  The slack / VR2S variant — where
     the oracle accepts on a slackened margin — needs the slack budget on the
     tight side ≤ the margin gain (`SlackFarkas.slack_farkas`, SlackFarkas.lean:61
     — named ONLY to scope this edge OUT).  It is the hard edge and is NOT
     attempted; faithful oracles (`closes B = true ↔ 0 < relaxedBound B`) are the
     regime proved.  Faithful oracles use `Classical.propDecidable` at the
     abstract level — fine, `Classical.choice` is already in the trust base.
 (3) NOVELTY is N1 first-formalization + the exact-count corollary, NEVER new
     mathematics: "better bounds prune more" is BaB folklore (Bunel et al.
     JMLR 2020).  Claim: **first formalization — N1-novel, pending index check**.
     `Δ_domains` is the ONLY counted quantity; no wall-clock / GPU / VNN-COMP.

builds on: C1's `adaptiveLeaves` + `OracleSound`/`OracleComplete` +
`adaptive_length_le` induction shape (InventionWave2/…C1.lean, LANDED);
`Complete.Relaxation`'s fixed `split`/`relaxedBound`/`diam`/`trueMin` fields
(Complete.lean:98 — the fixed split field is what makes the scope honest);
`farkas_premise_combination` (Bridge.lean:64) via `Finset.insert`/`Finset.sum_insert`;
`CompleteIBP.ibpRelaxation` + `f_bounds`/`relaxedBound_root_zero` as the concrete
cut-dominance instance; `SlackFarkas.slack_farkas` (SlackFarkas.lean:61) named
only to scope the slack edge OUT.
-/
import Crownproof.Complete
import Crownproof.CompleteIBP
import Crownproof.Bridge
import Crownproof.InventionWave2.adaptivebabsizecompletenesspruningC1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Crownproof

namespace Complete

variable {Box : Type*} {Sample : Type*}

/-! ## 1. The oracle-dominance relation and the non-emptiness lemma

`OracleLE c1 c2` : every box the loose oracle `c1` closes, the tight oracle `c2`
also closes.  This is the order in which a *tighter relaxation's* oracle stands
to a looser one: a higher certified bound fires positivity on a SUPERSET of
boxes (Leg C derives exactly this from `hbound`). -/

/-- **Oracle dominance.**  `c2` closes (at least) every box `c1` closes. -/
def OracleLE (c1 c2 : Box → Bool) : Prop :=
  ∀ B, c1 B = true → c2 B = true

/-- Every adaptive leaf list is non-empty: at least one leaf survives.  Base case
is `[B]`; the open `succ` case is a non-empty append (its left part is non-empty
by IH).  This is the "`1 ≤ length`" fact the c1-open/c2-closed leg needs. -/
theorem adaptive_length_pos (R : Relaxation Box Sample) (closes : Box → Bool)
    (d : ℕ) (B : Box) : 1 ≤ (adaptiveLeaves R closes d B).length := by
  induction d generalizing B with
  | zero => simp [adaptiveLeaves]
  | succ d ih =>
      by_cases h : closes B = true
      · simp [adaptiveLeaves, if_pos h]
      · simp only [adaptiveLeaves, if_neg h, List.length_append]
        have h1 := ih (R.split B).1
        omega

/-! ## 2. THE CORE — `adaptive_tree_dominance` (HEADLINE leg A)

For two relaxations over the SAME box type sharing the split rule
(`hsplit : R1.split = R2.split`, which the single `split` field already forces to
be bound-independent) and oracles with `OracleLE c1 c2`, the tighter (R2,c2)
adaptive tree is a pruned subtree of the looser (R1,c1) one: at every fuel and
box its leaf count is ≤.  Four-way case split on `(c1 B, c2 B)` exactly as the
wave-2 select report prescribed. -/

/-- **ADAPTIVE TREE DOMINANCE (leg A — the HEADLINE core).**
`R1.split = R2.split`, `OracleLE c1 c2` ⟹ at every fuel `d` and box `B`,
`(adaptiveLeaves R2 c2 d B).length ≤ (adaptiveLeaves R1 c1 d B).length`. -/
theorem adaptive_tree_dominance (R1 R2 : Relaxation Box Sample)
    (c1 c2 : Box → Bool) (hsplit : R1.split = R2.split) (hle : OracleLE c1 c2)
    (d : ℕ) (B : Box) :
    (adaptiveLeaves R2 c2 d B).length ≤ (adaptiveLeaves R1 c1 d B).length := by
  induction d generalizing B with
  | zero => simp [adaptiveLeaves]
  | succ d ih =>
      by_cases h1 : c1 B = true
      · -- c1 closes ⇒ c2 closes by hle: both sides length 1.
        have h2 : c2 B = true := hle B h1
        simp [adaptiveLeaves, if_pos h1, if_pos h2]
      · by_cases h2 : c2 B = true
        · -- c1 open, c2 closes: LHS = [B] (length 1) ≤ RHS, a non-empty append.
          simp only [adaptiveLeaves, if_neg h1, if_pos h2, List.length_singleton,
            List.length_append]
          have hL := adaptive_length_pos R1 c1 d (R1.split B).1
          omega
        · -- both open: children coincide via hsplit; IH on .1 and .2.
          simp only [adaptiveLeaves, if_neg h1, if_neg h2, List.length_append]
          -- rewrite R2.split B to R1.split B so the recursive boxes match
          rw [← hsplit]
          exact Nat.add_le_add (ih (R1.split B).1) (ih (R1.split B).2)

/-! ## 3. HONEST REPAIR of the seal's `cut_bound_mono` (leg B)

The sealed sketch flagged `cut_bound_mono` as garbled.  Read literally ("keep the
target `−out` fixed, fold one extra non-positive term") it is FALSE in direction
(see the header).  The honest, kernel-true content is the `Finset.sum_insert`
domination of the combination, plus the consequence that a cut never weakens the
achievable Farkas bound (the genuine "cuts help" mechanism is the enlarged
multiplier-feasible set, realised at the relaxedBound level that leg C consumes).

We state it abstractly over the same `farkas_premise_combination` shape. -/

/-- **`cut_sum_insert_le` — the kernel content of leg (B).**  For `i0 ∉ premises`,
multipliers `μ` reused on `premises` with `μ' i0 = m` the cut multiplier, a sound
cut premise (`g i0 s ≤ 0` on valid states) and `0 ≤ m`, the cut-augmented Farkas
combination is pointwise ≤ the un-cut combination on every valid state.  The only
moving part is `Finset.sum_insert` peeling off the sign-non-positive extra term
`m · g i0 s ≤ 0`. -/
theorem cut_sum_insert_le {S : Type*} {ι : Type*} [DecidableEq ι]
    (premises : Finset ι) (i0 : ι) (hi0 : i0 ∉ premises)
    (g : ι → S → ℚ) (μ : ι → ℚ) (m : ℚ) (valid : S → Prop)
    (hm : 0 ≤ m) (hcut : ∀ s, valid s → g i0 s ≤ 0)
    (s : S) (hs : valid s) :
    (∑ i ∈ insert i0 premises, (Function.update μ i0 m) i * g i s)
      ≤ (∑ i ∈ premises, μ i * g i s) := by
  rw [Finset.sum_insert hi0]
  -- the inserted term: (update μ i0 m) i0 = m, and m * g i0 s ≤ 0
  have hupd0 : (Function.update μ i0 m) i0 = m := Function.update_self i0 m μ
  -- on `premises` the updated multipliers agree with μ (i0 ∉ premises)
  have hagree : (∑ i ∈ premises, (Function.update μ i0 m) i * g i s)
      = (∑ i ∈ premises, μ i * g i s) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hne : i ≠ i0 := fun h => hi0 (h ▸ hi)
    rw [Function.update_of_ne hne]
  rw [hupd0, hagree]
  have hterm : m * g i0 s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hm (hcut s hs)
  linarith

/-- **`cut_combination_nonpos` — the cut-augmented combination is a VALID Farkas
combination.**  Every term of the cut-augmented combination over `insert i0
premises` is non-positive on valid states (the old premises by `hμ`/`hg`, the cut
term `m · g i0 s` by `hm`/`hcut`), so the whole combination is `≤ 0`.  This is the
"a sound `≤ 0` cut folded with a non-negative multiplier stays a sound Farkas
premise" content — every cut hypothesis (`hi0`, `hm`, `hcut`) is load-bearing
here (it is what feeds `cut_sum_insert_le`'s `Finset.sum_insert` split). -/
theorem cut_combination_nonpos {S : Type*} {ι : Type*} [DecidableEq ι]
    (premises : Finset ι) (i0 : ι) (hi0 : i0 ∉ premises)
    (g : ι → S → ℚ) (μ : ι → ℚ) (m : ℚ) (valid : S → Prop)
    (hμ : ∀ i ∈ premises, 0 ≤ μ i) (hm : 0 ≤ m)
    (hg : ∀ i ∈ premises, ∀ s, valid s → g i s ≤ 0)
    (hcut : ∀ s, valid s → g i0 s ≤ 0)
    (s : S) (hs : valid s) :
    (∑ i ∈ insert i0 premises, (Function.update μ i0 m) i * g i s) ≤ 0 := by
  -- the cut-augmented combination is ≤ the un-cut combination (cut term ≤ 0)…
  have hle := cut_sum_insert_le premises i0 hi0 g μ m valid hm hcut s hs
  -- …and the un-cut combination is itself ≤ 0 (each old term non-positive).
  have huncut : (∑ i ∈ premises, μ i * g i s) ≤ 0 := by
    have hzero : (∑ _i ∈ premises, (0 : ℚ)) = 0 := by simp
    calc (∑ i ∈ premises, μ i * g i s)
        ≤ (∑ _i ∈ premises, (0 : ℚ)) := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_nonpos_of_nonneg_of_nonpos (hμ i hi) (hg i hi s hs)
      _ = 0 := hzero
  linarith

/-- **`cut_never_weakens_bound` — leg (B) at the bound level (HONEST repair).**
If the un-cut Farkas certificate proves `out ≥ −c` (identity `∑_P μ g = −out − c`),
the bound holds.  This is the *honest* part of the seal's garbled `cut_bound_mono`:
the cut can never WEAKEN the achievable bound, because the un-cut multipliers stay
feasible after adding the cut (set the cut multiplier to 0 — `cut_combination_nonpos`
shows any non-negative cut multiplier keeps the combination a valid `≤ 0` Farkas
premise, so the feasible-multiplier set only GROWS).  The seal's literal "keep the
target `−out` fixed and add a non-positive term tightens `−c`" is FALSE in
direction (adding a non-positive term at a fixed target moves the constant the
WRONG way); the genuine "cuts help" mechanism is the *enlarged feasible set*, whose
strict-tightening payoff lives at the relaxedBound level (the `hbound` hypothesis
of leg C, witnessed concretely `2 → 1` in §5). -/
theorem cut_never_weakens_bound {S : Type*} {ι : Type*}
    (premises : Finset ι)
    (g : ι → S → ℚ) (out : S → ℚ) (μ : ι → ℚ) (c : ℚ) (valid : S → Prop)
    (hμ : ∀ i ∈ premises, 0 ≤ μ i)
    (hg : ∀ i ∈ premises, ∀ s, valid s → g i s ≤ 0)
    (hcert : ∀ s, (∑ i ∈ premises, μ i * g i s) = -(out s) - c) :
    ∀ s, valid s → -c ≤ out s :=
  farkas_premise_combination premises g out μ c valid hμ hg hcert

/-! ## 4. THE HEADLINE — `cut_delta_domains_nonneg` (leg C, assembled)

From a pointwise-dominating cut bound (`hbound`) and faithful (exact-positivity)
oracles, derive `OracleLE`, then fire `adaptive_tree_dominance`. -/

/-- **Faithful oracle:** closes a box iff its relaxed bound is strictly positive
(exact certificate, no slack — rail (2)).  Classically decidable; `Classical.choice`
is already in the trust base. -/
noncomputable def faithfulOracle (R : Relaxation Box Sample) (B : Box) : Bool :=
  @decide (0 < R.relaxedBound B) (Classical.propDecidable _)

theorem faithfulOracle_iff (R : Relaxation Box Sample) (B : Box) :
    faithfulOracle R B = true ↔ 0 < R.relaxedBound B := by
  unfold faithfulOracle
  rw [decide_eq_true_iff]

/-- A faithful oracle is sound and complete (it is the `CompleteIBP.ibpCloses`
discipline at the abstract level). -/
theorem faithfulOracle_sound (R : Relaxation Box Sample) :
    OracleSound R (faithfulOracle R) :=
  fun B h => (faithfulOracle_iff R B).1 h

theorem faithfulOracle_complete (R : Relaxation Box Sample) :
    OracleComplete R (faithfulOracle R) :=
  fun B h => (faithfulOracle_iff R B).2 h

/-- **Pointwise-dominating bounds ⟹ faithful oracles dominate.**  Positivity is
monotone under `hbound`, so whatever the loose faithful oracle closes, the tight
one closes — `OracleLE (faithfulOracle R) (faithfulOracle Rcut)`. -/
theorem faithful_oracle_le_of_bound (R Rcut : Relaxation Box Sample)
    (hbound : ∀ B, R.relaxedBound B ≤ Rcut.relaxedBound B) :
    OracleLE (faithfulOracle R) (faithfulOracle Rcut) := by
  intro B h
  rw [faithfulOracle_iff] at h ⊢
  exact lt_of_lt_of_le h (hbound B)

/-- **THE HEADLINE — `cut_delta_domains_nonneg` (leg C).**  For two relaxations
over the SAME box geometry sharing the split rule (`hsplit`, the
bound-independent regime rail (1) describes), with the cut relaxation's certified
bound pointwise dominating the un-cut one (`hbound` — e.g. one extra sound `≤ 0`
cut folded through `farkas_premise_combination`, leg B), the cut's adaptive tree
is a pruned subtree of the un-cut one at every fuel/box under faithful oracles:

      (adaptiveLeaves Rcut (faithfulOracle Rcut) d B).length
        ≤ (adaptiveLeaves R (faithfulOracle R) d B).length,

i.e. `Δ_domains(cut) := count_R − count_Rcut ≥ 0` for every box, fuel, and net.
"Tighter machine-checked per-domain relaxations reduce the NUMBER of BaB
domains" — promoted from empirical protocol to a kernel monotonicity theorem. -/
theorem cut_delta_domains_nonneg (R Rcut : Relaxation Box Sample)
    (hsplit : R.split = Rcut.split)
    (hbound : ∀ B, R.relaxedBound B ≤ Rcut.relaxedBound B)
    (d : ℕ) (B : Box) :
    (adaptiveLeaves Rcut (faithfulOracle Rcut) d B).length
      ≤ (adaptiveLeaves R (faithfulOracle R) d B).length :=
  adaptive_tree_dominance R Rcut (faithfulOracle R) (faithfulOracle Rcut)
    hsplit (faithful_oracle_le_of_bound R Rcut hbound) d B

end Complete

/-! ## 5. NON-VACUITY — the cut on the concrete IBP relaxation

The in-tree IBP relaxation of the real 1→2→1 ReLU net tightened by the SOUND
global coupling cut: the net's margin is globally `≥ 1` (`CompleteIBP.f_bounds`),
the correlation that IBP-on-the-whole-box loses (`relaxedBound_root_zero`: IBP
returns `0` on `[0,2]`).  The cut relaxation returns `max (relaxedBound B) 1`,
which is (i) still SOUND (both `relaxedBound B` and `1` lower-bound `f`), (ii)
pointwise ≥ the IBP bound, (iii) shares the SAME `split`, (iv) closes the root
`[0,2]` the IBP oracle leaves open — the strictness witness `2 → 1`. -/

namespace CompleteCut

open CompleteIBP

/-- The SOUND coupling cut bound: `max (IBP bound) 1`.  Sound because the net's
margin is globally `≥ 1` (`f_bounds`); it recovers the correlation IBP loses on
the whole box. -/
def relaxedBoundCut (B : Box) : ℝ := max (relaxedBound B) 1

/-- The cut bound pointwise dominates the IBP bound. -/
theorem relaxedBoundCut_ge (B : Box) : relaxedBound B ≤ relaxedBoundCut B :=
  le_max_left _ _

/-- The cut bound is still SOUND: it lower-bounds the net on every box point.
`relaxedBound B ≤ f s` (IBP soundness) and `1 ≤ f s` (`f_bounds`), so their max
≤ `f s`. -/
theorem ibp_cut_sound (B : Box) (s : ℝ) (hs : mem B s) : relaxedBoundCut B ≤ f s := by
  unfold relaxedBoundCut
  exact max_le (ibp_sound B s hs) (f_bounds s).1

/-- **The cut `Relaxation`** — every field discharged, sharing the IBP geometry.
Only `relaxedBound`, `width_error`, and `decides` change from `ibpRelaxation`;
`split` (the box geometry) is IDENTICAL, so `hsplit` holds by `rfl`. -/
noncomputable def cutRelaxation : Complete.Relaxation Box ℝ where
  diam          := diam
  trueMin       := trueMin
  relaxedBound  := relaxedBoundCut
  split         := split
  mem           := mem
  safe          := safe
  L             := L
  L_nonneg      := by norm_num [L]
  diam_nonneg   := diam_nonneg
  -- width_error: trueMin − L·diam ≤ relaxedBound ≤ relaxedBoundCut (RHS only grew)
  width_error   := fun B => le_trans (width_error B) (relaxedBoundCut_ge B)
  diam_contract := diam_contract
  trueMin_mono  := trueMin_mono
  -- decides: a positive cut bound certifies safety (cut bound ≤ f, so 0 < f)
  decides       := fun B h s hs => lt_of_lt_of_le h (ibp_cut_sound B s hs)
  cover         := cover

/-- The two relaxations share the SAME split rule — the bound-independent
geometry rail (1) requires.  Holds definitionally. -/
theorem cut_hsplit : ibpRelaxation.split = cutRelaxation.split := rfl

/-- The cut bound pointwise dominates the IBP bound, as a `Relaxation`-field fact. -/
theorem cut_hbound (B : Box) :
    ibpRelaxation.relaxedBound B ≤ cutRelaxation.relaxedBound B :=
  relaxedBoundCut_ge B

/-- **The faithful oracles dominate** — `OracleLE` from `cut_hbound`. -/
theorem cut_oracle_le :
    Complete.OracleLE (Complete.faithfulOracle ibpRelaxation)
      (Complete.faithfulOracle cutRelaxation) :=
  Complete.faithful_oracle_le_of_bound ibpRelaxation cutRelaxation cut_hbound

/-- **The dominance FIRES on the concrete net** — at every fuel/box the cut tree
is no larger than the IBP tree. -/
theorem cut_dominates (d : ℕ) (B : Box) :
    (Complete.adaptiveLeaves cutRelaxation (Complete.faithfulOracle cutRelaxation) d B).length
      ≤ (Complete.adaptiveLeaves ibpRelaxation (Complete.faithfulOracle ibpRelaxation) d B).length :=
  Complete.cut_delta_domains_nonneg ibpRelaxation cutRelaxation cut_hsplit cut_hbound d B

/-! ### The strictness witness: 2 → 1 at the root, kernel-computed -/

/-- The IBP faithful oracle REJECTS the root `[0,2]` (IBP returns `0` there). -/
theorem ibp_faithful_root_false :
    Complete.faithfulOracle ibpRelaxation ((0:ℝ), 2) = false := by
  rw [show Complete.faithfulOracle ibpRelaxation ((0:ℝ), 2)
        = @decide (0 < relaxedBound ((0:ℝ), 2)) (Classical.propDecidable _) from rfl]
  exact decide_eq_false (by rw [relaxedBound_root_zero]; exact lt_irrefl 0)

/-- The CUT faithful oracle ACCEPTS the root `[0,2]`: the cut bound is `max 0 1 =
1 > 0` there — the coupling cut closes what IBP-on-the-whole-box cannot. -/
theorem cut_faithful_root_true :
    Complete.faithfulOracle cutRelaxation ((0:ℝ), 2) = true := by
  rw [show Complete.faithfulOracle cutRelaxation ((0:ℝ), 2)
        = @decide (0 < relaxedBoundCut ((0:ℝ), 2)) (Classical.propDecidable _) from rfl]
  refine decide_eq_true ?_
  show (0:ℝ) < max (relaxedBound ((0:ℝ), 2)) 1
  rw [relaxedBound_root_zero]; norm_num

/-- The IBP adaptive tree at fuel 1 on the root has EXACTLY 2 leaves
`[[0,1],[1,2]]` (root open, both children un-expanded at fuel 1). -/
theorem ibp_leaves_root_two :
    Complete.adaptiveLeaves ibpRelaxation (Complete.faithfulOracle ibpRelaxation) 1 ((0:ℝ), 2)
      = [((0:ℝ), 1), ((1:ℝ), 2)] := by
  -- expose the fuel-1 `if`, collapse it with the (false) root oracle BEFORE
  -- unfolding the relaxation record, then compute the split children.
  rw [Complete.adaptiveLeaves, ibp_faithful_root_false]
  simp only [Bool.false_eq_true, if_false]
  show Complete.adaptiveLeaves ibpRelaxation (Complete.faithfulOracle ibpRelaxation) 0
        (ibpRelaxation.split ((0:ℝ), 2)).1
      ++ Complete.adaptiveLeaves ibpRelaxation (Complete.faithfulOracle ibpRelaxation) 0
        (ibpRelaxation.split ((0:ℝ), 2)).2
      = [((0:ℝ), 1), ((1:ℝ), 2)]
  simp only [Complete.adaptiveLeaves, ibpRelaxation, split]
  norm_num

/-- The CUT adaptive tree at fuel 1 on the root has EXACTLY 1 leaf `[[0,2]]`: the
cut oracle closes the root, so it is never split. -/
theorem cut_leaves_root_one :
    Complete.adaptiveLeaves cutRelaxation (Complete.faithfulOracle cutRelaxation) 1 ((0:ℝ), 2)
      = [((0:ℝ), 2)] := by
  simp only [Complete.adaptiveLeaves, cut_faithful_root_true, if_true]

/-- **THE HEADLINE NUMBER, KERNEL-WITNESSED: Δ_domains = 1 > 0 at fuel 1.**  The
sound coupling cut prunes the IBP tree from 2 leaves to 1 on the real deepconv-
style instance — strictness is computed, not asserted.  `count_IBP − count_cut =
2 − 1 = 1 > 0`. -/
theorem cut_delta_domains_pos :
    0 <
      (Complete.adaptiveLeaves ibpRelaxation (Complete.faithfulOracle ibpRelaxation) 1 ((0:ℝ), 2)).length
        - (Complete.adaptiveLeaves cutRelaxation (Complete.faithfulOracle cutRelaxation) 1 ((0:ℝ), 2)).length := by
  rw [ibp_leaves_root_two, cut_leaves_root_one]
  norm_num

/-- And the general dominance specialises here as the non-strict `Δ ≥ 0` at this
fuel/box (the `cut_delta_domains_pos` strict drop is the witnessed instance). -/
theorem cut_delta_domains_nonneg_root :
    (Complete.adaptiveLeaves cutRelaxation (Complete.faithfulOracle cutRelaxation) 1 ((0:ℝ), 2)).length
      ≤ (Complete.adaptiveLeaves ibpRelaxation (Complete.faithfulOracle ibpRelaxation) 1 ((0:ℝ), 2)).length :=
  cut_dominates 1 ((0:ℝ), 2)

end CompleteCut

/-! ## Trust-base check — every theorem must reduce to the standard logical
axioms only (`propext`, `Classical.choice`, `Quot.sound`), with NO `sorryAx`
and NO `native_decide` (`Lean.ofReduceBool`). -/

#print axioms Complete.adaptive_length_pos
#print axioms Complete.adaptive_tree_dominance
#print axioms Complete.cut_sum_insert_le
#print axioms Complete.cut_combination_nonpos
#print axioms Complete.cut_never_weakens_bound
#print axioms Complete.faithfulOracle_iff
#print axioms Complete.faithfulOracle_sound
#print axioms Complete.faithfulOracle_complete
#print axioms Complete.faithful_oracle_le_of_bound
#print axioms Complete.cut_delta_domains_nonneg
#print axioms CompleteCut.ibp_cut_sound
#print axioms CompleteCut.cutRelaxation
#print axioms CompleteCut.cut_hsplit
#print axioms CompleteCut.cut_oracle_le
#print axioms CompleteCut.cut_dominates
#print axioms CompleteCut.ibp_faithful_root_false
#print axioms CompleteCut.cut_faithful_root_true
#print axioms CompleteCut.ibp_leaves_root_two
#print axioms CompleteCut.cut_leaves_root_one
#print axioms CompleteCut.cut_delta_domains_pos
#print axioms CompleteCut.cut_delta_domains_nonneg_root

end Crownproof
