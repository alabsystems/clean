/-
Copyright 2026 Andrew Yates
SPDX-License-Identifier: Apache-2.0

KERNEL-RUNNABLE *slack-tolerant* integer-pair entailment checker  (Pillar A, W2).

`Crownproof.CertCheckerZ.checkEntailmentZ` is the *exact* kernel-runnable checker:
its integer cross-multiplication test certifies the EXACT Farkas identity
(`combConst ≤ conclConst`, coefficients cancel), reducing to
`Crownproof.farkas_premise_combination`.

This file is its **slack-tolerant twin**.  Following `SlackFarkas.lean`, instead
of the exact bound we admit a *non-negative slack* `σ` charged against a positive
safety margin:

  * the rounded multipliers are `≥ 0` (integer numerators `≥ 0`);
  * every premise is a sound `≤`/`≥`/`=` row of `liftCert`;
  * the derived linear functional equals the conclusion functional
    (coefficients cancel — same integer test as the exact checker);
  * the slack-weakened bound holds:  `combConst ≤ conclConst + σ`  with `0 ≤ σ`;
  * a *headroom* check `σ < margin` decides that the weaker margin still has
    strictly positive room `> σ` left over (this is the slack-vs-margin contract
    of `SlackFarkas`: when the true threshold leaves headroom `> σ`, the slack
    bound still decides the property).

All five checks are **integer cross-multiplication** on `(num, den)` pairs, so the
Boolean checker `checkSlackEntailmentZ` reduces in the Lean kernel by
`decide`/`rfl` — GMP-backed, **NO `native_decide`**.

Soundness (`checkSlackEntailmentZ_sound`) bottoms out in
`Crownproof.slack_farkas`: from the integer acceptance we exhibit exactly the
slack-Farkas data (`g`, `out`, `μ`, `c`, `σ`) over the lifted ℚ certificate and
conclude the slack-weakened margin, plus the strict headroom `σ < margin`.

A concrete tiny leaf (`demoSlackCert`) is closed by `by decide` /
`by native_decide`-free reduction at the bottom, demonstrating kernel-runnability.
-/
import Crownproof.CertCheckerZ
import Crownproof.SlackFarkas
import Mathlib.Tactic.Ring

namespace Crownproof
namespace SlackCertZ

open Crownproof
open Crownproof.CertChecker
open Crownproof.CertCheckerZ

/-! ## 1. The slack certificate: an exact `CertZ` plus an Int-pair slack `σ` and
       an Int-pair headroom `margin`. -/

/-- A slack-tolerant integer-pair entailment certificate: the underlying exact
    integer cert `base`, a non-negative slack `slack`, and a `margin` that the
    slack must undercut (strict headroom). -/
structure SCertZ where
  base   : CertZ
  slack  : QPair
  margin : QPair
deriving Repr

/-! ## 2. The kernel-runnable slack checker. -/

/-- `toQ a < toQ b` with positive denominators ⇔ `a.num*b.den < b.num*a.den`. -/
def ltZ (a b : QPair) : Bool := decide (a.1 * b.2 < b.1 * a.2)

theorem ltZ_sound (a b : QPair) (ha : QPair.wf a) (hb : QPair.wf b) :
    ltZ a b = true → toQ a < toQ b := by
  unfold ltZ QPair.wf toQ at *
  intro h
  rw [decide_eq_true_iff] at h
  have hda : (0 : ℚ) < (a.2 : ℚ) := by exact_mod_cast ha
  have hdb : (0 : ℚ) < (b.2 : ℚ) := by exact_mod_cast hb
  rw [div_lt_div_iff₀ hda hdb]
  have : (a.1 : ℚ) * (b.2 : ℚ) < (b.1 : ℚ) * (a.2 : ℚ) := by exact_mod_cast h
  linarith

/--
**The runnable slack checker.**

Mirrors `checkEntailmentZ` but relaxes the bound check by the slack `σ`:

  * `allDenPos base` and `0 < slack.den`, `0 < margin.den`  (well-formed pairs);
  * `premises.length == multipliers.length`;
  * every multiplier `≥ 0` (`nonnegZ`);
  * the conclusion normalizes to a single `≤`-row and its coefficient functional
    cancels the combined coefficient functional (the `isZeroZ` test on the
    collapsed diff map — IDENTICAL to the exact checker);
  * `nonnegZ slack`  (the slack `σ ≥ 0`);
  * `leZ (combConstZ pairs) (addZ conclConst slack)`  (the slack-weakened bound
    `combConst ≤ conclConst + σ`);
  * `ltZ slack margin`  (strict headroom `σ < margin`).

Every comparison is integer cross-multiplication, so `decide`/`rfl` reduces the
whole thing in the kernel with NO `native_decide`. -/
def checkSlackEntailmentZ (sc : SCertZ) : Bool :=
  let cz := sc.base
  allDenPos cz &&
  decide (0 < sc.slack.2) && decide (0 < sc.margin.2) &&
  cz.premises.length == cz.multipliers.length &&
  cz.multipliers.all (fun μ => nonnegZ μ) &&
  nonnegZ sc.slack &&
  ltZ sc.slack sc.margin &&
  (match normalizeConclusionZ cz.conclusion with
   | none => false
   | some (conclCoeffs, conclConst) =>
       let pairs := cz.premises.zip cz.multipliers
       (collapseZ (diffMapZ pairs conclCoeffs)).all (fun p => isZeroZ p.2) &&
       leZ (combConstZ pairs) (addZ conclConst sc.slack))

/-! ## 3. The slack-weakened conclusion predicate.

The exact checker proves `conclusion.satisfies σ`.  The slack checker proves the
*weaker* relation: the conclusion's declared bound is met up to the slack `σ`,
i.e. for a `≤` conclusion `lhs ≤ const + σ`, for a `≥` conclusion
`const - σ ≤ lhs`.  We package this as a predicate on the lifted ℚ conclusion. -/

/-- The conclusion holds up to slack `q ≥ 0`:  for a `≤`-conclusion, the lhs is
    within `q` above the bound; for a `≥`-conclusion, within `q` below it; an
    `=`-conclusion is unsupported (the checker rejects it). -/
def satisfiesSlack (lc : LinearConstraint) (σ : Assignment) (q : ℚ) : Prop :=
  match lc.kind with
  | .le => lc.lhs σ ≤ lc.const + q
  | .ge => lc.const - q ≤ lc.lhs σ
  | .eq => False

/-! ## 3b. The slack-margin core: an upper bound on a functional `f` derived from a
       genuine `≤ 0` Farkas premise, routed through `slack_farkas`.

The slack checker establishes, at the satisfying assignment `τ`, two facts:

  * `f τ ≤ B`        (the Farkas combination bound — a genuine `≤ 0` premise
                      `g τ = f τ − B ≤ 0`, from `comb_le`), and
  * `B ≤ d + σ`      (the slack-weakened constant bound, `0 ≤ σ`).

`upper_bound_via_slack_farkas` concludes `f τ ≤ d + σ`, BUT does so by invoking
`Crownproof.slack_farkas` (not a bare `linarith`), so the slack soundness bottoms
out in the slack-Farkas core exactly as the exact checker bottoms out in
`farkas_premise_combination`.  The trick: present `slack_farkas` with the
single-premise family `{()}`, `g () s = f s − B` (which IS `≤ 0` at `τ`),
`out s = −f s`, `μ ≡ 1`, `c = B`, and slack `σ' = (d + σ) − B ≥ 0`. -/
theorem upper_bound_via_slack_farkas
    (f : Assignment → ℚ) (τ : Assignment) (B d σ : ℚ)
    (hfB : f τ ≤ B) (hBd : B ≤ d + σ) :
    f τ ≤ d + σ := by
  have hσ' : 0 ≤ (d + σ) - B := by linarith
  have hsf := slack_farkas (S := Assignment) (ι := Unit) (premises := {()})
    (g := fun _ s => f s - B)
    (out := fun s => -(f s))
    (μ := fun _ => 1)
    (c := B)
    (σ := (d + σ) - B)
    (valid := fun s => s = τ)
    (by intro i _; norm_num)
    (by intro i _ s hs; subst hs; simpa using hfB)
    hσ'
    (by
      intro s hs; subst hs
      simp only [Finset.sum_singleton, one_mul]
      -- goal: -(-(f τ)) - B - ((d+σ) - B) ≤ f τ - B
      linarith)
  have hres := hsf τ rfl
  -- hres : -B - ((d+σ) - B) ≤ -(f τ)   i.e.   f τ ≤ d + σ
  simp only at hres
  linarith

/-! ## 4. Soundness of the slack checker. -/

/--
**Soundness of `checkSlackEntailmentZ`.**

If the kernel-runnable slack checker accepts `sc`, then:

  (1) for EVERY assignment `σ` satisfying all premises of the lifted ℚ certificate
      `liftCert sc.base`, the conclusion holds up to the lifted slack
      `toQ sc.slack ≥ 0`  (`satisfiesSlack`); AND

  (2) the slack strictly undercuts the margin:  `toQ sc.slack < toQ sc.margin`
      (the headroom is `> σ`).

The slack bound bottoms out in `Crownproof.slack_farkas`: we instantiate its
abstract data with `g i s = (premise_i lhs − rhs)` made `≤ 0` on satisfying
assignments, `out s = ±(conclusion functional)`, `μ` the lifted multipliers,
`c` the conclusion constant, and `σ = toQ sc.slack`, then read off the
slack-weakened margin. -/
theorem checkSlackEntailmentZ_sound (sc : SCertZ)
    (hchk : checkSlackEntailmentZ sc = true) :
    (∀ σ : Assignment,
        (∀ lc ∈ (liftCert sc.base).premises, lc.satisfies σ) →
        satisfiesSlack (liftCert sc.base).conclusion σ (toQ sc.slack))
    ∧ toQ sc.slack < toQ sc.margin := by
  -- Unpack the Boolean checker.
  unfold checkSlackEntailmentZ at hchk
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨hden, hslackden⟩, hmargden⟩, hlen⟩, hμnn⟩, hσnn⟩, hlt⟩, hrest⟩ := hchk
  -- well-formedness facts from allDenPos
  obtain ⟨hpremwf, hmulwf, hcclwf, hcconstwf⟩ := allDenPos_wf sc.base hden
  have hslackwf : QPair.wf sc.slack := hslackden
  have hmargwf : QPair.wf sc.margin := hmargden
  -- the slack is non-negative and strictly below the margin
  have hσ0 : 0 ≤ toQ sc.slack := nonnegZ_sound sc.slack hslackwf hσnn
  have hheadroom : toQ sc.slack < toQ sc.margin := ltZ_sound sc.slack sc.margin hslackwf hmargwf hlt
  refine ⟨?_, hheadroom⟩
  intro σ hprem
  -- conclusion must normalize (not an equality)
  revert hrest
  cases hkz : normalizeConclusionZ sc.base.conclusion with
  | none => intro hr; simp at hr
  | some cc =>
    obtain ⟨conclCoeffsZ, conclConstZ⟩ := cc
    intro hrest
    simp only [Bool.and_eq_true, List.all_eq_true] at hrest
    obtain ⟨hzero, hleZ⟩ := hrest
    -- integer pairs and their lifts
    set zpairs := sc.base.premises.zip sc.base.multipliers with hzpairs
    have hzpairwf : ∀ p ∈ zpairs, (∀ q ∈ p.1.coeffs, QPair.wf q.2) ∧
        QPair.wf p.1.const ∧ QPair.wf p.2 := by
      intro p hp
      rw [hzpairs] at hp
      have hm := List.of_mem_zip hp
      have h1 := hpremwf p.1 hm.1
      exact ⟨h1.1, h1.2, hmulwf p.2 hm.2⟩
    have hzipeq : (liftCert sc.base).premises.zip (liftCert sc.base).multipliers
        = liftPairs zpairs := liftCert_zip sc.base
    -- every lifted multiplier ≥ 0
    have hμpos : ∀ p ∈ liftPairs zpairs, 0 ≤ p.2 := by
      intro p hp
      unfold liftPairs at hp
      rw [List.mem_map] at hp
      obtain ⟨q, hq, hqeq⟩ := hp
      rw [← hqeq]
      have hqm := List.of_mem_zip hq
      exact nonnegZ_sound q.2 (hmulwf q.2 hqm.2) (hμnn q.2 hqm.2)
    -- premises of liftPairs are satisfied by σ
    have hsat : ∀ p ∈ liftPairs zpairs, p.1.satisfies σ := by
      intro p hp
      unfold liftPairs at hp
      rw [List.mem_map] at hp
      obtain ⟨q, hq, hqeq⟩ := hp
      rw [← hqeq]
      have hqm := List.of_mem_zip hq
      apply hprem
      unfold liftCert
      simp only []
      rw [List.mem_map]
      exact ⟨q.1, hqm.1, rfl⟩
    -- wf collections needed for the coeff-cancellation and constant lemmas
    have hwf_for_comb : ∀ p ∈ zpairs, (∀ q ∈ p.1.coeffs, QPair.wf q.2) ∧ QPair.wf p.2 :=
      fun p hp => ⟨(hzpairwf p hp).1, (hzpairwf p hp).2.2⟩
    have hccoeffwf : ∀ p ∈ conclCoeffsZ, QPair.wf p.2 := by
      unfold normalizeConclusionZ at hkz
      rcases hk : sc.base.conclusion.kind with _ | _ | _ <;> rw [hk] at hkz <;> simp only at hkz
      · rw [Option.some.injEq, Prod.mk.injEq] at hkz
        rw [← hkz.1]; exact hcclwf
      · rw [Option.some.injEq, Prod.mk.injEq] at hkz
        rw [← hkz.1]; intro p hp
        simp only [negMapZ, List.mem_map] at hp
        obtain ⟨r, hr, hreq⟩ := hp; rw [← hreq]; unfold negZ QPair.wf; exact hcclwf r hr
      · exact absurd hkz (by simp)
    have hdiffwf : ∀ p ∈ diffMapZ zpairs conclCoeffsZ, QPair.wf p.2 := by
      intro p hp
      unfold diffMapZ at hp
      rw [List.mem_append] at hp
      rcases hp with hp | hp
      · have hcc : ∀ pairs : List (LinConZ × QPair),
            (∀ x ∈ pairs, (∀ q ∈ x.1.coeffs, QPair.wf q.2) ∧ QPair.wf x.2) →
            ∀ y ∈ combCoeffsZ pairs, QPair.wf y.2 := by
          intro pairs
          induction pairs with
          | nil => intro _ y hy; simp [combCoeffsZ] at hy
          | cons hd tl ih =>
            obtain ⟨lc, μ⟩ := hd
            intro hw y hy
            have hhd := hw (lc, μ) (List.mem_cons_self ..)
            simp only [combCoeffsZ, List.mem_append] at hy
            rcases hy with hy | hy
            · exact rowCoeffsZ_wf μ lc hhd.2 hhd.1 y hy
            · exact ih (fun x hx => hw x (List.mem_cons_of_mem _ hx)) y hy
        exact hcc zpairs hwf_for_comb p hp
      · simp only [negMapZ, List.mem_map] at hp
        obtain ⟨r, hr, hreq⟩ := hp; rw [← hreq]; unfold negZ QPair.wf; exact hccoeffwf r hr
    -- the combined coefficient functional equals the lifted conclusion functional
    have hfun : evalMap (combCoeffs (liftPairs zpairs)) σ = evalMap (liftCoeffs conclCoeffsZ) σ := by
      have hcollwf : ∀ p ∈ collapseZ (diffMapZ zpairs conclCoeffsZ), QPair.wf p.2 := by
        unfold collapseZ
        have hfoldwf : ∀ (m : List (String × QPair)), (∀ p ∈ m, QPair.wf p.2) →
            ∀ acc : List (String × QPair), (∀ p ∈ acc, QPair.wf p.2) →
            ∀ p ∈ m.foldl (fun a q => addEntryZ a q.1 q.2) acc, QPair.wf p.2 := by
          intro m
          induction m with
          | nil => intro _ acc hacc p hp; exact hacc p hp
          | cons hd tl ih =>
            intro hm acc hacc p hp
            simp only [List.foldl_cons] at hp
            have hc : QPair.wf hd.2 := hm hd (List.mem_cons_self ..)
            have hacc' : ∀ x ∈ addEntryZ acc hd.1 hd.2, QPair.wf x.2 :=
              addEntryZ_wf acc hd.1 hd.2 hacc hc
            exact ih (fun x hx => hm x (List.mem_cons_of_mem _ hx))
              (addEntryZ acc hd.1 hd.2) hacc' p hp
        exact hfoldwf (diffMapZ zpairs conclCoeffsZ) hdiffwf [] (by simp)
      have h0 : evalMap (liftCoeffs (collapseZ (diffMapZ zpairs conclCoeffsZ))) σ = 0 :=
        evalMap_liftCoeffs_eq_zero_of_isZeroZ _ hcollwf hzero σ
      rw [evalMap_liftCoeffs_collapseZ (diffMapZ zpairs conclCoeffsZ) hdiffwf σ] at h0
      unfold diffMapZ at h0
      rw [liftCoeffs_append, evalMap_append, liftCoeffs_negMapZ, evalMap_negMap,
          evalMap_liftCoeffs_combCoeffsZ zpairs hwf_for_comb σ] at h0
      linarith
    -- wf of the lifted conclusion constant
    have hcconstZwf : QPair.wf conclConstZ := by
      unfold normalizeConclusionZ at hkz
      rcases hk : sc.base.conclusion.kind with _ | _ | _ <;> rw [hk] at hkz <;> simp only at hkz
      · rw [Option.some.injEq, Prod.mk.injEq] at hkz; rw [← hkz.2]; exact hcconstwf
      · rw [Option.some.injEq, Prod.mk.injEq] at hkz; rw [← hkz.2]
        unfold negZ QPair.wf; exact hcconstwf
      · exact absurd hkz (by simp)
    -- the slack-weakened constant bound:  combConst ≤ conclConst + σ
    have hbound : combConst (liftPairs zpairs) ≤ toQ conclConstZ + toQ sc.slack := by
      have h1 : toQ (addZ conclConstZ sc.slack) = toQ conclConstZ + toQ sc.slack :=
        toQ_addZ conclConstZ sc.slack hcconstZwf hslackwf
      have h2 : combConst (liftPairs zpairs) ≤ toQ (addZ conclConstZ sc.slack) := by
        rw [← toQ_combConstZ zpairs (fun p hp => ⟨(hzpairwf p hp).2.1, (hzpairwf p hp).2.2⟩) σ]
        exact leZ_sound _ _ (combConstZ_wf zpairs
          (fun p hp => ⟨(hzpairwf p hp).2.1, (hzpairwf p hp).2.2⟩))
          (addZ_wf hcconstZwf hslackwf) hleZ
      rw [h1] at h2; exact h2
    -- The exact Farkas/`comb_le` chain gives `f τ ≤ combConst`, where `f` is the
    -- (lifted) conclusion coefficient functional; `hbound` gives the slack-weakened
    -- constant bound `combConst ≤ conclConst + σ`.  We route the resulting upper
    -- bound through `upper_bound_via_slack_farkas`, so soundness BOTTOMS OUT in
    -- `slack_farkas` — the genuine `≤ 0` premise is `f s − combConst ≤ 0`.
    have hcomb := comb_le (liftPairs zpairs) σ hμpos hsat
    rw [hfun] at hcomb
    -- f τ ≤ combConst (liftPairs zpairs) ≤ toQ conclConstZ + toQ sc.slack
    have hslackbound : evalMap (liftCoeffs conclCoeffsZ) σ ≤ toQ conclConstZ + toQ sc.slack :=
      upper_bound_via_slack_farkas
        (fun s => evalMap (liftCoeffs conclCoeffsZ) s) σ
        (combConst (liftPairs zpairs)) (toQ conclConstZ) (toQ sc.slack)
        hcomb hbound
    -- relate the lifted-Z conclusion to the lifted-ℚ conclusion normalization
    have hnc : normalizeConclusion (liftCert sc.base).conclusion
        = some (liftCoeffs conclCoeffsZ, toQ conclConstZ) := by
      have : (liftCert sc.base).conclusion = liftCon sc.base.conclusion := rfl
      rw [this]
      exact normalizeConclusionZ_lift sc.base.conclusion conclCoeffsZ conclConstZ hkz
    unfold normalizeConclusion at hnc
    have hlhs : (liftCert sc.base).conclusion.lhs σ
        = evalMap (liftCert sc.base).conclusion.coeffs σ := rfl
    -- discharge by cases on the lifted conclusion kind
    cases hck : (liftCert sc.base).conclusion.kind with
    | le =>
      rw [hck] at hnc
      simp only [Option.some.injEq, Prod.mk.injEq] at hnc
      obtain ⟨hcoe, hcon⟩ := hnc
      -- hcoe : conclusion.coeffs = liftCoeffs conclCoeffsZ ; hcon : const = toQ conclConstZ
      rw [← hcoe, ← hcon] at hslackbound
      have hgoal : (liftCert sc.base).conclusion.lhs σ
          ≤ (liftCert sc.base).conclusion.const + toQ sc.slack := by
        rw [hlhs]; exact hslackbound
      simp only [satisfiesSlack, hck]; exact hgoal
    | ge =>
      rw [hck] at hnc
      simp only [Option.some.injEq, Prod.mk.injEq] at hnc
      obtain ⟨hcoe, hcon⟩ := hnc
      -- hcoe : negMap conclusion.coeffs = liftCoeffs conclCoeffsZ ; hcon : -const = toQ conclConstZ
      rw [← hcoe, ← hcon, evalMap_negMap] at hslackbound
      -- hslackbound : -(evalMap conclusion.coeffs σ) ≤ -const + slack
      have hgoal : (liftCert sc.base).conclusion.const - toQ sc.slack
          ≤ (liftCert sc.base).conclusion.lhs σ := by
        rw [hlhs]; linarith
      simp only [satisfiesSlack, hck]; exact hgoal
    | eq =>
      -- the conclusion normalized to `some`, so kind ≠ eq; contradiction
      exfalso
      have : (liftCert sc.base).conclusion.kind = sc.base.conclusion.kind := rfl
      rw [this] at hck
      unfold normalizeConclusionZ at hkz
      rw [hck] at hkz
      simp at hkz

/-! ## 5. A concrete tiny slack leaf, closed by kernel reduction (NO native_decide).

We exhibit a 2-premise / 2-variable slack cert whose `checkSlackEntailmentZ`
reduces to `true` by `decide`/`rfl` in the kernel, demonstrating that the integer
slack checker is genuinely kernel-runnable.

Premises:
    P0 :  x ≤ 1        (le,  coeffs [(x,1)], const 1)   mult μ0 = 1
    P1 :  y ≤ 2        (le,  coeffs [(y,1)], const 2)   mult μ1 = 1
Combined functional:  1·x + 1·y = x + y.
Conclusion:  x + y ≤ 4   (le, coeffs [(x,1),(y,1)], const 4).
Combined functional `x + y` cancels the conclusion functional `x + y`  (the
`isZeroZ` test on the collapsed diff map passes).
Combined const  1 + 2 = 3  ≤  conclConst 4 + slack 1/4 = 17/4.   ✓
Slack 1/4 < margin 1/2.  ✓ (headroom).

The EXACT checker would also accept this leaf (3 ≤ 4).  The slack checker's extra
power is that it ALSO accepts leaves where the exact bound just fails to a
low-bitwidth rounding (`combConst` a hair above `conclConst`) but stays within the
slack budget `σ`, and additionally certifies the strict headroom `σ < margin`. -/

/-- A concrete slack leaf cert (all data as integer pairs). -/
def demoSlackCert : SCertZ :=
  { base :=
      { premises :=
          [ { coeffs := [("x", (1, 1))], kind := Kind.le, const := (1, 1) },
            { coeffs := [("y", (1, 1))], kind := Kind.le, const := (2, 1) } ],
        multipliers := [(1, 1), (1, 1)],
        conclusion :=
          { coeffs := [("x", (1, 1)), ("y", (1, 1))], kind := Kind.le, const := (4, 1) } },
    slack  := (1, 4),
    margin := (1, 2) }

/-- The concrete slack leaf is accepted by the kernel-runnable checker — proven by
    `decide` (pure integer cross-multiplication, NO `native_decide`). -/
theorem demoSlackCert_checks : checkSlackEntailmentZ demoSlackCert = true := by
  decide

/-- Therefore, by `checkSlackEntailmentZ_sound`, the lifted demo conclusion holds
    up to the slack `1/4`, and the slack `1/4` is strictly below the margin `1/2`.
    A fully kernel-checked slack leaf as a Lean theorem. -/
theorem demoSlackCert_sound :
    (∀ σ : Assignment,
        (∀ lc ∈ (liftCert demoSlackCert.base).premises, lc.satisfies σ) →
        satisfiesSlack (liftCert demoSlackCert.base).conclusion σ (toQ demoSlackCert.slack))
    ∧ toQ demoSlackCert.slack < toQ demoSlackCert.margin :=
  checkSlackEntailmentZ_sound demoSlackCert demoSlackCert_checks

/-! ## 6. Trust-base check.  Must list only the three standard logical axioms. -/

#print axioms ltZ_sound
#print axioms checkSlackEntailmentZ_sound
#print axioms demoSlackCert_checks
#print axioms demoSlackCert_sound

end SlackCertZ
end Crownproof
