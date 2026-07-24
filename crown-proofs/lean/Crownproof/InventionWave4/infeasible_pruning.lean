/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

INVENTION WAVE 4 — C3: INFEASIBLE-DOMAIN PRUNING LEAVES  (completeness-pruning).

Sealed conjecture (wave-1 carryover, prove-next in wave-4):
  data/provenance/invention-wave-1-conjectures-2026-06-11.json
  C3 — "infeasible-domain pruning leaves: decidable Farkas-infeasibility
        certificates in the babtree recursor"
  sha256  b831fb3b0cc28534bbbd90e4ce98cbd3a9dca2a919bd65b47a425dfdb46db548
  (re-triaged in data/provenance/invention-wave-4-conjectures-2026-06-13.json
   carryover_digests, wave4_verdict = "prove-next"; plan
   reports/invention-wave-4-plan-2026-06-13.md, rank 5.)

WHAT THIS FILE LANDS
--------------------
A *second leaf kind* for the kernel-internal branch-and-bound proof tree of
`Crownproof.Bab` (`BabProof.lean`): a PRUNED leaf carrying a decidable Farkas
*infeasibility* certificate over the accumulated path premises.  The certificate
ships non-negative integer-pair multipliers `μᵢ` and a positive integer-pair
constant `κ` with

    ∑ μᵢ · (signᵢ · x_{cᵢ} − boundᵢ)  ≡  κ            (identically in x)

i.e. the residual coefficient of every coordinate is zero AND the residual
constant equals `κ`, both checked by the integer-pair `addZ`/`mulZ`/`isZeroZ`
residual fold — the SAME Int-pair discipline as `CertCheckerZ`, keyed by the
abstract `Coord` and specialized so the kernel reduces it by `decide`/`rfl`, NO
`native_decide`.

Soundness (`infeasCert_empties`): if the check passes AND every listed premise is
a sound `≤ 0` fact on the path box, then the μ-combination of the premises is
`≤ 0` (non-negative μ × non-positive premises) yet equals `κ > 0` — a
contradiction.  Hence NO sample reaches that leaf: the path box is *empty*, the
leaf is vacuously safe, the domain is pruned with a kernel-checkable certificate.
This routes through `Bridge.lean`'s kernel-checked Farkas core
`farkas_premise_combination` (with `out := 0`, `c := −toQ κ`) — the empty-margin
trick of `checkLeafCert_sound` run "in reverse" — so the prune bottoms out in the
same trusted core as every other leaf, not re-derived.

`babtree_prune_sound` is the recursor: a `BabProofP` tree composing margin leaves,
PRUNED leaves, and splits in ONE tree; if `checkBabProofP p = true` and the
tree's `ObligationsP` hold on the root region, then `0 ≤ out s` on the whole root
box.  Pruned leaves are discharged by `absurd`/`False.elim` from
`infeasCert_empties` (an empty box is vacuously safe); margin leaves reuse
`Bab.checkLeafCert_margin_nonneg`; splits reuse the SAME `le_total` covering as
`Bab.safe_on_path`.  `prunedLeafCount` exactly counts pruned domains alongside
C1's `length`/`prunedCount` Δdomains identity.

`prunedTree` + `prunedTree_checks` (`by decide`) + `prunedTree_safe` exhibit the
end-to-end path on a concrete depth-1 tree whose right child is PRUNED by κ = 1
from the contradictory premises `x ≤ 0 ∧ x ≥ 1`:  on that path
`1·(x − 0) + 1·(−x − (−1)) = 1 > 0` while both premises are `≤ 0`, so the box is
empty — the full-`decide` route is exhibited honestly on this tiny instance.

STATEMENT-FIDELITY DELTAS vs the SEALED sketch (documented, not hidden)
----------------------------------------------------------------------
The seal's `lean_statement_sketch` is a SKETCH ("extends BabProof.lean's types");
the faithful realization carries these deltas, each soundness-neutral:

  D1 (namespace).  The sketch writes `namespace Crownproof`; `BabProof.lean`'s
     types (`BoxPrem`, `premFun`, `LeafCert`, `Obligations`, `safe_on_path`,
     `checkLeafSafe`) actually live in `Crownproof.Bab`.  This file opens
     `Crownproof.Bab` and adds its content in `Crownproof.InventionWave4`,
     reusing those types verbatim.  No semantic change.

  D2 (field names).  The sketch's `InfeasCert.μ`/`.κ` are spelled `mu`/`kappa`
     (ASCII identifiers; `μ`/`κ` collide with local binders in the proofs).
     Same data.  No semantic change.

  D3 (residual checker realization).  The sketch declares `checkInfeasCert` and
     "reuse CertChecker.addEntry".  `CertChecker`'s `addEntry`/`collapse` are
     `String`-keyed; `BabProof` coordinates are an abstract `Coord`.  We supply a
     self-contained `Coord`-keyed `addEntryC`/`collapseC` mirroring that
     discipline EXACTLY (same fold, same evaluation-preserving lemma) over
     integer-pair `QPair` coefficients (`CertCheckerZ`'s `addZ`/`mulZ`/`negZ`/
     `isZeroZ`), under `[DecidableEq Coord]`.  "Reuse the discipline,
     re-instantiate at the right key type."  No semantic change to the cert.

  D4 (tree type name + recursor shape).  The sketch's `BabProofP` /
     `checkBabProofP` / `ObligationsP` / `babtree_prune_sound` are realized with
     exactly those names; `ObligationsP` parallels `Bab.Obligations` with the
     extra `pruned` arm, and the recursor is proved by direct structural
     induction (mirroring `Bab.safe_on_path` verbatim on the shared arms).  The
     sketch's `checkLeafSafe`/`checkInfeasSafe` obligation-bridges are realized as
     `leafSafeP`/`pruneSafeP`.  No semantic change.

  D5 (premise-binding is an Obligations-level HYPOTHESIS, stated not hidden).
     `infeasCert_empties` / the `pruned` obligation take
     `hprems : ∀ p ∈ ic.prems, ∀ x, path x → premFun coord p x ≤ 0` as an
     explicit hypothesis — exactly the W2-flavor "the cert's premises really are
     the path's premises" assumed-as-premise edge the seal's `risk` field flags
     (mirrors `Bab.checkLeafSafe`'s `hval`).  The DECIDABLE part is the
     residual/sign/positivity algebra; the premise-soundness binding is assumed,
     exactly as in every existing `Bab` leaf.

  D6 (kappa positivity carried in the constant check).  `checkInfeasCert` verifies
     `0 < kappa.num` and `0 < kappa.den` directly (the seal's "`κ` a positive
     constant"); the residual-constant identity `−∑ μᵢ·boundᵢ = κ` is checked by
     the integer-pair `isZeroZ` test on `addZ (combConst) kappa` (their ℚ-sum is
     0 ⇔ `−∑μ·bound = κ`).  No semantic change.

  D7 (sample type = `Coord → ℚ`).  The seal's sketch writes the sample type as a
     free `S` with `coord : Coord → S → ℚ`, but `BabProof.premFun`'s ACTUAL type
     is `coord : Coord → (Coord → ℚ) → ℚ` with samples `x : Coord → ℚ` (a sample
     IS its coordinate readout).  We realize `infeasCert_empties` / the recursor
     at `S := Coord → ℚ` to match `premFun` verbatim; `coord` stays an abstract
     parameter (so the canonical evaluation `coord c x = x c` is one instance,
     used in the demo, but the theorems are generic over `coord`).  This is a
     specialization to the substrate's real API, not a strengthening.  No
     soundness change.

HONESTY (N1, pending novelty-index check)
-----------------------------------------
Per-leaf Farkas-infeasibility certificates for BaB are Marabou's published
mechanism (Isac et al., CAV 2022), checked there by an UNVERIFIED C++ checker.
The claimable delta is strictly: *first kernel-internal decidable
infeasibility-pruning leaf composed in a verified BaB recursor* (N1
first-formalization phrasing) — NEVER a new certificate type.  Every counted
quantity (`prunedLeafCount`) is a Δdomains-class exactly-counted integer; no
GPU / wall-clock / VNN-COMP-score claim appears anywhere here.
-/
import Crownproof.BabProof
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin

namespace Crownproof
namespace InventionWave4

open Crownproof.Bab

/-! ## 0. Integer-pair arithmetic (mirrors `CertCheckerZ`, kept local).

We re-state the `QPair` arithmetic locally to keep this file self-contained on
the `Crownproof.Bab.QPair` alias (`ℤ × ℤ`, den > 0) and `Bab.toQ`.  These are
byte-for-byte the `CertCheckerZ` operations; the homomorphism lemmas to `toQ`
are re-proved here over `Bab.toQ` so nothing leaks from the `CertChecker`
String-keyed world. -/

/-- Well-formed pair: positive denominator. -/
def QPair.wf (p : QPair) : Prop := 0 < p.2

/-- Product of two integer pairs (unreduced). -/
def mulZ (a b : QPair) : QPair := (a.1 * b.1, a.2 * b.2)

/-- Sum of two integer pairs (unreduced common denominator). -/
def addZ (a b : QPair) : QPair := (a.1 * b.2 + b.1 * a.2, a.2 * b.2)

/-- Negation. -/
def negZ (a : QPair) : QPair := (-a.1, a.2)

/-- `toQ a = 0`  ⇔  `a.num = 0`  (the residual-zero decidable test). -/
def isZeroZ (a : QPair) : Bool := decide (a.1 = 0)

theorem toQ_mulZ (a b : QPair) (ha : QPair.wf a) (hb : QPair.wf b) :
    toQ (mulZ a b) = toQ a * toQ b := by
  unfold toQ mulZ QPair.wf at *
  have ha' : (a.2 : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b.2 : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  push_cast; field_simp

theorem toQ_addZ (a b : QPair) (ha : QPair.wf a) (hb : QPair.wf b) :
    toQ (addZ a b) = toQ a + toQ b := by
  unfold toQ addZ QPair.wf at *
  have ha' : (a.2 : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b.2 : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  push_cast; field_simp

theorem toQ_negZ (a : QPair) : toQ (negZ a) = - toQ a := by
  unfold toQ negZ; push_cast; ring

theorem isZeroZ_sound (a : QPair) (h : isZeroZ a = true) : toQ a = 0 := by
  unfold isZeroZ at h
  rw [decide_eq_true_iff] at h
  unfold toQ; rw [h]; simp

theorem mulZ_wf {a b : QPair} (ha : QPair.wf a) (hb : QPair.wf b) :
    QPair.wf (mulZ a b) := by unfold QPair.wf mulZ at *; exact mul_pos ha hb

theorem addZ_wf {a b : QPair} (ha : QPair.wf a) (hb : QPair.wf b) :
    QPair.wf (addZ a b) := by unfold QPair.wf addZ at *; exact mul_pos ha hb

/-- The integer-pair encoding of ℚ `0`. -/
def zeroZ : QPair := (0, 1)

theorem zeroZ_wf : QPair.wf zeroZ := by unfold QPair.wf zeroZ; norm_num

theorem toQ_zeroZ : toQ zeroZ = 0 := by unfold toQ zeroZ; simp

/-! ## 1. The infeasibility certificate. -/

/-- A Farkas *infeasibility* certificate for the accumulated path box.
`prems` are the path premises being contradicted (each interpreted by `premFun`
as `signᵢ·x_{cᵢ} − boundᵢ`, sound ⇒ `≤ 0`); `mu` are the non-negative
multipliers (one per premise, by position); `kappa` is the strictly-positive
constant the μ-combination equals (so a strictly-positive value equals a
non-positive sum — the contradiction). -/
structure InfeasCert (Coord : Type*) where
  prems : List (BoxPrem Coord)
  mu    : List QPair
  kappa : QPair

variable {Coord : Type*}

/-! ## 2. `Coord`-keyed coefficient algebra (mirrors `CertChecker.addEntry`).

`evalC m x = Σ (c,q) ∈ m, toQ q · x_c`.  The combination's coordinate-coefficient
map keys each premise's coordinate `prem.c` with `μ·sign`; collapsing by `Coord`
and testing each collapsed numerator is zero certifies the residual coordinate
coefficients all vanish. -/

/-- `evalC coord m x = Σ (c,q) ∈ m, toQ q · (coord c x)`.  Threads the same
    coordinate reader `coord : Coord → (Coord → ℚ) → ℚ` that `premFun` uses, so
    the combination's coordinate part aligns definitionally with the premises. -/
def evalC (coord : Coord → (Coord → ℚ) → ℚ) (m : List (Coord × QPair))
    (x : Coord → ℚ) : ℚ :=
  (m.map (fun p => toQ p.2 * coord p.1 x)).sum

@[simp] theorem evalC_nil (coord : Coord → (Coord → ℚ) → ℚ) (x : Coord → ℚ) :
    evalC coord ([] : List (Coord × QPair)) x = 0 := by
  simp [evalC]

theorem evalC_cons (coord : Coord → (Coord → ℚ) → ℚ) (hd : Coord × QPair)
    (tl : List (Coord × QPair)) (x : Coord → ℚ) :
    evalC coord (hd :: tl) x = toQ hd.2 * coord hd.1 x + evalC coord tl x := by
  simp [evalC]

/-- A map all of whose coefficients are `toQ = 0` has functional value `0`. -/
theorem evalC_eq_zero_of_allZeroQ (coord : Coord → (Coord → ℚ) → ℚ)
    (m : List (Coord × QPair)) (x : Coord → ℚ)
    (h : ∀ p ∈ m, toQ p.2 = 0) : evalC coord m x = 0 := by
  induction m with
  | nil => simp
  | cons hd tl ih =>
    rw [evalC_cons, h hd (List.mem_cons_self ..),
        ih (fun p hp => h p (List.mem_cons_of_mem _ hp))]
    ring

/-- Add coefficient `q` for coordinate `c` into an assoc-list, summing into an
    existing entry (via `addZ`) if present, else appending (mirrors `addEntry`). -/
def addEntryC [DecidableEq Coord] :
    List (Coord × QPair) → Coord → QPair → List (Coord × QPair)
  | [], c, q => [(c, q)]
  | (d, e) :: rest, c, q =>
      if c = d then (d, addZ e q) :: rest
      else (d, e) :: addEntryC rest c q

/-- `addEntryC` adds `toQ q · (coord c x)` to the functional value (given wf
    entries). -/
theorem evalC_addEntryC [DecidableEq Coord] (coord : Coord → (Coord → ℚ) → ℚ)
    (acc : List (Coord × QPair)) (c : Coord) (q : QPair)
    (hacc : ∀ p ∈ acc, QPair.wf p.2) (hq : QPair.wf q) (x : Coord → ℚ) :
    evalC coord (addEntryC acc c q) x = evalC coord acc x + toQ q * coord c x := by
  induction acc with
  | nil =>
    show evalC coord [(c, q)] x = evalC coord ([] : List (Coord × QPair)) x + toQ q * coord c x
    rw [evalC_cons, evalC_nil]; ring
  | cons hd tl ih =>
    obtain ⟨d, e⟩ := hd
    have he_wf : QPair.wf e := hacc (d, e) (List.mem_cons_self ..)
    have htl_wf : ∀ p ∈ tl, QPair.wf p.2 := fun p hp => hacc p (List.mem_cons_of_mem _ hp)
    by_cases hcd : c = d
    · subst hcd
      have he : addEntryC ((c, e) :: tl) c q = (c, addZ e q) :: tl := by
        show (if c = c then (c, addZ e q) :: tl else (c, e) :: addEntryC tl c q)
              = (c, addZ e q) :: tl
        rw [if_pos rfl]
      rw [he, evalC_cons, evalC_cons, toQ_addZ e q he_wf hq]; ring
    · have he : addEntryC ((d, e) :: tl) c q = (d, e) :: addEntryC tl c q := by
        show (if c = d then (d, addZ e q) :: tl else (d, e) :: addEntryC tl c q)
              = (d, e) :: addEntryC tl c q
        rw [if_neg hcd]
      rw [he, evalC_cons, evalC_cons, ih htl_wf]; ring

/-- `addEntryC` preserves well-formedness. -/
theorem addEntryC_wf [DecidableEq Coord] (acc : List (Coord × QPair)) (c : Coord)
    (q : QPair) (hacc : ∀ p ∈ acc, QPair.wf p.2) (hq : QPair.wf q) :
    ∀ p ∈ addEntryC acc c q, QPair.wf p.2 := by
  induction acc with
  | nil =>
    intro p hp
    simp only [addEntryC, List.mem_singleton] at hp
    subst hp; exact hq
  | cons hd tl ih =>
    obtain ⟨d, e⟩ := hd
    have he_wf : QPair.wf e := hacc (d, e) (List.mem_cons_self ..)
    have htl_wf : ∀ p ∈ tl, QPair.wf p.2 := fun p hp => hacc p (List.mem_cons_of_mem _ hp)
    by_cases hcd : c = d
    · have he : addEntryC ((d, e) :: tl) c q = (d, addZ e q) :: tl := by
        show (if c = d then (d, addZ e q) :: tl else (d, e) :: addEntryC tl c q)
              = (d, addZ e q) :: tl
        rw [if_pos hcd]
      rw [he]; intro p hp
      rcases List.mem_cons.mp hp with hp | hp
      · subst hp; exact addZ_wf he_wf hq
      · exact htl_wf p hp
    · have he : addEntryC ((d, e) :: tl) c q = (d, e) :: addEntryC tl c q := by
        show (if c = d then (d, addZ e q) :: tl else (d, e) :: addEntryC tl c q)
              = (d, e) :: addEntryC tl c q
        rw [if_neg hcd]
      rw [he]; intro p hp
      rcases List.mem_cons.mp hp with hp | hp
      · subst hp; exact he_wf
      · exact ih htl_wf p hp

/-- Collapse a coefficient map: sum contributions per coordinate. -/
def collapseC [DecidableEq Coord] (m : List (Coord × QPair)) : List (Coord × QPair) :=
  m.foldl (fun acc p => addEntryC acc p.1 p.2) []

/-- Folding `addEntryC` from a wf accumulator preserves the functional sum. -/
theorem evalC_foldl_addEntryC [DecidableEq Coord] (coord : Coord → (Coord → ℚ) → ℚ)
    (m : List (Coord × QPair)) (hm : ∀ p ∈ m, QPair.wf p.2) (x : Coord → ℚ) :
    ∀ acc : List (Coord × QPair), (∀ p ∈ acc, QPair.wf p.2) →
      evalC coord (m.foldl (fun a p => addEntryC a p.1 p.2) acc) x
        = evalC coord acc x + evalC coord m x := by
  induction m with
  | nil => intro acc _; simp
  | cons hd tl ih =>
    intro acc hacc
    obtain ⟨c, q⟩ := hd
    have hq : QPair.wf q := hm (c, q) (List.mem_cons_self ..)
    have htl : ∀ p ∈ tl, QPair.wf p.2 := fun p hp => hm p (List.mem_cons_of_mem _ hp)
    simp only [List.foldl_cons]
    have hacc' : ∀ p ∈ addEntryC acc c q, QPair.wf p.2 := addEntryC_wf acc c q hacc hq
    rw [ih htl (addEntryC acc c q) hacc', evalC_addEntryC coord acc c q hacc hq, evalC_cons]
    ring

/-- `collapseC` preserves the linear functional. -/
theorem evalC_collapseC [DecidableEq Coord] (coord : Coord → (Coord → ℚ) → ℚ)
    (m : List (Coord × QPair)) (hm : ∀ p ∈ m, QPair.wf p.2) (x : Coord → ℚ) :
    evalC coord (collapseC m) x = evalC coord m x := by
  unfold collapseC
  rw [evalC_foldl_addEntryC coord m hm x [] (by simp)]; simp

/-! ## 3. The μ-combination's coordinate map and residual constant. -/

/-- The coordinate-coefficient map of the μ-combination: for each `(prem, μ)`,
    key `prem.c` with the coefficient `μ · sign` (as a `QPair`,
    `mulZ μ (prem.sign, 1)`).  `evalC (combCoeffMap pairs) x` is the
    `x`-dependent part of `∑ μᵢ·premFun premᵢ x`. -/
def combCoeffMap (pairs : List (BoxPrem Coord × QPair)) : List (Coord × QPair) :=
  pairs.map (fun p => (p.1.c, mulZ p.2 (p.1.sign, 1)))

theorem combCoeffMap_cons (hd : BoxPrem Coord × QPair)
    (tl : List (BoxPrem Coord × QPair)) :
    combCoeffMap (hd :: tl) = (hd.1.c, mulZ hd.2 (hd.1.sign, 1)) :: combCoeffMap tl := by
  simp [combCoeffMap]

/-- The residual constant of the μ-combination: `∑ μᵢ · (−boundᵢ)` as a `QPair`
    via repeated `addZ` (the constant part of `∑ μᵢ·premFun premᵢ x`; note
    `premFun` subtracts `bound`, so the per-pair constant is `−μ·bound`). -/
def combConst : List (BoxPrem Coord × QPair) → QPair
  | [] => zeroZ
  | (prem, μ) :: rest => addZ (negZ (mulZ μ prem.bound)) (combConst rest)

theorem combCoeffMap_wf (pairs : List (BoxPrem Coord × QPair))
    (hwf : ∀ p ∈ pairs, QPair.wf p.2) :
    ∀ p ∈ combCoeffMap pairs, QPair.wf p.2 := by
  intro p hp
  unfold combCoeffMap at hp
  rw [List.mem_map] at hp
  obtain ⟨q, hq, hqeq⟩ := hp
  rw [← hqeq]
  exact mulZ_wf (hwf q hq) (by unfold QPair.wf; norm_num)

theorem combConst_wf (pairs : List (BoxPrem Coord × QPair))
    (hwf : ∀ p ∈ pairs, QPair.wf p.1.bound ∧ QPair.wf p.2) :
    QPair.wf (combConst pairs) := by
  induction pairs with
  | nil => exact zeroZ_wf
  | cons hd tl ih =>
    obtain ⟨prem, μ⟩ := hd
    have hhd := hwf (prem, μ) (List.mem_cons_self ..)
    have htl : ∀ p ∈ tl, QPair.wf p.1.bound ∧ QPair.wf p.2 :=
      fun p hp => hwf p (List.mem_cons_of_mem _ hp)
    simp only [combConst]
    refine addZ_wf ?_ (ih htl)
    unfold negZ QPair.wf; exact (mulZ_wf hhd.2 hhd.1)

/-- **The combination identity.**  As a rational function of `x`,
    `∑ μᵢ·premFun premᵢ x
       = evalC coord (combCoeffMap pairs) x + toQ (combConst pairs)`.
    This is the algebraic decomposition the checker certifies (coordinate part +
    constant part), proved by induction on the pair list. -/
theorem comb_decomp (coord : Coord → (Coord → ℚ) → ℚ)
    (pairs : List (BoxPrem Coord × QPair))
    (hwf : ∀ p ∈ pairs, QPair.wf p.1.bound ∧ QPair.wf p.2) (x : Coord → ℚ) :
    (pairs.map (fun p => toQ p.2 * premFun coord p.1 x)).sum
      = evalC coord (combCoeffMap pairs) x + toQ (combConst pairs) := by
  induction pairs with
  | nil => simp [combCoeffMap, combConst, toQ_zeroZ]
  | cons hd tl ih =>
    obtain ⟨prem, μ⟩ := hd
    have hhd := hwf (prem, μ) (List.mem_cons_self ..)
    have htl : ∀ p ∈ tl, QPair.wf p.1.bound ∧ QPair.wf p.2 :=
      fun p hp => hwf p (List.mem_cons_of_mem _ hp)
    have hsign_wf : QPair.wf ((prem.sign, 1) : QPair) := by unfold QPair.wf; norm_num
    rw [List.map_cons, List.sum_cons, ih htl, combCoeffMap_cons, evalC_cons]
    simp only [combConst]
    rw [toQ_addZ (negZ (mulZ μ prem.bound)) (combConst tl)
          (by unfold negZ QPair.wf; exact (mulZ_wf hhd.2 hhd.1)) (combConst_wf tl htl),
        toQ_negZ, toQ_mulZ μ prem.bound hhd.2 hhd.1,
        toQ_mulZ μ (prem.sign, 1) hhd.2 hsign_wf]
    -- premFun prem x = (sign) * coord prem.c x - toQ prem.bound
    unfold premFun
    have htoq_sign : toQ ((prem.sign, 1) : QPair) = (prem.sign : ℚ) := by
      unfold toQ; simp
    rw [htoq_sign]
    ring

/-! ## 4. The decidable infeasibility checker. -/

/-- Well-formedness of every `QPair` in a cert, computed as a `Bool`. -/
def allDenPos (ic : InfeasCert Coord) : Bool :=
  ic.prems.all (fun prem => decide (0 < prem.bound.2)) &&
  ic.mu.all (fun μ => decide (0 < μ.2)) &&
  decide (0 < ic.kappa.2)

/--
**The decidable infeasibility checker.**  All arithmetic is integer-pair
cross-multiplication, so `decide`/`rfl` reduces it in the kernel — GMP-backed,
NO `native_decide`.  It accepts `ic` iff:

  * all denominators are positive (`allDenPos`);
  * the premise and multiplier lists have equal length;
  * every multiplier numerator is `≥ 0`  (`μ ≥ 0`);
  * `κ` is strictly positive  (`0 < κ.num` and `0 < κ.den`);
  * every collapsed coordinate residual numerator is `0`  (the coordinate part of
    `∑ μᵢ·premFun premᵢ x` vanishes for all `x`); and
  * the residual constant identity `(∑ μᵢ·(−boundᵢ)) − κ = 0`, i.e.
    `−∑ μᵢ·boundᵢ = κ`  (so `∑ μᵢ·premFun premᵢ x = κ` for all `x`).
-/
def checkInfeasCert [DecidableEq Coord] (ic : InfeasCert Coord) : Bool :=
  allDenPos ic &&
  (ic.prems.length == ic.mu.length) &&
  ic.mu.all (fun μ => decide (0 ≤ μ.1)) &&
  decide (0 < ic.kappa.1) &&
  (let pairs := ic.prems.zip ic.mu
   (collapseC (combCoeffMap pairs)).all (fun p => isZeroZ p.2) &&
   isZeroZ (addZ (combConst pairs) (negZ ic.kappa)))

/-! ## 5. Soundness of the leaf check: a passing cert empties its path box. -/

/-- wf extraction from `allDenPos`. -/
theorem allDenPos_wf (ic : InfeasCert Coord) (h : allDenPos ic = true) :
    (∀ prem ∈ ic.prems, QPair.wf prem.bound) ∧
    (∀ μ ∈ ic.mu, QPair.wf μ) ∧ QPair.wf ic.kappa := by
  unfold allDenPos at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hprem, hmul⟩, hkappa⟩ := h
  refine ⟨fun prem hp => ?_, fun μ hm => ?_, ?_⟩ <;> unfold QPair.wf
  · exact hprem prem hp
  · exact hmul μ hm
  · exact hkappa

/--
**Pruning soundness (the C3 core).**  If `checkInfeasCert ic` passes AND every
listed premise is a sound `≤ 0` fact on the path (`hprems` — the
Obligations-level premise-binding hypothesis, delta D5), then NO sample satisfies
`path`: the path box is empty.

Routed through `Bridge.lean`'s kernel-checked Farkas core
`farkas_premise_combination` with `out := 0` and `c := −toQ ic.kappa`: the
certificate identity (`∑ μᵢ·premFun premᵢ x = κ`, recovered from the residual
checks via `comb_decomp`) gives `∑ μᵢ·gᵢ = −(out) − c = κ`; premises `≤ 0` and
`μ ≥ 0` give the sum `≤ 0`, hence the core concludes `−c = κ ≤ out = 0`,
contradicting `κ > 0`. -/
theorem infeasCert_empties [DecidableEq Coord]
    (coord : Coord → (Coord → ℚ) → ℚ) (ic : InfeasCert Coord)
    (h : checkInfeasCert ic = true) (path : (Coord → ℚ) → Prop)
    (hprems : ∀ p ∈ ic.prems, ∀ x, path x → premFun coord p x ≤ 0) :
    ∀ x, ¬ path x := by
  intro x hx
  -- Unpack the checker.
  unfold checkInfeasCert at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hden, _hlen⟩, hμnn⟩, hκpos⟩, hzero, hconst⟩ := h
  obtain ⟨hpremwf, hmulwf, hκwf⟩ := allDenPos_wf ic hden
  -- The zipped pairs and their wf.
  set pairs := ic.prems.zip ic.mu with hpairs
  have hpairwf : ∀ p ∈ pairs, QPair.wf p.1.bound ∧ QPair.wf p.2 := by
    intro p hp
    rw [hpairs] at hp
    have hm := List.of_mem_zip hp
    exact ⟨hpremwf p.1 hm.1, hmulwf p.2 hm.2⟩
  -- (a) The coordinate residual vanishes for all y: evalC coord (combCoeffMap pairs) y = 0.
  have hcoeffwf : ∀ p ∈ combCoeffMap pairs, QPair.wf p.2 :=
    combCoeffMap_wf pairs (fun p hp => (hpairwf p hp).2)
  have hcoord0 : ∀ y, evalC coord (combCoeffMap pairs) y = 0 := by
    intro y
    rw [← evalC_collapseC coord (combCoeffMap pairs) hcoeffwf y]
    apply evalC_eq_zero_of_allZeroQ
    intro p hp
    exact isZeroZ_sound p.2 (hzero p hp)
  -- (b) The constant identity: toQ (combConst pairs) = toQ ic.kappa.
  have hconst0 : toQ (addZ (combConst pairs) (negZ ic.kappa)) = 0 := isZeroZ_sound _ hconst
  have hconstEq : toQ (combConst pairs) = toQ ic.kappa := by
    rw [toQ_addZ (combConst pairs) (negZ ic.kappa)
          (combConst_wf pairs hpairwf) (by unfold negZ QPair.wf; exact hκwf),
        toQ_negZ] at hconst0
    linarith
  -- Per-pair facts: μ ≥ 0 and (on the path) premFun ≤ 0, indexed by position.
  --   `pairs[i].2` is a multiplier (μ ≥ 0, wf), `pairs[i].1` a premise (≤ 0 on path).
  have hidx : ∀ i : Fin pairs.length,
      0 ≤ toQ pairs[i].2 ∧ (∀ y, path y → premFun coord pairs[i].1 y ≤ 0) := by
    intro i
    have hmem : pairs[i] ∈ pairs := List.getElem_mem _
    have hm : pairs[i].1 ∈ ic.prems ∧ pairs[i].2 ∈ ic.mu := List.of_mem_zip hmem
    have hwfμ : QPair.wf pairs[i].2 := hmulwf pairs[i].2 hm.2
    have hnn : 0 ≤ pairs[i].2.1 := hμnn pairs[i].2 hm.2
    refine ⟨?_, ?_⟩
    · unfold toQ
      have hd : (0 : ℚ) < (pairs[i].2.2 : ℚ) := by exact_mod_cast hwfμ
      have hn : (0 : ℚ) ≤ (pairs[i].2.1 : ℚ) := by exact_mod_cast hnn
      positivity
    · intro y hy; exact hprems pairs[i].1 hm.1 y hy
  -- The certificate identity (over the LIST):  ∑ μᵢ·premFun premᵢ y = κ  for all y.
  have hcertList : ∀ y, (pairs.map (fun p => toQ p.2 * premFun coord p.1 y)).sum
      = toQ ic.kappa := by
    intro y
    rw [comb_decomp coord pairs hpairwf y, hcoord0 y, hconstEq]; ring
  -- Bridge the LIST sum to the Bridge core's `Finset.univ`-over-`Fin` sum:
  --   pairs.map f  =  List.ofFn (fun i => f pairs[i]),  and its sum  =  ∑ i, f pairs[i].
  have hcertUniv : ∀ y,
      (∑ i : Fin pairs.length,
          toQ pairs[i].2 * premFun coord pairs[i].1 y) = toQ ic.kappa := by
    intro y
    have hbridge : (pairs.map (fun p => toQ p.2 * premFun coord p.1 y)).sum
        = ∑ i : Fin pairs.length, toQ pairs[i].2 * premFun coord pairs[i].1 y := by
      rw [← List.ofFn_getElem_eq_map pairs (fun p => toQ p.2 * premFun coord p.1 y),
          List.sum_ofFn]
      simp only [Fin.getElem_fin]
    rw [← hbridge]; exact hcertList y
  -- Route through the kernel-checked Farkas core (Bridge.lean), indexed by position.
  --   g i y := premFun coord pairs[i].1 y,  μ i := toQ pairs[i].2,  out := 0,  c := −κ.
  have hcore : ∀ y, path y → -(- toQ ic.kappa) ≤ ((fun _ => (0 : ℚ)) : (Coord → ℚ) → ℚ) y :=
    farkas_premise_combination
      (S := (Coord → ℚ)) (ι := Fin pairs.length)
      (premises := Finset.univ)
      (g := fun i y => premFun coord pairs[i].1 y)
      (out := fun _ => 0)
      (μ := fun i => toQ pairs[i].2)
      (c := - toQ ic.kappa)
      (valid := path)
      (fun i _ => (hidx i).1)
      (fun i _ y hy => (hidx i).2 y hy)
      (by
        intro y
        -- ∑ μ i * g i y = ∑ toQ pairs[i].2 * premFun ... = κ = -(0) - (-κ)
        have := hcertUniv y
        simp only []
        rw [this]; ring)
  -- κ > 0 contradicts κ = -c ≤ out = 0.
  have hκq : (0 : ℚ) < toQ ic.kappa := by
    unfold toQ
    have hd : (0 : ℚ) < (ic.kappa.2 : ℚ) := by exact_mod_cast hκwf
    have hn : (0 : ℚ) < (ic.kappa.1 : ℚ) := by exact_mod_cast hκpos
    positivity
  have := hcore x hx
  simp only [neg_neg] at this
  linarith

/-! ## 6. The extended branch-and-bound proof tree with PRUNED leaves.

A `BabProofP` composes THREE node kinds in one tree:

* `leaf  lc` — a frontier box closed by an inline CROWN margin certificate
  (`Bab.LeafCert`, margin ≥ 0), exactly as `Bab.BabProof.leaf`;
* `pruned ic` — a frontier box PROVEN EMPTY by a Farkas infeasibility certificate
  (`InfeasCert`), the new C3 leaf kind;
* `split c m lo hi` — bisect coordinate `c` at rational `m`; `lo` proves the
  `x_c ≤ m` half-box, `hi` the `x_c ≥ m` half-box (same covering as
  `Bab.BabProof.split`).

Samples are `Coord → ℚ` (a sample IS its coordinate readout), with the abstract
`coord : Coord → (Coord → ℚ) → ℚ` carried so `premFun` applies verbatim.  The
recursor `babtree_prune_sound` is proved by direct structural induction,
mirroring `Bab.safe_on_path` on the `leaf`/`split` arms and discharging `pruned`
by `infeasCert_empties` (an empty box is vacuously safe). -/

/-- The extended BaB proof tree with a pruned-leaf constructor. -/
inductive BabProofP (Coord : Type*) where
  | leaf   (lc : LeafCert)         : BabProofP Coord
  | pruned (ic : InfeasCert Coord) : BabProofP Coord
  | split  (c : Coord) (m : ℚ) (lo hi : BabProofP Coord) : BabProofP Coord

/-- The total, computable recursive checker.  `leaf` runs `Bab.checkLeafCert`;
    `pruned` runs `checkInfeasCert`; `split` recurses both children (covering is
    `le_total`, discharged once in the soundness proof).  All arithmetic is
    integer cross-multiplication ⇒ kernel-reducible by `decide`/`rfl`, NO
    `native_decide`. -/
def checkBabProofP [DecidableEq Coord] : BabProofP Coord → Bool
  | .leaf lc         => checkLeafCert lc
  | .pruned ic       => checkInfeasCert ic
  | .split _ _ lo hi => checkBabProofP lo && checkBabProofP hi

/-- The leaf obligation bridge for margin leaves: the checker passed AND the
    output equals the certified constant margin on this path (D5-style binding,
    identical to `Bab.checkLeafSafe`). -/
def leafSafeP (out : (Coord → ℚ) → ℚ) (lc : LeafCert) (path : (Coord → ℚ) → Prop) :
    Prop :=
  checkLeafCert lc = true ∧ (∀ s, path s → out s = toQ lc.margin)

/-- The pruned obligation bridge: the infeasibility checker passed AND every
    listed premise is a sound `≤ 0` fact on this path (the D5 premise-binding
    hypothesis, stated not hidden — same modelling discipline as `leafSafeP`'s
    second conjunct). -/
def pruneSafeP [DecidableEq Coord] (coord : Coord → (Coord → ℚ) → ℚ)
    (ic : InfeasCert Coord) (path : (Coord → ℚ) → Prop) : Prop :=
  checkInfeasCert ic = true ∧
    (∀ p ∈ ic.prems, ∀ s, path s → premFun coord p s ≤ 0)

/-- The per-node proof obligation, relative to a path predicate, with the pruned
    arm.  Parallels `Bab.Obligations` exactly, plus the `pruned` case. -/
def ObligationsP [DecidableEq Coord] (coord : Coord → (Coord → ℚ) → ℚ)
    (out : (Coord → ℚ) → ℚ) :
    BabProofP Coord → ((Coord → ℚ) → Prop) → Prop
  | .leaf lc, path        => leafSafeP out lc path
  | .pruned ic, path      => pruneSafeP coord ic path
  | .split c m lo hi, path =>
      ObligationsP coord out lo (fun s => path s ∧ coord c s ≤ m) ∧
      ObligationsP coord out hi (fun s => path s ∧ m ≤ coord c s)

/--
**The pruned recursor's soundness.**  Fix `Safe s := 0 ≤ out s`.  If
`checkBabProofP p = true` AND the tree's `ObligationsP` hold along the root region
`inRegion`, then `0 ≤ out s` on the whole root box.

Margin leaves are discharged by `Bab.checkLeafCert_margin_nonneg` (margin ≥ 0 ⇒
output ≥ 0); PRUNED leaves are discharged by `infeasCert_empties` (the path box is
empty, so `0 ≤ out s` holds vacuously); splits reuse the SAME `le_total` covering
as `Bab.safe_on_path`.  Pruned leaves are admitted as empty-box contributions: the
adaptive/decisive-depth Δdomains theorems go through with them counted. -/
theorem babtree_prune_sound [DecidableEq Coord]
    (coord : Coord → (Coord → ℚ) → ℚ) (out : (Coord → ℚ) → ℚ)
    (inRegion : (Coord → ℚ) → Prop) (p : BabProofP Coord)
    (hchk : checkBabProofP p = true)
    (hob : ObligationsP coord out p inRegion) :
    ∀ s, inRegion s → 0 ≤ out s := by
  induction p generalizing inRegion with
  | leaf lc =>
      intro s hs
      obtain ⟨hcheck, hval⟩ := hob
      have hmargin : (0 : ℚ) ≤ toQ lc.margin := checkLeafCert_margin_nonneg lc hcheck
      rw [hval s hs]; exact hmargin
  | pruned ic =>
      intro s hs
      obtain ⟨hcheck, hprems⟩ := hob
      -- the path box is empty: no sample reaches this leaf, so the goal is vacuous
      exact absurd hs (infeasCert_empties coord ic hcheck inRegion hprems s)
  | split c m lo hi ihlo ihhi =>
      intro s hs
      obtain ⟨hoblo, hobhi⟩ := hob
      simp only [checkBabProofP, Bool.and_eq_true] at hchk
      obtain ⟨hchklo, hchkhi⟩ := hchk
      rcases le_total (coord c s) m with hle | hge
      · exact ihlo _ hchklo hoblo s ⟨hs, hle⟩
      · exact ihhi _ hchkhi hobhi s ⟨hs, hge⟩

/-! ## 7. Exact pruned-domain count (Δdomains-class, composes with C1's identity). -/

/-- The number of PRUNED leaves in a tree — an exactly-counted Δdomains-class
    integer (each pruned leaf removes a whole subtree the uniform tree would
    carry), composable with C1's `length`/`prunedCount = 2^d` identity. -/
def prunedLeafCount : BabProofP Coord → ℕ
  | .leaf _          => 0
  | .pruned _        => 1
  | .split _ _ lo hi => prunedLeafCount lo + prunedLeafCount hi

/-! ## 8. TINY DEMONSTRATION — a depth-1 tree with a PRUNED right child, by `decide`.

`Coord = Unit`, `coord _ x = x ()` (the sample is its one rational coordinate),
`out s = 1`.  The ROOT region carries the accumulated premise `x ≤ 0`; the tree
splits the coordinate at `1`.  The LEFT child path `x ≤ 0 ∧ x ≤ 1` is closed by a
unit-margin leaf.  The RIGHT child path `x ≤ 0 ∧ 1 ≤ x` is PRUNED: on it BOTH
infeasibility-cert premises hold (`x ≤ 0` from the region, `x ≥ 1` from the
split), and the certificate

    1·(x − 0) + 1·(−x − (−1)) = x − x + 1 = 1 = κ > 0

shows the μ-combination of two `≤ 0` premises equals `1 > 0` — impossible, so the
box is empty.  `checkInfeasCert` accepts the cert by `decide`, and
`babtree_prune_sound` then composes the margin leaf and the pruned leaf into a
whole-box bound on the root region `x ≤ 0`. -/

/-- The two contradictory path premises `x ≤ 0` and `x ≥ 1` over `Coord = Unit`.
    `x ≤ 0`:  `sign=+1`, `bound=(0,1)`  (i.e. `+x − 0 ≤ 0`).
    `x ≥ 1` :  `sign=−1`, `bound=(-1,1)` (i.e. `−x − (−1) ≤ 0`, i.e. `1 − x ≤ 0`). -/
def demoPrems : List (BoxPrem Unit) :=
  [⟨(), 1, (0, 1)⟩, ⟨(), -1, (-1, 1)⟩]

/-- The infeasibility cert: multipliers `1,1` and constant `κ = 1`. -/
def demoInfeasCert : InfeasCert Unit :=
  { prems := demoPrems, mu := [(1, 1), (1, 1)], kappa := (1, 1) }

/-- The kernel ACCEPTS the demo infeasibility certificate — verified by `decide`
    (all integer comparisons + the residual fold reduce). -/
theorem demoInfeasCert_checks : checkInfeasCert demoInfeasCert = true := by decide

/-- The demo coordinate readout: the sample IS its single rational coordinate. -/
def demoCoord : Unit → (Unit → ℚ) → ℚ := fun _ x => x ()

/-- The demo path box `x ≤ 0 ∧ x ≥ 1` (the accumulated contradictory premises). -/
def demoPath : (Unit → ℚ) → Prop := fun x => x () ≤ 0 ∧ 1 ≤ x ()

/--
**The pruned box is empty.**  Because `checkInfeasCert demoInfeasCert = true`
(`demoInfeasCert_checks`, by `decide`) and the two premises are sound `≤ 0` facts
on `demoPath` (discharged below), `infeasCert_empties` proves NO sample satisfies
`demoPath`: the domain is pruned with a kernel-checkable certificate. -/
theorem demoPath_empty : ∀ x : Unit → ℚ, ¬ demoPath x := by
  refine infeasCert_empties demoCoord demoInfeasCert demoInfeasCert_checks demoPath ?_
  -- the two premises are sound ≤ 0 facts on the path
  intro p hp x hx
  obtain ⟨hle, hge⟩ := hx
  simp only [demoInfeasCert, demoPrems, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with hp | hp
  · -- premise `+x − 0 ≤ 0`, i.e. `x ≤ 0`
    subst hp; unfold premFun demoCoord toQ; norm_num; linarith
  · -- premise `−x − (−1) ≤ 0`, i.e. `1 − x ≤ 0`
    subst hp; unfold premFun demoCoord toQ; norm_num; linarith

/-- A concrete depth-1 `BabProofP` over `Unit`: split the coordinate at `1`, left
    child a unit-margin leaf, RIGHT child PRUNED by `demoInfeasCert`.  Used under
    the root region `x () ≤ 0`, so the right path carries BOTH cert premises
    (`x () ≤ 0` from the region, `x () ≥ 1` from the split). -/
def prunedTree : BabProofP Unit :=
  .split () 1 (.leaf ⟨(1, 1)⟩) (.pruned demoInfeasCert)

/-- The recursive checker ACCEPTS the tree composing a margin leaf and a pruned
    leaf — verified by the KERNEL via `decide`. -/
theorem prunedTree_checks : checkBabProofP prunedTree = true := by decide

/-- The demo output functional: the constant unit margin `1`. -/
def prunedOut : (Unit → ℚ) → ℚ := fun _ => 1

/-- The demo root region: the accumulated premise `x ≤ 0`. -/
def prunedRegion : (Unit → ℚ) → Prop := fun x => x () ≤ 0

/-- This tree prunes exactly ONE domain. -/
theorem prunedTree_prunedLeafCount : prunedLeafCount prunedTree = 1 := by decide

/--
**End-to-end tiny pruned decision.**  Because `checkBabProofP prunedTree = true`
(`prunedTree_checks`, by `decide`), the recursor `babtree_prune_sound` yields
`0 ≤ prunedOut s` on the WHOLE root region `prunedRegion` (`x () ≤ 0`).  The RIGHT
child is a PRUNED leaf: its path box `x () ≤ 0 ∧ 1 ≤ x ()` carries both
infeasibility-cert premises and is proven EMPTY by `infeasCert_empties`, so it is
vacuously safe and counts as one pruned Δdomains contribution.  This is the
depth-1 instance of the kernel-internal BaB recursor WITH infeasible-domain
pruning: a split, one decidable margin leaf, one decidable PRUNED leaf, composed
by `le_total` covering into a whole-box bound. -/
theorem prunedTree_safe : ∀ s : Unit → ℚ, prunedRegion s → 0 ≤ prunedOut s := by
  refine babtree_prune_sound demoCoord prunedOut prunedRegion prunedTree
    prunedTree_checks ?_
  -- discharge the two obligations: left margin leaf + right pruned leaf
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · -- left leaf: checkLeafCert ⟨(1,1)⟩ = true
    decide
  · -- left leaf: prunedOut s = toQ ⟨(1,1)⟩.margin  (1 = 1/1)
    intro s _; unfold prunedOut toQ; norm_num
  · -- right pruned leaf: checkInfeasCert demoInfeasCert = true
    exact demoInfeasCert_checks
  · -- right pruned leaf: each cert premise is ≤ 0 on the right path
    --   right path:  prunedRegion s ∧ 1 ≤ coord () s,  i.e.  s () ≤ 0 ∧ 1 ≤ s ()
    intro p hp s hs
    obtain ⟨hreg, hge⟩ := hs
    have hle : s () ≤ 0 := hreg          -- from the root region `x ≤ 0`
    have hge' : (1 : ℚ) ≤ s () := hge    -- from the split `1 ≤ coord () s`
    simp only [demoInfeasCert, demoPrems, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with hp | hp
    · -- premise `+x − 0 ≤ 0`, i.e. `x ≤ 0` (holds by the region)
      subst hp; unfold premFun demoCoord toQ; norm_num; linarith
    · -- premise `−x − (−1) ≤ 0`, i.e. `1 − x ≤ 0` (holds by the split)
      subst hp; unfold premFun demoCoord toQ; norm_num; linarith

/-! ## Trust-base check.  Must list only the three standard logical axioms
    `[propext, Classical.choice, Quot.sound]`. -/

#print axioms infeasCert_empties
#print axioms babtree_prune_sound
#print axioms demoInfeasCert_checks
#print axioms demoPath_empty
#print axioms prunedTree_checks
#print axioms prunedTree_prunedLeafCount
#print axioms prunedTree_safe

end InventionWave4
end Crownproof
