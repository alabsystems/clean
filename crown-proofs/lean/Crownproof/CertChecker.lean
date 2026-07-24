/-
Copyright 2026 Andrew Yates
SPDX-License-Identifier: Apache-2.0

A LEAN-KERNEL-VERIFIED entailment certificate checker.

This is the module that closes the LAST trust gap in the whole-box ACAS prop_1
decision (`acas_wholebox_decision`).  Previously each leaf's safety was taken as
a HYPOTHESIS, discharged externally by the Rust `clean-extcert-verify` kernel
(`verify.rs::verify_entailment_certificate`).  Here we:

  1. define a `Cert` structure that holds the certificate AS DATA
     (premises = list of linear constraints, multipliers = list of ℚ,
      conclusion = a linear constraint giving the claimed bound);

  2. define a Boolean `checkEntailment : Cert → Bool` that MIRRORS verify.rs:
       * every multiplier ≥ 0,
       * the multiplier-weighted combination of the premises (each normalized to
         `coeffs·x ≤ const` form) has, after subtracting the normalized
         conclusion's coefficient map, ALL coefficients equal to 0
         (i.e. the derived linear functional equals the conclusion functional),
       * the derived bound implies the claimed bound;

  3. PROVE `checkEntailment_sound`:  `checkEntailment c = true` implies that for
     EVERY assignment `σ : String → ℚ` satisfying all premises, the conclusion
     constraint holds.  This is the Farkas argument, reusing
     `Crownproof.farkas_premise_combination`.

`#print axioms checkEntailment_sound` must report exactly
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no `native_decide`.
-/
import Crownproof.Bridge
import Mathlib.Tactic.Ring

namespace Crownproof
namespace CertChecker

open Crownproof

/-! ## 1. Data model: linear constraints, assignments, certificates. -/

/-- The three constraint relations we support (mirroring verify.rs `Le/Ge/Eq`;
    `Lt/Gt` are not produced by the CROWN emitter so we omit them — equality and
    the two non-strict inequalities are exactly what the leaf certs use). -/
inductive Kind where
  | le   -- coeffs · x ≤ const
  | ge   -- coeffs · x ≥ const
  | eq   -- coeffs · x = const
deriving DecidableEq, Repr

/-- A linear constraint `coeffs · x  (rel)  const`, with `coeffs` an association
    list from variable name to coefficient. -/
structure LinearConstraint where
  coeffs : List (String × ℚ)
  kind   : Kind
  const  : ℚ
deriving Repr

/-- An assignment of rational values to variables. -/
abbrev Assignment := String → ℚ

/-- The value of a coefficient map (association list) under an assignment:
    `Σ (v,c) ∈ m, c * σ v`.  This is the canonical "linear functional" of `m`. -/
def evalMap (m : List (String × ℚ)) (σ : Assignment) : ℚ :=
  (m.map (fun p => p.2 * σ p.1)).sum

/-- The left-hand-side value of a constraint under an assignment. -/
def LinearConstraint.lhs (lc : LinearConstraint) (σ : Assignment) : ℚ :=
  evalMap lc.coeffs σ

/-- Does the assignment satisfy the constraint (its declared relation)? -/
def LinearConstraint.satisfies (lc : LinearConstraint) (σ : Assignment) : Prop :=
  match lc.kind with
  | .le => lc.lhs σ ≤ lc.const
  | .ge => lc.const ≤ lc.lhs σ
  | .eq => lc.lhs σ = lc.const

/-- An entailment certificate, as DATA. -/
structure Cert where
  premises    : List LinearConstraint
  multipliers : List ℚ
  conclusion  : LinearConstraint
deriving Repr

/-! ## 2. Map algebra used by the checker, with evaluation lemmas. -/

/-- Scale every coefficient of a map by `k`. -/
def scaleMap (k : ℚ) (m : List (String × ℚ)) : List (String × ℚ) :=
  m.map (fun p => (p.1, k * p.2))

/-- Negate every coefficient of a map. -/
def negMap (m : List (String × ℚ)) : List (String × ℚ) :=
  m.map (fun p => (p.1, - p.2))

/-- Concatenation = pointwise sum of the two linear functionals. -/
theorem evalMap_append (m₁ m₂ : List (String × ℚ)) (σ : Assignment) :
    evalMap (m₁ ++ m₂) σ = evalMap m₁ σ + evalMap m₂ σ := by
  unfold evalMap
  rw [List.map_append, List.sum_append]

/-- `evalMap` on a cons unfolds to head term plus tail. -/
theorem evalMap_cons (hd : String × ℚ) (tl : List (String × ℚ)) (σ : Assignment) :
    evalMap (hd :: tl) σ = hd.2 * σ hd.1 + evalMap tl σ := by
  simp [evalMap]

@[simp] theorem evalMap_nil (σ : Assignment) : evalMap [] σ = 0 := by
  simp [evalMap]

/-- Scaling a map scales its functional. -/
theorem evalMap_scaleMap (k : ℚ) (m : List (String × ℚ)) (σ : Assignment) :
    evalMap (scaleMap k m) σ = k * evalMap m σ := by
  induction m with
  | nil => simp [scaleMap]
  | cons hd tl ih =>
    have h1 : scaleMap k (hd :: tl) = (hd.1, k * hd.2) :: scaleMap k tl := by
      simp [scaleMap]
    rw [h1, evalMap_cons, evalMap_cons, ih]
    ring

/-- Negating a map negates its functional. -/
theorem evalMap_negMap (m : List (String × ℚ)) (σ : Assignment) :
    evalMap (negMap m) σ = - evalMap m σ := by
  induction m with
  | nil => simp [negMap]
  | cons hd tl ih =>
    have h1 : negMap (hd :: tl) = (hd.1, - hd.2) :: negMap tl := by
      simp [negMap]
    rw [h1, evalMap_cons, evalMap_cons, ih]
    ring

/-- A map whose every coefficient is `0` has functional value `0`. -/
theorem evalMap_eq_zero_of_allZero (m : List (String × ℚ)) (σ : Assignment)
    (h : ∀ p ∈ m, p.2 = 0) : evalMap m σ = 0 := by
  induction m with
  | nil => simp
  | cons hd tl ih =>
    rw [evalMap_cons, h hd (List.mem_cons_self ..),
        ih (fun p hp => h p (List.mem_cons_of_mem _ hp))]
    ring

/-! ## 2b. Collapsing a coefficient map by variable.

verify.rs uses a `BTreeMap` keyed by variable, so contributions to the SAME
variable from different premises are summed.  Our association-list representation
keeps them as separate entries, so to mirror the "coefficients cancel" test we
first `collapse` the map: fold left, adding each entry's coefficient into the
accumulator's entry for that variable (or appending a new entry).  This is
evaluation-preserving, so the all-coefficients-zero test on the collapsed map is
a SOUND witness that the linear functional is identically zero. -/

/-- Add coefficient `c` for variable `v` into an association list, summing into an
    existing entry if present, else appending. -/
def addEntry : List (String × ℚ) → String → ℚ → List (String × ℚ)
  | [], v, c => [(v, c)]
  | (w, d) :: rest, v, c =>
      if v = w then (w, d + c) :: rest
      else (w, d) :: addEntry rest v c

/-- `addEntry` adds `c * σ v` to the functional value. -/
theorem evalMap_addEntry (acc : List (String × ℚ)) (v : String) (c : ℚ)
    (σ : Assignment) :
    evalMap (addEntry acc v c) σ = evalMap acc σ + c * σ v := by
  induction acc with
  | nil =>
    show evalMap [(v, c)] σ = evalMap [] σ + c * σ v
    rw [evalMap_cons, evalMap_nil]
    ring
  | cons hd tl ih =>
    obtain ⟨w, d⟩ := hd
    by_cases hvw : v = w
    · subst hvw
      have he : addEntry ((v, d) :: tl) v c = (v, d + c) :: tl := by
        show (if v = v then (v, d + c) :: tl else (v, d) :: addEntry tl v c)
              = (v, d + c) :: tl
        rw [if_pos rfl]
      rw [he, evalMap_cons, evalMap_cons]
      ring
    · have he : addEntry ((w, d) :: tl) v c = (w, d) :: addEntry tl v c := by
        show (if v = w then (w, d + c) :: tl else (w, d) :: addEntry tl v c)
              = (w, d) :: addEntry tl v c
        rw [if_neg hvw]
      rw [he, evalMap_cons, evalMap_cons, ih]
      ring

/-- Collapse a coefficient map: sum contributions per variable. -/
def collapse (m : List (String × ℚ)) : List (String × ℚ) :=
  m.foldl (fun acc p => addEntry acc p.1 p.2) []

/-- Folding `addEntry` from a nonempty accumulator preserves the functional sum
    `evalMap acc σ + evalMap m σ`. -/
theorem evalMap_foldl_addEntry (m : List (String × ℚ)) (σ : Assignment) :
    ∀ acc : List (String × ℚ),
      evalMap (m.foldl (fun a p => addEntry a p.1 p.2) acc) σ
        = evalMap acc σ + evalMap m σ := by
  induction m with
  | nil => intro acc; simp
  | cons hd tl ih =>
    intro acc
    obtain ⟨v, c⟩ := hd
    simp only [List.foldl_cons]
    rw [ih (addEntry acc v c), evalMap_addEntry, evalMap_cons]
    ring

/-- `collapse` preserves the linear functional. -/
theorem evalMap_collapse (m : List (String × ℚ)) (σ : Assignment) :
    evalMap (collapse m) σ = evalMap m σ := by
  unfold collapse
  rw [evalMap_foldl_addEntry m σ []]
  simp

/-! ## 3. Normalization to `coeffs · x ≤ const` form (mirroring verify.rs).

verify.rs normalizes each constraint into one or more `coeffs·x ≤ const` rows:
  * `le`:  identity;
  * `ge`:  negate coeffs and const  (`a·x ≥ b`  ↔  `-a·x ≤ -b`);
  * `eq`:  TWO rows, the `le` part and the `ge`-negated part.
We mirror this exactly.  A normalized constraint is just a `(coeffs, const)` pair
with the implicit meaning `coeffs · x ≤ const`. -/

/-- Normalize a constraint to a list of `(coeffs, const)` rows meaning
    `coeffs · x ≤ const`.  Identical decomposition to verify.rs. -/
def normalize (lc : LinearConstraint) : List (List (String × ℚ) × ℚ) :=
  match lc.kind with
  | .le => [(lc.coeffs, lc.const)]
  | .ge => [(negMap lc.coeffs, - lc.const)]
  | .eq => [(lc.coeffs, lc.const), (negMap lc.coeffs, - lc.const)]

/-- Soundness of normalization: if the assignment satisfies the constraint, then
    every normalized row `(c, b)` satisfies `evalMap c σ ≤ b`. -/
theorem normalize_sound (lc : LinearConstraint) (σ : Assignment)
    (h : lc.satisfies σ) :
    ∀ row ∈ normalize lc, evalMap row.1 σ ≤ row.2 := by
  unfold LinearConstraint.satisfies at h
  unfold normalize
  cases hk : lc.kind with
  | le =>
    rw [hk] at h
    intro row hrow
    simp only [List.mem_singleton] at hrow
    subst hrow
    exact h
  | ge =>
    rw [hk] at h
    intro row hrow
    simp only [List.mem_singleton] at hrow
    subst hrow
    simp only [evalMap_negMap]
    have : lc.lhs σ = evalMap lc.coeffs σ := rfl
    rw [this] at h
    linarith
  | eq =>
    rw [hk] at h
    have hlhs : lc.lhs σ = evalMap lc.coeffs σ := rfl
    rw [hlhs] at h
    intro row hrow
    rcases List.mem_cons.mp hrow with hrow | hrow
    · subst hrow; simp only []; linarith
    · rcases List.mem_singleton.mp hrow with hrow
      subst hrow; simp only [evalMap_negMap]; linarith

/-! ## 4. The multiplier-weighted combination of normalized premises.

For one `(premise, μ)` pair we scale every normalized row of the premise by `μ`
and concatenate the coefficient maps; the constants are likewise `μ`-weighted and
summed.  We then fold this over the whole `(premises, multipliers)` zip. -/

/-- Coefficient map contributed by a single `(premise, μ)` pair:
    concatenate `scaleMap μ row.1` over all normalized rows of the premise. -/
def rowCoeffs (μ : ℚ) (lc : LinearConstraint) : List (String × ℚ) :=
  ((normalize lc).map (fun row => scaleMap μ row.1)).flatten

/-- Constant contributed by a single `(premise, μ)` pair:
    `Σ rows, μ * row.2`. -/
def rowConst (μ : ℚ) (lc : LinearConstraint) : ℚ :=
  ((normalize lc).map (fun row => μ * row.2)).sum

/-- Combined coefficient map of the whole certificate: concatenate the per-pair
    coefficient maps over the `(premises, multipliers)` zip. -/
def combCoeffs : List (LinearConstraint × ℚ) → List (String × ℚ)
  | [] => []
  | (lc, μ) :: rest => rowCoeffs μ lc ++ combCoeffs rest

/-- Combined constant of the whole certificate. -/
def combConst : List (LinearConstraint × ℚ) → ℚ
  | [] => 0
  | (lc, μ) :: rest => rowConst μ lc + combConst rest

/-- Evaluation of one pair's coefficient map equals `μ · Σ_rows evalMap row.1`. -/
theorem evalMap_rowCoeffs (μ : ℚ) (lc : LinearConstraint) (σ : Assignment) :
    evalMap (rowCoeffs μ lc) σ
      = ((normalize lc).map (fun row => μ * evalMap row.1 σ)).sum := by
  unfold rowCoeffs
  induction (normalize lc) with
  | nil => simp [evalMap]
  | cons hd tl ih =>
    simp only [List.map_cons, List.flatten_cons, List.sum_cons]
    rw [evalMap_append, evalMap_scaleMap, ih]

/-- The Farkas bound for ONE pair: if `μ ≥ 0` and the assignment satisfies the
    premise, then `evalMap (rowCoeffs μ lc) σ ≤ rowConst μ lc`.

    Generalized over an arbitrary list of normalized rows each of which is a
    sound `evalMap row.1 σ ≤ row.2`, so the induction is clean. -/
theorem weighted_rows_le (μ : ℚ) (σ : Assignment) (hμ : 0 ≤ μ)
    (rows : List (List (String × ℚ) × ℚ))
    (hrows : ∀ row ∈ rows, evalMap row.1 σ ≤ row.2) :
    (rows.map (fun row => μ * evalMap row.1 σ)).sum
      ≤ (rows.map (fun row => μ * row.2)).sum := by
  induction rows with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons]
    have hhd : evalMap hd.1 σ ≤ hd.2 := hrows hd (List.mem_cons_self ..)
    have hhead : μ * evalMap hd.1 σ ≤ μ * hd.2 := mul_le_mul_of_nonneg_left hhd hμ
    have htail := ih (fun row hr => hrows row (List.mem_cons_of_mem _ hr))
    linarith

/-- The Farkas bound for ONE pair. -/
theorem rowCoeffs_le_rowConst (μ : ℚ) (lc : LinearConstraint) (σ : Assignment)
    (hμ : 0 ≤ μ) (hsat : lc.satisfies σ) :
    evalMap (rowCoeffs μ lc) σ ≤ rowConst μ lc := by
  rw [evalMap_rowCoeffs]
  unfold rowConst
  exact weighted_rows_le μ σ hμ (normalize lc) (normalize_sound lc σ hsat)

/-- Evaluation of the whole combined coefficient map equals the sum, over all
    pairs, of the per-pair evaluations. -/
theorem evalMap_combCoeffs (pairs : List (LinearConstraint × ℚ)) (σ : Assignment) :
    evalMap (combCoeffs pairs) σ
      = (pairs.map (fun p => evalMap (rowCoeffs p.2 p.1) σ)).sum := by
  induction pairs with
  | nil => simp [combCoeffs, evalMap]
  | cons hd tl ih =>
    obtain ⟨lc, μ⟩ := hd
    simp only [combCoeffs, List.map_cons, List.sum_cons]
    rw [evalMap_append, ih]

/-- The Farkas bound for the WHOLE combination: if every multiplier is ≥ 0 and
    the assignment satisfies every premise, then the combined functional value is
    ≤ the combined constant. -/
theorem comb_le (pairs : List (LinearConstraint × ℚ)) (σ : Assignment)
    (hμ : ∀ p ∈ pairs, 0 ≤ p.2)
    (hsat : ∀ p ∈ pairs, p.1.satisfies σ) :
    evalMap (combCoeffs pairs) σ ≤ combConst pairs := by
  rw [evalMap_combCoeffs]
  induction pairs with
  | nil => simp [combConst]
  | cons hd tl ih =>
    obtain ⟨lc, μ⟩ := hd
    simp only [List.map_cons, List.sum_cons, combConst]
    have hhd : evalMap (rowCoeffs μ lc) σ ≤ rowConst μ lc :=
      rowCoeffs_le_rowConst μ lc σ
        (hμ (lc, μ) (List.mem_cons_self ..))
        (hsat (lc, μ) (List.mem_cons_self ..))
    have htail :
        (tl.map (fun p => evalMap (rowCoeffs p.2 p.1) σ)).sum ≤ combConst tl :=
      ih (fun p hp => hμ p (List.mem_cons_of_mem _ hp))
         (fun p hp => hsat p (List.mem_cons_of_mem _ hp))
    linarith

/-! ## 5. The Boolean checker `checkEntailment` (mirrors verify.rs). -/

/-- The conclusion of an entailment cert is normalized to a SINGLE `≤` row
    (verify.rs rejects equality conclusions; a `ge`/`le` conclusion gives one
    row).  Returns `none` if the conclusion is an equality (unsupported). -/
def normalizeConclusion (lc : LinearConstraint) : Option (List (String × ℚ) × ℚ) :=
  match lc.kind with
  | .le => some (lc.coeffs, lc.const)
  | .ge => some (negMap lc.coeffs, - lc.const)
  | .eq => none

/-- Build the difference map  `combCoeffs ++ negMap conclCoeffs`.  When every
    coefficient of this list is `0`, the combined functional equals the
    conclusion functional (as functions of every assignment). -/
def diffMap (pairs : List (LinearConstraint × ℚ))
    (conclCoeffs : List (String × ℚ)) : List (String × ℚ) :=
  combCoeffs pairs ++ negMap conclCoeffs

/-- `checkEntailment` mirrors `verify.rs::verify_entailment_certificate`:
    * lengths of premises and multipliers agree;
    * every multiplier is ≥ 0;
    * the conclusion is not an equality (normalizes to one `≤` row);
    * the derived coefficient functional equals the conclusion functional, i.e.
      every coefficient of `combCoeffs ⊖ conclCoeffs` is 0;
    * the derived bound `combConst` implies the claimed bound `conclConst`
      (`combConst ≤ conclConst`, the non-strict case — all our rows are
       non-strict). -/
def checkEntailment (c : Cert) : Bool :=
  c.premises.length == c.multipliers.length &&
  c.multipliers.all (fun μ => decide (0 ≤ μ)) &&
  (match normalizeConclusion c.conclusion with
   | none => false
   | some (conclCoeffs, conclConst) =>
       let pairs := c.premises.zip c.multipliers
       (collapse (diffMap pairs conclCoeffs)).all (fun p => decide (p.2 = 0)) &&
       decide (combConst pairs ≤ conclConst))

/-! ## 6. Soundness of the checker (the Farkas theorem). -/

/-- If every coefficient of `diffMap pairs conclCoeffs` is `0`, then for every
    assignment the combined functional equals the conclusion functional. -/
theorem combCoeffs_eval_eq_concl
    (pairs : List (LinearConstraint × ℚ)) (conclCoeffs : List (String × ℚ))
    (hzero : ∀ p ∈ collapse (diffMap pairs conclCoeffs), p.2 = 0) (σ : Assignment) :
    evalMap (combCoeffs pairs) σ = evalMap conclCoeffs σ := by
  -- the collapsed diff map evaluates to 0 (all its coefficients are 0) ...
  have h0c : evalMap (collapse (diffMap pairs conclCoeffs)) σ = 0 :=
    evalMap_eq_zero_of_allZero _ σ hzero
  -- ... and collapse preserves the functional, so the raw diff map is 0 too.
  rw [evalMap_collapse] at h0c
  unfold diffMap at h0c
  rw [evalMap_append, evalMap_negMap] at h0c
  linarith

/--
**Soundness of `checkEntailment`.**

If `checkEntailment c = true`, then for EVERY assignment `σ` satisfying all the
premises of `c`, the conclusion constraint holds (`c.conclusion.satisfies σ`).

This is the Farkas / entailment argument.  The leaf safety obtained this way is a
LEAN-KERNEL theorem — it depends only on this proof (and `farkas`-style
ordered-field reasoning), NOT on the external Rust checker. -/
theorem checkEntailment_sound (c : Cert)
    (hchk : checkEntailment c = true) :
    ∀ σ : Assignment,
      (∀ lc ∈ c.premises, lc.satisfies σ) → c.conclusion.satisfies σ := by
  intro σ hprem
  -- Unpack the four conjuncts of the Boolean check.
  unfold checkEntailment at hchk
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨hlen, hμpos⟩, hrest⟩ := hchk
  -- The conclusion must normalize (not an equality).
  revert hrest
  cases hk : normalizeConclusion c.conclusion with
  | none => intro h; simp at h
  | some cc =>
    obtain ⟨conclCoeffs, conclConst⟩ := cc
    intro hrest
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hrest
    obtain ⟨hdiff, hbound⟩ := hrest
    set pairs := c.premises.zip c.multipliers with hpairs_def
    -- (a) every pair multiplier ≥ 0 and every pair premise is satisfied,
    --     because pairs is a zip of premises with multipliers.
    have hpair_mem : ∀ p ∈ pairs, p.1 ∈ c.premises ∧ p.2 ∈ c.multipliers := by
      intro p hp
      rw [hpairs_def] at hp
      have := List.of_mem_zip hp
      exact this
    have hμpairs : ∀ p ∈ pairs, 0 ≤ p.2 := by
      intro p hp
      exact hμpos p.2 ((hpair_mem p hp).2)
    have hsatpairs : ∀ p ∈ pairs, p.1.satisfies σ := by
      intro p hp
      exact hprem p.1 ((hpair_mem p hp).1)
    -- (b) Farkas bound on the combination.
    have hcomb := comb_le pairs σ hμpairs hsatpairs
    -- (c) the combined functional equals the conclusion functional.
    have hfun : evalMap (combCoeffs pairs) σ = evalMap conclCoeffs σ :=
      combCoeffs_eval_eq_concl pairs conclCoeffs hdiff σ
    -- (d) put it together:  evalMap conclCoeffs σ ≤ combConst ≤ conclConst.
    rw [hfun] at hcomb
    have hchain : evalMap conclCoeffs σ ≤ conclConst := le_trans hcomb hbound
    -- (e) translate back to the conclusion's declared relation.
    unfold normalizeConclusion at hk
    have hlhs : c.conclusion.lhs σ = evalMap c.conclusion.coeffs σ := rfl
    cases hck : c.conclusion.kind with
    | le =>
      rw [hck] at hk
      simp only [Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨hcoe, hcon⟩ := hk
      -- hcoe : c.conclusion.coeffs = conclCoeffs ; hcon : c.conclusion.const = conclConst
      -- rewrite hchain back into the conclusion's own fields
      rw [← hcoe, ← hcon] at hchain
      -- goal:  c.conclusion.satisfies σ
      have hgoal : c.conclusion.lhs σ ≤ c.conclusion.const := by rw [hlhs]; exact hchain
      simp only [LinearConstraint.satisfies, hck]
      exact hgoal
    | ge =>
      rw [hck] at hk
      simp only [Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨hcoe, hcon⟩ := hk
      -- hcoe : negMap c.conclusion.coeffs = conclCoeffs ; hcon : - c.conclusion.const = conclConst
      rw [← hcoe, ← hcon, evalMap_negMap] at hchain
      -- hchain : - evalMap c.conclusion.coeffs σ ≤ - c.conclusion.const
      have hgoal : c.conclusion.const ≤ c.conclusion.lhs σ := by rw [hlhs]; linarith
      simp only [LinearConstraint.satisfies, hck]
      exact hgoal
    | eq =>
      rw [hck] at hk
      exact absurd hk (by simp)

/-! ## 7. Trust-base check for the checker + its soundness theorem. -/

#print axioms evalMap_scaleMap
#print axioms normalize_sound
#print axioms comb_le
#print axioms checkEntailment_sound

end CertChecker
end Crownproof
