/-
Copyright 2026 Andrew Yates
SPDX-License-Identifier: Apache-2.0

KERNEL-RUNNABLE integer-pair entailment checker.

`Crownproof.CertChecker.checkEntailment` is the verified SPEC over ℚ.  But ℚ
arithmetic on the bignum leaf certs cannot be reduced by the Lean kernel
(`Rat` normalization calls `Nat.gcd`, which is not GMP-accelerated and would take
astronomically long on 800-bit denominators).  `Int`/`Nat` arithmetic, by
contrast, IS GMP-backed in the kernel and reduces instantly.

So here we give an EXECUTABLE checker `checkEntailmentZ` whose numbers are
unreduced integer pairs `(num, den)` with `den > 0`, and whose every comparison
is integer cross-multiplication — fully kernel-reducible by `decide`/`rfl`,
NO `native_decide`.  We then prove it SOUND directly against the ℚ Farkas core
`Crownproof.farkas_premise_combination` (via the homomorphism `toQ (n,d) = n/d`).

The result: for a REAL ACAS whole-box leaf cert parsed into a `CertZ`, evaluating
`checkEntailmentZ cz = true` by the kernel and then applying
`checkEntailmentZ_sound` yields the leaf-safety statement as a LEAN THEOREM.
-/
import Crownproof.CertChecker
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push

namespace Crownproof
namespace CertCheckerZ

open Crownproof
open Crownproof.CertChecker

/-! ## 1. Integer-pair rationals `(num, den)`, `den > 0`, with the map to ℚ. -/

/-- An unreduced rational as an integer numerator/denominator pair. -/
abbrev QPair := ℤ × ℤ

/-- Interpret an integer pair as a rational `num / den`. -/
def toQ (p : QPair) : ℚ := (p.1 : ℚ) / (p.2 : ℚ)

/-- Well-formed pair: positive denominator. -/
def QPair.wf (p : QPair) : Prop := 0 < p.2

/-- A linear constraint with integer-pair data. -/
structure LinConZ where
  coeffs : List (String × QPair)
  kind   : Kind
  const  : QPair
deriving Repr

/-- An entailment certificate with integer-pair data. -/
structure CertZ where
  premises    : List LinConZ
  multipliers : List QPair
  conclusion  : LinConZ
deriving Repr

/-! ## 2. Lifting integer-pair data to the ℚ spec types. -/

/-- Lift a coefficient map. -/
def liftCoeffs (m : List (String × QPair)) : List (String × ℚ) :=
  m.map (fun p => (p.1, toQ p.2))

/-- Lift a constraint. -/
def liftCon (lc : LinConZ) : LinearConstraint :=
  ⟨liftCoeffs lc.coeffs, lc.kind, toQ lc.const⟩

/-- Lift a whole certificate to the ℚ spec `Cert`. -/
def liftCert (cz : CertZ) : Cert :=
  { premises := cz.premises.map liftCon,
    multipliers := cz.multipliers.map toQ,
    conclusion := liftCon cz.conclusion }

/-! ## 3. Kernel-reducible integer checks (cross-multiplication). -/

/-- `0 ≤ num/den` (with `den > 0`)  ⇔  `0 ≤ num`. -/
def nonnegZ (p : QPair) : Bool := decide (0 ≤ p.1)

/-- `toQ a ≤ toQ b` with positive denominators  ⇔  `a.num*b.den ≤ b.num*a.den`. -/
def leZ (a b : QPair) : Bool := decide (a.1 * b.2 ≤ b.1 * a.2)

/-- `toQ a = 0`  ⇔  `a.num = 0`. -/
def isZeroZ (a : QPair) : Bool := decide (a.1 = 0)

/-! ### Integer-pair arithmetic mirroring ℚ `+`, `*` (unreduced). -/

/-- Product of two integer pairs (unreduced). -/
def mulZ (a b : QPair) : QPair := (a.1 * b.1, a.2 * b.2)

/-- Sum of two integer pairs (unreduced common denominator). -/
def addZ (a b : QPair) : QPair := (a.1 * b.2 + b.1 * a.2, a.2 * b.2)

/-- Negation. -/
def negZ (a : QPair) : QPair := (-a.1, a.2)

/-! ## 4. Homomorphism lemmas:  `toQ` commutes with the integer arithmetic and
       reflects the comparisons (given positive denominators). -/

theorem toQ_mulZ (a b : QPair) (ha : QPair.wf a) (hb : QPair.wf b) :
    toQ (mulZ a b) = toQ a * toQ b := by
  unfold toQ mulZ QPair.wf at *
  push_cast
  field_simp

theorem toQ_addZ (a b : QPair) (ha : QPair.wf a) (hb : QPair.wf b) :
    toQ (addZ a b) = toQ a + toQ b := by
  unfold toQ addZ QPair.wf at *
  have ha' : (a.2 : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b.2 : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  push_cast
  field_simp

theorem toQ_negZ (a : QPair) : toQ (negZ a) = - toQ a := by
  unfold toQ negZ
  push_cast
  ring

theorem nonnegZ_sound (p : QPair) (hp : QPair.wf p) :
    nonnegZ p = true → 0 ≤ toQ p := by
  unfold nonnegZ QPair.wf toQ at *
  intro h
  rw [decide_eq_true_iff] at h
  have hd : (0 : ℚ) < (p.2 : ℚ) := by exact_mod_cast hp
  have hn : (0 : ℚ) ≤ (p.1 : ℚ) := by exact_mod_cast h
  positivity

theorem leZ_sound (a b : QPair) (ha : QPair.wf a) (hb : QPair.wf b) :
    leZ a b = true → toQ a ≤ toQ b := by
  unfold leZ QPair.wf toQ at *
  intro h
  rw [decide_eq_true_iff] at h
  have hda : (0 : ℚ) < (a.2 : ℚ) := by exact_mod_cast ha
  have hdb : (0 : ℚ) < (b.2 : ℚ) := by exact_mod_cast hb
  rw [div_le_div_iff₀ hda hdb]
  have : (a.1 : ℚ) * (b.2 : ℚ) ≤ (b.1 : ℚ) * (a.2 : ℚ) := by exact_mod_cast h
  linarith

theorem isZeroZ_sound (a : QPair) (ha : QPair.wf a) :
    isZeroZ a = true → toQ a = 0 := by
  unfold isZeroZ QPair.wf toQ at *
  intro h
  rw [decide_eq_true_iff] at h
  rw [h]
  simp

theorem mulZ_wf {a b : QPair} (ha : QPair.wf a) (hb : QPair.wf b) :
    QPair.wf (mulZ a b) := by
  unfold QPair.wf mulZ at *; exact mul_pos ha hb

theorem addZ_wf {a b : QPair} (ha : QPair.wf a) (hb : QPair.wf b) :
    QPair.wf (addZ a b) := by
  unfold QPair.wf addZ at *; exact mul_pos ha hb

/-! ## 5. Integer mirrors of the ℚ-checker's map algebra (`CertChecker`).

Each integer function below mirrors EXACTLY the structure of its ℚ counterpart
in `Crownproof.CertChecker`, with `*`→`mulZ`, `+`→`addZ`, `-`→`negZ`.  The
`liftCoeffs`/`toQ` homomorphism then turns each into the ℚ version, which lets us
reuse the ℚ Farkas core for soundness while RUNNING the integer version. -/

/-- Integer scale of a coefficient map (mirrors `scaleMap`). -/
def scaleMapZ (k : QPair) (m : List (String × QPair)) : List (String × QPair) :=
  m.map (fun p => (p.1, mulZ k p.2))

/-- Integer negate of a coefficient map (mirrors `negMap`). -/
def negMapZ (m : List (String × QPair)) : List (String × QPair) :=
  m.map (fun p => (p.1, negZ p.2))

/-- Integer normalization to `≤`-form (mirrors `normalize`). -/
def normalizeZ (lc : LinConZ) : List (List (String × QPair) × QPair) :=
  match lc.kind with
  | .le => [(lc.coeffs, lc.const)]
  | .ge => [(negMapZ lc.coeffs, negZ lc.const)]
  | .eq => [(lc.coeffs, lc.const), (negMapZ lc.coeffs, negZ lc.const)]

/-- Integer per-pair coefficient map (mirrors `rowCoeffs`). -/
def rowCoeffsZ (μ : QPair) (lc : LinConZ) : List (String × QPair) :=
  ((normalizeZ lc).map (fun row => scaleMapZ μ row.1)).flatten

/-- Integer combined coefficient map (mirrors `combCoeffs`). -/
def combCoeffsZ : List (LinConZ × QPair) → List (String × QPair)
  | [] => []
  | (lc, μ) :: rest => rowCoeffsZ μ lc ++ combCoeffsZ rest

/-- Integer per-pair constant via repeated `addZ` (mirrors `rowConst = Σ μ*row.2`).
    `(0,1)` is the integer encoding of ℚ `0`. -/
def rowConstZ (μ : QPair) (lc : LinConZ) : QPair :=
  ((normalizeZ lc).map (fun row => mulZ μ row.2)).foldr addZ (0, 1)

/-- Integer combined constant (mirrors `combConst`). -/
def combConstZ : List (LinConZ × QPair) → QPair
  | [] => (0, 1)
  | (lc, μ) :: rest => addZ (rowConstZ μ lc) (combConstZ rest)

/-- Integer add-into-assoc-list (mirrors `addEntry`). -/
def addEntryZ : List (String × QPair) → String → QPair → List (String × QPair)
  | [], v, c => [(v, c)]
  | (w, d) :: rest, v, c =>
      if v = w then (w, addZ d c) :: rest
      else (w, d) :: addEntryZ rest v c

/-- Integer collapse (mirrors `collapse`). -/
def collapseZ (m : List (String × QPair)) : List (String × QPair) :=
  m.foldl (fun acc p => addEntryZ acc p.1 p.2) []

/-- Integer normalize conclusion (mirrors `normalizeConclusion`). -/
def normalizeConclusionZ (lc : LinConZ) : Option (List (String × QPair) × QPair) :=
  match lc.kind with
  | .le => some (lc.coeffs, lc.const)
  | .ge => some (negMapZ lc.coeffs, negZ lc.const)
  | .eq => none

/-- Integer diff map (mirrors `diffMap`). -/
def diffMapZ (pairs : List (LinConZ × QPair))
    (conclCoeffs : List (String × QPair)) : List (String × QPair) :=
  combCoeffsZ pairs ++ negMapZ conclCoeffs

/-! ## 6. The kernel-runnable integer checker. -/

/-- Well-formedness predicate computed as a Bool: every denominator `> 0`. -/
def allDenPos (cz : CertZ) : Bool :=
  (cz.premises.all (fun lc =>
      lc.coeffs.all (fun p => decide (0 < p.2.2)) && decide (0 < lc.const.2))) &&
  cz.multipliers.all (fun μ => decide (0 < μ.2)) &&
  cz.conclusion.coeffs.all (fun p => decide (0 < p.2.2)) &&
  decide (0 < cz.conclusion.const.2)

/--
**The runnable checker** (mirrors `checkEntailment`, but all arithmetic is integer
cross-multiplication, so `decide`/`rfl` reduces it in the kernel — GMP-backed,
NO `native_decide`). -/
def checkEntailmentZ (cz : CertZ) : Bool :=
  allDenPos cz &&
  cz.premises.length == cz.multipliers.length &&
  cz.multipliers.all (fun μ => nonnegZ μ) &&
  (match normalizeConclusionZ cz.conclusion with
   | none => false
   | some (conclCoeffs, conclConst) =>
       let pairs := cz.premises.zip cz.multipliers
       (collapseZ (diffMapZ pairs conclCoeffs)).all (fun p => isZeroZ p.2) &&
       leZ (combConstZ pairs) conclConst)

/-! ## 7. Homomorphism lemmas:  the integer maps lift to the ℚ-spec maps. -/

/-- Lift a `(LinConZ × QPair)` pair-list to the ℚ pair-list. -/
def liftPairs (pairs : List (LinConZ × QPair)) : List (LinearConstraint × ℚ) :=
  pairs.map (fun p => (liftCon p.1, toQ p.2))

/-- `liftCoeffs` commutes with append. -/
theorem liftCoeffs_append (m₁ m₂ : List (String × QPair)) :
    liftCoeffs (m₁ ++ m₂) = liftCoeffs m₁ ++ liftCoeffs m₂ := by
  unfold liftCoeffs; rw [List.map_append]

/-- `liftCoeffs` commutes with `negMapZ` ↦ `negMap`. -/
theorem liftCoeffs_negMapZ (m : List (String × QPair)) :
    liftCoeffs (negMapZ m) = negMap (liftCoeffs m) := by
  unfold liftCoeffs negMapZ negMap
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro p _
  simp only [Function.comp, toQ_negZ]

/-- `evalMap` of a lifted scaled map (with wf scale and wf entries). -/
theorem evalMap_liftCoeffs_scaleMapZ (k : QPair) (m : List (String × QPair))
    (hk : QPair.wf k) (hm : ∀ p ∈ m, QPair.wf p.2) (σ : Assignment) :
    evalMap (liftCoeffs (scaleMapZ k m)) σ = toQ k * evalMap (liftCoeffs m) σ := by
  induction m with
  | nil => simp [liftCoeffs, scaleMapZ]
  | cons hd tl ih =>
    have hhd : QPair.wf hd.2 := hm hd (List.mem_cons_self ..)
    have htl : ∀ p ∈ tl, QPair.wf p.2 := fun p hp => hm p (List.mem_cons_of_mem _ hp)
    have e1 : liftCoeffs (scaleMapZ k (hd :: tl))
        = (hd.1, toQ (mulZ k hd.2)) :: liftCoeffs (scaleMapZ k tl) := by
      simp [liftCoeffs, scaleMapZ]
    have e2 : liftCoeffs (hd :: tl) = (hd.1, toQ hd.2) :: liftCoeffs tl := by
      simp [liftCoeffs]
    rw [e1, evalMap_cons, e2, evalMap_cons, ih htl, toQ_mulZ k hd.2 hk hhd]
    ring

/-! ### Collapse over lifted integer maps preserves the functional. -/

/-- wf is preserved by `addEntryZ` if both the accumulator entries and the added
    coefficient are wf. -/
theorem addEntryZ_wf (acc : List (String × QPair)) (v : String) (c : QPair)
    (hacc : ∀ p ∈ acc, QPair.wf p.2) (hc : QPair.wf c) :
    ∀ p ∈ addEntryZ acc v c, QPair.wf p.2 := by
  induction acc with
  | nil =>
    intro p hp
    simp only [addEntryZ, List.mem_singleton] at hp
    subst hp; exact hc
  | cons hd tl ih =>
    obtain ⟨w, d⟩ := hd
    have hd_wf : QPair.wf d := hacc (w, d) (List.mem_cons_self ..)
    have htl_wf : ∀ p ∈ tl, QPair.wf p.2 := fun p hp => hacc p (List.mem_cons_of_mem _ hp)
    by_cases hvw : v = w
    · have he : addEntryZ ((w, d) :: tl) v c = (w, addZ d c) :: tl := by
        show (if v = w then (w, addZ d c) :: tl else (w, d) :: addEntryZ tl v c)
              = (w, addZ d c) :: tl
        rw [if_pos hvw]
      rw [he]
      intro p hp
      rcases List.mem_cons.mp hp with hp | hp
      · subst hp; exact addZ_wf hd_wf hc
      · exact htl_wf p hp
    · have he : addEntryZ ((w, d) :: tl) v c = (w, d) :: addEntryZ tl v c := by
        show (if v = w then (w, addZ d c) :: tl else (w, d) :: addEntryZ tl v c)
              = (w, d) :: addEntryZ tl v c
        rw [if_neg hvw]
      rw [he]
      intro p hp
      rcases List.mem_cons.mp hp with hp | hp
      · subst hp; exact hd_wf
      · exact ih htl_wf p hp

/-- `addEntryZ` adds `toQ c * σ v` to the lifted functional value (given wf). -/
theorem evalMap_liftCoeffs_addEntryZ (acc : List (String × QPair)) (v : String)
    (c : QPair) (hacc : ∀ p ∈ acc, QPair.wf p.2) (hc : QPair.wf c) (σ : Assignment) :
    evalMap (liftCoeffs (addEntryZ acc v c)) σ
      = evalMap (liftCoeffs acc) σ + toQ c * σ v := by
  induction acc with
  | nil =>
    have e : liftCoeffs (addEntryZ [] v c) = [(v, toQ c)] := by simp [liftCoeffs, addEntryZ]
    rw [e, evalMap_cons, evalMap_nil]
    show toQ c * σ v + 0 = evalMap (liftCoeffs []) σ + toQ c * σ v
    simp [liftCoeffs]
  | cons hd tl ih =>
    obtain ⟨w, d⟩ := hd
    have hd_wf : QPair.wf d := hacc (w, d) (List.mem_cons_self ..)
    have htl_wf : ∀ p ∈ tl, QPair.wf p.2 := fun p hp => hacc p (List.mem_cons_of_mem _ hp)
    by_cases hvw : v = w
    · subst hvw
      have he : addEntryZ ((v, d) :: tl) v c = (v, addZ d c) :: tl := by
        show (if v = v then (v, addZ d c) :: tl else (v, d) :: addEntryZ tl v c)
              = (v, addZ d c) :: tl
        rw [if_pos rfl]
      have e1 : liftCoeffs ((v, addZ d c) :: tl) = (v, toQ (addZ d c)) :: liftCoeffs tl := by
        simp [liftCoeffs]
      have e2 : liftCoeffs ((v, d) :: tl) = (v, toQ d) :: liftCoeffs tl := by simp [liftCoeffs]
      rw [he, e1, evalMap_cons, e2, evalMap_cons, toQ_addZ d c hd_wf hc]
      ring
    · have he : addEntryZ ((w, d) :: tl) v c = (w, d) :: addEntryZ tl v c := by
        show (if v = w then (w, addZ d c) :: tl else (w, d) :: addEntryZ tl v c)
              = (w, d) :: addEntryZ tl v c
        rw [if_neg hvw]
      have e1 : liftCoeffs ((w, d) :: addEntryZ tl v c)
          = (w, toQ d) :: liftCoeffs (addEntryZ tl v c) := by simp [liftCoeffs]
      have e2 : liftCoeffs ((w, d) :: tl) = (w, toQ d) :: liftCoeffs tl := by simp [liftCoeffs]
      rw [he, e1, evalMap_cons, e2, evalMap_cons, ih htl_wf]
      ring

/-- Folding `addEntryZ` preserves the lifted functional (accumulated). -/
theorem evalMap_foldl_addEntryZ (m : List (String × QPair))
    (hm : ∀ p ∈ m, QPair.wf p.2) (σ : Assignment) :
    ∀ acc : List (String × QPair), (∀ p ∈ acc, QPair.wf p.2) →
      evalMap (liftCoeffs (m.foldl (fun a p => addEntryZ a p.1 p.2) acc)) σ
        = evalMap (liftCoeffs acc) σ + evalMap (liftCoeffs m) σ := by
  induction m with
  | nil => intro acc _; simp [liftCoeffs]
  | cons hd tl ih =>
    intro acc hacc
    obtain ⟨v, c⟩ := hd
    have hc : QPair.wf c := hm (v, c) (List.mem_cons_self ..)
    have htl : ∀ p ∈ tl, QPair.wf p.2 := fun p hp => hm p (List.mem_cons_of_mem _ hp)
    simp only [List.foldl_cons]
    have hacc' : ∀ p ∈ addEntryZ acc v c, QPair.wf p.2 := addEntryZ_wf acc v c hacc hc
    rw [ih htl (addEntryZ acc v c) hacc', evalMap_liftCoeffs_addEntryZ acc v c hacc hc]
    have e2 : liftCoeffs ((v, c) :: tl) = (v, toQ c) :: liftCoeffs tl := by simp [liftCoeffs]
    rw [e2, evalMap_cons]
    ring

/-- `collapseZ` preserves the lifted functional. -/
theorem evalMap_liftCoeffs_collapseZ (m : List (String × QPair))
    (hm : ∀ p ∈ m, QPair.wf p.2) (σ : Assignment) :
    evalMap (liftCoeffs (collapseZ m)) σ = evalMap (liftCoeffs m) σ := by
  unfold collapseZ
  rw [evalMap_foldl_addEntryZ m hm σ [] (by simp)]
  simp [liftCoeffs]

/-- If every lifted coefficient of `m` is `0` (i.e. each numerator is 0), the
    lifted functional is `0`. -/
theorem evalMap_liftCoeffs_eq_zero_of_isZeroZ (m : List (String × QPair))
    (hm : ∀ p ∈ m, QPair.wf p.2) (hz : ∀ p ∈ m, isZeroZ p.2 = true) (σ : Assignment) :
    evalMap (liftCoeffs m) σ = 0 := by
  apply evalMap_eq_zero_of_allZero
  intro p hp
  unfold liftCoeffs at hp
  rw [List.mem_map] at hp
  obtain ⟨q, hq, hpeq⟩ := hp
  rw [← hpeq]
  exact isZeroZ_sound q.2 (hm q hq) (hz q hq)

/-! ### `combCoeffsZ` / `combConstZ` homomorphisms. -/

/-- wf of every coeff in a single premise's row-coefficient map. -/
theorem rowCoeffsZ_wf (μ : QPair) (lc : LinConZ)
    (hμ : QPair.wf μ) (hlc : ∀ p ∈ lc.coeffs, QPair.wf p.2) :
    ∀ p ∈ rowCoeffsZ μ lc, QPair.wf p.2 := by
  intro p hp
  unfold rowCoeffsZ at hp
  rw [List.mem_flatten] at hp
  obtain ⟨l, hl, hpl⟩ := hp
  rw [List.mem_map] at hl
  obtain ⟨row, hrow, hleq⟩ := hl
  rw [← hleq] at hpl
  unfold scaleMapZ at hpl
  rw [List.mem_map] at hpl
  obtain ⟨q, hq, hqeq⟩ := hpl
  rw [← hqeq]
  refine mulZ_wf hμ ?_
  unfold normalizeZ at hrow
  rcases hk : lc.kind with _ | _ | _ <;> rw [hk] at hrow <;>
    simp only [List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false] at hrow
  · subst hrow; exact hlc q hq
  · subst hrow
    simp only [negMapZ, List.mem_map] at hq
    obtain ⟨r, hr, hreq⟩ := hq; rw [← hreq]; unfold negZ QPair.wf; exact hlc r hr
  · rcases hrow with hrow | hrow
    · subst hrow; exact hlc q hq
    · subst hrow
      simp only [negMapZ, List.mem_map] at hq
      obtain ⟨r, hr, hreq⟩ := hq; rw [← hreq]; unfold negZ QPair.wf; exact hlc r hr

/-- General eval of a lifted flattened-scaled row list (no normalize specifics):
    `evalMap (lift (flatten (map (scaleMapZ μ ∘ .1) rows))) σ
       = toQ μ * Σ evalMap (lift row.1) σ`, given wf. -/
theorem evalMap_liftCoeffs_flatScale (μ : QPair) (hμ : QPair.wf μ)
    (rows : List (List (String × QPair) × QPair))
    (hrows : ∀ row ∈ rows, ∀ p ∈ row.1, QPair.wf p.2) (σ : Assignment) :
    evalMap (liftCoeffs ((rows.map (fun row => scaleMapZ μ row.1)).flatten)) σ
      = toQ μ * (rows.map (fun row => evalMap (liftCoeffs row.1) σ)).sum := by
  induction rows with
  | nil => simp [liftCoeffs]
  | cons hd tl ih =>
    have hhd : ∀ p ∈ hd.1, QPair.wf p.2 := hrows hd (List.mem_cons_self ..)
    have htl : ∀ row ∈ tl, ∀ p ∈ row.1, QPair.wf p.2 :=
      fun row hr => hrows row (List.mem_cons_of_mem _ hr)
    simp only [List.map_cons, List.flatten_cons, List.sum_cons]
    rw [liftCoeffs_append, evalMap_append,
        evalMap_liftCoeffs_scaleMapZ μ hd.1 hμ hhd σ, ih htl]
    ring

/-- The lifted integer per-pair coefficient functional equals the ℚ per-pair
    coefficient functional of the lifted constraint. -/
theorem evalMap_liftCoeffs_rowCoeffsZ (μ : QPair) (lc : LinConZ)
    (hμ : QPair.wf μ) (hlc : ∀ p ∈ lc.coeffs, QPair.wf p.2) (σ : Assignment) :
    evalMap (liftCoeffs (rowCoeffsZ μ lc)) σ
      = evalMap (rowCoeffs (toQ μ) (liftCon lc)) σ := by
  rw [evalMap_rowCoeffs, rowCoeffsZ]
  -- wf for every row of normalizeZ lc
  have hwf : ∀ row ∈ normalizeZ lc, ∀ p ∈ row.1, QPair.wf p.2 := by
    intro row hrow
    unfold normalizeZ at hrow
    rcases hk : lc.kind with _ | _ | _ <;> rw [hk] at hrow <;>
      simp only [List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false] at hrow
    · subst hrow; exact hlc
    · subst hrow; intro p hp
      simp only [negMapZ, List.mem_map] at hp
      obtain ⟨r, hr, hreq⟩ := hp; rw [← hreq]; exact hlc r hr
    · rcases hrow with hrow | hrow
      · subst hrow; exact hlc
      · subst hrow; intro p hp
        simp only [negMapZ, List.mem_map] at hp
        obtain ⟨r, hr, hreq⟩ := hp; rw [← hreq]; exact hlc r hr
  rw [evalMap_liftCoeffs_flatScale μ hμ (normalizeZ lc) hwf σ]
  -- now relate Σ over normalizeZ to Σ over normalize (liftCon lc); case on kind.
  rcases hk : lc.kind with _ | _ | _ <;>
    simp only [normalizeZ, normalize, liftCon, hk, List.map_cons, List.map_nil,
               List.sum_cons, List.sum_nil, liftCoeffs_negMapZ, toQ_negZ,
               evalMap_negMap] <;> ring

/-- The lifted integer per-pair constant equals the ℚ per-pair constant.  We need
    the premise coeffs/const and the multiplier to be wf. -/
theorem toQ_rowConstZ (μ : QPair) (lc : LinConZ)
    (hμ : QPair.wf μ) (hconst : QPair.wf lc.const) (σ : Assignment) :
    toQ (rowConstZ μ lc) = rowConst (toQ μ) (liftCon lc) := by
  unfold rowConstZ rowConst
  -- wf for every normalized row constant
  have hwf : ∀ row ∈ normalizeZ lc, QPair.wf row.2 := by
    intro row hrow
    unfold normalizeZ at hrow
    rcases hk : lc.kind with _ | _ | _ <;> rw [hk] at hrow <;>
      simp only [List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false] at hrow
    · subst hrow; exact hconst
    · subst hrow; unfold negZ QPair.wf; exact hconst
    · rcases hrow with hrow | hrow
      · subst hrow; exact hconst
      · subst hrow; unfold negZ QPair.wf; exact hconst
  -- foldr addZ over normalizeZ, lifted, equals sum over normalize (liftCon lc)
  have hfold : ∀ (rows : List (List (String × QPair) × QPair)),
      (∀ row ∈ rows, QPair.wf row.2) →
      toQ ((rows.map (fun row => mulZ μ row.2)).foldr addZ (0, 1))
        = (rows.map (fun row => toQ μ * toQ row.2)).sum := by
    intro rows hrows
    induction rows with
    | nil => simp [toQ]
    | cons hd tl ih =>
      have hhd : QPair.wf hd.2 := hrows hd (List.mem_cons_self ..)
      have htl : ∀ row ∈ tl, QPair.wf row.2 := fun r hr => hrows r (List.mem_cons_of_mem _ hr)
      simp only [List.map_cons, List.foldr_cons, List.sum_cons]
      have hmul_wf : QPair.wf (mulZ μ hd.2) := mulZ_wf hμ hhd
      have hfoldwf : QPair.wf ((tl.map (fun row => mulZ μ row.2)).foldr addZ (0, 1)) := by
        clear ih hrows
        induction tl with
        | nil => unfold QPair.wf; norm_num
        | cons hd2 tl2 ih2 =>
          simp only [List.map_cons, List.foldr_cons]
          exact addZ_wf (mulZ_wf hμ (htl hd2 (List.mem_cons_self ..)))
            (ih2 (fun r hr => htl r (List.mem_cons_of_mem _ hr)))
      rw [toQ_addZ _ _ hmul_wf hfoldwf, toQ_mulZ μ hd.2 hμ hhd, ih htl]
  rw [hfold (normalizeZ lc) hwf]
  -- relate to normalize (liftCon lc)
  rcases hk : lc.kind with _ | _ | _ <;>
    simp only [normalizeZ, normalize, liftCon, hk, List.map_cons, List.map_nil,
               List.sum_cons, List.sum_nil, toQ_negZ] <;> ring

/-- `rowConstZ` is wf when the premise const and multiplier are wf. -/
theorem rowConstZ_wf (μ : QPair) (lc : LinConZ)
    (hμ : QPair.wf μ) (hconst : QPair.wf lc.const) : QPair.wf (rowConstZ μ lc) := by
  unfold rowConstZ
  have hrows : ∀ row ∈ normalizeZ lc, QPair.wf row.2 := by
    intro row hrow
    unfold normalizeZ at hrow
    rcases hk : lc.kind with _ | _ | _ <;> rw [hk] at hrow <;>
      simp only [List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false] at hrow
    · subst hrow; exact hconst
    · subst hrow; unfold negZ QPair.wf; exact hconst
    · rcases hrow with hrow | hrow
      · subst hrow; exact hconst
      · subst hrow; unfold negZ QPair.wf; exact hconst
  generalize (normalizeZ lc) = rows at hrows ⊢
  induction rows with
  | nil => unfold QPair.wf; norm_num
  | cons r rs ihr =>
    simp only [List.map_cons, List.foldr_cons]
    exact addZ_wf (mulZ_wf hμ (hrows r (List.mem_cons_self ..)))
      (ihr (fun x hx => hrows x (List.mem_cons_of_mem _ hx)))

/-- `combConstZ` is wf when every premise const and multiplier are wf. -/
theorem combConstZ_wf (pairs : List (LinConZ × QPair))
    (hwf : ∀ p ∈ pairs, QPair.wf p.1.const ∧ QPair.wf p.2) :
    QPair.wf (combConstZ pairs) := by
  induction pairs with
  | nil => unfold combConstZ QPair.wf; norm_num
  | cons hd tl ih =>
    obtain ⟨lc, μ⟩ := hd
    have hhd := hwf (lc, μ) (List.mem_cons_self ..)
    simp only [combConstZ]
    exact addZ_wf (rowConstZ_wf μ lc hhd.2 hhd.1)
      (ih (fun p hp => hwf p (List.mem_cons_of_mem _ hp)))

/-- The lifted integer combined constant equals the ℚ combined constant. -/
theorem toQ_combConstZ (pairs : List (LinConZ × QPair))
    (hwf : ∀ p ∈ pairs, QPair.wf p.1.const ∧ QPair.wf p.2)
    (σ : Assignment) :
    toQ (combConstZ pairs) = combConst (liftPairs pairs) := by
  induction pairs with
  | nil => simp [combConstZ, combConst, liftPairs, toQ]
  | cons hd tl ih =>
    obtain ⟨lc, μ⟩ := hd
    have hhd := hwf (lc, μ) (List.mem_cons_self ..)
    have htl : ∀ p ∈ tl, QPair.wf p.1.const ∧ QPair.wf p.2 :=
      fun p hp => hwf p (List.mem_cons_of_mem _ hp)
    have hlp : liftPairs ((lc, μ) :: tl) = (liftCon lc, toQ μ) :: liftPairs tl := by
      simp [liftPairs]
    rw [hlp]
    simp only [combConstZ, combConst]
    rw [toQ_addZ _ _ (rowConstZ_wf μ lc hhd.2 hhd.1) (combConstZ_wf tl htl),
        toQ_rowConstZ μ lc hhd.2 hhd.1 σ, ih htl]

/-- The lifted integer combined coefficient FUNCTIONAL equals the ℚ combined
    coefficient functional of the lifted pair-list. -/
theorem evalMap_liftCoeffs_combCoeffsZ (pairs : List (LinConZ × QPair))
    (hwf : ∀ p ∈ pairs, (∀ q ∈ p.1.coeffs, QPair.wf q.2) ∧ QPair.wf p.2)
    (σ : Assignment) :
    evalMap (liftCoeffs (combCoeffsZ pairs)) σ = evalMap (combCoeffs (liftPairs pairs)) σ := by
  induction pairs with
  | nil => simp [combCoeffsZ, combCoeffs, liftPairs, liftCoeffs]
  | cons hd tl ih =>
    obtain ⟨lc, μ⟩ := hd
    have hhd := hwf (lc, μ) (List.mem_cons_self ..)
    have htl : ∀ p ∈ tl, (∀ q ∈ p.1.coeffs, QPair.wf q.2) ∧ QPair.wf p.2 :=
      fun p hp => hwf p (List.mem_cons_of_mem _ hp)
    have hlp : liftPairs ((lc, μ) :: tl) = (liftCon lc, toQ μ) :: liftPairs tl := by
      simp [liftPairs]
    rw [hlp]
    simp only [combCoeffsZ, combCoeffs]
    rw [liftCoeffs_append, evalMap_append, evalMap_append,
        evalMap_liftCoeffs_rowCoeffsZ μ lc hhd.2 hhd.1 σ, ih htl]

/-! ## 8. Glue:  the lifted cert's `zip` is the `liftPairs` of the integer `zip`. -/

/-- Lifting commutes with `zip`. -/
theorem liftCert_zip (cz : CertZ) :
    (liftCert cz).premises.zip (liftCert cz).multipliers
      = liftPairs (cz.premises.zip cz.multipliers) := by
  unfold liftCert liftPairs
  simp only []
  rw [List.zip_map]
  rfl

/-- The integer conclusion normalization lifts to the ℚ conclusion normalization. -/
theorem normalizeConclusionZ_lift (lc : LinConZ) (conclCoeffs : List (String × QPair))
    (conclConst : QPair)
    (h : normalizeConclusionZ lc = some (conclCoeffs, conclConst)) :
    normalizeConclusion (liftCon lc)
      = some (liftCoeffs conclCoeffs, toQ conclConst) := by
  unfold normalizeConclusionZ at h
  unfold normalizeConclusion liftCon
  rcases hk : lc.kind with _ | _ | _ <;> rw [hk] at h <;> simp only at h ⊢
  · rw [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [← h1, ← h2]
  · rw [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [← h1, ← h2, liftCoeffs_negMapZ, toQ_negZ]
  · exact absurd h (by simp)

/-! ## 9. wf extraction from `allDenPos`. -/

/-- From `allDenPos cz = true`, every premise's coeffs and const, every
    multiplier, and the conclusion's coeffs and const have positive denominators. -/
theorem allDenPos_wf (cz : CertZ) (h : allDenPos cz = true) :
    (∀ lc ∈ cz.premises, (∀ p ∈ lc.coeffs, QPair.wf p.2) ∧ QPair.wf lc.const) ∧
    (∀ μ ∈ cz.multipliers, QPair.wf μ) ∧
    (∀ p ∈ cz.conclusion.coeffs, QPair.wf p.2) ∧ QPair.wf cz.conclusion.const := by
  unfold allDenPos at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hprem, hmul⟩, hccoe⟩, hcconst⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro lc hlc
    have := hprem lc hlc
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at this
    exact ⟨fun p hp => this.1 p hp, this.2⟩
  · intro μ hμ; exact hmul μ hμ
  · intro p hp; exact hccoe p hp
  · exact hcconst

/-! ## 10. SOUNDNESS of the runnable integer checker. -/

/--
**Soundness of `checkEntailmentZ`.**

If the kernel-runnable integer checker accepts `cz`, then for EVERY assignment `σ`
satisfying all premises of the lifted ℚ certificate `liftCert cz`, the
conclusion constraint holds.  Proven by the Farkas core
`Crownproof.farkas_premise_combination` (through `comb_le`), pulling every
arithmetic fact back from the integer checks via the `toQ` homomorphism.

Thus a leaf is safe by a Lean-kernel-verified computation (`checkEntailmentZ cz`
reduced by `decide`/`rfl`) PLUS this proof — NOT by the external Rust checker. -/
theorem checkEntailmentZ_sound (cz : CertZ) (hchk : checkEntailmentZ cz = true) :
    ∀ σ : Assignment,
      (∀ lc ∈ (liftCert cz).premises, lc.satisfies σ) →
      (liftCert cz).conclusion.satisfies σ := by
  intro σ hprem
  -- unpack the Boolean checker
  unfold checkEntailmentZ at hchk
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hchk
  obtain ⟨⟨⟨hden, hlen⟩, hμnn⟩, hrest⟩ := hchk
  -- wf facts
  obtain ⟨hpremwf, hmulwf, hcclwf, hcconstwf⟩ := allDenPos_wf cz hden
  -- conclusion normalizes
  revert hrest
  cases hkz : normalizeConclusionZ cz.conclusion with
  | none => intro hr; simp at hr
  | some cc =>
    obtain ⟨conclCoeffsZ, conclConstZ⟩ := cc
    intro hrest
    simp only [Bool.and_eq_true, List.all_eq_true] at hrest
    obtain ⟨hzero, hleZ⟩ := hrest
    -- set up the integer pairs and the lifted pairs
    set zpairs := cz.premises.zip cz.multipliers with hzpairs
    -- wf for the zipped integer pairs
    have hzpairwf : ∀ p ∈ zpairs, (∀ q ∈ p.1.coeffs, QPair.wf q.2) ∧
        QPair.wf p.1.const ∧ QPair.wf p.2 := by
      intro p hp
      rw [hzpairs] at hp
      have hm := List.of_mem_zip hp
      have h1 := hpremwf p.1 hm.1
      exact ⟨h1.1, h1.2, hmulwf p.2 hm.2⟩
    -- the ℚ pairs are exactly liftPairs zpairs
    have hzipeq : (liftCert cz).premises.zip (liftCert cz).multipliers = liftPairs zpairs :=
      liftCert_zip cz
    -- (1) every lifted multiplier ≥ 0
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
      -- q.1 is a premise of cz, so liftCon q.1 ∈ (liftCert cz).premises
      apply hprem
      unfold liftCert
      simp only []
      rw [List.mem_map]
      exact ⟨q.1, hqm.1, rfl⟩
    -- (2) the combined functional equals the conclusion functional
    have hwf_for_comb : ∀ p ∈ zpairs, (∀ q ∈ p.1.coeffs, QPair.wf q.2) ∧ QPair.wf p.2 :=
      fun p hp => ⟨(hzpairwf p hp).1, (hzpairwf p hp).2.2⟩
    have hccoeffwf : ∀ p ∈ conclCoeffsZ, QPair.wf p.2 := by
      -- conclCoeffsZ is either cz.conclusion.coeffs or negMapZ thereof
      unfold normalizeConclusionZ at hkz
      rcases hk : cz.conclusion.kind with _ | _ | _ <;> rw [hk] at hkz <;> simp only at hkz
      · rw [Option.some.injEq, Prod.mk.injEq] at hkz
        rw [← hkz.1]; exact hcclwf
      · rw [Option.some.injEq, Prod.mk.injEq] at hkz
        rw [← hkz.1]; intro p hp
        simp only [negMapZ, List.mem_map] at hp
        obtain ⟨r, hr, hreq⟩ := hp; rw [← hreq]; unfold negZ QPair.wf; exact hcclwf r hr
      · exact absurd hkz (by simp)
    -- wf of the integer diff map
    have hdiffwf : ∀ p ∈ diffMapZ zpairs conclCoeffsZ, QPair.wf p.2 := by
      intro p hp
      unfold diffMapZ at hp
      rw [List.mem_append] at hp
      rcases hp with hp | hp
      · -- p ∈ combCoeffsZ zpairs ; combCoeffsZ wf by induction
        have hcc : ∀ pairs : List (LinConZ × QPair),
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
    -- collapse preserves the lifted functional and all collapsed coeffs are zero
    have hfun : evalMap (combCoeffs (liftPairs zpairs)) σ = evalMap (liftCoeffs conclCoeffsZ) σ := by
      -- evalMap of lifted diff = 0
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
    -- wf of conclConstZ (it is cz.conclusion.const or its negZ)
    have hcconstZwf : QPair.wf conclConstZ := by
      unfold normalizeConclusionZ at hkz
      rcases hk : cz.conclusion.kind with _ | _ | _ <;> rw [hk] at hkz <;> simp only at hkz
      · rw [Option.some.injEq, Prod.mk.injEq] at hkz; rw [← hkz.2]; exact hcconstwf
      · rw [Option.some.injEq, Prod.mk.injEq] at hkz; rw [← hkz.2]
        unfold negZ QPair.wf; exact hcconstwf
      · exact absurd hkz (by simp)
    -- (3) the bound
    have hbound : combConst (liftPairs zpairs) ≤ toQ conclConstZ := by
      rw [← toQ_combConstZ zpairs (fun p hp => ⟨(hzpairwf p hp).2.1, (hzpairwf p hp).2.2⟩) σ]
      exact leZ_sound _ _ (combConstZ_wf zpairs
        (fun p hp => ⟨(hzpairwf p hp).2.1, (hzpairwf p hp).2.2⟩)) hcconstZwf hleZ
    -- Farkas bound on the combination (over liftPairs)
    have hcomb := comb_le (liftPairs zpairs) σ hμpos hsat
    rw [hfun] at hcomb
    have hchain : evalMap (liftCoeffs conclCoeffsZ) σ ≤ toQ conclConstZ := le_trans hcomb hbound
    -- translate back to the conclusion's declared relation
    have hnc : normalizeConclusion (liftCert cz).conclusion
        = some (liftCoeffs conclCoeffsZ, toQ conclConstZ) := by
      have : (liftCert cz).conclusion = liftCon cz.conclusion := rfl
      rw [this]
      exact normalizeConclusionZ_lift cz.conclusion conclCoeffsZ conclConstZ hkz
    -- conclusion satisfies, by cases on the lifted conclusion kind
    unfold normalizeConclusion at hnc
    have hlhs : (liftCert cz).conclusion.lhs σ = evalMap (liftCert cz).conclusion.coeffs σ := rfl
    cases hck : (liftCert cz).conclusion.kind with
    | le =>
      rw [hck] at hnc
      simp only [Option.some.injEq, Prod.mk.injEq] at hnc
      obtain ⟨hcoe, hcon⟩ := hnc
      rw [← hcoe, ← hcon] at hchain
      have hgoal : (liftCert cz).conclusion.lhs σ ≤ (liftCert cz).conclusion.const := by
        rw [hlhs]; exact hchain
      simp only [LinearConstraint.satisfies, hck]; exact hgoal
    | ge =>
      rw [hck] at hnc
      simp only [Option.some.injEq, Prod.mk.injEq] at hnc
      obtain ⟨hcoe, hcon⟩ := hnc
      rw [← hcoe, ← hcon, evalMap_negMap] at hchain
      have hgoal : (liftCert cz).conclusion.const ≤ (liftCert cz).conclusion.lhs σ := by
        rw [hlhs]; linarith
      simp only [LinearConstraint.satisfies, hck]; exact hgoal
    | eq =>
      rw [hck] at hnc
      exact absurd hnc (by simp)

end CertCheckerZ
end Crownproof

namespace Crownproof.CertCheckerZ
#print axioms checkEntailmentZ_sound
end Crownproof.CertCheckerZ
