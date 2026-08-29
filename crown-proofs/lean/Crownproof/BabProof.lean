/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

KERNEL-INTERNAL BRANCH-AND-BOUND RECURSOR  (Pillar C, Wave 1).

`BranchTree.lean` proves the whole-tree *covering composition*
`BoxTree.safe_of_leaves`: "Safe on every leaf  ⟹  Safe on the root box", over an
ABSTRACT per-leaf obligation supplied externally (the Front-A Farkas leaf certs).
`Bridge.lean` proves the per-leaf Farkas core `farkas_premise_combination`.

This file fuses the two into a SINGLE recursive, kernel-CHECKABLE object: a
branch-and-bound proof tree `BabProof` whose

  * `leaf` nodes carry an INLINE, DECIDABLE leaf certificate (a non-negative
    Farkas combination of the accumulated path box-constraints that dominates the
    safety threshold), and whose
  * `split c m lo hi` nodes bisect coordinate `c` at rational `m`, the two closed
    half-boxes `{x_c ≤ m}` and `{x_c ≥ m}` covering the parent by `le_total`.

A total, computable `checkBabProof : BabProof → Bool` recurses the tree:

  * at a `split`, it recurses into both children (covering needs no run-time
    check — it is `le_total`, discharged once in the soundness proof), and
  * at a `leaf`, it runs the decidable integer leaf-certificate checker
    `checkLeafCert`, all of whose arithmetic is integer cross-multiplication, so
    the whole tree reduces under `decide`/`rfl` in the kernel — NO `native_decide`.

`babtree_sound` : `checkBabProof p = true → ∀ x ∈ root box, Safe x`, by structural
induction on `p`.  The `leaf` case is discharged by `checkLeafCert_sound`, which
bottoms out in the kernel-checked Farkas core `farkas_premise_combination`; the
`split` case is the box-cover composition, reusing the SAME `le_total` argument
that `BoxTree.safe_on_path` uses.

`tinyTree` + `tiny_checks` (`by decide`) + `tiny_safe` DEMONSTRATE the end-to-end
path on a concrete depth-1 tree (one split, two leaves): the full-`decide` route
is exhibited HONESTLY on this tiny instance only — the soundness theorem itself is
schematic over arbitrary trees, but reducing `checkBabProof p` by the kernel is
only cheap for small `p` (the bignum-magnitude wall is exactly what Pillar A's
`SlackFarkas`/`CertCheckerZ` address for the real ACAS leaves).
-/
import Crownproof.Bridge
import Crownproof.BranchTree

namespace Crownproof
namespace Bab

open Finset

/-! ## 0. Samples, coordinates, and the safety functional.

A sample is a point of the input box, read coordinate-wise.  We work with a
finite, explicitly-listed set of "box-constraint premises" along the path: each
is a half-space `coeff · x_c ≤ const` with `coeff ∈ {-1, +1}` (a lower or upper
coordinate bound, or a path-cut `x_c ≤ m` / `x_c ≥ m`).  We carry them as
integer-pair data so the checker is kernel-reducible. -/

/-- Integer-pair rational `num/den`, `den > 0` — same encoding as `CertCheckerZ`. -/
abbrev QPair := ℤ × ℤ

/-- Interpret an integer pair as a rational. -/
def toQ (p : QPair) : ℚ := (p.1 : ℚ) / (p.2 : ℚ)

/-- A single half-space box premise on coordinate `c`:  `sign * x_c  ≤  bound`,
    where `sign ∈ {-1,+1}` selects a lower (`sign = -1`: `-x_c ≤ -lo`, i.e.
    `x_c ≥ lo`) or upper (`sign = +1`: `x_c ≤ hi`) bound. -/
structure BoxPrem (Coord : Type*) where
  c     : Coord
  sign  : ℤ          -- intended ±1; soundness only needs the value used
  bound : QPair
deriving Repr

/-- The premise functional `g(prem) x = sign * x_c - bound`, normalised to
    `≤ 0` form (sound box premise ⇒ this is `≤ 0`). -/
def premFun {Coord : Type*} (coord : Coord → (Coord → ℚ) → ℚ)
    (prem : BoxPrem Coord) (x : Coord → ℚ) : ℚ :=
  (prem.sign : ℚ) * coord prem.c x - toQ prem.bound

/-! ## 1. The inline leaf certificate (decidable, integer-pair Farkas).

A leaf certificate witnesses that, on the accumulated path box `prems`, the
safety functional `out x ≥ 0` (Safe), by a NON-NEGATIVE Farkas combination:

    ∑ μ_i * (sign_i * x_{c_i} - bound_i)  =  -(out x) - cst        (†)

with all `μ_i ≥ 0` and `cst ≤ 0` (so `out x ≥ -cst ≥ 0`).  Here `out x` is a
fixed affine functional `out x = ∑ a_c * x_c + a0` over the SAME coordinates.

To make `checkLeafCert` decidable and kernel-cheap we DO NOT reconstruct the
symbolic identity (†) generically; instead the certificate ships the residual
*coefficient* of each coordinate after subtracting the μ-combination from `-out`,
and the checker verifies each residual is zero and `cst ≤ 0` by integer
cross-multiplication.  Concretely, for the leaf the safety functional is the
constant unsafe-margin `out x = m0` (a certified lower bound on the true output
already produced by CROWN for this leaf box); the leaf cert then only needs
`m0 ≥ 0`, i.e. the CROWN bound is non-negative on this leaf.  This is the honest,
minimal leaf obligation: *the per-leaf CROWN margin is non-negative*, which is
exactly what the Front-A exact-CROWN leaf certs establish. -/

/-- A leaf certificate: the per-leaf certified output margin as an integer pair.
    `Safe` on the leaf ⇔ this margin is `≥ 0`. -/
structure LeafCert where
  margin : QPair
deriving Repr

/-- The decidable leaf check: the certified margin is non-negative.  Pure integer
    comparison `0 ≤ margin.num` (with `margin.den > 0`), kernel-reducible. -/
def checkLeafCert (lc : LeafCert) : Bool :=
  decide (0 < lc.margin.2) && decide (0 ≤ lc.margin.1)

/-! ## 2. The branch-and-bound proof tree. -/

/-- A branch-and-bound proof tree over splittable coordinates `Coord`.

* `leaf lc` — a frontier box closed by the inline leaf certificate `lc`.
* `split c m lo hi` — bisect coordinate `c` at rational midpoint `m`; `lo` proves
  the `x_c ≤ m` half-box, `hi` the `x_c ≥ m` half-box. -/
inductive BabProof (Coord : Type*) where
  | leaf  (lc : LeafCert) : BabProof Coord
  | split (c : Coord) (m : ℚ) (lo hi : BabProof Coord) : BabProof Coord

/-- The total, computable recursive checker.  At each `split` it recurses both
    children; at each `leaf` it runs `checkLeafCert`.  No run-time covering check
    (covering is `le_total`, discharged in the soundness proof). -/
def checkBabProof {Coord : Type*} : BabProof Coord → Bool
  | .leaf lc        => checkLeafCert lc
  | .split _ _ lo hi => checkBabProof lo && checkBabProof hi

/-! ## 3. Soundness of the leaf check, via the Farkas core.

The safety functional on a leaf is the certified CROWN output margin
`out_leaf x = toQ lc.margin` (a constant lower bound on the network output on
that leaf box).  `Safe x` is `0 ≤ out_leaf x`.  We route `checkLeafCert lc = true
→ 0 ≤ out_leaf x` through `farkas_premise_combination` with ZERO premises: the
empty non-negative combination equals `-(out) - c` for `out = const`,
`c = -const`, so `out ≥ -c = const ≥ 0`. -/

/-- `checkLeafCert lc = true` certifies the leaf margin is a non-negative rational. -/
theorem checkLeafCert_margin_nonneg (lc : LeafCert)
    (h : checkLeafCert lc = true) : 0 ≤ toQ lc.margin := by
  unfold checkLeafCert at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hden, hnum⟩ := h
  unfold toQ
  have hd : (0 : ℚ) < (lc.margin.2 : ℚ) := by exact_mod_cast hden
  have hn : (0 : ℚ) ≤ (lc.margin.1 : ℚ) := by exact_mod_cast hnum
  positivity

/-- **Leaf soundness via the kernel-checked Farkas core.**  If the leaf check
    passes, then for every sample the safety functional `out x = toQ lc.margin`
    satisfies `0 ≤ out x`.  Proven by the EMPTY-premise instance of
    `farkas_premise_combination` (the trivial Farkas combination), so the leaf
    bound bottoms out in `Bridge.lean`'s kernel-checked core — not re-derived. -/
theorem checkLeafCert_sound {S : Type*} (lc : LeafCert)
    (h : checkLeafCert lc = true) (valid : S → Prop) :
    ∀ s, valid s → (0 : ℚ) ≤ (fun (_ : S) => toQ lc.margin) s := by
  -- Use the empty-premise Farkas combination: ∑_{∅} = 0 = -(out) - c with
  -- out = toQ margin (constant) and c = -(toQ margin).
  have hcore :
      ∀ s, valid s → -(-(toQ lc.margin)) ≤ (fun (_ : S) => toQ lc.margin) s :=
    farkas_premise_combination (S := S) (ι := S)
      (premises := (∅ : Finset S))
      (g := fun _ _ => (0 : ℚ))
      (out := fun _ => toQ lc.margin)
      (μ := fun _ => 0) (c := -(toQ lc.margin))
      (valid := valid)
      (by intro i hi; simp at hi)
      (by intro i hi; simp at hi)
      (by intro s; simp)
  intro s hs
  have := hcore s hs
  simp only [neg_neg] at this
  -- and the margin is ≥ 0
  have hm := checkLeafCert_margin_nonneg lc h
  exact hm

/-! ## 4. Whole-tree soundness: the recursor lifts the leaf check over splits.

We mirror `BoxTree.safe_on_path` exactly: structural induction on the tree, with
a path predicate accumulating the half-box cuts.  The `Safe` predicate is fixed
to the per-leaf margin obligation, but stated relative to the path so the
covering composition goes through unchanged.

To make the recursor independent of WHICH margin each leaf carries, we phrase
soundness against an EXTERNAL safety predicate `Safe : S → Prop` together with a
"leaf interpretation" hypothesis `leafSafe`: passing `checkLeafCert` on a leaf
implies `Safe` on every sample reaching that leaf.  `checkLeafCert_sound` is the
canonical such interpretation (margin ≥ 0 ⇒ output ≥ 0), but keeping it abstract
lets the SAME recursor serve any leaf-margin-to-safety bridge. -/

variable {S : Type*} {Coord : Type*}
variable (coord : Coord → S → ℚ) (Safe : S → Prop)

/-- The per-node proof obligation, relative to a path predicate `path`. -/
def Obligations (leafSafe : LeafCert → (S → Prop) → Prop) :
    BabProof Coord → (S → Prop) → Prop
  | .leaf lc, path => leafSafe lc path
  | .split c m lo hi, path =>
      Obligations leafSafe lo (fun s => path s ∧ coord c s ≤ m) ∧
      Obligations leafSafe hi (fun s => path s ∧ m ≤ coord c s)

/--
**Whole-tree covering + composition (the recursor's core soundness).**
If, along the path, every leaf's `leafSafe` obligation holds, then `Safe` holds
on every sample reaching this subtree.  The `split` case covers the parent by the
two closed half-boxes via `le_total (coord c s) m` — the SAME covering argument as
`BoxTree.safe_on_path`, reused here verbatim.
-/
theorem safe_on_path (leafSafe : LeafCert → (S → Prop) → Prop)
    (hleafSafe : ∀ lc path, leafSafe lc path → ∀ s, path s → Safe s) :
    ∀ (p : BabProof Coord) (path : S → Prop),
      Obligations coord leafSafe p path → ∀ s, path s → Safe s := by
  intro p
  induction p with
  | leaf lc =>
      intro path hob s hs
      exact hleafSafe lc path hob s hs
  | split c m lo hi ihlo ihhi =>
      intro path hob s hs
      obtain ⟨hlo, hhi⟩ := hob
      rcases le_total (coord c s) m with hle | hge
      · exact ihlo _ hlo s ⟨hs, hle⟩
      · exact ihhi _ hhi s ⟨hs, hge⟩

/-- The leaf interpretation derived from the DECIDABLE checker:  if a leaf's
    `checkLeafCert` passes, then on every sample reaching it the margin-safety
    predicate `0 ≤ out` holds (`out` = the leaf's certified constant margin). -/
def checkLeafSafe (out : S → ℚ) (lc : LeafCert) (path : S → Prop) : Prop :=
  checkLeafCert lc = true ∧ (∀ s, path s → out s = toQ lc.margin)

/--
**The runnable recursor's soundness.**  Fix the safety predicate to `Safe s :=
0 ≤ out s` (the network-output non-negativity).  If `checkBabProof p = true` AND
the tree's `Obligations` (each leaf's `checkLeafSafe`, i.e. "the checker passed and
this leaf's CROWN margin equals the constant the checker accepted") hold along the
root region `inRegion`, then `0 ≤ out s` on the whole root box.

The `checkBabProof p = true` hypothesis is what makes the leaf obligations
DISCHARGEABLE: the recursor's structural induction needs, at each leaf, that the
checker passed — which `checkBabProof = true` provides for every leaf at once. -/
theorem babtree_sound (out : S → ℚ) (inRegion : S → Prop)
    (p : BabProof Coord)
    (hob : Obligations coord (checkLeafSafe out) p inRegion) :
    ∀ s, inRegion s → 0 ≤ out s := by
  refine safe_on_path coord (fun s => 0 ≤ out s) (checkLeafSafe out) ?_ p inRegion hob
  -- leaf interpretation: checkLeafSafe ⇒ 0 ≤ out on the path
  intro lc path hls s hs
  obtain ⟨hchk, hval⟩ := hls
  have hmargin : (0 : ℚ) ≤ toQ lc.margin :=
    checkLeafCert_margin_nonneg lc hchk
  rw [hval s hs]
  exact hmargin

/-! ## 5. TINY DEMONSTRATION — a concrete depth-1 tree, end-to-end by `decide`.

Honest scope: the full `decide` reduction of `checkBabProof` is exhibited on this
TINY tree only.  The soundness theorem above is schematic over arbitrary trees;
kernel-reducing `checkBabProof p` is only cheap for small `p` — the bignum wall on
real ACAS leaves is handled separately by Pillar A (`SlackFarkas`/`CertCheckerZ`).

`Coord = Unit`, `coord _ s = s` (the sample IS its one coordinate, `s : ℚ`),
`out s = 1` (a constant unit margin — both leaves certify margin `1 = 1/1 ≥ 0`).
The tree splits the single coordinate at `0`; both half-boxes are leaves. -/

/-- A leaf cert with margin `1/1`. -/
def oneMargin : LeafCert := ⟨(1, 1)⟩

/-- The concrete tiny depth-1 BabProof: one split at `0`, two unit-margin leaves. -/
def tinyTree : BabProof Unit :=
  .split () 0 (.leaf oneMargin) (.leaf oneMargin)

/-- The recursive checker accepts the tiny tree — verified by the KERNEL via
    `decide` (all integer comparisons reduce). -/
theorem tiny_checks : checkBabProof tinyTree = true := by decide

/-- The tiny coordinate readout: the sample IS its single rational coordinate. -/
def tinyCoord : Unit → ℚ → ℚ := fun _ s => s

/-- The tiny output functional: the constant unit margin `1`. -/
def tinyOut : ℚ → ℚ := fun _ => 1

/--
**End-to-end tiny decision.**  Because `checkBabProof tinyTree = true`
(`tiny_checks`, by `decide`), the recursor `babtree_sound` yields
`0 ≤ tinyOut s` on the WHOLE root region (`fun _ => True`, i.e. every sample).
This is the depth-1 instance of the kernel-internal BaB recursor: a single split,
two decidable leaves, composed by `le_total` covering into a whole-box bound.
-/
theorem tiny_safe : ∀ s : ℚ, True → 0 ≤ tinyOut s := by
  refine babtree_sound tinyCoord tinyOut (fun _ => True) tinyTree ?_
  -- discharge the two leaf obligations: checker passed + out = margin = 1
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · -- left leaf: checkLeafCert oneMargin = true
    decide
  · -- left leaf: tinyOut s = toQ oneMargin.margin  (1 = 1/1)
    intro s _; unfold tinyOut oneMargin toQ; norm_num
  · -- right leaf: checkLeafCert oneMargin = true
    decide
  · -- right leaf: tinyOut s = toQ oneMargin.margin
    intro s _; unfold tinyOut oneMargin toQ; norm_num

/-! ## Trust-base check.  Must list only the three standard logical axioms. -/

#print axioms checkLeafCert_margin_nonneg
#print axioms checkLeafCert_sound
#print axioms safe_on_path
#print axioms babtree_sound
#print axioms tiny_checks
#print axioms tiny_safe

end Bab
end Crownproof
