/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

INVENTION WAVE 3 — `spec_inherit` / multi-spec pruning (completeness-pruning C5,
the SAFE de-risking anchor).

Sealed conjecture (data/provenance/invention-wave-1-conjectures-2026-06-11.json,
angle `completeness-pruning`, conjecture
sha256 1b81276f483e0db8dcec168a7c9d40c9c7373a3d030cdea2b98dff2360cd3abb,
sealed 2026-06-11 BEFORE any proof attempt):

  "C5 — spec_inherit / multi-spec pruning: verified certificate inheritance for
   ny's implemented spec-pruning (SAFE; theorem-backs live engine behavior)."

ny's multi-objective BaB (engine/graph/multi_objective/root.rs, cited at
DEEPCONV §1: "verified specs are pruned during BaB") verifies a CONJUNCTION of
output specs and stops re-checking spec `j` on all descendants of any domain
where `j` is certified.  This module is the verified counterpart, in three legs:

  (i)  `spec_inherit` — a certified margin `0 ≤ out j` on a path `P` is inherited
       by every sub-path `P' ⊆ P` (in tree form: by every descendant of the
       closing node).  Two-line monotonicity: function composition of the
       sub-path inclusion `hsub` and the certificate `hcert`.

  (ii) `SpecTree` — a multi-spec proof tree with `close`-nodes that retire a spec
       for the whole subtree, and `ObligationsS` relative to the ACTIVE spec
       `Finset`; the decidable per-node obligation verifies each spec EXACTLY
       once per branch.  `spectree_sound`: if the obligations hold over the root
       region then ALL specs in the original set hold on the whole root box
       (structural induction GENERALIZING over the active `Finset`).

  (iii) `pruned_obligations_exact` — the exact pruned-WORK identity
       `checkedObligations + prunedObligations = specs.card * leafCount`,
       the spec-axis sibling of C1's Δdomains identity
       (`Complete.delta_domains_exact`, InventionWave2, LANDED).  Additive
       phrasing (no ℕ-subtraction in the identity), so the engine's pruning rule
       is theorem-backed: it can never skip a (spec, leaf) obligation that
       mattered, and it never re-checks one that was already inherited.

## RESULT STATUS — proved-as-stated, sorry-free, axioms = [propext, Classical.choice, Quot.sound]

All three legs are proved at the sealed statements.  See `#print axioms` block.

## HONESTY RAILS (verifier-mandated — this conjecture has the highest
##   "is this even a result?" risk in the set)

The mathematics is TRIVIAL monotonicity.  The ONLY claim made here is:
"verified counterpart of an IMPLEMENTED engine optimization, with exact
pruned-obligation accounting" — N1 first-formalization AT MOST.  NO literature
leg is attempted or implied: this is engine documentation, not new mathematics.

W2-flavor edge, stated plainly (same shape as `checkLeafSafe`'s `hval`): the
`close`-node's certificate binds to `out j` as an ASSUMED `Obligations`-level
premise (`checkLeafSafe (out j) lc path`), exactly as `BabProof.checkLeafSafe`'s
`hval` binds the leaf margin to the network output.  The decidable checker
verifies the rational margin is non-negative (`checkLeafCert`, kernel-reducible
integer cross-multiplication); the binding of that margin to the live network's
`out j` is the trusted spec-emission interface, NOT proven here — the verified
content is the inheritance/composition/counting around it.

## DELTAS vs the sealed Lean sketch (every delta documented)

The sealed sketch is reproduced FAITHFULLY.  Deltas, all surface-level:

  D1. NAMESPACE / SUBSTRATE.  The sketch writes `namespace Crownproof` and uses
      bare `LeafCert / checkLeafSafe / checkLeafCert_margin_nonneg / safe_on_path`.
      Those live in `Crownproof.Bab` (BabProof.lean), so this module opens
      `namespace Crownproof.Bab` and reuses them DIRECTLY — same names, same
      definitions, no shadow copies.

  D2. `SpecTree` SIGNATURE.  The sketch declares `SpecTree (Coord J : Type*)`
      with the constructor argument orders `leaf (lcs : J → LeafCert)`,
      `close (j) (lc) (rest)`, `split (c) (m) (lo hi)`.  Reproduced verbatim.
      (`Coord` and `J` are module `variable`s rather than explicit inductive
      parameters, the idiomatic Lean phrasing; the constructors are identical.)

  D3. `spec_inherit` GENERALITY.  Stated EXACTLY as sealed — over arbitrary
      `out : J → S → ℚ`, `path path' : S → Prop`.  It does not touch `LeafCert`
      at all (pure monotonicity), matching the sketch.

  D4. COUNTING DEFINITIONS.  The sketch names `checkedObligations`,
      `prunedObligations`, `leafCount` only inside the identity; their bodies are
      not sealed.  We give the canonical additive bodies (relative to the active
      `Finset`, mirroring `ObligationsS`) that make the sealed identity hold for
      EVERY tree, spec set, and region.  `pruned_obligations_exact` is proved at
      the EXACT sealed equation `checkedObligations specs p + prunedObligations
      specs p = specs.card * leafCount p`.

  This module does NOT depend on `cut_tree_dominance` (C2, the headline) — it is
  fully independent and lands even if the headline slips, seeding the shared
  SpecTree/counting machinery for any future C3/C4.

Builds on: `BabProof.LeafCert / checkLeafCert / checkLeafSafe /
checkLeafCert_margin_nonneg / safe_on_path / Obligations`
(crown-proofs/lean/Crownproof/BabProof.lean:103-253); the additive-counting style
of `Complete.delta_domains_exact`
(InventionWave2/adaptivebabsizecompletenesspruningC1.lean:337, LANDED wave 2);
`Finset.erase / card_erase_of_mem / mem_erase` (mathlib).
-/
import Crownproof.BabProof

namespace Crownproof
namespace Bab

open Finset

/-! ## 0. Setting.

A sample `s : S`; coordinates read by `coord : Coord → S → ℚ`; a finite family of
output specs indexed by `J` with margins `out : J → S → ℚ`.  "Spec `j` holds on
`s`" is `0 ≤ out j s` (the per-spec safety margin is non-negative), exactly the
`BabProof` `Safe` predicate, replicated per spec. -/

variable {S : Type*} {Coord : Type*} {J : Type*} [DecidableEq J]
variable (coord : Coord → S → ℚ) (out : J → S → ℚ)

/-! ## 1. Leg (i): `spec_inherit` — certified margins survive path strengthening.

The whole content of ny's spec-pruning: once spec `j` is certified on a domain
(path) `P`, it is certified on every sub-domain `P' ⊆ P`, so the engine need not
re-check it below.  Two-line monotonicity — function composition of the sub-path
inclusion `hsub` and the certificate `hcert`. -/

omit [DecidableEq J] in
/-- **Leg (i) — spec inheritance.**  A certified spec margin `0 ≤ out j` on path
`path` is inherited by every sub-path `path'` (`path' s → path s`).  Stated
EXACTLY as the sealed sketch; pure monotonicity, no certificate machinery. -/
theorem spec_inherit (j : J) (path path' : S → Prop)
    (hsub : ∀ s, path' s → path s)
    (hcert : ∀ s, path s → 0 ≤ out j s) :
    ∀ s, path' s → 0 ≤ out j s :=
  fun s hs' => hcert s (hsub s hs')

/-! ## 2. Leg (ii): the multi-spec proof tree and its decidable obligations.

`SpecTree` mirrors `BabProof`, adding a `close`-node that retires one spec for
its entire subtree.  `ObligationsS` is relative to an ACTIVE `Finset J`:

* `leaf lcs`  — every STILL-ACTIVE spec is discharged here by its own leaf cert.
* `close j lc rest` — spec `j` is closed HERE (its leaf cert `lc` discharges it
  on this path), and the obligations below run over `active.erase j` — `j` is
  never re-checked in the subtree.
* `split c m lo hi` — the two path-conjoined recursions, the SAME `coord c s ≤ m`
  / `m ≤ coord c s` half-box covering as `BabProof.Obligations`. -/

/-- The multi-spec branch-and-bound proof tree.  `close`-nodes retire a spec for
the whole subtree below them (the verified counterpart of "drop spec `j` from the
active set after certifying it on this domain").  Constructor shapes verbatim
from the sealed sketch (see DELTA D2). -/
inductive SpecTree (Coord J : Type*) where
  | leaf  (lcs : J → LeafCert)                              : SpecTree Coord J
  | close (j : J) (lc : LeafCert) (rest : SpecTree Coord J) : SpecTree Coord J
  | split (c : Coord) (m : ℚ) (lo hi : SpecTree Coord J)    : SpecTree Coord J

/-- Obligations relative to the ACTIVE spec `Finset`; `close`-nodes erase from it
(spec verified exactly once per branch).  `checkLeafSafe (out j) lc path` is
`BabProof.checkLeafSafe`: "the integer-pair checker accepted `lc`'s margin AND
that margin equals `out j` on this path" — the assumed `Obligations`-level
binding of the margin to the live spec (the W2-flavor edge, header). -/
def ObligationsS (active : Finset J) : SpecTree Coord J → (S → Prop) → Prop
  | .leaf lcs, path => ∀ j ∈ active, checkLeafSafe (out j) (lcs j) path
  | .close j lc rest, path =>
      checkLeafSafe (out j) lc path ∧ ObligationsS (active.erase j) rest path
  | .split c m lo hi, path =>
      ObligationsS active lo (fun s => path s ∧ coord c s ≤ m) ∧
      ObligationsS active hi (fun s => path s ∧ m ≤ coord c s)

/--
**Leg (ii) — multi-spec soundness.**  If the obligations hold over the root
region `inRegion` with active set `specs`, then EVERY spec in `specs` holds on
the whole root box.  Structural induction GENERALIZING over the active `Finset`
(the close case shrinks it).

* `leaf`  — each active spec `j` is discharged by `checkLeafCert_margin_nonneg`
  through its `checkLeafSafe` binding (`hval : out j s = toQ (lcs j).margin`),
  exactly as `babtree_sound`'s leaf case.
* `close j lc rest` — case-split on `j' = j` vs `j' ∈ active.erase j`:
  - `j' = j`: discharge spec `j` from the CLOSE certificate on THIS path, then
    push it down to the sample's path by `spec_inherit` through the identity
    sub-path (the leaf is reached by a strengthening of `inRegion`, so the close
    margin is inherited).
  - `j' ∈ active.erase j`: the IH on `rest` over `active.erase j`, with
    `Finset.mem_erase`.
* `split` — the verbatim `le_total (coord c s) m` covering from `safe_on_path`.
-/
theorem spectree_sound (specs : Finset J) (inRegion : S → Prop)
    (p : SpecTree Coord J)
    (hob : ObligationsS coord out specs p inRegion) :
    ∀ s, inRegion s → ∀ j ∈ specs, 0 ≤ out j s := by
  induction p generalizing specs inRegion with
  | leaf lcs =>
      intro s hs j hj
      -- `hob : ∀ j ∈ specs, checkLeafSafe (out j) (lcs j) inRegion`
      obtain ⟨hchk, hval⟩ := hob j hj
      have hm : (0 : ℚ) ≤ toQ (lcs j).margin := checkLeafCert_margin_nonneg _ hchk
      rw [hval s hs]; exact hm
  | close j lc rest ih =>
      intro s hs j' hj'
      obtain ⟨hclose, hrest⟩ := hob
      by_cases hjj : j' = j
      · -- spec `j` is closed at this node: discharge from the close certificate
        subst hjj
        obtain ⟨hchk, hval⟩ := hclose
        have hm : (0 : ℚ) ≤ toQ lc.margin := checkLeafCert_margin_nonneg _ hchk
        -- inherit the certified margin to the sample (identity sub-path here)
        have hcert : ∀ t, inRegion t → 0 ≤ out j' t := by
          intro t ht; rw [hval t ht]; exact hm
        exact spec_inherit out j' inRegion inRegion (fun _ h => h) hcert s hs
      · -- spec `j'` is still active below; recurse over `active.erase j`
        have hj'' : j' ∈ specs.erase j := Finset.mem_erase.mpr ⟨hjj, hj'⟩
        exact ih (specs.erase j) inRegion hrest s hs j' hj''
  | split c m lo hi ihlo ihhi =>
      intro s hs j hj
      obtain ⟨hlo, hhi⟩ := hob
      rcases le_total (coord c s) m with hle | hge
      · exact ihlo specs _ hlo s ⟨hs, hle⟩ j hj
      · exact ihhi specs _ hhi s ⟨hs, hge⟩ j hj

/-! ## 3. Leg (iii): the exact pruned-obligation identity.

`leafCount` counts leaf nodes (the per-branch frontier).  Naive cost is
`specs.card * leafCount` — every spec re-checked at every leaf.  Each `close`
node on spec `j ∈ active` PRUNES `j` across all `leafCount rest` leaves below it.

* `checkedObligations active p` — sum over leaves of the active-spec count
  reaching that leaf (the obligations the engine ACTUALLY checks).
* `prunedObligations active p` — the obligations the `close`-nodes eliminate.

Additive phrasing throughout (no ℕ-subtraction in the identity), exactly the
`Complete.delta_domains_exact` style. -/

/-- Number of leaf nodes (the per-branch frontier of `SpecTree`). -/
def leafCount : SpecTree Coord J → ℕ
  | .leaf _ => 1
  | .close _ _ rest => leafCount rest
  | .split _ _ lo hi => leafCount lo + leafCount hi

/-- Obligations the engine actually checks: at each leaf, one per still-active
spec; `close`-nodes shrink the active set below. -/
def checkedObligations (active : Finset J) : SpecTree Coord J → ℕ
  | .leaf _ => active.card
  | .close j _ rest => checkedObligations (active.erase j) rest
  | .split _ _ lo hi => checkedObligations active lo + checkedObligations active hi

/-- Obligations the `close`-nodes prune: a `close` on an ACTIVE spec `j`
eliminates `j` across all `leafCount rest` leaves below it (`0` if `j` was
already inactive — it could not have been pruned twice). -/
def prunedObligations (active : Finset J) : SpecTree Coord J → ℕ
  | .leaf _ => 0
  | .close j _ rest =>
      (if j ∈ active then leafCount rest else 0)
        + prunedObligations (active.erase j) rest
  | .split _ _ lo hi => prunedObligations active lo + prunedObligations active hi

/--
**Leg (iii) — the exact pruned-WORK identity.**  Checked + pruned obligations
equal the naive `active.card * leafCount` product, for EVERY tree, EVERY active
set, EVERY region-independent shape.  The spec-axis sibling of C1's Δdomains
identity: the pruning rule is theorem-backed — every (spec, leaf) obligation is
either checked exactly once or pruned exactly once, never skipped, never doubled.

Stated for an arbitrary active set; the sealed headline
`checkedObligations specs p + prunedObligations specs p = specs.card * leafCount p`
is the instance `active := specs` (below, `pruned_obligations_exact`).
-/
theorem pruned_obligations_exact_active (active : Finset J) (p : SpecTree Coord J) :
    checkedObligations (J := J) active p + prunedObligations (J := J) active p
      = active.card * leafCount (Coord := Coord) (J := J) p := by
  induction p generalizing active with
  | leaf lcs => simp [checkedObligations, prunedObligations, leafCount]
  | close j lc rest ih =>
      simp only [checkedObligations, prunedObligations, leafCount]
      by_cases hj : j ∈ active
      · -- closing an ACTIVE spec: erase drops the card by 1, prune adds the
        -- subtree's leaf count; the identity rebalances exactly.
        have hcard : (active.erase j).card + 1 = active.card :=
          Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr ⟨j, hj⟩) ▸
            (Finset.card_erase_add_one hj)
        rw [if_pos hj]
        have hih := ih (active.erase j)
        -- (checked + (lc + pruned)) = ((checked + pruned) + lc)
        --   = (active.erase j).card * leafCount rest + leafCount rest
        --   = ((active.erase j).card + 1) * leafCount rest = active.card * leafCount rest
        have : checkedObligations (active.erase j) rest
              + (leafCount rest + prunedObligations (active.erase j) rest)
            = ((active.erase j).card + 1) * leafCount (Coord := Coord) rest := by
          rw [Nat.add_mul, Nat.one_mul]; omega
        rw [this, hcard]
      · -- closing an INACTIVE spec prunes nothing and `erase` is a no-op on card.
        rw [if_neg hj]
        have herase : active.erase j = active := Finset.erase_eq_of_notMem hj
        rw [herase]
        have hih := ih active
        omega
  | split c m lo hi ihlo ihhi =>
      simp only [checkedObligations, prunedObligations, leafCount]
      have hlo := ihlo active
      have hhi := ihhi active
      rw [Nat.mul_add]; omega

/-- **The sealed headline identity (leg (iii)).**  Verbatim instance of
`pruned_obligations_exact_active` at `active := specs`:
`checkedObligations specs p + prunedObligations specs p = specs.card * leafCount p`. -/
theorem pruned_obligations_exact (specs : Finset J) (p : SpecTree Coord J) :
    checkedObligations (J := J) specs p + prunedObligations (J := J) specs p
      = specs.card * leafCount (Coord := Coord) (J := J) p :=
  pruned_obligations_exact_active specs p

/-! ## 4. DEMO — a depth-1 `SpecTree` closing one spec at the root, end-to-end
by `decide` on the Int-pair discipline (the sealed `builds_on` demo).

Two specs `J = Fin 2`, both with constant unit margin `out j s = 1`.  The tree
`close 0 oneMargin (leaf …)` closes spec `0` at the root, then a leaf discharges
the remaining active spec `1` (after `{0,1}.erase 0 = {1}`).  Every margin is the
integer pair `(1,1)`, so `checkLeafCert` reduces under `decide` in the kernel —
no `native_decide`. -/

/-- Two output specs. -/
abbrev DemoJ := Fin 2

/-- Both demo specs have the constant unit margin `1` (so `0 ≤ out j s`). -/
def demoOut : DemoJ → ℚ → ℚ := fun _ _ => 1

/-- Sample = its single rational coordinate, `Coord = Unit`. -/
def demoCoord : Unit → ℚ → ℚ := fun _ s => s

/-- Every leaf cert in the demo is the integer-pair margin `1/1`. -/
def demoCert : LeafCert := ⟨(1, 1)⟩

/-- The depth-1 demo tree: `close` spec `0` at the root over a single leaf that
discharges the remaining active specs. -/
def demoTree : SpecTree Unit DemoJ :=
  .close 0 demoCert (.leaf (fun _ => demoCert))

/-- The two specs of the demo. -/
def demoSpecs : Finset DemoJ := Finset.univ

/-- End-to-end: the depth-1 tree's obligations hold on the whole region
(`fun _ => True`).  Each leaf-cert check is `checkLeafCert demoCert = true`,
reduced by `decide` on the Int-pair discipline; each margin binding `out j s = 1`
is `rfl`/`norm_num`.  Hence by `spectree_sound`, ALL specs hold everywhere. -/
theorem demo_specs_hold : ∀ s : ℚ, True → ∀ j ∈ demoSpecs, 0 ≤ demoOut j s := by
  refine spectree_sound demoCoord demoOut demoSpecs (fun _ => True) demoTree ?_
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- close-node: checkLeafCert demoCert = true  (kernel `decide`, Int-pair)
    decide
  · -- close-node: demoOut 0 s = toQ demoCert.margin  (1 = 1/1)
    intro s _; unfold demoOut demoCert toQ; norm_num
  · -- the leaf: every still-active spec (here only `1`) discharged
    intro j _hj
    refine ⟨?_, ?_⟩
    · -- the leaf cert is the constant `demoCert` (`(fun _ => demoCert) j` β-reduces)
      show checkLeafCert demoCert = true
      decide
    · intro s _; unfold demoOut demoCert toQ; norm_num

/-- The pruned-obligation accounting on the demo, witnessed by `decide`:
2 specs × 1 leaf = 2 naive obligations; the root `close` prunes spec `0` across
the single leaf (1 pruned), leaving 1 checked.  `1 + 1 = 2 = 2 * 1`. -/
theorem demo_pruned_count :
    checkedObligations demoSpecs demoTree = 1
      ∧ prunedObligations demoSpecs demoTree = 1
      ∧ leafCount (Coord := Unit) (J := DemoJ) demoTree = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The headline identity, instantiated and CHECKED on the demo by `decide`:
`checkedObligations + prunedObligations = demoSpecs.card * leafCount`. -/
theorem demo_identity :
    checkedObligations demoSpecs demoTree + prunedObligations demoSpecs demoTree
      = demoSpecs.card * leafCount (Coord := Unit) (J := DemoJ) demoTree := by
  decide

/-! ## Trust-base check.  Must list only the three standard logical axioms. -/

#print axioms spec_inherit
#print axioms spectree_sound
#print axioms pruned_obligations_exact_active
#print axioms pruned_obligations_exact
#print axioms demo_specs_hold
#print axioms demo_pruned_count
#print axioms demo_identity

end Bab
end Crownproof
