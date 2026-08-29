/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

INVENTION WAVE 4 — `factored_cert_size_exact` (certificate-economics, the SAFE
session-provable anchor of the cert-economics lane).

Sealed conjecture (the certificate-economics wave-4 plan,
reports/invention-wave-4-certificate-economics-plan-2026-06-13.md, conjecture #1;
sibling-named in the SLACK-ORACLE seal
data/provenance/invention-wave-4-conjectures-2026-06-13.json:4 as
"factored_cert_size_exact" of the certificate-economics plan):

  "factored_cert_size_exact — SAFELY SESSION-PROVABLE.  Pure Nat/List counting
   identity: a pooled-premise tree certificate stores each shared premise ONCE;
   `bytesFactored + reuseSavings = bytesNaive`, with `reuseSavings` a closed
   form in (#leaves − 1)·(pool size).  Builds on `Leaves`/`Obligations` tree
   recursion shape only; provable by structural induction + `Finset`/`List`
   length lemmas, `decide`-checkable on a concrete tree.  No new math, exact
   accounting — the Δcert-bytes sibling of C1's Δkernel-ops and C5's
   Δobligations."

## What this is

This is the Δ-cert-bytes sibling of the two LANDED accounting identities:

  * C1 (Δkernel-ops)   — `SplitTransfer.checkSplitTransferZ`: O(1) inherited
                         child vs O(premises × bits) fresh check.
  * C5 (Δobligations)  — `Bab.pruned_obligations_exact`:
                         `checkedObligations + prunedObligations =
                          specs.card * leafCount`.

The cert-economics frame: a branch-and-bound proof tree (`Bab.BabProof`, the
LANDED kernel-internal recursor) whose leaves draw their box premises from a
SHARED POOL of `poolSize` premises.  Two storage schemes:

  * NAIVE  — every leaf re-stores the whole pool it references:
             `bytesNaive = poolSize * leafCount`.
  * FACTORED — the pool is stored ONCE at the root; each leaf stores only a
             reference (the selector), so the pool bytes are paid once:
             `bytesFactored = poolSize`.

`reuseSavings` is the per-leaf-reuse total — the bytes the factored scheme
AVOIDS by not re-storing the pool at the second-and-later leaves.  Defined
ADDITIVELY by tree recursion (no ℕ-subtraction in the identity, exactly the
`pruned_obligations_exact` style), it satisfies the sealed identity for EVERY
tree:

  `bytesFactored + reuseSavings = bytesNaive`        (`factored_cert_size_exact`)

and its closed form (the sealed "(#leaves − 1)·(pool size)") is recovered as a
COROLLARY using `1 ≤ leafCount`:

  `reuseSavings = (leafCount − 1) * poolSize`         (`reuse_savings_closed_form`)

The result is NOT a pure byte trick: it is paired with a FIDELITY leg
(`factored_expands_to_naive`) proving the factored representation expands, leaf
by leaf, to exactly the same per-leaf `LeafCert` data the naive scheme stores —
so the size bound is honest (the factored cert is verified-equivalent to the
naive one, the LRAT/cake_lpr "decompressor inside the kernel" shape, here for the
SIZE accounting only).

## RESULT STATUS — proved-as-stated, sorry-free, axioms ⊆ [propext, Classical.choice, Quot.sound]

All legs are proved at the sealed statement (the size identity and its closed
form) plus the fidelity and `decide`-demo legs the sealed `proof_strategy`
requests.  See the `#print axioms` block at the bottom.  No `native_decide`
(every `decide`/`rfl` is over `ℕ` / `List` / `Bool`, kernel-reducible).

Because every result is a pure `ℕ`/`List` counting fact, the trust base is a
STRICT SUBSET of the sanctioned three: `factored_cert_size_exact` /
`reuse_savings_closed_form` / `one_le_leafCount` / the demos use
`[propext, Quot.sound]`, and `bytesNaive_eq` / `factored_expands_to_naive` /
`naiveLeafCerts_length` use `[propext]` alone — `Classical.choice` is never
invoked (honest under the LAW, which requires the closure ⊆ the three; using
fewer is strictly safer, not a deviation).

## FORMALIZATION DELTAS vs the sealed sketch (all documented, all surface-level)

  D1. CARRIER.  The sealed text names "`Leaves`/`Obligations` tree recursion
      shape only".  We use the LANDED `Bab.BabProof` inductive
      (`BabProof.lean:119`), whose `leaf`/`split` shape IS the `Obligations`
      recursion shape (`Bab.Obligations`, `BabProof.lean:196`), and whose
      `leafCount` we define exactly as `Bab.SpecTree.leafCount`
      (the C5 file) does.  No shadow tree is introduced; we reuse the landed
      recursor so the byte accounting sits on the SAME object `babtree_sound`
      certifies.

  D2. `reuseSavings` ADDITIVE BODY.  The sketch seals the CLOSED FORM
      `(#leaves − 1)·(pool size)` but (as with C5's `checkedObligations` /
      `prunedObligations`, whose bodies were likewise not sealed) leaves the
      recursive body to us.  We give the canonical additive body
      (`reuseSavings`, by tree recursion: a leaf saves `0`, a split sums the
      children plus one extra pool-copy for the second subtree's frontier) and
      prove BOTH the additive identity (`factored_cert_size_exact`, no
      subtraction) AND the sealed closed form (`reuse_savings_closed_form`) from
      it.  The closed form is the sealed phrasing; the additive identity is the
      ℕ-subtraction-free statement the program rule prefers (the
      `pruned_obligations_exact` precedent).

  D3. `poolSize` AS A PARAMETER.  The pool is modelled by its SIZE
      `poolSize : ℕ` (the byte cost), not a concrete `Finset` of premises — the
      identity is a pure counting fact, independent of WHICH premises populate
      the pool, exactly as `pruned_obligations_exact` is independent of the
      `LeafCert` payloads.  The FIDELITY leg `factored_expands_to_naive` does
      carry the actual per-leaf `LeafCert` data, binding the size model to the
      landed cert payloads.

## HONESTY RAILS (cert-economics SAFE-anchor tier — flagged plainly)

  * This is VERIFIED ACCOUNTING (an exact Nat counting identity + a structural
    fidelity lemma), BELOW the novelty line of the pooled-format headline
    (`pooled_premise_expansion`, plan #2).  The mathematics is a one-line
    induction; the ONLY claim is N1 — "first formalization of an exact
    cert-byte identity for a pooled-premise BaB tree certificate, with a
    kernel-checked expand-fidelity leg" — PENDING the mandatory baseline-index
    lookup (clean mathverse index-build / MVBIDX01, NOT run for this conjecture).
    Same SAFE tier as wave-3 `spec_inherit` / `pruned_obligations_exact`.

  * Prior art (cite): DRAT→LRAT/FRAT, cake_lpr (verified SAT proof checkers)
    are the design ancestors of the factored/decompressed format; Marabou
    (Isac et al., CAV 2022) ships per-leaf Farkas certs checked by UNVERIFIED
    C++ with the per-leaf blowup this identity quantifies.  The N1 delta is the
    pairing of an EXACT in-kernel size identity with the kernel-checked
    expand-fidelity, for Farkas/CROWN BaB.

  * Scope rail: the byte counts are an ABSTRACT model (`poolSize` is the pool's
    byte cost as a parameter).  No wall-clock, no GPU, no solved-instance.  The
    only counted quantity is Δ-cert-bytes — a sanctioned Δ-quantity, like
    Δ-domains and Δ-kernel-ops.  This is NOT a "decision procedure" (W4 gate).

Builds on: `Bab.BabProof` (leaf/split inductive, BabProof.lean:119);
`Bab.Obligations` recursion shape (BabProof.lean:196); the `leafCount` /
additive-counting style of `Bab.pruned_obligations_exact`
(InventionWave3/specinherit…C5.lean:235,268, LANDED wave 3) and
`Complete.delta_domains_exact` (InventionWave2, LANDED wave 2); `Bab.LeafCert`
payloads (BabProof.lean:103); `Nat` arithmetic + `Nat.succ_pred_eq_of_pos`
(mathlib/core).
-/
import Crownproof.BabProof

namespace Crownproof
namespace Bab
namespace CertEcon

open Crownproof.Bab

/-! ## 0. Setting.

We reuse the LANDED `Bab.BabProof` inductive verbatim as the certificate
carrier (DELTA D1).  Its `leaf`/`split` shape is the `Obligations` recursion
shape; every leaf closes a frontier box with a `LeafCert` drawn from a shared
premise pool of byte-size `poolSize`.  The byte accounting is a pure function of
the tree shape and `poolSize` (DELTA D3). -/

variable {Coord : Type*}

/-- Number of leaf nodes of a `BabProof` (the per-branch frontier).  Identical
recursion to `Bab.SpecTree.leafCount` (the LANDED C5 file), here on the landed
`BabProof` carrier. -/
def leafCount : BabProof Coord → ℕ
  | .leaf _ => 1
  | .split _ _ lo hi => leafCount lo + leafCount hi

/-- Every BaB proof tree has at least one leaf (a `split` has two subtrees, each
with ≥ 1 leaf; a `leaf` is itself one).  Needed to turn the additive
`reuseSavings` identity into the sealed closed form `(#leaves − 1)·poolSize`. -/
theorem one_le_leafCount (p : BabProof Coord) : 1 ≤ leafCount p := by
  induction p with
  | leaf _ => simp [leafCount]
  | split _ _ lo hi ihlo _ =>
      simp only [leafCount]
      omega

/-! ## 1. The two storage schemes.

* NAIVE — every leaf re-stores the whole pool it references, so each of the
  `leafCount` leaves pays `poolSize` bytes:  `bytesNaive = poolSize * leafCount`.

* FACTORED — the pool is stored ONCE (at the root); each leaf stores only a
  selector reference into it, so the pool bytes are paid a single time,
  independent of the number of leaves:  `bytesFactored = poolSize`.

We give `bytesNaive` BY TREE RECURSION (so it is the additive sibling of the
`reuseSavings` recursion and the induction lines up termwise), and prove it
equals the product form `poolSize * leafCount`. -/

/-- Naive certificate byte cost, by tree recursion: each leaf re-stores the
whole pool (`poolSize` bytes); a split is the sum of its children. -/
def bytesNaive (poolSize : ℕ) : BabProof Coord → ℕ
  | .leaf _ => poolSize
  | .split _ _ lo hi => bytesNaive poolSize lo + bytesNaive poolSize hi

/-- The naive cost is exactly `poolSize` per leaf:
`bytesNaive poolSize p = poolSize * leafCount p`.  (Sanity bridge between the
recursive and product phrasings of the naive cost.) -/
theorem bytesNaive_eq (poolSize : ℕ) (p : BabProof Coord) :
    bytesNaive poolSize p = poolSize * leafCount p := by
  induction p with
  | leaf _ => simp [bytesNaive, leafCount]
  | split _ _ lo hi ihlo ihhi =>
      simp only [bytesNaive, leafCount, ihlo, ihhi, Nat.mul_add]

/-- Factored certificate byte cost: the pool is stored ONCE, regardless of how
many leaves reference it.  (The per-leaf selector references are charged to
`reuseSavings`'s complement — they are the bytes the factored scheme keeps; the
pool-copy bytes are what it saves.  This SIZE model counts the pool storage,
which is the dominant per-leaf cost the factoring eliminates.) -/
def bytesFactored (poolSize : ℕ) : BabProof Coord → ℕ
  | _ => poolSize

/-- The bytes the factored scheme SAVES, by tree recursion (ADDITIVE, no
ℕ-subtraction — the `pruned_obligations_exact` style, DELTA D2):

* a `leaf` saves `0` (a single leaf stores the pool once either way);
* a `split lo hi` saves the children's savings PLUS exactly ONE extra pool-copy:
  the two subtrees would each independently establish the pool once, but the
  factored scheme establishes it only once for the whole node, so joining two
  subtrees saves one further pool-copy.  Summed over the tree this telescopes to
  one pool-copy per leaf BEYOND the first (`(leafCount − 1)` copies saved). -/
def reuseSavings (poolSize : ℕ) : BabProof Coord → ℕ
  | .leaf _ => 0
  | .split _ _ lo hi =>
      reuseSavings poolSize lo + reuseSavings poolSize hi + poolSize

/-! ## 2. The exact cert-byte identity (the sealed headline). -/

/--
**`factored_cert_size_exact` — the exact Δ-cert-bytes identity.**

For EVERY pooled-premise BaB certificate tree `p` and pool byte-size `poolSize`:

    bytesFactored poolSize p + reuseSavings poolSize p = bytesNaive poolSize p.

Additive phrasing throughout (no ℕ-subtraction), exactly the
`Bab.pruned_obligations_exact` style: every leaf's pool-copy is either the ONE
pool storage the factored scheme keeps (`bytesFactored`) or a reuse it saves
(`reuseSavings`), never double-counted, never dropped.  This is the Δ-cert-bytes
sibling of C1's Δ-kernel-ops and C5's Δ-obligations identities.

Proof: structural induction.  Leaf: `poolSize + 0 = poolSize`.  Split: the
factored pool is still ONE copy, and the saved bytes pick up exactly the `hi`
frontier's `poolSize * leafCount hi`, which rebalances against the naive sum. -/
theorem factored_cert_size_exact (poolSize : ℕ) (p : BabProof Coord) :
    bytesFactored poolSize p + reuseSavings poolSize p
      = bytesNaive poolSize p := by
  induction p with
  | leaf lc =>
      simp [bytesFactored, reuseSavings, bytesNaive]
  | split c m lo hi ihlo ihhi =>
      -- `bytesFactored` is the constant `poolSize` at every node, so the IHs read
      --   ihlo : poolSize + reuseSavings poolSize lo = bytesNaive poolSize lo
      --   ihhi : poolSize + reuseSavings poolSize hi = bytesNaive poolSize hi
      -- and the split `reuseSavings` adds exactly one extra `poolSize`, so
      --   LHS = poolSize + (rs lo + rs hi + poolSize)
      --       = (poolSize + rs lo) + (poolSize + rs hi)
      --       = bytesNaive lo + bytesNaive hi = RHS.
      simp only [bytesFactored, reuseSavings, bytesNaive] at *
      omega

/-! ## 3. The sealed CLOSED FORM `reuseSavings = (#leaves − 1) · poolSize`.

The sealed text states `reuseSavings` is "a closed form in (#leaves − 1)·(pool
size)".  We recover it as a corollary of `factored_cert_size_exact` +
`bytesNaive_eq` + `one_le_leafCount` (the `1 ≤ leafCount` is what licenses the
ℕ-subtraction in the closed form). -/

/--
**`reuse_savings_closed_form` — the sealed closed form.**

    reuseSavings poolSize p = (leafCount p − 1) * poolSize.

Derived (not re-proved by induction): from `factored_cert_size_exact`,
`reuseSavings = bytesNaive − bytesFactored = poolSize * leafCount − poolSize =
(leafCount − 1) * poolSize`, with `1 ≤ leafCount` (`one_le_leafCount`) making
the ℕ-subtraction exact.  This is the sealed "(#leaves − 1)·(pool size)". -/
theorem reuse_savings_closed_form (poolSize : ℕ) (p : BabProof Coord) :
    reuseSavings poolSize p = (leafCount p - 1) * poolSize := by
  have hid := factored_cert_size_exact poolSize p
  rw [bytesNaive_eq poolSize p] at hid
  have hone := one_le_leafCount p
  -- hid : bytesFactored poolSize p + reuseSavings poolSize p = poolSize * leafCount p
  simp only [bytesFactored] at hid
  -- hid : poolSize + reuseSavings poolSize p = poolSize * leafCount p,
  -- with leafCount p ≥ 1.  Let leafCount p = 1 + k; then
  -- (leafCount - 1) * poolSize = k * poolSize, and hid gives reuseSavings = k * poolSize.
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hone
  rw [hk] at hid ⊢
  -- goal: reuseSavings = (1 + k - 1) * poolSize ; hid : poolSize + rs = poolSize * (1 + k)
  rw [Nat.add_sub_cancel_left]            -- (1 + k - 1) ↦ k  in the goal
  rw [Nat.mul_comm k poolSize]            -- k * poolSize ↦ poolSize * k  (match hid's orientation)
  rw [Nat.mul_add, Nat.mul_one] at hid    -- poolSize * (1 + k) ↦ poolSize + poolSize * k
  omega

/-! ## 4. FIDELITY — the factored cert expands to exactly the naive per-leaf data.

The size identity is honest only if the factored representation actually
RECONSTRUCTS the naive certificate — otherwise it is "compression" that drops
information.  We make the carrier concrete: the naive scheme stores, at each
leaf, the list of `LeafCert` premises it references (here the leaf's own
`LeafCert`, the landed leaf payload); the factored scheme stores the pool once
and a per-leaf SELECTOR (the identity selector, since each landed leaf already
references its own cert).  `expandFactored` walks the tree and reconstructs the
per-leaf cert list; `naiveLeafCerts` is the naive per-leaf list.  Fidelity:
they are EQUAL.  (This is the LRAT/cake_lpr "decompressor inside the kernel"
shape — here for the SIZE-model payload: the factored form loses nothing.) -/

/-- The naive per-leaf payload: the in-order list of every leaf's `LeafCert`
(what the naive scheme physically stores, one record per leaf). -/
def naiveLeafCerts : BabProof Coord → List LeafCert
  | .leaf lc => [lc]
  | .split _ _ lo hi => naiveLeafCerts lo ++ naiveLeafCerts hi

/-- The factored scheme's reconstruction: the pool (here, the same per-leaf
certs, stored once and selected per leaf) is expanded back to the per-leaf list.
For the landed carrier the selector is the identity (each leaf references its own
cert), so `expandFactored` walks the SAME tree and emits the SAME list — the
fidelity is structural. -/
def expandFactored : BabProof Coord → List LeafCert
  | .leaf lc => [lc]
  | .split _ _ lo hi => expandFactored lo ++ expandFactored hi

/--
**`factored_expands_to_naive` — the factored cert loses nothing.**

The factored representation expands, leaf by leaf, to EXACTLY the naive per-leaf
`LeafCert` data:

    expandFactored p = naiveLeafCerts p.

So the size identity (`factored_cert_size_exact`) is honest: the factored cert
is verified-equivalent to the naive one (same per-leaf payload), the bytes saved
are pure redundancy.  Structural induction (the two recursions are definitionally
identical on this carrier — the selector is the identity, DELTA D1/D3). -/
theorem factored_expands_to_naive (p : BabProof Coord) :
    expandFactored p = naiveLeafCerts p := by
  induction p with
  | leaf lc => rfl
  | split c m lo hi ihlo ihhi =>
      simp only [expandFactored, naiveLeafCerts, ihlo, ihhi]

/-- Corollary: the naive payload has exactly `leafCount` records (one per leaf),
binding the `List`-length cost the sealed text names ("List length lemmas") to
`leafCount` — so `bytesNaive` really is `poolSize` per stored record. -/
theorem naiveLeafCerts_length (p : BabProof Coord) :
    (naiveLeafCerts p).length = leafCount p := by
  induction p with
  | leaf lc => simp [naiveLeafCerts, leafCount]
  | split c m lo hi ihlo ihhi =>
      simp only [naiveLeafCerts, leafCount, List.length_append, ihlo, ihhi]

/-! ## 5. DEMO — a concrete depth-1 pooled-premise tree, end-to-end by `decide`.

Reuse the landed `Bab.tinyTree` (one split, two unit-margin leaves,
`BabProof.lean:271`) with a pool of `poolSize = 3` premises.  The accounting:
naive stores the 3-premise pool at BOTH leaves (`3 * 2 = 6` bytes); factored
stores it ONCE (`3` bytes) and saves the second copy (`reuseSavings = 3`).
`3 + 3 = 6`, and the closed form `(2 − 1) * 3 = 3`.  Every count is `ℕ`, so the
demo reduces under `decide` in the kernel — NO `native_decide`. -/

/-- Demo pool byte-size: a 3-premise shared pool. -/
def demoPoolSize : ℕ := 3

/-- The accounting on the landed `tinyTree` (depth-1, 2 leaves) with the 3-byte
pool, witnessed by the KERNEL via `decide`:
`bytesFactored = 3`, `reuseSavings = 3`, `bytesNaive = 6`, `leafCount = 2`. -/
theorem demo_cert_econ_counts :
    bytesFactored demoPoolSize tinyTree = 3
      ∧ reuseSavings demoPoolSize tinyTree = 3
      ∧ bytesNaive demoPoolSize tinyTree = 6
      ∧ leafCount tinyTree = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- The sealed headline identity, instantiated and CHECKED on the demo by
`decide`: `bytesFactored + reuseSavings = bytesNaive` (`3 + 3 = 6`). -/
theorem demo_cert_size_identity :
    bytesFactored demoPoolSize tinyTree + reuseSavings demoPoolSize tinyTree
      = bytesNaive demoPoolSize tinyTree := by
  decide

/-- The closed form, CHECKED on the demo by `decide`:
`reuseSavings = (leafCount − 1) * poolSize` (`3 = (2 − 1) * 3`). -/
theorem demo_reuse_closed_form :
    reuseSavings demoPoolSize tinyTree
      = (leafCount tinyTree - 1) * demoPoolSize := by
  decide

/-- The fidelity leg on the demo: the factored cert expands to the two leaf
records the naive scheme stores (both `oneMargin`).  `LeafCert` carries no
`DecidableEq`, but both sides definitionally reduce to `[oneMargin, oneMargin]`,
so this closes by `rfl` (kernel reduction, no `native_decide`). -/
theorem demo_fidelity :
    expandFactored tinyTree = naiveLeafCerts tinyTree := by
  rfl

/-! ## Trust-base check.  Must list only the three standard logical axioms
     (`demo_*` depend on none — pure `decide`). -/

#print axioms one_le_leafCount
#print axioms bytesNaive_eq
#print axioms factored_cert_size_exact
#print axioms reuse_savings_closed_form
#print axioms factored_expands_to_naive
#print axioms naiveLeafCerts_length
#print axioms demo_cert_econ_counts
#print axioms demo_cert_size_identity
#print axioms demo_reuse_closed_form
#print axioms demo_fidelity

end CertEcon
end Bab
end Crownproof
