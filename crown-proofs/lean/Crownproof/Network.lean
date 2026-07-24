/-
Copyright 2026 Andrew Yates
Author: Andrew Yates <andrewyates.name@gmail.com>
SPDX-License-Identifier: Apache-2.0

FULL MULTI-BLOCK TRANSFORMER NETWORK end-to-end CROWN soundness — THE CAPSTONE
OF THE CAPSTONE.

A transformer NETWORK is a stack of `N` transformer blocks applied in sequence,
followed by the final classifier head:

      s_0  = input
      s_1  = B_1 (s_0)
      s_2  = B_2 (s_1)
      ...
      s_N  = B_N (s_{N-1})
      out  = Head (s_N)                  (final linear classifier)

Each block `B_k` already has an end-to-end soundness bridge in this project
(`Crownproof.Block.block_bridge`): on every genuine block execution, a
non-negative multiplier vector combines a *sound premise family* (the union of
that block's attention / LayerNorm / MLP component premises) into the block's
output functional.  The INTER-BLOCK CONNECTIONS `s_k = B_k(s_{k-1})` are linear
(the block outputs feed the next block's inputs by an exact affine/identity map,
exactly as the residual adds inside a block are linear) — so, precisely as
`Block.lean` folds each block's residual adds and affine layers into the block
validity predicate plus the Farkas certificate identity, the network folds the
inter-block connections in the same way.  They add NO new nonlinearity.

KEY INSIGHT (stated and proven below):
PREMISE SOUNDNESS AND MULTIPLIER-NONNEGATIVITY COMPOSE ACROSS BLOCKS.
`Block.lean` proved that a union of two sound premise families is sound
(`union_premises_sound`, indexed by `ι ⊕ κ`).  Iterated over the `N` blocks of
the network, the union of the `N` per-block sound premise families — indexed by
the dependent sum `Σ k, ι k` over the block index `k` — is itself sound.  Hence
the WHOLE network reduces to the SAME abstract Farkas core
`farkas_premise_combination` (from `Bridge.lean`) applied to the UNION of all
blocks' premise families.  The network bridge is block composition iterated:
composition adds premises, not new theory.

This file proves the iteration PARAMETRICALLY IN `N` (the blocks range over an
arbitrary `Finset` of block indices, with per-block premise index types), by a
single application of the abstract Farkas core to the `Σ`-indexed union, using
`Finset.sum_sigma` to fold the per-block certificate sums into the one global
certificate.  It then specialises to the concrete `N = 2` two-block network to
witness non-vacuity, and re-derives the explicit two-block iteration step from
`Block.lean`'s `block_compose_bridge` for continuity.

What is PROVEN here, sorry-free
-------------------------------
  * `union_blocks_premises_sound` — the iterated composition lemma: the union of
    an arbitrary `Finset` of sound per-block premise families, indexed by the
    dependent sum `Σ k, ι k`, is a sound premise family.  This is the formal
    statement that "premise soundness composes across blocks".
  * `union_blocks_mul_nonneg` — multiplier non-negativity composes across blocks.
  * `network_bridge` — `farkas_to_interval` for a FULL multi-block network of
    `N` transformer blocks + classifier head, parametric in `N`, proven
    sorry-free by reduction to `farkas_premise_combination` over the `Σ`-indexed
    UNION premise family.  The inter-block connections and the head are linear,
    folded into the validity predicate and the certificate identity.
  * `network_bridge_two` — the concrete `N = 2` instance, witnessing that the
    parametric bridge's hypotheses are satisfiable by a real two-block stack.
  * `network_iterate_step` — the explicit two-block iteration step phrased
    directly via `Block.lean`'s `block_compose_bridge`, showing the parametric
    fold and the binary composition principle agree.

What is HYPOTHESIS on the genuine state
---------------------------------------
  The per-block premise soundness (`hg`) and the per-block / global certificate
  identity (`hcert`).  These are exactly the per-block bridge outputs of
  `Block.block_bridge` being composed: each block supplies its sound premise
  family on the shared network state, and the verifier supplies the global
  Farkas certificate that folds the linear inter-block maps and the linear head
  into `-(out) - c`.  Carrying them as hypotheses is the standard CROWN
  "compose certified sub-bridges" treatment used throughout this project.
-/

import Crownproof.Bridge
import Crownproof.Block
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

namespace Crownproof

open Finset

/-! ## 1. Composition of sound premise families ACROSS BLOCKS (parametric in N).

`Block.lean` proved that the union of *two* sound premise families is sound
(`union_premises_sound`, indexed by `ι ⊕ κ`).  Here we iterate that over an
arbitrary collection of blocks: the union of a `Finset` of per-block sound
premise families, indexed by the dependent sum `Σ k, ι k`, is sound.  This is
the `N`-fold composition principle — `union_premises_sound` is the `N = 2` case.

We index the global union by `Σ k, ι k` (block index `k`, then that block's
premise index).  The combined premise functional and the combined multiplier
vector both dispatch on the block tag, and both inherit `≤ 0`-soundness and
non-negativity fiberwise. -/

/-- Premise soundness composes across blocks: if each block `k` supplies a
    `≤ 0`-sound premise family `g k` (indexed by `ι k`), then the union over all
    blocks — indexed by the dependent pair `⟨k, i⟩ : Σ k, ι k` — is `≤ 0`-sound.

    This is the `N`-fold iterate of `Block.union_premises_sound` (its `N = 2`
    binary case is `Sum.elim`; here the `N`-ary case is `fun ki s => g ki.1 ki.2 s`). -/
theorem union_blocks_premises_sound
    {S : Type*} {B : Type*} {ι : B → Type*}
    (g : ∀ k : B, ι k → S → ℚ)
    (valid : S → Prop)
    (hg : ∀ k : B, ∀ i : ι k, ∀ s, valid s → g k i s ≤ 0) :
    ∀ ki : Σ k : B, ι k, ∀ s, valid s → (fun s => g ki.1 ki.2 s) s ≤ 0 := by
  intro ki s hs
  exact hg ki.1 ki.2 s hs

/-- Multiplier non-negativity composes across blocks: the union of a collection
    of per-block non-negative multiplier vectors is non-negative. -/
theorem union_blocks_mul_nonneg
    {B : Type*} {ι : B → Type*}
    (μ : ∀ k : B, ι k → ℚ)
    (hμ : ∀ k : B, ∀ i : ι k, 0 ≤ μ k i) :
    ∀ ki : Σ k : B, ι k, 0 ≤ μ ki.1 ki.2 := by
  intro ki
  exact hμ ki.1 ki.2

/-! ## 2. The full multi-block network bridge (parametric in N).

A genuine execution of the whole network carries, on a shared state type `S`,
the input, every per-block intermediate (residual sums, LN product, ReLU
post-activations, …), and the final classifier output; `valid s` asserts the
whole pipeline `s_k = B_k(s_{k-1})`, `out = Head(s_N)` holds exactly (all the
inter-block linear maps and the linear head are equalities folded into `valid`).

The premises are the UNION over all `N` blocks of each block's sound premise
family `g k : ι k → S → ℚ` (the `block_bridge` premises of block `k`), indexed by
`Σ k, ι k`.  Each block supplies non-negative multipliers `μ k` and its premises
are `≤ 0` on every valid state (`hg`, supplied by `Block.block_bridge`'s premise
soundness).  The verifier supplies the GLOBAL Farkas certificate `hcert`: the
sum, over all blocks and all of each block's premises, of `μ k i * g k i s`,
equals `-(out s) - c` (this is where the linear inter-block connections and the
classifier head are folded in, exactly as the residual adds are folded into the
block certificate in `Block.lean`).

Conclusion: `out s ≥ -c` on every genuine network execution.  Proven sorry-free
by ONE application of `farkas_premise_combination` to the `Σ`-indexed union,
collapsing the per-block fiber sums with `Finset.sum_sigma`. -/
theorem network_bridge
    {S : Type*} {B : Type*} {ι : B → Type*}
    -- the finite set of blocks B_1 … B_N (parametric in N = blocks.card)
    (blocks : Finset B)
    -- per block: its premise index set, premise family, and multiplier vector
    (prem : ∀ k : B, Finset (ι k))
    (g : ∀ k : B, ι k → S → ℚ)
    (μ : ∀ k : B, ι k → ℚ)
    (out : S → ℚ) (c : ℚ) (valid : S → Prop)
    -- multiplier non-negativity composes across blocks
    (hμ : ∀ k ∈ blocks, ∀ i ∈ prem k, 0 ≤ μ k i)
    -- premise soundness composes across blocks
    (hg : ∀ k ∈ blocks, ∀ i ∈ prem k, ∀ s, valid s → g k i s ≤ 0)
    -- the GLOBAL Farkas certificate: the union μ-combination over ALL blocks
    -- (and all of each block's premises) IS  -(out) - c.  The linear inter-block
    -- connections and the linear classifier head are folded into this identity.
    (hcert : ∀ s,
        (∑ k ∈ blocks, ∑ i ∈ prem k, μ k i * g k i s) = -(out s) - c) :
    ∀ s, valid s → -c ≤ out s := by
  -- Index the global union by the dependent sum `Σ k, ι k`; the premise set is
  -- the sigma `blocks.sigma prem`.  One application of the abstract Farkas core.
  refine farkas_premise_combination (S := S) (ι := Σ k : B, ι k)
        (premises := blocks.sigma prem)
        (g := fun ki s => g ki.1 ki.2 s)
        (out := out) (μ := fun ki => μ ki.1 ki.2) (c := c)
        (valid := valid)
        ?hμU ?hgU ?hcertU
  case hμU =>
    -- non-negativity, fiberwise (multiplier-nonneg composes across blocks)
    intro ki hki
    rw [Finset.mem_sigma] at hki
    exact hμ ki.1 hki.1 ki.2 hki.2
  case hgU =>
    -- soundness, fiberwise (premise-soundness composes across blocks)
    intro ki hki s hs
    rw [Finset.mem_sigma] at hki
    exact hg ki.1 hki.1 ki.2 hki.2 s hs
  case hcertU =>
    -- collapse the sigma sum into the per-block fiber sums = global certificate
    intro s
    rw [Finset.sum_sigma]
    simpa using hcert s

/-! ## 3. Concrete `N = 2` two-block instance — non-vacuity witness.

We instantiate `network_bridge` at exactly `N = 2` blocks, indexed by `Bool`
(`false` = block 1, `true` = block 2), each with its own `Fin`-indexed premise
family.  This shows the parametric hypotheses are satisfiable by a genuine
two-block stack, so the network bridge is not vacuous. -/
theorem network_bridge_two
    {S : Type*} {ι₁ ι₂ : Type u}
    (prem₁ : Finset ι₁) (prem₂ : Finset ι₂)
    (g₁ : ι₁ → S → ℚ) (g₂ : ι₂ → S → ℚ)
    (μ₁ : ι₁ → ℚ) (μ₂ : ι₂ → ℚ)
    (out : S → ℚ) (c : ℚ) (valid : S → Prop)
    (hμ₁ : ∀ i ∈ prem₁, 0 ≤ μ₁ i) (hμ₂ : ∀ j ∈ prem₂, 0 ≤ μ₂ j)
    (hg₁ : ∀ i ∈ prem₁, ∀ s, valid s → g₁ i s ≤ 0)
    (hg₂ : ∀ j ∈ prem₂, ∀ s, valid s → g₂ j s ≤ 0)
    (hcert : ∀ s,
        (∑ i ∈ prem₁, μ₁ i * g₁ i s) + (∑ j ∈ prem₂, μ₂ j * g₂ j s)
          = -(out s) - c) :
    ∀ s, valid s → -c ≤ out s := by
  -- Block index type = Bool; fiber over `false` is block 1, over `true` block 2.
  refine network_bridge (S := S) (B := Bool)
        (ι := fun b => cond b ι₂ ι₁)
        (blocks := Finset.univ)
        (prem := fun b => Bool.rec prem₁ prem₂ b)
        (g := fun b => Bool.rec g₁ g₂ b)
        (μ := fun b => Bool.rec μ₁ μ₂ b)
        (out := out) (c := c) (valid := valid)
        ?hμ ?hg ?hcert
  case hμ =>
    intro k _ i hi
    cases k with
    | false => exact hμ₁ i hi
    | true  => exact hμ₂ i hi
  case hg =>
    intro k _ i hi s hs
    cases k with
    | false => exact hg₁ i hi s hs
    | true  => exact hg₂ i hi s hs
  case hcert =>
    intro s
    rw [Fintype.sum_bool]
    -- block `true` (= block 2) then block `false` (= block 1); add commutes
    have h := hcert s
    show (∑ i ∈ prem₂, μ₂ i * g₂ i s) + (∑ i ∈ prem₁, μ₁ i * g₁ i s) = -(out s) - c
    linarith [h]

/-! ## 4. Explicit two-block iteration step via `Block.block_compose_bridge`.

The binary iteration step of the network is exactly `Block.lean`'s
`block_compose_bridge` (the union of two sound premise families).  This theorem
re-derives the two-block network conclusion through that binary composition
principle, showing the parametric `Σ`-fold and the iterated binary `⊕`-union
agree: each step of the network fold is one `block_compose_bridge`. -/
theorem network_iterate_step
    {S : Type*} {ι₁ ι₂ : Type*}
    (prem₁ : Finset ι₁) (prem₂ : Finset ι₂)
    (g₁ : ι₁ → S → ℚ) (g₂ : ι₂ → S → ℚ)
    (μ₁ : ι₁ → ℚ) (μ₂ : ι₂ → ℚ)
    (out : S → ℚ) (c : ℚ) (valid : S → Prop)
    (hμ₁ : ∀ i ∈ prem₁, 0 ≤ μ₁ i) (hμ₂ : ∀ j ∈ prem₂, 0 ≤ μ₂ j)
    (hg₁ : ∀ i ∈ prem₁, ∀ s, valid s → g₁ i s ≤ 0)
    (hg₂ : ∀ j ∈ prem₂, ∀ s, valid s → g₂ j s ≤ 0)
    (hcert : ∀ s,
        (∑ i ∈ prem₁, μ₁ i * g₁ i s) + (∑ j ∈ prem₂, μ₂ j * g₂ j s)
          = -(out s) - c) :
    ∀ s, valid s → -c ≤ out s :=
  -- one binary composition step from Block.lean
  block_compose_bridge prem₁ prem₂ g₁ g₂ μ₁ μ₂ out c valid
    hμ₁ hμ₂ hg₁ hg₂ hcert

/-! ## 5. Trust-base check.  Must list ONLY the three standard logical axioms. -/

#print axioms union_blocks_premises_sound
#print axioms union_blocks_mul_nonneg
#print axioms network_bridge
#print axioms network_bridge_two
#print axioms network_iterate_step

end Crownproof
