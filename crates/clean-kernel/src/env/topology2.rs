// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Topology structures for Environment (continued)
//!
//! This module contains topology init_* and has_* functions:
//! - Suspension
//! - Vector bundles
//! - Coproducts

use crate::env::{EnvError, Environment};

impl Environment {
    // ================================================================
    // TOPOLOGY.SUSPENSION PRIMITIVES
    // ================================================================
    //
    // Suspension Σα is a fundamental construction in algebraic topology.
    // Given a topological space α, the suspension Σα is formed by:
    // - Taking α × [-1, 1]
    // - Collapsing α × {-1} to a point (south pole)
    // - Collapsing α × {1} to a point (north pole)
    //
    // The cone Cα is the "half" of this construction:
    // - Taking α × [0, 1]
    // - Collapsing α × {1} to a point (apex)
    //
    // Key facts:
    // - Σ(Sⁿ) ≅ Sⁿ⁺¹ (suspension of n-sphere is (n+1)-sphere)
    // - πₙ(α) ≅ πₙ₊₁(Σα) for n ≥ 1 (Freudenthal suspension theorem)
    // - Cα is contractible for any α
    // - Σα ≅ Cα ∪_α Cα (join along the base)
    // ================================================================

    /// Initialize Topology.Suspension primitives
    ///
    /// Introduces suspension and cone constructions:
    /// - `Topology.Suspension` : Type u → Type u (the suspension Σα)
    /// - `Topology.Suspension.north` : Suspension α (north pole)
    /// - `Topology.Suspension.south` : Suspension α (south pole)
    /// - `Topology.Suspension.merid` : α → north = south (meridian paths)
    /// - `Topology.Suspension.topological_space` : TopologicalSpace (Suspension α)
    /// - `Topology.Cone` : Type u → Type u (the cone Cα)
    /// - `Topology.Cone.apex` : Cone α (apex/tip of cone)
    /// - `Topology.Cone.base_incl` : α → Cone α (inclusion of base)
    /// - `Topology.Cone.topological_space` : TopologicalSpace (Cone α)
    /// - `Topology.Cone.contractible` : Contractible (Cone α)
    /// - `Topology.Suspension.sphere_succ` : Suspension (Sphere n) ≃ Sphere (n+1)
    /// - `Topology.Suspension.map` : (α → β) → Suspension α → Suspension β
    /// - `Topology.Suspension.map_continuous` : Continuous f → Continuous (Suspension.map f)
    /// - `Topology.Suspension.freudenthal` : πₙ(α, x₀) → πₙ₊₁(Σα, north) (for stable range)
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_suspension_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_topology_suspension(&mut self) -> Result<(), EnvError> {
        if self.topology_suspension_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_topological_space()?;
        self.init_topology_higher_homotopy()?;
        self.init_topology_continuous()?;
        self.init_topology_contractible()?;
        self.init_topology_homeomorphism()?;
        self.init_eq()?;

        {
            use crate::env::generated_overlay::{
                load_generated_namespace_overlay, TOPOLOGY_SUSPENSION_NAMESPACE,
            };
            load_generated_namespace_overlay(self, TOPOLOGY_SUSPENSION_NAMESPACE)?;
        }

        self.topology_suspension_init = true;
        Ok(())
    }

    /// Check if Topology.Suspension has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_suspension_init == true`
    pub(crate) fn has_topology_suspension(&self) -> bool {
        self.topology_suspension_init
    }

    /// Initialize Topology.VectorBundle for vector bundle theory.
    ///
    /// A vector bundle is a fiber bundle where the fiber is a vector space
    /// and the local trivializations are linear isomorphisms on fibers.
    /// This is fundamental for differential geometry and algebraic topology.
    ///
    /// Constants added:
    /// - `Topology.VectorBundle`: The type of vector bundle structures
    /// - `Topology.VectorBundle.toFiberBundle`: Coercion to FiberBundle
    /// - `Topology.VectorBundle.linear_fiber`: Linear structure on fibers
    /// - `Topology.VectorBundle.local_trivialization`: Local trivialization data
    /// - `Topology.VectorBundle.trivialization_linear`: Trivializations are linear on fibers
    /// - `Topology.VectorBundle.zero_section`: The zero section
    /// - `Topology.VectorBundle.zero_section_continuous`: Zero section is continuous
    /// - `Topology.VectorBundle.add_fibers`: Fiberwise addition
    /// - `Topology.VectorBundle.scalar_mult`: Fiberwise scalar multiplication
    /// - `Topology.VectorBundle.tangent_bundle`: Tangent bundle example type
    /// - `Topology.VectorBundle.cotangent_bundle`: Cotangent bundle type
    /// - `Topology.VectorBundle.direct_sum`: Direct sum of vector bundles
    /// - `Topology.VectorBundle.tensor_product`: Tensor product of vector bundles
    /// - `Topology.VectorBundle.dual_bundle`: Dual vector bundle
    /// - `Topology.VectorBundle.pullback`: Pullback of vector bundle
    /// - `Topology.VectorBundle.section`: Type of sections of a vector bundle
    /// - `Topology.VectorBundle.section_add`: Pointwise addition of sections
    /// - `Topology.VectorBundle.section_smul`: Scalar multiplication of sections
    /// - `Topology.VectorBundle.rank`: Rank (dimension of fiber)
    /// - `Topology.VectorBundle.trivial`: Trivial vector bundle B × F
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_vector_bundle_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_topology_vector_bundle(&mut self) -> Result<(), EnvError> {
        if self.topology_vector_bundle_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_topology_fiber_bundle()?;
        self.init_topology_continuous()?;
        self.init_add_comm_group()?;
        self.init_semiring()?;
        self.init_nat()?;
        self.init_eq()?;
        self.init_topology_product()?;

        {
            use crate::env::generated_overlay::{
                load_generated_namespace_overlay, TOPOLOGY_VECTOR_BUNDLE_NAMESPACE,
            };
            load_generated_namespace_overlay(self, TOPOLOGY_VECTOR_BUNDLE_NAMESPACE)?;
        }

        self.topology_vector_bundle_init = true;
        Ok(())
    }

    /// Check if Topology.VectorBundle has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_vector_bundle_init == true`
    pub(crate) fn has_topology_vector_bundle(&self) -> bool {
        self.topology_vector_bundle_init
    }

    /// Initialize Topology.CoproductTopology for disjoint union topology.
    ///
    /// Constants added:
    /// - `Topology.CoproductTopology`: Topology on Sum X Y
    /// - `Topology.CoproductTopology.isOpen_iff`: Openness via components
    /// - `Topology.CoproductTopology.isClosed_iff`: Closedness via components
    /// - `Topology.CoproductTopology.inl_continuous`: Continuity of Sum.inl
    /// - `Topology.CoproductTopology.inr_continuous`: Continuity of Sum.inr
    /// - `Topology.CoproductTopology.elim_continuous`: Continuity of Sum.elim
    /// - `Topology.CoproductTopology.universal`: Universal property of coproducts
    /// - `Topology.CoproductTopology.swap_homeomorphism`: Swap homeomorphism X ⊕ Y ≃ Y ⊕ X
    /// - `Topology.CoproductTopology.assoc_homeomorphism`: Associativity homeomorphism
    /// - `Topology.CoproductTopology.connected_iff`: Connectedness via components
    /// - `Topology.CoproductTopology.compact_iff`: Compactness via components
    /// - `Topology.CoproductTopology.sum_map_continuous`: Coproduct map continuity
    /// - `Topology.CoproductTopology.cover_by_components`: Cover by inl/inr images
    /// - `Topology.CoproductTopology.disjoint_union_subspace`: Relationship to subspace topology
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_coproduct_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_topology_coproduct(&mut self) -> Result<(), EnvError> {
        if self.topology_coproduct_init {
            return Ok(());
        }

        // Dependencies
        self.init_sum()?;
        self.init_topological_space()?;
        self.init_topology_continuous()?;
        self.init_topology_homeomorphism()?;
        self.init_topology_connected()?;
        self.init_topology_compact()?;
        self.init_eq()?;

        // #1444 overlay: load Topology.CoproductTopology declarations from generated
        // namespace payload artifacts (`env/generated/topology_coproduct.rs`)
        // instead of handwritten add_decl blocks.
        {
            use crate::env::generated_overlay::{
                load_generated_namespace_overlay, TOPOLOGY_COPRODUCT_NAMESPACE,
            };
            load_generated_namespace_overlay(self, TOPOLOGY_COPRODUCT_NAMESPACE)?;
        }

        self.topology_coproduct_init = true;
        Ok(())
    }

    /// Check if Topology.CoproductTopology has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_coproduct_init == true`
    pub(crate) fn has_topology_coproduct(&self) -> bool {
        self.topology_coproduct_init
    }
}
