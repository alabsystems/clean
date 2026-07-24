// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Topology construction functions for Environment
//!
//! This module contains init_* and has_* functions for constructing
//! new topological spaces from existing ones:
//! - Quotient topologies
//! - Subspace topologies
//! - Product topologies

use crate::env::{EnvError, Environment};

impl Environment {
    /// Initialize Topology.Quotient - quotient topology theory
    ///
    /// The quotient topology is the finest topology on a quotient space such that the
    /// quotient map is continuous. For a surjective map `q : X → Y`, a subset `U ⊆ Y`
    /// is open in the quotient topology iff `q⁻¹(U)` is open in `X`.
    ///
    /// # Constants added
    ///
    /// ## Core Quotient Topology
    /// - `Topology.QuotientTopology` : {X Y : Type u} → [TopologicalSpace X] → (X → Y) → TopologicalSpace Y
    ///   - The quotient topology on Y induced by a surjection q : X → Y
    ///
    /// ## Openness Characterization
    /// - `Topology.QuotientTopology.isOpen_iff` : IsOpen U ↔ IsOpen (q ⁻¹' U)
    ///   - Characterization of open sets in quotient topology
    /// - `Topology.QuotientTopology.isClosed_iff` : IsClosed C ↔ IsClosed (q ⁻¹' C)
    ///   - Characterization of closed sets
    ///
    /// ## Quotient Map Properties
    /// - `Topology.IsQuotientMap` : {X Y : Type u} → [...] → (X → Y) → Prop
    ///   - Predicate: q is a quotient map (surjective and has quotient topology)
    /// - `Topology.IsQuotientMap.surjective` : IsQuotientMap q → Function.Surjective q
    ///   - Quotient maps are surjective
    /// - `Topology.IsQuotientMap.continuous` : IsQuotientMap q → Continuous q
    ///   - Quotient maps are continuous
    /// - `Topology.IsQuotientMap.isOpen_preimage` : IsQuotientMap q → (IsOpen U ↔ IsOpen (q ⁻¹' U))
    ///   - Open iff preimage is open
    ///
    /// ## Universal Property
    /// - `Topology.QuotientTopology.continuous_iff` : Continuous f ↔ Continuous (f ∘ q)
    ///   - f is continuous iff f ∘ q is continuous (universal property)
    /// - `Topology.QuotientTopology.lift` : (f : X → Z) → (∀ x y, q x = q y → f x = f y) → (Y → Z)
    ///   - Lifting function to quotient
    /// - `Topology.QuotientTopology.lift_continuous` : Continuous f → Continuous (lift q f h)
    ///   - Lifted function is continuous
    ///
    /// ## Quotient by Equivalence Relation
    /// - `Topology.QuotientTopology.fromSetoid` : {X : Type u} → [TopologicalSpace X] →
    ///   (s : Setoid X) → TopologicalSpace (Quotient s)
    ///   - Quotient topology from setoid
    /// - `Topology.QuotientTopology.mk_continuous` : Continuous (Quotient.mk s)
    ///   - The quotient projection is continuous
    ///
    /// ## Separation Properties
    /// - `Topology.QuotientTopology.t1_of_t1` : T1Space X → (∀ x, IsClosed (q ⁻¹' {q x})) → T1Space Y
    ///   - Quotient is T1 if fibers are closed
    /// - `Topology.QuotientTopology.hausdorff_iff` : Hausdorff Y ↔ IsClosed {(x, y) | q x = q y}
    ///   - Quotient is Hausdorff iff relation is closed in X × X
    ///
    /// ## Composition and Products
    /// - `Topology.IsQuotientMap.comp` : IsQuotientMap p → IsQuotientMap q → IsQuotientMap (p ∘ q)
    ///   - Composition of quotient maps
    /// - `Topology.IsQuotientMap.prod` : IsQuotientMap p → IsQuotientMap q → IsQuotientMap (p × q)
    ///   - Product of quotient maps (under suitable conditions)
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_quotient_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_topology_quotient(&mut self) -> Result<(), EnvError> {
        if self.topology_quotient_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_topology_continuous()?; // brings Continuous, IsOpen, IsClosed
        self.init_topological_space()?; // brings TopologicalSpace
        self.init_eq()?;
        self.init_prod()?; // for products
        self.init_classical()?; // for Setoid

        // #1444 overlay: load Topology.QuotientTopology declarations from generated
        // namespace payload artifacts (`env/generated/*`) instead of inline
        // handwritten add_decl calls in this init path.
        {
            use crate::env::generated_overlay::{
                load_generated_namespace_overlay, TOPOLOGY_QUOTIENT_NAMESPACE,
            };
            load_generated_namespace_overlay(self, TOPOLOGY_QUOTIENT_NAMESPACE)?;
        }

        self.topology_quotient_init = true;
        Ok(())
    }

    /// Check if Topology.Quotient has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_quotient_init == true`
    pub(crate) fn has_topology_quotient(&self) -> bool {
        self.topology_quotient_init
    }

    /// Initialize Topology.Subspace for subspace topology theory.
    ///
    /// The subspace topology on a subset A ⊆ X is the coarsest topology
    /// that makes the inclusion map i : A → X continuous.
    ///
    /// This adds:
    /// - `Topology.SubspaceTopology` : {X : Type u} → [TopologicalSpace X] → (X → Prop) → TopologicalSpace (Subtype A)
    /// - `Topology.SubspaceTopology.isOpen_iff` : IsOpen U ↔ ∃ V, IsOpen V ∧ U = (Subtype.val ⁻¹' V)
    /// - `Topology.SubspaceTopology.isClosed_iff` : IsClosed C ↔ ∃ K, IsClosed K ∧ C = (Subtype.val ⁻¹' K)
    /// - `Topology.inclusion_continuous` : Continuous (Subtype.val : {x // A x} → X)
    /// - `Topology.IsEmbedding` : predicate for topological embeddings
    /// - `Topology.IsEmbedding.continuous` : embeddings are continuous
    /// - `Topology.IsEmbedding.injective` : embeddings are injective
    /// - `Topology.inclusion_embedding` : inclusion is an embedding
    /// - `Topology.SubspaceTopology.induced_eq` : subspace topology = induced topology
    /// - `Topology.SubspaceTopology.restrict_continuous` : restriction of continuous map is continuous
    /// - `Topology.IsOpenEmbedding` : open embedding predicate
    /// - `Topology.IsClosedEmbedding` : closed embedding predicate
    /// - `Topology.open_embedding_of_open_inclusion` : inclusion of open set is open embedding
    /// - `Topology.closed_embedding_of_closed_inclusion` : inclusion of closed set is closed embedding
    /// - `Topology.SubspaceTopology.isCoarsest` : subspace topology is coarsest making inclusion continuous
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_subspace_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_topology_subspace(&mut self) -> Result<(), EnvError> {
        if self.topology_subspace_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_topology_continuous()?; // brings Continuous, IsOpen, IsClosed
        self.init_topological_space()?; // brings TopologicalSpace
        self.init_subtype()?; // Subtype used in SubspaceTopology result type
        self.init_eq()?;
        self.init_exists()?; // for existential quantifiers

        // #1444 overlay: load the migrated Subspace declaration cluster from
        // generated payload artifacts (`env/generated/topology_subspace.rs`)
        // instead of inline handwritten add_decl calls in this init path.
        {
            use crate::env::generated_overlay::{
                load_generated_namespace_overlay, TOPOLOGY_SUBSPACE_NAMESPACE,
            };
            load_generated_namespace_overlay(self, TOPOLOGY_SUBSPACE_NAMESPACE)?;
        }

        // #1444 overlay: load the migrated Embedding declaration cluster from
        // generated payload artifacts (`env/generated/topology_embedding.rs`).
        // Includes: IsEmbedding, IsEmbedding.continuous, Function.Injective,
        // IsEmbedding.injective, inclusion_embedding, IsOpenEmbedding,
        // IsClosedEmbedding, toIsEmbedding projections, and open/closed
        // inclusion embedding lemmas.
        {
            use crate::env::generated_overlay::{
                load_generated_namespace_overlay, TOPOLOGY_EMBEDDING_NAMESPACE,
            };
            load_generated_namespace_overlay(self, TOPOLOGY_EMBEDDING_NAMESPACE)?;
        }

        self.topology_subspace_init = true;
        Ok(())
    }

    /// Check if Topology.Subspace has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_subspace_init == true`
    pub(crate) fn has_topology_subspace(&self) -> bool {
        self.topology_subspace_init
    }

    /// Initialize Topology.Product for product topology theory.
    ///
    /// The product topology on X × Y is the coarsest topology making both
    /// projection maps π₁ : X × Y → X and π₂ : X × Y → Y continuous.
    /// Equivalently, it has basis consisting of products U × V where U is open
    /// in X and V is open in Y.
    ///
    /// This adds:
    /// - `Topology.ProductTopology` : {X Y : Type u} → [TopologicalSpace X] → [TopologicalSpace Y] → TopologicalSpace (X × Y)
    /// - `Topology.ProductTopology.isOpen_iff` : IsOpen W ↔ ∀ p ∈ W, ∃ U V, IsOpen U ∧ IsOpen V ∧ p ∈ U × V ∧ U × V ⊆ W
    /// - `Topology.ProductTopology.fst_continuous` : Continuous Prod.fst
    /// - `Topology.ProductTopology.snd_continuous` : Continuous Prod.snd
    /// - `Topology.ProductTopology.continuous_prod_mk` : f, g continuous → (x ↦ (f x, g x)) continuous
    /// - `Topology.ProductTopology.isOpen_prod` : IsOpen U → IsOpen V → IsOpen (U × V)
    /// - `Topology.ProductTopology.isClosed_prod` : IsClosed C → IsClosed D → IsClosed (C × D)
    /// - `Topology.ProductTopology.prod_continuous` : f, g continuous → f × g continuous
    /// - `Topology.ProductTopology.prod_homeomorphism` : homeomorphism (X × Y) ≃ₜ (Y × X)
    /// - `Topology.ProductTopology.prod_connected` : X connected → Y connected → X × Y connected
    /// - `Topology.ProductTopology.prod_compact` : X compact → Y compact → X × Y compact (Tychonoff for finite products)
    /// - `Topology.ProductTopology.prod_hausdorff` : X Hausdorff → Y Hausdorff → X × Y Hausdorff
    /// - `Topology.ProductTopology.induced_eq` : product topology = induced topology from projections
    /// - `Topology.ProductTopology.isCoarsest` : coarsest topology making projections continuous
    /// - `Topology.ProductTopology.prod_assoc` : homeomorphism (X × Y) × Z ≃ₜ X × (Y × Z)
    /// - `Topology.ProductTopology.diagonal_closed` : Hausdorff X → IsClosed (diagonal X)
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_product_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_topology_product(&mut self) -> Result<(), EnvError> {
        if self.topology_product_init {
            return Ok(());
        }
        // #1483: dynamic stack growth — product is a common ancestor in deep
        // unwrapped chains (vector_bundle, ktheory, characteristic, spin).
        // Also calls topology_product::payload() directly (not through
        // load_generated_namespace_overlay), so needs its own wrapping.
        crate::expr::stack_safe(|| {
            self.init_topology_continuous()?;
            self.init_topological_space()?;
            self.init_prod()?;
            self.init_eq()?;

            {
                use crate::env::generated::topology_product;
                use crate::env::generated_overlay::load_namespace_overlay;

                let has_homeomorphism = self.has_topology_homeomorphism();
                let payload: Vec<_> = topology_product::payload()
                    .into_iter()
                    .filter(|c| {
                        has_homeomorphism
                            || c.name
                                != crate::name::Name::from_string(
                                    "Topology.ProductTopology.prod_homeomorphism",
                                )
                    })
                    .collect();
                load_namespace_overlay(self, payload)?;
            }

            self.topology_product_init = true;
            Ok(())
        })
    }

    /// Check if Topology.Product has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_product_init == true`
    pub(crate) fn has_topology_product(&self) -> bool {
        self.topology_product_init
    }
}
