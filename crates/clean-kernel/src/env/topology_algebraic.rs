// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Algebraic topology structures for Environment
//!
//! This module contains algebraic topology-related init_* and has_* functions
//! for the Environment type. It implements:
//! - CW complexes
//! - Simplicial complexes
//! - Homology
//! - de Rham cohomology
//! - Morse theory
//! - K-theory
//! - Filtrations and spectral sequences
//! - Sheaves
//! - Schemes
//! - Cobordism
//! - Characteristic classes

use crate::env::{EnvError, Environment};

impl Environment {
    /// Initialize Topology.CW for CW-complex theory.
    ///
    /// Constants added:
    /// - `Topology.CWComplex`: CW structure on a space
    /// - `Topology.CWComplex.skeleton`: n-skeleton
    /// - `Topology.CWComplex.cell`: n-cells
    /// - `Topology.CWComplex.attach_cell`: attaching cells
    /// - `Topology.CWComplex.characteristic_map`: characteristic map for cells
    /// - `Topology.CWComplex.closure_finite`: closure-finite condition
    /// - `Topology.CWComplex.weak_topology`: weak topology axiom
    /// - `Topology.CWComplex.homotopy_extension`: homotopy extension property
    /// - `Topology.CWComplex.whitehead`: Whitehead theorem statement
    /// - `Topology.CWComplex.cellular_approximation`: cellular approximation
    /// - `Topology.CWComplex.subcomplex`: subcomplex definition
    /// - `Topology.CWComplex.cw_on_subset`: CW structure on subsets
    /// - `Topology.CWComplex.connectivity`: connectivity of skeleta
    /// - `Topology.CWComplex.cellular_homology`: cellular chain complex
    /// - `Topology.CWComplex.attaching_map_continuous`: attaching maps are continuous
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_cw_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_topology_cw(&mut self) -> Result<(), EnvError> {
        if self.topology_cw_init {
            return Ok(());
        }

        // Dependencies
        self.init_topological_space()?;
        self.init_nat()?;
        self.init_topology_continuous()?;
        self.init_topology_connected()?;
        self.init_topology_contractible()?;
        self.init_eq()?;

        // #1444 overlay: load Topology.CWComplex declarations from generated
        // namespace payload artifacts (`env/generated/topology_cw.rs`)
        // instead of handwritten add_decl blocks.
        {
            use crate::env::generated_overlay::{
                load_generated_namespace_overlay, TOPOLOGY_CW_NAMESPACE,
            };
            load_generated_namespace_overlay(self, TOPOLOGY_CW_NAMESPACE)?;
        }

        self.topology_cw_init = true;
        Ok(())
    }

    /// Check if Topology.CW has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_cw_init == true`
    pub(crate) fn has_topology_cw(&self) -> bool {
        self.topology_cw_init
    }

    /// Initialize Topology.SimplicialComplex for simplicial complex theory.
    ///
    /// Constants added:
    /// - `Topology.SimplicialComplex`: abstract simplicial complex
    /// - `Topology.SimplicialComplex.simplex`: simplices in the complex
    /// - `Topology.SimplicialComplex.face`: face operators
    /// - `Topology.SimplicialComplex.degeneracy`: degeneracy operators
    /// - `Topology.SimplicialComplex.geometric_realization`: realization object
    /// - `Topology.SimplicialComplex.realization_topology`: topology on realization
    /// - `Topology.SimplicialComplex.realization_continuous`: universal map continuity
    /// - `Topology.SimplicialComplex.barycentric_subdivision`: barycentric subdivision
    /// - `Topology.SimplicialComplex.chain_complex`: associated chain complex
    /// - `Topology.SimplicialComplex.homology`: simplicial homology groups
    /// - `Topology.SimplicialComplex.cohomology`: simplicial cohomology
    /// - `Topology.SimplicialComplex.link`: link of a simplex
    /// - `Topology.SimplicialComplex.star`: star of a simplex
    /// - `Topology.SimplicialComplex.subcomplex`: subcomplex formation
    /// - `Topology.SimplicialComplex.euler_characteristic`: Euler characteristic
    /// - `Topology.SimplicialComplex.realization_to_cw`: realization relates to CW complexes
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_simplicial_complex_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_topology_simplicial_complex(&mut self) -> Result<(), EnvError> {
        if self.topology_simplicial_complex_init {
            return Ok(());
        }

        // Dependencies
        self.init_topological_space()?;
        self.init_nat()?;
        self.init_topology_continuous()?;
        self.init_topology_homeomorphism()?;
        self.init_topology_cw()?;
        self.init_eq()?;

        // #1444 overlay: load Topology.SimplicialComplex declarations from generated
        // namespace payload artifacts (`env/generated/topology_simplicial.rs`)
        // instead of handwritten add_decl blocks.
        {
            use crate::env::generated_overlay::{
                load_generated_namespace_overlay, TOPOLOGY_SIMPLICIAL_NAMESPACE,
            };
            load_generated_namespace_overlay(self, TOPOLOGY_SIMPLICIAL_NAMESPACE)?;
        }

        self.topology_simplicial_complex_init = true;
        Ok(())
    }

    /// Check if Topology.SimplicialComplex has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_simplicial_complex_init == true`
    pub(crate) fn has_topology_simplicial_complex(&self) -> bool {
        self.topology_simplicial_complex_init
    }

    /// Initialize Topology.Homology for singular homology theory.
    ///
    /// Provides foundational constants for singular homology and cohomology:
    ///
    /// Core structures:
    /// - `Topology.Homology.SingularChain : (n : Nat) → {X : Type u} → [TopologicalSpace X] → Type u` - n-chains
    /// - `Topology.Homology.ChainComplex : {R : Type u} → [Ring R] → Type (u+1)` - chain complex
    /// - `Topology.Homology.boundary : SingularChain (n+1) X → SingularChain n X` - boundary operator ∂
    /// - `Topology.Homology.boundary_sq_zero : ∂ ∘ ∂ = 0` - fundamental property
    ///
    /// Homology groups:
    /// - `Topology.Homology.H : (n : Nat) → {X : Type u} → [TopologicalSpace X] → Type u` - Hₙ(X)
    /// - `Topology.Homology.induced : {X Y : Type u} → (f : X → Y) → Continuous f → H n X → H n Y` - induced maps
    /// - `Topology.Homology.functoriality : H n (g ∘ f) = H n g ∘ H n f` - functoriality
    ///
    /// Cohomology:
    /// - `Topology.Homology.Cohomology : (n : Nat) → {X : Type u} → [TopologicalSpace X] → Type u` - Hⁿ(X)
    /// - `Topology.Homology.cup_product : Hⁿ(X) → Hᵐ(X) → Hⁿ⁺ᵐ(X)` - cup product
    ///
    /// Exact sequences and tools:
    /// - `Topology.Homology.exact_sequence` - exactness of homology sequence
    /// - `Topology.Homology.mayer_vietoris` - Mayer-Vietoris sequence
    /// - `Topology.Homology.long_exact_pair` - long exact sequence of a pair
    ///
    /// Fundamental theorems:
    /// - `Topology.Homology.homotopy_invariance` - homotopic maps induce same homology maps
    /// - `Topology.Homology.excision` - excision theorem
    /// - `Topology.Homology.dimension_axiom` - Hₙ(point) = 0 for n > 0
    /// - `Topology.Homology.hurewicz` - Hurewicz homomorphism πₙ → Hₙ
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_homology_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_topology_homology(&mut self) -> Result<(), EnvError> {
        if self.topology_homology_init {
            return Ok(());
        }
        // #1483: dynamic stack growth — homology is a common ancestor in deep
        // unwrapped chains (morse, derham, filtration, spectral, characteristic).
        crate::expr::stack_safe(|| {
            self.init_topological_space()?;
            self.init_nat()?;
            self.init_int()?;
            self.init_topology_continuous()?;
            self.init_topology_path_connected()?;
            self.init_topology_higher_homotopy()?;
            self.init_add_comm_group()?;
            self.init_ring()?;
            self.init_eq()?;

            {
                use crate::env::generated_overlay::{
                    load_generated_namespace_overlay, TOPOLOGY_HOMOLOGY_NAMESPACE,
                };
                load_generated_namespace_overlay(self, TOPOLOGY_HOMOLOGY_NAMESPACE)?;
            }

            self.topology_homology_init = true;
            Ok(())
        })
    }

    /// Check if Topology.Homology has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_homology_init == true`
    pub(crate) fn has_topology_homology(&self) -> bool {
        self.topology_homology_init
    }

    /// Initialize Topology.DeRham - de Rham cohomology theory
    ///
    /// De Rham cohomology is a cohomology theory based on differential forms on smooth manifolds.
    /// The de Rham theorem establishes an isomorphism between de Rham cohomology and singular
    /// cohomology with real coefficients.
    ///
    /// This module provides:
    /// - Differential forms (Ω^k) on smooth manifolds
    /// - Exterior derivative (d : Ω^k → Ω^k+1)
    /// - Wedge product (∧) of differential forms
    /// - De Rham cohomology groups H^k_dR(M)
    /// - De Rham theorem: H^k_dR(M) ≅ H^k(M; ℝ)
    /// - Poincaré lemma for contractible spaces
    /// - Integration of forms over chains
    /// - Stokes' theorem: ∫_∂M ω = ∫_M dω
    /// - Hodge star operator and Hodge decomposition
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_derham_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_topology_derham(&mut self) -> Result<(), EnvError> {
        if self.topology_derham_init {
            return Ok(());
        }

        // Dependencies
        self.init_topological_space()?;
        self.init_nat()?;
        self.init_rat()?; // de Rham cohomology uses real coefficients (Rat as proxy for Real)
        self.init_topology_continuous()?;
        self.init_topology_homology()?; // for de Rham theorem connection
        self.init_topology_contractible()?; // for Poincaré lemma
        self.init_eq()?;
        self.init_add_comm_group()?; // differential forms are abelian groups (proxy for vector spaces)

        // #1444 overlay: load Topology.DeRham declarations from generated
        // namespace payload artifacts (`env/generated/topology_derham.rs`)
        // instead of handwritten add_decl blocks.
        {
            use crate::env::generated_overlay::{
                load_generated_namespace_overlay, TOPOLOGY_DERHAM_NAMESPACE,
            };
            load_generated_namespace_overlay(self, TOPOLOGY_DERHAM_NAMESPACE)?;
        }

        self.topology_derham_init = true;
        Ok(())
    }

    /// Check if Topology.DeRham has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_derham_init == true`
    pub(crate) fn has_topology_derham(&self) -> bool {
        self.topology_derham_init
    }

    /// Initialize Topology.Morse module for Morse theory
    ///
    /// Provides axioms for Morse functions, critical points, gradient flow, Morse complexes,
    /// and Morse homology relating to singular homology.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_morse_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_topology_morse(&mut self) -> Result<(), EnvError> {
        if self.topology_morse_init {
            return Ok(());
        }

        // Dependencies
        self.init_topological_space()?;
        self.init_nat()?;
        self.init_rat()?;
        self.init_eq()?;
        self.init_topology_derham()?; // Smooth manifolds and differential forms
        self.init_topology_homology()?; // For Morse homology comparison
        self.init_topology_filtration()?; // Sublevel set filtrations
        self.init_add_comm_group()?;

        // #1444 overlay: load Topology.Morse declarations from generated
        // namespace payload artifacts (`env/generated/topology_morse.rs`)
        // instead of handwritten add_decl blocks.
        {
            use crate::env::generated_overlay::{
                load_generated_namespace_overlay, TOPOLOGY_MORSE_NAMESPACE,
            };
            load_generated_namespace_overlay(self, TOPOLOGY_MORSE_NAMESPACE)?;
        }

        self.topology_morse_init = true;
        Ok(())
    }

    /// Check if Topology.Morse has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_morse_init == true`
    pub(crate) fn has_topology_morse(&self) -> bool {
        self.topology_morse_init
    }

    /// Initialize Topology.KTheory constants for topological K-theory
    ///
    /// K-theory is a generalized cohomology theory that classifies vector bundles
    /// over topological spaces. This module adds constants for:
    /// - K⁰(X): Grothendieck group of vector bundles
    /// - K⁻¹(X): Odd K-group via suspension
    /// - Bott periodicity: K(X) ≅ K(Σ²X)
    /// - Adams operations ψᵏ
    /// - Ring structure via tensor product
    /// - Chern character to rational cohomology
    /// - Reduced K-theory
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_ktheory_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_topology_ktheory(&mut self) -> Result<(), EnvError> {
        if self.topology_ktheory_init {
            return Ok(());
        }

        // Dependencies
        self.init_topological_space()?;
        self.init_nat()?;
        self.init_int()?;
        self.init_rat()?;
        self.init_topology_continuous()?;
        self.init_topology_vector_bundle()?; // K-theory classifies vector bundles
        self.init_topology_suspension()?; // For K⁻¹ and Bott periodicity
        self.init_topology_compact()?; // K-theory often defined on compact spaces
        self.init_eq()?;
        self.init_add_comm_group()?;
        self.init_ring()?;

        // #1444 overlay: load Topology.KTheory declarations from generated
        // namespace payload artifacts (`env/generated/topology_ktheory.rs`)
        // instead of handwritten add_decl blocks.
        {
            use crate::env::generated_overlay::{
                load_generated_namespace_overlay, TOPOLOGY_KTHEORY_NAMESPACE,
            };
            load_generated_namespace_overlay(self, TOPOLOGY_KTHEORY_NAMESPACE)?;
        }

        self.topology_ktheory_init = true;
        Ok(())
    }

    /// Check if Topology.KTheory has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_ktheory_init == true`
    pub(crate) fn has_topology_ktheory(&self) -> bool {
        self.topology_ktheory_init
    }

    /// Initialize Topology.Filtration for filtered objects and graded pieces
    ///
    /// Provides abstract filtrations, associated graded objects, and filtered complexes
    /// that feed spectral sequences and Morse theory constructions.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_filtration_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_topology_filtration(&mut self) -> Result<(), EnvError> {
        if self.topology_filtration_init {
            return Ok(());
        }

        // Dependencies
        self.init_topological_space()?;
        self.init_nat()?;
        self.init_int()?;
        self.init_eq()?;
        self.init_ring()?;
        self.init_add_comm_group()?;
        self.init_topology_homology()?; // For filtered chain complexes

        // #1444 overlay: load Topology.Filtration declarations from generated
        // namespace payload artifacts (`env/generated/topology_filtration.rs`)
        // instead of handwritten add_decl blocks.
        {
            use crate::env::generated_overlay::{
                load_generated_namespace_overlay, TOPOLOGY_FILTRATION_NAMESPACE,
            };
            load_generated_namespace_overlay(self, TOPOLOGY_FILTRATION_NAMESPACE)?;
        }

        self.topology_filtration_init = true;
        Ok(())
    }

    /// Check if Topology.Filtration has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_filtration_init == true`
    pub(crate) fn has_topology_filtration(&self) -> bool {
        self.topology_filtration_init
    }
}
