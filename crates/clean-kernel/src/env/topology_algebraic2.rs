// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Algebraic topology structures for Environment (continued)
//!
//! This module contains algebraic topology init_* and has_* functions:
//! - Spectral sequences
//! - Sheaves
//! - Schemes
//! - Cobordism
//! - Characteristic classes

use crate::env::{EnvError, Environment};

impl Environment {
    /// Initialize spectral sequence theory
    ///
    /// Spectral sequences are a fundamental computational tool in algebraic topology
    /// and homological algebra. They provide a systematic way to compute homology
    /// and cohomology groups through successive approximations.
    ///
    /// Key concepts:
    /// - E_r pages: successive approximations E_0, E_1, E_2, ...
    /// - Differentials d_r: E^{p,q}_r → E^{p+r, q-r+1}_r with d_r ∘ d_r = 0
    /// - Convergence: E_r converges to graded pieces of target groups
    ///
    /// Classical spectral sequences:
    /// - Serre spectral sequence: for fiber bundles F → E → B
    /// - Atiyah-Hirzebruch: computes generalized cohomology from ordinary
    /// - Adams spectral sequence: computes stable homotopy groups
    /// - Leray spectral sequence: for continuous maps
    /// - Grothendieck spectral sequence: composition of derived functors
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_spectral_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    #[cfg(test)]
    pub(crate) fn init_topology_spectral(&mut self) -> Result<(), EnvError> {
        if self.topology_spectral_init {
            return Ok(());
        }

        // Dependencies
        self.init_topological_space()?;
        self.init_nat()?;
        self.init_int()?;
        self.init_topology_filtration()?; // Filtrations generate spectral sequences
        self.init_topology_homology()?; // Spectral sequences compute homology
        self.init_topology_fiber_bundle()?; // Serre spectral sequence
        self.init_eq()?;
        self.init_add_comm_group()?;
        self.init_ring()?; // from_filtered_complex needs Ring

        // #1444 overlay: load Topology.Spectral declarations from generated
        // namespace payload artifacts (`env/generated/topology_spectral.rs`)
        // instead of 40 inline handwritten add_decl calls with manual
        // de Bruijn index arithmetic.
        {
            use crate::env::generated_overlay::{
                load_generated_namespace_overlay, TOPOLOGY_SPECTRAL_NAMESPACE,
            };
            load_generated_namespace_overlay(self, TOPOLOGY_SPECTRAL_NAMESPACE)?;
        }

        self.topology_spectral_init = true;
        Ok(())
    }
    /// Check if Topology.Spectral has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_spectral_init == true`
    #[cfg(test)]
    pub(crate) fn has_topology_spectral(&self) -> bool {
        self.topology_spectral_init
    }

    /// Initialize sheaf theory
    ///
    /// Sheaves are a fundamental tool in algebraic geometry and algebraic topology,
    /// providing a way to track locally defined data and its compatibility conditions.
    ///
    /// Key concepts:
    /// - Presheaves: contravariant functors from open sets to sets/abelian groups
    /// - Sheaves: presheaves satisfying the gluing axiom
    /// - Stalks: limits of sections over neighborhoods of a point
    /// - Sheafification: universal construction from presheaf to sheaf
    /// - Sheaf cohomology: derived functors of global sections
    ///
    /// Important sheaf types:
    /// - Structure sheaf O_X for ringed spaces
    /// - Constant sheaves for local systems
    /// - Skyscraper sheaves for point data
    /// - Locally free sheaves (vector bundles)
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_sheaf_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_topology_sheaf(&mut self) -> Result<(), EnvError> {
        if self.topology_sheaf_init {
            return Ok(());
        }

        // Dependencies
        self.init_topological_space()?;
        self.init_nat()?;
        self.init_int()?;
        self.init_eq()?;
        self.init_add_comm_group()?;
        self.init_ring()?;

        // #1444 overlay: load Topology.Sheaf declarations from generated
        // namespace payload artifacts (`env/generated/topology_sheaf.rs`)
        // instead of 40 handwritten add_decl blocks with manual bvar arithmetic.
        {
            use crate::env::generated_overlay::{
                load_generated_namespace_overlay, TOPOLOGY_SHEAF_NAMESPACE,
            };
            load_generated_namespace_overlay(self, TOPOLOGY_SHEAF_NAMESPACE)?;
        }

        self.topology_sheaf_init = true;
        Ok(())
    }

    /// Check if Topology.Sheaf has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_sheaf_init == true`
    #[cfg(test)]
    pub(crate) fn has_topology_sheaf(&self) -> bool {
        self.topology_sheaf_init
    }

    /// Initialize Topology.Scheme for scheme theory
    ///
    /// Adds abstract axioms for schemes, morphisms, immersions, and standard
    /// finiteness and separation properties used in algebraic geometry.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_scheme_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_topology_scheme(&mut self) -> Result<(), EnvError> {
        if self.topology_scheme_init {
            return Ok(());
        }

        // Dependencies
        self.init_topological_space()?;
        self.init_nat()?;
        self.init_int()?;
        self.init_eq()?;
        self.init_ring()?;
        self.init_comm_ring()?;
        self.init_topology_sheaf()?;

        // #1444 overlay: load Topology.Scheme declarations from generated
        // namespace payload artifacts (`env/generated/topology_scheme.rs`)
        // instead of 35 handwritten add_decl blocks with manual bvar arithmetic.
        {
            use crate::env::generated_overlay::{
                load_generated_namespace_overlay, TOPOLOGY_SCHEME_NAMESPACE,
            };
            load_generated_namespace_overlay(self, TOPOLOGY_SCHEME_NAMESPACE)?;
        }

        self.topology_scheme_init = true;
        Ok(())
    }

    /// Check if Topology.Scheme has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_scheme_init == true`
    #[cfg(test)]
    pub(crate) fn has_topology_scheme(&self) -> bool {
        self.topology_scheme_init
    }

    /// Initialize Topology.Cobordism module for cobordism theory
    ///
    /// Cobordism theory studies equivalence relations between manifolds:
    /// two manifolds M and N are cobordant if there exists a manifold W
    /// whose boundary is the disjoint union of M and N.
    ///
    /// This module provides:
    /// - Cobordism relation and cobordism classes
    /// - Oriented, unoriented, and framed cobordism
    /// - Thom spaces and the Pontryagin-Thom construction
    /// - Cobordism groups and ring structure
    /// - h-cobordism theorem and surgery theory basics
    /// - Connections to stable homotopy and generalized homology
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_cobordism_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    #[cfg(test)]
    pub(crate) fn init_topology_cobordism(&mut self) -> Result<(), EnvError> {
        if self.topology_cobordism_init {
            return Ok(());
        }

        // Dependencies
        self.init_topological_space()?;
        self.init_nat()?;
        self.init_int()?;
        self.init_eq()?;
        self.init_topology_homology()?;
        self.init_add_comm_group()?;
        self.init_ring()?;

        {
            use crate::env::generated_overlay::{
                load_generated_namespace_overlay, TOPOLOGY_COBORDISM_NAMESPACE,
            };
            load_generated_namespace_overlay(self, TOPOLOGY_COBORDISM_NAMESPACE)?;
        }

        self.topology_cobordism_init = true;
        Ok(())
    }

    /// Check if Topology.Cobordism has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_cobordism_init == true`
    #[cfg(test)]
    pub(crate) fn has_topology_cobordism(&self) -> bool {
        self.topology_cobordism_init
    }

    /// Initialize Topology.Characteristic module for characteristic classes
    ///
    /// This provides the theory of characteristic classes for vector bundles:
    /// - Stiefel-Whitney classes for real vector bundles
    /// - Chern classes for complex vector bundles
    /// - Pontryagin classes for real bundles via complexification
    /// - Euler class
    /// - Total classes and their properties
    /// - Whitney sum formula
    /// - Splitting principle and classifying spaces
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_characteristic_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    #[cfg(test)]
    pub(crate) fn init_topology_characteristic(&mut self) -> Result<(), EnvError> {
        if self.topology_characteristic_init {
            return Ok(());
        }

        // Dependencies
        self.init_topological_space()?;
        self.init_nat()?;
        self.init_int()?;
        self.init_eq()?;
        self.init_topology_vector_bundle()?;
        self.init_topology_homology()?;
        self.init_add_comm_group()?;
        self.init_ring()?;

        {
            use crate::env::generated_overlay::{
                load_generated_namespace_overlay, TOPOLOGY_CHARACTERISTIC_NAMESPACE,
            };
            load_generated_namespace_overlay(self, TOPOLOGY_CHARACTERISTIC_NAMESPACE)?;
        }

        self.topology_characteristic_init = true;
        Ok(())
    }

    /// Check if Topology.Characteristic has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_characteristic_init == true`
    #[cfg(test)]
    pub(crate) fn has_topology_characteristic(&self) -> bool {
        self.topology_characteristic_init
    }
}
