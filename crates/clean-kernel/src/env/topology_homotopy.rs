// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Homotopy theory initialization functions for Environment
//!
//! This module contains homotopy-related init_* and has_* functions
//! for the Environment type. It implements:
//! - Path-connected spaces
//! - Simply connected spaces
//! - Contractible spaces
//! - Covering spaces
//! - Fundamental groups
//! - Homotopy equivalence
//! - Retracts

use crate::env::{EnvError, Environment};

impl Environment {
    /// Initialize path-connected topological spaces.
    ///
    /// A topological space is path-connected if any two points can be
    /// connected by a continuous path.
    ///
    /// This adds:
    /// - `Topology.Path` : {α : Type u} → [TopologicalSpace α] → α → α → Type u
    ///   - A path from x to y in α
    /// - `Topology.Path.continuous` : Path x y → Topology.Continuous (path function)
    /// - `Topology.Path.source` : Path x y → (path 0 = x)
    /// - `Topology.Path.target` : Path x y → (path 1 = y)
    /// - `Topology.Path.refl` : {α : Type u} → [TopologicalSpace α] → (x : α) → Path x x
    /// - `Topology.Path.symm` : {α : Type u} → [TopologicalSpace α] → Path x y → Path y x
    /// - `Topology.Path.trans` : Path x y → Path y z → Path x z
    /// - `Topology.PathConnected` : {α : Type u} → [TopologicalSpace α] → Prop
    /// - `Topology.path_connected_def` : PathConnected ↔ ∀ x y, ∃ (p : Path x y), True
    /// - `Topology.path_connected_of_connected` : Connected → PathConnected (requires convexity-like assumptions, axiom)
    /// - `Topology.continuous_image_path_connected` : Continuous f → PathConnected α → PathConnected β
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_path_connected_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_topology_path_connected(&mut self) -> Result<(), EnvError> {
        if self.topology_path_connected_init {
            return Ok(());
        }
        // #1483: dynamic stack growth for init chain + payload construction
        crate::expr::stack_safe(|| {
            self.init_topology_continuous()?;
            self.init_topology_connected()?;
            self.init_eq()?;
            self.init_iff()?;
            self.init_exists()?;

            {
                use crate::env::generated_overlay::{
                    load_generated_namespace_overlay, TOPOLOGY_PATH_CONNECTED_NAMESPACE,
                };
                load_generated_namespace_overlay(self, TOPOLOGY_PATH_CONNECTED_NAMESPACE)?;
            }

            self.topology_path_connected_init = true;
            Ok(())
        })
    }

    /// Check if Topology.PathConnected has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_path_connected_init == true`
    #[cfg(test)]
    pub(crate) fn has_topology_path_connected(&self) -> bool {
        self.topology_path_connected_init
    }

    /// Initialize Topology.SimplyConnected for simply connected topological spaces
    ///
    /// A simply connected space is a path-connected space in which every loop
    /// is null-homotopic (contractible to a point). This is equivalent to having
    /// a trivial fundamental group.
    ///
    /// # Constants added
    /// - `Topology.Loop` : {α : Type u} → [TopologicalSpace α] → α → Type u
    /// - `Topology.Loop.toPath` : Loop x → Path x x
    /// - `Topology.Loop.refl` : (x : α) → Loop x
    /// - `Topology.Loop.symm` : Loop x → Loop x
    /// - `Topology.Loop.trans` : Loop x → Loop x → Loop x
    /// - `Topology.Homotopy` : {α : Type u} → [TopologicalSpace α] → {x y : α} → Path x y → Path x y → Type u
    /// - `Topology.Homotopy.refl` : (p : Path x y) → Homotopy p p
    /// - `Topology.Homotopy.symm` : Homotopy p q → Homotopy q p
    /// - `Topology.Homotopy.trans` : Homotopy p q → Homotopy q r → Homotopy p r
    /// - `Topology.LoopHomotopy` : {α : Type u} → [TopologicalSpace α] → {x : α} → Loop x → Loop x → Type u
    /// - `Topology.NullHomotopic` : {α : Type u} → [TopologicalSpace α] → {x : α} → Loop x → Prop
    /// - `Topology.null_homotopic_def` : Iff (NullHomotopic γ) (∃ h : LoopHomotopy γ (Loop.refl x), True)
    /// - `Topology.SimplyConnected` : {α : Type u} → [TopologicalSpace α] → Prop
    /// - `Topology.simply_connected_def` : Iff SimplyConnected (PathConnected ∧ ∀ x (γ : Loop x), NullHomotopic γ)
    /// - `Topology.simply_connected_implies_path_connected` : SimplyConnected → PathConnected
    /// - `Topology.continuous_image_simply_connected` : Continuous f → SimplyConnected α → SimplyConnected β
    ///   (when f induces isomorphism on fundamental groups - simplified axiom)
    /// - `Topology.contractible_simply_connected` : Contractible α → SimplyConnected
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_simply_connected_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_topology_simply_connected(&mut self) -> Result<(), EnvError> {
        if self.topology_simply_connected_init {
            return Ok(());
        }
        // #1483: dynamic stack growth for init chain + payload construction
        crate::expr::stack_safe(|| {
            self.init_topology_path_connected()?;
            self.init_and()?;
            self.init_iff()?;
            self.init_exists()?;

            {
                use crate::env::generated_overlay::{
                    load_generated_namespace_overlay, TOPOLOGY_SIMPLY_CONNECTED_NAMESPACE,
                };
                load_generated_namespace_overlay(self, TOPOLOGY_SIMPLY_CONNECTED_NAMESPACE)?;
            }

            self.topology_simply_connected_init = true;
            Ok(())
        })
    }

    /// Check if Topology.SimplyConnected has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_simply_connected_init == true`
    #[cfg(test)]
    pub(crate) fn has_topology_simply_connected(&self) -> bool {
        self.topology_simply_connected_init
    }

    /// Initialize Topology.Contractible for contractible topological spaces.
    ///
    /// A contractible space is one that is homotopy equivalent to a point.
    /// Equivalently, the identity map is homotopic to a constant map.
    ///
    /// Prerequisites: SimplyConnected (which includes PathConnected, Continuous, etc.)
    ///
    /// New constants added:
    /// - `Topology.Contraction` : {α : Type u} → [TopologicalSpace α] → α → Type u
    ///     A contraction of the space to a given point
    /// - `Topology.Contraction.homotopy` : {α : Type u} → [TopologicalSpace α] → {x₀ : α} →
    ///     Contraction x₀ → (UnitInterval → α → α)
    ///     The underlying homotopy from identity to the constant map
    /// - `Topology.Contraction.at_zero` : {α : Type u} → [TopologicalSpace α] → {x₀ : α} →
    ///     (c : Contraction x₀) → ∀ x, Eq (Contraction.homotopy c 0 x) x
    ///     At time 0, the homotopy is the identity
    /// - `Topology.Contraction.at_one` : {α : Type u} → [TopologicalSpace α] → {x₀ : α} →
    ///     (c : Contraction x₀) → ∀ x, Eq (Contraction.homotopy c 1 x) x₀
    ///     At time 1, the homotopy is the constant map to x₀
    /// - `Topology.Contraction.continuous` : {α : Type u} → [TopologicalSpace α] → {x₀ : α} →
    ///     (c : Contraction x₀) → Continuous (fun t x => Contraction.homotopy c t x)
    ///     The homotopy is continuous
    /// - `Topology.Contractible` : {α : Type u} → [TopologicalSpace α] → Prop
    ///     Predicate for contractible spaces (space admits a contraction)
    /// - `Topology.contractible_def` : Iff Contractible (∃ x₀ : α, Nonempty (Contraction x₀))
    /// - `Topology.contractible_implies_simply_connected` : Contractible → SimplyConnected
    /// - `Topology.contractible_implies_path_connected` : Contractible → PathConnected
    /// - `Topology.contractible_implies_connected` : Contractible → Connected
    /// - `Topology.contractible_point` : (x : α) → Contractible α → Contraction x
    ///     Any point can serve as the contraction point
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_contractible_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    #[cfg(test)]
    pub(crate) fn init_topology_contractible(&mut self) -> Result<(), EnvError> {
        if self.topology_contractible_init {
            return Ok(());
        }
        // #1483: dynamic stack growth for init chain + payload construction
        crate::expr::stack_safe(|| {
            self.init_topology_simply_connected()?;
            self.init_exists()?;
            self.init_classical()?;

            {
                use crate::env::generated_overlay::{
                    load_generated_namespace_overlay, TOPOLOGY_CONTRACTIBLE_NAMESPACE,
                };
                load_generated_namespace_overlay(self, TOPOLOGY_CONTRACTIBLE_NAMESPACE)?;
            }

            self.topology_contractible_init = true;
            Ok(())
        })
    }

    /// Check if Topology.Contractible has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_contractible_init == true`
    pub(crate) fn has_topology_contractible(&self) -> bool {
        self.topology_contractible_init
    }

    #[cfg(test)]
    pub(crate) fn init_topology_covering_space(&mut self) -> Result<(), EnvError> {
        if self.topology_covering_space_init {
            return Ok(());
        }
        // #1483: dynamic stack growth for init chain + payload construction
        crate::expr::stack_safe(|| {
            self.init_topology_path_connected()?;
            self.init_topology_homeomorphism()?;
            self.init_exists()?;
            self.init_and()?;
            self.init_iff()?;

            {
                use crate::env::generated_overlay::{
                    load_generated_namespace_overlay, TOPOLOGY_COVERING_SPACE_NAMESPACE,
                };
                load_generated_namespace_overlay(self, TOPOLOGY_COVERING_SPACE_NAMESPACE)?;
            }

            self.topology_covering_space_init = true;
            Ok(())
        })
    }

    /// Check if Topology.CoveringSpace has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_covering_space_init == true`
    #[cfg(test)]
    pub(crate) fn has_topology_covering_space(&self) -> bool {
        self.topology_covering_space_init
    }
}
