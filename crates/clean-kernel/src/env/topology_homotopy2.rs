// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Homotopy theory structures for Environment (continued)
//!
//! This module contains homotopy theory init_* and has_* functions:
//! - Fundamental groups
//! - Homotopy equivalence
//! - Retracts

use crate::env::{EnvError, Environment};

impl Environment {
    /// Initialize Topology.FundamentalGroup for the fundamental group structure
    ///
    /// The fundamental group π₁(X, x₀) is the group of homotopy classes of loops
    /// based at a point x₀. It captures the essential "shape" of holes in a space.
    ///
    /// # Constants added
    /// - `Topology.FundamentalGroup` : {α : Type u} → [TopologicalSpace α] → α → Type u
    ///   The fundamental group π₁(α, x₀)
    /// - `Topology.FundamentalGroup.class` : {α : Type u} → [TopologicalSpace α] → {x₀ : α} → Loop x₀ → FundamentalGroup α x₀
    ///   The equivalence class of a loop
    /// - `Topology.FundamentalGroup.class_eq` : LoopHomotopy γ₁ γ₂ → Eq (class γ₁) (class γ₂)
    ///   Homotopic loops have the same class
    /// - `Topology.FundamentalGroup.mul` : {α : Type u} → [TopologicalSpace α] → {x₀ : α} →
    ///     FundamentalGroup α x₀ → FundamentalGroup α x₀ → FundamentalGroup α x₀
    ///   Group multiplication (composition of loop classes)
    /// - `Topology.FundamentalGroup.one` : {α : Type u} → [TopologicalSpace α] → {x₀ : α} → FundamentalGroup α x₀
    ///   The identity element (class of the constant loop)
    /// - `Topology.FundamentalGroup.inv` : {α : Type u} → [TopologicalSpace α] → {x₀ : α} →
    ///     FundamentalGroup α x₀ → FundamentalGroup α x₀
    ///   The inverse (class of the reversed loop)
    /// - `Topology.FundamentalGroup.mul_assoc` : ∀ a b c, Eq (mul (mul a b) c) (mul a (mul b c))
    /// - `Topology.FundamentalGroup.mul_one` : ∀ a, Eq (mul a one) a
    /// - `Topology.FundamentalGroup.one_mul` : ∀ a, Eq (mul one a) a
    /// - `Topology.FundamentalGroup.mul_inv` : ∀ a, Eq (mul a (inv a)) one
    /// - `Topology.FundamentalGroup.inv_mul` : ∀ a, Eq (mul (inv a) a) one
    /// - `Topology.FundamentalGroup.IsTrivial` : {α : Type u} → [TopologicalSpace α] → {x₀ : α} → Prop
    ///   Predicate that the fundamental group is trivial (has only one element)
    /// - `Topology.FundamentalGroup.trivial_def` : Iff IsTrivial (∀ g, Eq g one)
    /// - `Topology.simply_connected_iff_trivial_pi1` : {α : Type u} → [TopologicalSpace α] →
    ///     PathConnected α → Iff SimplyConnected (∀ x₀, IsTrivial (FundamentalGroup α x₀))
    /// - `Topology.FundamentalGroup.basepoint_independent` : {α : Type u} → [TopologicalSpace α] →
    ///     PathConnected α → {x₀ y₀ : α} → FundamentalGroup α x₀ ≃ FundamentalGroup α y₀
    ///   Fundamental groups at different base points are isomorphic in a path-connected space
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_fundamental_group_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_topology_fundamental_group(&mut self) -> Result<(), EnvError> {
        if self.topology_fundamental_group_init {
            return Ok(());
        }
        // #1483: dynamic stack growth for init chain + payload construction
        crate::expr::stack_safe(|| {
            self.init_topology_simply_connected()?;
            self.init_topology_path_connected()?;
            self.init_eq()?;
            self.init_iff()?;

            {
                use crate::env::generated_overlay::{
                    load_generated_namespace_overlay, TOPOLOGY_FUNDAMENTAL_GROUP_NAMESPACE,
                };
                load_generated_namespace_overlay(self, TOPOLOGY_FUNDAMENTAL_GROUP_NAMESPACE)?;
            }

            self.topology_fundamental_group_init = true;
            Ok(())
        })
    }

    /// Check if Topology.FundamentalGroup has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_fundamental_group_init == true`
    pub(crate) fn has_topology_fundamental_group(&self) -> bool {
        self.topology_fundamental_group_init
    }

    /// Initialize Topology.HomotopyEquivalence for homotopy equivalence theory.
    ///
    /// A homotopy equivalence between spaces X and Y consists of continuous maps
    /// f : X → Y and g : Y → X such that g ∘ f is homotopic to id_X and f ∘ g is
    /// homotopic to id_Y. This is weaker than homeomorphism but preserves many
    /// important topological invariants (e.g., fundamental group, homology).
    ///
    /// Prerequisites: Continuous, Contractible (brings Homotopy)
    ///
    /// ## Constants Added
    ///
    /// - `Topology.ContinuousHomotopy` : {α β : Type u} → [TopologicalSpace α] → [TopologicalSpace β] →
    ///     (α → β) → (α → β) → Type u
    ///   - Homotopy between continuous maps f and g
    /// - `Topology.ContinuousHomotopy.refl` : (f : α → β) → Continuous f → ContinuousHomotopy f f
    /// - `Topology.ContinuousHomotopy.symm` : ContinuousHomotopy f g → ContinuousHomotopy g f
    /// - `Topology.ContinuousHomotopy.trans` : ContinuousHomotopy f g → ContinuousHomotopy g h → ContinuousHomotopy f h
    /// - `Topology.HomotopyEquiv` : {α β : Type u} → [TopologicalSpace α] → [TopologicalSpace β] → Type u
    ///   - The type of homotopy equivalences between α and β
    /// - `Topology.HomotopyEquiv.toFun` : HomotopyEquiv α β → (α → β)
    ///   - The forward map
    /// - `Topology.HomotopyEquiv.invFun` : HomotopyEquiv α β → (β → α)
    ///   - The inverse map
    /// - `Topology.HomotopyEquiv.continuous_toFun` : (e : HomotopyEquiv α β) → Continuous (toFun e)
    /// - `Topology.HomotopyEquiv.continuous_invFun` : (e : HomotopyEquiv α β) → Continuous (invFun e)
    /// - `Topology.HomotopyEquiv.left_inv` : (e : HomotopyEquiv α β) → ContinuousHomotopy (invFun e ∘ toFun e) id
    /// - `Topology.HomotopyEquiv.right_inv` : (e : HomotopyEquiv α β) → ContinuousHomotopy (toFun e ∘ invFun e) id
    /// - `Topology.HomotopyEquiv.refl` : {α : Type u} → [TopologicalSpace α] → HomotopyEquiv α α
    /// - `Topology.HomotopyEquiv.symm` : HomotopyEquiv α β → HomotopyEquiv β α
    /// - `Topology.HomotopyEquiv.trans` : HomotopyEquiv α β → HomotopyEquiv β γ → HomotopyEquiv α γ
    /// - `Topology.AreHomotopyEquiv` : {α β : Type u} → [TopologicalSpace α] → [TopologicalSpace β] → Prop
    ///   - Predicate: α and β are homotopy equivalent
    /// - `Topology.are_homotopy_equiv_def` : Iff (AreHomotopyEquiv α β) (Nonempty (HomotopyEquiv α β))
    /// - `Topology.are_homotopy_equiv_refl` : AreHomotopyEquiv α α
    /// - `Topology.are_homotopy_equiv_symm` : AreHomotopyEquiv α β → AreHomotopyEquiv β α
    /// - `Topology.are_homotopy_equiv_trans` : AreHomotopyEquiv α β → AreHomotopyEquiv β γ → AreHomotopyEquiv α γ
    /// - `Topology.homeomorphism_to_homotopy_equiv` : Homeomorphism α β → HomotopyEquiv α β
    /// - `Topology.contractible_are_homotopy_equiv` : Contractible α → Contractible β → AreHomotopyEquiv α β
    /// - `Topology.homotopy_equiv_preserves_path_connected` : HomotopyEquiv α β → PathConnected α → PathConnected β
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_homotopy_equivalence_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_topology_homotopy_equivalence(&mut self) -> Result<(), EnvError> {
        if self.topology_homotopy_equivalence_init {
            return Ok(());
        }
        // #1483: dynamic stack growth for init chain + payload construction
        crate::expr::stack_safe(|| {
            self.init_topology_continuous()?;
            self.init_topology_contractible()?;
            self.init_topology_homeomorphism()?;
            self.init_topology_path_connected()?;
            self.init_classical()?;
            self.init_iff()?;

            {
                use crate::env::generated_overlay::{
                    load_generated_namespace_overlay, TOPOLOGY_HOMOTOPY_EQUIVALENCE_NAMESPACE,
                };
                load_generated_namespace_overlay(self, TOPOLOGY_HOMOTOPY_EQUIVALENCE_NAMESPACE)?;
            }

            self.topology_homotopy_equivalence_init = true;
            Ok(())
        })
    }

    /// Check if Topology.HomotopyEquivalence has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_homotopy_equivalence_init == true`
    pub(crate) fn has_topology_homotopy_equivalence(&self) -> bool {
        self.topology_homotopy_equivalence_init
    }

    /// Initialize Topology.Retract for retraction theory.
    ///
    /// A retraction is a continuous map r : X → A where A ⊆ X such that r|_A = id_A.
    /// In other words, r is a left inverse to the inclusion i : A → X, meaning r ∘ i = id_A.
    ///
    /// A deformation retract is a retraction where the composition i ∘ r is homotopic to id_X.
    /// A strong deformation retract additionally requires that every point in A stays fixed
    /// throughout the homotopy.
    ///
    /// Prerequisites: Continuous, HomotopyEquivalence (brings ContinuousHomotopy)
    ///
    /// ## Constants Added
    ///
    /// - `Topology.IsRetract` : {X : Type u} → [TopologicalSpace X] → (X → Prop) → Prop
    ///   - Predicate that a subset A is a retract of X
    /// - `Topology.Retraction` : {X : Type u} → [TopologicalSpace X] → (X → Prop) → Type u
    ///   - The type of retractions onto a subset A
    /// - `Topology.Retraction.map` : Retraction A → (X → X)
    ///   - The retraction map
    /// - `Topology.Retraction.continuous` : (r : Retraction A) → Continuous (map r)
    /// - `Topology.Retraction.maps_into` : (r : Retraction A) → ∀ x, A (map r x)
    /// - `Topology.Retraction.fixes_subset` : (r : Retraction A) → ∀ x, A x → Eq (map r x) x
    /// - `Topology.is_retract_def` : Iff (IsRetract A) (Nonempty (Retraction A))
    /// - `Topology.IsDeformationRetract` : {X : Type u} → [TopologicalSpace X] → (X → Prop) → Prop
    ///   - Predicate that a subset A is a deformation retract of X
    /// - `Topology.DeformationRetraction` : {X : Type u} → [TopologicalSpace X] → (X → Prop) → Type u
    ///   - The type of deformation retractions onto a subset A
    /// - `Topology.DeformationRetraction.toRetraction` : DeformationRetraction A → Retraction A
    /// - `Topology.DeformationRetraction.homotopy` : (r : DeformationRetraction A) → ContinuousHomotopy id (map (toRetraction r))
    /// - `Topology.is_deformation_retract_def` : Iff (IsDeformationRetract A) (Nonempty (DeformationRetraction A))
    /// - `Topology.IsStrongDeformationRetract` : {X : Type u} → [TopologicalSpace X] → (X → Prop) → Prop
    ///   - Predicate that a subset A is a strong deformation retract of X
    /// - `Topology.StrongDeformationRetraction` : {X : Type u} → [TopologicalSpace X] → (X → Prop) → Type u
    ///   - The type of strong deformation retractions onto a subset A
    /// - `Topology.StrongDeformationRetraction.toDeformationRetraction` : SDR A → DR A
    /// - `Topology.StrongDeformationRetraction.fixes_points_rel` : Prop (homotopy is relative to A)
    /// - `Topology.is_strong_deformation_retract_def` : Iff (IsStrongDeformationRetract A) (Nonempty (SDR A))
    /// - `Topology.strong_deformation_retract_is_deformation_retract` : IsStrongDeformationRetract A → IsDeformationRetract A
    /// - `Topology.deformation_retract_is_retract` : IsDeformationRetract A → IsRetract A
    /// - `Topology.deformation_retract_homotopy_equiv` : IsDeformationRetract A → AreHomotopyEquiv X A (with appropriate interpretation)
    /// - `Topology.contractible_iff_point_deformation_retract` : Contractible X ↔ (∃ x₀, IsDeformationRetract {x₀})
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_retract_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_topology_retract(&mut self) -> Result<(), EnvError> {
        if self.topology_retract_init {
            return Ok(());
        }
        // #1483: dynamic stack growth for init chain + payload construction
        crate::expr::stack_safe(|| {
            self.init_topology_continuous()?;
            self.init_topology_homotopy_equivalence()?;
            self.init_classical()?;
            self.init_iff()?;
            self.init_eq()?;

            {
                use crate::env::generated_overlay::{
                    load_generated_namespace_overlay, TOPOLOGY_RETRACT_NAMESPACE,
                };
                load_generated_namespace_overlay(self, TOPOLOGY_RETRACT_NAMESPACE)?;
            }

            self.topology_retract_init = true;
            Ok(())
        })
    }

    /// Check if Topology.Retract has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_retract_init == true`
    pub(crate) fn has_topology_retract(&self) -> bool {
        self.topology_retract_init
    }
}
