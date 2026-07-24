// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bundle topology for Environment
//!
//! This module contains bundle-related init_* and has_* functions:
//! - Fiber bundles
//! - Higher homotopy groups
//! - Suspensions
//! - Vector bundles
//! - Coproduct topologies

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Topology.FiberBundle and related fiber bundle theory.
    ///
    /// Fiber bundles are fundamental structures in topology and differential geometry.
    /// A fiber bundle consists of:
    /// - A total space E
    /// - A base space B
    /// - A fiber F
    /// - A projection π : E → B
    /// - Local triviality: locally, E looks like B × F
    ///
    /// ## Constants Added
    ///
    /// ### Core Bundle Structure
    /// - `Topology.FiberBundle` : {E B F : Type u} → [TopologicalSpace E] →
    ///   [TopologicalSpace B] → [TopologicalSpace F] → (E → B) → Type u
    ///   - The type of fiber bundle structures on (E, B, F, π)
    /// - `Topology.FiberBundle.proj` : FiberBundle π → (E → B)
    ///   - The projection map (π itself)
    /// - `Topology.FiberBundle.continuous_proj` : (b : FiberBundle π) → Continuous (proj b)
    ///   - The projection is continuous
    /// - `Topology.FiberBundle.fiber` : FiberBundle π → B → Type u
    ///   - The fiber over a point (π⁻¹(b))
    ///
    /// ### Local Triviality
    /// - `Topology.Trivialization` : {E B F : Type u} → [TopologicalSpace E] →
    ///   [TopologicalSpace B] → [TopologicalSpace F] → (E → B) → Type u
    ///   - A local trivialization of a bundle
    /// - `Topology.Trivialization.baseSet` : Trivialization π → (B → Prop)
    ///   - The open set in B over which the trivialization is defined
    /// - `Topology.Trivialization.baseSet_open` : (t : Trivialization π) → IsOpen (baseSet t)
    /// - `Topology.Trivialization.toFun` : Trivialization π → (E → B × F)
    ///   - The trivialization homeomorphism
    /// - `Topology.Trivialization.invFun` : Trivialization π → (B × F → E)
    ///   - The inverse homeomorphism
    /// - `Topology.Trivialization.proj_toFun` : ∀ e, (toFun t e).1 = π e
    ///   - Projection compatibility
    ///
    /// ### Bundle Maps
    /// - `Topology.IsBundleMap` : {E₁ E₂ B₁ B₂ F₁ F₂ : Type u} →
    ///   FiberBundle π₁ → FiberBundle π₂ → (E₁ → E₂) → (B₁ → B₂) → Prop
    ///   - Predicate for bundle morphisms
    /// - `Topology.IsBundleMap.continuous_total` : IsBundleMap b₁ b₂ φ f → Continuous φ
    /// - `Topology.IsBundleMap.continuous_base` : IsBundleMap b₁ b₂ φ f → Continuous f
    /// - `Topology.IsBundleMap.commutes` : IsBundleMap b₁ b₂ φ f → ∀ e, π₂ (φ e) = f (π₁ e)
    ///
    /// ### Special Bundles
    /// - `Topology.IsTrivialBundle` : FiberBundle π → Prop
    ///   - Predicate for globally trivial bundles (E ≅ B × F)
    /// - `Topology.trivial_bundle` : {B F : Type u} → [TopologicalSpace B] →
    ///   [TopologicalSpace F] → FiberBundle (Prod.fst : B × F → B)
    ///   - The trivial bundle B × F → B
    /// - `Topology.IsPullbackBundle` : FiberBundle π → (B' → B) → FiberBundle π' → Prop
    ///   - Predicate for pullback bundles
    ///
    /// ### Bundle Properties
    /// - `Topology.IsLocallyTrivial` : FiberBundle π → Prop
    ///   - Every point has a trivializing neighborhood (by definition true for FiberBundle)
    /// - `Topology.bundle_fiber_nonempty` : FiberBundle π → (b : B) → Nonempty (fiber b)
    ///   - Fibers are nonempty (if surjective projection)
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_fiber_bundle_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_topology_fiber_bundle(&mut self) -> Result<(), EnvError> {
        if self.topology_fiber_bundle_init {
            return Ok(());
        }
        // #1483: dynamic stack growth for init chain + payload construction
        crate::expr::stack_safe(|| {
            self.init_topology_continuous()?;
            self.init_prod()?;
            self.init_classical()?;
            self.init_eq()?;

            {
                use crate::env::generated_overlay::{
                    load_generated_namespace_overlay, TOPOLOGY_FIBER_BUNDLE_NAMESPACE,
                };
                load_generated_namespace_overlay(self, TOPOLOGY_FIBER_BUNDLE_NAMESPACE)?;
            }

            self.topology_fiber_bundle_init = true;
            Ok(())
        })
    }

    /// Check if Topology.FiberBundle has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_fiber_bundle_init == true`
    pub(crate) fn has_topology_fiber_bundle(&self) -> bool {
        self.topology_fiber_bundle_init
    }
    // ================================================================
    // TOPOLOGY.HIGHERHOMOTOPY - Higher Homotopy Groups πₙ
    // ================================================================
    //
    // Higher homotopy groups πₙ(X, x₀) for n ≥ 2 generalize the fundamental group:
    // - πₙ(X, x₀) = [Sⁿ, X]₊ (basepoint-preserving homotopy classes of maps Sⁿ → X)
    // - For n ≥ 2, πₙ is always abelian (unlike π₁)
    // - π₀(X) = path-connected components (not a group, but a pointed set)
    //
    // Key structures:
    // - `Topology.Sphere` : ℕ → Type - the n-sphere Sⁿ
    // - `Topology.SphereBasepoint` : {n : ℕ} → Sphere n - basepoint of Sⁿ
    // - `Topology.HigherHomotopyGroup` : {α : Type u} → [TopologicalSpace α] → ℕ → α → Type u
    //   The higher homotopy group πₙ(α, x₀)
    // - Group operations for πₙ (n ≥ 1): mul, one, inv
    // - Abelian property for πₙ (n ≥ 2): mul_comm
    // - Long exact sequence of a fibration
    // ================================================================

    /// Initialize Topology.HigherHomotopy primitives
    ///
    /// Adds the following constants:
    /// - `Topology.Sphere` : ℕ → Type 0 - the n-sphere Sⁿ
    /// - `Topology.Sphere.basepoint` : {n : ℕ} → Sphere n - the basepoint of Sⁿ
    /// - `Topology.Sphere.topological_space` : {n : ℕ} → TopologicalSpace (Sphere n)
    /// - `Topology.BasedMap` : {α : Type u} → [TopologicalSpace α] → {n : ℕ} → α → Type u
    ///   - A basepoint-preserving continuous map Sⁿ → α
    /// - `Topology.BasedMap.eval` : BasedMap x₀ → Sphere n → α
    /// - `Topology.BasedMap.preserves_basepoint` : (f : BasedMap x₀) → f.eval basepoint = x₀
    /// - `Topology.BasedHomotopy` : {α : Type u} → [TopologicalSpace α] →
    ///     {n : ℕ} → {x₀ : α} → BasedMap x₀ → BasedMap x₀ → Type u
    ///   - A basepoint-preserving homotopy between based maps
    /// - `Topology.HigherHomotopyGroup` : {α : Type u} → [TopologicalSpace α] → ℕ → α → Type u
    ///   - πₙ(α, x₀) - the n-th homotopy group
    /// - `Topology.HigherHomotopyGroup.class` : BasedMap x₀ → HigherHomotopyGroup n x₀
    /// - `Topology.HigherHomotopyGroup.class_eq` : BasedHomotopy f g → class f = class g
    /// - `Topology.HigherHomotopyGroup.mul` : (n > 0) → πₙ → πₙ → πₙ (group operation)
    /// - `Topology.HigherHomotopyGroup.one` : (n > 0) → πₙ (identity element)
    /// - `Topology.HigherHomotopyGroup.inv` : (n > 0) → πₙ → πₙ (inverse)
    /// - `Topology.HigherHomotopyGroup.mul_assoc` : (n > 0) → associativity
    /// - `Topology.HigherHomotopyGroup.one_mul` : (n > 0) → one · x = x
    /// - `Topology.HigherHomotopyGroup.mul_one` : (n > 0) → x · one = x
    /// - `Topology.HigherHomotopyGroup.mul_inv` : (n > 0) → x · x⁻¹ = one
    /// - `Topology.HigherHomotopyGroup.mul_comm` : (n > 1) → x · y = y · x (abelian for n ≥ 2)
    /// - `Topology.HigherHomotopyGroup.pi_zero_eq` : π₀ ≃ PathComponents
    /// - `Topology.HigherHomotopyGroup.pi_one_eq` : π₁ ≃ FundamentalGroup
    /// - `Topology.HigherHomotopyGroup.sphere_homotopy_trivial` : πₙ(Sⁿ) ≃ ℤ (degree map)
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_higher_homotopy_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_topology_higher_homotopy(&mut self) -> Result<(), EnvError> {
        if self.topology_higher_homotopy_init {
            return Ok(());
        }
        // Wrap in stack_safe: this init chain is 7 levels deep and each level
        // constructs large Expr trees. Without dynamic stack growth, direct
        // test-binary invocation (without RUST_MIN_STACK) overflows. See #1483.
        crate::expr::stack_safe(|| self.init_topology_higher_homotopy_impl())
    }

    fn init_topology_higher_homotopy_impl(&mut self) -> Result<(), EnvError> {
        // Initialize dependencies
        self.init_topology_fundamental_group()?; // brings FundamentalGroup, Loop, LoopHomotopy
        self.init_topology_path_connected()?; // brings PathConnected, Path
        self.init_nat()?;
        self.init_lt()?; // brings Nat.lt, needed for n > 0 condition
        self.init_eq()?;
        self.init_iff()?;

        // #1444 overlay: load 18 unconditional Topology.HigherHomotopy declarations
        // from generated namespace payload (`env/generated/topology_higher_homotopy.rs`)
        // instead of inline handwritten add_decl calls with manual bvar arithmetic.
        {
            use crate::env::generated_overlay::{
                load_generated_namespace_overlay, TOPOLOGY_HIGHER_HOMOTOPY_NAMESPACE,
            };
            load_generated_namespace_overlay(self, TOPOLOGY_HIGHER_HOMOTOPY_NAMESPACE)?;
        }

        // --- Conditional declarations (depend on runtime has_topology_* guards) ---
        // These cannot be part of the static overlay payload.

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let prop = Expr::sort(Level::zero());
        let topological_space =
            |lvl: Level| Expr::const_(Name::from_string("TopologicalSpace"), vec![lvl]);

        // ================================================================
        // Conditional: pi_one_eq_fundamental_group
        // {α : Type u} → [TopologicalSpace α] → {x₀ : α} → Prop
        // ================================================================
        if self.has_topology_fundamental_group() {
            use crate::env::decl_builder::EnvDeclBuilder;
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let ts_ty = Expr::app(topological_space(u_level.clone()), alpha.clone());
            let (ts_id, _inst) = b.fresh_local(ts_ty.clone());
            let (x0_id, _x0) = b.fresh_local(alpha.clone());
            let e = b.mk_pi(x0_id, BinderInfo::Implicit, alpha.clone(), prop.clone());
            let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
            let pi_one_eq_type = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);

            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Topology.HigherHomotopyGroup.pi_one_eq_fundamental_group"),
                level_params: vec![u.clone()],
                type_: pi_one_eq_type,
            })?;
        }

        // ================================================================
        // Conditional: contractible_trivial
        // {α : Type u} → [TopologicalSpace α] → {x₀ : α} →
        // Contractible α → {n : ℕ} → (0 < n) → (x : πₙ) → Prop
        // ================================================================
        if self.has_topology_contractible() {
            use crate::env::decl_builder::EnvDeclBuilder;
            let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
            let nat_zero_c = Expr::const_(Name::from_string("Nat.zero"), vec![]);
            let nat_lt_c = Expr::const_(Name::from_string("Nat.lt"), vec![]);
            let higher_homotopy_group = |lvl: Level| {
                Expr::const_(Name::from_string("Topology.HigherHomotopyGroup"), vec![lvl])
            };
            let contractible =
                |lvl: Level| Expr::const_(Name::from_string("Topology.Contractible"), vec![lvl]);

            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let ts_ty = Expr::app(topological_space(u_level.clone()), alpha.clone());
            let (ts_id, inst) = b.fresh_local(ts_ty.clone());
            let (x0_id, x0) = b.fresh_local(alpha.clone());
            let contr_ty = Expr::app(
                Expr::app(contractible(u_level.clone()), alpha.clone()),
                inst.clone(),
            );
            let (hc_id, _hc) = b.fresh_local(contr_ty.clone());
            let (n_id, n) = b.fresh_local(nat_type.clone());
            let lt_n = Expr::app(Expr::app(nat_lt_c, nat_zero_c), n.clone());
            let (hn_id, _hn) = b.fresh_local(lt_n.clone());
            let hhg = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(higher_homotopy_group(u_level.clone()), alpha.clone()),
                        inst.clone(),
                    ),
                    n.clone(),
                ),
                x0.clone(),
            );
            let (x_id, _x) = b.fresh_local(hhg.clone());
            let e = b.mk_pi(x_id, BinderInfo::Default, hhg, prop.clone());
            let e = b.mk_pi(hn_id, BinderInfo::Default, lt_n, e);
            let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_type, e);
            let e = b.mk_pi(hc_id, BinderInfo::Default, contr_ty, e);
            let e = b.mk_pi(x0_id, BinderInfo::Implicit, alpha.clone(), e);
            let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
            let contractible_trivial_type =
                b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);

            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Topology.HigherHomotopyGroup.contractible_trivial"),
                level_params: vec![u.clone()],
                type_: contractible_trivial_type,
            })?;
        }

        // ================================================================
        // Conditional: homotopy_equiv_iso
        // {α β : Type u} → [TS α] → [TS β] → {x₀ : α} → {y₀ : β} →
        // {n : ℕ} → Prop
        // ================================================================
        if self.has_topology_homotopy_equivalence() {
            use crate::env::decl_builder::EnvDeclBuilder;
            let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);

            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_u.clone());
            let ts_alpha = Expr::app(topological_space(u_level.clone()), alpha.clone());
            let (tsa_id, _tsa) = b.fresh_local(ts_alpha.clone());
            let ts_beta = Expr::app(topological_space(u_level.clone()), beta.clone());
            let (tsb_id, _tsb) = b.fresh_local(ts_beta.clone());
            let (x0_id, _x0) = b.fresh_local(alpha.clone());
            let (y0_id, _y0) = b.fresh_local(beta.clone());
            let (n_id, _n) = b.fresh_local(nat_type.clone());
            let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_type, prop.clone());
            let e = b.mk_pi(y0_id, BinderInfo::Implicit, beta.clone(), e);
            let e = b.mk_pi(x0_id, BinderInfo::Implicit, alpha.clone(), e);
            let e = b.mk_pi(tsb_id, BinderInfo::InstImplicit, ts_beta, e);
            let e = b.mk_pi(tsa_id, BinderInfo::InstImplicit, ts_alpha, e);
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), e);
            let homotopy_equiv_iso_type =
                b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);

            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Topology.HigherHomotopyGroup.homotopy_equiv_iso"),
                level_params: vec![u.clone()],
                type_: homotopy_equiv_iso_type,
            })?;
        }

        self.topology_higher_homotopy_init = true;
        Ok(())
    }

    /// Check if Topology.HigherHomotopy has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_higher_homotopy_init == true`
    pub(crate) fn has_topology_higher_homotopy(&self) -> bool {
        self.topology_higher_homotopy_init
    }
}
