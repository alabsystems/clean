// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Differential topology for Environment
//!
//! This module contains differential topology init_* and has_* functions:
//! - Manifolds (smooth/differentiable)
//! - Lie groups
//! - Principal bundles
//! - Connections

use crate::env::{EnvError, Environment};

impl Environment {
    /// Initialize Topology.Manifold module for smooth/differentiable manifolds
    ///
    /// Provides axioms for:
    /// - Charts and atlases
    /// - Smooth structures on topological manifolds
    /// - Tangent spaces and tangent bundles
    /// - Smooth maps between manifolds
    /// - Immersions, submersions, embeddings
    /// - Submanifolds
    /// - Diffeomorphisms
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_manifold_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_topology_manifold(&mut self) -> Result<(), EnvError> {
        if self.topology_manifold_init {
            return Ok(());
        }
        // #1483: dynamic stack growth for init chain + payload construction
        crate::expr::stack_safe(|| {
            self.init_topological_space()?;
            self.init_nat()?;
            self.init_fin()?;
            self.init_list()?;
            self.init_rat()?;
            self.init_eq()?;
            self.init_exists()?;
            self.init_true_false()?;
            self.init_topology_continuous()?;
            self.init_topology_homeomorphism()?;
            self.init_add_comm_group()?;

            {
                use crate::env::generated_overlay::{
                    load_generated_namespace_overlay, namespace_source_policy,
                    NamespaceSourcePolicy, TOPOLOGY_MANIFOLD_NAMESPACE,
                };

                match namespace_source_policy(TOPOLOGY_MANIFOLD_NAMESPACE) {
                    NamespaceSourcePolicy::GeneratedOverlayFirst => {
                        load_generated_namespace_overlay(self, TOPOLOGY_MANIFOLD_NAMESPACE)?;
                    }
                    NamespaceSourcePolicy::HandwrittenOnly => {
                        return Err(EnvError::UnsupportedGeneratedNamespace {
                            namespace: TOPOLOGY_MANIFOLD_NAMESPACE.to_owned(),
                        });
                    }
                }
            }

            self.topology_manifold_init = true;
            Ok(())
        })
    }

    /// Check if Topology.Manifold has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_manifold_init == true`
    #[cfg(test)]
    pub(crate) fn has_topology_manifold(&self) -> bool {
        self.topology_manifold_init
    }

    /// Initialize Topology.LieGroup module for Lie groups and Lie algebras
    ///
    /// Provides axioms for:
    /// - Lie groups (smooth manifolds that are also groups)
    /// - Lie algebras (tangent space at identity)
    /// - Exponential map from Lie algebra to Lie group
    /// - Lie group homomorphisms
    /// - Adjoint representations
    /// - Lie subgroups
    /// - One-parameter subgroups
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_lie_group_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_topology_lie_group(&mut self) -> Result<(), EnvError> {
        if self.topology_lie_group_init {
            return Ok(());
        }
        // #1483: dynamic stack growth for init chain + payload construction
        crate::expr::stack_safe(|| {
            self.init_topological_space()?;
            self.init_nat()?;
            self.init_rat()?;
            self.init_eq()?;
            self.init_topology_manifold()?;
            self.init_group()?;
            self.init_add_comm_group()?;

            {
                use crate::env::generated_overlay::{
                    load_generated_namespace_overlay, namespace_source_policy,
                    NamespaceSourcePolicy, TOPOLOGY_LIE_GROUP_NAMESPACE,
                };

                match namespace_source_policy(TOPOLOGY_LIE_GROUP_NAMESPACE) {
                    NamespaceSourcePolicy::GeneratedOverlayFirst => {
                        load_generated_namespace_overlay(self, TOPOLOGY_LIE_GROUP_NAMESPACE)?;
                    }
                    NamespaceSourcePolicy::HandwrittenOnly => {
                        return Err(EnvError::UnsupportedGeneratedNamespace {
                            namespace: TOPOLOGY_LIE_GROUP_NAMESPACE.to_owned(),
                        });
                    }
                }
            }

            self.topology_lie_group_init = true;
            Ok(())
        })
    }

    /// Check if Topology.LieGroup has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_lie_group_init == true`
    #[cfg(test)]
    pub(crate) fn has_topology_lie_group(&self) -> bool {
        self.topology_lie_group_init
    }

    /// Initialize Topology.PrincipalBundle - principal bundles over a base space
    ///
    /// A principal G-bundle is a fiber bundle where:
    /// - The fiber is a Lie group G
    /// - G acts freely and transitively on fibers (from the right)
    /// - Local trivializations are G-equivariant
    ///
    /// Constants added (16 total):
    /// - PrincipalBundle: the type of principal G-bundles
    /// - PrincipalBundle.proj: projection map
    /// - PrincipalBundle.action: the right action of G on P
    /// - PrincipalBundle.action_free: the action is free
    /// - PrincipalBundle.action_transitive: the action is transitive on fibers
    /// - GaugeTrans, GaugeGroup: gauge transformations
    /// - gauge_trans_compose, gauge_trans_id: gauge operations
    /// - AssociatedBundle, PullbackBundle, BundleMorphism
    /// - FrameBundle, TrivialBundle, Reduction, Extension
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_principal_bundle_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    #[cfg(test)]
    pub(crate) fn init_topology_principal_bundle(&mut self) -> Result<(), EnvError> {
        if self.topology_principal_bundle_init {
            return Ok(());
        }

        // Dependencies
        self.init_topological_space()?;
        self.init_nat()?;
        self.init_eq()?;
        self.init_topology_fiber_bundle()?;
        self.init_topology_lie_group()?;
        self.init_group()?;

        // #1444 overlay: load Topology.PrincipalBundle declarations from generated
        // namespace payload artifacts (`env/generated/*`).
        {
            use crate::env::generated_overlay::{
                load_generated_namespace_overlay, TOPOLOGY_PRINCIPAL_BUNDLE_NAMESPACE,
            };
            load_generated_namespace_overlay(self, TOPOLOGY_PRINCIPAL_BUNDLE_NAMESPACE)?;
        }

        self.topology_principal_bundle_init = true;
        Ok(())
    }

    /// Check if Topology.PrincipalBundle has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_principal_bundle_init == true`
    #[cfg(test)]
    pub(crate) fn has_topology_principal_bundle(&self) -> bool {
        self.topology_principal_bundle_init
    }

    /// Initialize Topology.Connection - connections on principal and vector bundles
    ///
    /// A connection on a principal bundle provides:
    /// - A way to lift paths from the base to the total space (horizontal lift)
    /// - Parallel transport along paths
    /// - Curvature measuring non-commutativity of parallel transport
    ///
    /// Constants added (20 total):
    /// - Connection, form, curvature, flat, holonomy
    /// - flat_trivial_holonomy, VectorConnection, covariant_derivative
    /// - LeviCivita and properties (metric_compatible, torsion_free, unique)
    /// - Christoffel, RiemannCurvature, RicciTensor, ScalarCurvature
    /// - Geodesic, ParallelTransport, HorizontalLift, BianchiIdentity
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_connection_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    #[cfg(test)]
    pub(crate) fn init_topology_connection(&mut self) -> Result<(), EnvError> {
        if self.topology_connection_init {
            return Ok(());
        }

        self.init_topological_space()?;
        self.init_nat()?;
        self.init_eq()?;
        self.init_topology_principal_bundle()?;
        self.init_topology_manifold()?;
        self.init_topology_lie_group()?;

        // #1444 overlay: load Topology.Connection declarations from generated
        // namespace payload artifacts (`env/generated/*`).
        {
            use crate::env::generated_overlay::{
                load_generated_namespace_overlay, TOPOLOGY_CONNECTION_NAMESPACE,
            };
            load_generated_namespace_overlay(self, TOPOLOGY_CONNECTION_NAMESPACE)?;
        }

        self.topology_connection_init = true;
        Ok(())
    }

    /// Check if Topology.Connection has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_connection_init == true`
    #[cfg(test)]
    pub(crate) fn has_topology_connection(&self) -> bool {
        self.topology_connection_init
    }

    /// Initialize Topology.Symplectic - symplectic manifolds and structures
    ///
    /// A symplectic manifold (M, ω) is an even-dimensional smooth manifold with
    /// a closed, non-degenerate 2-form ω (the symplectic form). Key in:
    /// - Classical mechanics (phase space)
    /// - Geometric quantization
    /// - Hamiltonian dynamics
    ///
    /// Constants added (27 total):
    /// - SymplecticForm: closed nondegenerate 2-form
    /// - SymplecticManifold: manifold with symplectic form
    /// - symplectic_form_closed: dω = 0
    /// - symplectic_form_nondegenerate: ω(v, ·) = 0 ⟹ v = 0
    /// - symplectic_dim_even: symplectic manifolds are even-dimensional
    /// - Symplectomorphism: diffeomorphism preserving ω
    /// - HamiltonianVector: X_H where ι_{X_H}ω = dH
    /// - HamiltonianFlow: flow of Hamiltonian vector field
    /// - PoissonBracket: {f, g} = ω(X_f, X_g)
    /// - poisson_jacobi: {f, {g, h}} + {g, {h, f}} + {h, {f, g}} = 0
    /// - LagrangianSubmanifold: maximal isotropic submanifold
    /// - CoisotropicSubmanifold: ω-orthogonal contained in tangent
    /// - IsotropicSubmanifold: tangent contained in ω-orthogonal
    /// - MomentMap: μ : M → g* for G-action
    /// - moment_equivariant: μ is G-equivariant
    /// - SymplecticReduction: M // G = μ⁻¹(0) / G
    /// - Darboux: local normal form theorem
    /// - Moser: nearby symplectic forms are symplectomorphic
    /// - ContactManifold: odd-dimensional contact structure
    /// - ContactForm: α ∧ (dα)^n ≠ 0
    /// - Reeb: unique vector field with α(R) = 1, ι_R dα = 0
    /// - Contactomorphism: diffeomorphism preserving contact structure
    /// - Legendrian: submanifold tangent to contact distribution
    /// - GrayStability: nearby contact structures are contactomorphic
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_symplectic_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    #[cfg(test)]
    pub(crate) fn init_topology_symplectic(&mut self) -> Result<(), EnvError> {
        if self.topology_symplectic_init {
            return Ok(());
        }

        // Dependencies
        self.init_topological_space()?;
        self.init_nat()?;
        self.init_eq()?;
        self.init_topology_manifold()?;
        self.init_topology_lie_group()?;
        self.init_topology_derham()?;

        // #1444 overlay: load Topology.Symplectic declarations from generated
        // namespace payload artifacts (`env/generated/*`).
        {
            use crate::env::generated_overlay::{
                load_generated_namespace_overlay, TOPOLOGY_SYMPLECTIC_NAMESPACE,
            };
            load_generated_namespace_overlay(self, TOPOLOGY_SYMPLECTIC_NAMESPACE)?;
        }

        self.topology_symplectic_init = true;
        Ok(())
    }

    /// Check if Topology.Symplectic has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_symplectic_init == true`
    #[cfg(test)]
    pub(crate) fn has_topology_symplectic(&self) -> bool {
        self.topology_symplectic_init
    }

    /// Initialize Topology.Kahler module for Kähler manifolds
    ///
    /// Kähler geometry is the intersection of Riemannian, symplectic, and complex geometry.
    /// A Kähler manifold has three compatible structures:
    /// - A Riemannian metric g
    /// - A symplectic form ω
    /// - An almost complex structure J
    ///   satisfying ω(X, Y) = g(JX, Y) and ∇J = 0 (J is parallel)
    ///
    /// Provides axioms for:
    /// - ComplexStructure: J² = -Id
    /// - AlmostComplexManifold: manifold with J
    /// - Hermitian: g(JX, JY) = g(X, Y)
    /// - KahlerForm: ω(X, Y) = g(JX, Y)
    /// - KahlerManifold: closed Kähler form
    /// - HolomorphicMap: respects complex structures
    /// - HolomorphicVectorBundle: complex vector bundle with holomorphic structure
    /// - ChernConnection: unique connection compatible with metric and complex structure
    /// - ChernClass: topological invariants c_k
    /// - RicciForm: curvature form ρ = Ric(J·, ·)
    /// - KahlerEinstein: Ricci form proportional to Kähler form
    /// - CalabiYau: Ricci-flat Kähler manifold
    /// - HodgeDecomposition: H^k = ⊕_{p+q=k} H^{p,q}
    /// - DolbeaultCohomology: H^{p,q} via ∂̄ operator
    /// - HardLefschetz: `[ω]^k` : H^{n-k} → H^{n+k} is isomorphism
    /// - Kodaira vanishing: cohomology vanishing for positive line bundles
    /// - FubiniStudy: canonical metric on CP^n
    /// - HyperKahler: quaternionic Kähler with three complex structures
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_kahler_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    #[cfg(test)]
    pub(crate) fn init_topology_kahler(&mut self) -> Result<(), EnvError> {
        if self.topology_kahler_init {
            return Ok(());
        }

        // Dependencies
        // Note: init_topology_manifold includes RiemannianManifold and RiemannianMetric
        self.init_topological_space()?;
        self.init_nat()?;
        self.init_eq()?;
        self.init_topology_manifold()?;
        self.init_topology_symplectic()?;
        self.init_topology_derham()?;

        // #1444 overlay: load Topology.Kahler declarations from generated
        // namespace payload artifacts (`env/generated/*`).
        {
            use crate::env::generated_overlay::{
                load_generated_namespace_overlay, TOPOLOGY_KAHLER_NAMESPACE,
            };
            load_generated_namespace_overlay(self, TOPOLOGY_KAHLER_NAMESPACE)?;
        }

        self.topology_kahler_init = true;
        Ok(())
    }

    /// Check if Topology.Kahler has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_kahler_init == true`
    #[cfg(test)]
    pub(crate) fn has_topology_kahler(&self) -> bool {
        self.topology_kahler_init
    }

    /// Initialize Topology.Spin module for spin geometry
    ///
    /// Spin geometry is fundamental to mathematical physics and topology.
    /// Spin structures on a manifold M exist iff w₂(M) = 0 (second Stiefel-Whitney class).
    ///
    /// Provides axioms for:
    /// - Clifford algebras: Cl(V, q) algebraic structure for quadratic forms
    /// - Spin groups: Spin(n) double cover of SO(n)
    /// - Spin structures: lifts of frame bundle to Spin(n)
    /// - Spinor bundles: associated vector bundles via spin representations
    /// - Dirac operators: first-order differential operators on spinor bundles
    /// - Index theory: Atiyah-Singer index theorem for Dirac operators
    /// - Spin^c structures: generalization when spin structure doesn't exist
    /// - Pin structures: extension to non-orientable manifolds
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_spin_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    #[cfg(test)]
    pub(crate) fn init_topology_spin(&mut self) -> Result<(), EnvError> {
        if self.topology_spin_init {
            return Ok(());
        }

        // Dependencies
        self.init_topological_space()?;
        self.init_nat()?;
        self.init_int()?;
        self.init_eq()?;
        self.init_topology_manifold()?;
        self.init_topology_principal_bundle()?;
        self.init_topology_connection()?;
        self.init_topology_characteristic()?;

        // #1444 overlay: load Topology.Spin declarations from generated
        // namespace payload artifacts (`env/generated/*`).
        {
            use crate::env::generated_overlay::{
                load_generated_namespace_overlay, TOPOLOGY_SPIN_NAMESPACE,
            };
            load_generated_namespace_overlay(self, TOPOLOGY_SPIN_NAMESPACE)?;
        }

        self.topology_spin_init = true;
        Ok(())
    }

    /// Check if Topology.Spin has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_spin_init == true`
    #[cfg(test)]
    pub(crate) fn has_topology_spin(&self) -> bool {
        self.topology_spin_init
    }
}
