// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Functional analysis structures for Environment
//!
//! This module contains functional analysis initialization:
//! - Normed spaces: vector spaces with norm structure
//! - Banach spaces: complete normed spaces
//! - Hilbert spaces: complete inner product spaces
//! - Bounded linear operators: continuous linear maps
//! - Spectral theory: eigenvalues, spectrum, functional calculus
//! - Operator algebras: C*-algebras, von Neumann algebras

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize FunctionalAnalysis module
    ///
    /// Functional analysis studies infinite-dimensional vector spaces with
    /// topological structure. It is fundamental to:
    /// - Partial differential equations
    /// - Quantum mechanics
    /// - Signal processing
    /// - Optimization theory
    ///
    /// Key concepts:
    /// - Normed spaces: vector spaces with norm ‖·‖
    /// - Banach spaces: complete normed spaces
    /// - Hilbert spaces: complete inner product spaces
    /// - Bounded operators: continuous linear maps
    /// - Spectral theory: generalization of eigenvalue theory
    ///
    /// This module provides axioms for:
    /// - Norms and normed spaces
    /// - Banach and Hilbert spaces
    /// - Bounded linear operators
    /// - Spectral theory fundamentals
    /// - Operator algebras basics
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.functional_analysis_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_functional_analysis(&mut self) -> Result<(), EnvError> {
        if self.functional_analysis_init {
            return Ok(());
        }

        // Dependencies
        self.init_eq()?;
        self.init_nat()?;
        self.init_rat()?;
        self.init_topological_space()?;
        self.init_algebra_linear()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        // Functional analysis constants
        for name in &[
            // ================================================================
            // Norms and Seminorms
            // ================================================================
            "Analysis.Norm",            // ‖·‖ : E → ℝ
            "Analysis.norm_nonneg",     // ‖x‖ ≥ 0
            "Analysis.norm_eq_zero",    // ‖x‖ = 0 ↔ x = 0
            "Analysis.norm_add_le",     // ‖x + y‖ ≤ ‖x‖ + ‖y‖
            "Analysis.norm_smul",       // ‖c • x‖ = |c| * ‖x‖
            "Analysis.norm_neg",        // ‖-x‖ = ‖x‖
            "Analysis.norm_sub_rev",    // ‖x - y‖ = ‖y - x‖
            "Analysis.Seminorm",        // seminorm (allows ‖x‖ = 0 for x ≠ 0)
            "Analysis.seminorm_nonneg", // p(x) ≥ 0
            "Analysis.seminorm_add_le", // p(x + y) ≤ p(x) + p(y)
            "Analysis.seminorm_smul",   // p(c • x) = |c| * p(x)
            // ================================================================
            // Normed Spaces
            // ================================================================
            "Analysis.NormedAddCommGroup", // normed abelian group
            "Analysis.NormedSpace",        // normed vector space over 𝕜
            "Analysis.NormedRing",         // normed ring
            "Analysis.NormedAlgebra",      // normed algebra
            "Analysis.NormedField",        // normed field
            "Analysis.dist_eq_norm",       // d(x, y) = ‖x - y‖
            "Analysis.edist_eq_norm",      // extended distance from norm
            "Analysis.norm_sub_le",        // ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖
            // ================================================================
            // Inner Product Spaces
            // ================================================================
            "Analysis.InnerProductSpace",     // ⟨·, ·⟩ : E × E → 𝕜
            "Analysis.inner_self_nonneg",     // ⟨x, x⟩ ≥ 0 (real part)
            "Analysis.inner_self_eq_zero",    // ⟨x, x⟩ = 0 ↔ x = 0
            "Analysis.inner_add_left",        // ⟨x + y, z⟩ = ⟨x, z⟩ + ⟨y, z⟩
            "Analysis.inner_smul_left",       // ⟨c • x, y⟩ = c * ⟨x, y⟩
            "Analysis.inner_conj_symm",       // ⟨x, y⟩ = conj ⟨y, x⟩
            "Analysis.norm_sq_eq_inner",      // ‖x‖² = ⟨x, x⟩
            "Analysis.inner_mul_le_norm_mul", // |⟨x, y⟩| ≤ ‖x‖ * ‖y‖ (Cauchy-Schwarz)
            "Analysis.parallelogram_law",     // ‖x+y‖² + ‖x-y‖² = 2(‖x‖² + ‖y‖²)
            "Analysis.polarization_identity", // 4⟨x,y⟩ = ‖x+y‖² - ‖x-y‖² + i...
            // ================================================================
            // Banach Spaces
            // ================================================================
            "Analysis.CompleteSpace",          // complete metric space
            "Analysis.BanachSpace",            // complete normed space
            "Analysis.banach_closed_subspace", // closed subspace of Banach is Banach
            "Analysis.banach_quotient",        // quotient of Banach by closed is Banach
            "Analysis.banach_product",         // product of Banach spaces is Banach
            "Analysis.UniformConvergence",     // uniform convergence of sequences
            "Analysis.uniform_limit",          // uniform limit preserves properties
            "Analysis.series_summable",        // ∑ xₙ converges
            "Analysis.series_absolute_conv",   // absolute convergence
            "Analysis.norm_series_le",         // ‖∑ xₙ‖ ≤ ∑ ‖xₙ‖
            // ================================================================
            // Hilbert Spaces
            // ================================================================
            "Analysis.HilbertSpace",          // complete inner product space
            "Analysis.orthogonal_projection", // P : H → K for closed K ⊆ H
            "Analysis.projection_orthogonal", // x - Px ⊥ K
            "Analysis.projection_closest_point", // ‖x - Px‖ = inf_{y ∈ K} ‖x - y‖
            "Analysis.projection_idempotent", // P² = P
            "Analysis.projection_self_adjoint", // P* = P
            "Analysis.riesz_representation",  // H* ≅ H via inner product
            "Analysis.orthonormal_basis",     // {eᵢ} with ⟨eᵢ, eⱼ⟩ = δᵢⱼ
            "Analysis.orthonormal_expansion", // x = ∑ᵢ ⟨x, eᵢ⟩ eᵢ
            "Analysis.parseval_identity",     // ‖x‖² = ∑ᵢ |⟨x, eᵢ⟩|²
            "Analysis.bessel_inequality",     // ∑ᵢ |⟨x, eᵢ⟩|² ≤ ‖x‖²
            // ================================================================
            // Bounded Linear Operators
            // ================================================================
            "Analysis.ContinuousLinearMap",         // T : E →L[𝕜] F
            "Analysis.ContinuousLinearMap.mk",      // construct bounded linear map
            "Analysis.ContinuousLinearMap.op_norm", // ‖T‖ = sup_{‖x‖=1} ‖Tx‖
            "Analysis.op_norm_nonneg",              // ‖T‖ ≥ 0
            "Analysis.op_norm_le_iff",              // ‖T‖ ≤ c ↔ ∀ x, ‖Tx‖ ≤ c * ‖x‖
            "Analysis.apply_norm_le",               // ‖Tx‖ ≤ ‖T‖ * ‖x‖
            "Analysis.op_norm_comp_le",             // ‖S ∘ T‖ ≤ ‖S‖ * ‖T‖
            "Analysis.op_norm_id",                  // ‖id‖ ≤ 1
            "Analysis.BoundedLinearEquiv",          // bounded linear isomorphism
            "Analysis.bounded_linear_equiv_symm",   // inverse of bounded isomorphism
            // ================================================================
            // Operator Spaces
            // ================================================================
            "Analysis.ContinuousLinearMap.BanachSpace", // B(E, F) is Banach
            "Analysis.ContinuousLinearMap.add",         // T + S operator
            "Analysis.ContinuousLinearMap.smul",        // c • T operator
            "Analysis.ContinuousLinearMap.comp",        // S ∘ T operator
            "Analysis.op_norm_add_le",                  // ‖T + S‖ ≤ ‖T‖ + ‖S‖
            "Analysis.op_norm_smul",                    // ‖c • T‖ = |c| * ‖T‖
            // ================================================================
            // Dual Spaces
            // ================================================================
            "Analysis.NormedSpace.Dual",                // E* = E →L[𝕜] 𝕜
            "Analysis.NormedSpace.dual_def",            // dual space definition
            "Analysis.NormedSpace.dual_pairing",        // ⟨φ, x⟩ = φ(x)
            "Analysis.NormedSpace.Dual.BanachSpace",    // E* is always Banach
            "Analysis.NormedSpace.bidual",              // E** = (E*)*
            "Analysis.NormedSpace.canonical_embedding", // J : E → E**
            "Analysis.canonical_embedding_isometry",    // ‖Jx‖ = ‖x‖
            "Analysis.reflexive",                       // E ≅ E** via J
            // ================================================================
            // Hahn-Banach Theorem
            // ================================================================
            "Analysis.HahnBanach.extension", // extend functional preserving bound
            "Analysis.HahnBanach.separation", // separating hyperplane theorem
            "Analysis.HahnBanach.geometric", // geometric Hahn-Banach
            "Analysis.exists_dual_vector",   // ∀ x ≠ 0, ∃ φ, φ(x) = ‖x‖, ‖φ‖ = 1
            "Analysis.dual_norm_eq",         // ‖x‖ = sup_{‖φ‖≤1} |φ(x)|
            // ================================================================
            // Open Mapping and Closed Graph
            // ================================================================
            "Analysis.OpenMapping.theorem", // T surjective → T is open
            "Analysis.ClosedGraph.theorem", // graph(T) closed → T bounded
            "Analysis.BanachSteinhaus",     // uniform boundedness principle
            "Analysis.bounded_of_pointwise_bounded", // pointwise bounded → uniformly bounded
            // ================================================================
            // Compact Operators
            // ================================================================
            "Analysis.CompactOperator", // T maps bounded to precompact
            "Analysis.compact_op_def",  // T bounded and T(B₁) precompact
            "Analysis.compact_op_of_finite_rank", // finite rank → compact
            "Analysis.compact_op_ideal", // K ∘ T and T ∘ K compact
            "Analysis.compact_op_limit", // limit of finite rank is compact
            "Analysis.compact_op_adjoint", // T compact → T* compact
            "Analysis.compact_op_composition", // K compact, T bounded → K ∘ T compact
            // ================================================================
            // Fredholm Operators
            // ================================================================
            "Analysis.FredholmOperator", // finite dim kernel and cokernel
            "Analysis.fredholm_index",   // index(T) = dim(ker T) - dim(coker T)
            "Analysis.fredholm_index_zero", // index(id) = 0
            "Analysis.fredholm_index_sum", // index(S ∘ T) = index(S) + index(T)
            "Analysis.fredholm_perturbation", // T Fredholm, K compact → T + K Fredholm
            "Analysis.fredholm_index_stable", // index(T + K) = index(T) for K compact
            // ================================================================
            // Spectrum and Resolvent
            // ================================================================
            "Analysis.Spectrum",           // σ(T) = {λ | T - λI not invertible}
            "Analysis.spectrum_def",       // λ ∈ σ(T) definition
            "Analysis.resolvent_set",      // ρ(T) = complement of σ(T)
            "Analysis.resolvent",          // R(λ, T) = (T - λI)⁻¹
            "Analysis.resolvent_equation", // R(λ) - R(μ) = (λ-μ)R(λ)R(μ)
            "Analysis.spectrum_nonempty",  // σ(T) ≠ ∅ for Banach
            "Analysis.spectrum_closed",    // σ(T) is closed
            "Analysis.spectrum_bounded",   // σ(T) ⊆ B(0, ‖T‖)
            "Analysis.spectral_radius",    // r(T) = sup{|λ| : λ ∈ σ(T)}
            "Analysis.spectral_radius_formula", // r(T) = lim ‖Tⁿ‖^(1/n)
            // ================================================================
            // Point, Continuous, and Residual Spectrum
            // ================================================================
            "Analysis.point_spectrum",      // σₚ(T) = eigenvalues
            "Analysis.continuous_spectrum", // σc(T): (T-λI) injective, dense range, unbounded inverse
            "Analysis.residual_spectrum",   // σᵣ(T): (T-λI) injective, non-dense range
            "Analysis.spectrum_partition",  // σ = σₚ ∪ σc ∪ σᵣ
            "Analysis.eigenvalue_bound",    // |λ| ≤ ‖T‖ for λ eigenvalue
            // ================================================================
            // Self-Adjoint Operators
            // ================================================================
            "Analysis.IsSelfAdjoint",                        // T* = T
            "Analysis.self_adjoint_inner",                   // ⟨Tx, y⟩ = ⟨x, Ty⟩
            "Analysis.self_adjoint_spectrum_real",           // σ(T) ⊆ ℝ for T* = T
            "Analysis.self_adjoint_eigenvectors_orthogonal", // eigenspaces orthogonal
            "Analysis.IsPositive",                           // ⟨Tx, x⟩ ≥ 0
            "Analysis.positive_spectrum_nonneg",             // σ(T) ⊆ [0, ∞) for T positive
            "Analysis.positive_square_root",                 // T ≥ 0 → ∃! S ≥ 0, S² = T
            // ================================================================
            // Normal Operators
            // ================================================================
            "Analysis.IsNormal",                       // T T* = T* T
            "Analysis.normal_spectral_radius",         // r(T) = ‖T‖ for normal T
            "Analysis.normal_eigenvectors_orthogonal", // eigenvectors orthogonal
            "Analysis.IsUnitary",                      // T T* = T* T = I
            "Analysis.unitary_spectrum_circle",        // σ(U) ⊆ S¹ for unitary U
            "Analysis.unitary_isometry",               // ‖Ux‖ = ‖x‖
            // ================================================================
            // Spectral Theorem
            // ================================================================
            "Analysis.SpectralTheorem.compact_self_adjoint", // T = ∑ λᵢ Pᵢ
            "Analysis.compact_sa_eigenvalues",               // eigenvalues real, → 0
            "Analysis.compact_sa_eigenvectors",              // eigenvectors form ONB
            "Analysis.SpectralTheorem.bounded_self_adjoint", // spectral measure version
            "Analysis.spectral_measure",                     // E : Borel(σ(T)) → projections
            "Analysis.spectral_integral",                    // T = ∫ λ dE(λ)
            "Analysis.functional_calculus",                  // f(T) = ∫ f(λ) dE(λ)
            // ================================================================
            // Lp Spaces (Function Spaces)
            // ================================================================
            "Analysis.Lp.BanachSpace",  // Lp is Banach for 1 ≤ p < ∞
            "Analysis.Lp.HilbertSpace", // L² is Hilbert
            "Analysis.Lp.norm_def",     // ‖f‖ₚ = (∫ |f|ᵖ)^(1/p)
            "Analysis.Lp.holder",       // ‖fg‖₁ ≤ ‖f‖ₚ ‖g‖_q (1/p + 1/q = 1)
            "Analysis.Lp.minkowski",    // ‖f + g‖ₚ ≤ ‖f‖ₚ + ‖g‖ₚ
            "Analysis.Lp.dual",         // (Lp)* ≅ Lq for 1 < p < ∞
            "Analysis.L2.inner",        // ⟨f, g⟩ = ∫ f ḡ
            "Analysis.L_infty",         // essential supremum norm
            // ================================================================
            // Sobolev Spaces
            // ================================================================
            "Analysis.SobolevSpace",              // W^{k,p}(Ω)
            "Analysis.sobolev_norm",              // ‖u‖_{W^{k,p}} = (∑ ‖D^α u‖ₚᵖ)^(1/p)
            "Analysis.weak_derivative",           // weak derivative definition
            "Analysis.sobolev_embedding",         // W^{k,p} ↪ L^q for certain k,p,q
            "Analysis.sobolev_compact_embedding", // compact embedding theorem
            "Analysis.trace_theorem",             // trace operator on boundary
            "Analysis.poincare_inequality",       // ‖u‖ₚ ≤ C‖∇u‖ₚ on bounded domain
            "Analysis.rellich_kondrachov",        // compact embedding theorem
            // ================================================================
            // Semigroups of Operators
            // ================================================================
            "Analysis.ContinuousSemigroup", // T(t) : t ≥ 0, strongly continuous
            "Analysis.semigroup_composition", // T(s+t) = T(s)T(t)
            "Analysis.semigroup_identity",  // T(0) = I
            "Analysis.semigroup_continuity", // t ↦ T(t)x is continuous
            "Analysis.semigroup_generator", // A = lim_{t→0} (T(t) - I)/t
            "Analysis.hille_yosida",        // characterization of generators
            "Analysis.semigroup_exponential", // T(t) = e^{tA}
            "Analysis.lumer_phillips",      // dissipative operator generates
            // ================================================================
            // C*-Algebras
            // ================================================================
            "Analysis.CStarAlgebra",     // Banach *-algebra with ‖a*a‖ = ‖a‖²
            "Analysis.cstar_identity",   // ‖a*a‖ = ‖a‖² (C*-identity)
            "Analysis.cstar_involution", // a** = a, (ab)* = b*a*
            "Analysis.cstar_positive",   // a*a ≥ 0
            "Analysis.cstar_spectrum_real", // σ(a) ⊆ ℝ for self-adjoint a
            "Analysis.GelfandNaimark",   // commutative C* ≅ C₀(X)
            "Analysis.cstar_representation", // *-homomorphism to B(H)
            "Analysis.gns_construction", // GNS representation from state
            // ================================================================
            // Von Neumann Algebras
            // ================================================================
            "Analysis.VonNeumannAlgebra", // weak-operator closed *-subalgebra of B(H)
            "Analysis.von_neumann_bicommutant", // M = M'' (bicommutant theorem)
            "Analysis.von_neumann_predual", // predual M_*
            "Analysis.von_neumann_type",  // type I, II, III classification
            "Analysis.von_neumann_projection", // projections in von Neumann algebra
            "Analysis.von_neumann_trace", // trace on type II₁
            // ================================================================
            // Unbounded Operators
            // ================================================================
            "Analysis.UnboundedOperator", // densely defined operator
            "Analysis.UnboundedOperator.domain", // domain of operator
            "Analysis.UnboundedOperator.graph", // graph of operator
            "Analysis.UnboundedOperator.closed", // closed operator
            "Analysis.UnboundedOperator.closable", // closable operator
            "Analysis.UnboundedOperator.adjoint", // adjoint of unbounded operator
            "Analysis.UnboundedOperator.self_adjoint", // D(T) = D(T*), T = T*
            "Analysis.UnboundedOperator.essentially_self_adjoint", // closure is self-adjoint
            "Analysis.UnboundedOperator.spectrum", // spectrum of unbounded
            "Analysis.spectral_theorem_unbounded", // spectral theorem for unbounded
            // ================================================================
            // Fixed Point Theorems
            // ================================================================
            "Analysis.BanachFixedPoint", // contraction has unique fixed point
            "Analysis.contraction_def",  // d(Tx, Ty) ≤ k d(x, y), k < 1
            "Analysis.banach_fixed_point_unique", // uniqueness of fixed point
            "Analysis.banach_fixed_point_limit", // xₙ = Tⁿ x₀ → fixed point
            "Analysis.SchauderFixedPoint", // compact convex, continuous → fixed point
            "Analysis.LeraySchauder",    // degree theory variant
            // ================================================================
            // Weak Topologies
            // ================================================================
            "Analysis.WeakTopology",          // σ(E, E*) topology
            "Analysis.weak_convergence",      // xₙ ⇀ x if φ(xₙ) → φ(x)
            "Analysis.WeakStarTopology",      // σ(E*, E) topology
            "Analysis.weak_star_convergence", // φₙ ⇀* φ if φₙ(x) → φ(x)
            "Analysis.Banach_Alaoglu",        // closed unit ball of E* is weak-* compact
            "Analysis.Goldstine",             // unit ball of E weak-* dense in unit ball of E**
            "Analysis.Eberlein_Smulian",      // weak compactness = weak sequential compactness
            "Analysis.Mazur",                 // weak closure = norm closure for convex sets
            // ================================================================
            // Interpolation Theory
            // ================================================================
            "Analysis.Interpolation.compatible", // compatible Banach couple
            "Analysis.Interpolation.complex",    // complex interpolation [X₀, X₁]_θ
            "Analysis.Interpolation.real",       // real interpolation (X₀, X₁)_{θ,p}
            "Analysis.Riesz_Thorin",             // complex interpolation of operators
            "Analysis.Marcinkiewicz",            // real interpolation of operators
        ] {
            let name = Name::from_string(name);
            self.add_decl(Declaration::Axiom {
                name: name.clone(),
                level_params: vec![u.clone()],
                type_: type_u.clone(),
            })?;
        }

        self.functional_analysis_init = true;
        Ok(())
    }

    /// Check if FunctionalAnalysis has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.functional_analysis_init == true`
    pub(crate) fn has_functional_analysis(&self) -> bool {
        self.functional_analysis_init
    }
}
