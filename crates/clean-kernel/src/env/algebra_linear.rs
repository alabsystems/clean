// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Linear algebra structures for Environment
//!
//! This module contains linear algebra initialization:
//! - Module: R-modules over a ring R
//! - VectorSpace: modules over a field
//! - LinearMap: linear transformations
//! - Basis: free modules and basis theory
//! - Matrix: matrices and operations
//! - InnerProductSpace: inner products and norms
//! - Eigenvalue: eigenvalues and eigenvectors
//! - Decomposition: matrix decompositions (LU, QR, SVD)

use crate::env::{EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Algebra.LinearAlgebra module
    ///
    /// Linear algebra is fundamental for:
    /// - Numerical analysis and optimization
    /// - Physics and engineering applications
    /// - Machine learning and data science
    /// - Computer graphics and geometry
    ///
    /// This module provides axioms for:
    /// - Modules over rings and vector spaces over fields
    /// - Linear maps and their properties
    /// - Basis, dimension, and rank
    /// - Matrices and matrix operations
    /// - Inner product spaces
    /// - Eigenvalue theory
    /// - Matrix decompositions
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.algebra_linear_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_algebra_linear(&mut self) -> Result<(), EnvError> {
        if self.algebra_linear_init {
            return Ok(());
        }

        // Dependencies
        self.init_eq()?;
        self.init_nat()?;
        self.init_int()?;
        self.init_field()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        // Linear algebra constants
        self.add_init_axioms(
            &[
                // ================================================================
                // Module Theory (R-modules)
                // ================================================================
                "Algebra.LinearAlgebra.Module", // Module R M - R-module structure on M
                "Algebra.LinearAlgebra.smul",   // (•) : R → M → M scalar multiplication
                "Algebra.LinearAlgebra.smul_add", // r • (x + y) = r • x + r • y
                "Algebra.LinearAlgebra.add_smul", // (r + s) • x = r • x + s • x
                "Algebra.LinearAlgebra.mul_smul", // (r * s) • x = r • (s • x)
                "Algebra.LinearAlgebra.one_smul", // 1 • x = x
                "Algebra.LinearAlgebra.smul_zero", // r • 0 = 0
                "Algebra.LinearAlgebra.zero_smul", // 0 • x = 0
                "Algebra.LinearAlgebra.Submodule", // Submodule R M - submodule of M
                "Algebra.LinearAlgebra.submodule_add_closed", // x, y ∈ N → x + y ∈ N
                "Algebra.LinearAlgebra.submodule_smul_closed", // x ∈ N → r • x ∈ N
                "Algebra.LinearAlgebra.submodule_zero", // 0 ∈ N
                // ================================================================
                // Vector Spaces (modules over fields)
                // ================================================================
                "Algebra.LinearAlgebra.VectorSpace", // VectorSpace K V - K-vector space
                "Algebra.LinearAlgebra.vector_space_is_module", // VectorSpace → Module
                "Algebra.LinearAlgebra.trivial_subspace", // {0} is a subspace
                "Algebra.LinearAlgebra.whole_space", // V is a subspace of V
                "Algebra.LinearAlgebra.subspace_intersection", // intersection of subspaces
                "Algebra.LinearAlgebra.subspace_sum", // sum of subspaces
                // ================================================================
                // Linear Maps
                // ================================================================
                "Algebra.LinearAlgebra.LinearMap", // LinearMap R M N - R-linear M → N
                "Algebra.LinearAlgebra.linear_map_add", // f(x + y) = f(x) + f(y)
                "Algebra.LinearAlgebra.linear_map_smul", // f(r • x) = r • f(x)
                "Algebra.LinearAlgebra.linear_map_zero", // f(0) = 0
                "Algebra.LinearAlgebra.linear_map_comp", // composition of linear maps
                "Algebra.LinearAlgebra.linear_map_id", // identity linear map
                "Algebra.LinearAlgebra.ker",       // ker f = {x | f(x) = 0}
                "Algebra.LinearAlgebra.range",     // range f = {f(x) | x ∈ M}
                "Algebra.LinearAlgebra.ker_submodule", // ker f is a submodule
                "Algebra.LinearAlgebra.range_submodule", // range f is a submodule
                "Algebra.LinearAlgebra.injective_iff_ker_trivial", // injective ↔ ker = {0}
                // ================================================================
                // Linear Isomorphisms
                // ================================================================
                "Algebra.LinearAlgebra.LinearEquiv", // LinearEquiv R M N - linear isomorphism
                "Algebra.LinearAlgebra.linear_equiv_bijective", // linear equiv is bijective
                "Algebra.LinearAlgebra.linear_equiv_inverse", // inverse of linear equiv
                "Algebra.LinearAlgebra.linear_equiv_symm", // symmetry of linear equiv
                "Algebra.LinearAlgebra.linear_equiv_trans", // transitivity of linear equiv
                "Algebra.LinearAlgebra.linear_equiv_refl", // reflexivity of linear equiv
                // ================================================================
                // Span and Linear Independence
                // ================================================================
                "Algebra.LinearAlgebra.Span", // Span R S - submodule generated by S
                "Algebra.LinearAlgebra.span_mono", // S ⊆ T → Span S ⊆ Span T
                "Algebra.LinearAlgebra.span_union", // Span(S ∪ T) = Span S + Span T
                "Algebra.LinearAlgebra.LinearIndependent", // LinearIndependent R v
                "Algebra.LinearAlgebra.linear_independent_def", // Σᵢ rᵢvᵢ = 0 → all rᵢ = 0
                "Algebra.LinearAlgebra.linear_independent_empty", // empty set is lin indep
                "Algebra.LinearAlgebra.linear_independent_singleton", // {v} lin indep ↔ v ≠ 0
                "Algebra.LinearAlgebra.linear_dependent", // ¬LinearIndependent
                // ================================================================
                // Basis and Dimension
                // ================================================================
                "Algebra.LinearAlgebra.Basis", // Basis ι R M - indexed basis
                "Algebra.LinearAlgebra.basis_linear_independent", // basis is lin indep
                "Algebra.LinearAlgebra.basis_span", // span of basis is whole space
                "Algebra.LinearAlgebra.basis_unique_repr", // unique representation
                "Algebra.LinearAlgebra.coordinates", // coordinates w.r.t. basis
                "Algebra.LinearAlgebra.FiniteDimensional", // finite-dimensional space
                "Algebra.LinearAlgebra.dim",   // dimension of vector space
                "Algebra.LinearAlgebra.dim_eq_card_basis", // dim = cardinality of basis
                "Algebra.LinearAlgebra.basis_extension", // extend lin indep to basis
                "Algebra.LinearAlgebra.dim_subspace_le", // dim(W) ≤ dim(V) for W ⊆ V
                "Algebra.LinearAlgebra.rank_nullity", // dim(V) = dim(ker f) + dim(range f)
                // ================================================================
                // Quotient Modules
                // ================================================================
                "Algebra.LinearAlgebra.QuotientModule", // M / N quotient module
                "Algebra.LinearAlgebra.quotient_surjective", // projection is surjective
                "Algebra.LinearAlgebra.first_iso_theorem", // M / ker f ≅ range f
                // ================================================================
                // Direct Sums and Products
                // ================================================================
                "Algebra.LinearAlgebra.DirectSum", // ⨁ᵢ Mᵢ direct sum
                "Algebra.LinearAlgebra.internal_direct_sum", // M = N ⊕ P internal
                "Algebra.LinearAlgebra.direct_sum_universal", // universal property
                "Algebra.LinearAlgebra.product_module", // Πᵢ Mᵢ product module
                // ================================================================
                // Matrices
                // ================================================================
                "Algebra.LinearAlgebra.Matrix", // Matrix m n R - m×n matrix over R
                "Algebra.LinearAlgebra.matrix_add", // A + B matrix addition
                "Algebra.LinearAlgebra.matrix_smul", // r • A scalar multiplication
                "Algebra.LinearAlgebra.matrix_mul", // A * B matrix multiplication
                "Algebra.LinearAlgebra.matrix_transpose", // Aᵀ transpose
                "Algebra.LinearAlgebra.matrix_mul_assoc", // (AB)C = A(BC)
                "Algebra.LinearAlgebra.matrix_identity", // I identity matrix
                "Algebra.LinearAlgebra.matrix_mul_one", // A * I = A
                "Algebra.LinearAlgebra.one_mul_matrix", // I * A = A
                "Algebra.LinearAlgebra.matrix_to_linear_map", // matrix induces linear map
                "Algebra.LinearAlgebra.linear_map_to_matrix", // linear map gives matrix (w.r.t. basis)
                // ================================================================
                // Matrix Operations
                // ================================================================
                "Algebra.LinearAlgebra.trace",      // tr(A) = Σᵢ Aᵢᵢ
                "Algebra.LinearAlgebra.trace_add",  // tr(A + B) = tr(A) + tr(B)
                "Algebra.LinearAlgebra.trace_smul", // tr(rA) = r·tr(A)
                "Algebra.LinearAlgebra.trace_transpose", // tr(Aᵀ) = tr(A)
                "Algebra.LinearAlgebra.trace_mul_comm", // tr(AB) = tr(BA)
                "Algebra.LinearAlgebra.det",        // det(A) determinant
                "Algebra.LinearAlgebra.det_mul",    // det(AB) = det(A)·det(B)
                "Algebra.LinearAlgebra.det_transpose", // det(Aᵀ) = det(A)
                "Algebra.LinearAlgebra.det_identity", // det(I) = 1
                "Algebra.LinearAlgebra.det_zero_iff", // det(A) = 0 ↔ A singular
                "Algebra.LinearAlgebra.invertible_iff_det_ne_zero", // invertible ↔ det ≠ 0
                "Algebra.LinearAlgebra.matrix_inverse", // A⁻¹ when invertible
                "Algebra.LinearAlgebra.inverse_mul", // A⁻¹A = I
                "Algebra.LinearAlgebra.mul_inverse", // AA⁻¹ = I
                "Algebra.LinearAlgebra.inverse_unique", // inverse is unique
                // ================================================================
                // Matrix Rank
                // ================================================================
                "Algebra.LinearAlgebra.matrix_rank", // rank(A)
                "Algebra.LinearAlgebra.rank_eq_dim_range", // rank = dim(range)
                "Algebra.LinearAlgebra.rank_transpose", // rank(Aᵀ) = rank(A)
                "Algebra.LinearAlgebra.rank_mul_le", // rank(AB) ≤ min(rank A, rank B)
                "Algebra.LinearAlgebra.row_rank_eq_col_rank", // row rank = column rank
                // ================================================================
                // Inner Product Spaces
                // ================================================================
                "Algebra.LinearAlgebra.InnerProductSpace", // inner product space
                "Algebra.LinearAlgebra.inner",             // ⟨·,·⟩ : V × V → K
                "Algebra.LinearAlgebra.inner_add_left",    // ⟨x + y, z⟩ = ⟨x,z⟩ + ⟨y,z⟩
                "Algebra.LinearAlgebra.inner_smul_left",   // ⟨rx, y⟩ = r⟨x,y⟩
                "Algebra.LinearAlgebra.inner_conj_symm",   // ⟨y,x⟩ = conj⟨x,y⟩
                "Algebra.LinearAlgebra.inner_self_nonneg", // ⟨x,x⟩ ≥ 0
                "Algebra.LinearAlgebra.inner_self_eq_zero", // ⟨x,x⟩ = 0 ↔ x = 0
                "Algebra.LinearAlgebra.norm_sq",           // ‖x‖² = ⟨x,x⟩
                "Algebra.LinearAlgebra.cauchy_schwarz",    // |⟨x,y⟩|² ≤ ⟨x,x⟩⟨y,y⟩
                "Algebra.LinearAlgebra.triangle_inequality", // ‖x + y‖ ≤ ‖x‖ + ‖y‖
                // ================================================================
                // Orthogonality
                // ================================================================
                "Algebra.LinearAlgebra.orthogonal", // x ⊥ y ↔ ⟨x,y⟩ = 0
                "Algebra.LinearAlgebra.orthogonal_symm", // x ⊥ y ↔ y ⊥ x
                "Algebra.LinearAlgebra.orthogonal_zero", // x ⊥ 0 for all x
                "Algebra.LinearAlgebra.orthogonal_complement", // S⊥ orthogonal complement
                "Algebra.LinearAlgebra.orthogonal_complement_subspace", // S⊥ is subspace
                "Algebra.LinearAlgebra.double_orthogonal", // S ⊆ S⊥⊥
                "Algebra.LinearAlgebra.orthogonal_projection", // projection onto subspace
                "Algebra.LinearAlgebra.orthogonal_decomposition", // V = W ⊕ W⊥
                "Algebra.LinearAlgebra.GramSchmidt", // Gram-Schmidt orthogonalization
                "Algebra.LinearAlgebra.orthonormal", // orthonormal set
                "Algebra.LinearAlgebra.orthonormal_basis", // orthonormal basis exists
                // ================================================================
                // Eigenvalues and Eigenvectors
                // ================================================================
                "Algebra.LinearAlgebra.eigenvalue", // λ is eigenvalue of A
                "Algebra.LinearAlgebra.eigenvector", // v is eigenvector for λ
                "Algebra.LinearAlgebra.eigenspace", // eigenspace E_λ = ker(A - λI)
                "Algebra.LinearAlgebra.eigenspace_subspace", // eigenspace is subspace
                "Algebra.LinearAlgebra.eigenspaces_lin_indep", // distinct eigenspaces lin indep
                "Algebra.LinearAlgebra.char_poly",  // χ_A(λ) = det(λI - A)
                "Algebra.LinearAlgebra.eigenvalue_root_char_poly", // λ eigenvalue ↔ χ_A(λ) = 0
                "Algebra.LinearAlgebra.cayley_hamilton", // χ_A(A) = 0
                "Algebra.LinearAlgebra.spectral_radius", // ρ(A) = max|λ|
                // ================================================================
                // Diagonalization
                // ================================================================
                "Algebra.LinearAlgebra.Diagonalizable", // A is diagonalizable
                "Algebra.LinearAlgebra.diagonalizable_iff", // diagonalizable ↔ basis of eigenvectors
                "Algebra.LinearAlgebra.diagonal_form",      // A = PDP⁻¹
                "Algebra.LinearAlgebra.diagonal_matrix",    // D diagonal matrix
                // ================================================================
                // Symmetric and Hermitian Matrices
                // ================================================================
                "Algebra.LinearAlgebra.symmetric", // A = Aᵀ
                "Algebra.LinearAlgebra.hermitian", // A = A* (conjugate transpose)
                "Algebra.LinearAlgebra.symmetric_real_eigenvalues", // symmetric → real eigenvalues
                "Algebra.LinearAlgebra.symmetric_orthogonal_eigenvectors", // orthogonal eigenvectors
                "Algebra.LinearAlgebra.spectral_theorem", // symmetric → orthogonally diagonalizable
                "Algebra.LinearAlgebra.positive_definite", // x*Ax > 0 for x ≠ 0
                "Algebra.LinearAlgebra.positive_semidefinite", // x*Ax ≥ 0
                "Algebra.LinearAlgebra.positive_definite_eigenvalues", // PD ↔ all λ > 0
                // ================================================================
                // Matrix Decompositions
                // ================================================================
                "Algebra.LinearAlgebra.LU",        // A = LU decomposition
                "Algebra.LinearAlgebra.PLU",       // PA = LU with pivoting
                "Algebra.LinearAlgebra.QR",        // A = QR decomposition
                "Algebra.LinearAlgebra.qr_exists", // QR exists for full column rank
                "Algebra.LinearAlgebra.Cholesky",  // A = LLᵀ for positive definite
                "Algebra.LinearAlgebra.SVD",       // A = UΣVᵀ singular value decomposition
                "Algebra.LinearAlgebra.singular_value", // σ singular value
                "Algebra.LinearAlgebra.svd_exists", // SVD exists for all matrices
                "Algebra.LinearAlgebra.rank_eq_nonzero_singular", // rank = # nonzero σ
                "Algebra.LinearAlgebra.pseudoinverse", // A⁺ Moore-Penrose pseudoinverse
                "Algebra.LinearAlgebra.pseudoinverse_properties", // AA⁺A = A, etc.
                // ================================================================
                // Special Matrices
                // ================================================================
                "Algebra.LinearAlgebra.orthogonal_matrix", // Qᵀ Q = I
                "Algebra.LinearAlgebra.unitary_matrix",    // U* U = I
                "Algebra.LinearAlgebra.normal_matrix",     // AA* = A*A
                "Algebra.LinearAlgebra.nilpotent",         // Aᵏ = 0 for some k
                "Algebra.LinearAlgebra.idempotent",        // A² = A
                "Algebra.LinearAlgebra.projection_matrix", // projection = idempotent
                "Algebra.LinearAlgebra.permutation_matrix", // permutation matrix
                "Algebra.LinearAlgebra.stochastic_matrix", // rows sum to 1
                // ================================================================
                // Tensor Products
                // ================================================================
                "Algebra.LinearAlgebra.TensorProduct", // M ⊗ N tensor product
                "Algebra.LinearAlgebra.tensor_universal", // universal property
                "Algebra.LinearAlgebra.tensor_assoc",  // (M ⊗ N) ⊗ P ≅ M ⊗ (N ⊗ P)
                "Algebra.LinearAlgebra.tensor_comm",   // M ⊗ N ≅ N ⊗ M
                "Algebra.LinearAlgebra.tensor_unit",   // R ⊗ M ≅ M
                "Algebra.LinearAlgebra.tensor_sum",    // M ⊗ (N ⊕ P) ≅ (M ⊗ N) ⊕ (M ⊗ P)
                // ================================================================
                // Bilinear Forms
                // ================================================================
                "Algebra.LinearAlgebra.BilinearForm", // B : M × M → R bilinear
                "Algebra.LinearAlgebra.bilinear_left", // B(x + y, z) = B(x,z) + B(y,z)
                "Algebra.LinearAlgebra.bilinear_right", // B(x, y + z) = B(x,y) + B(x,z)
                "Algebra.LinearAlgebra.symmetric_bilinear", // B(x,y) = B(y,x)
                "Algebra.LinearAlgebra.alternating_bilinear", // B(x,x) = 0
                "Algebra.LinearAlgebra.nondegenerate", // B(x,·) = 0 → x = 0
                "Algebra.LinearAlgebra.bilinear_matrix", // matrix of bilinear form
                // ================================================================
                // Quadratic Forms
                // ================================================================
                "Algebra.LinearAlgebra.QuadraticForm", // Q : M → R with Q(rx) = r²Q(x)
                "Algebra.LinearAlgebra.associated_bilinear", // B(x,y) = (Q(x+y) - Q(x) - Q(y))/2
                "Algebra.LinearAlgebra.quadratic_from_bilinear", // Q(x) = B(x,x)
                "Algebra.LinearAlgebra.Signature",     // signature (p, q) of quadratic form
                "Algebra.LinearAlgebra.sylvester_law_of_inertia", // signature is invariant
                // ================================================================
                // Dual Spaces
                // ================================================================
                "Algebra.LinearAlgebra.Dual", // V* = V →ₗ K dual space
                "Algebra.LinearAlgebra.dual_basis", // dual basis
                "Algebra.LinearAlgebra.eval_dual_basis", // ε_i(e_j) = δ_ij
                "Algebra.LinearAlgebra.dim_dual", // dim(V*) = dim(V) (finite dim)
                "Algebra.LinearAlgebra.double_dual", // V** ≅ V (finite dim)
                "Algebra.LinearAlgebra.annihilator", // W° = {f ∈ V* | f|_W = 0}
                // ================================================================
                // Multilinear Algebra
                // ================================================================
                "Algebra.LinearAlgebra.MultilinearMap", // V^n →ₗ W
                "Algebra.LinearAlgebra.alternating_map", // antisymmetric multilinear
                "Algebra.LinearAlgebra.ExteriorPower",  // ⋀ⁿV exterior power
                "Algebra.LinearAlgebra.wedge_product",  // v ∧ w wedge product
                "Algebra.LinearAlgebra.wedge_antisymm", // v ∧ w = -w ∧ v
                "Algebra.LinearAlgebra.dim_exterior_power", // dim(⋀ⁿV) = C(dim V, n)
            ],
            std::slice::from_ref(&u),
            &type_u,
        )?;

        self.algebra_linear_init = true;
        Ok(())
    }

    /// Check if Algebra.LinearAlgebra has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.algebra_linear_init == true`
    #[allow(dead_code)] // Used by integration tests
    pub(crate) fn has_algebra_linear(&self) -> bool {
        self.algebra_linear_init
    }
}
