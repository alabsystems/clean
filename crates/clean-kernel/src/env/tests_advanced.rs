// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for advanced mathematical structures
//!
//! This module tests:
//! - Linear algebra (modules, vector spaces, linear maps, matrices)
//! - Category theory (categories, functors, natural transformations, adjunctions)
//! - Homological algebra (chain complexes, homology, derived categories)
//! - Number theory (primes, algebraic number theory, Galois theory)
//! - Algebraic geometry (varieties, schemes, sheaves)
//! - Representation theory (Lie groups, algebras, symmetric groups)
//! - Measure theory (measures, probability, integration)
//! - Functional analysis (Banach/Hilbert spaces, operators)
//! - Differential equations (ODEs, PDEs, dynamical systems)
//! - Combinatorics (graphs, matroids, enumeration)
//! - Optimization (convex, variational calculus, operations research)
//! - Computability (Turing machines, decidability, complexity theory)

use super::*;
#[test]
fn test_algebra_linear_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_algebra_linear());
    env.init_algebra_linear().unwrap();
    assert!(env.has_algebra_linear());
}

#[test]
fn test_algebra_linear_idempotent() {
    let mut env = Environment::new();
    env.init_algebra_linear().unwrap();
    env.init_algebra_linear().unwrap();
    assert!(env.has_algebra_linear());
}

#[test]
fn test_algebra_linear_module_theory_exist() {
    let mut env = Environment::new();
    env.init_algebra_linear().unwrap();

    let constants = vec![
        "Algebra.LinearAlgebra.Module",
        "Algebra.LinearAlgebra.smul",
        "Algebra.LinearAlgebra.smul_add",
        "Algebra.LinearAlgebra.add_smul",
        "Algebra.LinearAlgebra.mul_smul",
        "Algebra.LinearAlgebra.one_smul",
        "Algebra.LinearAlgebra.smul_zero",
        "Algebra.LinearAlgebra.zero_smul",
        "Algebra.LinearAlgebra.Submodule",
        "Algebra.LinearAlgebra.submodule_add_closed",
        "Algebra.LinearAlgebra.submodule_smul_closed",
        "Algebra.LinearAlgebra.submodule_zero",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_algebra_linear_vector_space_exist() {
    let mut env = Environment::new();
    env.init_algebra_linear().unwrap();

    let constants = vec![
        "Algebra.LinearAlgebra.VectorSpace",
        "Algebra.LinearAlgebra.vector_space_is_module",
        "Algebra.LinearAlgebra.trivial_subspace",
        "Algebra.LinearAlgebra.whole_space",
        "Algebra.LinearAlgebra.subspace_intersection",
        "Algebra.LinearAlgebra.subspace_sum",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_algebra_linear_linear_maps_exist() {
    let mut env = Environment::new();
    env.init_algebra_linear().unwrap();

    let constants = vec![
        "Algebra.LinearAlgebra.LinearMap",
        "Algebra.LinearAlgebra.linear_map_add",
        "Algebra.LinearAlgebra.linear_map_smul",
        "Algebra.LinearAlgebra.linear_map_zero",
        "Algebra.LinearAlgebra.linear_map_comp",
        "Algebra.LinearAlgebra.linear_map_id",
        "Algebra.LinearAlgebra.ker",
        "Algebra.LinearAlgebra.range",
        "Algebra.LinearAlgebra.ker_submodule",
        "Algebra.LinearAlgebra.range_submodule",
        "Algebra.LinearAlgebra.injective_iff_ker_trivial",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_algebra_linear_linear_equiv_exist() {
    let mut env = Environment::new();
    env.init_algebra_linear().unwrap();

    let constants = vec![
        "Algebra.LinearAlgebra.LinearEquiv",
        "Algebra.LinearAlgebra.linear_equiv_bijective",
        "Algebra.LinearAlgebra.linear_equiv_inverse",
        "Algebra.LinearAlgebra.linear_equiv_symm",
        "Algebra.LinearAlgebra.linear_equiv_trans",
        "Algebra.LinearAlgebra.linear_equiv_refl",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_algebra_linear_span_independence_exist() {
    let mut env = Environment::new();
    env.init_algebra_linear().unwrap();

    let constants = vec![
        "Algebra.LinearAlgebra.Span",
        "Algebra.LinearAlgebra.span_mono",
        "Algebra.LinearAlgebra.span_union",
        "Algebra.LinearAlgebra.LinearIndependent",
        "Algebra.LinearAlgebra.linear_independent_def",
        "Algebra.LinearAlgebra.linear_independent_empty",
        "Algebra.LinearAlgebra.linear_independent_singleton",
        "Algebra.LinearAlgebra.linear_dependent",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_algebra_linear_basis_dimension_exist() {
    let mut env = Environment::new();
    env.init_algebra_linear().unwrap();

    let constants = vec![
        "Algebra.LinearAlgebra.Basis",
        "Algebra.LinearAlgebra.basis_linear_independent",
        "Algebra.LinearAlgebra.basis_span",
        "Algebra.LinearAlgebra.basis_unique_repr",
        "Algebra.LinearAlgebra.coordinates",
        "Algebra.LinearAlgebra.FiniteDimensional",
        "Algebra.LinearAlgebra.dim",
        "Algebra.LinearAlgebra.dim_eq_card_basis",
        "Algebra.LinearAlgebra.basis_extension",
        "Algebra.LinearAlgebra.dim_subspace_le",
        "Algebra.LinearAlgebra.rank_nullity",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_algebra_linear_matrices_exist() {
    let mut env = Environment::new();
    env.init_algebra_linear().unwrap();

    let constants = vec![
        "Algebra.LinearAlgebra.Matrix",
        "Algebra.LinearAlgebra.matrix_add",
        "Algebra.LinearAlgebra.matrix_smul",
        "Algebra.LinearAlgebra.matrix_mul",
        "Algebra.LinearAlgebra.matrix_transpose",
        "Algebra.LinearAlgebra.matrix_mul_assoc",
        "Algebra.LinearAlgebra.matrix_identity",
        "Algebra.LinearAlgebra.matrix_mul_one",
        "Algebra.LinearAlgebra.one_mul_matrix",
        "Algebra.LinearAlgebra.matrix_to_linear_map",
        "Algebra.LinearAlgebra.linear_map_to_matrix",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_algebra_linear_matrix_operations_exist() {
    let mut env = Environment::new();
    env.init_algebra_linear().unwrap();

    let constants = vec![
        "Algebra.LinearAlgebra.trace",
        "Algebra.LinearAlgebra.trace_add",
        "Algebra.LinearAlgebra.trace_smul",
        "Algebra.LinearAlgebra.trace_transpose",
        "Algebra.LinearAlgebra.trace_mul_comm",
        "Algebra.LinearAlgebra.det",
        "Algebra.LinearAlgebra.det_mul",
        "Algebra.LinearAlgebra.det_transpose",
        "Algebra.LinearAlgebra.det_identity",
        "Algebra.LinearAlgebra.det_zero_iff",
        "Algebra.LinearAlgebra.invertible_iff_det_ne_zero",
        "Algebra.LinearAlgebra.matrix_inverse",
        "Algebra.LinearAlgebra.inverse_mul",
        "Algebra.LinearAlgebra.mul_inverse",
        "Algebra.LinearAlgebra.inverse_unique",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_algebra_linear_inner_product_exist() {
    let mut env = Environment::new();
    env.init_algebra_linear().unwrap();

    let constants = vec![
        "Algebra.LinearAlgebra.InnerProductSpace",
        "Algebra.LinearAlgebra.inner",
        "Algebra.LinearAlgebra.inner_add_left",
        "Algebra.LinearAlgebra.inner_smul_left",
        "Algebra.LinearAlgebra.inner_conj_symm",
        "Algebra.LinearAlgebra.inner_self_nonneg",
        "Algebra.LinearAlgebra.inner_self_eq_zero",
        "Algebra.LinearAlgebra.norm_sq",
        "Algebra.LinearAlgebra.cauchy_schwarz",
        "Algebra.LinearAlgebra.triangle_inequality",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_algebra_linear_orthogonality_exist() {
    let mut env = Environment::new();
    env.init_algebra_linear().unwrap();

    let constants = vec![
        "Algebra.LinearAlgebra.orthogonal",
        "Algebra.LinearAlgebra.orthogonal_symm",
        "Algebra.LinearAlgebra.orthogonal_zero",
        "Algebra.LinearAlgebra.orthogonal_complement",
        "Algebra.LinearAlgebra.orthogonal_complement_subspace",
        "Algebra.LinearAlgebra.double_orthogonal",
        "Algebra.LinearAlgebra.orthogonal_projection",
        "Algebra.LinearAlgebra.orthogonal_decomposition",
        "Algebra.LinearAlgebra.GramSchmidt",
        "Algebra.LinearAlgebra.orthonormal",
        "Algebra.LinearAlgebra.orthonormal_basis",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_algebra_linear_eigenvalue_exist() {
    let mut env = Environment::new();
    env.init_algebra_linear().unwrap();

    let constants = vec![
        "Algebra.LinearAlgebra.eigenvalue",
        "Algebra.LinearAlgebra.eigenvector",
        "Algebra.LinearAlgebra.eigenspace",
        "Algebra.LinearAlgebra.eigenspace_subspace",
        "Algebra.LinearAlgebra.eigenspaces_lin_indep",
        "Algebra.LinearAlgebra.char_poly",
        "Algebra.LinearAlgebra.eigenvalue_root_char_poly",
        "Algebra.LinearAlgebra.cayley_hamilton",
        "Algebra.LinearAlgebra.spectral_radius",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_algebra_linear_decompositions_exist() {
    let mut env = Environment::new();
    env.init_algebra_linear().unwrap();

    let constants = vec![
        "Algebra.LinearAlgebra.LU",
        "Algebra.LinearAlgebra.PLU",
        "Algebra.LinearAlgebra.QR",
        "Algebra.LinearAlgebra.qr_exists",
        "Algebra.LinearAlgebra.Cholesky",
        "Algebra.LinearAlgebra.SVD",
        "Algebra.LinearAlgebra.singular_value",
        "Algebra.LinearAlgebra.svd_exists",
        "Algebra.LinearAlgebra.rank_eq_nonzero_singular",
        "Algebra.LinearAlgebra.pseudoinverse",
        "Algebra.LinearAlgebra.pseudoinverse_properties",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_algebra_linear_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_algebra_linear().unwrap();

    assert!(env.has_eq());
    assert!(env.has_nat());
    assert!(env.has_int());
    assert!(env.has_field());
}

#[test]
fn test_algebra_linear_constant_count() {
    let mut env = Environment::new();
    let before = env.constants.len();
    env.init_algebra_linear().unwrap();
    let after = env.constants.len();

    // Module (12) + VectorSpace (6) + LinearMap (11) + LinearEquiv (6) +
    // Span/Independence (8) + Basis/Dim (11) + Quotient (3) + DirectSum (4) +
    // Matrix (11) + MatrixOps (15) + Rank (5) + InnerProduct (10) +
    // Orthogonal (11) + Eigenvalue (9) + Diagonalization (4) +
    // Symmetric (8) + Decompositions (11) + Special (8) +
    // Tensor (6) + Bilinear (7) + Quadratic (5) + Dual (6) + Multilinear (6)
    // = 183 constants for LinearAlgebra module itself
    let linear_algebra_count = after - before;
    assert!(
        linear_algebra_count >= 150,
        "Expected at least 150 linear algebra constants, got {linear_algebra_count}"
    );
}

// ============================================================================
// CategoryTheory tests
// ============================================================================

#[test]
fn test_category_theory_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_category_theory());
    env.init_category_theory().unwrap();
    assert!(env.has_category_theory());
}

#[test]
fn test_category_theory_idempotent() {
    let mut env = Environment::new();
    env.init_category_theory().unwrap();
    env.init_category_theory().unwrap();
    assert!(env.has_category_theory());
}

#[test]
fn test_category_theory_categories_exist() {
    let mut env = Environment::new();
    env.init_category_theory().unwrap();

    let constants = vec![
        "CategoryTheory.Category",
        "CategoryTheory.Hom",
        "CategoryTheory.id",
        "CategoryTheory.comp",
        "CategoryTheory.id_comp",
        "CategoryTheory.comp_id",
        "CategoryTheory.assoc",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_category_theory_morphism_properties_exist() {
    let mut env = Environment::new();
    env.init_category_theory().unwrap();

    let constants = vec![
        "CategoryTheory.Mono",
        "CategoryTheory.Epi",
        "CategoryTheory.Iso",
        "CategoryTheory.iso_inv",
        "CategoryTheory.iso_hom_inv",
        "CategoryTheory.iso_inv_hom",
        "CategoryTheory.Section",
        "CategoryTheory.Retraction",
        "CategoryTheory.SplitMono",
        "CategoryTheory.SplitEpi",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_category_theory_functors_exist() {
    let mut env = Environment::new();
    env.init_category_theory().unwrap();

    let constants = vec![
        "CategoryTheory.Functor",
        "CategoryTheory.Functor.obj",
        "CategoryTheory.Functor.map",
        "CategoryTheory.Functor.map_id",
        "CategoryTheory.Functor.map_comp",
        "CategoryTheory.Functor.comp",
        "CategoryTheory.Functor.id",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_category_theory_natural_transformations_exist() {
    let mut env = Environment::new();
    env.init_category_theory().unwrap();

    let constants = vec![
        "CategoryTheory.NatTrans",
        "CategoryTheory.NatTrans.app",
        "CategoryTheory.NatTrans.naturality",
        "CategoryTheory.NatTrans.id",
        "CategoryTheory.NatTrans.vcomp",
        "CategoryTheory.NatTrans.hcomp",
        "CategoryTheory.NatIso",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_category_theory_adjunctions_exist() {
    let mut env = Environment::new();
    env.init_category_theory().unwrap();

    let constants = vec![
        "CategoryTheory.Adjunction",
        "CategoryTheory.Adjunction.unit",
        "CategoryTheory.Adjunction.counit",
        "CategoryTheory.Adjunction.homEquiv",
        "CategoryTheory.triangle_left",
        "CategoryTheory.triangle_right",
        "CategoryTheory.adjoint_unique",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_category_theory_limits_exist() {
    let mut env = Environment::new();
    env.init_category_theory().unwrap();

    let constants = vec![
        "CategoryTheory.Cone",
        "CategoryTheory.Cone.pt",
        "CategoryTheory.Limit",
        "CategoryTheory.Limit.cone",
        "CategoryTheory.Limit.lift",
        "CategoryTheory.Limit.fac",
        "CategoryTheory.Limit.unique",
        "CategoryTheory.HasLimits",
        "CategoryTheory.HasFiniteLimits",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_category_theory_products_equalizers_exist() {
    let mut env = Environment::new();
    env.init_category_theory().unwrap();

    let constants = vec![
        "CategoryTheory.Product",
        "CategoryTheory.product_fst",
        "CategoryTheory.product_snd",
        "CategoryTheory.product_lift",
        "CategoryTheory.Equalizer",
        "CategoryTheory.equalizer_fork",
        "CategoryTheory.Pullback",
        "CategoryTheory.pullback_fst",
        "CategoryTheory.pullback_snd",
        "CategoryTheory.pullback_condition",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_category_theory_colimits_exist() {
    let mut env = Environment::new();
    env.init_category_theory().unwrap();

    let constants = vec![
        "CategoryTheory.Cocone",
        "CategoryTheory.Colimit",
        "CategoryTheory.Colimit.cocone",
        "CategoryTheory.Colimit.desc",
        "CategoryTheory.HasColimits",
        "CategoryTheory.HasFiniteColimits",
        "CategoryTheory.Coproduct",
        "CategoryTheory.coproduct_inl",
        "CategoryTheory.coproduct_inr",
        "CategoryTheory.coproduct_desc",
        "CategoryTheory.Coequalizer",
        "CategoryTheory.Pushout",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_category_theory_monads_exist() {
    let mut env = Environment::new();
    env.init_category_theory().unwrap();

    let constants = vec![
        "CategoryTheory.Monad",
        "CategoryTheory.Monad.T",
        "CategoryTheory.Monad.η",
        "CategoryTheory.Monad.μ",
        "CategoryTheory.Monad.assoc",
        "CategoryTheory.Monad.left_unit",
        "CategoryTheory.Monad.right_unit",
        "CategoryTheory.Monad.Algebra",
        "CategoryTheory.Kleisli",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_category_theory_yoneda_exist() {
    let mut env = Environment::new();
    env.init_category_theory().unwrap();

    let constants = vec![
        "CategoryTheory.yoneda",
        "CategoryTheory.yoneda_obj",
        "CategoryTheory.yoneda_map",
        "CategoryTheory.yoneda_faithful",
        "CategoryTheory.yoneda_full",
        "CategoryTheory.yoneda_lemma",
        "CategoryTheory.Representable",
        "CategoryTheory.representing_object",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_category_theory_abelian_exist() {
    let mut env = Environment::new();
    env.init_category_theory().unwrap();

    let constants = vec![
        "CategoryTheory.Preadditive",
        "CategoryTheory.Additive",
        "CategoryTheory.Abelian",
        "CategoryTheory.Kernel",
        "CategoryTheory.Cokernel",
        "CategoryTheory.Image",
        "CategoryTheory.Coimage",
        "CategoryTheory.Exact",
        "CategoryTheory.ShortExact",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_category_theory_examples_exist() {
    let mut env = Environment::new();
    env.init_category_theory().unwrap();

    let constants = vec![
        "CategoryTheory.TypeCat",
        "CategoryTheory.Grp",
        "CategoryTheory.Ring_",
        "CategoryTheory.Module_",
        "CategoryTheory.Top",
        "CategoryTheory.forget",
        "CategoryTheory.free",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_category_theory_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_category_theory().unwrap();

    assert!(env.has_eq());
    assert!(env.has_prod());
}

#[test]
fn test_category_theory_constant_count() {
    let mut env = Environment::new();
    let before = env.constants.len();
    env.init_category_theory().unwrap();
    let after = env.constants.len();

    // Categories (7) + Morphism Properties (10) + Special Objects (4) +
    // Functors (7) + Functor Properties (6) + Natural Transformations (7) +
    // Adjunctions (7) + Limits (9) + Products/Equalizers (10) +
    // Colimits (12) + Monads (9) + Comonads (5) + Yoneda (8) +
    // Presheaves (3) + Comma Categories (4) + Kan Extensions (4) +
    // Abelian (9) + Derived (5) + Enriched (3) + 2-Categories (5) +
    // Examples (7) = 141 constants for CategoryTheory module
    let category_theory_count = after - before;
    assert!(
        category_theory_count >= 100,
        "Expected at least 100 category theory constants, got {category_theory_count}"
    );
}

// ============================================================================
// HomologicalAlgebra Module Tests
// ============================================================================

#[test]
fn test_homological_algebra_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_homological_algebra());
    env.init_homological_algebra().unwrap();
    assert!(env.has_homological_algebra());
}

#[test]
fn test_homological_algebra_idempotent() {
    let mut env = Environment::new();
    env.init_homological_algebra().unwrap();
    env.init_homological_algebra().unwrap();
    assert!(env.has_homological_algebra());
}

#[test]
fn test_homological_algebra_chain_complexes_exist() {
    let mut env = Environment::new();
    env.init_homological_algebra().unwrap();

    let constants = vec![
        "HomologicalAlgebra.ChainComplex",
        "HomologicalAlgebra.CochainComplex",
        "HomologicalAlgebra.differential",
        "HomologicalAlgebra.d_squared_zero",
        "HomologicalAlgebra.ChainComplex.component",
        "HomologicalAlgebra.BoundedAbove",
        "HomologicalAlgebra.BoundedBelow",
        "HomologicalAlgebra.Bounded",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_homological_algebra_chain_maps_exist() {
    let mut env = Environment::new();
    env.init_homological_algebra().unwrap();

    let constants = vec![
        "HomologicalAlgebra.ChainMap",
        "HomologicalAlgebra.ChainMap.component",
        "HomologicalAlgebra.ChainMap.comm",
        "HomologicalAlgebra.ChainMap.id",
        "HomologicalAlgebra.ChainMap.comp",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_homological_algebra_homotopy_exist() {
    let mut env = Environment::new();
    env.init_homological_algebra().unwrap();

    let constants = vec![
        "HomologicalAlgebra.ChainHomotopy",
        "HomologicalAlgebra.homotopy_component",
        "HomologicalAlgebra.homotopy_formula",
        "HomologicalAlgebra.homotopy_equiv",
        "HomologicalAlgebra.HomotopyEquiv",
        "HomologicalAlgebra.null_homotopic",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_homological_algebra_homology_exist() {
    let mut env = Environment::new();
    env.init_homological_algebra().unwrap();

    let constants = vec![
        "HomologicalAlgebra.Cycles",
        "HomologicalAlgebra.Boundaries",
        "HomologicalAlgebra.Homology",
        "HomologicalAlgebra.homology_functor",
        "HomologicalAlgebra.induced_map",
        "HomologicalAlgebra.homotopy_invariance",
        "HomologicalAlgebra.Cocycles",
        "HomologicalAlgebra.Coboundaries",
        "HomologicalAlgebra.Cohomology",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_homological_algebra_exact_sequences_exist() {
    let mut env = Environment::new();
    env.init_homological_algebra().unwrap();

    let constants = vec![
        "HomologicalAlgebra.ShortExact",
        "HomologicalAlgebra.ses_inject",
        "HomologicalAlgebra.ses_surject",
        "HomologicalAlgebra.ses_exact",
        "HomologicalAlgebra.SplitShortExact",
        "HomologicalAlgebra.splitting_lemma",
        "HomologicalAlgebra.LongExactSequence",
        "HomologicalAlgebra.connecting_homomorphism",
        "HomologicalAlgebra.snake_lemma",
        "HomologicalAlgebra.les_exactness",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_homological_algebra_derived_category_exist() {
    let mut env = Environment::new();
    env.init_homological_algebra().unwrap();

    let constants = vec![
        "HomologicalAlgebra.QuasiIsomorphism",
        "HomologicalAlgebra.DerivedCategory",
        "HomologicalAlgebra.DboundedAbove",
        "HomologicalAlgebra.DboundedBelow",
        "HomologicalAlgebra.Dbounded",
        "HomologicalAlgebra.localization",
        "HomologicalAlgebra.roof",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_homological_algebra_triangulated_exist() {
    let mut env = Environment::new();
    env.init_homological_algebra().unwrap();

    let constants = vec![
        "HomologicalAlgebra.DistinguishedTriangle",
        "HomologicalAlgebra.shift",
        "HomologicalAlgebra.cone",
        "HomologicalAlgebra.cocone",
        "HomologicalAlgebra.triangle_rotation",
        "HomologicalAlgebra.octahedral_axiom",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_homological_algebra_ext_tor_exist() {
    let mut env = Environment::new();
    env.init_homological_algebra().unwrap();

    let constants = vec![
        "HomologicalAlgebra.Ext",
        "HomologicalAlgebra.Ext.zero",
        "HomologicalAlgebra.Ext.les",
        "HomologicalAlgebra.Ext.bifunctor",
        "HomologicalAlgebra.Tor",
        "HomologicalAlgebra.Tor.zero",
        "HomologicalAlgebra.Tor.les",
        "HomologicalAlgebra.Tor.symmetric",
        "HomologicalAlgebra.flat_module",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_homological_algebra_spectral_sequences_exist() {
    let mut env = Environment::new();
    env.init_homological_algebra().unwrap();

    let constants = vec![
        "HomologicalAlgebra.SpectralSequence",
        "HomologicalAlgebra.ss_page",
        "HomologicalAlgebra.ss_differential",
        "HomologicalAlgebra.ss_convergence",
        "HomologicalAlgebra.LeraySpectralSeq",
        "HomologicalAlgebra.GrothendieckSS",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_homological_algebra_group_cohomology_exist() {
    let mut env = Environment::new();
    env.init_homological_algebra().unwrap();

    let constants = vec![
        "HomologicalAlgebra.GroupCohomology",
        "HomologicalAlgebra.BarResolution",
        "HomologicalAlgebra.cocycle_group",
        "HomologicalAlgebra.group_extension",
        "HomologicalAlgebra.inflation",
        "HomologicalAlgebra.restriction",
        "HomologicalAlgebra.transfer",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_homological_algebra_hochschild_cyclic_exist() {
    let mut env = Environment::new();
    env.init_homological_algebra().unwrap();

    let constants = vec![
        "HomologicalAlgebra.HochschildHomology",
        "HomologicalAlgebra.HochschildCohomology",
        "HomologicalAlgebra.HochschildComplex",
        "HomologicalAlgebra.CyclicHomology",
        "HomologicalAlgebra.CyclicCohomology",
        "HomologicalAlgebra.ConnesOperator",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_homological_algebra_dg_ainfinity_exist() {
    let mut env = Environment::new();
    env.init_homological_algebra().unwrap();

    let constants = vec![
        "HomologicalAlgebra.DGCategory",
        "HomologicalAlgebra.DGFunctor",
        "HomologicalAlgebra.DGModule",
        "HomologicalAlgebra.AInfinityAlgebra",
        "HomologicalAlgebra.AInfinityMorphism",
        "HomologicalAlgebra.minimal_model",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_homological_algebra_duality_exist() {
    let mut env = Environment::new();
    env.init_homological_algebra().unwrap();

    let constants = vec![
        "HomologicalAlgebra.DualizingComplex",
        "HomologicalAlgebra.GrothendieckDuality",
        "HomologicalAlgebra.LocalDuality",
        "HomologicalAlgebra.VerdierDuality",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_homological_algebra_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_homological_algebra().unwrap();

    assert!(env.has_category_theory());
    assert!(env.has_algebra_linear());
}

#[test]
fn test_homological_algebra_constant_count() {
    let mut env = Environment::new();
    let before = env.constants.len();
    env.init_homological_algebra().unwrap();
    let after = env.constants.len();

    // Chain Complexes (8) + Chain Maps (5) + Chain Homotopy (6) +
    // Homology (6) + Cohomology (3) + Short Exact (6) + Long Exact (4) +
    // Quasi-iso (3) + Derived Category (6) + Triangulated (6) +
    // t-structures (7) + Resolutions (6) + Ext (6) + Tor (5) +
    // Dimension (5) + Spectral Sequences (6) + Standard SS (5) +
    // Double Complexes (5) + Derived Functors (5) + Koszul (4) +
    // Group Cohomology (7) + Lie Cohomology (4) + Hochschild (5) +
    // Cyclic (6) + DG/A-infinity (6) + Derived Advanced (6) +
    // Sheaf Cohomology (5) + Grothendieck Duality (4) +
    // Stability (5) = ~151 constants total, but some deps add more
    let homological_count = after - before;

    // With dependencies (category_theory adds 141, algebra_linear adds 185)
    // we expect the new constants plus dependencies
    assert!(
        homological_count >= 100,
        "Expected at least 100 new constants for homological algebra (including deps), got {homological_count}"
    );
}

// ============================================================================
// NumberTheory (Number Theory) tests
// ============================================================================

#[test]
fn test_number_theory_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_number_theory());
    env.init_number_theory().unwrap();
    assert!(env.has_number_theory());
}

#[test]
fn test_number_theory_idempotent() {
    let mut env = Environment::new();
    env.init_number_theory().unwrap();
    env.init_number_theory().unwrap();
    assert!(env.has_number_theory());
}

#[test]
fn test_number_theory_primes_constants_exist() {
    let mut env = Environment::new();
    env.init_number_theory().unwrap();

    let constants = vec![
        "NumberTheory.Prime",
        "NumberTheory.InfinitelyManyPrimes",
        "NumberTheory.PrimeNumberTheorem",
        "NumberTheory.PrimeCounting",
        "NumberTheory.RiemannHypothesis",
        "NumberTheory.GeneralizedRiemannHypothesis",
        "NumberTheory.TwinPrimeConjecture",
        "NumberTheory.GoldbachConjecture",
        "NumberTheory.GreenTao",
        "NumberTheory.BombieriVinogradov",
        "NumberTheory.SieveOfEratosthenes",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_number_theory_local_and_congruence_exist() {
    let mut env = Environment::new();
    env.init_number_theory().unwrap();

    let constants = vec![
        "NumberTheory.CongruentMod",
        "NumberTheory.ResidueClass",
        "NumberTheory.ChineseRemainder",
        "NumberTheory.HenselLemma",
        "NumberTheory.QuadraticReciprocity",
        "NumberTheory.LegendreSymbol",
        "NumberTheory.PAdicNumbers",
        "NumberTheory.PAdicIntegers",
        "NumberTheory.PAdicValuation",
        "NumberTheory.LocalField",
        "NumberTheory.Completion",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_number_theory_algebraic_number_theory_exist() {
    let mut env = Environment::new();
    env.init_number_theory().unwrap();

    let constants = vec![
        "NumberTheory.AlgebraicInteger",
        "NumberTheory.NumberField",
        "NumberTheory.RingOfIntegers",
        "NumberTheory.IntegralBasis",
        "NumberTheory.IdealFactorization",
        "NumberTheory.ClassGroup",
        "NumberTheory.ClassNumber",
        "NumberTheory.UnitGroup",
        "NumberTheory.DirichletUnitTheorem",
        "NumberTheory.MinkowskiBound",
        "NumberTheory.SUnitEquation",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_number_theory_ramification_and_class_field_exist() {
    let mut env = Environment::new();
    env.init_number_theory().unwrap();

    let constants = vec![
        "NumberTheory.DecompositionGroup",
        "NumberTheory.InertiaGroup",
        "NumberTheory.FrobeniusElement",
        "NumberTheory.RamificationIndex",
        "NumberTheory.TamelyRamified",
        "NumberTheory.WildlyRamified",
        "NumberTheory.ClassFieldTheory",
        "NumberTheory.ArtinMap",
        "NumberTheory.ChebotarevDensity",
        "NumberTheory.HasseNormTheorem",
        "NumberTheory.IdeleClassGroup",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_number_theory_galois_constants_exist() {
    let mut env = Environment::new();
    env.init_number_theory().unwrap();

    let constants = vec![
        "NumberTheory.GaloisExtension",
        "NumberTheory.GaloisGroup",
        "NumberTheory.SplittingField",
        "NumberTheory.FundamentalTheoremGalois",
        "NumberTheory.CyclotomicField",
        "NumberTheory.CyclotomicPolynomial",
        "NumberTheory.KroneckerWeber",
        "NumberTheory.KummerExtension",
        "NumberTheory.ArtinSchreier",
        "NumberTheory.ComplexMultiplication",
        "NumberTheory.GaloisRepresentation",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_number_theory_modular_forms_exist() {
    let mut env = Environment::new();
    env.init_number_theory().unwrap();

    let constants = vec![
        "NumberTheory.ModularForm",
        "NumberTheory.CuspForm",
        "NumberTheory.EisensteinSeries",
        "NumberTheory.HeckeOperator",
        "NumberTheory.HeckeEigenform",
        "NumberTheory.qExpansion",
        "NumberTheory.ModularCurve",
        "NumberTheory.X0N",
        "NumberTheory.ModularityTheorem",
        "NumberTheory.SerreConjecture",
        "NumberTheory.LanglandsCorrespondence",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_number_theory_elliptic_curves_exist() {
    let mut env = Environment::new();
    env.init_number_theory().unwrap();

    let constants = vec![
        "NumberTheory.EllipticCurve",
        "NumberTheory.WeierstrassModel",
        "NumberTheory.MinimalModel",
        "NumberTheory.Conductor",
        "NumberTheory.jInvariant",
        "NumberTheory.MordellWeilGroup",
        "NumberTheory.Rank",
        "NumberTheory.SelmerGroup",
        "NumberTheory.TateShafarevich",
        "NumberTheory.EllipticCurveLFunction",
        "NumberTheory.BSDConjecture",
        "NumberTheory.NeronModel",
        "NumberTheory.ReductionType",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_number_theory_diophantine_exist() {
    let mut env = Environment::new();
    env.init_number_theory().unwrap();

    let constants = vec![
        "NumberTheory.DiophantineEquation",
        "NumberTheory.FermatLastTheorem",
        "NumberTheory.CatalanMihailescu",
        "NumberTheory.PellEquation",
        "NumberTheory.MordellEquation",
        "NumberTheory.ThueEquation",
        "NumberTheory.FaltingsTheorem",
        "NumberTheory.MordellLang",
        "NumberTheory.HeightFunction",
        "NumberTheory.NorthcottProperty",
        "NumberTheory.ArakelovDivisor",
        "NumberTheory.ArithmeticScheme",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_number_theory_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_number_theory().unwrap();

    assert!(env.has_algebra_linear());
    assert!(env.has_category_theory());
    assert!(env.has_topology_scheme());
}

#[test]
fn test_number_theory_constant_count() {
    let mut env = Environment::new();
    let before = env.constants.len();
    env.init_number_theory().unwrap();
    let after = env.constants.len();

    // Expect a rich collection of number theory constants plus dependencies
    let number_theory_count = after - before;
    assert!(
        number_theory_count >= 120,
        "Expected at least 120 new constants for number theory (including deps), got {number_theory_count}"
    );
}

// ============================================================================
// AlgebraicGeometry Module Tests
// ============================================================================

#[test]
fn test_algebraic_geometry_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_algebraic_geometry());
    env.init_algebraic_geometry().unwrap();
    assert!(env.has_algebraic_geometry());
}

#[test]
fn test_algebraic_geometry_idempotent() {
    let mut env = Environment::new();
    env.init_algebraic_geometry().unwrap();
    env.init_algebraic_geometry().unwrap();
    assert!(env.has_algebraic_geometry());
}

#[test]
fn test_algebraic_geometry_affine_varieties_exist() {
    let mut env = Environment::new();
    env.init_algebraic_geometry().unwrap();

    let constants = vec![
        "AlgebraicGeometry.AffineVariety",
        "AlgebraicGeometry.AffineSpace",
        "AlgebraicGeometry.CoordinateRing",
        "AlgebraicGeometry.RadicalIdeal",
        "AlgebraicGeometry.ZeroLocus",
        "AlgebraicGeometry.Nullstellensatz",
        "AlgebraicGeometry.IrreducibleVariety",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_algebraic_geometry_projective_varieties_exist() {
    let mut env = Environment::new();
    env.init_algebraic_geometry().unwrap();

    let constants = vec![
        "AlgebraicGeometry.ProjectiveVariety",
        "AlgebraicGeometry.ProjectiveSpace",
        "AlgebraicGeometry.HomogeneousCoordinate",
        "AlgebraicGeometry.VeroneseEmbedding",
        "AlgebraicGeometry.SegreEmbedding",
        "AlgebraicGeometry.GrassmannVariety",
        "AlgebraicGeometry.FlagVariety",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_algebraic_geometry_schemes_exist() {
    let mut env = Environment::new();
    env.init_algebraic_geometry().unwrap();

    let constants = vec![
        "AlgebraicGeometry.Scheme",
        "AlgebraicGeometry.AffineScheme",
        "AlgebraicGeometry.StructureSheaf",
        "AlgebraicGeometry.LocalRing",
        "AlgebraicGeometry.GenericPoint",
        "AlgebraicGeometry.NoetherianScheme",
        "AlgebraicGeometry.ReducedScheme",
        "AlgebraicGeometry.IntegralScheme",
        "AlgebraicGeometry.NormalScheme",
        "AlgebraicGeometry.SmoothScheme",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_algebraic_geometry_morphisms_exist() {
    let mut env = Environment::new();
    env.init_algebraic_geometry().unwrap();

    let constants = vec![
        "AlgebraicGeometry.SchemeMorphism",
        "AlgebraicGeometry.ProperMorphism",
        "AlgebraicGeometry.FlatMorphism",
        "AlgebraicGeometry.SmoothMorphism",
        "AlgebraicGeometry.EtaleMorphism",
        "AlgebraicGeometry.SeparatedMorphism",
        "AlgebraicGeometry.FiniteMorphism",
        "AlgebraicGeometry.ProjectiveMorphism",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_algebraic_geometry_sheaves_exist() {
    let mut env = Environment::new();
    env.init_algebraic_geometry().unwrap();

    let constants = vec![
        "AlgebraicGeometry.Sheaf",
        "AlgebraicGeometry.QuasiCoherentSheaf",
        "AlgebraicGeometry.CoherentSheaf",
        "AlgebraicGeometry.LocallyFreeSheaf",
        "AlgebraicGeometry.VectorBundle",
        "AlgebraicGeometry.LineBundle",
        "AlgebraicGeometry.CanonicalBundle",
        "AlgebraicGeometry.PushforwardSheaf",
        "AlgebraicGeometry.PullbackSheaf",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_algebraic_geometry_divisors_exist() {
    let mut env = Environment::new();
    env.init_algebraic_geometry().unwrap();

    let constants = vec![
        "AlgebraicGeometry.WeilDivisor",
        "AlgebraicGeometry.CartierDivisor",
        "AlgebraicGeometry.PrincipalDivisor",
        "AlgebraicGeometry.EffectiveDivisor",
        "AlgebraicGeometry.DivisorClass",
        "AlgebraicGeometry.PicardGroup",
        "AlgebraicGeometry.NefDivisor",
        "AlgebraicGeometry.BigDivisor",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_algebraic_geometry_curves_exist() {
    let mut env = Environment::new();
    env.init_algebraic_geometry().unwrap();

    let constants = vec![
        "AlgebraicGeometry.Curve",
        "AlgebraicGeometry.SmoothCurve",
        "AlgebraicGeometry.Genus",
        "AlgebraicGeometry.RiemannRoch",
        "AlgebraicGeometry.Jacobian",
        "AlgebraicGeometry.AbelJacobiMap",
        "AlgebraicGeometry.AbelianVariety",
        "AlgebraicGeometry.ModuliCurve",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_algebraic_geometry_surfaces_exist() {
    let mut env = Environment::new();
    env.init_algebraic_geometry().unwrap();

    let constants = vec![
        "AlgebraicGeometry.Surface",
        "AlgebraicGeometry.MinimalModel",
        "AlgebraicGeometry.KodairaDimension",
        "AlgebraicGeometry.K3Surface",
        "AlgebraicGeometry.EnriquesSurface",
        "AlgebraicGeometry.RationalSurface",
        "AlgebraicGeometry.RuledSurface",
        "AlgebraicGeometry.NoetherFormula",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_algebraic_geometry_intersection_theory_exist() {
    let mut env = Environment::new();
    env.init_algebraic_geometry().unwrap();

    let constants = vec![
        "AlgebraicGeometry.IntersectionNumber",
        "AlgebraicGeometry.IntersectionProduct",
        "AlgebraicGeometry.ChowRing",
        "AlgebraicGeometry.ChowGroup",
        "AlgebraicGeometry.BezoutTheorem",
        "AlgebraicGeometry.ChernClass",
        "AlgebraicGeometry.ChernCharacter",
        "AlgebraicGeometry.ToddClass",
        "AlgebraicGeometry.GRR",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_algebraic_geometry_cohomology_exist() {
    let mut env = Environment::new();
    env.init_algebraic_geometry().unwrap();

    let constants = vec![
        "AlgebraicGeometry.SheafCohomology",
        "AlgebraicGeometry.CechCohomology",
        "AlgebraicGeometry.SheafExt",
        "AlgebraicGeometry.KodairaVanishing",
        "AlgebraicGeometry.SerreVanishing",
        "AlgebraicGeometry.SerreDuality",
        "AlgebraicGeometry.GrothendieckDuality",
        "AlgebraicGeometry.EtaleCohomology",
        "AlgebraicGeometry.LadicCohomology",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_algebraic_geometry_birational_exist() {
    let mut env = Environment::new();
    env.init_algebraic_geometry().unwrap();

    let constants = vec![
        "AlgebraicGeometry.Blowup",
        "AlgebraicGeometry.ExceptionalDivisor",
        "AlgebraicGeometry.Resolution",
        "AlgebraicGeometry.Hironaka",
        "AlgebraicGeometry.MinimalModelProgram",
        "AlgebraicGeometry.Flip",
        "AlgebraicGeometry.Flop",
        "AlgebraicGeometry.MoriCone",
        "AlgebraicGeometry.NefCone",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_algebraic_geometry_moduli_exist() {
    let mut env = Environment::new();
    env.init_algebraic_geometry().unwrap();

    let constants = vec![
        "AlgebraicGeometry.ModuliSpace",
        "AlgebraicGeometry.ModuliFunctor",
        "AlgebraicGeometry.HilbertScheme",
        "AlgebraicGeometry.QuotScheme",
        "AlgebraicGeometry.GeometricInvariantTheory",
        "AlgebraicGeometry.Stability",
        "AlgebraicGeometry.GITQuotient",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_algebraic_geometry_stacks_exist() {
    let mut env = Environment::new();
    env.init_algebraic_geometry().unwrap();

    let constants = vec![
        "AlgebraicGeometry.AlgebraicStack",
        "AlgebraicGeometry.DeligneMumfordStack",
        "AlgebraicGeometry.ArtinStack",
        "AlgebraicGeometry.Gerbe",
        "AlgebraicGeometry.QuotientStack",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_algebraic_geometry_toric_exist() {
    let mut env = Environment::new();
    env.init_algebraic_geometry().unwrap();

    let constants = vec![
        "AlgebraicGeometry.ToricVariety",
        "AlgebraicGeometry.Fan",
        "AlgebraicGeometry.Cone",
        "AlgebraicGeometry.Polytope",
        "AlgebraicGeometry.TorusDivisor",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_algebraic_geometry_special_varieties_exist() {
    let mut env = Environment::new();
    env.init_algebraic_geometry().unwrap();

    let constants = vec![
        "AlgebraicGeometry.CalabiYau",
        "AlgebraicGeometry.FanoVariety",
        "AlgebraicGeometry.RationalVariety",
        "AlgebraicGeometry.HyperkahlerVariety",
        "AlgebraicGeometry.WeilConjectures",
        "AlgebraicGeometry.ZetaFunction",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Constant {name} should exist"
        );
    }
}

#[test]
fn test_algebraic_geometry_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_algebraic_geometry().unwrap();

    // AlgebraicGeometry depends on CategoryTheory, HomologicalAlgebra, TopologyScheme
    assert!(env.has_category_theory());
    assert!(env.has_homological_algebra());
    assert!(env.has_topology_scheme());
}

#[test]
fn test_algebraic_geometry_constant_count() {
    let mut env = Environment::new();
    let before = env.constants.len();
    env.init_algebraic_geometry().unwrap();
    let after = env.constants.len();

    // Expect a rich collection of algebraic geometry constants plus dependencies
    let algebraic_geometry_count = after - before;
    assert!(
        algebraic_geometry_count >= 200,
        "Expected at least 200 new constants for algebraic geometry (including deps), got {algebraic_geometry_count}"
    );
}

// ============================================================================
// Representation Theory Tests
// ============================================================================

#[test]
fn test_representation_theory_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_representation_theory());
    env.init_representation_theory().unwrap();
    assert!(env.has_representation_theory());
}

#[test]
fn test_representation_theory_idempotent() {
    let mut env = Environment::new();
    env.init_representation_theory().unwrap();
    env.init_representation_theory().unwrap();
    assert!(env.has_representation_theory());
}

#[test]
fn test_representation_theory_lie_groups_exist() {
    let mut env = Environment::new();
    env.init_representation_theory().unwrap();

    // Basic Lie group structure
    let lie_groups = [
        "RepresentationTheory.LieGroup",
        "RepresentationTheory.LieGroup.mul",
        "RepresentationTheory.LieGroup.inv",
        "RepresentationTheory.LieGroup.one",
        "RepresentationTheory.LieSubgroup",
        "RepresentationTheory.ConnectedComponent",
        "RepresentationTheory.CoveringGroup",
    ];
    for name in &lie_groups {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing Lie group constant: {name}"
        );
    }
}

#[test]
fn test_representation_theory_classical_groups_exist() {
    let mut env = Environment::new();
    env.init_representation_theory().unwrap();

    // Classical Lie groups
    let classical_groups = [
        "RepresentationTheory.GL",
        "RepresentationTheory.SL",
        "RepresentationTheory.O",
        "RepresentationTheory.SO",
        "RepresentationTheory.U",
        "RepresentationTheory.SU",
        "RepresentationTheory.Sp",
        "RepresentationTheory.Spin",
        "RepresentationTheory.Pin",
    ];
    for name in &classical_groups {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing classical group: {name}"
        );
    }
}

#[test]
fn test_representation_theory_exceptional_groups_exist() {
    let mut env = Environment::new();
    env.init_representation_theory().unwrap();

    // Exceptional Lie groups
    let exceptional = [
        "RepresentationTheory.G2",
        "RepresentationTheory.F4",
        "RepresentationTheory.E6",
        "RepresentationTheory.E7",
        "RepresentationTheory.E8",
    ];
    for name in &exceptional {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing exceptional group: {name}"
        );
    }
}

#[test]
fn test_representation_theory_lie_algebras_exist() {
    let mut env = Environment::new();
    env.init_representation_theory().unwrap();

    // Lie algebra basics
    let lie_algebras = [
        "RepresentationTheory.LieAlgebra",
        "RepresentationTheory.LieBracket",
        "RepresentationTheory.bracket_antisymm",
        "RepresentationTheory.jacobi",
        "RepresentationTheory.LieSubalgebra",
        "RepresentationTheory.LieIdeal",
        "RepresentationTheory.Center",
        "RepresentationTheory.Derived",
        "RepresentationTheory.ad",
    ];
    for name in &lie_algebras {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing Lie algebra constant: {name}"
        );
    }
}

#[test]
fn test_representation_theory_classical_algebras_exist() {
    let mut env = Environment::new();
    env.init_representation_theory().unwrap();

    // Classical Lie algebras
    let classical_algebras = [
        "RepresentationTheory.gl",
        "RepresentationTheory.sl",
        "RepresentationTheory.so",
        "RepresentationTheory.sp",
        "RepresentationTheory.su",
    ];
    for name in &classical_algebras {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing classical Lie algebra: {name}"
        );
    }
}

#[test]
fn test_representation_theory_structure_theory_exist() {
    let mut env = Environment::new();
    env.init_representation_theory().unwrap();

    // Structure theory
    let structure_theory = [
        "RepresentationTheory.Solvable",
        "RepresentationTheory.Nilpotent",
        "RepresentationTheory.Semisimple",
        "RepresentationTheory.Simple",
        "RepresentationTheory.Reductive",
        "RepresentationTheory.RadicalLA",
        "RepresentationTheory.LeviDecomposition",
    ];
    for name in &structure_theory {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing structure theory constant: {name}"
        );
    }
}

#[test]
fn test_representation_theory_root_systems_exist() {
    let mut env = Environment::new();
    env.init_representation_theory().unwrap();

    // Root systems
    let root_systems = [
        "RepresentationTheory.CartanSubalgebra",
        "RepresentationTheory.RootSystem",
        "RepresentationTheory.Root",
        "RepresentationTheory.SimpleRoot",
        "RepresentationTheory.PositiveRoot",
        "RepresentationTheory.RootSpace",
        "RepresentationTheory.Coroot",
        "RepresentationTheory.CartanMatrix",
        "RepresentationTheory.DynkinDiagram",
        "RepresentationTheory.Rank",
    ];
    for name in &root_systems {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing root system constant: {name}"
        );
    }
}

#[test]
fn test_representation_theory_weyl_groups_exist() {
    let mut env = Environment::new();
    env.init_representation_theory().unwrap();

    // Weyl groups
    let weyl = [
        "RepresentationTheory.WeylGroup",
        "RepresentationTheory.SimpleReflection",
        "RepresentationTheory.WeylElement",
        "RepresentationTheory.WeylLength",
        "RepresentationTheory.LongestElement",
        "RepresentationTheory.WeylChamber",
        "RepresentationTheory.BruhatOrder",
    ];
    for name in &weyl {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing Weyl group constant: {name}"
        );
    }
}

#[test]
fn test_representation_theory_representations_exist() {
    let mut env = Environment::new();
    env.init_representation_theory().unwrap();

    // Representations
    let reps = [
        "RepresentationTheory.Representation",
        "RepresentationTheory.Rep.vector_space",
        "RepresentationTheory.Rep.action",
        "RepresentationTheory.LieAlgebraRep",
        "RepresentationTheory.Irreducible",
        "RepresentationTheory.CompletelyReducible",
        "RepresentationTheory.Faithful",
        "RepresentationTheory.Unitary",
    ];
    for name in &reps {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing representation constant: {name}"
        );
    }
}

#[test]
fn test_representation_theory_operations_exist() {
    let mut env = Environment::new();
    env.init_representation_theory().unwrap();

    // Rep operations
    let ops = [
        "RepresentationTheory.DirectSum",
        "RepresentationTheory.TensorProduct",
        "RepresentationTheory.DualRep",
        "RepresentationTheory.Hom",
        "RepresentationTheory.ExteriorPower",
        "RepresentationTheory.SymmetricPower",
        "RepresentationTheory.Restriction",
        "RepresentationTheory.Induction",
    ];
    for name in &ops {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing rep operation: {name}"
        );
    }
}

#[test]
fn test_representation_theory_characters_exist() {
    let mut env = Environment::new();
    env.init_representation_theory().unwrap();

    // Characters
    let characters = [
        "RepresentationTheory.Character",
        "RepresentationTheory.char_class_fn",
        "RepresentationTheory.char_sum",
        "RepresentationTheory.char_tensor",
        "RepresentationTheory.SchurOrthogonality",
        "RepresentationTheory.IrreducibleCharacter",
        "RepresentationTheory.CharacterTable",
        "RepresentationTheory.InnerProduct",
    ];
    for name in &characters {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing character constant: {name}"
        );
    }
}

#[test]
fn test_representation_theory_schur_exist() {
    let mut env = Environment::new();
    env.init_representation_theory().unwrap();

    // Schur's lemma and decomposition
    let schur = [
        "RepresentationTheory.SchurLemma",
        "RepresentationTheory.schur_simple",
        "RepresentationTheory.Maschke",
        "RepresentationTheory.IsotypicComponent",
        "RepresentationTheory.Multiplicity",
        "RepresentationTheory.Decomposition",
    ];
    for name in &schur {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing Schur constant: {name}"
        );
    }
}

#[test]
fn test_representation_theory_weights_exist() {
    let mut env = Environment::new();
    env.init_representation_theory().unwrap();

    // Weight theory
    let weights = [
        "RepresentationTheory.Weight",
        "RepresentationTheory.WeightSpace",
        "RepresentationTheory.WeightMultiplicity",
        "RepresentationTheory.DominantWeight",
        "RepresentationTheory.IntegralWeight",
        "RepresentationTheory.HighestWeight",
        "RepresentationTheory.HighestWeightVector",
        "RepresentationTheory.FundamentalWeight",
        "RepresentationTheory.WeylCharacterFormula",
    ];
    for name in &weights {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing weight constant: {name}"
        );
    }
}

#[test]
fn test_representation_theory_verma_modules_exist() {
    let mut env = Environment::new();
    env.init_representation_theory().unwrap();

    // Highest weight modules
    let verma = [
        "RepresentationTheory.VermaModule",
        "RepresentationTheory.HighestWeightModule",
        "RepresentationTheory.BGGCategory",
        "RepresentationTheory.BGGResolution",
        "RepresentationTheory.DualVerma",
    ];
    for name in &verma {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing Verma module constant: {name}"
        );
    }
}

#[test]
fn test_representation_theory_symmetric_groups_exist() {
    let mut env = Environment::new();
    env.init_representation_theory().unwrap();

    // Symmetric groups
    let symmetric = [
        "RepresentationTheory.SymmetricGroup",
        "RepresentationTheory.Permutation",
        "RepresentationTheory.Cycle",
        "RepresentationTheory.Transposition",
        "RepresentationTheory.CycleType",
        "RepresentationTheory.Sign",
        "RepresentationTheory.AlternatingGroup",
        "RepresentationTheory.ConjugacyClass",
    ];
    for name in &symmetric {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing symmetric group constant: {name}"
        );
    }
}

#[test]
fn test_representation_theory_partitions_exist() {
    let mut env = Environment::new();
    env.init_representation_theory().unwrap();

    // Partitions and Young diagrams
    let partitions = [
        "RepresentationTheory.Partition",
        "RepresentationTheory.YoungDiagram",
        "RepresentationTheory.Hook",
        "RepresentationTheory.HookLength",
        "RepresentationTheory.Content",
        "RepresentationTheory.ConjugatePartition",
        "RepresentationTheory.DominanceOrder",
    ];
    for name in &partitions {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing partition constant: {name}"
        );
    }
}

#[test]
fn test_representation_theory_young_tableaux_exist() {
    let mut env = Environment::new();
    env.init_representation_theory().unwrap();

    // Young tableaux
    let tableaux = [
        "RepresentationTheory.YoungTableau",
        "RepresentationTheory.StandardTableau",
        "RepresentationTheory.SemiStandardTableau",
        "RepresentationTheory.RobinsonSchensted",
        "RepresentationTheory.RSK",
        "RepresentationTheory.JeuDeTaquin",
    ];
    for name in &tableaux {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing Young tableau constant: {name}"
        );
    }
}

#[test]
fn test_representation_theory_specht_modules_exist() {
    let mut env = Environment::new();
    env.init_representation_theory().unwrap();

    // Specht modules
    let specht = [
        "RepresentationTheory.SpchtModule",
        "RepresentationTheory.Polytabloid",
        "RepresentationTheory.StandardBasis",
        "RepresentationTheory.YoungSymmetrizer",
        "RepresentationTheory.HookLengthFormula",
        "RepresentationTheory.BranchingRule",
    ];
    for name in &specht {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing Specht module constant: {name}"
        );
    }
}

#[test]
fn test_representation_theory_schur_weyl_exist() {
    let mut env = Environment::new();
    env.init_representation_theory().unwrap();

    // Schur-Weyl duality
    let schur_weyl = [
        "RepresentationTheory.SchurWeylDuality",
        "RepresentationTheory.SchurFunctor",
        "RepresentationTheory.WeylModule",
        "RepresentationTheory.SchurModule",
    ];
    for name in &schur_weyl {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing Schur-Weyl constant: {name}"
        );
    }
}

#[test]
fn test_representation_theory_symmetric_functions_exist() {
    let mut env = Environment::new();
    env.init_representation_theory().unwrap();

    // Symmetric functions
    let sym_funcs = [
        "RepresentationTheory.SymmetricFunction",
        "RepresentationTheory.ElementarySymmetric",
        "RepresentationTheory.PowerSum",
        "RepresentationTheory.CompleteHomogeneous",
        "RepresentationTheory.SchurFunction",
        "RepresentationTheory.FrobeniusCharacteristic",
        "RepresentationTheory.LittlewoodRichardson",
    ];
    for name in &sym_funcs {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing symmetric function constant: {name}"
        );
    }
}

#[test]
fn test_representation_theory_coxeter_exist() {
    let mut env = Environment::new();
    env.init_representation_theory().unwrap();

    // Coxeter groups
    let coxeter = [
        "RepresentationTheory.CoxeterGroup",
        "RepresentationTheory.CoxeterSystem",
        "RepresentationTheory.CoxeterMatrix",
        "RepresentationTheory.CoxeterGraph",
        "RepresentationTheory.Reflection",
    ];
    for name in &coxeter {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing Coxeter constant: {name}"
        );
    }
}

#[test]
fn test_representation_theory_hecke_exist() {
    let mut env = Environment::new();
    env.init_representation_theory().unwrap();

    // Hecke algebras
    let hecke = [
        "RepresentationTheory.HeckeAlgebra",
        "RepresentationTheory.HeckeGenerator",
        "RepresentationTheory.HeckeRelation",
        "RepresentationTheory.KazhdanLusztig",
        "RepresentationTheory.KLPolynomial",
    ];
    for name in &hecke {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing Hecke algebra constant: {name}"
        );
    }
}

#[test]
fn test_representation_theory_quantum_groups_exist() {
    let mut env = Environment::new();
    env.init_representation_theory().unwrap();

    // Quantum groups
    let quantum = [
        "RepresentationTheory.QuantumGroup",
        "RepresentationTheory.Uq",
        "RepresentationTheory.QParameter",
        "RepresentationTheory.Coproduct",
        "RepresentationTheory.Antipode",
        "RepresentationTheory.RMatrix",
        "RepresentationTheory.YangBaxter",
    ];
    for name in &quantum {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing quantum group constant: {name}"
        );
    }
}

#[test]
fn test_representation_theory_affine_exist() {
    let mut env = Environment::new();
    env.init_representation_theory().unwrap();

    // Affine Lie algebras
    let affine = [
        "RepresentationTheory.AffineLA",
        "RepresentationTheory.Loop",
        "RepresentationTheory.CentralExtension",
        "RepresentationTheory.AffineRoot",
        "RepresentationTheory.AffineWeyl",
        "RepresentationTheory.IntegrableRep",
        "RepresentationTheory.Level",
    ];
    for name in &affine {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing affine constant: {name}"
        );
    }
}

#[test]
fn test_representation_theory_vertex_algebras_exist() {
    let mut env = Environment::new();
    env.init_representation_theory().unwrap();

    // Vertex algebras
    let vertex = [
        "RepresentationTheory.VertexAlgebra",
        "RepresentationTheory.VertexOperator",
        "RepresentationTheory.OPE",
        "RepresentationTheory.Conformal",
        "RepresentationTheory.VirasoroAlgebra",
        "RepresentationTheory.HeisenbergAlgebra",
    ];
    for name in &vertex {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing vertex algebra constant: {name}"
        );
    }
}

#[test]
fn test_representation_theory_physics_exist() {
    let mut env = Environment::new();
    env.init_representation_theory().unwrap();

    // Physics applications
    let physics = [
        "RepresentationTheory.SpinRep",
        "RepresentationTheory.SpinorSpace",
        "RepresentationTheory.CliffordAlgebra",
        "RepresentationTheory.DiracSpinor",
        "RepresentationTheory.WeylSpinor",
        "RepresentationTheory.LorentzGroup",
        "RepresentationTheory.PoincareGroup",
        "RepresentationTheory.WignerClassification",
    ];
    for name in &physics {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing physics constant: {name}"
        );
    }
}

#[test]
fn test_representation_theory_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_representation_theory().unwrap();

    // Check that dependencies are initialized
    assert!(env.has_eq());
    assert!(env.has_prod());
    assert!(env.has_category_theory());
}

#[test]
fn test_representation_theory_constant_count() {
    let mut env = Environment::new();
    let before = env.constants.len();
    env.init_representation_theory().unwrap();
    let after = env.constants.len();

    // Expect a rich collection of representation theory constants plus dependencies
    let rep_theory_count = after - before;
    assert!(
        rep_theory_count >= 200,
        "Expected at least 200 new constants for representation theory (including deps), got {rep_theory_count}"
    );
}

// ============================================================================
// MeasureTheory Tests
// ============================================================================

#[test]
fn test_measure_theory_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_measure_theory());
    env.init_measure_theory().unwrap();
    assert!(env.has_measure_theory());
}

#[test]
fn test_measure_theory_idempotent() {
    let mut env = Environment::new();
    env.init_measure_theory().unwrap();
    env.init_measure_theory().unwrap();
    assert!(env.has_measure_theory());
}

#[test]
fn test_measure_theory_sigma_algebras_exist() {
    let mut env = Environment::new();
    env.init_measure_theory().unwrap();

    let sigma_algebra_names = [
        "MeasureTheory.MeasurableSpace",
        "MeasureTheory.MeasurableSet",
        "MeasureTheory.measurable_empty",
        "MeasureTheory.measurable_univ",
        "MeasureTheory.measurable_compl",
        "MeasureTheory.measurable_union",
        "MeasureTheory.measurable_inter",
        "MeasureTheory.generateMeasurable",
        "MeasureTheory.BorelSpace",
        "MeasureTheory.borel",
    ];

    for name in &sigma_algebra_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing sigma-algebra constant: {name}"
        );
    }
}

#[test]
fn test_measure_theory_measurable_functions_exist() {
    let mut env = Environment::new();
    env.init_measure_theory().unwrap();

    let measurable_fn_names = [
        "MeasureTheory.Measurable",
        "MeasureTheory.measurable_id",
        "MeasureTheory.measurable_const",
        "MeasureTheory.measurable_comp",
        "MeasureTheory.StronglyMeasurable",
        "MeasureTheory.AEMeasurable",
        "MeasureTheory.MeasurableEquiv",
    ];

    for name in &measurable_fn_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing measurable function constant: {name}"
        );
    }
}

#[test]
fn test_measure_theory_measures_exist() {
    let mut env = Environment::new();
    env.init_measure_theory().unwrap();

    let measure_names = [
        "MeasureTheory.Measure",
        "MeasureTheory.measure_empty",
        "MeasureTheory.measure_mono",
        "MeasureTheory.measure_countable_union",
        "MeasureTheory.OuterMeasure",
        "MeasureTheory.FiniteMeasure",
        "MeasureTheory.ProbabilityMeasure",
        "MeasureTheory.SigmaFinite",
        "MeasureTheory.counting",
        "MeasureTheory.dirac",
    ];

    for name in &measure_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing measure constant: {name}"
        );
    }
}

#[test]
fn test_measure_theory_lebesgue_measure_exist() {
    let mut env = Environment::new();
    env.init_measure_theory().unwrap();

    let lebesgue_names = [
        "MeasureTheory.LebesgueMeasure",
        "MeasureTheory.lebesgue_interval",
        "MeasureTheory.lebesgue_translation",
        "MeasureTheory.lebesgue_scaling",
        "MeasureTheory.lebesgue_borel",
        "MeasureTheory.lebesgue_complete",
        "MeasureTheory.lebesgue_regular",
    ];

    for name in &lebesgue_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing Lebesgue measure constant: {name}"
        );
    }
}

#[test]
fn test_measure_theory_null_sets_exist() {
    let mut env = Environment::new();
    env.init_measure_theory().unwrap();

    let null_names = [
        "MeasureTheory.NullSet",
        "MeasureTheory.NullMeasurableSet",
        "MeasureTheory.ae",
        "MeasureTheory.ae_eq",
        "MeasureTheory.ae_le",
        "MeasureTheory.ae_of_all",
    ];

    for name in &null_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing null set constant: {name}"
        );
    }
}

#[test]
fn test_measure_theory_simple_functions_exist() {
    let mut env = Environment::new();
    env.init_measure_theory().unwrap();

    let simple_names = [
        "MeasureTheory.SimpleFunc",
        "MeasureTheory.SimpleFunc.mk",
        "MeasureTheory.SimpleFunc.range",
        "MeasureTheory.SimpleFunc.map",
        "MeasureTheory.SimpleFunc.indicator",
        "MeasureTheory.SimpleFunc.lintegral",
    ];

    for name in &simple_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing simple function constant: {name}"
        );
    }
}

#[test]
fn test_measure_theory_lebesgue_integral_exist() {
    let mut env = Environment::new();
    env.init_measure_theory().unwrap();

    let lintegral_names = [
        "MeasureTheory.lintegral",
        "MeasureTheory.lintegral_zero",
        "MeasureTheory.lintegral_add",
        "MeasureTheory.lintegral_const",
        "MeasureTheory.lintegral_mono",
        "MeasureTheory.lintegral_indicator",
    ];

    for name in &lintegral_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing Lebesgue integral constant: {name}"
        );
    }
}

#[test]
fn test_measure_theory_bochner_integral_exist() {
    let mut env = Environment::new();
    env.init_measure_theory().unwrap();

    let integral_names = [
        "MeasureTheory.integral",
        "MeasureTheory.Integrable",
        "MeasureTheory.integral_zero",
        "MeasureTheory.integral_add",
        "MeasureTheory.integral_neg",
        "MeasureTheory.integral_sub",
        "MeasureTheory.integral_smul",
        "MeasureTheory.integral_mono",
        "MeasureTheory.integral_nonneg",
    ];

    for name in &integral_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing Bochner integral constant: {name}"
        );
    }
}

#[test]
fn test_measure_theory_convergence_theorems_exist() {
    let mut env = Environment::new();
    env.init_measure_theory().unwrap();

    let convergence_names = [
        "MeasureTheory.monotone_convergence",
        "MeasureTheory.fatou",
        "MeasureTheory.dominated_convergence",
        "MeasureTheory.vitali_convergence",
    ];

    for name in &convergence_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing convergence theorem constant: {name}"
        );
    }
}

#[test]
fn test_measure_theory_fubini_tonelli_exist() {
    let mut env = Environment::new();
    env.init_measure_theory().unwrap();

    let fubini_names = [
        "MeasureTheory.MeasureProd",
        "MeasureTheory.prod_apply",
        "MeasureTheory.fubini",
        "MeasureTheory.tonelli",
        "MeasureTheory.integral_prod",
    ];

    for name in &fubini_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing Fubini-Tonelli constant: {name}"
        );
    }
}

#[test]
fn test_measure_theory_radon_nikodym_exist() {
    let mut env = Environment::new();
    env.init_measure_theory().unwrap();

    let radon_nikodym_names = [
        "MeasureTheory.AbsolutelyContinuous",
        "MeasureTheory.MutuallySingular",
        "MeasureTheory.radon_nikodym",
        "MeasureTheory.rnDeriv",
        "MeasureTheory.withDensity",
        "MeasureTheory.lebesgue_decomposition",
    ];

    for name in &radon_nikodym_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing Radon-Nikodym constant: {name}"
        );
    }
}

#[test]
fn test_measure_theory_lp_spaces_exist() {
    let mut env = Environment::new();
    env.init_measure_theory().unwrap();

    let lp_names = [
        "MeasureTheory.Lp",
        "MeasureTheory.Lp.norm",
        "MeasureTheory.Memℒp",
        "MeasureTheory.snorm",
        "MeasureTheory.Lp.complete",
        "MeasureTheory.holder",
        "MeasureTheory.minkowski",
        "MeasureTheory.Lp.dual",
    ];

    for name in &lp_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing Lp space constant: {name}"
        );
    }
}

#[test]
fn test_measure_theory_probability_basic_exist() {
    let mut env = Environment::new();
    env.init_measure_theory().unwrap();

    let prob_names = [
        "MeasureTheory.ProbabilitySpace",
        "MeasureTheory.prob_univ",
        "MeasureTheory.prob_empty",
        "MeasureTheory.prob_compl",
        "MeasureTheory.prob_union",
        "MeasureTheory.prob_inter",
    ];

    for name in &prob_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing probability constant: {name}"
        );
    }
}

#[test]
fn test_measure_theory_random_variables_exist() {
    let mut env = Environment::new();
    env.init_measure_theory().unwrap();

    let rv_names = [
        "MeasureTheory.RandomVariable",
        "MeasureTheory.rv_measurable",
        "MeasureTheory.pushforward",
        "MeasureTheory.Distribution",
        "MeasureTheory.IdenticallyDistributed",
    ];

    for name in &rv_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing random variable constant: {name}"
        );
    }
}

#[test]
fn test_measure_theory_expectation_exist() {
    let mut env = Environment::new();
    env.init_measure_theory().unwrap();

    let exp_names = [
        "MeasureTheory.Expectation",
        "MeasureTheory.expectation_const",
        "MeasureTheory.expectation_add",
        "MeasureTheory.expectation_smul",
        "MeasureTheory.expectation_nonneg",
        "MeasureTheory.expectation_mono",
        "MeasureTheory.expectation_indicator",
    ];

    for name in &exp_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing expectation constant: {name}"
        );
    }
}

#[test]
fn test_measure_theory_variance_exist() {
    let mut env = Environment::new();
    env.init_measure_theory().unwrap();

    let var_names = [
        "MeasureTheory.Variance",
        "MeasureTheory.variance_def",
        "MeasureTheory.variance_nonneg",
        "MeasureTheory.variance_const",
        "MeasureTheory.variance_smul",
        "MeasureTheory.StandardDeviation",
        "MeasureTheory.Moment",
        "MeasureTheory.CentralMoment",
    ];

    for name in &var_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing variance/moment constant: {name}"
        );
    }
}

#[test]
fn test_measure_theory_independence_exist() {
    let mut env = Environment::new();
    env.init_measure_theory().unwrap();

    let indep_names = [
        "MeasureTheory.IndepSets",
        "MeasureTheory.Indep",
        "MeasureTheory.IndepFun",
        "MeasureTheory.indep_prod",
        "MeasureTheory.indep_expectation",
        "MeasureTheory.indep_variance",
        "MeasureTheory.iIndep",
    ];

    for name in &indep_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing independence constant: {name}"
        );
    }
}

#[test]
fn test_measure_theory_conditional_expectation_exist() {
    let mut env = Environment::new();
    env.init_measure_theory().unwrap();

    let condexp_names = [
        "MeasureTheory.condexp",
        "MeasureTheory.condexp_const",
        "MeasureTheory.condexp_add",
        "MeasureTheory.condexp_smul",
        "MeasureTheory.condexp_of_measurable",
        "MeasureTheory.condexp_tower",
        "MeasureTheory.condexp_integral",
    ];

    for name in &condexp_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing conditional expectation constant: {name}"
        );
    }
}

#[test]
fn test_measure_theory_convergence_modes_exist() {
    let mut env = Environment::new();
    env.init_measure_theory().unwrap();

    let conv_names = [
        "MeasureTheory.TendstoInMeasure",
        "MeasureTheory.TendstoInLp",
        "MeasureTheory.TendstoAe",
        "MeasureTheory.TendstoProb",
        "MeasureTheory.TendstoDistr",
        "MeasureTheory.ae_implies_prob",
        "MeasureTheory.Lp_implies_prob",
        "MeasureTheory.prob_implies_distr",
    ];

    for name in &conv_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing convergence mode constant: {name}"
        );
    }
}

#[test]
fn test_measure_theory_lln_exist() {
    let mut env = Environment::new();
    env.init_measure_theory().unwrap();

    let lln_names = [
        "MeasureTheory.strong_law",
        "MeasureTheory.weak_law",
        "MeasureTheory.SLLN_iid",
        "MeasureTheory.WLLN_iid",
    ];

    for name in &lln_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing LLN constant: {name}"
        );
    }
}

#[test]
fn test_measure_theory_clt_exist() {
    let mut env = Environment::new();
    env.init_measure_theory().unwrap();

    let clt_names = [
        "MeasureTheory.CLT",
        "MeasureTheory.CLT_iid",
        "MeasureTheory.NormalDistribution",
        "MeasureTheory.StandardNormal",
        "MeasureTheory.normal_pdf",
        "MeasureTheory.normal_cdf",
    ];

    for name in &clt_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing CLT/Normal constant: {name}"
        );
    }
}

#[test]
fn test_measure_theory_distributions_exist() {
    let mut env = Environment::new();
    env.init_measure_theory().unwrap();

    let dist_names = [
        "MeasureTheory.Bernoulli",
        "MeasureTheory.Binomial",
        "MeasureTheory.Poisson",
        "MeasureTheory.Geometric",
        "MeasureTheory.Exponential",
        "MeasureTheory.Uniform",
        "MeasureTheory.Gamma",
        "MeasureTheory.Beta",
    ];

    for name in &dist_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing distribution constant: {name}"
        );
    }
}

#[test]
fn test_measure_theory_martingales_exist() {
    let mut env = Environment::new();
    env.init_measure_theory().unwrap();

    let mart_names = [
        "MeasureTheory.Martingale",
        "MeasureTheory.Submartingale",
        "MeasureTheory.Supermartingale",
        "MeasureTheory.Filtration",
        "MeasureTheory.Adapted",
        "MeasureTheory.StoppingTime",
        "MeasureTheory.optional_stopping",
        "MeasureTheory.martingale_convergence",
        "MeasureTheory.DoobMaximal",
    ];

    for name in &mart_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing martingale constant: {name}"
        );
    }
}

#[test]
fn test_measure_theory_characteristic_functions_exist() {
    let mut env = Environment::new();
    env.init_measure_theory().unwrap();

    let charfun_names = [
        "MeasureTheory.CharFun",
        "MeasureTheory.charfun_unique",
        "MeasureTheory.charfun_normal",
        "MeasureTheory.charfun_sum",
        "MeasureTheory.levy_continuity",
    ];

    for name in &charfun_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing characteristic function constant: {name}"
        );
    }
}

#[test]
fn test_measure_theory_ergodic_exist() {
    let mut env = Environment::new();
    env.init_measure_theory().unwrap();

    let ergodic_names = [
        "MeasureTheory.MeasurePreserving",
        "MeasureTheory.QuasiMeasurePreserving",
        "MeasureTheory.Ergodic",
        "MeasureTheory.ergodic_theorem",
        "MeasureTheory.MixingOn",
    ];

    for name in &ergodic_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing ergodic theory constant: {name}"
        );
    }
}

#[test]
fn test_measure_theory_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_measure_theory().unwrap();
    assert!(env.has_eq());
    assert!(env.has_nat());
    assert!(env.has_rat());
    assert!(env.has_topological_space());
}

#[test]
fn test_measure_theory_constant_count() {
    let mut env = Environment::new();
    let before = env.constants.len();
    env.init_measure_theory().unwrap();
    let after = env.constants.len();

    // Expect a rich collection of measure theory constants plus dependencies
    let measure_theory_count = after - before;
    assert!(
        measure_theory_count >= 200,
        "Expected at least 200 new constants for measure theory (including deps), got {measure_theory_count}"
    );
}

// ============================================================================
// FUNCTIONAL ANALYSIS TESTS
// ============================================================================

#[test]
fn test_functional_analysis_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_functional_analysis());
    env.init_functional_analysis().unwrap();
    assert!(env.has_functional_analysis());
}

#[test]
fn test_functional_analysis_idempotent() {
    let mut env = Environment::new();
    env.init_functional_analysis().unwrap();
    env.init_functional_analysis().unwrap();
    assert!(env.has_functional_analysis());
}

#[test]
fn test_functional_analysis_norms_exist() {
    let mut env = Environment::new();
    env.init_functional_analysis().unwrap();

    let norm_names = [
        "Analysis.Norm",
        "Analysis.norm_nonneg",
        "Analysis.norm_eq_zero",
        "Analysis.norm_add_le",
        "Analysis.norm_smul",
        "Analysis.norm_neg",
        "Analysis.Seminorm",
        "Analysis.seminorm_nonneg",
    ];

    for name in &norm_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing norm constant: {name}"
        );
    }
}

#[test]
fn test_functional_analysis_normed_spaces_exist() {
    let mut env = Environment::new();
    env.init_functional_analysis().unwrap();

    let normed_names = [
        "Analysis.NormedAddCommGroup",
        "Analysis.NormedSpace",
        "Analysis.NormedRing",
        "Analysis.NormedAlgebra",
        "Analysis.NormedField",
        "Analysis.dist_eq_norm",
    ];

    for name in &normed_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing normed space constant: {name}"
        );
    }
}

#[test]
fn test_functional_analysis_inner_product_exist() {
    let mut env = Environment::new();
    env.init_functional_analysis().unwrap();

    let inner_names = [
        "Analysis.InnerProductSpace",
        "Analysis.inner_self_nonneg",
        "Analysis.inner_self_eq_zero",
        "Analysis.inner_add_left",
        "Analysis.inner_smul_left",
        "Analysis.inner_conj_symm",
        "Analysis.norm_sq_eq_inner",
        "Analysis.inner_mul_le_norm_mul",
        "Analysis.parallelogram_law",
    ];

    for name in &inner_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing inner product constant: {name}"
        );
    }
}

#[test]
fn test_functional_analysis_banach_spaces_exist() {
    let mut env = Environment::new();
    env.init_functional_analysis().unwrap();

    let banach_names = [
        "Analysis.CompleteSpace",
        "Analysis.BanachSpace",
        "Analysis.banach_closed_subspace",
        "Analysis.banach_quotient",
        "Analysis.banach_product",
        "Analysis.UniformConvergence",
        "Analysis.series_summable",
        "Analysis.norm_series_le",
    ];

    for name in &banach_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing Banach space constant: {name}"
        );
    }
}

#[test]
fn test_functional_analysis_hilbert_spaces_exist() {
    let mut env = Environment::new();
    env.init_functional_analysis().unwrap();

    let hilbert_names = [
        "Analysis.HilbertSpace",
        "Analysis.orthogonal_projection",
        "Analysis.projection_orthogonal",
        "Analysis.projection_closest_point",
        "Analysis.riesz_representation",
        "Analysis.orthonormal_basis",
        "Analysis.orthonormal_expansion",
        "Analysis.parseval_identity",
        "Analysis.bessel_inequality",
    ];

    for name in &hilbert_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing Hilbert space constant: {name}"
        );
    }
}

#[test]
fn test_functional_analysis_bounded_operators_exist() {
    let mut env = Environment::new();
    env.init_functional_analysis().unwrap();

    let bounded_names = [
        "Analysis.ContinuousLinearMap",
        "Analysis.ContinuousLinearMap.mk",
        "Analysis.ContinuousLinearMap.op_norm",
        "Analysis.op_norm_nonneg",
        "Analysis.op_norm_le_iff",
        "Analysis.apply_norm_le",
        "Analysis.op_norm_comp_le",
        "Analysis.BoundedLinearEquiv",
    ];

    for name in &bounded_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing bounded operator constant: {name}"
        );
    }
}

#[test]
fn test_functional_analysis_dual_spaces_exist() {
    let mut env = Environment::new();
    env.init_functional_analysis().unwrap();

    let dual_names = [
        "Analysis.NormedSpace.Dual",
        "Analysis.NormedSpace.dual_def",
        "Analysis.NormedSpace.dual_pairing",
        "Analysis.NormedSpace.Dual.BanachSpace",
        "Analysis.NormedSpace.bidual",
        "Analysis.NormedSpace.canonical_embedding",
        "Analysis.canonical_embedding_isometry",
        "Analysis.reflexive",
    ];

    for name in &dual_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing dual space constant: {name}"
        );
    }
}

#[test]
fn test_functional_analysis_hahn_banach_exist() {
    let mut env = Environment::new();
    env.init_functional_analysis().unwrap();

    let hb_names = [
        "Analysis.HahnBanach.extension",
        "Analysis.HahnBanach.separation",
        "Analysis.HahnBanach.geometric",
        "Analysis.exists_dual_vector",
        "Analysis.dual_norm_eq",
    ];

    for name in &hb_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing Hahn-Banach constant: {name}"
        );
    }
}

#[test]
fn test_functional_analysis_fundamental_theorems_exist() {
    let mut env = Environment::new();
    env.init_functional_analysis().unwrap();

    let theorem_names = [
        "Analysis.OpenMapping.theorem",
        "Analysis.ClosedGraph.theorem",
        "Analysis.BanachSteinhaus",
        "Analysis.bounded_of_pointwise_bounded",
    ];

    for name in &theorem_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing fundamental theorem constant: {name}"
        );
    }
}

#[test]
fn test_functional_analysis_compact_operators_exist() {
    let mut env = Environment::new();
    env.init_functional_analysis().unwrap();

    let compact_names = [
        "Analysis.CompactOperator",
        "Analysis.compact_op_def",
        "Analysis.compact_op_of_finite_rank",
        "Analysis.compact_op_ideal",
        "Analysis.compact_op_limit",
        "Analysis.compact_op_adjoint",
    ];

    for name in &compact_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Missing compact operator constant: {name}"
        );
    }
}

// ============================================================================
// Domain Types Module Tests (algebra_module.rs - init_domain_types)
// ============================================================================

#[test]
fn test_domain_types_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_domain_types());
    env.init_domain_types().unwrap();
    assert!(env.has_domain_types());
}

#[test]
fn test_domain_types_idempotent() {
    let mut env = Environment::new();
    env.init_domain_types().unwrap();
    env.init_domain_types().unwrap();
    assert!(env.has_domain_types());
}

/// Regression test for #2884: .olean pre-loads Finite before init_domain_types runs.
/// Previously crashed with DuplicateName("Finite").
#[test]
fn test_domain_types_preexisting_finite_no_crash() {
    let mut env = Environment::new();
    // Simulate .olean loading Finite before init runs
    let u = Name::from_string("u");
    let type_u = Expr::sort(Level::succ(Level::param(u.clone())));
    let prop = Expr::sort(Level::zero());
    let finite_type = Expr::pi(BinderInfo::Default, type_u, prop);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Finite"),
        level_params: vec![u],
        type_: finite_type,
    })
    .unwrap();
    // init_domain_types must succeed despite Finite already existing
    env.init_domain_types().unwrap();
    assert!(env.has_domain_types());
    assert!(env.get_const(&Name::from_string("Finite")).is_some());
}

#[test]
fn test_domain_types_isdomain_exist() {
    let mut env = Environment::new();
    env.init_domain_types().unwrap();

    // Core domain predicates (used in ~60% of FATE-X problems)
    let constants = vec!["IsDomain", "NoZeroDivisors"];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Domain predicate {name} should exist"
        );
    }
}

#[test]
fn test_domain_types_noetherian_ring_exist() {
    let mut env = Environment::new();
    env.init_domain_types().unwrap();

    // Noetherian/Artinian ring properties (used in ~50% of FATE-X problems)
    let constants = vec!["IsNoetherianRing", "IsArtinianRing", "IsGorensteinRing"];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Ring property {name} should exist"
        );
    }
}

#[test]
fn test_domain_types_chain_complex_exist() {
    let mut env = Environment::new();
    env.init_domain_types().unwrap();

    // Chain complex types (used in ~15% of FATE-X problems)
    let constants = vec![
        "ChainComplex",
        "ChainComplex.d",
        "ChainComplex.X",
        "ChainComplex.Acyclic",
        "ModuleCat",
        "ModuleCat.of",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Chain complex type {name} should exist"
        );
    }
}

#[test]
fn test_domain_types_homological_algebra_exist() {
    let mut env = Environment::new();
    env.init_domain_types().unwrap();

    // Homological algebra types
    let constants = vec![
        "DirectSum",
        "DirectSum.Decomposition",
        "Ext",
        "Tor",
        "MvPolynomial",
        "MvPolynomial.homogeneousSubmodule",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Homological algebra type {name} should exist"
        );
    }
}

#[test]
fn test_domain_types_alg_hom_exist() {
    let mut env = Environment::new();
    env.init_domain_types().unwrap();

    // Algebra homomorphisms (used in ~20% of FATE-X)
    let constants = vec![
        "AlgHom",
        "AlgHom.toRingHom",
        "AlgHom.comp",
        "AlgHom.id",
        "AlgEquiv",
        "AlgEquiv.toAlgHom",
        "AlgEquiv.symm",
        "AlgEquiv.trans",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Algebra homomorphism type {name} should exist"
        );
    }
}

#[test]
fn test_domain_types_dimension_theory_exist() {
    let mut env = Environment::new();
    env.init_domain_types().unwrap();

    // Dimension theory (used in ~19% of FATE-X)
    let constants = vec![
        "KrullDimension",
        "ringKrullDim",
        "Ideal.height",
        "FiniteDimensional",
        "Module.finrank",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Dimension theory type {name} should exist"
        );
    }
}

#[test]
fn test_domain_types_tensor_flat_exist() {
    let mut env = Environment::new();
    env.init_domain_types().unwrap();

    // Tensor products and flat modules (used in ~8-13% of FATE-X)
    let constants = vec![
        "TensorProduct",
        "TensorProduct.tmul",
        "TensorProduct.lift",
        "TensorProduct.assoc",
        "Module.Flat",
        "Module.Flat.of_free",
        "Module.Flat.of_projective",
    ];

    for name in constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Tensor/flat type {name} should exist"
        );
    }
}

#[test]
fn test_domain_types_batch2_local_ring_char_exist() {
    // Batch 2 stubs from #132: IsLocalRing, CharZero, Finite, DualNumber
    let mut env = Environment::new();
    env.init_domain_types().unwrap();

    // Local ring stubs (9 occurrences in FATE-X)
    let local_ring_constants = vec![
        "IsLocalRing",
        "LocalRing",
        "LocalRing.maximalIdeal",
        "LocalRing.closed_point",
        "IsRegularLocalRing",
    ];
    for name in local_ring_constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Local ring stub {name} should exist"
        );
    }

    // Characteristic stubs (3 occurrences in FATE-X)
    let char_constants = vec!["CharZero", "CharP", "CharP.cast_eq_zero"];
    for name in char_constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Characteristic stub {name} should exist"
        );
    }

    // Finite type stubs (3 occurrences in FATE-X)
    let finite_constants = vec!["Finite", "Finite.intro", "Finite.of_fintype", "Fintype"];
    for name in finite_constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Finite type stub {name} should exist"
        );
    }

    // Dual number stubs (3 occurrences in FATE-X)
    let dual_constants = vec!["DualNumber", "DualNumber.eps"];
    for name in dual_constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Dual number stub {name} should exist"
        );
    }
}

/// Regression test for #2884: Finite/CharZero/IsMaximal must use
/// BinderInfo::Default (explicit), not BinderInfo::Implicit. Implicit binders
/// cause TooManyArguments downstream (e.g., `Finite Nat` auto-fills the type
/// arg, leaving `Nat` as an extra).
///
/// `Fintype` is no longer in this list: it is now a real Type-valued data
/// *structure* (`{ elems : Finset α, complete : … }`, see `init_fintype`),
/// not an opaque `(α : Type u) → Prop` predicate. Its explicit-binder
/// invariant is covered by `data_types_finset::test_fintype_structure_*`.
#[test]
fn test_domain_types_simple_predicates_use_explicit_binder() {
    let mut env = Environment::new();
    env.init_domain_types().unwrap();

    for name in &["Finite", "CharZero", "IsMaximal"] {
        let ci = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} must exist after init_domain_types"));
        match ci.type_.kind() {
            ExprKind::Pi(bd, _ty, _body) => {
                assert_eq!(
                    bd.info,
                    BinderInfo::Default,
                    "{name} should have explicit (Default) binder, not {:?}. \
                     Lean 4 declares these as `(α : Sort*)`, not `{{α : Sort*}}`.",
                    bd.info
                );
            }
            other => panic!("{name} type should be Pi, got {other:?}"),
        }
    }
}

#[test]
fn test_init_module_algebra_all_calls_domain_types() {
    let mut env = Environment::new();
    assert!(!env.has_domain_types());
    env.init_module_algebra_all().unwrap();
    assert!(
        env.has_domain_types(),
        "init_module_algebra_all should initialize domain types"
    );
    assert!(
        env.has_module(),
        "init_module_algebra_all should initialize module"
    );
    assert!(
        env.has_algebra(),
        "init_module_algebra_all should initialize algebra"
    );
    assert!(
        env.has_submodule(),
        "init_module_algebra_all should initialize submodule"
    );
    assert!(
        env.has_ideal(),
        "init_module_algebra_all should initialize ideal"
    );
}

/// Test that core Module/Algebra/Ideal/Submodule constants exist (Phase 17b, Issue #587)
#[test]
fn test_module_algebra_core_constants_exist() {
    let mut env = Environment::new();
    env.init_module_algebra_all().unwrap();

    // Core constants required by Phase 17b for FATE-X elaboration
    let core_constants = [
        "Module",
        "Module.smul",
        "Algebra",
        "Algebra.algebraMap",
        "Ideal",
        "Ideal.span",
        "Submodule",
        "Submodule.span",
    ];

    for name in core_constants {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "Core constant {} should exist after init_module_algebra_all",
            name
        );
    }
}

// ================================================================
// Type well-formedness tests (Issue #1538)
//
// Each domain gets at least one tc.infer_type() call on a key constant
// to verify that registered types are actually well-formed, not just
// present in the environment.
// ================================================================

/// Helper: verify that key constants in a domain have well-formed types.
/// Looks up each constant's declaration to determine the correct number of
/// universe parameters, then verifies tc.infer_type() succeeds and returns
/// a Sort type.
fn assert_key_types_well_formed(env: &Environment, domain: &str, constants: &[&str]) {
    use crate::expr::ExprKind;
    use crate::level::Level;
    use crate::tc::TypeChecker;

    let tc = TypeChecker::new(env);
    for name in constants {
        let n = Name::from_string(name);
        let ci = env
            .get_const(&n)
            .unwrap_or_else(|| panic!("{domain}/{name}: constant not found in env"));
        let levels: Vec<Level> = ci.level_params.iter().map(|_| Level::zero()).collect();
        let expr = Expr::const_(n, levels);
        let ty = tc
            .infer_type(&expr)
            .unwrap_or_else(|e| panic!("{domain}/{name}: tc.infer_type failed: {e}"));
        assert!(
            matches!(&ty.kind, ExprKind::Sort(_)),
            "{domain}/{name}: expected Sort type, got {ty:?}"
        );
    }
}

/// Helper: verify a constant has a Pi type with exactly `expected_binders` binders.
/// Looks up universe params from the declaration and substitutes Level::zero().
fn assert_pi_binder_count(env: &Environment, domain: &str, name: &str, expected_binders: usize) {
    use crate::expr::ExprKind;
    use crate::level::Level;
    use crate::tc::TypeChecker;

    let tc = TypeChecker::new(env);
    let n = Name::from_string(name);
    let ci = env
        .get_const(&n)
        .unwrap_or_else(|| panic!("{domain}/{name}: constant not found in env"));
    let levels: Vec<Level> = ci.level_params.iter().map(|_| Level::zero()).collect();
    let expr = Expr::const_(n, levels);
    let ty = tc
        .infer_type(&expr)
        .unwrap_or_else(|e| panic!("{domain}/{name}: tc.infer_type failed: {e}"));
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(
        count, expected_binders,
        "{domain}/{name}: expected {expected_binders} Pi binders, got {count}"
    );
}

/// Helper: verify a constant type-checks with Level::param() universe parameters
/// (not just Level::zero()), confirming universe polymorphism is well-formed.
fn assert_polymorphic_type_well_formed(env: &Environment, domain: &str, name: &str) {
    use crate::level::Level;
    use crate::tc::TypeChecker;

    let tc = TypeChecker::new(env);
    let n = Name::from_string(name);
    let ci = env
        .get_const(&n)
        .unwrap_or_else(|| panic!("{domain}/{name}: constant not found in env"));
    let levels: Vec<Level> = ci
        .level_params
        .iter()
        .map(|p| Level::param(p.clone()))
        .collect();
    let expr = Expr::const_(n, levels);
    let _ = tc
        .infer_type(&expr)
        .unwrap_or_else(|e| panic!("{domain}/{name}: tc.infer_type with param levels failed: {e}"));
}

#[test]
fn test_algebra_linear_key_types_well_formed() {
    let mut env = Environment::new();
    env.init_algebra_linear().unwrap();
    assert_key_types_well_formed(
        &env,
        "algebra_linear",
        &[
            "Algebra.LinearAlgebra.Module",
            "Algebra.LinearAlgebra.VectorSpace",
            "Algebra.LinearAlgebra.LinearMap",
        ],
    );
}

#[test]
fn test_category_theory_key_types_well_formed() {
    let mut env = Environment::new();
    env.init_category_theory().unwrap();
    assert_key_types_well_formed(
        &env,
        "category_theory",
        &[
            "CategoryTheory.Category",
            "CategoryTheory.Functor",
            "CategoryTheory.NatTrans",
        ],
    );
}

#[test]
fn test_homological_algebra_key_types_well_formed() {
    let mut env = Environment::new();
    env.init_homological_algebra().unwrap();
    assert_key_types_well_formed(
        &env,
        "homological_algebra",
        &[
            "HomologicalAlgebra.ChainComplex",
            "HomologicalAlgebra.Homology",
            "HomologicalAlgebra.DerivedCategory",
        ],
    );
}

#[test]
fn test_number_theory_key_types_well_formed() {
    let mut env = Environment::new();
    env.init_number_theory().unwrap();
    assert_key_types_well_formed(
        &env,
        "number_theory",
        &[
            "NumberTheory.Prime",
            "NumberTheory.GaloisGroup",
            "NumberTheory.EllipticCurve",
        ],
    );
}

#[test]
fn test_algebraic_geometry_key_types_well_formed() {
    let mut env = Environment::new();
    env.init_algebraic_geometry().unwrap();
    assert_key_types_well_formed(
        &env,
        "algebraic_geometry",
        &[
            "AlgebraicGeometry.AffineVariety",
            "AlgebraicGeometry.Scheme",
            "AlgebraicGeometry.Sheaf",
        ],
    );
}

#[test]
fn test_representation_theory_key_types_well_formed() {
    let mut env = Environment::new();
    env.init_representation_theory().unwrap();
    assert_key_types_well_formed(
        &env,
        "representation_theory",
        &[
            "RepresentationTheory.LieGroup",
            "RepresentationTheory.LieAlgebra",
            "RepresentationTheory.Representation",
        ],
    );
}

#[test]
fn test_measure_theory_key_types_well_formed() {
    let mut env = Environment::new();
    env.init_measure_theory().unwrap();
    assert_key_types_well_formed(
        &env,
        "measure_theory",
        &[
            "MeasureTheory.MeasurableSpace",
            "MeasureTheory.Measure",
            "MeasureTheory.lintegral",
        ],
    );
}

#[test]
fn test_functional_analysis_key_types_well_formed() {
    let mut env = Environment::new();
    env.init_functional_analysis().unwrap();
    assert_key_types_well_formed(
        &env,
        "functional_analysis",
        &[
            "Analysis.Norm",
            "Analysis.BanachSpace",
            "Analysis.HilbertSpace",
        ],
    );
}

#[test]
fn test_domain_types_key_types_well_formed() {
    use crate::expr::ExprKind;
    use crate::level::Level;
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_domain_types().unwrap();
    let tc = TypeChecker::new(&env);

    // Type-level constants (Sort(succ(u)) at u=0 → Sort(1))
    assert_key_types_well_formed(&env, "domain_types", &["KrullDimension", "LocalRing"]);

    // Predicate constants (Pi types) — verify infer_type succeeds
    for name in &["IsDomain", "IsNoetherianRing"] {
        let expr = Expr::const_(Name::from_string(name), vec![Level::zero()]);
        let ty = tc
            .infer_type(&expr)
            .unwrap_or_else(|e| panic!("domain_types/{name}: tc.infer_type failed: {e}"));
        assert!(
            matches!(&ty.kind, ExprKind::Pi(..)),
            "domain_types/{name}: expected Pi type, got {ty:?}"
        );
    }
}

#[test]
fn test_module_algebra_key_types_well_formed() {
    let mut env = Environment::new();
    env.init_module_algebra_all().unwrap();
    assert_key_types_well_formed(&env, "module_algebra", &["Module", "Algebra", "Submodule"]);
}

// ================================================================
// Pi binder count tests (Issue #1538, acceptance criteria #3)
//
// Function-typed constants must have correct Pi binder counts.
// ================================================================

#[test]
fn test_ideal_pi_binder_count() {
    let mut env = Environment::new();
    env.init_module_algebra_all().unwrap();
    // Ideal : Type u → Type u (1 Pi binder)
    assert_pi_binder_count(&env, "module_algebra", "Ideal", 1);
}

#[test]
fn test_mvpolynomial_pi_binder_count() {
    let mut env = Environment::new();
    env.init_module_algebra_all().unwrap();
    // MvPolynomial : Type u → Type v → Type (max u v) (2 Pi binders)
    assert_pi_binder_count(&env, "module_algebra", "MvPolynomial", 2);
}

#[test]
fn test_tensor_product_pi_binder_count() {
    let mut env = Environment::new();
    env.init_module_algebra_all().unwrap();
    // TensorProduct : Type u → Type v → Type (max u v) (2 Pi binders)
    assert_pi_binder_count(&env, "module_algebra", "TensorProduct", 2);
}

#[test]
fn test_domain_types_predicate_pi_binder_count() {
    let mut env = Environment::new();
    env.init_domain_types().unwrap();
    // IsDomain, IsNoetherianRing : {α : Type u} → [Ring α] → Prop (2 Pi binders)
    assert_pi_binder_count(&env, "domain_types", "IsDomain", 2);
    assert_pi_binder_count(&env, "domain_types", "IsNoetherianRing", 2);
}

// ================================================================
// Universe polymorphism tests (Issue #1538, acceptance criteria #2)
//
// Polymorphic constants must type-check with Level::param() universes,
// not just Level::zero().
// ================================================================

#[test]
fn test_algebra_linear_universe_polymorphism() {
    let mut env = Environment::new();
    env.init_algebra_linear().unwrap();
    assert_polymorphic_type_well_formed(&env, "algebra_linear", "Algebra.LinearAlgebra.Module");
    assert_polymorphic_type_well_formed(&env, "algebra_linear", "Algebra.LinearAlgebra.LinearMap");
}

#[test]
fn test_category_theory_universe_polymorphism() {
    let mut env = Environment::new();
    env.init_category_theory().unwrap();
    assert_polymorphic_type_well_formed(&env, "category_theory", "CategoryTheory.Category");
    assert_polymorphic_type_well_formed(&env, "category_theory", "CategoryTheory.Functor");
}

#[test]
fn test_module_algebra_universe_polymorphism() {
    let mut env = Environment::new();
    env.init_module_algebra_all().unwrap();
    assert_polymorphic_type_well_formed(&env, "module_algebra", "Module");
    assert_polymorphic_type_well_formed(&env, "module_algebra", "Ideal");
    assert_polymorphic_type_well_formed(&env, "module_algebra", "TensorProduct");
}

#[test]
fn test_number_theory_universe_polymorphism() {
    let mut env = Environment::new();
    env.init_number_theory().unwrap();
    assert_polymorphic_type_well_formed(&env, "number_theory", "NumberTheory.Prime");
    assert_polymorphic_type_well_formed(&env, "number_theory", "NumberTheory.GaloisGroup");
}
