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

use crate::env::test_helpers::assert_const;
use crate::env::*;

#[test]
fn test_functional_analysis_fredholm_operators_exist() {
    let mut env = Environment::new();
    env.init_functional_analysis().unwrap();

    let fredholm_names = [
        "Analysis.FredholmOperator",
        "Analysis.fredholm_index",
        "Analysis.fredholm_index_zero",
        "Analysis.fredholm_index_sum",
        "Analysis.fredholm_perturbation",
        "Analysis.fredholm_index_stable",
    ];

    for name in &fredholm_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_functional_analysis_spectrum_exist() {
    let mut env = Environment::new();
    env.init_functional_analysis().unwrap();

    let spectrum_names = [
        "Analysis.Spectrum",
        "Analysis.spectrum_def",
        "Analysis.resolvent_set",
        "Analysis.resolvent",
        "Analysis.resolvent_equation",
        "Analysis.spectrum_nonempty",
        "Analysis.spectrum_closed",
        "Analysis.spectrum_bounded",
        "Analysis.spectral_radius",
        "Analysis.spectral_radius_formula",
    ];

    for name in &spectrum_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_functional_analysis_spectrum_partition_exist() {
    let mut env = Environment::new();
    env.init_functional_analysis().unwrap();

    let partition_names = [
        "Analysis.point_spectrum",
        "Analysis.continuous_spectrum",
        "Analysis.residual_spectrum",
        "Analysis.spectrum_partition",
        "Analysis.eigenvalue_bound",
    ];

    for name in &partition_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_functional_analysis_self_adjoint_exist() {
    let mut env = Environment::new();
    env.init_functional_analysis().unwrap();

    let sa_names = [
        "Analysis.IsSelfAdjoint",
        "Analysis.self_adjoint_inner",
        "Analysis.self_adjoint_spectrum_real",
        "Analysis.self_adjoint_eigenvectors_orthogonal",
        "Analysis.IsPositive",
        "Analysis.positive_spectrum_nonneg",
        "Analysis.positive_square_root",
    ];

    for name in &sa_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_functional_analysis_normal_operators_exist() {
    let mut env = Environment::new();
    env.init_functional_analysis().unwrap();

    let normal_names = [
        "Analysis.IsNormal",
        "Analysis.normal_spectral_radius",
        "Analysis.normal_eigenvectors_orthogonal",
        "Analysis.IsUnitary",
        "Analysis.unitary_spectrum_circle",
        "Analysis.unitary_isometry",
    ];

    for name in &normal_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_functional_analysis_spectral_theorem_exist() {
    let mut env = Environment::new();
    env.init_functional_analysis().unwrap();

    let spectral_names = [
        "Analysis.SpectralTheorem.compact_self_adjoint",
        "Analysis.compact_sa_eigenvalues",
        "Analysis.compact_sa_eigenvectors",
        "Analysis.SpectralTheorem.bounded_self_adjoint",
        "Analysis.spectral_measure",
        "Analysis.spectral_integral",
        "Analysis.functional_calculus",
    ];

    for name in &spectral_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_functional_analysis_lp_spaces_exist() {
    let mut env = Environment::new();
    env.init_functional_analysis().unwrap();

    let lp_names = [
        "Analysis.Lp.BanachSpace",
        "Analysis.Lp.HilbertSpace",
        "Analysis.Lp.norm_def",
        "Analysis.Lp.holder",
        "Analysis.Lp.minkowski",
        "Analysis.Lp.dual",
        "Analysis.L2.inner",
        "Analysis.L_infty",
    ];

    for name in &lp_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_functional_analysis_sobolev_spaces_exist() {
    let mut env = Environment::new();
    env.init_functional_analysis().unwrap();

    let sobolev_names = [
        "Analysis.SobolevSpace",
        "Analysis.sobolev_norm",
        "Analysis.weak_derivative",
        "Analysis.sobolev_embedding",
        "Analysis.sobolev_compact_embedding",
        "Analysis.trace_theorem",
        "Analysis.poincare_inequality",
        "Analysis.rellich_kondrachov",
    ];

    for name in &sobolev_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_functional_analysis_semigroups_exist() {
    let mut env = Environment::new();
    env.init_functional_analysis().unwrap();

    let semigroup_names = [
        "Analysis.ContinuousSemigroup",
        "Analysis.semigroup_composition",
        "Analysis.semigroup_identity",
        "Analysis.semigroup_continuity",
        "Analysis.semigroup_generator",
        "Analysis.hille_yosida",
        "Analysis.semigroup_exponential",
        "Analysis.lumer_phillips",
    ];

    for name in &semigroup_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_functional_analysis_cstar_algebras_exist() {
    let mut env = Environment::new();
    env.init_functional_analysis().unwrap();

    let cstar_names = [
        "Analysis.CStarAlgebra",
        "Analysis.cstar_identity",
        "Analysis.cstar_involution",
        "Analysis.cstar_positive",
        "Analysis.cstar_spectrum_real",
        "Analysis.GelfandNaimark",
        "Analysis.cstar_representation",
        "Analysis.gns_construction",
    ];

    for name in &cstar_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_functional_analysis_von_neumann_exist() {
    let mut env = Environment::new();
    env.init_functional_analysis().unwrap();

    let vn_names = [
        "Analysis.VonNeumannAlgebra",
        "Analysis.von_neumann_bicommutant",
        "Analysis.von_neumann_predual",
        "Analysis.von_neumann_type",
        "Analysis.von_neumann_projection",
        "Analysis.von_neumann_trace",
    ];

    for name in &vn_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_functional_analysis_unbounded_operators_exist() {
    let mut env = Environment::new();
    env.init_functional_analysis().unwrap();

    let unbounded_names = [
        "Analysis.UnboundedOperator",
        "Analysis.UnboundedOperator.domain",
        "Analysis.UnboundedOperator.graph",
        "Analysis.UnboundedOperator.closed",
        "Analysis.UnboundedOperator.closable",
        "Analysis.UnboundedOperator.adjoint",
        "Analysis.UnboundedOperator.self_adjoint",
        "Analysis.UnboundedOperator.spectrum",
        "Analysis.spectral_theorem_unbounded",
    ];

    for name in &unbounded_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_functional_analysis_fixed_point_exist() {
    let mut env = Environment::new();
    env.init_functional_analysis().unwrap();

    let fixed_point_names = [
        "Analysis.BanachFixedPoint",
        "Analysis.contraction_def",
        "Analysis.banach_fixed_point_unique",
        "Analysis.banach_fixed_point_limit",
        "Analysis.SchauderFixedPoint",
        "Analysis.LeraySchauder",
    ];

    for name in &fixed_point_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_functional_analysis_weak_topologies_exist() {
    let mut env = Environment::new();
    env.init_functional_analysis().unwrap();

    let weak_names = [
        "Analysis.WeakTopology",
        "Analysis.weak_convergence",
        "Analysis.WeakStarTopology",
        "Analysis.weak_star_convergence",
        "Analysis.Banach_Alaoglu",
        "Analysis.Goldstine",
        "Analysis.Eberlein_Smulian",
        "Analysis.Mazur",
    ];

    for name in &weak_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_functional_analysis_interpolation_exist() {
    let mut env = Environment::new();
    env.init_functional_analysis().unwrap();

    let interp_names = [
        "Analysis.Interpolation.compatible",
        "Analysis.Interpolation.complex",
        "Analysis.Interpolation.real",
        "Analysis.Riesz_Thorin",
        "Analysis.Marcinkiewicz",
    ];

    for name in &interp_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_functional_analysis_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_functional_analysis().unwrap();
    assert!(env.has_eq());
    assert!(env.has_nat());
    assert!(env.has_rat());
    assert!(env.has_topological_space());
    assert!(env.has_algebra_linear());
}

#[test]
fn test_functional_analysis_constant_count() {
    let mut env = Environment::new();
    let before = env.constants.len();
    env.init_functional_analysis().unwrap();
    let after = env.constants.len();

    // Expect a rich collection of functional analysis constants plus dependencies
    let functional_analysis_count = after - before;
    assert!(
        functional_analysis_count >= 180,
        "Expected at least 180 new constants for functional analysis (including deps), got {functional_analysis_count}"
    );
}

#[test]
fn test_functional_analysis_key_types_well_formed() {
    use crate::expr::ExprKind;
    use crate::level::Level;
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_functional_analysis().unwrap();
    let tc = TypeChecker::new(&env);

    for name in &[
        "Analysis.Spectrum",
        "Analysis.BanachFixedPoint",
        "Analysis.CStarAlgebra",
        "Analysis.SobolevSpace",
    ] {
        let expr = Expr::const_(Name::from_string(name), vec![Level::zero()]);
        let ty = tc
            .infer_type(&expr)
            .unwrap_or_else(|e| panic!("{name}: tc.infer_type failed: {e}"));
        assert!(
            matches!(&ty.kind, ExprKind::Sort(_) | ExprKind::Pi(..)),
            "{name}: expected Sort or Pi type, got {ty:?}"
        );
    }
}

// ============================================================================
// DifferentialEquations Module Tests
// ============================================================================
