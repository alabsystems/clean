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
fn test_real_complex_analysis_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_real_complex_analysis());
    env.init_real_complex_analysis().unwrap();
    assert!(env.has_real_complex_analysis());
}

#[test]
fn test_real_complex_analysis_idempotent() {
    let mut env = Environment::new();
    env.init_real_complex_analysis().unwrap();
    env.init_real_complex_analysis().unwrap();
    assert!(env.has_real_complex_analysis());
}

#[test]
fn test_real_number_construction_exists() {
    let mut env = Environment::new();
    env.init_real_complex_analysis().unwrap();

    let construction_names = [
        "Real",
        "Real.ofRat",
        "Real.ofNat",
        "Real.ofInt",
        "Real.DedekindCut",
        "Real.CauchySeq",
        "Real.CauchySeq.equiv",
    ];

    for name in &construction_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_real_field_axioms_exist() {
    let mut env = Environment::new();
    env.init_real_complex_analysis().unwrap();

    let field_axioms = [
        "Real.add",
        "Real.mul",
        "Real.neg",
        "Real.inv",
        "Real.add_comm",
        "Real.add_assoc",
        "Real.mul_comm",
        "Real.mul_assoc",
        "Real.distrib",
        "Real.zero_ne_one",
    ];

    for name in &field_axioms {
        assert_const(&env, name);
    }
}

#[test]
fn test_real_completeness_exists() {
    let mut env = Environment::new();
    env.init_real_complex_analysis().unwrap();

    let completeness_names = [
        "Real.sup",
        "Real.inf",
        "Real.completeness",
        "Real.archimedean",
        "Real.bolzano_weierstrass",
        "Real.heine_borel",
        "Real.monotone_convergence",
    ];

    for name in &completeness_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_real_limits_continuity_exist() {
    let mut env = Environment::new();
    env.init_real_complex_analysis().unwrap();

    let limit_names = [
        "Real.Limit",
        "Real.Limit.def",
        "Real.Continuous",
        "Real.UniformlyContinuous",
        "Real.IVT",
        "Real.EVT",
    ];

    for name in &limit_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_real_sequences_series_exist() {
    let mut env = Environment::new();
    env.init_real_complex_analysis().unwrap();

    let seq_names = [
        "Real.Seq",
        "Real.Seq.Convergent",
        "Real.Seq.Cauchy",
        "Real.Series",
        "Real.Series.AbsolutelyConvergent",
        "Real.Series.RatioTest",
        "Real.PowerSeries",
    ];

    for name in &seq_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_real_differentiation_exist() {
    let mut env = Environment::new();
    env.init_real_complex_analysis().unwrap();

    let diff_names = [
        "Real.Differentiable",
        "Real.Derivative",
        "Real.Derivative.chain",
        "Real.MVT",
        "Real.Rolle",
        "Real.Taylor",
        "Real.LHopital",
    ];

    for name in &diff_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_real_integration_exist() {
    let mut env = Environment::new();
    env.init_real_complex_analysis().unwrap();

    let int_names = [
        "Real.Integral",
        "Real.RiemannIntegrable",
        "Real.FTC1",
        "Real.FTC2",
        "Real.IntegrationByParts",
        "Real.Substitution",
    ];

    for name in &int_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_complex_numbers_exist() {
    let mut env = Environment::new();
    env.init_real_complex_analysis().unwrap();

    let complex_names = [
        "Complex",
        "Complex.re",
        "Complex.im",
        "Complex.I",
        "Complex.I_sq",
        "Complex.conj",
        "Complex.abs",
        "Complex.field",
        "Complex.algebraically_closed",
    ];

    for name in &complex_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_complex_exp_trig_exist() {
    let mut env = Environment::new();
    env.init_real_complex_analysis().unwrap();

    let exp_trig_names = [
        "Complex.exp",
        "Complex.log",
        "Complex.sin",
        "Complex.cos",
        "Complex.euler_formula",
        "Complex.euler_identity",
        "Complex.de_moivre",
    ];

    for name in &exp_trig_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_complex_analysis_holomorphic_exist() {
    let mut env = Environment::new();
    env.init_real_complex_analysis().unwrap();

    let holo_names = [
        "Complex.Holomorphic",
        "Complex.CauchyRiemann",
        "Complex.Analytic",
        "Complex.EntireFunction",
        "Complex.Meromorphic",
        "Complex.Singularity.Pole",
    ];

    for name in &holo_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_complex_integration_theorems_exist() {
    let mut env = Environment::new();
    env.init_real_complex_analysis().unwrap();

    let int_names = [
        "Complex.ContourIntegral",
        "Complex.CauchyTheorem",
        "Complex.CauchyIntegralFormula",
        "Complex.ResidueTheorem",
        "Complex.Residue",
        "Complex.Rouche",
    ];

    for name in &int_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_complex_series_exist() {
    let mut env = Environment::new();
    env.init_real_complex_analysis().unwrap();

    let series_names = [
        "Complex.PowerSeries",
        "Complex.LaurentSeries",
        "Complex.TaylorExpansion",
        "Complex.MaximumModulusPrinciple",
        "Complex.SchwarzLemma",
        "Complex.Liouville",
        "Complex.FTA",
    ];

    for name in &series_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_conformal_mappings_exist() {
    let mut env = Environment::new();
    env.init_real_complex_analysis().unwrap();

    let conformal_names = [
        "Complex.ConformalMap",
        "Complex.BiholomorphicMap",
        "Complex.RiemannMappingTheorem",
        "Complex.MobiusTransformation",
        "Complex.Mobius.cross_ratio",
    ];

    for name in &conformal_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_special_functions_exist() {
    let mut env = Environment::new();
    env.init_real_complex_analysis().unwrap();

    let special_names = [
        "Real.exp",
        "Real.log",
        "Real.sin",
        "Real.cos",
        "Real.Gamma",
        "Real.Beta",
        "Complex.Zeta",
        "Complex.Zeta.euler_product",
    ];

    for name in &special_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_advanced_analysis_exist() {
    let mut env = Environment::new();
    env.init_real_complex_analysis().unwrap();

    let advanced_names = [
        "Real.UniformConvergence",
        "Real.ArzelaAscoli",
        "Real.StoneWeierstrass",
        "Complex.WeierstrassFactorization",
        "Complex.MittagLeffler",
        "Complex.Picard",
    ];

    for name in &advanced_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_real_complex_analysis_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_real_complex_analysis().unwrap();
    // RealComplexAnalysis depends on metric_space and topological_space
    assert!(env.has_metric_space());
    assert!(env.has_topological_space());
}

#[test]
fn test_real_complex_analysis_key_types_well_formed() {
    use crate::expr::ExprKind;
    use crate::level::Level;
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_real_complex_analysis().unwrap();
    let tc = TypeChecker::new(&env);

    for name in &["Real", "Complex", "Real.Derivative", "Complex.Holomorphic"] {
        // Real is declared with zero level params; all others take one
        let levels = if *name == "Real" {
            vec![]
        } else {
            vec![Level::zero()]
        };
        let expr = Expr::const_(Name::from_string(name), levels);
        let ty = tc
            .infer_type(&expr)
            .unwrap_or_else(|e| panic!("{name}: tc.infer_type failed: {e}"));
        assert!(
            matches!(&ty.kind, ExprKind::Sort(_) | ExprKind::Pi(..)),
            "{name}: expected Sort or Pi type, got {ty:?}"
        );
    }
}
