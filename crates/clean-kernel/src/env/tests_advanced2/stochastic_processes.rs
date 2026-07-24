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
fn test_stochastic_processes_init() {
    let mut env = Environment::new();
    assert!(!env.has_stochastic_processes());
    env.init_stochastic_processes().unwrap();
    assert!(env.has_stochastic_processes());
}

#[test]
fn test_stochastic_processes_idempotent() {
    let mut env = Environment::new();
    env.init_stochastic_processes().unwrap();
    let count_after_first = env.constants.len();
    env.init_stochastic_processes().unwrap();
    let count_after_second = env.constants.len();
    assert_eq!(count_after_first, count_after_second);
}

#[test]
fn test_stochastic_processes_markov_chains_exist() {
    let mut env = Environment::new();
    env.init_stochastic_processes().unwrap();

    let mc_names = [
        "StochasticProcess.MarkovChain",
        "StochasticProcess.MarkovProperty",
        "StochasticProcess.TransitionMatrix",
        "StochasticProcess.StationaryDistribution",
        "StochasticProcess.ChapmanKolmogorov",
        "StochasticProcess.Irreducible",
        "StochasticProcess.Aperiodic",
        "StochasticProcess.Ergodic",
        "StochasticProcess.DetailedBalance",
        "StochasticProcess.Reversible",
    ];

    for name in &mc_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_stochastic_processes_ctmc_exist() {
    let mut env = Environment::new();
    env.init_stochastic_processes().unwrap();

    let ctmc_names = [
        "StochasticProcess.CTMC",
        "StochasticProcess.Generator",
        "StochasticProcess.HoldingTime",
        "StochasticProcess.JumpChain",
        "StochasticProcess.KolmogorovForward",
        "StochasticProcess.KolmogorovBackward",
        "StochasticProcess.BirthDeathProcess",
    ];

    for name in &ctmc_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_stochastic_processes_concentration_inequalities_exist() {
    let mut env = Environment::new();
    env.init_stochastic_processes().unwrap();

    // Critical for ML bounds
    let concentration_names = [
        "StochasticProcess.MarkovInequality",
        "StochasticProcess.ChebyshevInequality",
        "StochasticProcess.ChernoffBound",
        "StochasticProcess.HoeffdingLemma",
        "StochasticProcess.HoeffdingInequality",
        "StochasticProcess.AzumaHoeffding",
        "StochasticProcess.McDiarmid",
        "StochasticProcess.ChernoffMultiplicative",
        "StochasticProcess.ChernoffAdditive",
        "StochasticProcess.bernstein_inequality",
        "StochasticProcess.bennett_inequality",
        "StochasticProcess.SubGaussian",
        "StochasticProcess.SubExponential",
    ];

    for name in &concentration_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_stochastic_processes_ml_bounds_exist() {
    let mut env = Environment::new();
    env.init_stochastic_processes().unwrap();

    // PAC learning and empirical process theory
    let ml_names = [
        "StochasticProcess.VC_dimension",
        "StochasticProcess.shattering",
        "StochasticProcess.vc_generalization",
        "StochasticProcess.Rademacher",
        "StochasticProcess.rademacher_bound",
        "StochasticProcess.EmpiricalMeasure",
        "StochasticProcess.EmpiricalProcess",
        "StochasticProcess.GlivenkoCantelli",
        "StochasticProcess.DKW_inequality",
        "StochasticProcess.CoveringNumber",
        "StochasticProcess.MetricEntropy",
    ];

    for name in &ml_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_stochastic_processes_brownian_motion_exist() {
    let mut env = Environment::new();
    env.init_stochastic_processes().unwrap();

    let bm_names = [
        "StochasticProcess.BrownianMotion",
        "StochasticProcess.bm_continuous",
        "StochasticProcess.bm_independent_increments",
        "StochasticProcess.bm_gaussian_increments",
        "StochasticProcess.bm_quadratic_variation",
        "StochasticProcess.bm_martingale",
        "StochasticProcess.GeometricBM",
        "StochasticProcess.OrnsteinUhlenbeck",
    ];

    for name in &bm_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_stochastic_processes_ito_calculus_exist() {
    let mut env = Environment::new();
    env.init_stochastic_processes().unwrap();

    let ito_names = [
        "StochasticProcess.ItoIntegral",
        "StochasticProcess.ito_isometry",
        "StochasticProcess.ItoProcess",
        "StochasticProcess.ItoFormula",
        "StochasticProcess.ito_product_rule",
        "StochasticProcess.QuadraticCovariation",
        "StochasticProcess.Semimartingale",
        "StochasticProcess.SDE",
        "StochasticProcess.Girsanov",
        "StochasticProcess.FeynmanKac",
    ];

    for name in &ito_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_stochastic_processes_queueing_theory_exist() {
    let mut env = Environment::new();
    env.init_stochastic_processes().unwrap();

    let queue_names = [
        "StochasticProcess.Queue",
        "StochasticProcess.MM1Queue",
        "StochasticProcess.MMcQueue",
        "StochasticProcess.MG1Queue",
        "StochasticProcess.LittleLaw",
        "StochasticProcess.PASTA",
        "StochasticProcess.JacksonNetwork",
        "StochasticProcess.PollaczekKhintchine",
    ];

    for name in &queue_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_stochastic_processes_levy_processes_exist() {
    let mut env = Environment::new();
    env.init_stochastic_processes().unwrap();

    let levy_names = [
        "StochasticProcess.LevyProcess",
        "StochasticProcess.LevyKhintchine",
        "StochasticProcess.PoissonProcess",
        "StochasticProcess.CompoundPoisson",
        "StochasticProcess.JumpDiffusion",
    ];

    for name in &levy_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_stochastic_processes_random_walks_exist() {
    let mut env = Environment::new();
    env.init_stochastic_processes().unwrap();

    let rw_names = [
        "StochasticProcess.RandomWalk",
        "StochasticProcess.SimpleRandomWalk",
        "StochasticProcess.rw_recurrence",
        "StochasticProcess.rw_transience",
        "StochasticProcess.rw_clt",
        "StochasticProcess.ArcsineLaw",
    ];

    for name in &rw_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_stochastic_processes_renewal_theory_exist() {
    let mut env = Environment::new();
    env.init_stochastic_processes().unwrap();

    let renewal_names = [
        "StochasticProcess.RenewalProcess",
        "StochasticProcess.RenewalEquation",
        "StochasticProcess.ElementaryRenewal",
        "StochasticProcess.BlackwellRenewal",
        "StochasticProcess.KeyRenewalTheorem",
    ];

    for name in &renewal_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_stochastic_processes_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_stochastic_processes().unwrap();
    // Should have initialized dependencies
    assert!(env.has_eq());
    assert!(env.has_nat());
    assert!(env.has_rat());
    assert!(env.has_measure_theory());
}

#[test]
fn test_stochastic_processes_constant_count() {
    let mut env = Environment::new();
    let before = env.constants.len();
    env.init_stochastic_processes().unwrap();
    let after = env.constants.len();

    // Expect significant number of constants
    let sp_count = after - before;
    assert!(
        sp_count >= 100,
        "Expected at least 100 new constants for stochastic processes (including deps), got {sp_count}"
    );
}

#[test]
fn test_stochastic_processes_key_types_well_formed() {
    use crate::expr::ExprKind;
    use crate::level::Level;
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_stochastic_processes().unwrap();
    let tc = TypeChecker::new(&env);

    for name in &[
        "StochasticProcess.MarkovChain",
        "StochasticProcess.BrownianMotion",
        "StochasticProcess.PoissonProcess",
        "StochasticProcess.DoobMartingale",
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
