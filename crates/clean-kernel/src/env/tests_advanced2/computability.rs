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
fn test_computability_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_computability());
    env.init_computability().unwrap();
    assert!(env.has_computability());
}

#[test]
fn test_computability_idempotent() {
    let mut env = Environment::new();
    env.init_computability().unwrap();
    env.init_computability().unwrap();
    assert!(env.has_computability());
}

#[test]
fn test_computability_turing_machines_exist() {
    let mut env = Environment::new();
    env.init_computability().unwrap();

    let tm_names = [
        "Computability.TuringMachine",
        "Computability.TMState",
        "Computability.TMTape",
        "Computability.TMTransition",
        "Computability.TMComputes",
        "Computability.TMHalts",
        "Computability.TMAccepts",
        "Computability.TMRejects",
        "Computability.TMDiverges",
        "Computability.UniversalTM",
    ];

    for name in tm_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_computability_decidability_exist() {
    let mut env = Environment::new();
    env.init_computability().unwrap();

    let dec_names = [
        "Computability.Computable",
        "Computability.PartialComputable",
        "Computability.TotalComputable",
        "Computability.Decidable",
        "Computability.SemiDecidable",
        "Computability.Undecidable",
        "Computability.CoSemiDecidable",
    ];

    for name in dec_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_computability_recursive_sets_exist() {
    let mut env = Environment::new();
    env.init_computability().unwrap();

    let rec_names = [
        "Computability.PrimitiveRecursive",
        "Computability.MuRecursive",
        "Computability.RecursiveSet",
        "Computability.RecursivelyEnumerable",
        "Computability.Creative",
        "Computability.Simple",
        "Computability.Immune",
    ];

    for name in rec_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_computability_fundamental_theorems_exist() {
    let mut env = Environment::new();
    env.init_computability().unwrap();

    let thm_names = [
        "Computability.HaltingProblem",
        "Computability.HaltingUndecidable",
        "Computability.RicesTheorem",
        "Computability.PostsTheorem",
        "Computability.SmnTheorem",
        "Computability.RecursionTheorem",
        "Computability.FixedPointTheorem",
        "Computability.EnumerationTheorem",
    ];

    for name in thm_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_computability_reductions_exist() {
    let mut env = Environment::new();
    env.init_computability().unwrap();

    let red_names = [
        "Computability.ManyOneReducible",
        "Computability.TuringReducible",
        "Computability.TruthTableReducible",
        "Computability.TuringDegree",
        "Computability.JumpOperator",
        "Computability.DegreeZero",
        "Computability.DegreeZeroPrime",
    ];

    for name in red_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_computability_arithmetic_hierarchy_exist() {
    let mut env = Environment::new();
    env.init_computability().unwrap();

    let ah_names = [
        "Computability.Sigma0",
        "Computability.Pi0",
        "Computability.Delta0",
        "Computability.ArithmeticHierarchy",
    ];

    for name in ah_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_computability_complexity_time_exist() {
    let mut env = Environment::new();
    env.init_computability().unwrap();

    let time_names = [
        "Computability.TIME",
        "Computability.DTIME",
        "Computability.NTIME",
        "Computability.P",
        "Computability.NP",
        "Computability.coNP",
        "Computability.EXP",
        "Computability.EXPTIME",
    ];

    for name in time_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_computability_complexity_space_exist() {
    let mut env = Environment::new();
    env.init_computability().unwrap();

    let space_names = [
        "Computability.SPACE",
        "Computability.DSPACE",
        "Computability.NSPACE",
        "Computability.L",
        "Computability.NL",
        "Computability.PSPACE",
        "Computability.EXPSPACE",
    ];

    for name in space_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_computability_np_completeness_exist() {
    let mut env = Environment::new();
    env.init_computability().unwrap();

    let npc_names = [
        "Computability.NPComplete",
        "Computability.NPHard",
        "Computability.PolynomialReduction",
        "Computability.CookLevinTheorem",
        "Computability.PSPACEComplete",
    ];

    for name in npc_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_computability_randomized_exist() {
    let mut env = Environment::new();
    env.init_computability().unwrap();

    let rand_names = [
        "Computability.BPP",
        "Computability.RP",
        "Computability.coRP",
        "Computability.ZPP",
        "Computability.PP",
    ];

    for name in rand_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_computability_circuit_exist() {
    let mut env = Environment::new();
    env.init_computability().unwrap();

    let circuit_names = [
        "Computability.BooleanCircuit",
        "Computability.CircuitSize",
        "Computability.CircuitDepth",
        "Computability.AC0",
        "Computability.NC",
        "Computability.NC1",
    ];

    for name in circuit_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_computability_kolmogorov_exist() {
    let mut env = Environment::new();
    env.init_computability().unwrap();

    let kolm_names = [
        "Computability.KolmogorovComplexity",
        "Computability.ConditionalComplexity",
        "Computability.PrefixComplexity",
        "Computability.Incompressible",
        "Computability.InvariantTheorem",
    ];

    for name in kolm_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_computability_lambda_calculus_exist() {
    let mut env = Environment::new();
    env.init_computability().unwrap();

    let lambda_names = [
        "Computability.LambdaTerm",
        "Computability.BetaReduction",
        "Computability.BetaNormalForm",
        "Computability.ChurchNumeral",
        "Computability.YCombinator",
        "Computability.SKCombinator",
    ];

    for name in lambda_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_computability_oracle_exist() {
    let mut env = Environment::new();
    env.init_computability().unwrap();

    let oracle_names = [
        "Computability.OracleTM",
        "Computability.RelativizedComputation",
        "Computability.OracleP",
        "Computability.OracleNP",
        "Computability.BakerGillSolovay",
    ];

    for name in oracle_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_computability_interactive_proofs_exist() {
    let mut env = Environment::new();
    env.init_computability().unwrap();

    let ip_names = [
        "Computability.IP",
        "Computability.AM",
        "Computability.MA",
        "Computability.IPequalsPSPACE",
        "Computability.PCP",
        "Computability.PCPTheorem",
    ];

    for name in ip_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_computability_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_computability().unwrap();
    assert!(env.has_nat());
    // init_logic_types should have been called
}

#[test]
fn test_computability_constant_count() {
    let mut env = Environment::new();
    let before = env.constants.len();
    env.init_computability().unwrap();
    let after = env.constants.len();

    // Expect ~150+ constants for computability plus dependencies
    let comp_count = after - before;
    assert!(
        comp_count >= 100,
        "Expected at least 100 new constants for computability (including deps), got {comp_count}"
    );
}

#[test]
fn test_computability_key_types_well_formed() {
    use crate::expr::ExprKind;
    use crate::level::Level;
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_computability().unwrap();
    let tc = TypeChecker::new(&env);

    for name in &[
        "Computability.TuringMachine",
        "Computability.HaltingProblem",
        "Computability.P",
        "Computability.NP",
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
// Set Theory Tests
// ============================================================================
