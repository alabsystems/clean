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
fn test_set_theory_initialization() {
    let mut env = Environment::new();
    assert!(!env.has_set_theory());
    env.init_set_theory().unwrap();
    assert!(env.has_set_theory());
}

#[test]
fn test_set_theory_idempotent() {
    let mut env = Environment::new();
    env.init_set_theory().unwrap();
    env.init_set_theory().unwrap();
    assert!(env.has_set_theory());
}

#[test]
fn test_set_theory_ordinals_exist() {
    let mut env = Environment::new();
    env.init_set_theory().unwrap();

    let ordinal_names = [
        "SetTheory.Ordinal",
        "SetTheory.OrdinalZero",
        "SetTheory.OrdinalSucc",
        "SetTheory.OrdinalLimit",
        "SetTheory.OrdinalLt",
        "SetTheory.OrdinalLe",
        "SetTheory.Mathverse",
        "SetTheory.MathverseOne",
        "SetTheory.Epsilon0",
    ];

    for name in ordinal_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_set_theory_ordinal_arithmetic_exist() {
    let mut env = Environment::new();
    env.init_set_theory().unwrap();

    let arith_names = [
        "SetTheory.OrdinalAdd",
        "SetTheory.OrdinalMul",
        "SetTheory.OrdinalExp",
        "SetTheory.OrdinalAddAssoc",
        "SetTheory.CantorNormalForm",
    ];

    for name in arith_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_set_theory_cardinals_exist() {
    let mut env = Environment::new();
    env.init_set_theory().unwrap();

    let cardinal_names = [
        "SetTheory.Cardinal",
        "SetTheory.CardinalZero",
        "SetTheory.CardinalOne",
        "SetTheory.CardinalFinite",
        "SetTheory.CardinalInfinite",
        "SetTheory.CardinalCountable",
        "SetTheory.CardinalUncountable",
        "SetTheory.Cardinality",
    ];

    for name in cardinal_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_set_theory_aleph_numbers_exist() {
    let mut env = Environment::new();
    env.init_set_theory().unwrap();

    let aleph_names = [
        "SetTheory.Aleph",
        "SetTheory.Aleph0",
        "SetTheory.Aleph1",
        "SetTheory.AlephSucc",
        "SetTheory.AlephLimit",
        "SetTheory.AlephMonotone",
    ];

    for name in aleph_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_set_theory_beth_numbers_exist() {
    let mut env = Environment::new();
    env.init_set_theory().unwrap();

    let beth_names = [
        "SetTheory.Beth",
        "SetTheory.Beth0",
        "SetTheory.BethSucc",
        "SetTheory.BethLimit",
    ];

    for name in beth_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_set_theory_continuum_exist() {
    let mut env = Environment::new();
    env.init_set_theory().unwrap();

    let ch_names = [
        "SetTheory.Continuum",
        "SetTheory.ContinuumHypothesis",
        "SetTheory.GeneralizedCH",
        "SetTheory.CHIndependent",
    ];

    for name in ch_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_set_theory_well_orderings_exist() {
    let mut env = Environment::new();
    env.init_set_theory().unwrap();

    let wo_names = [
        "SetTheory.WellOrder",
        "SetTheory.WellFounded",
        "SetTheory.IsWellOrder",
        "SetTheory.OrderType",
        "SetTheory.InitialSegment",
        "SetTheory.WellOrderingTheorem",
        "SetTheory.HartogNumber",
    ];

    for name in wo_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_set_theory_axiom_of_choice_exist() {
    let mut env = Environment::new();
    env.init_set_theory().unwrap();

    let ac_names = [
        "SetTheory.AxiomOfChoice",
        "SetTheory.WellOrderingPrinciple",
        "SetTheory.ZornsLemma",
        "SetTheory.ZornsLemmaEquivAC",
        "SetTheory.CountableChoice",
        "SetTheory.DependentChoice",
    ];

    for name in ac_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_set_theory_transfinite_induction_exist() {
    let mut env = Environment::new();
    env.init_set_theory().unwrap();

    let tfi_names = [
        "SetTheory.TransfiniteInduction",
        "SetTheory.TransfiniteRecursion",
        "SetTheory.OrdinalInduction",
        "SetTheory.WellFoundedInduction",
        "SetTheory.BuraliForti",
    ];

    for name in tfi_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_set_theory_zfc_axioms_exist() {
    let mut env = Environment::new();
    env.init_set_theory().unwrap();

    let zfc_names = [
        "SetTheory.AxiomExtensionality",
        "SetTheory.AxiomEmptySet",
        "SetTheory.AxiomPairing",
        "SetTheory.AxiomUnion",
        "SetTheory.AxiomPowerSet",
        "SetTheory.AxiomInfinity",
        "SetTheory.AxiomSeparation",
        "SetTheory.AxiomReplacement",
        "SetTheory.AxiomRegularity",
        "SetTheory.ZF",
        "SetTheory.ZFC",
    ];

    for name in zfc_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_set_theory_large_cardinals_weak_exist() {
    let mut env = Environment::new();
    env.init_set_theory().unwrap();

    let lc_names = [
        "SetTheory.Inaccessible",
        "SetTheory.WeaklyInaccessible",
        "SetTheory.StronglyInaccessible",
        "SetTheory.Mahlo",
    ];

    for name in lc_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_set_theory_large_cardinals_strong_exist() {
    let mut env = Environment::new();
    env.init_set_theory().unwrap();

    let lc_names = [
        "SetTheory.Measurable",
        "SetTheory.Supercompact",
        "SetTheory.Extendible",
        "SetTheory.Huge",
    ];

    for name in lc_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_set_theory_inner_models_exist() {
    let mut env = Environment::new();
    env.init_set_theory().unwrap();

    let model_names = [
        "SetTheory.ConstructibleUniverse",
        "SetTheory.VEqualsL",
        "SetTheory.RelativeConsistency",
        "SetTheory.GoedelConsistency",
        "SetTheory.CohenForcing",
    ];

    for name in model_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_set_theory_descriptive_exist() {
    let mut env = Environment::new();
    env.init_set_theory().unwrap();

    let desc_names = [
        "SetTheory.BorelSet",
        "SetTheory.AnalyticSet",
        "SetTheory.ProjectiveSet",
        "SetTheory.AxiomOfDeterminacy",
        "SetTheory.PerfectSetProperty",
    ];

    for name in desc_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_set_theory_combinatorial_exist() {
    let mut env = Environment::new();
    env.init_set_theory().unwrap();

    let comb_names = [
        "SetTheory.RamseyTheorem",
        "SetTheory.TreeProperty",
        "SetTheory.AronszajnTree",
        "SetTheory.ClubFilter",
        "SetTheory.StationarySet",
        "SetTheory.FodorsLemma",
        "SetTheory.MartinsAxiom",
    ];

    for name in comb_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_set_theory_fundamental_theorems_exist() {
    let mut env = Environment::new();
    env.init_set_theory().unwrap();

    let thm_names = [
        "SetTheory.SchroederBernstein",
        "SetTheory.CantorTheorem",
        "SetTheory.CantorDiagonal",
        "SetTheory.KoenigsTheorem",
    ];

    for name in thm_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_set_theory_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_set_theory().unwrap();
    // Should have initialized dependencies
    assert!(env.has_eq());
    assert!(env.has_nat());
}

#[test]
fn test_set_theory_constant_count() {
    let mut env = Environment::new();
    let before = env.constants.len();
    env.init_set_theory().unwrap();
    let after = env.constants.len();

    // Expect ~150+ constants for set theory plus dependencies
    let st_count = after - before;
    assert!(
        st_count >= 100,
        "Expected at least 100 new constants for set theory (including deps), got {st_count}"
    );
}

#[test]
fn test_set_theory_key_types_well_formed() {
    use crate::expr::ExprKind;
    use crate::level::Level;
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_set_theory().unwrap();
    let tc = TypeChecker::new(&env);

    for name in &[
        "SetTheory.ZF",
        "SetTheory.Ordinal",
        "SetTheory.Cardinal",
        "SetTheory.ContinuumHypothesis",
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

// =============================================================================
// Stochastic Processes Tests
// =============================================================================
