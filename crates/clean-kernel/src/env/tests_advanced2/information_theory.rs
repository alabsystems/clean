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
fn test_information_theory_entropy_and_divergence_constants_exist() {
    let mut env = Environment::new();
    env.init_information_theory().unwrap();

    let entropy_names = [
        "InformationTheory.Entropy",
        "InformationTheory.JointEntropy",
        "InformationTheory.ConditionalEntropy",
        "InformationTheory.MutualInformation",
        "InformationTheory.ConditionalMutualInformation",
        "InformationTheory.DataProcessing",
        "InformationTheory.KLDivergence",
        "InformationTheory.GibbsInequality",
        "InformationTheory.JensenShannon",
        "InformationTheory.PinskerInequality",
        "InformationTheory.EntropyPowerInequality",
    ];

    for name in &entropy_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_information_theory_coding_theorems_exist() {
    let mut env = Environment::new();
    env.init_information_theory().unwrap();

    let coding_names = [
        "InformationTheory.DiscreteMemorylessChannel",
        "InformationTheory.ChannelCapacity",
        "InformationTheory.ChannelCodingTheorem",
        "InformationTheory.SpherePackingBound",
        "InformationTheory.RandomCoding",
        "InformationTheory.TypicalSetDecoder",
        "InformationTheory.KraftInequality",
        "InformationTheory.SourceCodingTheorem",
        "InformationTheory.RateDistortionTheorem",
        "InformationTheory.BlahutArimoto",
    ];

    for name in &coding_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_information_theory_multiuser_and_learning_constants_exist() {
    let mut env = Environment::new();
    env.init_information_theory().unwrap();

    let multiuser_names = [
        "InformationTheory.MultipleAccessChannel",
        "InformationTheory.MACCapacityRegion",
        "InformationTheory.BroadcastChannel",
        "InformationTheory.BroadcastCapacity",
        "InformationTheory.InterferenceChannel",
        "InformationTheory.HanKobayashiRegion",
        "InformationTheory.SlepianWolf",
        "InformationTheory.WynerZiv",
        "InformationTheory.InformationBottleneck",
        "InformationTheory.InfoNCE",
    ];

    for name in &multiuser_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_information_theory_key_types_well_formed() {
    use crate::expr::ExprKind;
    use crate::level::Level;
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_information_theory().unwrap();
    let tc = TypeChecker::new(&env);

    for name in &[
        "InformationTheory.Entropy",
        "InformationTheory.KLDivergence",
        "InformationTheory.ChannelCapacity",
        "InformationTheory.MutualInformation",
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
// Formal Logic Tests
// ============================================================================
