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
fn test_formal_logic_propositional_syntax_exist() {
    let mut env = Environment::new();
    env.init_formal_logic().unwrap();

    let prop_syntax_names = [
        "FormalLogic.PropFormula",
        "FormalLogic.PropVar",
        "FormalLogic.PropTop",
        "FormalLogic.PropBot",
        "FormalLogic.PropNeg",
        "FormalLogic.PropAnd",
        "FormalLogic.PropOr",
        "FormalLogic.PropImpl",
        "FormalLogic.PropIff",
        "FormalLogic.PropNand",
        "FormalLogic.PropXor",
        "FormalLogic.PropSubformula",
    ];

    for name in &prop_syntax_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_formal_logic_propositional_semantics_exist() {
    let mut env = Environment::new();
    env.init_formal_logic().unwrap();

    let prop_sem_names = [
        "FormalLogic.PropValuation",
        "FormalLogic.PropEval",
        "FormalLogic.PropSatisfies",
        "FormalLogic.PropTautology",
        "FormalLogic.PropContradiction",
        "FormalLogic.PropSatisfiable",
        "FormalLogic.PropEquivalent",
        "FormalLogic.PropEntails",
        "FormalLogic.PropModel",
    ];

    for name in &prop_sem_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_formal_logic_normal_forms_exist() {
    let mut env = Environment::new();
    env.init_formal_logic().unwrap();

    let nf_names = [
        "FormalLogic.NNF",
        "FormalLogic.CNF",
        "FormalLogic.DNF",
        "FormalLogic.Clause",
        "FormalLogic.Literal",
        "FormalLogic.TseitinTransform",
        "FormalLogic.CNFPreservesEquisat",
    ];

    for name in &nf_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_formal_logic_proof_systems_exist() {
    let mut env = Environment::new();
    env.init_formal_logic().unwrap();

    let proof_names = [
        "FormalLogic.PropModusPonens",
        "FormalLogic.PropDeduction",
        "FormalLogic.PropNaturalDeduction",
        "FormalLogic.PropNDAndIntro",
        "FormalLogic.PropNDOrElim",
        "FormalLogic.PropNDImplIntro",
        "FormalLogic.PropSequent",
        "FormalLogic.PropLK",
        "FormalLogic.PropCutElimination",
    ];

    for name in &proof_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_formal_logic_sat_exist() {
    let mut env = Environment::new();
    env.init_formal_logic().unwrap();

    let sat_names = [
        "FormalLogic.SAT",
        "FormalLogic.UNSAT",
        "FormalLogic.SATNPComplete",
        "FormalLogic.DPLL",
        "FormalLogic.UnitPropagation",
        "FormalLogic.CDCL",
        "FormalLogic.Resolution",
        "FormalLogic.ResolutionComplete",
        "FormalLogic.ResolutionSound",
    ];

    for name in &sat_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_formal_logic_first_order_syntax_exist() {
    let mut env = Environment::new();
    env.init_formal_logic().unwrap();

    let fol_syntax_names = [
        "FormalLogic.FOTerm",
        "FormalLogic.FOVariable",
        "FormalLogic.FOConstant",
        "FormalLogic.FOFunction",
        "FormalLogic.FOFormula",
        "FormalLogic.FOPredicate",
        "FormalLogic.FOEquality",
        "FormalLogic.FOForall",
        "FormalLogic.FOExists",
        "FormalLogic.FOSignature",
        "FormalLogic.FOFreeVars",
        "FormalLogic.FOSentence",
        "FormalLogic.FOSubstitution",
    ];

    for name in &fol_syntax_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_formal_logic_first_order_semantics_exist() {
    let mut env = Environment::new();
    env.init_formal_logic().unwrap();

    let fol_sem_names = [
        "FormalLogic.FOStructure",
        "FormalLogic.FODomain",
        "FormalLogic.FOInterpretation",
        "FormalLogic.FOAssignment",
        "FormalLogic.FOTermEval",
        "FormalLogic.FOSatisfaction",
        "FormalLogic.FOValid",
        "FormalLogic.FOSatisfiable",
        "FormalLogic.FOEntails",
        "FormalLogic.FOTheory",
        "FormalLogic.FOModelOf",
    ];

    for name in &fol_sem_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_formal_logic_metatheory_exist() {
    let mut env = Environment::new();
    env.init_formal_logic().unwrap();

    let meta_names = [
        "FormalLogic.FOSoundness",
        "FormalLogic.FOCompleteness",
        "FormalLogic.FOCompactness",
        "FormalLogic.FOLowenheimSkolem",
        "FormalLogic.FOCraigInterpolation",
        "FormalLogic.FOBethDefinability",
        "FormalLogic.HerbrandTheorem",
        "FormalLogic.FOUnification",
        "FormalLogic.FOMGU",
    ];

    for name in &meta_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_formal_logic_model_theory_exist() {
    let mut env = Environment::new();
    env.init_formal_logic().unwrap();

    let model_names = [
        "FormalLogic.MTElementaryEquiv",
        "FormalLogic.MTIsomorphism",
        "FormalLogic.MTElementarySubstr",
        "FormalLogic.MTType",
        "FormalLogic.MTCompleteType",
        "FormalLogic.MTSaturated",
        "FormalLogic.MTComplete",
        "FormalLogic.MTCategorical",
        "FormalLogic.MTQuantifierElim",
        "FormalLogic.MTUltraproduct",
        "FormalLogic.MTLosTheorem",
    ];

    for name in &model_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_formal_logic_modal_logic_exist() {
    let mut env = Environment::new();
    env.init_formal_logic().unwrap();

    let modal_names = [
        "FormalLogic.ModalFormula",
        "FormalLogic.ModalBox",
        "FormalLogic.ModalDiamond",
        "FormalLogic.KripkeFrame",
        "FormalLogic.KripkeModel",
        "FormalLogic.Accessibility",
        "FormalLogic.KripkeSatisfaction",
        "FormalLogic.ModalK",
        "FormalLogic.ModalKAxiom",
        "FormalLogic.ModalT",
        "FormalLogic.ModalS4",
        "FormalLogic.ModalS5",
        "FormalLogic.ModalGL",
        "FormalLogic.SahlqvistCorr",
    ];

    for name in &modal_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_formal_logic_temporal_logic_exist() {
    let mut env = Environment::new();
    env.init_formal_logic().unwrap();

    let temporal_names = [
        "FormalLogic.LTL",
        "FormalLogic.LTLNext",
        "FormalLogic.LTLUntil",
        "FormalLogic.LTLGlobally",
        "FormalLogic.LTLFinally",
        "FormalLogic.LTLSemantics",
        "FormalLogic.CTL",
        "FormalLogic.CTLStar",
        "FormalLogic.LTLModelCheck",
        "FormalLogic.BuchiAutomaton",
        "FormalLogic.LTLToBuchi",
    ];

    for name in &temporal_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_formal_logic_nonclassical_exist() {
    let mut env = Environment::new();
    env.init_formal_logic().unwrap();

    let nonclass_names = [
        "FormalLogic.IntLogic",
        "FormalLogic.IntKripkeModel",
        "FormalLogic.IntDoubleNegTrans",
        "FormalLogic.IntGlivenko",
        "FormalLogic.IntCurryHoward",
        "FormalLogic.LinearLogic",
        "FormalLogic.LinearTensor",
        "FormalLogic.LinearBang",
        "FormalLogic.FuzzyLogic",
        "FormalLogic.GodelLogic",
    ];

    for name in &nonclass_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_formal_logic_atp_exist() {
    let mut env = Environment::new();
    env.init_formal_logic().unwrap();

    let atp_names = [
        "FormalLogic.ATPResolution",
        "FormalLogic.ATPParamodulation",
        "FormalLogic.ATPSuperposition",
        "FormalLogic.ATPTableaux",
        "FormalLogic.ATPConnectionMethod",
    ];

    for name in &atp_names {
        assert_const(&env, name);
    }
}

#[test]
fn test_formal_logic_key_types_well_formed() {
    use crate::expr::ExprKind;
    use crate::level::Level;
    use crate::tc::TypeChecker;

    let mut env = Environment::new();
    env.init_formal_logic().unwrap();
    let tc = TypeChecker::new(&env);

    for name in &[
        "FormalLogic.PropFormula",
        "FormalLogic.FOFormula",
        "FormalLogic.KripkeFrame",
        "FormalLogic.LTL",
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
// Cryptography Module Tests
// ============================================================================
