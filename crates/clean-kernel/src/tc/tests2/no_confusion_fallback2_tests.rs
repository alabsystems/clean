// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! noConfusion fallback sort-level tests for #3208 (part 2):
//! WHNF reduction, axiom-stub replacement, and idempotent regeneration.
//!
//! See `no_confusion_fallback_tests` for the companion regeneration tests
//! and the full rationale.

use super::support::make_nat_env_with_eq;
use super::*;
use crate::env::{ConstantInfo, TrustedEnvExt};
use crate::inductive::{Constructor, InductiveDecl, InductiveType};

/// Helper: create an environment with Nat, Eq, and an opaque constant
/// `OpaqueType : Type` that has no value (simulating an axiom or opaque
/// definition whose sort the TC cannot infer during noConfusion generation).
fn make_env_with_opaque_type() -> Environment {
    let mut env = make_nat_env_with_eq();
    // Register an opaque constant: OpaqueType : Type
    // This has no value, so infer_sort on an application of OpaqueType
    // will fail (can't reduce or unfold).
    let opaque_name = Name::from_string("OpaqueType");
    let opaque_ci = ConstantInfo::new(
        opaque_name,
        vec![],
        Expr::type_(), // OpaqueType : Type
        None,          // No value (axiom-like)
        false,         // Not reducible
    );
    env.extend_constants_unchecked(std::iter::once(opaque_ci));
    env
}

/// Create an inductive that has a constructor field referencing OpaqueType.
///
/// Mimics `Int.Linear.Expr` pattern: a recursive inductive where one
/// constructor has a field of a complex external type.
///
/// ```text
/// inductive FbExpr : Type where
///   | lit : OpaqueType -> FbExpr
///   | add : FbExpr -> FbExpr -> FbExpr
/// ```
fn fb_expr_decl() -> InductiveDecl {
    let fb = Name::from_string("FbExpr");
    let fb_ref = Expr::const_(fb.clone(), vec![]);
    let opaque_ref = Expr::const_(Name::from_string("OpaqueType"), vec![]);
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: fb,
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("FbExpr.lit"),
                    type_: Expr::arrow(opaque_ref, fb_ref.clone()),
                },
                Constructor {
                    name: Name::from_string("FbExpr.add"),
                    type_: Expr::arrow(fb_ref.clone(), Expr::arrow(fb_ref.clone(), fb_ref)),
                },
            ],
        }],
    }
}

/// Create an inductive that has multiple constructors, some with opaque fields.
///
/// Mimics `Lean.ParserDescr` pattern: multiple constructors with a mix of
/// recursive fields, external type fields, and Nat fields.
///
/// ```text
/// inductive FbDescr : Type where
///   | node : OpaqueType -> FbDescr -> FbDescr
///   | atom : Nat -> FbDescr
///   | pair : FbDescr -> FbDescr -> FbDescr
/// ```
fn fb_descr_decl() -> InductiveDecl {
    let fd = Name::from_string("FbDescr");
    let fd_ref = Expr::const_(fd.clone(), vec![]);
    let opaque_ref = Expr::const_(Name::from_string("OpaqueType"), vec![]);
    let nat_ref = Expr::const_(Name::from_string("Nat"), vec![]);
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: fd,
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("FbDescr.node"),
                    type_: Expr::arrow(opaque_ref, Expr::arrow(fd_ref.clone(), fd_ref.clone())),
                },
                Constructor {
                    name: Name::from_string("FbDescr.atom"),
                    type_: Expr::arrow(nat_ref, fd_ref.clone()),
                },
                Constructor {
                    name: Name::from_string("FbDescr.pair"),
                    type_: Expr::arrow(fd_ref.clone(), Expr::arrow(fd_ref.clone(), fd_ref)),
                },
            ],
        }],
    }
}

/// Create a parametric inductive with an opaque field.
///
/// Mimics `DoResultPRBC` pattern: a parametric inductive where a constructor
/// has a field whose sort depends on a type parameter that interacts with
/// an opaque external type.
///
/// ```text
/// inductive FbResult (A : Type u) : Type u where
///   | pure : A -> FbResult A
///   | bind : OpaqueType -> FbResult A -> FbResult A
/// ```
fn fb_result_decl() -> InductiveDecl {
    let u = Name::from_string("u");
    let fr = Name::from_string("FbResult");
    let _fr_applied = Expr::app(
        Expr::const_(fr.clone(), vec![Level::param(u.clone())]),
        Expr::bvar(0), // A
    );
    let opaque_ref = Expr::const_(Name::from_string("OpaqueType"), vec![]);
    let fr_type = Expr::pi(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone())))),
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone())))),
    );
    // pure : (A : Type u) -> A -> FbResult A
    let pure_type = Expr::pi(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone())))),
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0), // A
            Expr::app(
                Expr::const_(fr.clone(), vec![Level::param(u.clone())]),
                Expr::bvar(1), // A
            ),
        ),
    );
    // bind : (A : Type u) -> OpaqueType -> FbResult A -> FbResult A
    let bind_type = Expr::pi(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone())))),
        Expr::pi(
            BinderInfo::Default,
            opaque_ref,
            Expr::pi(
                BinderInfo::Default,
                Expr::app(
                    Expr::const_(fr.clone(), vec![Level::param(u.clone())]),
                    Expr::bvar(1), // A
                ),
                Expr::app(
                    Expr::const_(fr.clone(), vec![Level::param(u.clone())]),
                    Expr::bvar(2), // A
                ),
            ),
        ),
    );
    InductiveDecl {
        level_params: vec![u],
        num_params: 1,
        types: vec![InductiveType {
            name: fr,
            type_: fr_type,
            constructors: vec![
                Constructor {
                    name: Name::from_string("FbResult.pure"),
                    type_: pure_type,
                },
                Constructor {
                    name: Name::from_string("FbResult.bind"),
                    type_: bind_type,
                },
            ],
        }],
    }
}

/// Assert that a named constant's value typechecks.
fn assert_value_typechecks(env: &Environment, name: &str) {
    let tc = TypeChecker::new(env);
    let ci = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} should exist"));
    let value = ci
        .value
        .as_ref()
        .unwrap_or_else(|| panic!("{name} should have a value"));
    match tc.check_type(value, &ci.type_) {
        Ok(()) => {}
        Err(e) => panic!("{name} value failed type check: {e:?}"),
    }
}

/// Test: noConfusionType WHNF reduces to Pi after fallback regeneration.
///
/// After regeneration with fallback, noConfusionType P (lit x) (lit y) must
/// WHNF to a Pi type (specifically (x = y -> P) -> P). If this fails,
/// per-constructor noConfusion bodies would get NotAFunction.
#[test]
fn test_fallback_nct_whnf_reduces_to_pi() {
    let mut env = make_env_with_opaque_type();
    env.add_inductive(fb_expr_decl()).unwrap();

    let nct_name = Name::from_string("FbExpr.noConfusionType");
    let nc_name = Name::from_string("FbExpr.noConfusion");
    env.remove_constant(&nct_name);
    env.remove_constant(&nc_name);
    env.regenerate_missing_no_confusion();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u_nc");
    let nct = Expr::const_(
        Name::from_string("FbExpr.noConfusionType"),
        vec![Level::param(u)],
    );
    // Build: noConfusionType P (lit x) (lit y)
    let lit = Expr::const_(Name::from_string("FbExpr.lit"), vec![]);
    let app_a = Expr::app(lit.clone(), Expr::bvar(1)); // lit x
    let app_b = Expr::app(
        Expr::const_(Name::from_string("FbExpr.lit"), vec![]),
        Expr::bvar(0), // lit y
    );
    let applied = Expr::app(Expr::app(Expr::app(nct, Expr::bvar(2)), app_a), app_b);
    let result = tc.whnf_impl(&applied);
    assert!(
        matches!(result.kind(), ExprKind::Pi(..)),
        "noConfusionType P (lit x) (lit y) should WHNF to Pi, got: {result:?}"
    );
}

/// Test: noConfusionType WHNF reduces for cross-constructor case.
///
/// noConfusionType P (lit x) (add a b) should WHNF to P (different ctors
/// → trivially true via False.elim in the casesOn alternative).
#[test]
fn test_fallback_nct_whnf_cross_ctor() {
    let mut env = make_env_with_opaque_type();
    env.add_inductive(fb_expr_decl()).unwrap();

    let nct_name = Name::from_string("FbExpr.noConfusionType");
    let nc_name = Name::from_string("FbExpr.noConfusion");
    env.remove_constant(&nct_name);
    env.remove_constant(&nc_name);
    env.regenerate_missing_no_confusion();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u_nc");
    let nct = Expr::const_(
        Name::from_string("FbExpr.noConfusionType"),
        vec![Level::param(u)],
    );
    let lit = Expr::const_(Name::from_string("FbExpr.lit"), vec![]);
    let add = Expr::const_(Name::from_string("FbExpr.add"), vec![]);
    let app_a = Expr::app(lit, Expr::bvar(2)); // lit x
    let app_b = Expr::app(Expr::app(add, Expr::bvar(1)), Expr::bvar(0)); // add a b
    let applied = Expr::app(Expr::app(Expr::app(nct, Expr::bvar(3)), app_a), app_b);
    let result = tc.whnf_impl(&applied);
    // Cross-constructor: should reduce, but the exact form depends on whether
    // it reduces fully. At minimum it should not be stuck.
    assert!(
        !matches!(result.kind(), ExprKind::App(..))
            || !matches!(result.get_app_fn().kind(), ExprKind::Const(..)),
        "noConfusionType P (lit x) (add a b) should not be stuck on a Const application, got: {result:?}"
    );
}

/// Test: axiom stub noConfusionType gets replaced by fallback regeneration.
///
/// Simulates the exact .olean loading scenario: an axiom stub (no value)
/// for noConfusionType exists, and regeneration replaces it with a proper
/// definition using fallback sort levels.
#[test]
fn test_fallback_replaces_axiom_stub() {
    let mut env = make_env_with_opaque_type();
    env.add_inductive(fb_expr_decl()).unwrap();

    let nct_name = Name::from_string("FbExpr.noConfusionType");
    let nc_name = Name::from_string("FbExpr.noConfusion");

    // Get the correct type before removing
    let nct_type = env.get_const(&nct_name).unwrap().type_.clone();
    let nc_type = env.get_const(&nc_name).unwrap().type_.clone();

    // Replace with axiom stubs (value=None) to simulate .olean loading.
    // Must remove first because extend_constants_unchecked panics on duplicates.
    env.remove_constant(&nct_name);
    let nct_stub = ConstantInfo::new(
        nct_name.clone(),
        vec![Name::from_string("u_1")],
        nct_type,
        None,  // Axiom stub — no value
        false, // Wrong reducibility
    );
    env.extend_constants_unchecked(std::iter::once(nct_stub));

    env.remove_constant(&nc_name);
    let nc_stub = ConstantInfo::new(
        nc_name.clone(),
        vec![Name::from_string("u_1")],
        nc_type,
        None,
        false,
    );
    env.extend_constants_unchecked(std::iter::once(nc_stub));

    // Verify stubs have no value
    assert!(env.get_const(&nct_name).unwrap().value.is_none());
    assert!(env.get_const(&nc_name).unwrap().value.is_none());

    // Regenerate — should replace stubs with proper definitions
    env.regenerate_missing_no_confusion();

    // Verify replacement
    let nct = env.get_const(&nct_name).unwrap();
    assert!(
        nct.value.is_some(),
        "axiom stub should be replaced with definition"
    );
    assert!(nct.is_reducible, "should be Reducible after regeneration");

    let nc = env.get_const(&nc_name).unwrap();
    assert!(
        nc.value.is_some(),
        "axiom stub should be replaced with definition"
    );

    // Verify typechecking
    assert_value_typechecks(&env, "FbExpr.noConfusionType");
    assert_value_typechecks(&env, "FbExpr.noConfusion");
}

/// Test: FbDescr noConfusionType WHNF reduces for all 3 constructors.
///
/// Three constructors means 9 same/cross pairs. Test same-constructor cases
/// (3) to verify iota reduction through all minor premises.
#[test]
fn test_fallback_fbdescr_nct_whnf_all_ctors() {
    let mut env = make_env_with_opaque_type();
    env.add_inductive(fb_descr_decl()).unwrap();

    let nct_name = Name::from_string("FbDescr.noConfusionType");
    let nc_name = Name::from_string("FbDescr.noConfusion");
    env.remove_constant(&nct_name);
    env.remove_constant(&nc_name);
    env.regenerate_missing_no_confusion();

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u_nc");

    // Test each same-constructor case: node-node, atom-atom, pair-pair
    let cases: Vec<(&str, Vec<Expr>, Vec<Expr>, u32)> = vec![
        // node(x, r) vs node(y, s): needs P at bvar(4)
        (
            "FbDescr.node",
            vec![Expr::bvar(3), Expr::bvar(2)],
            vec![Expr::bvar(1), Expr::bvar(0)],
            4,
        ),
        // atom(n) vs atom(m): needs P at bvar(2)
        ("FbDescr.atom", vec![Expr::bvar(1)], vec![Expr::bvar(0)], 2),
        // pair(a, b) vs pair(c, d): needs P at bvar(4)
        (
            "FbDescr.pair",
            vec![Expr::bvar(3), Expr::bvar(2)],
            vec![Expr::bvar(1), Expr::bvar(0)],
            4,
        ),
    ];

    for (ctor_name, args_a, args_b, p_idx) in cases {
        let nct = Expr::const_(
            Name::from_string("FbDescr.noConfusionType"),
            vec![Level::param(u.clone())],
        );
        let mut app_a = Expr::const_(Name::from_string(ctor_name), vec![]);
        for arg in args_a {
            app_a = Expr::app(app_a, arg);
        }
        let mut app_b = Expr::const_(Name::from_string(ctor_name), vec![]);
        for arg in args_b {
            app_b = Expr::app(app_b, arg);
        }
        let applied = Expr::app(Expr::app(Expr::app(nct, Expr::bvar(p_idx)), app_a), app_b);
        let result = tc.whnf_impl(&applied);
        assert!(
            matches!(result.kind(), ExprKind::Pi(..)),
            "{ctor_name}: noConfusionType P (...) (...) should WHNF to Pi, got: {result:?}"
        );
    }
}

/// Test: regeneration is idempotent — running it twice doesn't break anything.
#[test]
fn test_fallback_regenerate_idempotent() {
    let mut env = make_env_with_opaque_type();
    env.add_inductive(fb_expr_decl()).unwrap();

    let nct_name = Name::from_string("FbExpr.noConfusionType");
    let nc_name = Name::from_string("FbExpr.noConfusion");
    env.remove_constant(&nct_name);
    env.remove_constant(&nc_name);

    // First regeneration
    env.regenerate_missing_no_confusion();
    assert!(env.get_const(&nct_name).unwrap().value.is_some());

    // Second regeneration should be a no-op (constants already have values)
    env.regenerate_missing_no_confusion();
    assert!(env.get_const(&nct_name).unwrap().value.is_some());

    // Still typechecks
    assert_value_typechecks(&env, "FbExpr.noConfusionType");
    assert_value_typechecks(&env, "FbExpr.noConfusion");
}
