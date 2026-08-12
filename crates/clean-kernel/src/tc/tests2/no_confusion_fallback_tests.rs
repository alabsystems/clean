// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! noConfusion fallback sort-level tests for #3208.
//!
//! Tests that `regenerate_missing_no_confusion` correctly uses fallback sort
//! levels when `compute_ctor_field_sort_levels` fails on complex constructor
//! fields. This exercises the fix from commit 543167041 where 5 NotAFunction
//! errors occurred on per-constructor noConfusion bodies loaded from
//! `.olean.private` for recursive inductives like `Int.Linear.Expr`,
//! `Lean.ParserDescr`, and `Lean.Syntax`.
//!
//! The root cause: during post-load regeneration, `infer_sort` fails on fields
//! whose types reference complex expressions that the TC can't fully reduce.
//! The fallback uses the inductive's own result sort level as a conservative
//! approximation.

use super::support::make_nat_env_with_eq;
use super::*;
use crate::env::ConstantInfo;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};

/// Helper: create an environment with Nat, Eq, and an opaque constant
/// `OpaqueType : Type` that has no value (simulating an axiom or opaque
/// definition whose sort the TC cannot infer during noConfusion generation).
fn make_env_with_opaque_type() -> Environment {
    let mut env = make_nat_env_with_eq();
    // HEq before any parameterized add_inductive: the v4.30 heterogeneous
    // noConfusion convention (designs/2026-07-03-noconfusion-ctoridx-
    // convention.md) uses HEq/eq_of_heq for parameterized types (FbResult).
    env.init_heq().expect("invariant: init_heq");
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

/// Test: noConfusion regeneration works for FbExpr (recursive + opaque field).
///
/// This is the core #3208 test: FbExpr.lit has an OpaqueType field whose sort
/// can't be inferred by the strict path. The fallback uses FbExpr's result
/// sort (Type = Sort 1) to approximate the field sort.
#[test]
fn test_fallback_regenerate_fbexpr_typechecks() {
    let mut env = make_env_with_opaque_type();
    env.add_inductive(fb_expr_decl()).unwrap();

    // Remove noConfusion constants (simulating .olean loading gap)
    let nct_name = Name::from_string("FbExpr.noConfusionType");
    let nc_name = Name::from_string("FbExpr.noConfusion");
    env.remove_constant(&nct_name);
    env.remove_constant(&nc_name);
    assert!(env.get_const(&nct_name).is_none());

    // Regenerate using the fallback path
    env.regenerate_missing_no_confusion();

    // Verify constants were regenerated
    let nct = env.get_const(&nct_name).expect("nct should be regenerated");
    assert!(nct.value.is_some(), "nct should have a value");
    assert!(nct.is_reducible, "nct should be Reducible");
    let nc = env.get_const(&nc_name).expect("nc should be regenerated");
    assert!(nc.value.is_some(), "nc should have a value");

    // Verify regenerated values typecheck
    assert_value_typechecks(&env, "FbExpr.noConfusionType");
    assert_value_typechecks(&env, "FbExpr.noConfusion");
}

/// Test: noConfusion regeneration for FbDescr (3 ctors, mix of field types).
///
/// Mimics Lean.ParserDescr: node has OpaqueType + recursive, atom has Nat,
/// pair has two recursive fields.
#[test]
fn test_fallback_regenerate_fbdescr_typechecks() {
    let mut env = make_env_with_opaque_type();
    env.add_inductive(fb_descr_decl()).unwrap();

    let nct_name = Name::from_string("FbDescr.noConfusionType");
    let nc_name = Name::from_string("FbDescr.noConfusion");
    env.remove_constant(&nct_name);
    env.remove_constant(&nc_name);

    env.regenerate_missing_no_confusion();

    let nct = env.get_const(&nct_name).expect("nct should be regenerated");
    assert!(nct.value.is_some(), "nct should have a value");
    let nc = env.get_const(&nc_name).expect("nc should be regenerated");
    assert!(nc.value.is_some(), "nc should have a value");

    assert_value_typechecks(&env, "FbDescr.noConfusionType");
    assert_value_typechecks(&env, "FbDescr.noConfusion");
}

/// Test: noConfusion regeneration for parametric FbResult (universe-polymorphic).
///
/// Mimics DoResultPRBC: parametric inductive with OpaqueType field.
/// The fallback sort level must account for the universe parameter u.
#[test]
fn test_fallback_regenerate_fbresult_typechecks() {
    let mut env = make_env_with_opaque_type();
    env.add_inductive(fb_result_decl()).unwrap();

    let nct_name = Name::from_string("FbResult.noConfusionType");
    let nc_name = Name::from_string("FbResult.noConfusion");
    env.remove_constant(&nct_name);
    env.remove_constant(&nc_name);

    env.regenerate_missing_no_confusion();

    let nct = env.get_const(&nct_name).expect("nct should be regenerated");
    assert!(nct.value.is_some());
    let nc = env.get_const(&nc_name).expect("nc should be regenerated");
    assert!(nc.value.is_some());

    assert_value_typechecks(&env, "FbResult.noConfusionType");
    assert_value_typechecks(&env, "FbResult.noConfusion");
}
