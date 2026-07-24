// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! noConfusion VALUE type-checking tests.
//!
//! These tests verify that the noConfusion *value* (the proof term using Eq.rec
//! and diagonal casesOn) actually typechecks against its declared type.
//! This is distinct from the structural tests in `no_confusion.rs` which check
//! that noConfusion exists and has the right type signature.
//!
//! Bug context: build_no_confusion (inductive_no_confusion.rs:1150-1173) sets
//! K_type to the fully-applied noConfusionType instead of the inner eq_chain
//! (f1=f1 -> ... -> fk=fk -> P). This causes TypeMismatch for all types.
//! Part of #2162.

use super::support::make_nat_env_with_eq;
use super::*;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};

/// Create Nat inductive declaration (zero, succ).
fn nat_decl() -> InductiveDecl {
    let nat = Name::from_string("Nat");
    let nat_ref = Expr::const_(nat.clone(), vec![]);
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nat,
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Nat.zero"),
                    type_: nat_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("Nat.succ"),
                    type_: Expr::arrow(nat_ref.clone(), nat_ref),
                },
            ],
        }],
    }
}

/// Create MyExpr inductive declaration (var: Nat->MyExpr, add: MyExpr->MyExpr->MyExpr).
fn myexpr_decl() -> InductiveDecl {
    let nat_ref = Expr::const_(Name::from_string("Nat"), vec![]);
    let myexpr = Name::from_string("MyExpr");
    let myexpr_ref = Expr::const_(myexpr.clone(), vec![]);
    InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: myexpr,
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("MyExpr.var"),
                    type_: Expr::arrow(nat_ref, myexpr_ref.clone()),
                },
                Constructor {
                    name: Name::from_string("MyExpr.add"),
                    type_: Expr::arrow(
                        myexpr_ref.clone(),
                        Expr::arrow(myexpr_ref.clone(), myexpr_ref),
                    ),
                },
            ],
        }],
    }
}

/// Create environment with Nat + MyExpr + Eq.
fn make_myexpr_env() -> Environment {
    let mut env = Environment::new();
    env.add_inductive(nat_decl()).unwrap();
    env.add_inductive(myexpr_decl()).unwrap();
    env.init_eq().unwrap();
    env
}

/// Assert that the named constant's value typechecks against its declared type.
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

/// Assert that `noConfusionType P (ctor args1) (ctor args2)` WHNF-reduces to Pi.
fn assert_nct_whnf_is_pi(
    env: &Environment,
    nct_levels: Vec<Level>,
    ctor_name: &str,
    ctor_args_a: Vec<Expr>,
    ctor_args_b: Vec<Expr>,
    p_bvar_idx: u32,
) {
    let tc = TypeChecker::new(env);
    let nct = Expr::const_(Name::from_string("MyExpr.noConfusionType"), nct_levels);
    let ctor = Expr::const_(Name::from_string(ctor_name), vec![]);
    let mut app_a = ctor.clone();
    for arg in ctor_args_a {
        app_a = Expr::app(app_a, arg);
    }
    let mut app_b = Expr::const_(Name::from_string(ctor_name), vec![]);
    for arg in ctor_args_b {
        app_b = Expr::app(app_b, arg);
    }
    let applied = Expr::app(
        Expr::app(Expr::app(nct, Expr::bvar(p_bvar_idx)), app_a),
        app_b,
    );
    let result = tc.whnf_impl(&applied);
    assert!(
        matches!(result.kind(), ExprKind::Pi(..)),
        "noConfusionType P ({ctor_name} ...) ({ctor_name} ...) should WHNF to Pi, got: {result:?}",
    );
}

/// Test: Nat.noConfusion value typechecks against its declared type.
#[test]
fn test_no_confusion_value_typechecks_nat() {
    let env = make_nat_env_with_eq();
    assert_value_typechecks(&env, "Nat.noConfusion");
}

/// Test: MyOption.noConfusion value typechecks (parametric type, 1 param, 2 ctors).
///
/// MyOption : Type u -> Type u (mirrors Lean's Option); the Type-u result keeps
/// large elimination, so noConfusion gets its fresh elim level.
#[test]
fn test_no_confusion_value_typechecks_parametric() {
    let mut env = Environment::new();
    let u = Name::from_string("u");
    let opt = Name::from_string("MyOption");
    let opt_type = Expr::pi(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone())))),
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone())))),
    );
    let opt_a = Expr::app(
        Expr::const_(opt.clone(), vec![Level::param(u.clone())]),
        Expr::bvar(0),
    );
    let none_type = Expr::pi(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone())))),
        opt_a,
    );
    let some_type = Expr::pi(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone())))),
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0),
            Expr::app(
                Expr::const_(opt.clone(), vec![Level::param(u.clone())]),
                Expr::bvar(1),
            ),
        ),
    );
    let decl = InductiveDecl {
        level_params: vec![u],
        num_params: 1,
        types: vec![InductiveType {
            name: opt,
            type_: opt_type,
            constructors: vec![
                Constructor {
                    name: Name::from_string("MyOption.none"),
                    type_: none_type,
                },
                Constructor {
                    name: Name::from_string("MyOption.some"),
                    type_: some_type,
                },
            ],
        }],
    };
    // Eq + HEq before add_inductive: the v4.30 heterogeneous noConfusion
    // convention (designs/2026-07-03-noconfusion-ctoridx-convention.md) uses
    // HEq/eq_of_heq for parameterized types.
    env.init_eq().unwrap();
    env.init_heq().unwrap();
    env.add_inductive(decl).unwrap();
    assert_value_typechecks(&env, "MyOption.noConfusion");
}

/// Test: noConfusion value typechecks for a RECURSIVE inductive type.
///
/// MyExpr : Type, with constructors var : Nat -> MyExpr, add : MyExpr -> MyExpr -> MyExpr.
/// Reproduces the bug from #3208 where per-constructor noConfusion definitions
/// from .olean.private fail with NotAFunction for recursive inductives.
#[test]
fn test_no_confusion_value_typechecks_recursive() {
    let env = make_myexpr_env();
    assert_value_typechecks(&env, "MyExpr.noConfusionType");
    assert_value_typechecks(&env, "MyExpr.noConfusion");
}

/// Test: WHNF of noConfusionType applied to `var` constructor reduces to Pi.
///
/// When type-checking per-constructor noConfusion, the TC needs:
///   noConfusionType P (var n) (var m) ~~>whnf~~> (n = m -> P) -> P  (a Pi type)
/// If this reduction fails, the TC throws NotAFunction (#3208).
#[test]
fn test_no_confusion_type_whnf_reduces_var() {
    let env = make_myexpr_env();
    let u = Name::from_string("u");
    assert_nct_whnf_is_pi(
        &env,
        vec![Level::param(u)],
        "MyExpr.var",
        vec![Expr::bvar(1)],
        vec![Expr::bvar(0)],
        2,
    );
}

/// Test: WHNF of noConfusionType applied to `add` constructor reduces to Pi.
#[test]
fn test_no_confusion_type_whnf_reduces_add() {
    let env = make_myexpr_env();
    let u = Name::from_string("u");
    assert_nct_whnf_is_pi(
        &env,
        vec![Level::param(u)],
        "MyExpr.add",
        vec![Expr::bvar(3), Expr::bvar(2)],
        vec![Expr::bvar(1), Expr::bvar(0)],
        4,
    );
}

/// Test: regenerate_missing_no_confusion creates noConfusionType for an inductive
/// that was loaded WITHOUT noConfusionType (simulating .olean loading).
///
/// Reproduces the exact #3208 failure path: .olean loading uses
/// extend_*_unchecked which does NOT auto-generate noConfusionType.
#[test]
fn test_regenerate_creates_missing_no_confusion() {
    let mut env = make_myexpr_env();
    let nct_name = Name::from_string("MyExpr.noConfusionType");
    let nc_name = Name::from_string("MyExpr.noConfusion");

    // Sanity: both exist after add_inductive
    assert!(env.get_const(&nct_name).is_some());
    assert!(env.get_const(&nc_name).is_some());

    // Simulate .olean loading gap by removing both constants
    env.remove_constant(&nct_name);
    env.remove_constant(&nc_name);
    assert!(env.get_const(&nct_name).is_none());

    // The fix: regenerate_missing_no_confusion detects and creates them
    env.regenerate_missing_no_confusion();

    // Verify regenerated constants exist with correct properties
    let nct = env.get_const(&nct_name).expect("should be regenerated");
    assert!(nct.value.is_some(), "should have a value");
    assert!(nct.is_reducible, "should be Reducible");
    let nc = env.get_const(&nc_name).expect("should be regenerated");
    assert!(nc.value.is_some(), "should have a value");

    // Regenerated values typecheck
    assert_value_typechecks(&env, "MyExpr.noConfusionType");
    assert_value_typechecks(&env, "MyExpr.noConfusion");
}

/// Test: regenerate_missing_no_confusion RETURNS the names it inserted.
///
/// The olean import path (load.rs) folds these into a synthetic LoadSummary so
/// the O(new) verify-batch name scan sees the auto-generated noConfusion
/// constants (they are created after register_converted_constants, in no other
/// summary). A return that omitted them would silently under-count tc_pass.
#[test]
fn test_regenerate_returns_inserted_names() {
    let mut env = make_myexpr_env();
    let nct_name = Name::from_string("MyExpr.noConfusionType");
    let nc_name = Name::from_string("MyExpr.noConfusion");

    // Simulate the .olean gap (extend_*_unchecked never adds noConfusion).
    env.remove_constant(&nct_name);
    env.remove_constant(&nc_name);

    let inserted = env.regenerate_missing_no_confusion();

    // The returned set must contain exactly the (re)created constants, and each
    // returned name must actually be present in the env afterward.
    assert!(
        inserted.contains(&nct_name),
        "return must include the regenerated noConfusionType, got {inserted:?}"
    );
    assert!(
        inserted.contains(&nc_name),
        "return must include the regenerated noConfusion, got {inserted:?}"
    );
    for name in &inserted {
        assert!(
            env.get_const(name).is_some(),
            "every returned name must be a real env constant: {name}"
        );
    }
}

/// Test: regenerated noConfusionType WHNF-reduces to Pi (not stuck).
#[test]
fn test_regenerate_nct_whnf_reduces() {
    let mut env = make_myexpr_env();
    let nct_name = Name::from_string("MyExpr.noConfusionType");
    let nc_name = Name::from_string("MyExpr.noConfusion");
    env.remove_constant(&nct_name);
    env.remove_constant(&nc_name);
    env.regenerate_missing_no_confusion();

    let u = Name::from_string("u_nc");
    assert_nct_whnf_is_pi(
        &env,
        vec![Level::param(u)],
        "MyExpr.var",
        vec![Expr::bvar(1)],
        vec![Expr::bvar(0)],
        2,
    );
}

/// Test: regenerate_missing_no_confusion regenerates noConfusionType +
/// noConfusion even when they already have values and are Reducible.
///
/// Historical context (#3208): .olean-loaded noConfusionType values used
/// Lean 4's casesOn argument order (major before minors) while clean's
/// casesOn RecursorVal then used MajorAfterMinors, so iota reduction failed
/// (the major premise landed at the wrong position) and delta unfolding
/// failed because RecursorVals are not in env.constants. Clean's casesOn is
/// now Lean-faithful (MajorAfterMotive), so the orders agree; this test
/// keeps the regeneration path honest: regenerated values must typecheck
/// and reduce.
///
/// Part of #3208
#[test]
fn test_regenerate_fixes_olean_arg_order_mismatch() {
    // Create a fresh environment with casesOn as RecursorVal (clean convention)
    let mut env = make_myexpr_env();
    let nct_name = Name::from_string("MyExpr.noConfusionType");
    let nc_name = Name::from_string("MyExpr.noConfusion");

    // Sanity: both exist after add_inductive with correct values
    let nct = env.get_const(&nct_name).unwrap();
    assert!(nct.value.is_some());
    assert!(nct.is_reducible);

    // Verify casesOn is a RecursorVal (not a Definition)
    let cases_on_name = Name::from_string("MyExpr.casesOn");
    assert!(
        env.get_recursor(&cases_on_name).is_some(),
        "casesOn should be a RecursorVal"
    );

    // regenerate_missing_no_confusion should detect the arg order mismatch
    // and regenerate noConfusionType+noConfusion even though they already
    // have values and are Reducible.
    env.regenerate_missing_no_confusion();

    // The regenerated values should still typecheck
    assert_value_typechecks(&env, "MyExpr.noConfusionType");
    assert_value_typechecks(&env, "MyExpr.noConfusion");

    // And noConfusionType should WHNF-reduce to Pi
    let u = Name::from_string("u_nc");
    assert_nct_whnf_is_pi(
        &env,
        vec![Level::param(u)],
        "MyExpr.add",
        vec![Expr::bvar(3), Expr::bvar(2)],
        vec![Expr::bvar(1), Expr::bvar(0)],
        4,
    );
}

/// Test: noConfusion value typechecks for a multi-field type (2 fields).
///
/// Wrap2 : Type u -> Type u, with ctor mk : (A : Type u) -> A -> A -> Wrap2 A.
/// Two fields of the same type exercises the equality chain with multiple
/// Eq.refl applications in the diagonal casesOn alternative.
#[test]
fn test_no_confusion_value_typechecks_multi_field() {
    let mut env = Environment::new();
    let u = Name::from_string("u");
    let wrap = Name::from_string("Wrap2");
    let wrap_type = Expr::pi(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone())))),
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone())))),
    );
    let mk_type = Expr::pi(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone())))),
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1),
                Expr::app(
                    Expr::const_(wrap.clone(), vec![Level::param(u.clone())]),
                    Expr::bvar(2),
                ),
            ),
        ),
    );
    let decl = InductiveDecl {
        level_params: vec![u],
        num_params: 1,
        types: vec![InductiveType {
            name: wrap,
            type_: wrap_type,
            constructors: vec![Constructor {
                name: Name::from_string("Wrap2.mk"),
                type_: mk_type,
            }],
        }],
    };
    // Eq + HEq before add_inductive (v4.30 heterogeneous convention).
    env.init_eq().unwrap();
    env.init_heq().unwrap();
    env.add_inductive(decl).unwrap();
    assert_value_typechecks(&env, "Wrap2.noConfusionType");
    assert_value_typechecks(&env, "Wrap2.noConfusion");
}
