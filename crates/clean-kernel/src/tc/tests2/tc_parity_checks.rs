// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for TC parity fixes #3225, #3226, #3231.
//!
//! - #3225: check_level for Sort when infer_only=false
//! - #3226: unsafe/partial declaration check in infer_constant
//! - #3231: Structure eta restricted to match Lean 4

use super::*;
use crate::env::Declaration;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};
use crate::level::Level;

// =============================================================================
// #3225: check_level for Sort when infer_only=false
// =============================================================================

/// check_type succeeds for Sort with level params when level_params is not set
/// (backward-compatible: no level_params means no validation).
#[test]
fn test_check_level_sort_no_params_set_passes() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    // Sort(Param("u")) — no level_params set, should pass
    let sort_u = Expr::sort(Level::param(Name::from_string("u")));
    let sort_succ_u = Expr::sort(Level::succ(Level::param(Name::from_string("u"))));
    let result = tc.check_type(&sort_u, &sort_succ_u);
    assert!(result.is_ok(), "should pass when level_params is None");
}

/// check_type catches undefined level param in Sort when level_params is set.
#[test]
fn test_check_level_sort_undefined_param_fails() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    tc.set_level_params(vec![Name::from_string("v")]);
    // Sort(Param("u")) — but only "v" is allowed
    let sort_u = Expr::sort(Level::param(Name::from_string("u")));
    let sort_succ_u = Expr::sort(Level::succ(Level::param(Name::from_string("u"))));
    let result = tc.check_type(&sort_u, &sort_succ_u);
    assert!(
        matches!(
            result,
            Err(TypeError::UndefinedLevelParam { ref param }) if param.to_string() == "u"
        ),
        "expected UndefinedLevelParam for 'u', got {result:?}"
    );
}

/// check_type succeeds for Sort with known level param.
#[test]
fn test_check_level_sort_known_param_passes() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    tc.set_level_params(vec![Name::from_string("u")]);
    let sort_u = Expr::sort(Level::param(Name::from_string("u")));
    let sort_succ_u = Expr::sort(Level::succ(Level::param(Name::from_string("u"))));
    let result = tc.check_type(&sort_u, &sort_succ_u);
    assert!(
        result.is_ok(),
        "should pass with known level param: {result:?}"
    );
}

/// check_level validates nested level expressions (Max, IMax, Succ).
#[test]
fn test_check_level_nested_undefined_param_fails() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    tc.set_level_params(vec![Name::from_string("u")]);
    // Sort(Max(u, v)) — "v" is not allowed
    let level = Level::max(
        Level::param(Name::from_string("u")),
        Level::param(Name::from_string("v")),
    );
    let sort = Expr::sort(level.clone());
    let sort_succ = Expr::sort(Level::succ(level));
    let result = tc.check_type(&sort, &sort_succ);
    assert!(
        matches!(
            result,
            Err(TypeError::UndefinedLevelParam { ref param }) if param.to_string() == "v"
        ),
        "expected UndefinedLevelParam for 'v', got {result:?}"
    );
}

/// infer_type (infer_only=true) does NOT check level params — backward compat.
#[test]
fn test_infer_only_skips_level_check() {
    let env = Environment::new();
    let mut tc = TypeChecker::new(&env);
    tc.set_level_params(vec![Name::from_string("v")]);
    // Sort(Param("u")) — "u" not in level_params, but infer_only=true skips check
    let sort_u = Expr::sort(Level::param(Name::from_string("u")));
    let result = tc.infer_type(&sort_u);
    assert!(
        result.is_ok(),
        "infer_type should skip level check: {result:?}"
    );
}

// =============================================================================
// #3226: unsafe/partial declaration check in infer_constant
// =============================================================================

/// Helper: add a simple axiom to env and optionally mark it unsafe/partial.
fn add_test_axiom(env: &mut Environment, name_str: &str, mark_unsafe: bool, mark_partial: bool) {
    let name = Name::from_string(name_str);
    env.add_decl(Declaration::Axiom {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("add axiom");
    if mark_unsafe {
        env.mark_unsafe(name.clone());
    }
    if mark_partial {
        env.mark_partial(name);
    }
}

/// check_type rejects unsafe constants when allow_unsafe=false.
#[test]
fn test_unsafe_decl_rejected_when_disallowed() {
    let mut env = Environment::new();
    add_test_axiom(&mut env, "UnsafeThing", true, false);
    let mut tc = TypeChecker::new(&env);
    tc.set_allow_unsafe(false);
    // Type of `UnsafeThing` is `Type`, so check_type(UnsafeThing, Type) should fail
    let c = Expr::const_(Name::from_string("UnsafeThing"), vec![]);
    let result = tc.check_type(&c, &Expr::type_());
    assert!(
        matches!(result, Err(TypeError::UnsafeDeclaration { ref name }) if name.to_string() == "UnsafeThing"),
        "expected UnsafeDeclaration, got {result:?}"
    );
}

/// check_type allows unsafe constants when allow_unsafe=true (default).
#[test]
fn test_unsafe_decl_allowed_by_default() {
    let mut env = Environment::new();
    add_test_axiom(&mut env, "UnsafeThing", true, false);
    let tc = TypeChecker::new(&env);
    let c = Expr::const_(Name::from_string("UnsafeThing"), vec![]);
    let result = tc.check_type(&c, &Expr::type_());
    assert!(
        result.is_ok(),
        "unsafe should be allowed by default: {result:?}"
    );
}

/// check_type rejects partial constants when allow_partial=false.
#[test]
fn test_partial_decl_rejected_when_disallowed() {
    let mut env = Environment::new();
    add_test_axiom(&mut env, "PartialThing", false, true);
    let mut tc = TypeChecker::new(&env);
    tc.set_allow_partial(false);
    let c = Expr::const_(Name::from_string("PartialThing"), vec![]);
    let result = tc.check_type(&c, &Expr::type_());
    assert!(
        matches!(result, Err(TypeError::PartialDeclaration { ref name }) if name.to_string() == "PartialThing"),
        "expected PartialDeclaration, got {result:?}"
    );
}

/// check_type allows partial constants when allow_partial=true (default).
#[test]
fn test_partial_decl_allowed_by_default() {
    let mut env = Environment::new();
    add_test_axiom(&mut env, "PartialThing", false, true);
    let tc = TypeChecker::new(&env);
    let c = Expr::const_(Name::from_string("PartialThing"), vec![]);
    let result = tc.check_type(&c, &Expr::type_());
    assert!(
        result.is_ok(),
        "partial should be allowed by default: {result:?}"
    );
}

/// infer_type (infer_only=true) does NOT check unsafe/partial — backward compat.
#[test]
fn test_infer_only_skips_unsafe_partial_check() {
    let mut env = Environment::new();
    add_test_axiom(&mut env, "UnsafeThing", true, false);
    add_test_axiom(&mut env, "PartialThing", false, true);
    let mut tc = TypeChecker::new(&env);
    tc.set_allow_unsafe(false);
    tc.set_allow_partial(false);
    // infer_type uses infer_only=true, so these should pass
    let unsafe_c = Expr::const_(Name::from_string("UnsafeThing"), vec![]);
    let partial_c = Expr::const_(Name::from_string("PartialThing"), vec![]);
    assert!(
        tc.infer_type(&unsafe_c).is_ok(),
        "infer_type should skip unsafe check"
    );
    assert!(
        tc.infer_type(&partial_c).is_ok(),
        "infer_type should skip partial check"
    );
}

/// check_level validates Const universe level params when level_params is set.
#[test]
fn test_check_level_const_universe_params() {
    let mut env = Environment::new();
    // Add axiom with universe polymorphism: Foo.{u} : Sort(u+1)
    let u_name = Name::from_string("u");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Foo"),
        level_params: vec![u_name.clone()],
        type_: Expr::sort(Level::succ(Level::param(u_name.clone()))),
    })
    .expect("add Foo");

    let mut tc = TypeChecker::new(&env);
    tc.set_level_params(vec![Name::from_string("v")]);
    // Foo.{u} — but level_params only allows "v", not "u"
    let foo_u = Expr::const_(
        Name::from_string("Foo"),
        vec![Level::param(Name::from_string("u"))],
    );
    let expected_ty = Expr::sort(Level::succ(Level::param(Name::from_string("u"))));
    let result = tc.check_type(&foo_u, &expected_ty);
    assert!(
        matches!(
            result,
            Err(TypeError::UndefinedLevelParam { ref param }) if param.to_string() == "u"
        ),
        "expected UndefinedLevelParam for 'u' in Const levels, got {result:?}"
    );
}

// =============================================================================
// #3231: Structure eta more permissive than Lean 4
// =============================================================================

/// Helper: set up a simple struct S with 2 fields for eta testing.
fn setup_two_field_struct(env: &mut Environment) {
    let s_name = Name::from_string("S");
    let s_mk = Name::from_string("S.mk");

    // S : Type
    // S.mk : Nat -> Nat -> S
    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    let s_type = Expr::type_();
    let ctor_type = Expr::pi(
        BinderInfo::Default,
        nat_type.clone(),
        Expr::pi(
            BinderInfo::Default,
            nat_type,
            Expr::const_(s_name.clone(), vec![]),
        ),
    );

    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: s_name,
            type_: s_type,
            constructors: vec![Constructor {
                name: s_mk,
                type_: ctor_type,
            }],
        }],
    })
    .expect("add_inductive S");
}

/// Structure eta still works for non-constructor expressions.
/// Given `x : S`, eta-expanding `x` to `S.mk (x.0) (x.1)` should be
/// definitionally equal to `x`.
#[test]
fn test_struct_eta_expansion_non_constructor() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    setup_two_field_struct(&mut env);

    let tc = TypeChecker::new(&env);
    let s_name = Name::from_string("S");
    let s_mk_name = Name::from_string("S.mk");

    // Use a local decl `x : S`
    let x_id = tc.ctx_push(
        Name::from_string("x"),
        Expr::const_(s_name.clone(), vec![]),
        BinderInfo::Default,
    );
    let x = Expr::fvar(x_id);

    // eta-expanded: S.mk (x.0) (x.1)
    let expanded = Expr::app(
        Expr::app(
            Expr::const_(s_mk_name, vec![]),
            Expr::proj(s_name.clone(), 0, x.clone()),
        ),
        Expr::proj(s_name.clone(), 1, x.clone()),
    );

    // x should be def_eq to its eta expansion
    assert!(
        tc.is_def_eq(&x, &expanded),
        "non-ctor struct eta should still work"
    );

    tc.ctx_pop();
}

/// Structure eta should work symmetrically (both directions).
#[test]
fn test_struct_eta_symmetric() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    setup_two_field_struct(&mut env);

    let tc = TypeChecker::new(&env);
    let s_name = Name::from_string("S");
    let s_mk_name = Name::from_string("S.mk");

    let x_id = tc.ctx_push(
        Name::from_string("x"),
        Expr::const_(s_name.clone(), vec![]),
        BinderInfo::Default,
    );
    let x = Expr::fvar(x_id);

    let expanded = Expr::app(
        Expr::app(
            Expr::const_(s_mk_name, vec![]),
            Expr::proj(s_name.clone(), 0, x.clone()),
        ),
        Expr::proj(s_name.clone(), 1, x.clone()),
    );

    // Both directions
    assert!(tc.is_def_eq(&expanded, &x), "expanded = x");
    assert!(tc.is_def_eq(&x, &expanded), "x = expanded");

    tc.ctx_pop();
}
