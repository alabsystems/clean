// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for structural validation of ConstantInfo during import.
//!
//! Part of #3233: validates that `validate_constant_info_structural` and
//! `extend_constants_structural` catch malformed constants that
//! `extend_constants_unchecked` would silently accept.

use super::types::{ConstantInfo, ConstantKind, Reducibility};
use super::Environment;
use crate::expr::{Expr, FVarId};
use crate::level::Level;
use crate::name::Name;

fn mk_valid_constant(name: &str) -> ConstantInfo {
    ConstantInfo {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::sort(Level::Zero),
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    }
}

#[test]
fn test_validate_structural_accepts_valid_constant() {
    let env = Environment::default();
    let info = mk_valid_constant("test.valid");
    env.validate_constant_info_structural(&info)
        .expect("valid constant should pass structural validation");
}

#[test]
fn test_validate_structural_rejects_duplicate_level_params() {
    let env = Environment::default();
    let u = Name::from_string("u");
    let info = ConstantInfo {
        name: Name::from_string("test.dup_levels"),
        level_params: vec![u.clone(), u],
        type_: Expr::sort(Level::Zero),
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    };
    let err = env
        .validate_constant_info_structural(&info)
        .expect_err("duplicate level params should be rejected");
    assert!(
        err.to_string()
            .contains("Duplicate universe level parameter"),
        "error should mention duplicate: {err}"
    );
}

#[test]
fn test_validate_structural_rejects_fvar_in_type() {
    let env = Environment::default();
    let fvar_type = Expr::fvar(FVarId::new(42));
    let info = ConstantInfo {
        name: Name::from_string("test.fvar_type"),
        level_params: vec![],
        type_: fvar_type,
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    };
    let err = env
        .validate_constant_info_structural(&info)
        .expect_err("fvar in type should be rejected");
    assert!(
        err.to_string().contains("free variables"),
        "error should mention free variables: {err}"
    );
}

#[test]
fn test_validate_structural_rejects_fvar_in_value() {
    let env = Environment::default();
    let fvar_val = Expr::fvar(FVarId::new(99));
    let info = ConstantInfo {
        name: Name::from_string("test.fvar_value"),
        level_params: vec![],
        type_: Expr::sort(Level::Zero),
        value: Some(fvar_val),
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Definition,
    };
    let err = env
        .validate_constant_info_structural(&info)
        .expect_err("fvar in value should be rejected");
    assert!(
        err.to_string().contains("free variables"),
        "error should mention free variables: {err}"
    );
}

#[test]
fn test_validate_structural_rejects_undefined_level_param() {
    let env = Environment::default();
    let u = Name::from_string("u");
    // Type uses Level::Param("u") but level_params is empty
    let info = ConstantInfo {
        name: Name::from_string("test.undef_level"),
        level_params: vec![],
        type_: Expr::sort(Level::Param(u)),
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    };
    let err = env
        .validate_constant_info_structural(&info)
        .expect_err("undefined level param should be rejected");
    assert!(
        err.to_string()
            .contains("Undefined universe level parameter"),
        "error should mention undefined param: {err}"
    );
}

#[test]
fn test_extend_constants_structural_rejects_bad_and_accepts_good() {
    let mut env = Environment::default();

    let valid = mk_valid_constant("test.good");
    let u = Name::from_string("u");
    let bad = ConstantInfo {
        name: Name::from_string("test.bad_fvar"),
        level_params: vec![],
        type_: Expr::fvar(FVarId::new(777)),
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    };
    let bad_levels = ConstantInfo {
        name: Name::from_string("test.bad_levels"),
        level_params: vec![u.clone(), u],
        type_: Expr::sort(Level::Zero),
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    };

    let rejected = env.extend_constants_structural(vec![valid, bad, bad_levels].into_iter());

    // Two constants should be rejected
    assert_eq!(
        rejected.len(),
        2,
        "expected 2 rejections, got: {rejected:?}"
    );
    assert_eq!(rejected[0].0, Name::from_string("test.bad_fvar"));
    assert_eq!(rejected[1].0, Name::from_string("test.bad_levels"));

    // The valid constant should have been inserted
    assert!(
        env.get_const(&Name::from_string("test.good")).is_some(),
        "valid constant should be in environment"
    );
    // The bad constants should NOT be in the environment
    assert!(
        env.get_const(&Name::from_string("test.bad_fvar")).is_none(),
        "fvar constant should not be in environment"
    );
    assert!(
        env.get_const(&Name::from_string("test.bad_levels"))
            .is_none(),
        "bad levels constant should not be in environment"
    );
}

// ─────────────────────────── G4: extend_constants_checked ───────────────────────────

/// G4: a well-formed axiom batch (well-formed types) passes the checked lane.
#[test]
fn test_extend_constants_checked_accepts_well_formed_axioms() {
    let mut env = Environment::default();
    let a = mk_valid_constant("g4.axiom_a"); // type: Sort 0 (Prop)
    let b = mk_valid_constant("g4.axiom_b");
    env.extend_constants_checked(vec![a, b].into_iter())
        .expect("well-formed axiom batch must pass the checked lane");
    assert!(env.get_const(&Name::from_string("g4.axiom_a")).is_some());
    assert!(env.get_const(&Name::from_string("g4.axiom_b")).is_some());
}

/// G4 TIER 1 (structural): a record whose TYPE carries a leaked free variable —
/// the exact "leaked fvar/mvar or out-of-scope Level::Param" smuggle G4 names —
/// is rejected by the unconditional structural check, WITHOUT needing any
/// referenced constant present.
#[test]
fn test_extend_constants_checked_rejects_leaked_fvar_in_type() {
    let mut env = Environment::default();
    let bad = ConstantInfo {
        name: Name::from_string("g4.leaked_fvar"),
        level_params: vec![],
        type_: Expr::fvar(FVarId::new(0xF00D)),
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    };
    let err = env
        .extend_constants_checked(std::iter::once(bad))
        .expect_err("a leaked-fvar axiom type must fail the checked lane");
    assert_eq!(err.0, Name::from_string("g4.leaked_fvar"));
}

/// G4 TIER 2 (kernel): a VALUE-bearing record whose value is NOT def-eq to its
/// declared type — the `Function.Injective`-style unchecked-body shape — is
/// rejected by the kernel `check_type` when its dependencies are present.
#[test]
fn test_extend_constants_checked_rejects_ill_typed_value() {
    let mut env = Environment::default();
    env.init_true_false().expect("init true/false");
    // `bogus : False := True.intro` as a value-bearing (reducible) Axiom shape —
    // exactly the shape add_decl cannot mint. Its value `True.intro : True` is not
    // a proof of `False`, so the kernel check_type must reject it.
    let bogus = ConstantInfo {
        name: Name::from_string("g4.bogus"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("False"), vec![]),
        value: Some(Expr::const_(Name::from_string("True.intro"), vec![])),
        is_reducible: true,
        reducibility: Reducibility::Reducible,
        kind: ConstantKind::Axiom,
    };
    let err = env
        .extend_constants_checked(std::iter::once(bogus))
        .expect_err("an ill-typed reducible-axiom value must fail the checked lane");
    assert_eq!(err.0, Name::from_string("g4.bogus"));
}

/// G4 dependency-tolerance: a record whose TYPE references a constant NOT present
/// in the env (a legitimate forward/external overlay dependency) is TOLERATED —
/// the checked lane must not reject legitimate incremental overlay loading. It is
/// still fully structurally checked (tier 1); only the unresolved-const kernel
/// error is skipped.
#[test]
fn test_extend_constants_checked_tolerates_unknown_const_forward_ref() {
    let mut env = Environment::default();
    // Type `NotLoaded.Foo` — structurally clean (no fvar/mvar/level leak) but the
    // referenced const is absent. This is a forward/external reference, not a
    // smuggle, so the checked lane must ACCEPT it.
    let fwd = ConstantInfo {
        name: Name::from_string("g4.forward_ref"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("NotLoaded.Foo"), vec![]),
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    };
    env.extend_constants_checked(std::iter::once(fwd))
        .expect("an unresolved external reference must be tolerated (forward dep)");
    assert!(
        env.get_const(&Name::from_string("g4.forward_ref"))
            .is_some(),
        "the forward-ref record must be registered"
    );
}
