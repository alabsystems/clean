// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for [`crate::extract_rust`] — split out when the beta-redex fix took
//! the parent past the 1000-line paragon bar (real split, not `--update`).
use super::*;

use clean_kernel::BinderInfo;

/// The redex BINDING is load-bearing: argument in the OUTER scope, body in
/// the EXTENDED scope.
///
/// The three-arm e2e test (`test_extract_three_arm_match_on_rust` in
/// `cmd_extract`) cannot distinguish a correct redex binding from one that
/// binds garbage — its `_` arm ignores the binder. This test hand-builds
/// `(fun x : Nat => Nat.add x x) (Nat.succ a)` with `a` an outer parameter,
/// so BOTH resolutions are pinned: the argument must render against the
/// outer scope (`a`), and the body's de Bruijn index must resolve to the
/// fresh `let` binding, used twice. A mutation that translates the body
/// against the outer scope, binds the wrong value, or extends the scope in
/// the wrong order fails this assertion.
#[test]
fn test_beta_redex_binds_argument_once_and_scopes_the_body() {
    let head = Expr::lam(
        BinderInfo::Default,
        Expr::const_str("Nat"),
        Expr::app(
            Expr::app(Expr::const_str("Nat.add"), Expr::bvar(0)),
            Expr::bvar(0),
        ),
    );
    let arg = Expr::app(Expr::const_str("Nat.succ"), Expr::bvar(0));
    let e = Expr::app(head, arg);
    let params = vec![("a".to_string(), ScalarTy::Nat)];
    let r = translate(&e, ScalarTy::Nat, &params).expect("redex must translate");
    assert!(
        r.text.contains("let __r1_0 = a.checked_add(1u64).expect("),
        "the argument must be translated in the OUTER scope (naming `a`) and \
             bound exactly once; got: {}",
        r.text
    );
    assert!(
        r.text.contains("__r1_0.checked_add(__r1_0)"),
        "the body's de Bruijn index must resolve to the redex binding, used \
             twice; got: {}",
        r.text
    );
}

/// Fail-closed shapes: over-application and a non-scalar binder domain
/// both REFUSE with named diagnostics — never a guess.
#[test]
fn test_beta_redex_refuses_overapplication_and_nonscalar_domain() {
    let identity = Expr::lam(BinderInfo::Default, Expr::const_str("Nat"), Expr::bvar(0));
    let over = Expr::app(Expr::app(identity, Expr::bvar(0)), Expr::bvar(0));
    let params = vec![("a".to_string(), ScalarTy::Nat)];
    let err =
        translate(&over, ScalarTy::Nat, &params).expect_err("2 args onto 1 binder must refuse");
    assert!(
        err.to_string().contains("beta-redex applies 2 argument(s)"),
        "got: {err}"
    );

    let alien_dom = Expr::app(
        Expr::lam(
            BinderInfo::Default,
            Expr::const_str("String"),
            Expr::bvar(1),
        ),
        Expr::bvar(0),
    );
    let err = translate(&alien_dom, ScalarTy::Nat, &params)
        .expect_err("a non-scalar binder domain must refuse");
    assert!(err.to_string().contains("non-scalar domain"), "got: {err}");
}

#[test]
fn test_rust_fn_name_refuses_non_identifiers() {
    assert_eq!(rust_fn_name("Foo.barU").expect("dots become _"), "Foo_barU");
    assert!(matches!(rust_fn_name("f'"), Err(RustEmitError::BadName(_))));
    assert!(matches!(
        rust_fn_name("1bad"),
        Err(RustEmitError::BadName(_))
    ));
}

#[test]
fn test_param_names_are_readable_then_indexed() {
    assert_eq!(param_name(0), "a");
    assert_eq!(param_name(25), "z");
    assert_eq!(param_name(26), "x26");
}
