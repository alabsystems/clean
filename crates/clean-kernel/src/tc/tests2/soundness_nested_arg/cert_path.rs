// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cert-path soundness regressions, split out of the parent
//! `soundness_nested_arg` module to keep each file within the 500-line
//! paragon limit. These drive the same False payloads through
//! `infer_type_with_cert` (the certificate inference path). Shared env
//! helpers (`make_true_false_env`, `add_myid`, `bad_inner_app`) come from
//! the parent module via `use super::*`.

use super::*;

// ===========================================================================
// (f) CERT PATH — the dabf7a35 fix must also reject through `infer_type_with_cert`
// ===========================================================================
//
// The nested-App / Let-value deep checks (cert/infer_core.rs:116-146, 290-329)
// are gated `if !self.infer_only.get()`. `TypeChecker::new` defaults
// `infer_only = true` (tc/mod.rs:657); only `check_type` flips it to false. The
// exploit tests above assert on `add_decl`/`check_type`, so the *certificate*
// inference path (`infer_type_with_cert`, used by the debug cross-validator) was
// only ever exercised incidentally and never directly asserted — the
// inspection-only gap recorded for the dabf7a35 fix. These tests drive the SAME
// False payloads through `infer_type_with_cert` in check mode and assert
// rejection.

/// Cert path (a): `infer_type_with_cert(myid False True.intro)` in check mode
/// must REJECT — the nested App argument `True.intro : True` is not `False`.
#[test]
fn nested_app_false_cert_path_rejects() {
    let mut env = make_true_false_env();
    add_myid(&mut env);

    let tc = TypeChecker::new(&env);
    // Force check mode: under the default infer_only=true the deep arg check at
    // cert/infer_core.rs:125 is SKIPPED and the exploit would slip through.
    tc.infer_only.set(false);

    let result = tc.infer_type_with_cert(&bad_inner_app());
    assert!(
        result.is_err(),
        "cert path accepted ill-typed nested App argument: {result:?}"
    );
}

/// Cert path (b): `let v : False := myid False True.intro; True.intro` drives the
/// Let-value deep check (cert/infer_core.rs:304) through the cert path. The body
/// is kept CLOSED (a bare `True.intro`, no loose BVar) so the rejection comes
/// from the Let-value check, not an incidental UnboundVariable on the body.
#[test]
fn let_false_cert_path_rejects() {
    let mut env = make_true_false_env();
    add_myid(&mut env);

    let false_const = Expr::const_(Name::from_string("False"), vec![]);
    let closed_body = Expr::const_(Name::from_string("True.intro"), vec![]);
    let proof = Expr::let_named(
        Name::from_string("v"),
        false_const,
        bad_inner_app(),
        closed_body,
        false,
    );

    let tc = TypeChecker::new(&env);
    tc.infer_only.set(false);

    let result = tc.infer_type_with_cert(&proof);
    assert!(
        result.is_err(),
        "cert path accepted a False let-value: {result:?}"
    );
}

/// Positive control: the cert path in check mode must still ACCEPT a well-typed
/// nested application (`myid True True.intro : True`), so the guard above is not
/// over-rejecting valid terms.
#[test]
fn well_typed_nested_app_cert_path_accepts() {
    let mut env = make_true_false_env();
    add_myid(&mut env);

    let true_const = Expr::const_(Name::from_string("True"), vec![]);
    let true_intro = Expr::const_(Name::from_string("True.intro"), vec![]);
    let good = Expr::app(
        Expr::app(Expr::const_(Name::from_string("myid"), vec![]), true_const),
        true_intro,
    );

    let tc = TypeChecker::new(&env);
    tc.infer_only.set(false);

    let result = tc.infer_type_with_cert(&good);
    assert!(
        result.is_ok(),
        "cert path wrongly rejected a well-typed nested App: {result:?}"
    );
}
