// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Deep recursion regressions for cert WHNF and def_eq stack safety.

use crate::cert::*;
use crate::env::Environment;
use crate::expr::{BinderInfo, Expr};
use crate::Name;

fn empty_env() -> Environment {
    Environment::new()
}

fn deep_let_chain(depth: usize) -> Expr {
    let mut expr = Expr::bvar(0);
    for _ in 0..depth {
        expr = Expr::let_named(Name::anon(), Expr::prop(), Expr::prop(), expr, false);
    }
    expr
}

fn deep_lambda_chain(depth: usize, binder_info: BinderInfo) -> Expr {
    let mut expr = Expr::bvar(0);
    for _ in 0..depth {
        expr = Expr::lam(binder_info, Expr::prop(), expr);
    }
    expr
}

#[test]
fn test_whnf_deep_let_chain_is_stack_safe() {
    let env = empty_env();
    let verifier = CertVerifier::new(&env);

    let result = verifier.whnf(&deep_let_chain(10_000));

    assert_eq!(result, Expr::prop());
}

#[test]
fn test_def_eq_deep_lambda_chain_is_stack_safe() {
    let env = empty_env();
    let verifier = CertVerifier::new(&env);

    assert!(verifier.def_eq(
        &deep_lambda_chain(10_000, BinderInfo::Default),
        &deep_lambda_chain(10_000, BinderInfo::Implicit),
    ));
}

/// Regression: `replay_cert` was not stack-safe (no `stack_safe` wrapper),
/// while the verifier's `verify()` was. A deeply nested certificate tree
/// could cause stack overflow during replay.
#[test]
fn test_replay_cert_deep_def_eq_chain_is_stack_safe() {
    use crate::level::Level;

    // Build a deeply nested cert: DefEq { inner: DefEq { inner: ... Sort } }
    let mut cert = ProofCert::Sort {
        level: Level::zero(),
    };
    let sort_type = Expr::from_kind(crate::expr::ExprKind::Sort(Level::succ(Level::zero())));
    for _ in 0..10_000 {
        cert = ProofCert::DefEq {
            inner: Box::new(cert),
            expected_type: Box::new(sort_type.clone()),
            actual_type: Box::new(sort_type.clone()),
            eq_steps: Vec::new(),
        };
    }

    // This should not stack overflow
    let result = replay_cert(&cert);
    assert_eq!(
        result,
        Expr::from_kind(crate::expr::ExprKind::Sort(Level::zero()))
    );
}
