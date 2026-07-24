// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `prove()` result-shape regression tests (#2281).

use super::support::build_eq_expr;
use super::*;
use clean_kernel::Expr;

/// Regression test (#2281): prove() must return Err(AyError::Unknown) when
/// the solver times out, not Ok(false) which is indistinguishable from
/// a definitive disproof (Sat counterexample).
#[test]
fn test_prove_unknown_returns_error_not_false() {
    let config = AyBackendConfig::new(AyLogic::QfLia).timeout(0);
    let mut backend = AyBackend::with_config(config);

    // Any provable goal — with zero timeout the solver won't be able to
    // decide either way and should return Unknown.
    let goal = build_eq_expr(Expr::nat_lit(1), Expr::nat_lit(1));
    let result = backend.prove(&goal);

    let err = result.expect_err("prove() must return Err on Unknown, not Ok");
    assert!(
        matches!(err, AyError::Unknown),
        "prove() error on Unknown should be AyError::Unknown, got: {err:?}"
    );
}
