// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::fixtures::*;
use super::*;

mod core;
mod queries;
mod recursor;

fn assert_valid_result(
    arena: &batch::VerificationArena,
    idx: u32,
    expected_ty: &Expr,
    context: &str,
) {
    let result = arena
        .get_result(idx)
        .expect("verification result should exist after verify_all");
    assert!(
        result.valid,
        "{context}: expected valid result, got {result:?}"
    );
    assert_eq!(
        result.inferred_type.as_ref(),
        Some(expected_ty),
        "{context}: inferred type mismatch"
    );
}

fn assert_invalid_result(arena: &batch::VerificationArena, idx: u32, context: &str) {
    let result = arena
        .get_result(idx)
        .expect("verification result should exist after verify_all");
    assert!(
        !result.valid,
        "{context}: expected invalid result, got {result:?}"
    );
}
