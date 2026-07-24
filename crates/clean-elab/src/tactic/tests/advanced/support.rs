// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared helpers for the advanced tactic test suite.

use super::*;

/// Build a `LocalDecl` with the given fvar id, name, and type.
pub(super) fn make_local(id: u64, name: &str, ty: Expr) -> LocalDecl {
    LocalDecl {
        fvar: FVarId::new(id),
        name: name.to_string(),
        ty,
        value: None,
    }
}

pub(super) fn close_current_goal_checked(state: &mut ProofState, proof: Expr) {
    let goal = state
        .current_goal()
        .expect("test fixture should have an active goal")
        .clone();
    state
        .close_goal(&goal, proof)
        .expect("test fixture proof should close the current goal");
}
