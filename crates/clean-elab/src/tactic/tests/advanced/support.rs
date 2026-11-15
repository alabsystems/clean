// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared helpers for the advanced tactic test suite.

use super::*;

/// Build a `LocalDecl` with an explicit fixed fixture name (not source text).
pub(super) fn make_local(id: u64, name: &'static str, ty: Expr) -> LocalDecl {
    LocalDecl {
        binder_info: Default::default(),
        fvar: FVarId::new(id),
        name: clean_parser::SurfaceName::generated_path(name),
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
