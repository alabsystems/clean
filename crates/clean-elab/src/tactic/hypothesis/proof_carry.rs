// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::{Expr, ExprKind, Level};

use crate::tactic::{Goal, ProofState, TacticError, TacticResult};

pub(super) fn infer_sort_level(
    state: &ProofState,
    goal: &Goal,
    ty: &Expr,
    detail: &'static str,
) -> Result<Level, TacticError> {
    state
        .infer_type(goal, ty)
        .ok()
        .and_then(|sort| match sort.kind() {
            ExprKind::Sort(level) => Some(level.clone()),
            _ => None,
        })
        .ok_or_else(|| TacticError::TypeCheckFailed(detail.into()))
}

pub(super) fn replace_local_hyp_with_proof(
    state: &mut ProofState,
    goal: &Goal,
    hyp_idx: usize,
    new_ty: Expr,
    cast_proof: Expr,
) -> TacticResult {
    let hyp_fvar = goal
        .local_ctx
        .get(hyp_idx)
        .map(|decl| decl.fvar)
        .expect("invariant: hypothesis index came from goal.local_ctx");
    state.replace_local_decl_with_cast(hyp_fvar, new_ty, cast_proof)
}
