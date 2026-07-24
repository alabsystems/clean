// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// Collect all Hypothesis FVarIds referenced in a ProofStep tree.
pub(super) fn collect_hypothesis_ids(step: &ProofStep) -> Vec<FVarId> {
    let mut ids = Vec::new();
    collect_hypothesis_ids_inner(step, &mut ids);
    ids
}

fn collect_hypothesis_ids_inner(step: &ProofStep, ids: &mut Vec<FVarId>) {
    match step {
        ProofStep::Hypothesis(id) => ids.push(*id),
        ProofStep::Symm(inner) => collect_hypothesis_ids_inner(inner, ids),
        ProofStep::Trans(l, r) => {
            collect_hypothesis_ids_inner(l, ids);
            collect_hypothesis_ids_inner(r, ids);
        }
        ProofStep::Congr(_, args) => {
            for arg in args {
                collect_hypothesis_ids_inner(arg, ids);
            }
        }
        ProofStep::Refl(_) | ProofStep::Axiom(..) | ProofStep::Propositional(..) => {}
    }
}

/// Extract the constant name from a ProofStep::Congr's function expression.
pub(super) fn congr_func_name(step: &ProofStep) -> Option<String> {
    match step {
        ProofStep::Congr(func_expr, _) => match func_expr.kind() {
            ExprKind::Const(name, _) => Some(name.to_string()),
            _ => None,
        },
        _ => None,
    }
}
