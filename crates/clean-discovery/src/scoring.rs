// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Scoring functions for novelty assessment of candidate theorems.
//!
//! Provides bound tightness, parameter novelty, and proof compactness
//! scoring used by the `NoveltyFilter`.
//!
//! Part of #3272.

use crate::candidate::{CandidateTheorem, ParamValue};
use crate::family::TheoremFamily;
use clean_kernel::ExprKind;

/// Maximum node count for normalization. Proofs larger than this get score 0.
pub(crate) const MAX_PROOF_NODES: usize = 1000;

/// Score bound tightness based on the bound function variant.
///
/// For `CertSizeBound` family, the first parameter is a `Choice` index
/// mapping to: 0=Linear, 1=QuadraticWidth, 2=QuadraticDepth, 3=QuadraticBoth.
/// Lower-order polynomials (Linear) are tighter bounds and score higher.
///
/// Also factors in the constant C: lower C means a tighter bound.
pub(crate) fn score_bound_tightness(theorem: &CandidateTheorem) -> f64 {
    if theorem.family != TheoremFamily::CertSizeBound {
        return 0.5; // neutral score for other families
    }

    let params = &theorem.params.0;
    if params.is_empty() {
        return 0.5;
    }

    // Bound function variant score (index 0).
    let variant_score = match params.first() {
        Some(ParamValue::Choice(0)) => 1.0,  // Linear - tightest
        Some(ParamValue::Choice(1)) => 0.75, // QuadraticWidth
        Some(ParamValue::Choice(2)) => 0.5,  // QuadraticDepth
        Some(ParamValue::Choice(3)) => 0.25, // QuadraticBoth - loosest
        _ => 0.5,
    };

    // Constant C score (index 1): lower C = tighter = higher score.
    let c_score = match params.get(1) {
        Some(ParamValue::Nat(c)) if *c > 0 => 1.0 / (*c as f64),
        _ => 0.5,
    };

    // Weighted combination: variant matters more than constant.
    0.7 * variant_score + 0.3 * c_score
}

/// Score parameter novelty based on how unusual the parameter combination is.
///
/// Higher depth and width values are less common in typical proofs, so they
/// score higher for novelty.
pub(crate) fn score_parameter_novelty(theorem: &CandidateTheorem) -> f64 {
    let params = &theorem.params.0;
    if params.is_empty() {
        return 0.0;
    }

    // For CertSizeBound: params are [choice, C, depth, width].
    // Higher depth/width = more novel.
    let depth = match params.get(2) {
        Some(ParamValue::Nat(d)) => *d as f64,
        _ => 1.0,
    };
    let width = match params.get(3) {
        Some(ParamValue::Nat(w)) => *w as f64,
        _ => 1.0,
    };

    // Normalize: assume max useful values around 10.
    let depth_score = (depth / 10.0).min(1.0);
    let width_score = (width / 10.0).min(1.0);

    (depth_score + width_score) / 2.0
}

/// Score proof compactness based on the Expr node count.
///
/// Smaller proofs are more elegant and score higher.
pub(crate) fn score_proof_compactness(theorem: &CandidateTheorem) -> f64 {
    let node_count = match &theorem.proof {
        Some(proof) => count_expr_nodes(proof),
        None => {
            // No proof term: score based on statement size instead.
            count_expr_nodes(&theorem.statement)
        }
    };

    if node_count == 0 {
        return 1.0;
    }

    if node_count >= MAX_PROOF_NODES {
        return 0.0;
    }

    // Inverse relationship: fewer nodes = higher score.
    1.0 - (node_count as f64 / MAX_PROOF_NODES as f64)
}

/// Count the number of nodes in an `Expr` tree.
///
/// Traverses the expression recursively, counting each constructor as one node.
/// Uses the public `Expr::kind()` -> `ExprKind` API.
pub(crate) fn count_expr_nodes(expr: &clean_kernel::Expr) -> usize {
    match expr.kind() {
        ExprKind::BVar(_) | ExprKind::FVar(_) | ExprKind::Sort(_) | ExprKind::Lit(_) => 1,
        ExprKind::Const(_, _) => 1,
        ExprKind::App(f, a) => 1 + count_expr_nodes(f) + count_expr_nodes(a),
        ExprKind::Lam(_, domain, body) | ExprKind::Pi(_, domain, body) => {
            1 + count_expr_nodes(domain) + count_expr_nodes(body)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            1 + count_expr_nodes(ty) + count_expr_nodes(val) + count_expr_nodes(body)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => 1 + count_expr_nodes(inner),
        // Catch any future variants conservatively.
        _ => 1,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::Expr;

    #[test]
    fn test_count_expr_nodes_simple() {
        assert_eq!(count_expr_nodes(&Expr::prop()), 1);
    }

    #[test]
    fn test_count_expr_nodes_app() {
        let f = Expr::const_str("f");
        let x = Expr::const_str("x");
        let app = Expr::app(f, x);
        // app(f, x) = 1(app) + 1(f) + 1(x) = 3
        assert_eq!(count_expr_nodes(&app), 3);
    }

    #[test]
    fn test_count_expr_nodes_nested() {
        let f = Expr::const_str("f");
        let x = Expr::const_str("x");
        let y = Expr::const_str("y");
        let app_inner = Expr::app(f, x);
        let app_outer = Expr::app(app_inner, y);
        // app(app(f, x), y) = 1 + (1 + 1 + 1) + 1 = 5
        assert_eq!(count_expr_nodes(&app_outer), 5);
    }
}
