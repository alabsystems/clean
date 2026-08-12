// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for let_rec_ext2: mutual recursion analysis, termination hints,
//! dependency ordering, recursion depth estimation, binding statistics,
//! inlining candidates, and well-foundedness hints.

use clean_kernel::{Expr, FVarId};

use crate::let_rec_ext::LetRecBinding;
use crate::let_rec_ext2::*;

// =============================================================================
// Helper constructors
// =============================================================================

fn mk_binding(name: &str, fvar_id: u64, params: Vec<(&str, Expr)>, body: Expr) -> LetRecBinding {
    LetRecBinding {
        name: name.to_string(),
        params: params
            .into_iter()
            .map(|(n, ty)| (n.to_string(), ty))
            .collect(),
        return_type: None,
        body,
        fvar_id,
    }
}

fn nat_ty() -> Expr {
    Expr::const_str("Nat")
}

// Test scaffolding not exercised by every including build — kept per the 2026-07-30
// keep-and-annotate sweep; see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md.
#[allow(dead_code)]
fn bool_ty() -> Expr {
    Expr::const_str("Bool")
}

fn list_ty() -> Expr {
    Expr::const_str("List")
}

/// A self-recursive call: `fvar(id) applied to arg`.
fn self_call(fvar_id: u64, arg: Expr) -> Expr {
    Expr::app(Expr::fvar(FVarId::new(fvar_id)), arg)
}

/// A call to another binding's fvar.
fn call_other(fvar_id: u64) -> Expr {
    Expr::fvar(FVarId::new(fvar_id))
}

/// Build `f(g(x))` — a nested call.
fn nested_call(outer_fvar: u64, inner_fvar: u64, x: Expr) -> Expr {
    let inner = Expr::app(Expr::fvar(FVarId::new(inner_fvar)), x);
    Expr::app(Expr::fvar(FVarId::new(outer_fvar)), inner)
}

// =============================================================================
// Mutual recursion analysis tests
// =============================================================================

#[test]
fn test_mutual_analysis_empty_bindings_errors() {
    let result = analyze_mutual_recursion(&[]);
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        LetRecExt2Error::EmptyBindings
    ));
}

#[test]
fn test_mutual_analysis_single_nonrecursive() {
    let b = mk_binding("f", 1, vec![("x", nat_ty())], Expr::bvar(0));
    let analysis = analyze_mutual_recursion(&[b]).expect("should succeed");
    assert_eq!(analysis.patterns.len(), 1);
    assert_eq!(analysis.patterns[0], MutualPattern::Independent);
}

#[test]
fn test_mutual_analysis_single_self_recursive() {
    // f(x) = f(x) — trivially self-recursive.
    let b = mk_binding("f", 1, vec![("x", nat_ty())], self_call(1, Expr::bvar(0)));
    let analysis = analyze_mutual_recursion(&[b]).expect("should succeed");
    assert_eq!(analysis.patterns[0], MutualPattern::SelfRecursive);
}

#[test]
fn test_mutual_analysis_two_mutual() {
    // f calls g, g calls f.
    let f = mk_binding("f", 1, vec![("x", nat_ty())], call_other(2));
    let g = mk_binding("g", 2, vec![("x", nat_ty())], call_other(1));
    let analysis = analyze_mutual_recursion(&[f, g]).expect("should succeed");
    assert_eq!(analysis.patterns[0], MutualPattern::MutualRecursive);
    assert_eq!(analysis.patterns[1], MutualPattern::MutualRecursive);
    // Should have one SCC with both.
    assert!(analysis.sccs.iter().any(|scc| scc.len() == 2));
}

#[test]
fn test_mutual_analysis_leaf_binding() {
    // f calls g, g does not call anyone.
    let f = mk_binding("f", 1, vec![("x", nat_ty())], call_other(2));
    let g = mk_binding("g", 2, vec![("x", nat_ty())], Expr::bvar(0));
    let analysis = analyze_mutual_recursion(&[f, g]).expect("should succeed");
    // f is independent (calls g but no cycle).
    // g is a leaf (called by f, calls nobody).
    assert_eq!(analysis.patterns[1], MutualPattern::Leaf);
}

#[test]
fn test_mutual_analysis_forward_reverse_edges() {
    // f -> g, g -> h.
    let f = mk_binding("f", 1, vec![], call_other(2));
    let g = mk_binding("g", 2, vec![], call_other(3));
    let h = mk_binding("h", 3, vec![], Expr::bvar(0));
    let analysis = analyze_mutual_recursion(&[f, g, h]).expect("should succeed");
    assert!(analysis.forward_edges[0].contains(&1)); // f -> g
    assert!(analysis.forward_edges[1].contains(&2)); // g -> h
    assert!(analysis.reverse_edges[1].contains(&0)); // g <- f
    assert!(analysis.reverse_edges[2].contains(&1)); // h <- g
}

#[test]
fn test_mutual_analysis_three_way_cycle() {
    // f -> g, g -> h, h -> f.
    let f = mk_binding("f", 1, vec![], call_other(2));
    let g = mk_binding("g", 2, vec![], call_other(3));
    let h = mk_binding("h", 3, vec![], call_other(1));
    let analysis = analyze_mutual_recursion(&[f, g, h]).expect("should succeed");
    assert_eq!(analysis.patterns[0], MutualPattern::MutualRecursive);
    assert_eq!(analysis.patterns[1], MutualPattern::MutualRecursive);
    assert_eq!(analysis.patterns[2], MutualPattern::MutualRecursive);
    assert!(analysis.sccs.iter().any(|scc| scc.len() == 3));
}

#[test]
fn test_mutual_analysis_mixed_block() {
    // f is self-recursive, g is independent, h is leaf called by f.
    let f = mk_binding(
        "f",
        1,
        vec![("x", nat_ty())],
        Expr::app(self_call(1, Expr::bvar(0)), call_other(3)),
    );
    let g = mk_binding("g", 2, vec![], Expr::const_str("hello"));
    let h = mk_binding("h", 3, vec![], Expr::bvar(0));
    let analysis = analyze_mutual_recursion(&[f, g, h]).expect("should succeed");
    assert_eq!(analysis.patterns[0], MutualPattern::SelfRecursive);
    assert_eq!(analysis.patterns[1], MutualPattern::Independent);
    assert_eq!(analysis.patterns[2], MutualPattern::Leaf);
}

// =============================================================================
// Termination hint tests
// =============================================================================

#[test]
fn test_termination_hints_nonrecursive_empty() {
    let b = mk_binding("f", 1, vec![("n", nat_ty())], Expr::bvar(0));
    let hints = collect_termination_hints(&b);
    // Non-recursive: only InductiveType hint from the param type.
    assert!(hints
        .iter()
        .all(|h| matches!(h.evidence, DecreaseEvidence::InductiveType { .. })));
}

#[test]
fn test_termination_hints_nat_param_type() {
    let b = mk_binding("f", 1, vec![("n", nat_ty())], self_call(1, Expr::bvar(0)));
    let hints = collect_termination_hints(&b);
    assert!(hints
        .iter()
        .any(|h| h.param_name == "n" && matches!(&h.evidence, DecreaseEvidence::InductiveType { type_name } if type_name == "Nat")));
}

#[test]
fn test_termination_hints_list_param_type() {
    let b = mk_binding("f", 1, vec![("xs", list_ty())], self_call(1, Expr::bvar(0)));
    let hints = collect_termination_hints(&b);
    assert!(hints
        .iter()
        .any(|h| h.param_name == "xs" && matches!(&h.evidence, DecreaseEvidence::InductiveType { type_name } if type_name == "List")));
}

#[test]
fn test_termination_hints_destructor_app() {
    // f(n) = f(Nat.pred(n))
    let pred_call = Expr::app(Expr::const_str("Nat.pred"), Expr::bvar(0));
    let body = self_call(1, pred_call);
    let b = mk_binding("f", 1, vec![("n", nat_ty())], body);
    let hints = collect_termination_hints(&b);
    assert!(hints.iter().any(|h| matches!(
        &h.evidence,
        DecreaseEvidence::DestructorApp { destructor } if destructor == "Nat.pred"
    )));
}

#[test]
fn test_termination_hints_sub_expr_arg() {
    // f(n) = f(some_expr) where some_expr is not a known destructor.
    let body = self_call(1, Expr::const_str("something"));
    let b = mk_binding("f", 1, vec![("n", nat_ty())], body);
    let hints = collect_termination_hints(&b);
    assert!(hints
        .iter()
        .any(|h| h.evidence == DecreaseEvidence::SubExprArg));
}

#[test]
fn test_termination_hints_no_params() {
    let b = mk_binding("f", 1, vec![], self_call(1, Expr::const_str("x")));
    let hints = collect_termination_hints(&b);
    assert!(hints.is_empty());
}

// =============================================================================
// Dependency ordering tests
// =============================================================================

#[test]
fn test_dependency_order_empty_errors() {
    let result = dependency_order(&[]);
    assert!(result.is_err());
}

#[test]
fn test_dependency_order_single() {
    let b = mk_binding("f", 1, vec![], Expr::bvar(0));
    let order = dependency_order(&[b]).expect("should succeed");
    assert_eq!(order, vec![0]);
}

#[test]
fn test_dependency_order_chain() {
    // f depends on g, g depends on h. Expected: h, g, f.
    let f = mk_binding("f", 1, vec![], call_other(2));
    let g = mk_binding("g", 2, vec![], call_other(3));
    let h = mk_binding("h", 3, vec![], Expr::bvar(0));
    let order = dependency_order(&[f, g, h]).expect("should succeed");
    // h (idx 2) should come before g (idx 1), which should come before f (idx 0).
    let pos_f = order.iter().position(|&x| x == 0).expect("f present");
    let pos_g = order.iter().position(|&x| x == 1).expect("g present");
    let pos_h = order.iter().position(|&x| x == 2).expect("h present");
    assert!(pos_h < pos_g);
    assert!(pos_g < pos_f);
}

#[test]
fn test_dependency_order_cycle_errors() {
    let f = mk_binding("f", 1, vec![], call_other(2));
    let g = mk_binding("g", 2, vec![], call_other(1));
    let result = dependency_order(&[f, g]);
    assert!(result.is_err());
    assert!(matches!(
        result.unwrap_err(),
        LetRecExt2Error::CycleDetected { count: 2 }
    ));
}

#[test]
fn test_dependency_order_independent_bindings() {
    let f = mk_binding("f", 1, vec![], Expr::bvar(0));
    let g = mk_binding("g", 2, vec![], Expr::bvar(0));
    let order = dependency_order(&[f, g]).expect("should succeed");
    assert_eq!(order.len(), 2);
    // Both should appear, order doesn't matter.
    assert!(order.contains(&0));
    assert!(order.contains(&1));
}

// =============================================================================
// Recursion depth estimation tests
// =============================================================================

#[test]
fn test_depth_estimate_nonrecursive() {
    let b = mk_binding("f", 1, vec![("x", nat_ty())], Expr::bvar(0));
    let est = estimate_recursion_depth(&b);
    assert_eq!(est.call_site_count, 0);
    assert!(!est.has_tail_calls);
    assert!(!est.is_nonlinear);
}

#[test]
fn test_depth_estimate_single_tail_call() {
    // f(x) = f(x) — tail recursive.
    let b = mk_binding("f", 1, vec![("x", nat_ty())], self_call(1, Expr::bvar(0)));
    let est = estimate_recursion_depth(&b);
    assert_eq!(est.call_site_count, 1);
    assert!(est.has_tail_calls);
    assert!(!est.is_nonlinear);
}

#[test]
fn test_depth_estimate_nonlinear() {
    // f(x) = f(x) + f(x) — two calls in one branch.
    let body = Expr::app(self_call(1, Expr::bvar(0)), self_call(1, Expr::bvar(0)));
    let b = mk_binding("f", 1, vec![("x", nat_ty())], body);
    let est = estimate_recursion_depth(&b);
    assert!(est.call_site_count >= 2);
    assert!(
        est.is_nonlinear,
        "two self-calls in the same branch must flag is_nonlinear=true"
    );
}

/// Wave 101 negative test: a single self-call (linear recursion) must NOT
/// be flagged as nonlinear. This proves the count-calls walker is
/// conservative and only sets `is_nonlinear` when a branch genuinely
/// contains more than one recursive call.
#[test]
fn test_depth_estimate_single_call_is_linear() {
    // f(x) = f(x) — exactly one call site.
    let body = self_call(1, Expr::bvar(0));
    let b = mk_binding("f", 1, vec![("x", nat_ty())], body);
    let est = estimate_recursion_depth(&b);
    assert_eq!(est.call_site_count, 1);
    assert!(
        !est.is_nonlinear,
        "a single self-call must not flag is_nonlinear=true"
    );
}

#[test]
fn test_depth_estimate_nested_calls() {
    // f(x) = f(f(x)) — nested recursive call.
    let body = nested_call(1, 1, Expr::bvar(0));
    let b = mk_binding("f", 1, vec![("x", nat_ty())], body);
    let est = estimate_recursion_depth(&b);
    assert!(est.max_call_nesting >= 1);
}

// =============================================================================
// Binding statistics tests
// =============================================================================

#[test]
fn test_binding_stats_empty_errors() {
    let result = compute_binding_stats(&[]);
    assert!(result.is_err());
}

#[test]
fn test_binding_stats_single_nonrecursive() {
    let b = mk_binding("f", 1, vec![("x", nat_ty())], Expr::bvar(0));
    let stats = compute_binding_stats(&[b]).expect("should succeed");
    assert_eq!(stats.total, 1);
    assert_eq!(stats.non_recursive, 1);
    assert_eq!(stats.self_recursive, 0);
    assert_eq!(stats.mutual_recursive, 0);
    assert_eq!(stats.total_params, 1);
}

#[test]
fn test_binding_stats_mixed() {
    let f = mk_binding("f", 1, vec![("x", nat_ty())], self_call(1, Expr::bvar(0)));
    let g = mk_binding("g", 2, vec![], Expr::const_str("hello"));
    let stats = compute_binding_stats(&[f, g]).expect("should succeed");
    assert_eq!(stats.total, 2);
    assert_eq!(stats.self_recursive, 1);
    assert_eq!(stats.non_recursive, 1);
    assert_eq!(stats.total_params, 1);
}

#[test]
fn test_binding_stats_expr_size() {
    // Body: app(bvar(0), bvar(1)) — 3 nodes.
    let body = Expr::app(Expr::bvar(0), Expr::bvar(1));
    let b = mk_binding("f", 1, vec![], body);
    let stats = compute_binding_stats(&[b]).expect("should succeed");
    assert_eq!(stats.max_expr_size, 3);
    assert_eq!(stats.total_expr_size, 3);
}

#[test]
fn test_binding_stats_mutual_count() {
    let f = mk_binding("f", 1, vec![], call_other(2));
    let g = mk_binding("g", 2, vec![], call_other(1));
    let stats = compute_binding_stats(&[f, g]).expect("should succeed");
    assert_eq!(stats.mutual_recursive, 2);
}

// =============================================================================
// Inlining candidate tests
// =============================================================================

#[test]
fn test_inlining_empty_errors() {
    let result = score_inlining_candidates(&[]);
    assert!(result.is_err());
}

#[test]
fn test_inlining_small_nonrecursive_high_score() {
    let b = mk_binding("f", 1, vec![], Expr::bvar(0));
    let candidates = score_inlining_candidates(&[b]).expect("should succeed");
    assert_eq!(candidates.len(), 1);
    // Small + non-recursive should yield high score.
    assert!(candidates[0].score > 0.7);
    assert!(candidates[0]
        .reasons
        .contains(&InliningReason::NonRecursive));
    assert!(candidates[0]
        .reasons
        .iter()
        .any(|r| matches!(r, InliningReason::SmallBody { .. })));
}

#[test]
fn test_inlining_recursive_low_score() {
    let b = mk_binding("f", 1, vec![("x", nat_ty())], self_call(1, Expr::bvar(0)));
    let candidates = score_inlining_candidates(&[b]).expect("should succeed");
    assert!(
        candidates[0].score < 0.5,
        "self-recursive binding score must be penalised below 0.5; got {}",
        candidates[0].score
    );
    assert!(
        candidates[0].reasons.contains(&InliningReason::Recursive),
        "self-recursive binding must surface the Recursive reason; got {:?}",
        candidates[0].reasons
    );
}

#[test]
fn test_inlining_mutual_recursive_lowest_score() {
    let f = mk_binding("f", 1, vec![], call_other(2));
    let g = mk_binding("g", 2, vec![], call_other(1));
    let candidates = score_inlining_candidates(&[f, g]).expect("should succeed");
    for c in &candidates {
        assert!(
            c.score < 0.3,
            "mutually-recursive binding score must be penalised below 0.3; got {} for {}",
            c.score,
            c.name
        );
        assert!(
            c.reasons.contains(&InliningReason::MutualRecursion),
            "mutually-recursive binding must surface the MutualRecursion reason; got {:?} for {}",
            c.reasons,
            c.name
        );
    }
}

/// Wave 101 negative test: a non-recursive binding must NOT have its score
/// dragged below 0.5 by a phantom Recursive/MutualRecursion penalty.
/// Proves the penalties only fire for genuinely-recursive patterns.
#[test]
fn test_inlining_nonrecursive_not_penalised_as_recursive() {
    let b = mk_binding("f", 1, vec![("x", nat_ty())], Expr::bvar(0));
    let candidates = score_inlining_candidates(&[b]).expect("should succeed");
    assert!(
        candidates[0].score >= 0.5,
        "non-recursive binding must not be penalised below 0.5; got {}",
        candidates[0].score
    );
    assert!(
        !candidates[0].reasons.contains(&InliningReason::Recursive),
        "non-recursive binding must not surface the Recursive reason; got {:?}",
        candidates[0].reasons
    );
    assert!(
        !candidates[0]
            .reasons
            .contains(&InliningReason::MutualRecursion),
        "non-recursive binding must not surface the MutualRecursion reason; got {:?}",
        candidates[0].reasons
    );
}

#[test]
fn test_inlining_single_use_bonus() {
    // Two bindings: f and g. f references g once, g references nobody.
    let f = mk_binding("f", 1, vec![], call_other(2));
    let g = mk_binding("g", 2, vec![], Expr::bvar(0));
    let candidates = score_inlining_candidates(&[f, g]).expect("should succeed");
    // g is used once by f, and only once total.
    let g_candidate = &candidates[1];
    assert!(g_candidate.reasons.contains(&InliningReason::SingleUse));
}

#[test]
fn test_inlining_score_clamped() {
    // Ensure scores stay in [0.0, 1.0] even with many bonuses/penalties.
    let b = mk_binding("f", 1, vec![], Expr::bvar(0));
    let candidates = score_inlining_candidates(&[b]).expect("should succeed");
    assert!(candidates[0].score >= 0.0);
    assert!(candidates[0].score <= 1.0);
}

// =============================================================================
// Well-foundedness hint tests
// =============================================================================

#[test]
fn test_wf_hints_empty_errors() {
    let result = suggest_well_foundedness(&[]);
    assert!(result.is_err());
}

#[test]
fn test_wf_hints_nat_param() {
    let b = mk_binding("f", 1, vec![("n", nat_ty())], self_call(1, Expr::bvar(0)));
    let hints = suggest_well_foundedness(&[b]).expect("should succeed");
    assert!(hints
        .iter()
        .any(|h| h.relation == "Nat.lt" && h.confidence == HintConfidence::High));
}

#[test]
fn test_wf_hints_list_param() {
    let b = mk_binding("f", 1, vec![("xs", list_ty())], self_call(1, Expr::bvar(0)));
    let hints = suggest_well_foundedness(&[b]).expect("should succeed");
    assert!(hints
        .iter()
        .any(|h| h.relation == "List.length" && h.confidence == HintConfidence::High));
}

#[test]
fn test_wf_hints_destructor_medium_confidence() {
    let pred_call = Expr::app(Expr::const_str("Nat.pred"), Expr::bvar(0));
    let body = self_call(1, pred_call);
    let b = mk_binding("f", 1, vec![("n", nat_ty())], body);
    let hints = suggest_well_foundedness(&[b]).expect("should succeed");
    assert!(hints.iter().any(|h| h.confidence == HintConfidence::Medium));
}

#[test]
fn test_wf_hints_fallback_sizeof() {
    // Recursive binding with non-inductive param type — should get low-confidence sizeOf.
    let b = mk_binding(
        "f",
        1,
        vec![("x", Expr::type_())],
        self_call(1, Expr::bvar(0)),
    );
    let _hints = suggest_well_foundedness(&[b]).expect("should succeed");
    // Type param (Sort) is skipped, so we might get no fallback.
    // In this case, Expr::type_() is a Sort, so no sizeOf fallback is generated.
    // We verify graceful handling — no panic, no error.
}

#[test]
fn test_wf_hints_fallback_with_nonsort_param() {
    // Recursive with a non-inductive, non-sort param.
    let b = mk_binding(
        "f",
        1,
        vec![("x", Expr::const_str("MyCustomType"))],
        self_call(1, Expr::bvar(0)),
    );
    let hints = suggest_well_foundedness(&[b]).expect("should succeed");
    // Should get at least a low-confidence sizeOf hint.
    assert!(hints
        .iter()
        .any(|h| h.relation == "sizeOf" && h.confidence == HintConfidence::Low));
}

#[test]
fn test_wf_hints_nonrecursive_no_fallback() {
    let b = mk_binding("f", 1, vec![("x", nat_ty())], Expr::bvar(0));
    let hints = suggest_well_foundedness(&[b]).expect("should succeed");
    // Non-recursive: should only get InductiveType hints, no fallback sizeOf.
    assert!(hints.iter().all(|h| h.confidence == HintConfidence::High));
}

#[test]
fn test_wf_hints_multiple_params() {
    let b = mk_binding(
        "f",
        1,
        vec![("n", nat_ty()), ("xs", list_ty())],
        self_call(1, Expr::bvar(1)),
    );
    let hints = suggest_well_foundedness(&[b]).expect("should succeed");
    // Should have hints for both params.
    assert!(hints.iter().any(|h| h.param_idx == 0));
    assert!(hints.iter().any(|h| h.param_idx == 1));
}

// =============================================================================
// Error display tests
// =============================================================================

#[test]
fn test_error_display_empty_bindings() {
    let err = LetRecExt2Error::EmptyBindings;
    assert_eq!(err.to_string(), "empty binding set");
}

#[test]
fn test_error_display_index_out_of_range() {
    let err = LetRecExt2Error::IndexOutOfRange { idx: 5, max: 3 };
    assert_eq!(err.to_string(), "binding index 5 out of range (max 3)");
}

#[test]
fn test_error_display_cycle_detected() {
    let err = LetRecExt2Error::CycleDetected { count: 2 };
    assert_eq!(
        err.to_string(),
        "cycle detected in dependency graph involving 2 bindings"
    );
}
