// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Unit tests for the contraction/resolution Alethe-rule handlers. In a
//! `tests_*.rs` file so the ay-coupling ratchet (which scans production files
//! only) skips the synthetic-proof `AletheRule` usage; declared `#[path]` from
//! generic_step.rs so it stays a child module with private-method access.
use super::super::{ReconstructionContext, VariableMapping};
use ay::Sort;
use ay_core::{AletheRule, Proof, ProofId, TermStore};
use clean_kernel::expr::ExprKind;
use clean_kernel::{Expr, Name};

/// `contraction` on `[a, b, b]` → `[a, b]` reconstructs to an `Or.rec` walk
/// that proves the deduplicated conclusion chain. Zero trust.
#[test]
fn contraction_dedup_builds_or_rec() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);

    let mut map = VariableMapping::new();
    map.register_var(
        "a",
        Expr::const_(Name::from_string("PropA"), vec![]),
        Expr::prop(),
    );
    map.register_var(
        "b",
        Expr::const_(Name::from_string("PropB"), vec![]),
        Expr::prop(),
    );

    // Premise is a generic Step whose clause keeps the literal list verbatim
    // (no dedup), so `clause_of_step` yields the duplicated [a, b, b].
    let mut proof = Proof::new();
    let premise = proof.add_rule_step(AletheRule::Trust, vec![a, b, b], vec![], vec![]);
    let _contraction =
        proof.add_rule_step(AletheRule::Contraction, vec![a, b], vec![premise], vec![]);

    let mut ctx = ReconstructionContext::with_proof(&proof, &terms, &map);
    // Seed the premise's reconstructed proof term (placeholder; the unit test
    // only checks the produced *shape*, not full kernel typing).
    ctx.step_cache[premise.0 as usize] = Some(Expr::const_(Name::from_string("hpremise"), vec![]));

    let result = ctx
        .reconstruct_contraction(&[a, b], &[premise], ProofId(1))
        .expect("contraction should reconstruct");

    assert!(
        matches!(result.get_app_fn().kind(), ExprKind::Const(n, _) if n.to_string() == "Or.rec"),
        "expected Or.rec head for dedup contraction, got {:?}",
        result.get_app_fn().kind()
    );
}

/// `contraction` whose conclusion is structurally identical to its premise
/// (no duplicates) returns the premise proof unchanged.
#[test]
fn contraction_identity_returns_premise() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);

    let mut map = VariableMapping::new();
    map.register_var(
        "a",
        Expr::const_(Name::from_string("PropA"), vec![]),
        Expr::prop(),
    );
    map.register_var(
        "b",
        Expr::const_(Name::from_string("PropB"), vec![]),
        Expr::prop(),
    );

    let mut proof = Proof::new();
    let premise = proof.add_rule_step(AletheRule::Trust, vec![a, b], vec![], vec![]);
    let _contraction =
        proof.add_rule_step(AletheRule::Contraction, vec![a, b], vec![premise], vec![]);

    let placeholder = Expr::const_(Name::from_string("hpremise"), vec![]);
    let mut ctx = ReconstructionContext::with_proof(&proof, &terms, &map);
    ctx.step_cache[premise.0 as usize] = Some(placeholder.clone());

    let result = ctx
        .reconstruct_contraction(&[a, b], &[premise], ProofId(1))
        .expect("identity contraction should reconstruct");
    assert_eq!(
        result, placeholder,
        "no-duplicate contraction must return the premise proof unchanged"
    );
}

/// `resolution` with a non-binary premise count fails closed.
#[test]
fn resolution_rule_non_binary_fails_closed() {
    let terms = TermStore::new();
    let map = VariableMapping::new();
    let mut ctx = ReconstructionContext::new(&terms, &map, 1);
    let result =
        ctx.reconstruct_resolution_rule(&[], &[ProofId(0), ProofId(1), ProofId(2)], ProofId(3));
    assert!(
        result.is_err(),
        "n-ary resolution (>2 premises) must fail closed, got {:?}",
        result.map(|e| e.kind().clone())
    );
}
