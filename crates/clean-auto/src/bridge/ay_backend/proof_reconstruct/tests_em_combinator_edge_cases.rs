// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_em_case_split_nonzero_initial_idx_skips_items() {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let p = register_bool_var(&mut terms, &mut map, "fvar_1", 1);
    let q = register_bool_var(&mut terms, &mut map, "fvar_2", 2);
    let r = register_bool_var(&mut terms, &mut map, "fvar_3", 3);
    let not_p = terms.mk_not(p);
    let not_q = terms.mk_not(q);
    let clause = vec![not_p, not_q, r];

    let mut ctx = translation_context(&terms, &map);
    let props = translated_props(&mut ctx, &clause);
    let target = disjunction::or_chain_type(&props);
    let items = vec![EmSplitItem { clause_idx: 0 }, EmSplitItem { clause_idx: 1 }];
    let base_depth = Cell::new(None);

    let result =
        ctx.build_em_case_split(&clause, &props, &target, &items, ProofId(0), 1, &|depth| {
            base_depth.set(Some(depth));
            Ok(disjunction::inject_into_or_chain(&props, 2, Expr::bvar(0)))
        });

    assert!(result.is_ok(), "nonzero initial idx should still succeed");
    assert_eq!(
        base_depth.get(),
        Some(2),
        "depth should remain items.len() even when idx skips early items"
    );
}

/// Verify the negative-case lambda body uses bvar(0) to reference its own
/// lambda parameter. This catches off-by-one BVar indexing in em_combinator.rs
/// line 65: if `Expr::bvar(0)` were changed to `bvar(1)`, this test fails.
#[test]
fn test_em_case_split_negative_body_uses_bvar_zero() {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let p = register_bool_var(&mut terms, &mut map, "fvar_1", 1);
    let q = register_bool_var(&mut terms, &mut map, "fvar_2", 2);
    let not_p = terms.mk_not(p);
    let clause = vec![not_p, q];

    let mut ctx = translation_context(&terms, &map);
    let props = translated_props(&mut ctx, &clause);
    let target = disjunction::or_chain_type(&props);
    let items = vec![EmSplitItem { clause_idx: 0 }];

    let result =
        ctx.build_em_case_split(&clause, &props, &target, &items, ProofId(0), 0, &|_depth| {
            Ok(disjunction::inject_into_or_chain(&props, 1, Expr::bvar(0)))
        });

    let proof_term = result.expect("single-item split should succeed");
    let args = proof_term.get_app_args();
    assert_eq!(args.len(), 6, "Or.rec should have 6 args");

    // args[4] = case_neg = λ(¬P). Or.inl(¬P, Q, bvar(0))
    let case_neg = &args[4];
    let ExprKind::Lam(_, _binder_type, body) = case_neg.kind() else {
        panic!(
            "case_neg (args[4]) should be a lambda, got {:?}",
            case_neg.kind()
        );
    };

    // The lambda body is Or.inl applied to 3 args; the last arg is the proof.
    let body_args = body.get_app_args();
    assert!(
        body_args.len() >= 3,
        "Or.inl in negative case body should have >= 3 args, got {}",
        body_args.len()
    );
    let injected_proof = &body_args[body_args.len() - 1];
    assert!(
        matches!(injected_proof.kind(), ExprKind::BVar(0)),
        "negative case should inject bvar(0) (its own lambda parameter), got {:?}",
        injected_proof.kind()
    );
}

/// When idx == items.len(), the combinator immediately calls base_case
/// without creating any Or.rec wrapper. Verifies degenerate boundary.
#[test]
fn test_em_case_split_idx_equals_len_immediate_base_case() {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let p = register_bool_var(&mut terms, &mut map, "fvar_1", 1);
    let q = register_bool_var(&mut terms, &mut map, "fvar_2", 2);
    let not_p = terms.mk_not(p);
    let clause = vec![not_p, q];

    let mut ctx = translation_context(&terms, &map);
    let props = translated_props(&mut ctx, &clause);
    let target = disjunction::or_chain_type(&props);
    let items = vec![EmSplitItem { clause_idx: 0 }];
    let base_called = Cell::new(false);

    // idx = 1 = items.len(), so we skip past all items immediately
    let sentinel = Expr::const_(Name::from_string("sentinel_base"), vec![]);
    let result =
        ctx.build_em_case_split(&clause, &props, &target, &items, ProofId(0), 1, &|depth| {
            base_called.set(true);
            assert_eq!(depth, 1, "depth should be items.len() = 1");
            Ok(sentinel.clone())
        });

    assert!(base_called.get(), "base case should be called immediately");
    let proof_term = result.expect("idx==len should succeed");
    // The result should be exactly the sentinel, NOT wrapped in Or.rec
    let ExprKind::Const(name, _) = proof_term.kind() else {
        panic!(
            "expected sentinel Const, got {:?} — combinator should NOT wrap in Or.rec when idx==len",
            proof_term.kind()
        );
    };
    assert_eq!(name.to_string(), "sentinel_base");
}
