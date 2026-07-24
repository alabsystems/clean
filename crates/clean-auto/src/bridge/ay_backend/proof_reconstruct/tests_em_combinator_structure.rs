// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_em_case_split_single_item_produces_or_rec() {
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
        ctx.build_em_case_split(&clause, &props, &target, &items, ProofId(0), 0, &|depth| {
            assert_eq!(depth, 1, "base case depth should equal items.len()");
            Ok(disjunction::inject_into_or_chain(&props, 1, Expr::bvar(0)))
        });

    let proof_term = result.expect("single-item em case split should succeed");
    let head = proof_term.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(_, _)),
        "expected Const head for single-item split, got {:?}",
        head.kind()
    );
    let ExprKind::Const(name, _) = head.kind() else {
        unreachable!("asserted Const head above");
    };
    assert_eq!(name.to_string(), "Or.rec");
}

#[test]
fn test_em_case_split_empty_items_calls_base_case_at_depth_zero() {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let p = register_bool_var(&mut terms, &mut map, "fvar_1", 1);
    let clause = vec![p];

    let mut ctx = translation_context(&terms, &map);
    let props = translated_props(&mut ctx, &clause);
    let target = disjunction::or_chain_type(&props);
    let base_called = Cell::new(false);

    let result = ctx.build_em_case_split(&clause, &props, &target, &[], ProofId(0), 0, &|depth| {
        base_called.set(true);
        assert_eq!(depth, 0, "empty items should call base_case with depth 0");
        Ok(Expr::const_(Name::from_string("placeholder"), vec![]))
    });

    assert!(result.is_ok(), "empty items should succeed");
    assert!(
        base_called.get(),
        "base case should be called for empty items"
    );
}

#[test]
fn test_em_case_split_two_items_nested_or_rec() {
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
        ctx.build_em_case_split(&clause, &props, &target, &items, ProofId(0), 0, &|depth| {
            base_depth.set(Some(depth));
            Ok(disjunction::inject_into_or_chain(&props, 2, Expr::bvar(0)))
        });

    let proof_term = result.expect("two-item em case split should succeed");
    assert_eq!(base_depth.get(), Some(2));
    let head = proof_term.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(_, _)),
        "expected Const head for two-item split, got {:?}",
        head.kind()
    );
    let ExprKind::Const(name, _) = head.kind() else {
        unreachable!("asserted Const head above");
    };
    assert_eq!(name.to_string(), "Or.rec");
}

#[test]
fn test_em_case_split_sparse_items_skips_middle_literal() {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let p = register_bool_var(&mut terms, &mut map, "fvar_1", 1);
    let q = register_bool_var(&mut terms, &mut map, "fvar_2", 2);
    let r = register_bool_var(&mut terms, &mut map, "fvar_3", 3);
    let not_p = terms.mk_not(p);
    let not_r = terms.mk_not(r);
    let clause = vec![not_p, q, not_r];

    let mut ctx = translation_context(&terms, &map);
    let props = translated_props(&mut ctx, &clause);
    let target = disjunction::or_chain_type(&props);
    let items = vec![EmSplitItem { clause_idx: 0 }, EmSplitItem { clause_idx: 2 }];
    let base_depth = Cell::new(None);

    let result =
        ctx.build_em_case_split(&clause, &props, &target, &items, ProofId(0), 0, &|depth| {
            base_depth.set(Some(depth));
            Ok(disjunction::inject_into_or_chain(&props, 1, Expr::bvar(0)))
        });

    let proof_term = result.expect("sparse items em case split should succeed");
    assert_eq!(base_depth.get(), Some(2));
    let head = proof_term.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(_, _)),
        "expected Const head for sparse split, got {:?}",
        head.kind()
    );
    let ExprKind::Const(name, _) = head.kind() else {
        unreachable!("asserted Const head above");
    };
    assert_eq!(name.to_string(), "Or.rec");
}

#[test]
fn test_em_case_split_negative_case_injects_at_clause_idx() {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let p0 = register_bool_var(&mut terms, &mut map, "fvar_0", 10);
    let p1 = register_bool_var(&mut terms, &mut map, "fvar_1", 11);
    let p2 = register_bool_var(&mut terms, &mut map, "fvar_2", 12);
    let not_p1 = terms.mk_not(p1);
    let clause = vec![p0, not_p1, p2];

    let mut ctx = translation_context(&terms, &map);
    let props = translated_props(&mut ctx, &clause);
    let target = disjunction::or_chain_type(&props);
    let items = vec![EmSplitItem { clause_idx: 1 }];

    let result =
        ctx.build_em_case_split(&clause, &props, &target, &items, ProofId(0), 0, &|depth| {
            assert_eq!(depth, 1);
            Ok(disjunction::inject_into_or_chain(&props, 0, Expr::bvar(0)))
        });

    assert!(result.is_ok(), "middle-index em case split should succeed");
}

#[test]
fn test_em_case_split_contains_classical_em_application() {
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
    let em_head = args[5].get_app_fn();
    assert!(
        matches!(em_head.kind(), ExprKind::Const(_, _)),
        "expected Const head for Classical.em application, got {:?}",
        em_head.kind()
    );
    let ExprKind::Const(name, _) = em_head.kind() else {
        unreachable!("asserted Const head above");
    };
    assert_eq!(name.to_string(), "Classical.em");
}
