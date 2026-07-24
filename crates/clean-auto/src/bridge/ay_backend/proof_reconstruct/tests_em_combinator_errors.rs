// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_em_case_split_non_negated_literal_returns_error() {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let p = register_bool_var(&mut terms, &mut map, "fvar_1", 1);
    let q = register_bool_var(&mut terms, &mut map, "fvar_2", 2);
    let clause = vec![p, q];

    let mut ctx = translation_context(&terms, &map);
    let props = translated_props(&mut ctx, &clause);
    let target = disjunction::or_chain_type(&props);
    let items = vec![EmSplitItem { clause_idx: 0 }];

    let result = ctx.build_em_case_split(
        &clause,
        &props,
        &target,
        &items,
        ProofId(42),
        0,
        &|_depth| Ok(Expr::const_(Name::from_string("unreachable"), vec![])),
    );

    match result {
        Err(ReconstructionError::UnsupportedStep {
            step_index,
            description,
        }) => {
            assert_eq!(step_index, 42);
            assert!(description.contains("negated"));
        }
        other => panic!(
            "expected UnsupportedStep for non-negated literal, got {:?}",
            other
        ),
    }
}

#[test]
fn test_em_case_split_cache_miss_returns_error() {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let p = register_bool_var(&mut terms, &mut map, "fvar_1", 1);
    let not_p = terms.mk_not(p);
    let clause = vec![not_p];

    let ctx = translation_context(&terms, &map);
    let props = vec![Expr::const_(Name::from_string("not_p_placeholder"), vec![])];
    let target = props[0].clone();
    let items = vec![EmSplitItem { clause_idx: 0 }];

    let result = ctx.build_em_case_split(
        &clause,
        &props,
        &target,
        &items,
        ProofId(99),
        0,
        &|_depth| Ok(Expr::const_(Name::from_string("unreachable"), vec![])),
    );

    match result {
        Err(ReconstructionError::UnsupportedStep {
            step_index,
            description,
        }) => {
            assert_eq!(step_index, 99);
            assert!(description.contains("not in cache"));
        }
        other => panic!("expected UnsupportedStep for cache miss, got {:?}", other),
    }
}

#[test]
fn test_em_case_split_base_case_error_propagates() {
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
            Err(ReconstructionError::UnsupportedStep {
                step_index: 77,
                description: "base case intentional error".to_string(),
            })
        });

    match result {
        Err(ReconstructionError::UnsupportedStep {
            step_index,
            description,
        }) => {
            assert_eq!(step_index, 77);
            assert!(description.contains("intentional"));
        }
        other => panic!("expected base case error to propagate, got {:?}", other),
    }
}
