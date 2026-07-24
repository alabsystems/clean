// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use num_bigint::BigInt;

fn mk_deep_or_chain(terms: &mut TermStore, depth: usize) -> Vec<ay_core::TermId> {
    assert!(depth > 0, "deep-or fixture requires at least one literal");

    let mut leaves = Vec::with_capacity(depth);
    let first = terms.mk_var("fvar_0", Sort::Bool);
    leaves.push(first);

    let mut current = first;
    for idx in 1..depth {
        let next = terms.mk_var(format!("fvar_{idx}"), Sort::Bool);
        leaves.push(next);
        // Use a raw application so the fixture stays deeply nested.
        // `TermStore::mk_or` flattens nested disjunctions eagerly.
        current = terms.mk_app(
            ay_core::Symbol::named("or"),
            vec![current, next],
            Sort::Bool,
        );
    }

    leaves.push(current);
    leaves
}

#[test]
fn test_flatten_or_handles_deep_nested_chain() {
    let depth = 10_000;
    let mut terms = TermStore::new();
    let mut leaves_and_root = mk_deep_or_chain(&mut terms, depth);
    let root = leaves_and_root
        .pop()
        .expect("fixture should append the root term last");
    let expected_leaves = leaves_and_root;
    match terms.get(root) {
        ay_core::TermData::App(ay_core::Symbol::Named(name), args) => {
            assert_eq!(name, "or", "fixture root should stay an Or application");
            assert_eq!(
                args.len(),
                2,
                "fixture must stay binary to exercise recursion"
            );
        }
        other => panic!("expected binary Or fixture root, got {other:?}"),
    }

    let trace = ProofTrace::without_proof(&terms);
    let flattened = trace.flatten_or(root);

    assert_eq!(
        flattened.len(),
        depth,
        "deep Or chain should flatten to exactly {depth} leaves"
    );
    assert_eq!(
        flattened, expected_leaves,
        "flatten_or should preserve left-to-right literal order on deep nesting"
    );
}

#[test]
fn test_translate_term_handles_deep_uninterpreted_chain() {
    // Match other stack-safety stress tests in the repo: this depth is large
    // enough to exercise the guard instead of just documenting shallow behavior.
    let depth = 10_000;
    let mut terms = TermStore::new();
    let atom = terms.mk_var("fvar_1", Sort::Bool);
    let mut nested = atom;
    for _ in 0..depth {
        nested = terms.mk_app(
            ay_core::Symbol::Named("deep_f".to_string()),
            vec![nested],
            Sort::Bool,
        );
    }

    let mut map = VariableMapping::new();
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    map.register_var("fvar_1", Expr::fvar(FVarId::new(1)), bool_ty.clone());
    map.register_var("deep_f", Expr::fvar(FVarId::new(99)), bool_ty);

    let mut ctx = translation_context(&terms, &map);
    let translated = ctx
        .translate_term(nested)
        .expect("deep unary application chain should translate successfully");

    let mut current = &translated;
    for idx in 0..depth {
        let ExprKind::App(func, arg) = current.kind() else {
            panic!("expected unary application at depth {idx}, got {current:?}");
        };
        match func.kind() {
            ExprKind::FVar(id) => assert_eq!(
                id.as_u64(),
                99,
                "expected deep_f to map to FVar(99) at nesting depth {idx}"
            ),
            other => panic!("expected unary function head at depth {idx}, got {other:?}"),
        }
        current = arg;
    }

    match current.kind() {
        ExprKind::FVar(id) => assert_eq!(id.as_u64(), 1, "innermost atom should be fvar_1"),
        other => panic!("expected innermost translated atom to be FVar(1), got {other:?}"),
    }
}

#[test]
fn test_int_add_nf_flatten_handles_deep_addition_chain() {
    use super::super::theory_lemma_lra_additive::mk_int_add;
    use super::super::theory_lemma_lra_sum_nf::IntAddNf;

    let depth = 10_000;
    let atom = Expr::const_(Name::from_string("x"), vec![]);
    let mut chain = atom.clone();
    for _ in 0..depth {
        chain = mk_int_add(&atom, &chain);
    }

    let nf = IntAddNf::from_expr(&chain);

    assert_eq!(
        nf.atoms.len(),
        depth + 1,
        "deep Int.add chain should flatten to exactly {depth}+1 atom leaves"
    );
    assert_eq!(
        nf.constant,
        BigInt::from(0),
        "chain of pure atoms should have zero constant"
    );
    assert!(
        nf.constant_terms.is_empty(),
        "chain of pure atoms should have no constant terms"
    );
}
