// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn trace_has_attached_proof(trace: &ProofTrace<'_>, terms: &TermStore) -> bool {
    use std::mem::size_of;

    assert_eq!(
        size_of::<ProofTrace<'_>>(),
        2 * size_of::<usize>(),
        "ProofTrace layout changed; update this regression helper"
    );
    let words = unsafe {
        // SAFETY: this test-only helper only reads the raw pointer words of
        // `ProofTrace` to distinguish `without_proof(...)` from an attached
        // empty `Proof`. The assertion above constrains the layout to the
        // current two-word representation used by this regression.
        std::slice::from_raw_parts(trace as *const _ as *const usize, 2)
    };
    let terms_ptr = terms as *const TermStore as usize;
    let proof_word = words
        .iter()
        .copied()
        .find(|word| *word != terms_ptr)
        .expect("ProofTrace should contain a proof slot distinct from the term-store pointer");
    proof_word != 0
}

#[test]
fn test_sort_to_lean_type_bool() {
    use clean_kernel::Level;
    // Sort::Bool maps to Prop (Sort 0), not the inductive type Bool (#2269).
    let expr = sort_to_lean_type(&Sort::Bool);
    match expr.kind() {
        ExprKind::Sort(level) => assert_eq!(
            *level,
            Level::Zero,
            "expected Sort(0) for Prop, got Sort({:?})",
            level
        ),
        _ => panic!("expected Sort(0) for Prop, got {:?}", expr),
    }
}

#[test]
fn test_sort_to_lean_type_int() {
    let expr = sort_to_lean_type(&Sort::Int);
    match expr.kind() {
        ExprKind::Const(name, _) => assert_eq!(name.to_string(), "Int"),
        _ => panic!("expected Const(Int), got {:?}", expr),
    }
}

#[test]
fn test_mk_not() {
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let not_p = mk_not(&p);
    match not_p.kind() {
        ExprKind::App(func, arg) => {
            match func.kind() {
                ExprKind::Const(name, _) => assert_eq!(name.to_string(), "Not"),
                _ => panic!("expected Const(Not)"),
            }
            match arg.kind() {
                ExprKind::Const(name, _) => assert_eq!(name.to_string(), "P"),
                _ => panic!("expected Const(P)"),
            }
        }
        _ => panic!("expected App"),
    }
}

#[test]
fn test_mk_eq() {
    let ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let a = Expr::nat_lit(1);
    let b = Expr::nat_lit(2);
    let eq = mk_eq(&ty, &a, &b);
    // Should be App(App(App(Const("Eq", [u]), Nat), 1), 2)
    let args = eq.get_app_args();
    assert_eq!(args.len(), 3, "Eq should have 3 args: type, lhs, rhs");
}

#[test]
fn test_mk_and() {
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    let and = mk_and(&a, &b);
    let head = and.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(name.to_string(), "And"),
        _ => panic!("expected And"),
    }
}

#[test]
fn test_variable_mapping() {
    let mut map = VariableMapping::new();
    let expr = Expr::fvar(FVarId::new(42));
    let ty = Expr::const_(Name::from_string("Nat"), vec![]);
    map.register_var("fvar_42", expr.clone(), ty);
    let (found_expr, _) = map.get_var("fvar_42").unwrap();
    assert_eq!(*found_expr, expr);
}

#[test]
fn test_translate_bool_constants() {
    let terms = TermStore::new();
    let t = terms.true_term();
    let f = terms.false_term();

    let map = VariableMapping::new();
    let mut ctx = translation_context(&terms, &map);

    let true_expr = ctx.translate_term(t).unwrap();
    match true_expr.kind() {
        ExprKind::Const(name, _) => assert_eq!(name.to_string(), "True"),
        _ => panic!("expected True"),
    }

    let false_expr = ctx.translate_term(f).unwrap();
    match false_expr.kind() {
        ExprKind::Const(name, _) => assert_eq!(name.to_string(), "False"),
        _ => panic!("expected False"),
    }
}

#[test]
fn test_new_context_translates_without_attached_proof() {
    let terms = TermStore::new();
    let t = terms.true_term();
    let map = VariableMapping::new();
    let mut ctx = ReconstructionContext::new(&terms, &map, 0);

    let true_expr = ctx
        .translate_term(t)
        .expect("translation-only context should not require a proof handle");
    match true_expr.kind() {
        ExprKind::Const(name, _) => assert_eq!(name.to_string(), "True"),
        other => panic!("expected True constant, got {:?}", other),
    }
}

#[test]
fn test_translation_context_helper_uses_proofless_trace() {
    let terms = TermStore::new();
    let map = VariableMapping::new();
    let ctx = translation_context(&terms, &map);

    assert!(
        !trace_has_attached_proof(ctx.trace(), &terms),
        "translation helper should keep the trace detached from any proof object"
    );
    assert_eq!(
        ctx.trace().step_count(),
        0,
        "translation helper should report zero steps when no proof is attached"
    );
}

#[test]
fn test_empty_proof_can_have_zero_steps_while_still_attached() {
    let terms = TermStore::new();
    let map = VariableMapping::new();
    let proof = Proof::new();
    let ctx = ReconstructionContext::with_proof(&proof, &terms, &map);

    assert!(
        trace_has_attached_proof(ctx.trace(), &terms),
        "empty proof traces should still report an attached proof handle"
    );
    assert_eq!(
        ctx.trace().step_count(),
        0,
        "empty proofs still carry zero steps even when a proof is attached"
    );
}

#[test]
fn test_translate_variable() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("fvar_42", Sort::Bool);

    let mut map = VariableMapping::new();
    let expr = Expr::fvar(FVarId::new(42));
    let ty = Expr::const_(Name::from_string("Bool"), vec![]);
    map.register_var("fvar_42", expr.clone(), ty);

    let mut ctx = translation_context(&terms, &map);
    let result = ctx.translate_term(x).unwrap();
    assert_eq!(result, expr);
}

#[test]
fn test_translate_not() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("fvar_1", Sort::Bool);
    let not_x = terms.mk_not(x);

    let mut map = VariableMapping::new();
    let expr = Expr::fvar(FVarId::new(1));
    let ty = Expr::const_(Name::from_string("Bool"), vec![]);
    map.register_var("fvar_1", expr, ty);

    let mut ctx = translation_context(&terms, &map);
    let result = ctx.translate_term(not_x).unwrap();
    let head = result.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(name.to_string(), "Not"),
        _ => panic!("expected Not, got {:?}", head),
    }
}

#[test]
fn test_translate_equality() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("fvar_1", Sort::Int);
    let b = terms.mk_var("fvar_2", Sort::Int);
    let eq = terms.mk_eq(a, b);

    let mut map = VariableMapping::new();
    let a_expr = Expr::fvar(FVarId::new(1));
    let b_expr = Expr::fvar(FVarId::new(2));
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    map.register_var("fvar_1", a_expr, int_ty.clone());
    map.register_var("fvar_2", b_expr, int_ty);

    let mut ctx = translation_context(&terms, &map);
    let result = ctx
        .translate_term(eq)
        .expect("equality translation should succeed");
    // Verify the result is @Eq.{u} Int fvar_1 fvar_2, not just "some Ok value"
    let head = result.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, levels) => {
            assert_eq!(name.to_string(), "Eq", "head should be Eq constant");
            assert_eq!(levels.len(), 1, "Eq should have exactly 1 universe level");
            // Int : Type 0 = Sort 1, so u = succ(0) = 1
            assert_eq!(
                levels[0],
                Level::succ(Level::zero()),
                "Eq universe for Int should be 1"
            );
        }
        _ => panic!("expected Const(Eq, [1]), got {:?}", head),
    }
    let args = result.get_app_args();
    assert_eq!(args.len(), 3, "Eq should have 3 args: type, lhs, rhs");
    // arg[0] = Int type
    match args[0].kind() {
        ExprKind::Const(name, _) => assert_eq!(name.to_string(), "Int"),
        _ => panic!("expected Int as Eq type arg, got {:?}", args[0]),
    }
    // arg[1] = fvar_1
    match args[1].kind() {
        ExprKind::FVar(id) => assert_eq!(id.as_u64(), 1, "lhs should be fvar_1"),
        _ => panic!("expected FVar(1) as lhs, got {:?}", args[1]),
    }
    // arg[2] = fvar_2
    match args[2].kind() {
        ExprKind::FVar(id) => assert_eq!(id.as_u64(), 2, "rhs should be fvar_2"),
        _ => panic!("expected FVar(2) as rhs, got {:?}", args[2]),
    }
}

#[test]
fn test_translate_and() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("fvar_1", Sort::Bool);
    let b = terms.mk_var("fvar_2", Sort::Bool);
    let and = terms.mk_and(vec![a, b]);

    let mut map = VariableMapping::new();
    map.register_var(
        "fvar_1",
        Expr::fvar(FVarId::new(1)),
        Expr::const_(Name::from_string("Bool"), vec![]),
    );
    map.register_var(
        "fvar_2",
        Expr::fvar(FVarId::new(2)),
        Expr::const_(Name::from_string("Bool"), vec![]),
    );

    let mut ctx = translation_context(&terms, &map);
    let result = ctx.translate_term(and).unwrap();
    let head = result.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => assert_eq!(name.to_string(), "And"),
        _ => panic!("expected And, got {:?}", head),
    }
}

#[test]
fn test_empty_proof_reconstruction() {
    let terms = TermStore::new();
    let map = VariableMapping::new();
    let goal = Expr::const_(Name::from_string("False"), vec![]);

    let result = attempt_reconstruction(&Proof::new(), &terms, &map, &goal);
    assert!(
        result.proof_term.is_none(),
        "empty proof should produce no proof term"
    );
    let diagnostic = result
        .stats
        .first_diagnostic
        .as_ref()
        .expect("empty proof should report a diagnostic");
    assert_eq!(
        diagnostic.error,
        ReconstructionError::EmptyProof,
        "expected EmptyProof diagnostic, got {:?}",
        diagnostic.error
    );
}

#[test]
fn test_reconstruction_stats() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);

    let mut proof = Proof::new();
    let h1 = proof.add_assume(x, None);
    let h2 = proof.add_assume(not_x, None);
    proof.add_resolution(vec![], x, h1, h2);

    let map = VariableMapping::new();
    let goal = Expr::const_(Name::from_string("False"), vec![]);

    let result = attempt_reconstruction(&proof, &terms, &map, &goal);
    assert_eq!(result.stats.total_steps, 3);
    assert_eq!(result.stats.assume_steps, 2);
    assert_eq!(result.stats.resolution_steps, 1);
}
