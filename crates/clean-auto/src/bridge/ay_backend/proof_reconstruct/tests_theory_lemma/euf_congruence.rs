// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::support::semantic::register_int_var;
use super::{
    attempt_reconstruction, Expr, ExprKind, FVarId, Name, Proof, Sort, TermStore, TheoryLemmaKind,
    VariableMapping,
};

#[test]
fn test_theory_lemma_euf_congruent_single_arg() {
    // EUF congruent: {¬(a=b), f(a)=f(b)}
    // Should produce congrArg f h
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let a = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let b = register_int_var(&mut terms, &mut map, "fvar_2", 2);

    // Register f as a unary function
    let f_name = "fvar_10";
    let f_a = terms.mk_app(
        ay_core::Symbol::Named(f_name.to_string()),
        vec![a],
        Sort::Int,
    );
    let f_b = terms.mk_app(
        ay_core::Symbol::Named(f_name.to_string()),
        vec![b],
        Sort::Int,
    );
    let f_expr = Expr::fvar(FVarId::new(10));
    let int_to_int = Expr::pi(
        clean_kernel::BinderInfo::Default,
        Expr::const_(Name::from_string("Int"), vec![]),
        Expr::const_(Name::from_string("Int"), vec![]),
    );
    map.register_var(f_name, f_expr, int_to_int);

    let eq_ab = terms.mk_eq(a, b);
    let eq_fafb = terms.mk_eq(f_a, f_b);
    let not_eq_ab = terms.mk_not(eq_ab);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind(
        "EUF",
        vec![not_eq_ab, eq_fafb],
        TheoryLemmaKind::EufCongruent,
    );

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.theory_lemma_steps, 1);
    assert_eq!(
        result.stats.reconstructed_steps, 1,
        "EUF congruent should be reconstructed, error: {:?}",
        result.stats.error,
    );
    let _ = result
        .proof_term
        .expect("EUF congruent should produce a proof term");
}

#[test]
fn test_theory_lemma_euf_congruent_two_args() {
    // EUF congruent with 2 args: {¬(a₁=b₁), ¬(a₂=b₂), f(a₁,a₂)=f(b₁,b₂)}
    // Should produce congr (congrArg f h₁) h₂
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let a1 = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let b1 = register_int_var(&mut terms, &mut map, "fvar_2", 2);
    let a2 = register_int_var(&mut terms, &mut map, "fvar_3", 3);
    let b2 = register_int_var(&mut terms, &mut map, "fvar_4", 4);

    // Register f as a binary function
    let f_name = "fvar_10";
    let f_a1a2 = terms.mk_app(
        ay_core::Symbol::Named(f_name.to_string()),
        vec![a1, a2],
        Sort::Int,
    );
    let f_b1b2 = terms.mk_app(
        ay_core::Symbol::Named(f_name.to_string()),
        vec![b1, b2],
        Sort::Int,
    );
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let f_ty = Expr::pi(
        clean_kernel::BinderInfo::Default,
        int_ty.clone(),
        Expr::pi(clean_kernel::BinderInfo::Default, int_ty.clone(), int_ty),
    );
    map.register_var(f_name, Expr::fvar(FVarId::new(10)), f_ty);

    let eq_a1b1 = terms.mk_eq(a1, b1);
    let eq_a2b2 = terms.mk_eq(a2, b2);
    let eq_fafb = terms.mk_eq(f_a1a2, f_b1b2);
    let not_a1b1 = terms.mk_not(eq_a1b1);
    let not_a2b2 = terms.mk_not(eq_a2b2);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind(
        "EUF",
        vec![not_a1b1, not_a2b2, eq_fafb],
        TheoryLemmaKind::EufCongruent,
    );

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.theory_lemma_steps, 1);
    assert_eq!(
        result.stats.reconstructed_steps, 1,
        "2-arg EUF congruent should be reconstructed, error: {:?}",
        result.stats.error,
    );
    let _ = result
        .proof_term
        .expect("2-arg EUF congruent should produce a proof term");
}

#[test]
fn test_theory_lemma_euf_congruent_three_args() {
    // EUF congruent with 3 args: {¬(a₁=b₁), ¬(a₂=b₂), ¬(a₃=b₃), f(a₁,a₂,a₃)=f(b₁,b₂,b₃)}
    // Should produce congr (congr (congrArg f h₁) h₂) h₃
    // This exercises the full multi-arg loop (for k in 1..n) with n=3.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let a1 = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let b1 = register_int_var(&mut terms, &mut map, "fvar_2", 2);
    let a2 = register_int_var(&mut terms, &mut map, "fvar_3", 3);
    let b2 = register_int_var(&mut terms, &mut map, "fvar_4", 4);
    let a3 = register_int_var(&mut terms, &mut map, "fvar_5", 5);
    let b3 = register_int_var(&mut terms, &mut map, "fvar_6", 6);

    // Register f as a ternary function: Int → Int → Int → Int
    let f_name = "fvar_10";
    let f_a = terms.mk_app(
        ay_core::Symbol::Named(f_name.to_string()),
        vec![a1, a2, a3],
        Sort::Int,
    );
    let f_b = terms.mk_app(
        ay_core::Symbol::Named(f_name.to_string()),
        vec![b1, b2, b3],
        Sort::Int,
    );
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let f_ty = Expr::pi(
        clean_kernel::BinderInfo::Default,
        int_ty.clone(),
        Expr::pi(
            clean_kernel::BinderInfo::Default,
            int_ty.clone(),
            Expr::pi(clean_kernel::BinderInfo::Default, int_ty.clone(), int_ty),
        ),
    );
    map.register_var(f_name, Expr::fvar(FVarId::new(10)), f_ty);

    let eq_a1b1 = terms.mk_eq(a1, b1);
    let eq_a2b2 = terms.mk_eq(a2, b2);
    let eq_a3b3 = terms.mk_eq(a3, b3);
    let eq_fafb = terms.mk_eq(f_a, f_b);
    let not_a1b1 = terms.mk_not(eq_a1b1);
    let not_a2b2 = terms.mk_not(eq_a2b2);
    let not_a3b3 = terms.mk_not(eq_a3b3);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind(
        "EUF",
        vec![not_a1b1, not_a2b2, not_a3b3, eq_fafb],
        TheoryLemmaKind::EufCongruent,
    );

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.theory_lemma_steps, 1);
    assert_eq!(
        result.stats.reconstructed_steps, 1,
        "3-arg EUF congruent should be reconstructed, error: {:?}",
        result.stats.error,
    );
    let _ = result
        .proof_term
        .expect("3-arg EUF congruent should produce a proof term");
}

#[test]
fn test_theory_lemma_euf_congruent_pred_single_arg() {
    // EUF congruent-pred: {¬(a=b), ¬(P(a)), P(b)}
    // Should produce Classical.em chain + congrArg P + Eq.mpr
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let a = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let b = register_int_var(&mut terms, &mut map, "fvar_2", 2);

    // Register P as a predicate (Int → Bool)
    let p_name = "fvar_10";
    let p_a = terms.mk_app(
        ay_core::Symbol::Named(p_name.to_string()),
        vec![a],
        Sort::Bool,
    );
    let p_b = terms.mk_app(
        ay_core::Symbol::Named(p_name.to_string()),
        vec![b],
        Sort::Bool,
    );
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let prop_ty = Expr::sort(clean_kernel::Level::zero());
    let p_ty = Expr::pi(clean_kernel::BinderInfo::Default, int_ty, prop_ty);
    map.register_var(p_name, Expr::fvar(FVarId::new(10)), p_ty);

    let eq_ab = terms.mk_eq(a, b);
    let not_eq_ab = terms.mk_not(eq_ab);
    let not_p_a = terms.mk_not(p_a);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind(
        "EUF",
        vec![not_eq_ab, not_p_a, p_b],
        TheoryLemmaKind::EufCongruentPred,
    );

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.theory_lemma_steps, 1);
    assert_eq!(
        result.stats.reconstructed_steps, 1,
        "EUF congruent-pred should be reconstructed, error: {:?}",
        result.stats.error,
    );
    let proof_term = result
        .proof_term
        .expect("EUF congruent-pred should produce a proof term");
    // Top-level should be Or.rec (from first Classical.em)
    let head = proof_term.get_app_fn();
    let actual_name = match head.kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        _ => None,
    };
    assert_eq!(
        actual_name.as_deref(),
        Some("Or.rec"),
        "EUF congruent-pred should use Or.rec; got {:?}",
        head
    );
}

#[test]
fn test_theory_lemma_euf_congruent_pred_two_args() {
    // EUF congruent-pred with 2 args: {¬(a₁=b₁), ¬(a₂=b₂), ¬(P(a₁,a₂)), P(b₁,b₂)}
    // Should produce Classical.em chain + congr (congrArg P h₁) h₂ + Eq.mpr
    // This exercises the multi-arg pred congr chain with BVar depth = n_eqs + 1 = 3.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let a1 = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let b1 = register_int_var(&mut terms, &mut map, "fvar_2", 2);
    let a2 = register_int_var(&mut terms, &mut map, "fvar_3", 3);
    let b2 = register_int_var(&mut terms, &mut map, "fvar_4", 4);

    // Register P as a binary predicate: Int → Int → Prop
    let p_name = "fvar_10";
    let p_a = terms.mk_app(
        ay_core::Symbol::Named(p_name.to_string()),
        vec![a1, a2],
        Sort::Bool,
    );
    let p_b = terms.mk_app(
        ay_core::Symbol::Named(p_name.to_string()),
        vec![b1, b2],
        Sort::Bool,
    );
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let prop_ty = Expr::sort(clean_kernel::Level::zero());
    let p_ty = Expr::pi(
        clean_kernel::BinderInfo::Default,
        int_ty.clone(),
        Expr::pi(clean_kernel::BinderInfo::Default, int_ty, prop_ty),
    );
    map.register_var(p_name, Expr::fvar(FVarId::new(10)), p_ty);

    let eq_a1b1 = terms.mk_eq(a1, b1);
    let eq_a2b2 = terms.mk_eq(a2, b2);
    let not_a1b1 = terms.mk_not(eq_a1b1);
    let not_a2b2 = terms.mk_not(eq_a2b2);
    let not_p_a = terms.mk_not(p_a);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind(
        "EUF",
        vec![not_a1b1, not_a2b2, not_p_a, p_b],
        TheoryLemmaKind::EufCongruentPred,
    );

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.theory_lemma_steps, 1);
    assert_eq!(
        result.stats.reconstructed_steps, 1,
        "2-arg EUF congruent-pred should be reconstructed, error: {:?}",
        result.stats.error,
    );
    let proof_term = result
        .proof_term
        .expect("2-arg EUF congruent-pred should produce a proof term");
    // Top-level should be Or.rec (from first Classical.em)
    let head = proof_term.get_app_fn();
    let actual_name = match head.kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        _ => None,
    };
    assert_eq!(
        actual_name.as_deref(),
        Some("Or.rec"),
        "2-arg EUF congruent-pred should use Or.rec; got {:?}",
        head
    );
}
