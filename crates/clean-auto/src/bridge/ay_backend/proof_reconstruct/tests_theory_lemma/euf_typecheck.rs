// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level type checking tests for EUF theory lemma reconstructed proofs.
//!
//! These tests verify that proof terms produced by the EUF transitivity and
//! EUF congruent reconstructors actually type-check in the kernel via
//! `TypeChecker::infer_type`, proving the proof terms are kernel-sound.

use super::support::semantic::register_int_var;
use super::{
    attempt_reconstruction, Expr, FVarId, Name, Proof, TermStore, TheoryLemmaKind, VariableMapping,
};

fn mk_euf_kernel_env() -> clean_kernel::Environment {
    use clean_kernel::Environment;

    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    env.init_true_false().expect("init_true_false");
    env.init_classical().expect("init_classical");
    env.init_int().expect("init_int");
    env
}

fn assert_proof_type_checks_as_prop(
    env: &clean_kernel::Environment,
    proof_term: &Expr,
    fvar_ids: &[(FVarId, &str)],
    msg: &str,
) {
    use clean_kernel::{BinderInfo, LocalContext, TypeChecker};

    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let mut ctx = LocalContext::new();
    for &(id, name) in fvar_ids {
        ctx.push_with_id(
            id,
            Name::from_string(name),
            int_ty.clone(),
            BinderInfo::Default,
        );
    }

    let tc = TypeChecker::with_context(env, ctx);
    let inferred_type = tc
        .infer_type(proof_term)
        .expect("proof term should type-check in the kernel");

    // The proof should inhabit a Prop (Sort 0). The inferred type of a proof
    // term is its proposition; verify the proposition itself lives in Prop.
    let type_of_type = tc
        .infer_type(&inferred_type)
        .expect("inferred type should be well-typed");
    let prop = Expr::prop();
    assert!(
        tc.is_def_eq(&type_of_type, &prop),
        "{msg}: proof type should be a Prop, but its type is {:?}",
        type_of_type,
    );
}

/// Trivial EUF transitivity: `{¬(a=b), a=b}` — proof is `Classical.em (a=b)`.
#[test]
fn test_euf_transitivity_trivial_type_checks_in_kernel() {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let a = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let b = register_int_var(&mut terms, &mut map, "fvar_2", 2);

    let eq_ab = terms.mk_eq(a, b);
    let not_eq_ab = terms.mk_not(eq_ab);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind(
        "EUF",
        vec![not_eq_ab, eq_ab],
        TheoryLemmaKind::EufTransitive,
    );

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.reconstructed_steps, 1);
    assert_eq!(result.stats.trust_fallback_steps, 0);
    let proof_term = result
        .proof_term
        .expect("EUF transitivity should produce proof");

    let env = mk_euf_kernel_env();
    assert_proof_type_checks_as_prop(
        &env,
        &proof_term,
        &[(FVarId::new(1), "a"), (FVarId::new(2), "b")],
        "trivial EUF transitivity",
    );
}

/// 3-step EUF transitivity: `{¬(a=b), ¬(b=c), a=c}` — proof uses Eq.trans chain.
#[test]
fn test_euf_transitivity_three_step_type_checks_in_kernel() {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let a = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let b = register_int_var(&mut terms, &mut map, "fvar_2", 2);
    let c = register_int_var(&mut terms, &mut map, "fvar_3", 3);

    let eq_ab = terms.mk_eq(a, b);
    let eq_bc = terms.mk_eq(b, c);
    let eq_ac = terms.mk_eq(a, c);
    let not_eq_ab = terms.mk_not(eq_ab);
    let not_eq_bc = terms.mk_not(eq_bc);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind(
        "EUF",
        vec![not_eq_ab, not_eq_bc, eq_ac],
        TheoryLemmaKind::EufTransitive,
    );

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.reconstructed_steps, 1);
    assert_eq!(result.stats.trust_fallback_steps, 0);
    let proof_term = result
        .proof_term
        .expect("3-step EUF transitivity should produce proof");

    let env = mk_euf_kernel_env();
    assert_proof_type_checks_as_prop(
        &env,
        &proof_term,
        &[
            (FVarId::new(1), "a"),
            (FVarId::new(2), "b"),
            (FVarId::new(3), "c"),
        ],
        "3-step EUF transitivity",
    );
}

/// EUF transitivity with Eq.symm: `{¬(b=a), ¬(b=c), a=c}` — needs symmetry.
#[test]
fn test_euf_transitivity_with_symm_type_checks_in_kernel() {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let a = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let b = register_int_var(&mut terms, &mut map, "fvar_2", 2);
    let c = register_int_var(&mut terms, &mut map, "fvar_3", 3);

    let eq_ba = terms.mk_eq(b, a); // reversed — needs Eq.symm
    let eq_bc = terms.mk_eq(b, c);
    let eq_ac = terms.mk_eq(a, c);
    let not_eq_ba = terms.mk_not(eq_ba);
    let not_eq_bc = terms.mk_not(eq_bc);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind(
        "EUF",
        vec![not_eq_ba, not_eq_bc, eq_ac],
        TheoryLemmaKind::EufTransitive,
    );

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.reconstructed_steps, 1);
    assert_eq!(result.stats.trust_fallback_steps, 0);
    let proof_term = result
        .proof_term
        .expect("EUF transitivity with symm should produce proof");

    let env = mk_euf_kernel_env();
    assert_proof_type_checks_as_prop(
        &env,
        &proof_term,
        &[
            (FVarId::new(1), "a"),
            (FVarId::new(2), "b"),
            (FVarId::new(3), "c"),
        ],
        "EUF transitivity with Eq.symm",
    );
}
