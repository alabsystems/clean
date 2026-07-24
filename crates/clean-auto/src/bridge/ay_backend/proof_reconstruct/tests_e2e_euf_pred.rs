// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Focused e2e coverage for congruent-predicate reconstruction cases that need
//! multiple iterations through `build_pred_congr_chain`.

use super::super::{attempt_reconstruction, VariableMapping};
use super::{assert_proof_type_checks_to_false, mk_eq_int};
use ay::Sort;
use ay_core::{Proof, TermStore};
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Declaration, Environment, Expr, FVarId, Level, LocalContext};

struct ThreeArgCongruentPredInput<'a> {
    eq_a1b1: &'a Expr,
    eq_a2b2: &'a Expr,
    eq_a3b3: &'a Expr,
    p_a: &'a Expr,
    p_const: &'a Expr,
}

fn mk_euf_congruent_pred_three_arg_ay_proof(
    h_ids: [FVarId; 4],
    input: ThreeArgCongruentPredInput<'_>,
) -> (TermStore, VariableMapping, Proof) {
    use ay_core::TheoryLemmaKind;

    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();
    let [h1_id, h2_id, h3_id, h_pa_id] = h_ids;
    let ThreeArgCongruentPredInput {
        eq_a1b1,
        eq_a2b2,
        eq_a3b3,
        p_a,
        p_const,
    } = input;

    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let ay_a1 = terms.mk_var("fvar_1", Sort::Int);
    let ay_b1 = terms.mk_var("fvar_2", Sort::Int);
    let ay_a2 = terms.mk_var("fvar_3", Sort::Int);
    let ay_b2 = terms.mk_var("fvar_4", Sort::Int);
    let ay_a3 = terms.mk_var("fvar_5", Sort::Int);
    let ay_b3 = terms.mk_var("fvar_6", Sort::Int);

    for (name, expr_name) in [
        ("fvar_1", "testA1"),
        ("fvar_2", "testB1"),
        ("fvar_3", "testA2"),
        ("fvar_4", "testB2"),
        ("fvar_5", "testA3"),
        ("fvar_6", "testB3"),
    ] {
        map.register_var(
            name,
            Expr::const_(Name::from_string(expr_name), vec![]),
            int_ty.clone(),
        );
    }

    let pred_name = "fvar_10";
    let p_a_ay = terms.mk_app(
        ay_core::Symbol::Named(pred_name.to_string()),
        vec![ay_a1, ay_a2, ay_a3],
        Sort::Bool,
    );
    let p_b_ay = terms.mk_app(
        ay_core::Symbol::Named(pred_name.to_string()),
        vec![ay_b1, ay_b2, ay_b3],
        Sort::Bool,
    );
    let pred_ty = Expr::pi(
        BinderInfo::Default,
        int_ty.clone(),
        Expr::pi(
            BinderInfo::Default,
            int_ty.clone(),
            Expr::pi(BinderInfo::Default, int_ty, Expr::sort(Level::zero())),
        ),
    );
    map.register_var(pred_name, p_const.clone(), pred_ty);

    let ay_eq_a1b1 = terms.mk_eq(ay_a1, ay_b1);
    let ay_eq_a2b2 = terms.mk_eq(ay_a2, ay_b2);
    let ay_eq_a3b3 = terms.mk_eq(ay_a3, ay_b3);
    let ay_not_a1b1 = terms.mk_not(ay_eq_a1b1);
    let ay_not_a2b2 = terms.mk_not(ay_eq_a2b2);
    let ay_not_a3b3 = terms.mk_not(ay_eq_a3b3);
    let ay_not_p_a = terms.mk_not(p_a_ay);

    map.register_hypothesis("h1", h1_id, Expr::fvar(h1_id), eq_a1b1.clone());
    map.register_hypothesis("h2", h2_id, Expr::fvar(h2_id), eq_a2b2.clone());
    map.register_hypothesis("h3", h3_id, Expr::fvar(h3_id), eq_a3b3.clone());
    map.register_hypothesis("h_pa", h_pa_id, Expr::fvar(h_pa_id), p_a.clone());

    let mut proof = Proof::new();
    let s0 = proof.add_theory_lemma_with_kind(
        "EUF",
        vec![ay_not_a1b1, ay_not_a2b2, ay_not_a3b3, ay_not_p_a, p_b_ay],
        TheoryLemmaKind::EufCongruentPred,
    );
    let s1 = proof.add_assume(ay_eq_a1b1, None);
    let s2 = proof.add_resolution(
        vec![ay_not_a2b2, ay_not_a3b3, ay_not_p_a, p_b_ay],
        ay_not_a1b1,
        s0,
        s1,
    );
    let s3 = proof.add_assume(ay_eq_a2b2, None);
    let s4 = proof.add_resolution(vec![ay_not_a3b3, ay_not_p_a, p_b_ay], ay_not_a2b2, s2, s3);
    let s5 = proof.add_assume(ay_eq_a3b3, None);
    let s6 = proof.add_resolution(vec![ay_not_p_a, p_b_ay], ay_not_a3b3, s4, s5);
    let s7 = proof.add_assume(p_a_ay, None);
    let s8 = proof.add_resolution(vec![p_b_ay], ay_not_p_a, s6, s7);
    let ay_not_p_b = terms.mk_not(p_b_ay);
    let s9 = proof.add_assume(ay_not_p_b, None);
    proof.add_resolution(vec![], p_b_ay, s8, s9);

    (terms, map, proof)
}

fn mk_three_arg_congruent_pred_fixture() -> (Environment, Expr, Expr, Expr, Expr, Expr, Expr) {
    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    env.init_nat().expect("init_nat");
    env.init_int().expect("init_int");
    env.init_true_false().expect("init_true_false");
    env.init_classical().expect("init_classical");

    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    for name in ["testA1", "testB1", "testA2", "testB2", "testA3", "testB3"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: int_ty.clone(),
        })
        .unwrap_or_else(|e| panic!("add {name}: {e:?}"));
    }

    let p_ty = Expr::pi(
        BinderInfo::Default,
        int_ty.clone(),
        Expr::pi(
            BinderInfo::Default,
            int_ty.clone(),
            Expr::pi(
                BinderInfo::Default,
                int_ty.clone(),
                Expr::sort(Level::zero()),
            ),
        ),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("testP"),
        level_params: vec![],
        type_: p_ty,
    })
    .expect("add testP");

    let eq_a1b1 = mk_eq_int("testA1", "testB1");
    let eq_a2b2 = mk_eq_int("testA2", "testB2");
    let eq_a3b3 = mk_eq_int("testA3", "testB3");
    let p_const = Expr::const_(Name::from_string("testP"), vec![]);
    let p_a = Expr::app(
        Expr::app(
            Expr::app(
                p_const.clone(),
                Expr::const_(Name::from_string("testA1"), vec![]),
            ),
            Expr::const_(Name::from_string("testA2"), vec![]),
        ),
        Expr::const_(Name::from_string("testA3"), vec![]),
    );
    let p_b = Expr::app(
        Expr::app(
            Expr::app(
                p_const.clone(),
                Expr::const_(Name::from_string("testB1"), vec![]),
            ),
            Expr::const_(Name::from_string("testB2"), vec![]),
        ),
        Expr::const_(Name::from_string("testB3"), vec![]),
    );
    let not_p_b = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), p_b);

    (env, eq_a1b1, eq_a2b2, eq_a3b3, p_const, p_a, not_p_b)
}

/// E2E: EUF 3-arg congruent-pred + resolution chain -> kernel type-checks to False.
///
/// Exercises two iterations of `build_pred_congr_chain`'s running accumulator:
/// `congr (congr (congrArg testP h1) h2) h3`, then `Eq.mpr` transports `P(a...)`
/// to `P(b...)`.
///
/// Part of #2545.
#[test]
fn test_e2e_euf_congruent_pred_three_arg_type_checks() {
    let (env, eq_a1b1, eq_a2b2, eq_a3b3, p_const, p_a, not_p_b) =
        mk_three_arg_congruent_pred_fixture();
    let h1_id = FVarId::new(10);
    let h2_id = FVarId::new(11);
    let h3_id = FVarId::new(12);
    let h_pa_id = FVarId::new(13);

    let (terms, map, proof) = mk_euf_congruent_pred_three_arg_ay_proof(
        [h1_id, h2_id, h3_id, h_pa_id],
        ThreeArgCongruentPredInput {
            eq_a1b1: &eq_a1b1,
            eq_a2b2: &eq_a2b2,
            eq_a3b3: &eq_a3b3,
            p_a: &p_a,
            p_const: &p_const,
        },
    );

    let mut ctx = LocalContext::new();
    ctx.push_with_id(h1_id, Name::from_string("h1"), eq_a1b1, BinderInfo::Default);
    ctx.push_with_id(h2_id, Name::from_string("h2"), eq_a2b2, BinderInfo::Default);
    ctx.push_with_id(h3_id, Name::from_string("h3"), eq_a3b3, BinderInfo::Default);
    ctx.push_with_id(h_pa_id, Name::from_string("h_pa"), p_a, BinderInfo::Default);

    let result = attempt_reconstruction(&proof, &terms, &map, &not_p_b);
    assert!(
        result.stats.reconstructed_steps >= 11,
        "all 11 steps should reconstruct, got {} (error: {:?})",
        result.stats.reconstructed_steps,
        result.stats.error,
    );
    let mut proof_term = result
        .proof_term
        .expect("3-arg congruent-pred + resolution should produce a proof term");

    if let Some(sentinel_id) = result.negated_goal_fvar {
        let neg_id = FVarId::new(20);
        proof_term = proof_term.subst_fvar(sentinel_id, &Expr::fvar(neg_id));
        ctx.push_with_id(
            neg_id,
            Name::from_string("h_neg_goal"),
            not_p_b.clone(),
            BinderInfo::Default,
        );
    }

    assert_proof_type_checks_to_false(&env, ctx, &proof_term, "EUF 3-arg congruent-pred e2e");
}
