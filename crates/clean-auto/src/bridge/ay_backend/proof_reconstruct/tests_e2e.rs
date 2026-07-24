// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end tests: ay proof reconstruction either produces proofs
//! that type-check through the kernel via TypeChecker or stops at a
//! typed trust boundary without fabricating a proof term.
//!
//! These tests build ay proofs (manually), call attempt_reconstruction(),
//! and verify the resulting proof term has type `False` when type-checked
//! with a local context containing the input hypotheses.
//!
//! LRA-specific tests are in the `tests_e2e_lra` module.
//!
//! Follows the pattern from superposition_reconstruction/tests_e2e.rs.
//! Part of #2412.

use super::{attempt_reconstruction, VariableMapping};
use crate::bridge::ay_backend::{AyLogic, AyProofBackend, AyProofResult};
use ay::Sort;
use ay_core::{Proof, TermStore};
use clean_kernel::name::Name;
use clean_kernel::{
    BinderInfo, Declaration, Environment, Expr, ExprKind, FVarId, Level, LocalContext, TypeChecker,
};

#[path = "tests_e2e_euf_pred.rs"]
mod tests_e2e_euf_pred;
#[path = "tests_e2e_euf_transitivity.rs"]
mod tests_e2e_euf_transitivity;

/// Create an environment with Eq, Nat, Not/absurd/False, and two test axioms.
fn mk_env() -> Environment {
    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    env.init_nat().expect("init_nat");
    env.init_true_false().expect("init_true_false");

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("testA"),
        level_params: vec![],
        type_: nat_ty.clone(),
    })
    .expect("add testA");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("testB"),
        level_params: vec![],
        type_: nat_ty,
    })
    .expect("add testB");
    env
}

/// Create an environment with Or, Classical.em, Eq, Int, absurd, and three test axioms.
fn mk_env_with_classical() -> Environment {
    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    env.init_nat().expect("init_nat");
    env.init_int().expect("init_int");
    env.init_true_false().expect("init_true_false");
    env.init_classical().expect("init_classical");

    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    for name in ["testA", "testB", "testC"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: int_ty.clone(),
        })
        .unwrap_or_else(|e| panic!("add {name}: {e:?}"));
    }
    env
}

/// Build `@Eq.{1} Int x y` for named Int axioms.
pub(super) fn mk_eq_int(x: &str, y: &str) -> Expr {
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let x_expr = Expr::const_(Name::from_string(x), vec![]);
    let y_expr = Expr::const_(Name::from_string(y), vec![]);
    let u1 = Level::succ(Level::zero());
    Expr::app(
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Eq"), vec![u1]), int_ty),
            x_expr,
        ),
        y_expr,
    )
}

/// Build `@Eq.{1} Nat testA testB` — the proposition that testA = testB.
fn mk_eq_prop() -> Expr {
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let a = Expr::const_(Name::from_string("testA"), vec![]);
    let b = Expr::const_(Name::from_string("testB"), vec![]);
    let u1 = Level::succ(Level::zero());
    Expr::app(
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Eq"), vec![u1]), nat_ty),
            a,
        ),
        b,
    )
}

/// Build `Not (Eq Nat testA testB)` — the proposition that testA ≠ testB.
fn mk_neq_prop() -> Expr {
    Expr::app(Expr::const_(Name::from_string("Not"), vec![]), mk_eq_prop())
}

/// Assert that a proof term type-checks to False in the given context.
pub(super) fn assert_proof_type_checks_to_false(
    env: &Environment,
    ctx: LocalContext,
    proof: &Expr,
    msg: &str,
) {
    let tc = TypeChecker::with_context(env, ctx);
    let ty = tc
        .infer_type(proof)
        .unwrap_or_else(|e| panic!("{msg}: type-check failed: {e:?}"));
    assert!(
        matches!(ty.kind(), ExprKind::Const(n, _) if *n == Name::from_string("False")),
        "{msg}: expected type False, got {:?}",
        ty.kind(),
    );
}

/// E2E: Resolution unit contradiction → kernel type-checks to False.
///
/// Setup: h_eq : (testA = testB), negated goal ¬(testA = testB).
/// ay proof: Assume(p), Assume(¬p), Resolution([], p, h1, h2) → empty clause.
/// The reconstruction should produce `@absurd (Eq Nat testA testB) False h_eq h_neg`
/// which type-checks to False when h_eq and h_neg have the right types.
#[test]
fn test_e2e_resolution_unit_contradiction_type_checks() {
    let env = mk_env();
    let eq_prop = mk_eq_prop();
    let neq_prop = mk_neq_prop();

    // FVar IDs: 10 = h_eq proof, sentinel range = negated goal proof
    let h_eq_id = FVarId::new(10);

    // 1. Build ay terms and proof
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    // Register ay Bool variable "p" mapped to the Lean proposition (Eq Nat testA testB)
    let p = terms.mk_var("p", Sort::Bool);
    map.register_var("p", eq_prop.clone(), Expr::prop());
    // Hypothesis: "p" has proof h_eq (FVar 10) of type eq_prop
    map.register_hypothesis("p", h_eq_id, Expr::fvar(h_eq_id), eq_prop.clone());

    let not_p = terms.mk_not(p);

    let mut proof = Proof::new();
    let h1 = proof.add_assume(p, None);
    let h2 = proof.add_assume(not_p, None);
    proof.add_resolution(vec![], p, h1, h2);

    // 2. Build local context with hypothesis
    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        h_eq_id,
        Name::from_string("h_eq"),
        eq_prop.clone(),
        BinderInfo::Default,
    );

    // 3. Reconstruct — negated goal = ¬(Eq Nat testA testB)
    let result = attempt_reconstruction(&proof, &terms, &map, &neq_prop);

    // 4. Verify reconstruction succeeded
    assert!(
        result.stats.reconstructed_steps >= 3,
        "all 3 steps should reconstruct, got {} (error: {:?})",
        result.stats.reconstructed_steps,
        result.stats.error
    );
    let mut proof_term = result
        .proof_term
        .expect("unit contradiction should produce a proof term");

    // 5. If a sentinel negated-goal FVar was introduced, replace it with a
    //    normal FVarId that can safely live in LocalContext.
    //    Sentinel FVarIds (u64::MAX range) cannot be pushed to LocalContext
    //    because `push_with_id` does `id.0 + 1` which overflows.
    if let Some(sentinel_id) = result.negated_goal_fvar {
        let normal_neg_id = FVarId::new(20);
        proof_term = proof_term.subst_fvar(sentinel_id, &Expr::fvar(normal_neg_id));
        ctx.push_with_id(
            normal_neg_id,
            Name::from_string("h_neg"),
            neq_prop.clone(),
            BinderInfo::Default,
        );
    }

    // 6. Type-check through the kernel
    assert_proof_type_checks_to_false(&env, ctx, &proof_term, "ay unit contradiction e2e");
}

/// E2E: live ay QF_UF contradiction P, ¬P reconstructs to a False proof.
///
/// Unlike the synthetic unit-contradiction fixture above, this exercises the
/// real `AyProofBackend` emission path that `SmtSolver::prove` consumes.
#[test]
fn test_e2e_live_ay_prop_contradiction_type_checks() {
    let mut env = Environment::new();
    env.init_true_false().expect("init_true_false");
    let p_prop = Expr::const_(Name::from_string("P"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("add P : Prop");

    let h_p_id = FVarId::new(30);
    let h_not_p_id = FVarId::new(31);
    let not_p_prop = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        p_prop.clone(),
    );
    let neg_false = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        Expr::const_(Name::from_string("False"), vec![]),
    );

    let mut backend = AyProofBackend::new_with_proofs(AyLogic::QfUf);
    let p_name = backend.fresh_bool("P");
    backend.assert_formula(&p_name);
    backend.assert_formula(&format!("(not {p_name})"));

    match backend
        .check_sat()
        .expect("ay should solve prop contradiction")
    {
        AyProofResult::Unsat { .. } => {}
        other => panic!("expected UNSAT, got {other:?}"),
    }

    let mut map = VariableMapping::new();
    map.register_var(&p_name, p_prop.clone(), Expr::prop());
    map.register_hypothesis(&p_name, h_p_id, Expr::fvar(h_p_id), p_prop.clone());
    map.register_hypothesis(
        "h_not_p",
        h_not_p_id,
        Expr::fvar(h_not_p_id),
        not_p_prop.clone(),
    );

    let result = backend
        .attempt_kernel_reconstruction(&map, &neg_false)
        .expect("live ay contradiction should produce an accepted refutation");
    assert!(
        result.quality().is_fully_verified(),
        "live ay contradiction should be fully reconstructed without embedded trust"
    );

    let mut ctx = LocalContext::new();
    ctx.push_with_id(h_p_id, Name::from_string("hP"), p_prop, BinderInfo::Default);
    ctx.push_with_id(
        h_not_p_id,
        Name::from_string("hNotP"),
        not_p_prop,
        BinderInfo::Default,
    );

    let proof_term = result.refutation();
    assert_proof_type_checks_to_false(&env, ctx, proof_term, "live ay contradiction e2e");
}

/// Build a ay congruent-pred proof: {¬(a=b), ¬P(a), P(b)} + resolution to empty clause.
///
/// Returns (terms, map, proof, p_a, p_b) where p_a/p_b are the Lean proposition exprs.
fn mk_euf_congruent_pred_ay_proof(
    h_ab_id: FVarId,
    h_pa_id: FVarId,
    eq_ab: &Expr,
    p_a: &Expr,
    p_const: &Expr,
) -> (TermStore, VariableMapping, Proof) {
    use ay_core::TheoryLemmaKind;

    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let ay_a = terms.mk_var("fvar_1", Sort::Int);
    let ay_b = terms.mk_var("fvar_2", Sort::Int);

    map.register_var(
        "fvar_1",
        Expr::const_(Name::from_string("testA"), vec![]),
        int_ty.clone(),
    );
    map.register_var(
        "fvar_2",
        Expr::const_(Name::from_string("testB"), vec![]),
        int_ty.clone(),
    );

    let pred_name = "fvar_10";
    let p_a_ay = terms.mk_app(
        ay_core::Symbol::Named(pred_name.to_string()),
        vec![ay_a],
        Sort::Bool,
    );
    let p_b_ay = terms.mk_app(
        ay_core::Symbol::Named(pred_name.to_string()),
        vec![ay_b],
        Sort::Bool,
    );
    let pred_ty = Expr::pi(BinderInfo::Default, int_ty, Expr::sort(Level::zero()));
    map.register_var(pred_name, p_const.clone(), pred_ty);

    let ay_eq_ab = terms.mk_eq(ay_a, ay_b);
    let ay_not_eq_ab = terms.mk_not(ay_eq_ab);
    let ay_not_p_a = terms.mk_not(p_a_ay);

    map.register_hypothesis("h_ab", h_ab_id, Expr::fvar(h_ab_id), eq_ab.clone());
    map.register_hypothesis("h_pa", h_pa_id, Expr::fvar(h_pa_id), p_a.clone());

    let mut proof = Proof::new();
    let s0 = proof.add_theory_lemma_with_kind(
        "EUF",
        vec![ay_not_eq_ab, ay_not_p_a, p_b_ay],
        TheoryLemmaKind::EufCongruentPred,
    );
    let s1 = proof.add_assume(ay_eq_ab, None);
    let s2 = proof.add_resolution(vec![ay_not_p_a, p_b_ay], ay_not_eq_ab, s0, s1);
    let s3 = proof.add_assume(p_a_ay, None);
    let s4 = proof.add_resolution(vec![p_b_ay], ay_not_p_a, s2, s3);
    let ay_not_p_b = terms.mk_not(p_b_ay);
    let s5 = proof.add_assume(ay_not_p_b, None);
    proof.add_resolution(vec![], p_b_ay, s4, s5);

    (terms, map, proof)
}

/// E2E: EUF congruent-pred theory lemma + resolution → kernel type-checks to False.
///
/// Exercises Eq.mpr transport in theory_lemma_pred.rs: congrArg builds P(a) = P(b),
/// then Eq.mpr transports the proof. Catches universe and direction errors.
///
/// Part of #2398.
#[test]
fn test_e2e_euf_congruent_pred_type_checks() {
    let mut env = mk_env_with_classical();
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let p_type = Expr::pi(BinderInfo::Default, int_ty, Expr::sort(Level::zero()));
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("testP"),
        level_params: vec![],
        type_: p_type,
    })
    .expect("add testP");

    let p_const = Expr::const_(Name::from_string("testP"), vec![]);
    let p_a = Expr::app(
        p_const.clone(),
        Expr::const_(Name::from_string("testA"), vec![]),
    );
    let p_b = Expr::app(
        p_const.clone(),
        Expr::const_(Name::from_string("testB"), vec![]),
    );

    let h_ab_id = FVarId::new(10);
    let h_pa_id = FVarId::new(11);
    let eq_ab = mk_eq_int("testA", "testB");

    let (terms, map, proof) =
        mk_euf_congruent_pred_ay_proof(h_ab_id, h_pa_id, &eq_ab, &p_a, &p_const);

    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        h_ab_id,
        Name::from_string("h_ab"),
        eq_ab,
        BinderInfo::Default,
    );
    ctx.push_with_id(h_pa_id, Name::from_string("h_pa"), p_a, BinderInfo::Default);

    let not_p_b = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), p_b);
    let result = attempt_reconstruction(&proof, &terms, &map, &not_p_b);

    assert!(
        result.stats.reconstructed_steps >= 7,
        "all 7 steps should reconstruct, got {} (error: {:?})",
        result.stats.reconstructed_steps,
        result.stats.error
    );
    let mut proof_term = result
        .proof_term
        .expect("congruent-pred + resolution should produce a proof term");

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

    assert_proof_type_checks_to_false(&env, ctx, &proof_term, "EUF congruent-pred e2e");
}

/// Build ay terms, variable mappings, and 3-arg EUF congruent proof:
/// {¬(a1=b1), ¬(a2=b2), ¬(a3=b3), f(a1,a2,a3)=f(b1,b2,b3)} resolved to empty clause.
fn mk_euf_congruent_three_arg_ay_proof(
    h1_id: FVarId,
    h2_id: FVarId,
    h3_id: FVarId,
    eq_a1b1: &Expr,
    eq_a2b2: &Expr,
    eq_a3b3: &Expr,
) -> (TermStore, VariableMapping, Proof) {
    use ay_core::TheoryLemmaKind;

    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let ay_a1 = terms.mk_var("fvar_1", Sort::Int);
    let ay_b1 = terms.mk_var("fvar_2", Sort::Int);
    let ay_a2 = terms.mk_var("fvar_3", Sort::Int);
    let ay_b2 = terms.mk_var("fvar_4", Sort::Int);
    let ay_a3 = terms.mk_var("fvar_5", Sort::Int);
    let ay_b3 = terms.mk_var("fvar_6", Sort::Int);

    map.register_var(
        "fvar_1",
        Expr::const_(Name::from_string("testA1"), vec![]),
        int_ty.clone(),
    );
    map.register_var(
        "fvar_2",
        Expr::const_(Name::from_string("testB1"), vec![]),
        int_ty.clone(),
    );
    map.register_var(
        "fvar_3",
        Expr::const_(Name::from_string("testA2"), vec![]),
        int_ty.clone(),
    );
    map.register_var(
        "fvar_4",
        Expr::const_(Name::from_string("testB2"), vec![]),
        int_ty.clone(),
    );
    map.register_var(
        "fvar_5",
        Expr::const_(Name::from_string("testA3"), vec![]),
        int_ty.clone(),
    );
    map.register_var(
        "fvar_6",
        Expr::const_(Name::from_string("testB3"), vec![]),
        int_ty.clone(),
    );

    // Register testF as ternary function: Int → Int → Int → Int
    let f_name = "fvar_10";
    let f_ty = Expr::pi(
        BinderInfo::Default,
        int_ty.clone(),
        Expr::pi(
            BinderInfo::Default,
            int_ty.clone(),
            Expr::pi(BinderInfo::Default, int_ty.clone(), int_ty),
        ),
    );
    map.register_var(
        f_name,
        Expr::const_(Name::from_string("testF"), vec![]),
        f_ty,
    );

    let f_a = terms.mk_app(
        ay_core::Symbol::Named(f_name.to_string()),
        vec![ay_a1, ay_a2, ay_a3],
        Sort::Int,
    );
    let f_b = terms.mk_app(
        ay_core::Symbol::Named(f_name.to_string()),
        vec![ay_b1, ay_b2, ay_b3],
        Sort::Int,
    );

    let ay_eq_a1b1 = terms.mk_eq(ay_a1, ay_b1);
    let ay_eq_a2b2 = terms.mk_eq(ay_a2, ay_b2);
    let ay_eq_a3b3 = terms.mk_eq(ay_a3, ay_b3);
    let ay_eq_fafb = terms.mk_eq(f_a, f_b);
    let ay_not_a1b1 = terms.mk_not(ay_eq_a1b1);
    let ay_not_a2b2 = terms.mk_not(ay_eq_a2b2);
    let ay_not_a3b3 = terms.mk_not(ay_eq_a3b3);

    map.register_hypothesis("h1", h1_id, Expr::fvar(h1_id), eq_a1b1.clone());
    map.register_hypothesis("h2", h2_id, Expr::fvar(h2_id), eq_a2b2.clone());
    map.register_hypothesis("h3", h3_id, Expr::fvar(h3_id), eq_a3b3.clone());

    // Proof: TheoryLemma + 3 Assumes + 3 Resolutions + 1 Assume(¬goal) + 1 Resolution
    let mut proof = Proof::new();
    let s0 = proof.add_theory_lemma_with_kind(
        "EUF",
        vec![ay_not_a1b1, ay_not_a2b2, ay_not_a3b3, ay_eq_fafb],
        TheoryLemmaKind::EufCongruent,
    );
    // Resolve ¬(a1=b1) with Assume(a1=b1)
    let s1 = proof.add_assume(ay_eq_a1b1, None);
    let s2 = proof.add_resolution(
        vec![ay_not_a2b2, ay_not_a3b3, ay_eq_fafb],
        ay_not_a1b1,
        s0,
        s1,
    );
    // Resolve ¬(a2=b2) with Assume(a2=b2)
    let s3 = proof.add_assume(ay_eq_a2b2, None);
    let s4 = proof.add_resolution(vec![ay_not_a3b3, ay_eq_fafb], ay_not_a2b2, s2, s3);
    // Resolve ¬(a3=b3) with Assume(a3=b3)
    let s5 = proof.add_assume(ay_eq_a3b3, None);
    let s6 = proof.add_resolution(vec![ay_eq_fafb], ay_not_a3b3, s4, s5);
    // Resolve f(a)=f(b) with Assume(¬(f(a)=f(b)))
    let ay_not_fafb = terms.mk_not(ay_eq_fafb);
    let s7 = proof.add_assume(ay_not_fafb, None);
    proof.add_resolution(vec![], ay_eq_fafb, s6, s7);

    (terms, map, proof)
}

/// Environment with 6 Int axioms (testA1..testB3) and ternary function testF.
/// Returns (env, eq_a1b1, eq_a2b2, eq_a3b3, neg_fafb).
fn mk_env_three_arg_congruent() -> (Environment, Expr, Expr, Expr, Expr) {
    let mut env = mk_env_with_classical();
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    for name in ["testA1", "testB1", "testA2", "testB2", "testA3", "testB3"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: int_ty.clone(),
        })
        .unwrap_or_else(|e| panic!("add {name}: {e:?}"));
    }
    let f_ty = Expr::pi(
        BinderInfo::Default,
        int_ty.clone(),
        Expr::pi(
            BinderInfo::Default,
            int_ty.clone(),
            Expr::pi(BinderInfo::Default, int_ty.clone(), int_ty.clone()),
        ),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("testF"),
        level_params: vec![],
        type_: f_ty,
    })
    .expect("add testF");

    let eq_a1b1 = mk_eq_int("testA1", "testB1");
    let eq_a2b2 = mk_eq_int("testA2", "testB2");
    let eq_a3b3 = mk_eq_int("testA3", "testB3");

    let f_const = Expr::const_(Name::from_string("testF"), vec![]);
    let f_a = Expr::app(
        Expr::app(
            Expr::app(
                f_const.clone(),
                Expr::const_(Name::from_string("testA1"), vec![]),
            ),
            Expr::const_(Name::from_string("testA2"), vec![]),
        ),
        Expr::const_(Name::from_string("testA3"), vec![]),
    );
    let f_b = Expr::app(
        Expr::app(
            Expr::app(f_const, Expr::const_(Name::from_string("testB1"), vec![])),
            Expr::const_(Name::from_string("testB2"), vec![]),
        ),
        Expr::const_(Name::from_string("testB3"), vec![]),
    );
    let eq_fafb = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                int_ty,
            ),
            f_a,
        ),
        f_b,
    );
    let neg_fafb = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), eq_fafb);
    (env, eq_a1b1, eq_a2b2, eq_a3b3, neg_fafb)
}

/// E2E: EUF 3-arg congruent + resolution chain → kernel type-checks to False.
///
/// Exercises the full multi-arg congr chain loop (for k in 1..n with n=3):
///   congr (congr (congrArg testF h1) h2) h3
/// Catches BVar index errors in depth calculation BVar(depth-1-k).
///
/// Part of #2415.
#[test]
fn test_e2e_euf_congruent_three_arg_type_checks() {
    let (env, eq_a1b1, eq_a2b2, eq_a3b3, neg_fafb) = mk_env_three_arg_congruent();
    let h1_id = FVarId::new(10);
    let h2_id = FVarId::new(11);
    let h3_id = FVarId::new(12);

    let (terms, map, proof) =
        mk_euf_congruent_three_arg_ay_proof(h1_id, h2_id, h3_id, &eq_a1b1, &eq_a2b2, &eq_a3b3);

    let mut ctx = LocalContext::new();
    ctx.push_with_id(h1_id, Name::from_string("h1"), eq_a1b1, BinderInfo::Default);
    ctx.push_with_id(h2_id, Name::from_string("h2"), eq_a2b2, BinderInfo::Default);
    ctx.push_with_id(h3_id, Name::from_string("h3"), eq_a3b3, BinderInfo::Default);

    let result = attempt_reconstruction(&proof, &terms, &map, &neg_fafb);
    assert!(
        result.stats.reconstructed_steps >= 9,
        "all 9 steps should reconstruct, got {} (error: {:?})",
        result.stats.reconstructed_steps,
        result.stats.error,
    );
    let mut proof_term = result
        .proof_term
        .expect("3-arg EUF congruent + resolution should produce a proof term");

    if let Some(sentinel_id) = result.negated_goal_fvar {
        let neg_id = FVarId::new(20);
        proof_term = proof_term.subst_fvar(sentinel_id, &Expr::fvar(neg_id));
        ctx.push_with_id(
            neg_id,
            Name::from_string("h_neg_goal"),
            neg_fafb.clone(),
            BinderInfo::Default,
        );
    }

    assert_proof_type_checks_to_false(&env, ctx, &proof_term, "EUF 3-arg congruent e2e");
}
