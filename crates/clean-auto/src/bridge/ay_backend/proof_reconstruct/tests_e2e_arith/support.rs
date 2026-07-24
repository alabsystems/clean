// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared helpers for arithmetic e2e tests.

use super::*;
use crate::bridge::ay_backend::ResidualTrustSummary;

pub(super) type HypothesisSetup = Vec<(FVarId, &'static str, Expr)>;

pub(super) struct ArithmeticE2eCase {
    pub(super) env: Environment,
    pub(super) terms: TermStore,
    pub(super) map: VariableMapping,
    pub(super) proof: Proof,
    pub(super) neg_goal: Expr,
    pub(super) hyps: HypothesisSetup,
    pub(super) context: &'static str,
}

pub(super) fn mk_env_for_int_arith() -> Environment {
    let mut env = Environment::new();
    env.init_int_ord_lemmas()
        .expect("init_int_ord_lemmas (pulls in Int arithmetic + ordering)");

    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    for name in ["testX", "testY"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: int_ty.clone(),
        })
        .expect("add test axiom decl");
    }
    env
}

pub(super) fn mk_env_for_real_arith() -> Environment {
    let mut env = Environment::new();
    env.init_true_false()
        .expect("init_true_false for False/Not/absurd");
    env.init_int_ord_lemmas()
        .expect("init_int_ord_lemmas for Int-based closers");
    env.init_real_linear_order()
        .expect("init_real_linear_order");

    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);
    for name in ["testX", "testY"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: real_ty.clone(),
        })
        .expect("add test axiom decl");
    }
    env
}

pub(super) fn mk_int_ofnat(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(n),
    )
}

pub(super) fn mk_real_ofnat(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Real.ofNat"), vec![]),
        Expr::nat_lit(n),
    )
}

pub(super) fn mk_le_int(a: &Expr, b: &Expr) -> Expr {
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
                    int_ty,
                ),
                Expr::const_(Name::from_string("instLEInt"), vec![]),
            ),
            a.clone(),
        ),
        b.clone(),
    )
}

pub(super) fn mk_lt_int(a: &Expr, b: &Expr) -> Expr {
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
                    int_ty,
                ),
                Expr::const_(Name::from_string("instLTInt"), vec![]),
            ),
            a.clone(),
        ),
        b.clone(),
    )
}

pub(super) fn mk_le_real(a: &Expr, b: &Expr) -> Expr {
    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
                    real_ty,
                ),
                Expr::const_(Name::from_string("instLEReal"), vec![]),
            ),
            a.clone(),
        ),
        b.clone(),
    )
}

pub(super) fn mk_lt_real(a: &Expr, b: &Expr) -> Expr {
    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
                    real_ty,
                ),
                Expr::const_(Name::from_string("instLTReal"), vec![]),
            ),
            a.clone(),
        ),
        b.clone(),
    )
}

pub(super) fn bind_negated_goal(
    mut proof_term: Expr,
    ctx: &mut LocalContext,
    neg_goal: &Expr,
    negated_goal_fvar: Option<FVarId>,
) -> Expr {
    if let Some(sentinel_id) = negated_goal_fvar {
        let normal_neg_id = FVarId::new(20);
        proof_term = proof_term.subst_fvar(sentinel_id, &Expr::fvar(normal_neg_id));
        ctx.push_with_id(
            normal_neg_id,
            Name::from_string("h_neg"),
            neg_goal.clone(),
            BinderInfo::Default,
        );
    }
    proof_term
}

pub(super) fn negated_false_goal() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        Expr::const_(Name::from_string("False"), vec![]),
    )
}

pub(super) fn assert_zero_trust_reconstruction(result: &ReconstructionResult, context: &str) {
    assert!(
        result.proof_term.is_some(),
        "{context} should produce a proof term: {:?}",
        result.stats
    );
    assert_eq!(
        result.stats.trust_boundary_steps, 0,
        "{context} should avoid the trust boundary: {:?}",
        result.stats
    );
    assert_eq!(
        result.stats.trust_fallback_steps, 0,
        "{context} should not use trusted fallback: {:?}",
        result.stats
    );
    assert_eq!(
        result.residual,
        ResidualTrustSummary::empty(),
        "{context} kernel-reconstructed proof should carry zero residual trust",
    );
}

pub(super) fn assert_case_type_checks(case: ArithmeticE2eCase) {
    let result = attempt_reconstruction(&case.proof, &case.terms, &case.map, &case.neg_goal);
    assert_zero_trust_reconstruction(&result, case.context);

    let mut ctx = LocalContext::new();
    for (id, name, prop) in case.hyps {
        ctx.push_with_id(id, Name::from_string(name), prop, BinderInfo::Default);
    }
    let proof_term = bind_negated_goal(
        result.proof_term.expect("arithmetic e2e proof term"),
        &mut ctx,
        &case.neg_goal,
        result.negated_goal_fvar,
    );
    assert_proof_type_checks_to_false(&case.env, ctx, &proof_term, case.context);
}
