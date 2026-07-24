// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regressions for local-context simp lemma collection and usage.
//!
//! Part of #2496.

use super::*;
use crate::tactic::simp::simp_expr;

fn mk_explicit_eq(ty: Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                ty,
            ),
            lhs,
        ),
        rhs,
    )
}

fn add_axiom(env: &mut Environment, name: &str, type_: Expr) {
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
    })
    .unwrap();
}

fn setup_no_index_env() -> (Environment, Expr) {
    let mut env = Environment::new();
    env.init_eq().unwrap();
    add_axiom(&mut env, "N", Expr::type_());
    let n = Expr::const_(Name::from_string("N"), vec![]);
    add_axiom(
        &mut env,
        "f",
        Expr::arrow(n.clone(), Expr::arrow(n.clone(), n.clone())),
    );
    add_axiom(&mut env, "g", Expr::arrow(n.clone(), n.clone()));
    for name in ["a", "b"] {
        add_axiom(&mut env, name, n.clone());
    }
    (env, n)
}

fn add_unary_function(env: &mut Environment, name: &str, domain: &Expr) {
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, domain.clone(), domain.clone()),
    })
    .unwrap();
}

fn mk_no_index_local_eq(n: &Expr) -> Expr {
    Expr::pi(
        BinderInfo::Default,
        n.clone(),
        mk_explicit_eq(
            n.clone(),
            Expr::app(
                Expr::app(Expr::const_(Name::from_string("f"), vec![]), Expr::bvar(0)),
                Expr::app(Expr::const_(Name::from_string("g"), vec![]), Expr::bvar(0)),
            ),
            Expr::app(Expr::const_(Name::from_string("g"), vec![]), Expr::bvar(0)),
        ),
    )
}

fn mk_no_index_query() -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("f"), vec![]),
            Expr::const_(Name::from_string("a"), vec![]),
        ),
        Expr::const_(Name::from_string("b"), vec![]),
    )
}

fn wrap_app(arg: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("wrap"), vec![]), arg)
}

fn setup_no_index_local_state() -> (ProofState, Goal, Expr) {
    let (env, n) = setup_no_index_env();
    let local_eq = mk_no_index_local_eq(&n);
    let state = ProofState::with_context(
        env,
        mk_explicit_eq(
            n,
            Expr::const_(Name::from_string("a"), vec![]),
            Expr::const_(Name::from_string("a"), vec![]),
        ),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: local_eq,
            value: None,
        }],
    );
    let goal = state.current_goal().expect("goal should exist").clone();
    let query = mk_no_index_query();
    (state, goal, query)
}

#[test]
fn test_collect_simp_lemmas_resolves_local_extra_lemma() {
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let goal = Expr::pi(
        BinderInfo::Default,
        make_eq_n(x.clone(), y.clone()),
        make_p(x.clone()),
    );
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "hxy").expect("intro should create the local equality hypothesis");

    let mut config = SimpConfig::new();
    config.extra_lemmas.push("hxy".to_string());

    let lemmas = collect_simp_lemmas(&state, &config);
    let local = lemmas
        .iter()
        .find(|lemma| lemma.name == Name::from_string("hxy"))
        .expect("local equality hypothesis should become a simp lemma");

    let hyp_fvar = state.current_goal().unwrap().local_ctx[0].fvar;
    assert_eq!(
        local.lhs, x,
        "local simp lemma should use the hypothesis lhs"
    );
    assert_eq!(
        local.rhs, y,
        "local simp lemma should use the hypothesis rhs"
    );
    assert_eq!(
        local.proof_expr,
        Some(Expr::fvar(hyp_fvar)),
        "local simp lemma should carry the hypothesis proof fvar"
    );
    assert_eq!(
        local.index_mode,
        SimpIndexMode::NoIndexAtArgs,
        "local proof-backed simp lemmas should opt into no-index-at-args matching"
    );
}

#[test]
fn test_simp_expr_uses_local_proof_backed_extra_lemma() {
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let goal = Expr::pi(
        BinderInfo::Default,
        make_eq_n(x.clone(), y.clone()),
        make_eq_n(x.clone(), y.clone()),
    );
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "hxy").expect("intro should create the local equality hypothesis");

    let mut config = SimpConfig::new();
    config.extra_lemmas.push("hxy".to_string());

    let goal = state.current_goal().expect("goal should exist").clone();
    let lemmas = collect_simp_lemmas(&state, &config);
    let result = simp_expr(&state, &goal, &x, &lemmas, &config);

    let hyp_fvar = goal.local_ctx[0].fvar;
    assert_eq!(
        result.expr, y,
        "local equality hypotheses should rewrite directly"
    );
    assert_eq!(
        result.proof,
        Some(Expr::fvar(hyp_fvar)),
        "local proof-backed rewrites should reuse the hypothesis witness"
    );
}

#[test]
fn test_local_extra_lemma_candidates_use_no_index_at_args_matching() {
    let (state, goal, query) = setup_no_index_local_state();

    let mut config = SimpConfig::new();
    config.extra_lemmas.push("h".to_string());
    let lemmas = collect_simp_lemmas(&state, &config);

    assert!(
        lemmas
            .candidates(&state, &goal, &query)
            .iter()
            .any(|lemma| lemma.name == Name::from_string("h")),
        "local proof-backed entries should be retrievable through no-index-at-args matching"
    );
}

#[test]
fn test_simp_expr_multi_binder_local_extra_lemma_instantiates_proof_arguments() {
    let mut env = setup_env_with_full_eq();
    let n = Expr::const_(Name::from_string("N"), vec![]);
    add_unary_function(&mut env, "wrap", &n);

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let local_eq_ty = Expr::pi(
        BinderInfo::Default,
        n,
        make_eq_n(
            Expr::app(
                Expr::const_(Name::from_string("wrap"), vec![]),
                Expr::bvar(0),
            ),
            Expr::bvar(0),
        ),
    );
    let goal = Expr::pi(
        BinderInfo::Default,
        local_eq_ty,
        make_eq_n(wrap_app(x.clone()), x.clone()),
    );
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "h").expect("intro should create the local bindered simp hypothesis");

    let mut config = SimpConfig::new();
    config.extra_lemmas.push("h".to_string());
    let goal = state.current_goal().expect("goal should exist").clone();
    let lemmas = collect_simp_lemmas(&state, &config);
    let result = simp_expr(&state, &goal, &wrap_app(x.clone()), &lemmas, &config);

    let hyp_fvar = goal.local_ctx[0].fvar;
    let expected_proof = Expr::app(Expr::fvar(hyp_fvar), x.clone());
    let expected_ty = make_eq_n(wrap_app(x.clone()), x);

    assert_eq!(
        result.expr,
        Expr::const_(Name::from_string("x"), vec![]),
        "bindered local simp lemma should rewrite the application result"
    );
    assert_eq!(
        result.proof,
        Some(expected_proof.clone()),
        "bindered local simp rewrites should instantiate the local proof witness"
    );
    assert!(
        state.infer_type(&goal, &expected_proof).ok().as_ref() == Some(&expected_ty),
        "the instantiated local proof witness should remain kernel-valid"
    );
}

#[test]
fn test_simp_with_local_extra_lemma_rewrites_non_dependent_pi_domain() {
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let target = Expr::pi(BinderInfo::Default, make_p(x.clone()), make_p(y.clone()));
    let mut state = ProofState::with_context(
        env,
        target,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: make_eq_n(x, y.clone()),
            value: None,
        }],
    );

    let mut config = SimpConfig::new();
    config.extra_lemmas.push("h".to_string());
    simp(&mut state, config).expect("simp [h] should rewrite the implication premise");

    let goal = state.current_goal().expect("goal should remain open");
    assert_eq!(
        goal.target,
        Expr::pi(BinderInfo::Default, make_p(y.clone()), make_p(y)),
        "local simp lemmas should rewrite nondependent Pi domains"
    );
}
