// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! simp must carry a proof through a binder whose body mentions that binder.
//!
//! # The defect these fixtures pin
//!
//! Every congruence builder in `tactic::simp::proof` types its subterms with
//! `ProofState::infer_type`, and the kernel cannot type a term with LOOSE bound
//! variables. Before `simp::binder::open_binder`, the traversal descended into
//! `Lam`/`Pi` bodies in raw de Bruijn form, so any redex mentioning an
//! enclosing binder was an open term: `mk_congr_arg` returned `None`,
//! `mk_funext`/`mk_forall_congr` were never reached, and `simp` recorded
//! `made_progress = true` with `accumulated_proof = None`.
//!
//! `accumulated_proof = None` *claims the change was definitional*, so `simp`
//! then went through `replace_target_def_eq`, which correctly refused — the
//! rewrite was propositional, not definitional. Mathlib source elaboration saw
//! that as
//!
//! ```text
//! Tactic failed: goal mismatch: replace_target_def_eq:
//!   new target is not definitionally equal to current target
//! ```
//!
//! on `Logic/Basic.forall_apply_eq_imp_iff'`, `forall_eq_apply_imp_iff'`,
//! `dite_ne_right_iff`, `Function/Basic.not_injective_iff` and
//! `Function.invFun_eq` (2026-08-23 srcelab report, commit `14a1e99a9`).
//!
//! The last fixture here is the counterweight required by the lane rule that a
//! tactic producing a WRONG proof is worse than one that fails: when the
//! congruence genuinely cannot be built (dependent codomain — `mk_funext`
//! refuses by contract), `simp` must still fail closed and leave the goal
//! alone rather than install an unproved target.

use super::*;
use crate::tactic::simp::{collect_simp_lemmas, simp_expr, SimpConfig};
use clean_kernel::env::SimpPriority;
use serial_test::serial;

/// `N`, `x`/`y`/`z : N`, `P : N → Prop`, `Eq`, plus `funext` and a unary
/// `f : N → N` with the registered simp lemma `f_eq : ∀ t, f t = c`.
fn setup_env_with_unary_simp_lemma() -> Environment {
    let mut env = setup_env_with_full_eq();
    env.init_funext().unwrap();

    let n = Expr::const_(Name::from_string("N"), vec![]);
    for name in ["f", "g"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::pi(BinderInfo::Default, n.clone(), n.clone()),
        })
        .unwrap();
    }
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("c"),
        level_params: vec![],
        type_: n.clone(),
    })
    .unwrap();

    // f_eq : ∀ (t : N), f t = c
    let f_t = Expr::app(Expr::const_(Name::from_string("f"), vec![]), Expr::bvar(0));
    let f_eq_ty = Expr::pi(
        BinderInfo::Default,
        n,
        make_eq_n(f_t, Expr::const_(Name::from_string("c"), vec![])),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("f_eq"),
        level_params: vec![],
        type_: f_eq_ty,
    })
    .unwrap();
    env.register_simp_lemma(Name::from_string("f_eq"), SimpPriority::Default);
    env
}

fn n_ty() -> Expr {
    Expr::const_(Name::from_string("N"), vec![])
}

fn call(name: &str, arg: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string(name), vec![]), arg)
}

/// `@Eq.{u+1} ty lhs rhs` for an arbitrary carrier `ty : Sort u`.
fn make_eq_at(ty: Expr, level: Level, lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Eq"), vec![level]), ty),
            lhs,
        ),
        rhs,
    )
}

fn assert_kernel_valid_proof(env: &Environment, proof: &Expr, expected_ty: &Expr, context: &str) {
    let tc = TypeChecker::new(env);
    match tc.check_type(proof, expected_ty) {
        Ok(()) => {}
        Err(e) => panic!("{context}: kernel rejected the simp proof term: {e:?}"),
    }
}

/// The core regression: a redex under a `λ` binder that MENTIONS that binder.
///
/// `λ a : N, g (f a)` simplifies to `λ a : N, g c`; the step needs
/// `congrArg` under the binder and `funext` to close over it, both of which
/// need the body's type — unavailable while `f a` is `f (BVar 0)`.
#[test]
#[serial]
fn test_simp_expr_lambda_body_mentioning_binder_carries_kernel_valid_proof() {
    reset_all_counters();
    let env = setup_env_with_unary_simp_lemma();

    let lam_old = Expr::lam(
        BinderInfo::Default,
        n_ty(),
        call("g", call("f", Expr::bvar(0))),
    );
    let lam_new = Expr::lam(
        BinderInfo::Default,
        n_ty(),
        call("g", Expr::const_(Name::from_string("c"), vec![])),
    );

    let state = ProofState::new(env, Expr::const_(Name::from_string("N"), vec![]));
    let goal = state.current_goal().unwrap().clone();
    let config = SimpConfig::new();
    let lemmas = collect_simp_lemmas(&state, &config);
    let result = simp_expr(&state, &goal, &lam_old, &lemmas, &config);

    assert_eq!(
        result.expr, lam_new,
        "simp must rewrite `f a` to `c` under the lambda binder"
    );
    let proof = result.proof.as_ref().expect(
        "simp must carry a proof for a rewrite under a binder — a `None` here \
         claims the change was DEFINITIONAL, which it is not",
    );
    let fn_ty = Expr::pi(BinderInfo::Default, n_ty(), n_ty());
    let expected = make_eq_at(fn_ty, Level::succ(Level::zero()), lam_old, lam_new);
    assert_kernel_valid_proof(state.env(), proof, &expected, "lambda-body rewrite");
}

/// Same shape one level deeper: the redex mentions the OUTER of two binders.
#[test]
#[serial]
fn test_simp_expr_nested_lambda_outer_binder_redex_carries_kernel_valid_proof() {
    reset_all_counters();
    let env = setup_env_with_unary_simp_lemma();

    // λ a : N, λ _b : N, g (f a)   — `f a` is `f (BVar 1)` inside the inner λ.
    let inner_old = Expr::lam(
        BinderInfo::Default,
        n_ty(),
        call("g", call("f", Expr::bvar(1))),
    );
    let lam_old = Expr::lam(BinderInfo::Default, n_ty(), inner_old);
    let inner_new = Expr::lam(
        BinderInfo::Default,
        n_ty(),
        call("g", Expr::const_(Name::from_string("c"), vec![])),
    );
    let lam_new = Expr::lam(BinderInfo::Default, n_ty(), inner_new);

    let state = ProofState::new(env, n_ty());
    let goal = state.current_goal().unwrap().clone();
    let config = SimpConfig::new();
    let lemmas = collect_simp_lemmas(&state, &config);
    let result = simp_expr(&state, &goal, &lam_old, &lemmas, &config);

    assert_eq!(
        result.expr, lam_new,
        "simp must rewrite under two binders when the redex mentions the outer one"
    );
    let proof = result
        .proof
        .as_ref()
        .expect("nested-binder rewrite must carry a proof");
    let inner_fn_ty = Expr::pi(BinderInfo::Default, n_ty(), n_ty());
    let outer_fn_ty = Expr::pi(BinderInfo::Default, n_ty(), inner_fn_ty);
    let expected = make_eq_at(outer_fn_ty, Level::succ(Level::zero()), lam_old, lam_new);
    assert_kernel_valid_proof(state.env(), proof, &expected, "nested-lambda rewrite");
}

/// End-to-end: the `simp` TACTIC on a `∀`-goal whose body mentions the binder.
///
/// This is the exact Mathlib failure surface — before the fix this returned
/// `Err(GoalMismatch("replace_target_def_eq: …"))`. The assertion is not just
/// "simp succeeded": the closed proof term is handed to the kernel against the
/// ORIGINAL target, so a rewrite that lied about its proof cannot pass here.
#[test]
#[serial]
fn test_simp_tactic_forall_goal_with_binder_redex_closes_kernel_checked() {
    reset_all_counters();
    let mut env = setup_env_with_unary_simp_lemma();
    add_lean_forall_congr(&mut env);

    // Goal: ∀ (a : N), P (g (f a))
    let target = Expr::pi(
        BinderInfo::Default,
        n_ty(),
        call("P", call("g", call("f", Expr::bvar(0)))),
    );
    // Witness for the SIMPLIFIED statement, so `exact` can close it.
    let simplified = Expr::pi(
        BinderInfo::Default,
        n_ty(),
        call("P", call("g", Expr::const_(Name::from_string("c"), vec![]))),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("h_simplified"),
        level_params: vec![],
        type_: simplified.clone(),
    })
    .unwrap();

    let mut state = ProofState::new(env, target.clone());
    simp_default(&mut state).expect(
        "simp must rewrite `f a` under the ∀ binder — a GoalMismatch here is the \
         `replace_target_def_eq` defect, i.e. simp made progress it could not prove",
    );
    assert_eq!(
        state.current_goal().unwrap().target,
        simplified,
        "the rewritten target must be the simplified statement"
    );

    exact(
        &mut state,
        Expr::const_(Name::from_string("h_simplified"), vec![]),
    )
    .expect("the simplified goal is closed by its witness");
    assert!(state.is_complete(), "simp + exact must close the goal");
    let closed = state
        .closed_proof()
        .expect("a complete proof state must expose its proof term");
    assert_kernel_valid_proof(state.env(), &closed, &target, "∀-goal simp closure");
}

/// The counterweight: simp must REFUSE when the congruence cannot be built.
///
/// `mk_funext` refuses a DEPENDENT codomain by contract — closing a pointwise
/// equality over `(a : N) → Vec a` needs dependent function extensionality,
/// which `funext` is not. So the body rewrite here has a perfectly good proof
/// and the lambda still cannot be lifted: no proof reaches `simp`, and the
/// change (`f a` → `c` under an axiom `f`) is not definitional either.
///
/// `simp` must therefore fail closed. Opening binders makes simp prove MORE,
/// and this fixture is the boundary: it must never make simp install a target
/// on the strength of a proof it does not have.
#[test]
#[serial]
fn test_simp_refuses_dependent_codomain_rewrite_it_cannot_prove() {
    reset_all_counters();
    let mut env = setup_env_with_unary_simp_lemma();
    let n = n_ty();

    // Vec : N → Type, and mkv : (t : N) → N → Vec t.
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Vec"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, n.clone(), Expr::type_()),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("mkv"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            n.clone(),
            Expr::pi(BinderInfo::Default, n.clone(), call("Vec", Expr::bvar(1))),
        ),
    })
    .unwrap();

    // PV : ((a : N) → Vec a) → Prop
    let dep_fn_ty = Expr::pi(BinderInfo::Default, n.clone(), call("Vec", Expr::bvar(0)));
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("PV"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, dep_fn_ty, Expr::prop()),
    })
    .unwrap();

    // Goal: PV (fun a : N => mkv a (f a)).  The body rewrite `f a → c` is
    // provable (congrArg over the non-dependent `mkv a`), but lifting it over
    // the binder needs dependent funext, which simp does not have.
    let lam = Expr::lam(
        BinderInfo::Default,
        n,
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("mkv"), vec![]),
                Expr::bvar(0),
            ),
            call("f", Expr::bvar(0)),
        ),
    );
    let target = call("PV", lam);

    let mut state = ProofState::new(env, target.clone());
    let outcome = simp_default(&mut state);
    assert!(
        outcome.is_err(),
        "simp must fail closed when it cannot lift the rewrite over a dependent \
         codomain — Ok here means it installed a target it could not prove"
    );
    assert_eq!(
        state.current_goal().unwrap().target,
        target,
        "a refused simp must leave the goal target untouched"
    );
}

/// simp must not INVENT progress: with no lemma matching the goal it reports
/// `NoProgress` and leaves the target alone, binder-opening notwithstanding.
#[test]
#[serial]
fn test_simp_reports_no_progress_under_binder_without_a_matching_lemma() {
    reset_all_counters();
    let env = setup_env_with_unary_simp_lemma();

    // `g` has no simp lemma; `∀ a, P (g a)` must stay exactly as written.
    let target = Expr::pi(
        BinderInfo::Default,
        n_ty(),
        call("P", call("g", Expr::bvar(0))),
    );
    let mut state = ProofState::new(env, target.clone());
    let outcome = simp_default(&mut state);
    assert!(
        matches!(outcome, Err(TacticError::NoProgress { .. })),
        "simp must report NoProgress, got {outcome:?}"
    );
    assert!(
        !state.is_complete(),
        "simp must not close a goal nothing proves"
    );
    assert_eq!(
        state.current_goal().unwrap().target,
        target,
        "a no-progress simp must leave the goal target untouched"
    );
}
