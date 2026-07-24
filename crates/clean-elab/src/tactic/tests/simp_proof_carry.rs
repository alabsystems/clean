// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof-carry regressions for simp-family target rewrites.
//!
//! Part of #2503.

use super::*;
use serial_test::serial;

fn assert_no_trusted_fallback(state: &ProofState, tactic_name: &str, before: (u64, u64)) {
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "{tactic_name} must not record trusted axiom usage"
    );
    assert_no_trusted_axiom_usage(tactic_name, "simp-family target rewrite", before);
}

fn add_unary_function(env: &mut Environment, name: &str) {
    let n = Expr::const_(Name::from_string("N"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, n.clone(), n),
    })
    .unwrap();
}

fn wrap_app(arg: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("wrap"), vec![]), arg)
}

fn assert_kernel_valid_closed_proof(
    env: &Environment,
    proof: &Expr,
    expected_ty: &Expr,
    context: &str,
) {
    let tc = TypeChecker::new(env);
    let result = tc.check_type(proof, expected_ty);
    assert!(
        result.is_ok(),
        "{context}: closed proof must type-check against the rewritten goal, got {result:?} for proof {proof:?}"
    );
}

#[test]
#[serial]
fn test_simp_rw_local_forward_rewrite_preserves_proof_chain() {
    reset_all_counters();
    let env = setup_env_with_eq();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let h_ty = make_eq(a_ty.clone(), a.clone(), b.clone());
    let goal = Expr::pi(BinderInfo::Default, h_ty, make_eq(a_ty, a.clone(), a));
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "h").expect("intro should create the local rewrite hypothesis");
    let axiom_before = axiom_snapshot();

    simp_rw(&mut state, vec!["h".to_string()])
        .expect("simp_rw should rewrite via the local equality proof");

    assert!(
        state.is_complete(),
        "simp_rw should close the reflexive goal"
    );
    assert_no_trusted_fallback(&state, "simp_rw forward", axiom_before);
    assert!(
        state.proof_term().is_some(),
        "simp_rw must preserve proof_term() extraction on the forward path"
    );
    assert!(
        state.closed_proof().is_some(),
        "simp_rw must preserve closed_proof() extraction on the forward path"
    );
}

#[test]
#[serial]
fn test_simp_rw_local_reverse_rewrite_preserves_proof_chain() {
    reset_all_counters();
    let env = setup_env_with_eq();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let h_ty = make_eq(a_ty.clone(), a.clone(), b.clone());
    let goal = Expr::pi(BinderInfo::Default, h_ty, make_eq(a_ty, b.clone(), b));
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "h").expect("intro should create the local rewrite hypothesis");
    let axiom_before = axiom_snapshot();

    simp_rw(&mut state, vec!["h".to_string()])
        .expect("simp_rw should use Eq.symm h for the reverse local rewrite");

    assert!(
        state.is_complete(),
        "simp_rw should close the reverse reflexive goal"
    );
    assert_no_trusted_fallback(&state, "simp_rw reverse", axiom_before);
    assert!(
        state.proof_term().is_some(),
        "simp_rw must preserve proof_term() extraction on the reverse path"
    );
    assert!(
        state.closed_proof().is_some(),
        "simp_rw must preserve closed_proof() extraction on the reverse path"
    );
}

#[test]
#[serial]
fn test_simp_only_multi_binder_local_lemma_preserves_proof_chain() {
    reset_all_counters();
    let mut env = setup_env_with_full_eq();
    add_unary_function(&mut env, "wrap");

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let local_eq_ty = Expr::pi(
        BinderInfo::Default,
        Expr::const_(Name::from_string("N"), vec![]),
        make_eq_n(wrap_app(Expr::bvar(0)), Expr::bvar(0)),
    );
    let target_ty = make_eq_n(wrap_app(x.clone()), x);
    let goal_ty = Expr::pi(BinderInfo::Default, local_eq_ty, target_ty);
    let goal = goal_ty.clone();
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "h").expect("intro should create the local simp hypothesis");
    let axiom_before = axiom_snapshot();

    simp_only(&mut state, vec!["h".to_string()])
        .expect("simp_only should instantiate the local bindered lemma");

    assert!(
        state.is_complete(),
        "simp_only should close the goal via the local bindered rewrite"
    );
    assert_no_trusted_fallback(&state, "simp_only bindered local", axiom_before);
    let closed = state
        .closed_proof()
        .expect("simp_only should expose a closed proof after the local rewrite");
    assert_kernel_valid_closed_proof(state.env(), &closed, &goal_ty, "simp_only bindered local");
}

#[test]
#[serial]
fn test_simp_rw_multi_binder_local_forward_rewrite_preserves_proof_chain() {
    reset_all_counters();
    let mut env = setup_env_with_full_eq();
    add_unary_function(&mut env, "wrap");

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let local_eq_ty = Expr::pi(
        BinderInfo::Default,
        Expr::const_(Name::from_string("N"), vec![]),
        make_eq_n(wrap_app(Expr::bvar(0)), Expr::bvar(0)),
    );
    let target_ty = make_eq_n(wrap_app(x.clone()), x);
    let goal_ty = Expr::pi(BinderInfo::Default, local_eq_ty, target_ty);
    let goal = goal_ty.clone();
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "h").expect("intro should create the local simp_rw hypothesis");
    let axiom_before = axiom_snapshot();

    simp_rw(&mut state, vec!["h".to_string()])
        .expect("simp_rw should instantiate the local bindered rewrite");

    assert!(
        state.is_complete(),
        "simp_rw should close the forward bindered rewrite goal"
    );
    assert_no_trusted_fallback(&state, "simp_rw bindered forward", axiom_before);
    let closed = state
        .closed_proof()
        .expect("simp_rw forward bindered rewrite should produce a closed proof");
    assert_kernel_valid_closed_proof(state.env(), &closed, &goal_ty, "simp_rw bindered forward");
}

#[test]
#[serial]
fn test_simp_rw_multi_binder_local_reverse_goal_closes_without_overmatching() {
    reset_all_counters();
    let mut env = setup_env_with_full_eq();
    add_unary_function(&mut env, "wrap");

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let local_eq_ty = Expr::pi(
        BinderInfo::Default,
        Expr::const_(Name::from_string("N"), vec![]),
        make_eq_n(wrap_app(Expr::bvar(0)), Expr::bvar(0)),
    );
    let target_ty = make_eq_n(x.clone(), wrap_app(x));
    let goal_ty = Expr::pi(BinderInfo::Default, local_eq_ty, target_ty);
    let goal = goal_ty.clone();
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "h").expect("intro should create the reverse local simp_rw hypothesis");
    let axiom_before = axiom_snapshot();

    simp_rw(&mut state, vec!["h".to_string()]).expect(
        "simp_rw should close the reverse-oriented goal without overmatching generic reverse rules",
    );

    assert!(
        state.is_complete(),
        "simp_rw should close the reverse-oriented bindered goal"
    );
    assert_no_trusted_fallback(&state, "simp_rw bindered reverse", axiom_before);
    let closed = state
        .closed_proof()
        .expect("simp_rw reverse-oriented bindered goal should produce a closed proof");
    assert_kernel_valid_closed_proof(state.env(), &closed, &goal_ty, "simp_rw bindered reverse");
}

#[test]
#[serial]
fn test_squeeze_simp_uses_checked_rewrite_path() {
    reset_all_counters();
    let mut env = Environment::new();
    env.init_bool().unwrap();
    env.init_eq().unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("b"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Bool"), vec![]),
    })
    .unwrap();

    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let lhs = Expr::app(
        Expr::const_(Name::from_string("Bool.not"), vec![]),
        Expr::app(
            Expr::const_(Name::from_string("Bool.not"), vec![]),
            b.clone(),
        ),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("my_not_not"),
        level_params: vec![],
        type_: make_eq(bool_ty.clone(), lhs.clone(), b.clone()),
    })
    .unwrap();
    env.register_simp_lemma(
        Name::from_string("my_not_not"),
        clean_kernel::env::SimpPriority::Default,
    );

    let goal = make_eq(bool_ty, lhs, b);
    let mut state = ProofState::new(env, goal);
    let axiom_before = axiom_snapshot();

    let result = squeeze_simp(&mut state).expect("squeeze_simp should simplify the Bool goal");

    assert!(
        result.closed,
        "squeeze_simp should close the goal after rewriting to a reflexive equality"
    );
    assert_eq!(
        result.used_lemmas,
        vec!["my_not_not".to_string()],
        "squeeze_simp should report the exact simp lemma it used"
    );
    assert!(
        state.is_complete(),
        "squeeze_simp should leave the proof complete"
    );
    assert_no_trusted_fallback(&state, "squeeze_simp", axiom_before);
    assert!(
        state.proof_term().is_some(),
        "squeeze_simp must preserve proof_term() extraction"
    );
    assert!(
        state.closed_proof().is_some(),
        "squeeze_simp must preserve closed_proof() extraction"
    );
}

/// Part of #2442: the simp transitivity loop rewrites the LHS of equality goals
/// via a chain of simp lemmas. Previously this path fell back to trustedArith
/// because no proof terms were produced for the LHS rewrite steps. After the
/// proof-carry fix, congruence proofs are constructed for each step.
#[test]
#[serial]
fn test_simp_transitivity_chain_no_trusted_arith() {
    reset_all_counters();
    let mut env = Environment::new();
    env.init_bool().unwrap();
    env.init_eq().unwrap();

    // Declare constants a, b, c : Bool
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    for name in &["a", "b", "c"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: bool_ty.clone(),
        })
        .unwrap();
    }

    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    // Simp lemma: a = b
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("ab_lemma"),
        level_params: vec![],
        type_: make_eq(bool_ty.clone(), a.clone(), b.clone()),
    })
    .unwrap();
    env.register_simp_lemma(
        Name::from_string("ab_lemma"),
        clean_kernel::env::SimpPriority::Default,
    );

    // Simp lemma: b = c
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("bc_lemma"),
        level_params: vec![],
        type_: make_eq(bool_ty.clone(), b.clone(), c.clone()),
    })
    .unwrap();
    env.register_simp_lemma(
        Name::from_string("bc_lemma"),
        clean_kernel::env::SimpPriority::Default,
    );

    // Goal: a = c  (should close via transitivity: a → b → c, then rfl)
    let goal = make_eq(bool_ty, a, c);
    let mut state = ProofState::new(env, goal);
    let axiom_before = axiom_snapshot();

    simp_default(&mut state).expect("simp should close a = c via transitivity chain");

    assert!(
        state.is_complete(),
        "simp should close the goal via transitivity a → b → c"
    );
    assert_no_trusted_fallback(&state, "simp transitivity chain", axiom_before);
}

/// Part of #2442: `simp_all` rewrites the goal target using the same simp proof
/// machinery as `simp`/`squeeze_simp`. When that target rewrite is
/// propositional, it must use the proof-carry replacement APIs instead of the
/// trusted fallback wrapper.
#[test]
#[serial]
fn test_simp_all_local_rewrite_no_trusted_arith() {
    reset_all_counters();
    let mut env = Environment::new();
    env.init_bool().unwrap();
    env.init_eq().unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("b"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Bool"), vec![]),
    })
    .unwrap();

    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let lhs = Expr::app(
        Expr::const_(Name::from_string("Bool.not"), vec![]),
        Expr::app(
            Expr::const_(Name::from_string("Bool.not"), vec![]),
            b.clone(),
        ),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("my_not_not"),
        level_params: vec![],
        type_: make_eq(bool_ty.clone(), lhs.clone(), b.clone()),
    })
    .unwrap();
    env.register_simp_lemma(
        Name::from_string("my_not_not"),
        clean_kernel::env::SimpPriority::Default,
    );

    let goal = make_eq(bool_ty, lhs, b);
    let mut state = ProofState::new(env, goal);
    let axiom_before = axiom_snapshot();

    simp_all(&mut state).expect("simp_all should rewrite the Bool goal via simp lemmas");

    assert!(
        state.is_complete(),
        "simp_all should close the rewritten reflexive goal"
    );
    assert_no_trusted_fallback(&state, "simp_all local rewrite", axiom_before);
    assert!(
        state.proof_term().is_some(),
        "simp_all must preserve proof_term() extraction after the target rewrite"
    );
    assert!(
        state.closed_proof().is_some(),
        "simp_all must preserve closed_proof() extraction after the target rewrite"
    );
}

/// Part of #2496: `simp_all` must treat local equality hypotheses as rewrite
/// lemmas for other hypotheses, not just environment constants.
#[test]
#[serial]
fn test_simp_all_uses_local_equality_hypothesis_for_other_hypotheses() {
    reset_all_counters();
    let env = setup_env_with_full_eq();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let goal = Expr::pi(
        BinderInfo::Default,
        make_eq_n(x.clone(), y.clone()),
        Expr::pi(BinderInfo::Default, make_p(x), make_p(y)),
    );
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "hxy").expect("intro should create the local rewrite hypothesis");
    intro(&mut state, "hpx").expect("intro should create the dependent hypothesis");
    let axiom_before = axiom_snapshot();

    simp_all(&mut state).expect("simp_all should rewrite hypotheses using local equality proofs");

    assert!(
        state.is_complete(),
        "simp_all should close the goal once hpx rewrites to the target"
    );
    assert_no_trusted_fallback(&state, "simp_all local hypothesis rewrite", axiom_before);
    assert!(
        state.proof_term().is_some(),
        "simp_all must preserve proof_term() extraction after local hypothesis rewrites"
    );
    assert!(
        state.closed_proof().is_some(),
        "simp_all must preserve closed_proof() extraction after local hypothesis rewrites"
    );
}

/// Part of #2442: when simp only makes beta/eta-definitional progress (no
/// simp lemma fires), `accumulated_proof` is `None` and the replacement
/// must use `replace_target_def_eq` instead of trustedArith.
#[test]
#[serial]
fn test_simp_beta_only_uses_def_eq_not_trusted_arith() {
    reset_all_counters();
    let env = setup_env_with_eq();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    // Goal: (fun x => x) a = a  — simp beta-reduces LHS, then rfl closes.
    let id_a = Expr::app(
        Expr::lam(BinderInfo::Default, a_ty.clone(), Expr::bvar(0)),
        a.clone(),
    );
    let goal = make_eq(a_ty, id_a, a);
    let mut state = ProofState::new(env, goal);
    let axiom_before = axiom_snapshot();

    simp_default(&mut state).expect("simp should beta-reduce and close via rfl");

    assert!(
        state.is_complete(),
        "simp should close the beta-reducible equality goal"
    );
    assert_no_trusted_fallback(&state, "simp beta-only", axiom_before);
    assert!(
        state.proof_term().is_some(),
        "simp beta-only must preserve proof_term() extraction"
    );
    assert!(
        state.closed_proof().is_some(),
        "simp beta-only must preserve closed_proof() extraction"
    );
}
