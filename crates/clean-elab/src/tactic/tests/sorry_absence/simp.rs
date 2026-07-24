// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
#[serial]
fn test_simp_no_sorry_on_beta_reduction() {
    // Goal: (λ x : A => x) a = a — simp should close via beta + rfl, no sorry
    reset_all_counters();
    let env = setup_env_with_eq();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    // (λ x : A => x) a
    let identity = Expr::lam(BinderInfo::Default, a_ty.clone(), Expr::bvar(0));
    let lhs = Expr::app(identity, a.clone());

    let goal = make_eq(a_ty, lhs, a);
    let mut state = ProofState::new(env, goal);

    let before = sorry_count();
    let ax = axiom_snapshot();
    simp_default(&mut state).expect("simp should prove (λ x => x) a = a");
    let after = sorry_count();

    assert_eq!(
        before,
        after,
        "SORRY LEAK: simp used {} sorry (expected 0)",
        after - before
    );
    assert_no_trusted_axiom_usage("simp", "beta-reduction", ax);
}

#[test]
#[serial]
fn test_simp_no_sorry_on_registered_lemma() {
    reset_all_counters();
    let (env, goal) = setup_env_with_simp_add_lemma();
    let mut state = ProofState::new(env, goal);

    let before = sorry_count();
    let ax = axiom_snapshot();
    let result = simp_default(&mut state);
    let sorry_used = sorry_count() - before;
    let arith_used = arith_proof_count() - ax.0;
    let ay_used = ay_proof_count() - ax.1;

    match result {
        Ok(()) => {
            assert_eq!(
                sorry_used, 0,
                "SORRY LEAK: simp used {sorry_used} sorry with lemma"
            );
            assert_no_trusted_axiom_usage("simp (registered lemma)", "add_one_one = two", ax);
        }
        Err(e) => {
            assert_all_counters_zero_on_failure(
                "simp (registered lemma)",
                "errored",
                sorry_used,
                arith_used,
                ay_used,
            );
            eprintln!("KNOWN GAP: simp error with registered lemma: {e:?} (Part of #1144)");
        }
    }
}

#[test]
#[serial]
fn test_simp_no_sorry_on_hypothesis_rewrite() {
    // Setup: hypothesis h : P, goal : P
    // Simp should either close via assumption or leave the goal unchanged.
    // This specifically tests that simp_at_hyp doesn't produce sorry when
    // processing hypotheses.
    reset_all_counters();
    let env = setup_env_with_and_or();
    let p = Expr::const_(Name::from_string("P"), vec![]);

    let mut state = ProofState::with_context(
        env,
        p.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: p,
            value: None,
        }],
    );

    let before = sorry_count();
    let ax = axiom_snapshot();
    // simp_default processes both hypotheses and goal
    let result = simp_default(&mut state);
    let sorry_used = sorry_count() - before;

    // Whether simp succeeds or reports no progress, it must not generate sorry.
    match &result {
        Ok(()) => {
            assert_eq!(
                sorry_used, 0,
                "SORRY LEAK: simp used {sorry_used} sorry on hypothesis"
            );
            assert_no_trusted_axiom_usage("simp (hyp rewrite)", "P from h:P", ax);
        }
        Err(e) => {
            assert_eq!(
                sorry_used, 0,
                "simp errored ({e}) AND used {sorry_used} sorry terms"
            );
        }
    }
}
