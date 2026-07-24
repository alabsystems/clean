// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_auto::oracle::OracleCandidate;
use clean_kernel::env::Declaration;
use clean_kernel::{BinderInfo, FVarId, Name};

fn setup_type_env() -> Environment {
    let mut env = Environment::new();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("add A");
    env
}

fn identity_goal() -> Expr {
    let a = Expr::const_(Name::from_string("A"), vec![]);
    Expr::arrow(a.clone(), a)
}

fn prop_chain_goal(name: &str, depth: usize) -> Expr {
    let prop = Expr::const_(Name::from_string(name), vec![]);
    let mut goal = prop.clone();
    for _ in 0..depth {
        goal = Expr::pi(BinderInfo::Default, prop.clone(), goal);
    }
    goal
}

#[test]
fn test_oracle_runner_proves_identity_script() {
    let env = setup_type_env();
    let goal = identity_goal();
    let runner = ElabOracleCandidateRunner;
    let candidate = OracleCandidate::new("intro x\nexact x", 0.9);

    let result = runner
        .try_candidate(&env, None, &goal, &candidate, Duration::from_secs(5))
        .expect("runner should not error")
        .expect("runner should verify the identity script");
    assert_eq!(result.proof_text, "intro x\nexact x");
    let inferred = result.infer_type(&env);
    assert!(
        inferred.is_ok(),
        "oracle proof should type-check, got: {:?}",
        inferred.err()
    );
}

#[test]
fn test_oracle_runner_resolves_exact_local_hypothesis() {
    let env = setup_type_env();
    let goal = Expr::const_(Name::from_string("A"), vec![]);
    let mut local_ctx = LocalContext::new();
    local_ctx.push_with_id(
        FVarId::new(7),
        Name::from_string("h"),
        goal.clone(),
        BinderInfo::Default,
    );
    let runner = ElabOracleCandidateRunner;
    let candidate = OracleCandidate::new("exact h", 0.9);

    let result = runner
        .try_candidate(
            &env,
            Some(&local_ctx),
            &goal,
            &candidate,
            Duration::from_secs(5),
        )
        .expect("runner should not error")
        .expect("runner should resolve the local hypothesis");
    assert_eq!(result.proof_text, "exact h");
    let inferred = result.infer_type(&env);
    assert!(
        inferred.is_ok(),
        "local-hypothesis oracle proof should type-check, got: {:?}",
        inferred.err()
    );
}

#[test]
fn test_oracle_runner_returns_none_when_candidate_fails() {
    let env = setup_type_env();
    let goal = identity_goal();
    let runner = ElabOracleCandidateRunner;
    assert!(
        runner
            .try_candidate(
                &env,
                None,
                &goal,
                &OracleCandidate::new("intro x\nunknown_tactic", 0.9),
                Duration::from_secs(5),
            )
            .expect("runner should not error")
            .is_none(),
        "failing candidate should return None so the engine can try the next one"
    );
}

#[test]
fn test_parse_strips_standalone_comments() {
    let script = "intro h\n-- this is a standalone comment\nexact h";
    let tactics = parse_tactic_script(script);
    assert_eq!(tactics, vec!["intro h", "exact h"]);
}

#[test]
fn test_parse_strips_inline_comments() {
    let script = "intro h -- introduce hypothesis\nexact h -- close the goal";
    let tactics = parse_tactic_script(script);
    assert_eq!(tactics, vec!["intro h", "exact h"]);
}

#[test]
fn test_parse_strips_multiple_comment_lines() {
    let script = "-- proof sketch\nintro h\n-- TODO: automate this\nassumption\n-- done";
    let tactics = parse_tactic_script(script);
    assert_eq!(tactics, vec!["intro h", "assumption"]);
}

#[test]
fn test_parse_strips_comment_after_semicolon() {
    let script = "intro h; -- now close\nexact h";
    let tactics = parse_tactic_script(script);
    assert_eq!(tactics, vec!["intro h", "exact h"]);
}

#[test]
fn test_oracle_runner_succeeds_with_commented_script() {
    let env = setup_type_env();
    let goal = identity_goal();
    let runner = ElabOracleCandidateRunner;
    let candidate = OracleCandidate::new("intro x -- bind\n-- now close\nexact x -- done", 0.9);

    let result = runner
        .try_candidate(&env, None, &goal, &candidate, Duration::from_secs(5))
        .expect("runner should not error")
        .expect("commented script should still verify");
    let inferred = result.infer_type(&env);
    assert!(
        inferred.is_ok(),
        "commented oracle proof should type-check, got: {:?}",
        inferred.err()
    );
}

#[test]
fn test_parse_strips_inline_block_comments() {
    let script = "intro h /- bind -/ ; exact h";
    let tactics = parse_tactic_script(script);
    assert_eq!(tactics, vec!["intro h", "exact h"]);
}

#[test]
fn test_parse_strips_multiline_block_comments() {
    let script = "intro h\n/- this spans\nmultiple lines -/\nexact h";
    let tactics = parse_tactic_script(script);
    assert_eq!(tactics, vec!["intro h", "exact h"]);
}

#[test]
fn test_oracle_runner_succeeds_with_block_commented_script() {
    let env = setup_type_env();
    let goal = identity_goal();
    let runner = ElabOracleCandidateRunner;
    let candidate = OracleCandidate::new("intro x /- bind -/ \nexact x /- done -/", 0.9);

    let result = runner
        .try_candidate(&env, None, &goal, &candidate, Duration::from_secs(5))
        .expect("runner should not error")
        .expect("block-commented script should still verify");
    let inferred = result.infer_type(&env);
    assert!(
        inferred.is_ok(),
        "block-commented oracle proof should type-check, got: {:?}",
        inferred.err()
    );
}

/// Regression: script_runner preserves upstream `ElabError` structurally.
#[test]
fn test_script_runner_preserves_upstream_elab_error() {
    let env = setup_type_env();
    let goal = Expr::const_(Name::from_string("A"), vec![]);
    let mut ps = elab_tactic::ProofState::new(env.clone(), goal);
    let err = execute_simple_tactic(&mut ps, "exact nonexistent_term", &env)
        .expect_err("exact with unknown ident should fail");
    assert!(
        matches!(&err, elab_tactic::TacticError::UpstreamElabError { source }
            if matches!(source.as_ref(), crate::ElabError::UnknownIdent(..))),
        "expected UpstreamElabError(UnknownIdent), got: {err:?}"
    );
    assert!(err.to_string().contains("Unknown identifier"));
}

#[test]
fn test_execute_simple_tactic_set_option_max_depth_controls_tauto() {
    let mut env = Environment::new();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("add P");

    let goal = prop_chain_goal("P", 20);

    let mut default_state = elab_tactic::ProofState::new(env.clone(), goal.clone());
    let default_err = execute_simple_tactic(&mut default_state, "tauto", &env)
        .expect_err("default tauto depth should be exhausted on a 20-step implication chain");
    assert!(
        matches!(default_err, elab_tactic::TacticError::NoProgress { .. }),
        "expected depth-limited tauto failure, got {default_err:?}"
    );

    let mut configured_state = elab_tactic::ProofState::new(env.clone(), goal);
    execute_simple_tactic(&mut configured_state, "set_option max_depth 21", &env)
        .expect("set_option max_depth should parse and store");
    execute_simple_tactic(&mut configured_state, "tauto", &env)
        .expect("raised max_depth should let tauto finish the implication chain");
    assert!(
        configured_state.is_complete(),
        "tauto should close the goal after the depth override"
    );
}

#[test]
fn test_execute_simple_tactic_dispatches_cert_mathverse() {
    let mut env = Environment::new();
    env.init_cast_simp_lemmas()
        .expect("cast simp lemmas should initialize");
    env.init_true_false()
        .expect("true/false declarations should initialize");
    let false_ty = Expr::const_(Name::from_string("False"), vec![]);
    let h_ty = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.le"), vec![]),
            Expr::nat_lit(5),
        ),
        Expr::nat_lit(3),
    );
    let mut ps = elab_tactic::ProofState::with_context(
        env.clone(),
        false_ty,
        vec![elab_tactic::LocalDecl {
            fvar: FVarId::new(0),
            name: "h".into(),
            ty: h_ty,
            value: None,
        }],
    );

    execute_simple_tactic(&mut ps, "cert_mathverse", &env)
        .expect("script runner should dispatch cert_mathverse");

    assert!(
        ps.is_complete(),
        "cert_mathverse should close the contradiction"
    );
}

#[test]
fn test_execute_simple_tactic_dispatches_cert_simp() {
    let mut env = Environment::with_prelude();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("m"),
        level_params: vec![],
        type_: nat.clone(),
    })
    .expect("m should register");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("n"),
        level_params: vec![],
        type_: nat,
    })
    .expect("n should register");
    env.add_decl(Declaration::Definition {
        name: Name::from_string("Cert.PB.checkBound"),
        level_params: vec![],
        type_: Expr::prop(),
        value: Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Nat.le"), vec![]),
                Expr::const_(Name::from_string("m"), vec![]),
            ),
            Expr::const_(Name::from_string("n"), vec![]),
        ),
        is_reducible: true,
    })
    .expect("certificate wrapper should register");
    let mut ps = elab_tactic::ProofState::with_context(
        env.clone(),
        Expr::const_(Name::from_string("False"), vec![]),
        vec![elab_tactic::LocalDecl {
            fvar: FVarId::new(0),
            name: "h".into(),
            ty: Expr::const_(Name::from_string("Cert.PB.checkBound"), vec![]),
            value: None,
        }],
    );

    execute_simple_tactic(&mut ps, "cert_simp", &env)
        .expect("script runner should dispatch cert_simp");

    let h = ps
        .current_goal()
        .expect("cert_simp should simplify without closing this symbolic False goal")
        .local_ctx
        .iter()
        .find(|decl| decl.name == "h")
        .expect("hypothesis should remain after simplification");
    assert_ne!(
        h.ty,
        Expr::const_(Name::from_string("Cert.PB.checkBound"), vec![]),
        "cert_simp should unfold the certificate wrapper"
    );
}

#[test]
fn test_execute_simple_tactic_clear_removes_hypothesis() {
    let env = setup_type_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut ps = elab_tactic::ProofState::with_context(
        env.clone(),
        a.clone(),
        vec![elab_tactic::LocalDecl {
            fvar: FVarId::new(0),
            name: "h".into(),
            ty: a,
            value: None,
        }],
    );

    execute_simple_tactic(&mut ps, "clear h", &env).expect("script runner should dispatch clear");

    let goal = ps.current_goal().expect("goal should remain after clear");
    assert!(
        goal.local_ctx.iter().all(|d| d.name != "h"),
        "clear should remove hypothesis h from the local context"
    );
}

#[test]
fn test_execute_simple_tactic_rename_renames_hypothesis() {
    let env = setup_type_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut ps = elab_tactic::ProofState::with_context(
        env.clone(),
        a.clone(),
        vec![elab_tactic::LocalDecl {
            fvar: FVarId::new(0),
            name: "h".into(),
            ty: a,
            value: None,
        }],
    );

    execute_simple_tactic(&mut ps, "rename h g", &env)
        .expect("script runner should dispatch rename");

    let goal = ps.current_goal().expect("goal should remain after rename");
    assert!(
        goal.local_ctx.iter().any(|d| d.name == "g"),
        "rename should introduce the new hypothesis name g"
    );
    assert!(
        goal.local_ctx.iter().all(|d| d.name != "h"),
        "rename should retire the old hypothesis name h"
    );
}

#[test]
fn test_execute_simple_tactic_clear_missing_arg_errors() {
    let env = setup_type_env();
    let mut ps =
        elab_tactic::ProofState::new(env.clone(), Expr::const_(Name::from_string("A"), vec![]));
    let err = execute_simple_tactic(&mut ps, "clear", &env)
        .expect_err("clear without a hypothesis name should error");
    assert!(
        matches!(err, elab_tactic::TacticError::MissingArgument { .. }),
        "expected MissingArgument, got {err:?}"
    );
}

/// Wiring regression: the newly dispatched tactics route to their real
/// implementations rather than falling through to `UnknownIdent`. Each is run
/// against a goal that triggers a *domain* error (NoProgress / GoalMismatch /
/// EnvironmentMissing), which still proves the dispatch arm exists.
#[test]
fn test_execute_simple_tactic_wires_domain_tactics() {
    let env = setup_type_env();
    let goal = Expr::const_(Name::from_string("A"), vec![]);
    for tactic in [
        "push_neg",
        "contrapose",
        "field_simp",
        "by_contra",
        "left",
        "right",
        "exfalso",
        "contradiction",
        "itauto",
        "swap",
        "rotate_left",
        "rotate_right",
        "subst_vars",
    ] {
        let mut ps = elab_tactic::ProofState::new(env.clone(), goal.clone());
        let outcome = execute_simple_tactic(&mut ps, tactic, &env);
        if let Err(err) = outcome {
            assert!(
                !matches!(err, elab_tactic::TacticError::UnknownIdent(_)),
                "tactic `{tactic}` should be wired into the dispatcher, got {err:?}"
            );
        }
    }
}

#[test]
fn test_execute_simple_tactic_swap_reorders_goals() {
    let env = setup_type_env();
    let goal_a = Expr::const_(Name::from_string("A"), vec![]);
    let goal_b = Expr::type_();
    let mut ps = elab_tactic::ProofState::new(env.clone(), goal_a.clone());
    let meta_id = ps.metas.fresh(goal_b.clone());
    ps.goals.push_back(elab_tactic::Goal {
        meta_id,
        target: goal_b.clone(),
        local_ctx: vec![],
        tag: None,
    });

    execute_simple_tactic(&mut ps, "swap", &env).expect("swap should reorder two goals");

    assert_eq!(
        ps.current_goal().expect("a goal should remain").target,
        goal_b,
        "swap should move the second goal to the front"
    );
}

#[test]
fn test_execute_simple_tactic_subst_missing_arg_errors() {
    let env = setup_type_env();
    let mut ps =
        elab_tactic::ProofState::new(env.clone(), Expr::const_(Name::from_string("A"), vec![]));
    let err = execute_simple_tactic(&mut ps, "subst", &env)
        .expect_err("subst without a hypothesis name should error");
    assert!(
        matches!(err, elab_tactic::TacticError::MissingArgument { .. }),
        "expected MissingArgument, got {err:?}"
    );
}

#[test]
fn test_execute_simple_tactic_rotate_left_rejects_non_numeric_count() {
    let env = setup_type_env();
    let mut ps =
        elab_tactic::ProofState::new(env.clone(), Expr::const_(Name::from_string("A"), vec![]));
    let err = execute_simple_tactic(&mut ps, "rotate_left abc", &env)
        .expect_err("rotate_left with a non-numeric count should error");
    assert!(
        matches!(err, elab_tactic::TacticError::InvalidTarget { .. }),
        "expected InvalidTarget, got {err:?}"
    );
}

/// Wiring regression for the algebra/closure family: `ac_rfl`, `positivity`,
/// `gcongr`, `cc`, `norm_cast`, `abel`, `group`, `solve_by_elim` route to their
/// real implementations rather than falling through to `UnknownIdent`. Each is
/// run against a goal that triggers a *domain* outcome (Ok / NoProgress /
/// GoalMismatch / NoGoals), which still proves the dispatch arm exists.
#[test]
fn test_execute_simple_tactic_wires_algebra_tactics() {
    let env = setup_type_env();
    let goal = Expr::const_(Name::from_string("A"), vec![]);
    for tactic in [
        "ac_rfl",
        "positivity",
        "gcongr",
        "cc",
        "norm_cast",
        "abel",
        "group",
        "solve_by_elim",
    ] {
        let mut ps = elab_tactic::ProofState::new(env.clone(), goal.clone());
        let outcome = execute_simple_tactic(&mut ps, tactic, &env);
        if let Err(err) = outcome {
            assert!(
                !matches!(err, elab_tactic::TacticError::UnknownIdent(_)),
                "tactic `{tactic}` should be wired into the dispatcher, got {err:?}"
            );
        }
    }
}

#[test]
fn test_execute_simple_tactic_solve_by_elim_rejects_non_numeric_depth() {
    let env = setup_type_env();
    let mut ps =
        elab_tactic::ProofState::new(env.clone(), Expr::const_(Name::from_string("A"), vec![]));
    let err = execute_simple_tactic(&mut ps, "solve_by_elim abc", &env)
        .expect_err("solve_by_elim with a non-numeric depth should error");
    assert!(
        matches!(err, elab_tactic::TacticError::InvalidTarget { .. }),
        "expected InvalidTarget, got {err:?}"
    );
}

/// Soundness: `solve_by_elim` closes a goal by elaborating a type-checked
/// proof from a local hypothesis. After `intro x` the goal `A → A` reduces to
/// `A` with `x : A` in context, and `solve_by_elim` must discharge it via
/// `assumption`, leaving no open goals.
#[test]
fn test_execute_simple_tactic_solve_by_elim_closes_via_assumption() {
    let env = setup_type_env();
    let mut ps = elab_tactic::ProofState::new(env.clone(), identity_goal());
    execute_simple_tactic(&mut ps, "intro x", &env).expect("intro x should succeed");
    execute_simple_tactic(&mut ps, "solve_by_elim", &env)
        .expect("solve_by_elim should close the goal from the local hypothesis");
    assert!(
        ps.goals.is_empty(),
        "solve_by_elim should leave no open goals, found {}",
        ps.goals.len()
    );
}

/// Wiring regression for the structural family: `delta`, `revert`, `unfold`,
/// `fin_cases`, `ext` route to their real implementations rather than
/// `UnknownIdent`. Each is run against a goal that triggers a *domain* outcome
/// (HypothesisNotFound / EnvironmentMissing / GoalMismatch / Ok), which still
/// proves the dispatch arm exists.
#[test]
fn test_execute_simple_tactic_wires_structural_tactics() {
    let env = setup_type_env();
    let goal = Expr::const_(Name::from_string("A"), vec![]);
    for tactic in ["delta", "revert h", "unfold foo", "fin_cases h", "ext x"] {
        let mut ps = elab_tactic::ProofState::new(env.clone(), goal.clone());
        let outcome = execute_simple_tactic(&mut ps, tactic, &env);
        if let Err(err) = outcome {
            assert!(
                !matches!(err, elab_tactic::TacticError::UnknownIdent(_)),
                "tactic `{tactic}` should be wired into the dispatcher, got {err:?}"
            );
        }
    }
}

#[test]
fn test_execute_simple_tactic_revert_missing_arg_errors() {
    let env = setup_type_env();
    let mut ps =
        elab_tactic::ProofState::new(env.clone(), Expr::const_(Name::from_string("A"), vec![]));
    let err = execute_simple_tactic(&mut ps, "revert", &env)
        .expect_err("revert without a hypothesis name should error");
    assert!(
        matches!(err, elab_tactic::TacticError::MissingArgument { .. }),
        "expected MissingArgument, got {err:?}"
    );
}

#[test]
fn test_execute_simple_tactic_unfold_missing_arg_errors() {
    let env = setup_type_env();
    let mut ps =
        elab_tactic::ProofState::new(env.clone(), Expr::const_(Name::from_string("A"), vec![]));
    let err = execute_simple_tactic(&mut ps, "unfold", &env)
        .expect_err("unfold without a definition name should error");
    assert!(
        matches!(err, elab_tactic::TacticError::MissingArgument { .. }),
        "expected MissingArgument, got {err:?}"
    );
}

/// Wiring regression for the `at <hyp>` target forms: `push_neg at h`,
/// `norm_num at h`, `unfold foo at h` route to the hypothesis-targeted
/// implementations rather than `UnknownIdent`. Against a goal with no matching
/// hypothesis they return `HypothesisNotFound` / `UnfoldFailed`, which still
/// proves the `at` branch is taken.
#[test]
fn test_execute_simple_tactic_wires_at_target_tactics() {
    let env = setup_type_env();
    let goal = Expr::const_(Name::from_string("A"), vec![]);
    for tactic in ["push_neg at h", "norm_num at h", "unfold foo at h"] {
        let mut ps = elab_tactic::ProofState::new(env.clone(), goal.clone());
        let outcome = execute_simple_tactic(&mut ps, tactic, &env);
        if let Err(err) = outcome {
            assert!(
                !matches!(err, elab_tactic::TacticError::UnknownIdent(_)),
                "tactic `{tactic}` should be wired into the dispatcher, got {err:?}"
            );
        }
    }
}

/// Routing: `norm_num at <hyp>` dispatches to the hypothesis-targeted variant,
/// not the goal-directed `norm_num`. With no such hypothesis the at-variant
/// reports `HypothesisNotFound`, distinguishing it from the bare form.
#[test]
fn test_execute_simple_tactic_norm_num_at_routes_to_hypothesis() {
    let env = setup_type_env();
    let mut ps =
        elab_tactic::ProofState::new(env.clone(), Expr::const_(Name::from_string("A"), vec![]));
    let err = execute_simple_tactic(&mut ps, "norm_num at missing", &env)
        .expect_err("norm_num at a missing hypothesis should error");
    assert!(
        matches!(err, elab_tactic::TacticError::HypothesisNotFound(_)),
        "expected HypothesisNotFound from the at-variant, got {err:?}"
    );
}

/// Wiring regression for the automation family: `grind` and `blast` route to
/// their real implementations rather than `UnknownIdent`. Against a bare goal
/// with no usable hypotheses they make no progress (`NoProgress`), which still
/// proves the dispatch arm exists.
#[test]
fn test_execute_simple_tactic_wires_automation_tactics() {
    let env = setup_type_env();
    let goal = Expr::const_(Name::from_string("A"), vec![]);
    for tactic in ["grind", "blast"] {
        let mut ps = elab_tactic::ProofState::new(env.clone(), goal.clone());
        let outcome = execute_simple_tactic(&mut ps, tactic, &env);
        if let Err(err) = outcome {
            assert!(
                !matches!(err, elab_tactic::TacticError::UnknownIdent(_)),
                "tactic `{tactic}` should be wired into the dispatcher, got {err:?}"
            );
        }
    }
}

/// Soundness: `grind` closes a goal only by delegating to checked sub-tactics.
/// After `intro x` the goal `A → A` reduces to `A` with `x : A`, and `grind`
/// must discharge it via its `assumption` closer, leaving no open goals.
#[test]
fn test_execute_simple_tactic_grind_closes_via_assumption() {
    let env = setup_type_env();
    let mut ps = elab_tactic::ProofState::new(env.clone(), identity_goal());
    execute_simple_tactic(&mut ps, "intro x", &env).expect("intro x should succeed");
    execute_simple_tactic(&mut ps, "grind", &env)
        .expect("grind should close the goal from the local hypothesis");
    assert!(
        ps.goals.is_empty(),
        "grind should leave no open goals, found {}",
        ps.goals.len()
    );
}

/// Wiring regression for the inductive/convert family: `injection`,
/// `discriminate`, `interval_cases`, `convert` route to their real
/// implementations rather than `UnknownIdent`. Each is run against a goal that
/// triggers a *domain* outcome (HypothesisNotFound / GoalMismatch / etc.),
/// which still proves the dispatch arm exists.
#[test]
fn test_execute_simple_tactic_wires_inductive_tactics() {
    let env = setup_type_env();
    let goal = Expr::const_(Name::from_string("A"), vec![]);
    for tactic in [
        "injection h",
        "discriminate h",
        "interval_cases x",
        "convert h",
    ] {
        let mut ps = elab_tactic::ProofState::new(env.clone(), goal.clone());
        let outcome = execute_simple_tactic(&mut ps, tactic, &env);
        if let Err(err) = outcome {
            assert!(
                !matches!(err, elab_tactic::TacticError::UnknownIdent(_)),
                "tactic `{tactic}` should be wired into the dispatcher, got {err:?}"
            );
        }
    }
}

#[test]
fn test_execute_simple_tactic_injection_missing_arg_errors() {
    let env = setup_type_env();
    let mut ps =
        elab_tactic::ProofState::new(env.clone(), Expr::const_(Name::from_string("A"), vec![]));
    let err = execute_simple_tactic(&mut ps, "injection", &env)
        .expect_err("injection without a hypothesis name should error");
    assert!(
        matches!(err, elab_tactic::TacticError::MissingArgument { .. }),
        "expected MissingArgument, got {err:?}"
    );
}

#[test]
fn test_execute_simple_tactic_convert_missing_arg_errors() {
    let env = setup_type_env();
    let mut ps =
        elab_tactic::ProofState::new(env.clone(), Expr::const_(Name::from_string("A"), vec![]));
    let err = execute_simple_tactic(&mut ps, "convert", &env)
        .expect_err("convert without an expression should error");
    assert!(
        matches!(err, elab_tactic::TacticError::MissingArgument { .. }),
        "expected MissingArgument, got {err:?}"
    );
}

/// Soundness: `revert` is the inverse of `intro`. After `intro x` the goal
/// `A → A` becomes `A` with `x : A`; `revert x` must regeneralize the
/// hypothesis, restoring the original `A → A` goal via a type-checked proof.
#[test]
fn test_execute_simple_tactic_revert_roundtrips_intro() {
    let env = setup_type_env();
    let mut ps = elab_tactic::ProofState::new(env.clone(), identity_goal());
    execute_simple_tactic(&mut ps, "intro x", &env).expect("intro x should succeed");
    execute_simple_tactic(&mut ps, "revert x", &env)
        .expect("revert x should regeneralize the hypothesis");
    assert_eq!(
        ps.current_goal().expect("a goal should remain").target,
        identity_goal(),
        "revert should restore the original A → A goal"
    );
}
