// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source-level observations of the real declaration registrar, including
//! partial/invalid proofs. An observed goal is not a declaration pass.

use super::core::{Goal, LocalDecl};
use super::{TacticGoalCapture, TacticGoalObservation, TacticGoalObservationUnavailable};
use crate::module_driver::{
    elaborate_decls, module_elaboration_lock, module_environment, module_file_context,
    parse_module, DriverOptions, EnvironmentSetup, FailureIsolation, ImportHandling, ModuleReport,
    VerdictKind,
};
use clean_kernel::{Environment, ExprKind, Name, TypeChecker};
use std::path::Path;

fn run(source: &str, observe: bool) -> (ModuleReport, Environment, Vec<TacticGoalObservation>) {
    let _lock = module_elaboration_lock();
    let path = Path::new("ObservedGoals.lean");
    let mut env = module_environment(EnvironmentSetup::default()).expect("normal module prelude");
    let parsed = parse_module(path, source).1.expect("source parses");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut file = module_file_context(path);
    let capture = TacticGoalCapture::default();
    if observe {
        file.set_tactic_goal_capture(Some(capture.clone()));
    }
    let report = elaborate_decls(
        &mut env,
        &parsed.decls,
        source,
        &mut file,
        DriverOptions {
            imports: ImportHandling::Preloaded,
            isolation: FailureIsolation::Rollback,
            ..DriverOptions::default()
        },
        &mut (),
    );
    (
        report,
        env,
        capture.take().expect("unpoisoned actual collector"),
    )
}

fn local<'a>(goal: &'a Goal, name: &str) -> &'a LocalDecl {
    goal.local_ctx
        .iter()
        .find(|d| d.name.to_string() == name)
        .unwrap_or_else(|| panic!("missing {name}: {:?}", goal.local_ctx))
}

fn at<'a>(
    observations: &'a [TacticGoalObservation],
    source: &str,
    tactic: &str,
) -> &'a TacticGoalObservation {
    let offset = source.find(tactic).expect("tactic is in source");
    observations
        .iter()
        .rev()
        .find(|o| o.tactic_range.start == offset)
        .unwrap_or_else(|| panic!("no actual state at {tactic}: {observations:?}"))
}

fn checked_root(env: &Environment, name: &str) {
    let name = Name::from_string(name);
    let info = env.get_const(&name).expect("registered public root");
    assert_eq!(info.kind, clean_kernel::env::ConstantKind::Theorem);
    assert_eq!(
        env.declaration_verification(&name),
        Some(clean_kernel::env::DeclarationVerification::FullKernelCheck)
    );
    let body = info.value.as_ref().expect("actual theorem body");
    let tc = TypeChecker::new(env);
    assert!(tc
        .infer_sort(&info.type_)
        .expect("full public type")
        .is_zero());
    let inferred = tc
        .infer_type_full(body)
        .expect("full public body inference");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "public inferred/stored types agree"
    );
    tc.check_type(body, &info.type_).expect("public body check");
    assert!(
        !body.has_fvar_quick() && !body.has_loose_bvars_quick(),
        "closed public body"
    );
    assert!(
        !body.collect_constants().contains(&name),
        "no self-reference"
    );
    assert!(env.axiom_deps(&name).expect("stored closure").is_empty());
    assert!(crate::print_axioms::collect_axioms(env, &name)
        .expect("computed closure")
        .is_empty());
}

#[test]
fn normal_observation_preserves_intro_identity_and_default_verdict() {
    let source =
        "theorem observed_intro (p q : Prop) (hp : p) : q → p := by\n  intro hq\n  exact hp\n";
    let (default_report, default_env, default_views) = run(source, false);
    let (report, env, observations) = run(source, true);
    assert_eq!(default_report.verdicts, report.verdicts);
    assert!(
        report
            .verdicts
            .iter()
            .all(|v| v.kind == VerdictKind::Passed),
        "{report:?}"
    );
    assert!(default_views.is_empty(), "observation is opt in");
    assert_eq!(
        env.get_const(&Name::from_string("observed_intro"))
            .unwrap()
            .value,
        default_env
            .get_const(&Name::from_string("observed_intro"))
            .unwrap()
            .value
    );
    checked_root(&env, "observed_intro");
    let observation = at(&observations, source, "intro hq");
    assert_eq!(
        observation.tactic_range.end,
        source.find("intro hq").unwrap() + "intro hq".len(),
        "actual Named argument extent belongs to the observation only"
    );
    let before = &observation.before.as_ref().expect("typed before").goals[0];
    let after = &observation
        .after
        .as_ref()
        .unwrap()
        .as_ref()
        .expect("typed after")
        .goals[0];
    assert!(matches!(before.target.kind(), ExprKind::Pi(..)));
    let p = local(before, "p");
    let q = local(before, "q");
    for original in &before.local_ctx {
        let retained = local(after, &original.name.to_string());
        assert_eq!(retained.fvar, original.fvar);
        assert_eq!(retained.ty, original.ty);
    }
    assert_eq!(after.target, clean_kernel::Expr::fvar(p.fvar));
    assert_eq!(local(after, "hq").ty, clean_kernel::Expr::fvar(q.fvar));
    assert!(before
        .local_ctx
        .iter()
        .all(|d| d.fvar != local(after, "hq").fvar));
    assert!(at(&observations, source, "exact hp")
        .after
        .as_ref()
        .unwrap()
        .as_ref()
        .unwrap()
        .goals
        .is_empty());
}

#[test]
fn normal_observation_retains_example_and_dependent_binders_on_partial_proofs() {
    for source in [
        "example (n : Nat) : n = n := by\n  skip\n",
        "theorem dependent_view (α : Type) (x : α) (h : x = x) : x = x := by\n  skip\n",
    ] {
        let (report, _, observations) = run(source, true);
        assert!(
            report.verdicts.iter().any(|v| v.kind.is_failure()),
            "partial proof: {report:?}"
        );
        let view = at(&observations, source, "skip")
            .before
            .as_ref()
            .expect("typed partial view");
        let goal = &view.goals[0];
        assert!(
            !view.rendered_targets[0].contains("#F"),
            "{:?}",
            view.rendered_targets
        );
        if source.starts_with("example") {
            assert_eq!(goal.local_ctx.len(), 1);
            assert!(super::hypothesis::collect_fvars(&goal.target).contains(&local(goal, "n").fvar));
        } else {
            assert_eq!(
                local(goal, "x").ty,
                clean_kernel::Expr::fvar(local(goal, "α").fvar)
            );
            assert!(super::hypothesis::collect_fvars(&local(goal, "h").ty)
                .contains(&local(goal, "x").fvar));
            assert_eq!(local(goal, "h").ty, goal.target);
        }
    }
}

#[test]
fn normal_observation_keeps_local_instances_and_have_target() {
    let source = "theorem observed_instance (α : Type) [inst : Inhabited α] (h : True) : True := by\n  have x : α := default\n  exact h\n";
    let (report, env, observations) = run(source, true);
    assert!(
        report
            .verdicts
            .iter()
            .all(|v| v.kind == VerdictKind::Passed),
        "{report:?}"
    );
    checked_root(&env, "observed_instance");
    let before = &at(&observations, source, "have x")
        .before
        .as_ref()
        .unwrap()
        .goals[0];
    let after = &at(&observations, source, "exact h")
        .before
        .as_ref()
        .unwrap()
        .goals[0];
    assert_eq!(local(before, "inst").fvar, local(after, "inst").fvar);
    assert_eq!(
        local(after, "x").ty,
        clean_kernel::Expr::fvar(local(before, "α").fvar)
    );
    assert_eq!(before.target, after.target);
}

#[test]
fn normal_observation_disambiguates_shadowed_fvars() {
    let source = "theorem observed_shadow (n : Nat) (h : n = n) (n : Nat) : n = n := by\n  skip\n";
    let (_, _, observations) = run(source, true);
    let view = at(&observations, source, "skip").before.as_ref().unwrap();
    let goal = &view.goals[0];
    let ns: Vec<_> = goal
        .local_ctx
        .iter()
        .filter(|d| d.name.to_string() == "n")
        .collect();
    assert_eq!(ns.len(), 2);
    assert_ne!(ns[0].fvar, ns[1].fvar);
    assert!(super::hypothesis::collect_fvars(&local(goal, "h").ty).contains(&ns[0].fvar));
    assert!(!super::hypothesis::collect_fvars(&local(goal, "h").ty).contains(&ns[1].fvar));
    assert!(super::hypothesis::collect_fvars(&goal.target).contains(&ns[1].fvar));
    assert!(
        view.rendered_targets[0].contains("h : n✝ = n✝"),
        "{:?}",
        view.rendered_targets
    );
    assert!(view.rendered_targets[0].ends_with("⊢ n = n"));
}

#[test]
fn normal_observation_refuses_invalid_unused_header_even_after_closed_goal() {
    let (positive, env, positive_views) = run(
        "theorem valid_header (n : Nat) : True := by\n  trivial\n",
        true,
    );
    assert!(
        positive
            .verdicts
            .iter()
            .all(|v| v.kind == VerdictKind::Passed),
        "{positive:?}"
    );
    checked_root(&env, "valid_header");
    assert!(positive_views.iter().any(|v| v
        .after
        .as_ref()
        .is_some_and(|a| a.as_ref().is_ok_and(|g| g.goals.is_empty()))));
    let (negative, env, views) = run(
        "theorem invalid_header (n : 0) : True := by\n  trivial\n",
        true,
    );
    assert!(
        negative.verdicts.iter().any(|v| v.kind.is_failure()),
        "{negative:?}"
    );
    assert!(env
        .get_const(&Name::from_string("invalid_header"))
        .is_none());
    assert!(
        views
            .iter()
            .all(|v| v.before.is_err() && v.after.as_ref().is_none_or(Result::is_err)),
        "{views:?}"
    );
}

#[test]
fn normal_observation_keeps_sorry_debt_and_failed_exact_unavailable() {
    let source = "example (n : Nat) : n = n := by\n  sorry\n";
    let (_, _, observations) = run(source, true);
    let sorry = at(&observations, source, "sorry");
    assert_eq!(sorry.before.as_ref().unwrap().goals[0].local_ctx.len(), 1);
    assert!(
        matches!(
            sorry.after.as_ref().unwrap(),
            Err(TacticGoalObservationUnavailable::Trusted(_))
        ),
        "{sorry:?}"
    );
    let source = "theorem invalid_exact (n : Nat) : True := by\n  exact n\n";
    let (report, env, observations) = run(source, true);
    assert!(report.verdicts.iter().any(|v| v.kind.is_failure()));
    assert!(env.get_const(&Name::from_string("invalid_exact")).is_none());
    let failed = at(&observations, source, "exact n");
    assert!(failed.before.is_ok());
    assert!(
        failed.after.is_none(),
        "failed tactics cannot supply successful after states"
    );
}

#[test]
fn normal_observation_uses_current_namespace_prefix_and_resets_on_fork() {
    let source = "namespace Observed\ndef pred (n : Nat) : Prop := n = n\ntheorem prefix_view (n : Nat) : pred n := by\n  rfl\nend Observed\n";
    let (report, env, observations) = run(source, true);
    assert!(
        report
            .verdicts
            .iter()
            .all(|v| v.kind == VerdictKind::Passed),
        "{report:?}"
    );
    checked_root(&env, "Observed.prefix_view");
    assert!(at(&observations, source, "rfl").before.is_ok());
    let mut file = crate::FileContext::new();
    file.set_tactic_goal_capture(Some(TacticGoalCapture::default()));
    assert!(file.clone().tactic_goal_capture().is_some());
    assert!(file.fork_run().tactic_goal_capture().is_none());
}

#[test]
fn normal_observation_reaches_by_tactic_inside_compound_proof_term() {
    let source =
        "theorem observed_compound (p q : Prop) (hp : p) : q → p := (by\n  intro hq\n  exact hp)\n";
    let (report, env, observations) = run(source, true);
    assert!(
        report
            .verdicts
            .iter()
            .all(|v| v.kind == VerdictKind::Passed),
        "{report:?}"
    );
    checked_root(&env, "observed_compound");
    let after = at(&observations, source, "intro hq")
        .after
        .as_ref()
        .unwrap()
        .as_ref()
        .unwrap();
    assert_eq!(
        after.goals[0].target,
        clean_kernel::Expr::fvar(local(&after.goals[0], "p").fvar)
    );
    assert_eq!(
        local(&after.goals[0], "hq").ty,
        clean_kernel::Expr::fvar(local(&after.goals[0], "q").fvar)
    );
}

#[test]
fn normal_observation_rejects_nested_sorry_and_transitive_admitted_terms() {
    for source in [
        "theorem nested_sorry (p : Prop) : p := by\n  exact (by sorry)\n",
        "theorem admitted (p : Prop) : p := by\n  sorry\ntheorem used_admitted (p : Prop) : p := by\n  exact admitted p\n",
        "theorem admitted_cursor (p : Prop) : p := by\n  sorry\ntheorem uses_admitted_cursor (p : Prop) : p := by\n  exact admitted_cursor p\n",
    ] {
        let (_, _, observations) = run(source, true);
        let observation = at(&observations, source, "exact");
        assert!(observation.before.is_ok(), "typed untrusted-free initial goal");
        assert!(matches!(observation.after.as_ref().unwrap(),
            Err(TacticGoalObservationUnavailable::Trusted(_)) |
            Err(TacticGoalObservationUnavailable::TrustedTerms(_))), "{observation:?}");
        if source.contains("\ntheorem") {
            assert_eq!(observation.tactic_range.end, source.trim_end().len(),
                "actual application argument belongs to the observed interval");
        }
    }
}

#[test]
fn normal_observation_never_publishes_closed_root_with_unresolved_witness() {
    let positive = "theorem explicit_witness : ∃ n : Nat, True := by\n  exact ⟨0, True.intro⟩\n";
    let (report, env, observations) = run(positive, true);
    assert!(
        report
            .verdicts
            .iter()
            .all(|v| v.kind == VerdictKind::Passed),
        "{report:?}"
    );
    checked_root(&env, "explicit_witness");
    assert!(at(&observations, positive, "exact")
        .after
        .as_ref()
        .unwrap()
        .as_ref()
        .unwrap()
        .goals
        .is_empty());
    let negative = "theorem unresolved_witness : ∃ n : Nat, True := by\n  exact ⟨_, True.intro⟩\n";
    let (report, env, observations) = run(negative, true);
    assert!(
        report.verdicts.iter().any(|v| v.kind.is_failure()),
        "{report:?}"
    );
    assert!(env
        .get_const(&Name::from_string("unresolved_witness"))
        .is_none());
    let view = at(&observations, negative, "exact");
    assert!(view.before.is_ok());
    assert!(
        view.after
            .as_ref()
            .is_none_or(|after| after.as_ref().is_err()
                || after.as_ref().is_ok_and(|goals| !goals.goals.is_empty())),
        "{view:?}"
    );
}

#[test]
fn normal_observation_tracks_actual_by_prefix_and_distinct_nested_blocks() {
    let source =
        "theorem nested_blocks (p : Prop) (hp : p) : p := by\n  exact (by\n    exact hp)\n";
    let (report, env, observations) = run(source, true);
    assert!(
        report
            .verdicts
            .iter()
            .all(|v| v.kind == VerdictKind::Passed),
        "{report:?}"
    );
    checked_root(&env, "nested_blocks");
    let prefixes: Vec<_> = observations
        .iter()
        .filter(|o| o.kind == super::TacticGoalObservationKind::ByPrefix)
        .collect();
    assert_eq!(prefixes.len(), 2);
    assert_ne!(prefixes[0].block_id, prefixes[1].block_id);
    let outer = prefixes
        .iter()
        .find(|o| o.tactic_range.start == source.find("by").unwrap())
        .unwrap();
    assert_eq!(outer.tactic_range.end, source.find("exact (by").unwrap());
    let before = outer.before.as_ref().unwrap();
    assert_eq!(before.goals[0].local_ctx.len(), 2);
    let outer_tactic = at(&observations, source, "exact (by");
    assert_eq!(outer_tactic.block_id, outer.block_id);
    let inner = at(&observations, source, "exact hp");
    assert_ne!(inner.block_id, outer.block_id);
    assert!(inner
        .after
        .as_ref()
        .unwrap()
        .as_ref()
        .unwrap()
        .goals
        .is_empty());
}

/// API fence control, separate from the source Exists/_ pair: ordinary tactic
/// checking intentionally treats open metas as typed FVars while constructing
/// a proof. A zero queued-goal list alone cannot license a solved IDE view.
#[test]
fn normal_observation_api_closed_root_rejects_unresolved_meta() {
    let _lock = module_elaboration_lock();
    let env = module_environment(EnvironmentSetup::default()).expect("normal module prelude");
    let nat = clean_kernel::Expr::const_str("Nat");
    for unresolved in [false, true] {
        let mut state = super::core::ProofState::new(env.clone(), nat.clone());
        let value = if unresolved {
            let witness = state.metas.fresh(nat.clone());
            clean_kernel::Expr::fvar(crate::unify::MetaState::to_fvar(witness))
        } else {
            clean_kernel::Expr::nat_lit(0)
        };
        let before = state.clone();
        super::exact(&mut state, value.clone()).expect("normal checked tactic API");
        assert!(state.is_complete(), "actual zero queued goals");
        let tc = TypeChecker::new(&env);
        if unresolved {
            assert!(
                tc.infer_type_full(&value).is_err(),
                "public kernel has no meta-FVar assumptions"
            );
        } else {
            let inferred = tc
                .infer_type_full(&value)
                .expect("full public value inference");
            assert!(tc.is_def_eq(&inferred, &nat));
            tc.check_type(&value, &nat)
                .expect("full public value check");
            assert!(env
                .axiom_deps(&Name::from_string("Nat"))
                .unwrap()
                .is_empty());
            assert!(clean_kernel::env::DomainAxiomClosure::new()
                .of_expr(&env, &value)
                .is_empty());
        }
        let capture = TacticGoalCapture::default();
        let block = capture.start_block(None).expect("observation identity");
        capture.record(
            block,
            super::TacticGoalObservationKind::Tactic,
            false,
            super::TacticPostSnapshotRange { start: 0, end: 1 },
            Box::new(before),
            Some(Box::new(state)),
        );
        let observations = capture.take().expect("unpoisoned collector");
        assert!(observations[0].before.is_ok());
        let after = observations[0].after.as_ref().unwrap();
        if unresolved {
            assert!(
                matches!(after, Err(TacticGoalObservationUnavailable::InvalidType(message))
                if message.contains("retains unresolved metavariable")),
                "{after:?}"
            );
        } else {
            assert!(after.as_ref().unwrap().goals.is_empty());
        }
    }
}

#[test]
fn normal_observation_rewrite_and_parenthesized_terms_have_checked_public_roots() {
    let source = "theorem observed_rewrite (a b c : Nat) (h : a = b) (hc : b = c) : a = c := by\n  rw [h]\n  exact hc\n";
    let (report, env, observations) = run(source, true);
    assert!(
        report
            .verdicts
            .iter()
            .all(|v| v.kind == VerdictKind::Passed),
        "{report:?}"
    );
    checked_root(&env, "observed_rewrite");
    let observation = at(&observations, source, "rw [h]");
    let before = &observation.before.as_ref().unwrap().goals[0];
    let after_view = observation.after.as_ref().unwrap().as_ref().unwrap();
    let after = &after_view.goals[0];
    assert!(after_view.rendered_targets[0].ends_with("⊢ b = c"));
    for name in ["a", "b", "c", "h", "hc"] {
        assert_eq!(local(before, name).fvar, local(after, name).fvar);
    }
    let target_fvars = super::hypothesis::collect_fvars(&after.target);
    assert!(target_fvars.contains(&local(after, "b").fvar));
    assert!(target_fvars.contains(&local(after, "c").fvar));
    assert!(!target_fvars.contains(&local(after, "a").fvar));

    let source = "theorem observed_parentheses (p : Prop) (hp : p) : p := by\n  exact ((hp))\n";
    let (report, env, observations) = run(source, true);
    assert!(
        report
            .verdicts
            .iter()
            .all(|v| v.kind == VerdictKind::Passed),
        "{report:?}"
    );
    checked_root(&env, "observed_parentheses");
    assert!(at(&observations, source, "exact ((hp))")
        .after
        .as_ref()
        .unwrap()
        .as_ref()
        .unwrap()
        .goals
        .is_empty());

    let source = "theorem observed_application (p : Prop) (hp : p) (identity : p → p) : p := by\n  exact identity hp\n";
    let (default_report, default_env, default_views) = run(source, false);
    let (report, env, observations) = run(source, true);
    assert_eq!(default_report.verdicts, report.verdicts);
    assert!(default_views.is_empty());
    assert_eq!(
        env.get_const(&Name::from_string("observed_application"))
            .unwrap()
            .value,
        default_env
            .get_const(&Name::from_string("observed_application"))
            .unwrap()
            .value
    );
    assert!(
        report
            .verdicts
            .iter()
            .all(|v| v.kind == VerdictKind::Passed),
        "{report:?}"
    );
    checked_root(&env, "observed_application");
    let observation = at(&observations, source, "exact identity hp");
    assert_eq!(observation.tactic_range.end, source.trim_end().len());
    assert!(observation
        .after
        .as_ref()
        .unwrap()
        .as_ref()
        .unwrap()
        .goals
        .is_empty());
}

#[test]
fn normal_observation_rwa_retains_pre_state_until_its_rule_list_tail() {
    let source = "theorem observed_rwa (a b : Nat) (h : a = b) : a = b := by\n  rwa [h]\n";
    let (default_report, default_env, default_views) = run(source, false);
    let (report, env, observations) = run(source, true);
    assert_eq!(default_report.verdicts, report.verdicts);
    assert!(default_views.is_empty());
    assert!(
        report
            .verdicts
            .iter()
            .all(|v| v.kind == VerdictKind::Passed),
        "{report:?}"
    );
    checked_root(&env, "observed_rwa");
    assert_eq!(
        env.get_const(&Name::from_string("observed_rwa"))
            .unwrap()
            .value,
        default_env
            .get_const(&Name::from_string("observed_rwa"))
            .unwrap()
            .value
    );
    let observation = at(&observations, source, "rwa [h]");
    assert!(
        observation.after_at_tail,
        "rule interiors must not expose the complete tactic's after-state"
    );
    let before = observation.before.as_ref().expect("typed actual before");
    assert!(before.rendered_targets[0].ends_with("⊢ a = b"));
    assert_eq!(local(&before.goals[0], "h").ty, before.goals[0].target);
    assert!(observation
        .after
        .as_ref()
        .unwrap()
        .as_ref()
        .unwrap()
        .goals
        .is_empty());
}
