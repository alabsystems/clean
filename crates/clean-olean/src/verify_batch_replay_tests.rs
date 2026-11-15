// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit pins for the replay lanes' budget handling (`verify_batch_replay.rs`,
//! `local_check_roster.rs`): a starved check never decides a later one, and a
//! declaration is undecided only when every failed check of it was starved.
//! The same holds for a check refused for a sharing-dependent universe
//! instantiation (DECISIONS R150).
//!
//! The checks are real kernel checks over one definition, `T : Type := Prop →
//! Prop`: the check `(fun p : Prop => p) : T` needs a δ-unfolding of `T` and
//! so reaches `is_def_eq`.

use super::*;
use crate::bootstrap_verify::{categorize_failures, BootstrapFailure};
use crate::verify_batch_full::local_roster::BUDGET_EXHAUSTED;
use clean_kernel::env::{ConstantInfo, Reducibility};
use clean_kernel::expr::{BinderInfo, Expr};

fn n(s: &str) -> Name {
    Name::from_string(s)
}

/// Real kernel checks distinguish a finite-budget refusal from an ill-typed
/// definition, including the replay verdict of each declaration's dependent.
#[test]
fn test_parallel_replay_preserves_budget_and_kernel_refusal_diagnostics() {
    const LIMIT: u32 = 1;
    let mut env = env_with_t();
    let identity_type = Expr::const_(n("T"), vec![]);
    let identity = Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
    for (label, type_, value) in [
        ("Starved", identity_type.clone(), identity),
        (
            "UsesStarved",
            identity_type,
            Expr::const_(n("Starved"), vec![]),
        ),
        ("Rejected", Expr::prop(), Expr::prop()),
        (
            "UsesRejected",
            Expr::prop(),
            Expr::const_(n("Rejected"), vec![]),
        ),
        ("Independent", Expr::type_(), Expr::prop()),
    ] {
        // Adversarial test fixture only: the intentionally bad definition is
        // not admitted and this assumed environment never leaves the test.
        env.add_constant_unchecked_for_test(ConstantInfo::new_with_reducibility(
            n(label),
            vec![],
            type_,
            Some(value),
            Reducibility::Regular(1),
            ConstantKind::Definition,
        ));
    }
    let all_targets = [
        "Starved",
        "UsesStarved",
        "Rejected",
        "UsesRejected",
        "Independent",
    ]
    .into_iter()
    .map(str::to_owned)
    .collect();
    let none = BTreeSet::new();
    let redeclarations = BTreeMap::new();
    let scope = ReplayScope {
        prerequisites: &none,
        not_admitted: &none,
        already_declared: &redeclarations,
    };
    let budget_targets = ["Starved", "UsesStarved", "Independent"]
        .into_iter()
        .map(str::to_owned)
        .collect();
    let plan = ReplayPlan::new(&env, &budget_targets, &scope);
    let (checks, serial_verdicts) = run_eager(&plan, &env, LIMIT);
    assert!(
        matches!(
            serial_verdicts.get(&n("Starved")).unwrap(),
            Err(ReplayRefusal::BudgetExhausted { limit: LIMIT, .. })
        ),
        "actual serial verdicts: {serial_verdicts:?}"
    );
    assert!(serial_verdicts[&n("UsesStarved")]
        .as_ref()
        .unwrap_err()
        .undecided());
    assert!(serial_verdicts[&n("Independent")].is_ok());
    let serial = plan.finish(checks, &serial_verdicts);
    assert_eq!((serial.0, serial.1), (1, 2), "{serial:?}");

    // The valid target and its dependent pass when their resource limit is
    // removed. A genuinely ill-typed target and its dependent refuse with
    // budget to spare, rather than borrowing the finite run's starvation.
    let unbounded_plan = ReplayPlan::new(&env, &all_targets, &scope);
    let (checks, unbounded) = run_eager(&unbounded_plan, &env, 0);
    assert!(unbounded[&n("Starved")].is_ok());
    assert!(unbounded[&n("UsesStarved")].is_ok());
    assert!(matches!(
        unbounded.get(&n("Rejected")).unwrap(),
        Err(ReplayRefusal::KernelRejected { .. })
    ));
    assert!(!unbounded[&n("UsesRejected")]
        .as_ref()
        .unwrap_err()
        .undecided());
    assert!(unbounded[&n("Independent")].is_ok());
    let unbounded_report = unbounded_plan.finish(checks, &unbounded);
    assert_eq!(
        (unbounded_report.0, unbounded_report.1),
        (3, 2),
        "{unbounded_report:?}"
    );

    for workers in [1, 2] {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(workers)
            .stack_size(clean_kernel::test_utils::LARGE_STACK)
            .build()
            .unwrap();
        let (checks, verdicts) = run_parallel(&plan, &env, &pool, LIMIT);
        assert_eq!(
            verdicts, serial_verdicts,
            "typed budget verdicts, workers={workers}"
        );
        assert_eq!(plan.finish(checks, &verdicts), serial);
        let actual = parallel(&env, &budget_targets, &scope, &pool, LIMIT);
        assert_eq!(actual, serial, "all counts and findings, workers={workers}");
        let (checks, verdicts) = run_parallel(&unbounded_plan, &env, &pool, 0);
        assert_eq!(verdicts, unbounded, "typed refusals, workers={workers}");
        assert_eq!(unbounded_plan.finish(checks, &verdicts), unbounded_report);
        assert_eq!(
            parallel(&env, &all_targets, &scope, &pool, 0),
            unbounded_report,
            "all unbounded counts and findings, workers={workers}"
        );
    }
}

fn prop() -> Expr {
    Expr::sort(Level::zero())
}

/// `T : Type := Prop → Prop`, a regular definition the check must unfold.
fn env_with_t() -> Environment {
    let mut env = Environment::default();
    env.add_constant_unchecked_for_test(ConstantInfo::new_with_reducibility(
        n("T"),
        vec![],
        Expr::sort(Level::succ(Level::zero())),
        Some(Expr::pi(BinderInfo::Default, prop(), prop())),
        Reducibility::Regular(1),
        ConstantKind::Definition,
    ));
    env
}

/// `(fun p : Prop => p) : T`: well-typed, admitted with no budget.
fn identity_has_type_t(tc: &TypeChecker<'_>) -> Result<(), String> {
    let identity = Expr::lam(BinderInfo::Default, prop(), Expr::bvar(0));
    tc.check_type(&identity, &Expr::const_(n("T"), vec![]))
        .map_err(|error| format!("check_type: {error:?}"))
}

/// `Prop : Prop`: ill-typed (`Prop : Type`), refused with budget to spare.
fn prop_has_type_prop(tc: &TypeChecker<'_>) -> Result<(), String> {
    tc.check_type(&prop(), &prop())
        .map_err(|error| format!("check_type: {error:?}"))
}

/// The unbudgeted control: the check passes, so any failure of it under a
/// budget is the budget's.
#[test]
fn test_replay_checker_identity_check_passes_without_a_budget() {
    let env = env_with_t();
    let mut checker = ReplayChecker::new(&env, 0);
    assert_eq!(checker.check(identity_has_type_t), None);
    assert_eq!(checker.check(identity_has_type_t), None);
}

/// Entries the checker has memoised: reduction, def-eq and inferred types.
fn memoised(tc: &TypeChecker<'_>) -> usize {
    tc.whnf_cache_entries()
        + tc.def_eq_cache_entries()
        + tc.type_cache_stats().map_or(0, |stats| stats.entries)
}

/// The defect a long-lived checker had: a check that ran out of budget
/// memoises what its starved `whnf`/`is_def_eq` answered (and what it inferred
/// on the way), and the next check, run with a fresh budget, is answered from
/// that. [`ReplayChecker::check`] must hand the next check a checker that
/// memoised nothing, and must never report a failure of this honest check as
/// a verdict, at any budget. The control replays each budget on the bare
/// kernel checker (no replacement) and must find one at which the starved
/// check left memoised entries behind, or this test pins nothing.
#[test]
fn test_replay_checker_replaces_the_kernel_checker_after_a_starved_check() {
    let env = env_with_t();
    let mut memoised_while_starved = Vec::new();
    for limit in 1..=64 {
        let bare = ReplayChecker::new(&env, limit);
        let tc = bare.kernel();
        tc.reset_local_context();
        tc.reset_heartbeat();
        if identity_has_type_t(tc).is_err() && tc.heartbeat_spent() && memoised(tc) > 0 {
            memoised_while_starved.push(limit);
        }

        let mut checker = ReplayChecker::new(&env, limit);
        let first = checker.check(identity_has_type_t);
        if first.as_ref().is_some_and(CheckProblem::budget_spent) {
            assert_eq!(
                memoised(checker.kernel()),
                0,
                "limit {limit}: a starved check's memo must not reach the next check"
            );
        }
        for problem in [first, checker.check(identity_has_type_t)]
            .into_iter()
            .flatten()
        {
            assert!(
                problem.budget_spent(),
                "limit {limit}: an honest check failed with budget to spare: {problem:?}"
            );
        }
    }
    assert!(
        !memoised_while_starved.is_empty(),
        "control: at some budget the bare checker must memoise a starved check's \
         answers, or this test pins nothing"
    );
}

/// A declaration is BUDGET EXHAUSTED only when every failed check starved:
/// one failure with budget to spare is the kernel's verdict, whichever check
/// came first, and invalid accounting is never laundered into the budget.
#[test]
fn test_verdict_of_is_undecided_only_when_every_failed_check_starved() {
    let env = env_with_t();
    let starved = ReplayChecker::new(&env, 1)
        .check(identity_has_type_t)
        .expect("one heartbeat cannot check `fun p => p : T`");
    assert!(starved.budget_spent(), "{starved:?}");
    let finding = ReplayChecker::new(&env, 0)
        .check(prop_has_type_prop)
        .expect("`Prop : Prop` is ill-typed");
    assert!(!finding.budget_spent(), "{finding:?}");
    assert!(finding.error().contains("TypeMismatch"), "{finding:?}");

    let name = n("d");
    for mixed in [
        [starved.clone(), finding.clone()],
        [finding.clone(), starved.clone()],
    ] {
        let refusal = verdict_of(&name, &mixed, true, 1).expect_err("refused");
        assert!(
            matches!(&refusal, ReplayRefusal::KernelRejected { message, .. }
                if message.contains("TypeMismatch") && message.contains(BUDGET_EXHAUSTED)),
            "{refusal:?}"
        );
        assert!(!refusal.undecided(), "{refusal:?}");
    }

    let undecided =
        verdict_of(&name, &[starved.clone(), starved.clone()], true, 1).expect_err("not admitted");
    assert!(
        matches!(undecided, ReplayRefusal::BudgetExhausted { limit: 1, .. }),
        "{undecided:?}"
    );
    assert!(undecided.undecided());
    let shown = undecided.to_string();
    assert!(shown.starts_with("budget exhausted: `d`"), "{shown}");
    assert_eq!(
        shown.matches(BUDGET_EXHAUSTED).count(),
        1,
        "the budget is named once: {shown}"
    );

    assert!(matches!(
        verdict_of(&name, std::slice::from_ref(&starved), false, 1),
        Err(ReplayRefusal::KernelRejected { .. })
    ));
    assert!(matches!(
        verdict_of(&name, &[], false, 1),
        Err(ReplayRefusal::KernelRejected { message, .. }) if message.contains("accounting")
    ));
    assert_eq!(verdict_of(&name, &[], true, 1), Ok(()));
}

/// A starved check's report names the budget first, so the lanes' triage
/// files it under the budget and never under what the under-reduction
/// failed with.
#[test]
fn test_starved_report_is_categorised_as_the_budget() {
    let env = env_with_t();
    let starved = ReplayChecker::new(&env, 1)
        .check(identity_has_type_t)
        .expect("one heartbeat cannot check `fun p => p : T`");
    let report = starved.report();
    assert!(
        report.starts_with("budget exhausted: the check spent its heartbeat budget of 1"),
        "{report}"
    );
    assert!(report.ends_with(starved.error()), "{report}");
    let categories = categorize_failures(&[BootstrapFailure {
        name: "d".into(),
        error: format!("{report} [Anon/Str(\"d\")]"),
    }]);
    assert_eq!(
        categories.into_iter().collect::<Vec<_>>(),
        [(BUDGET_EXHAUSTED.to_owned(), 1)]
    );
    assert_eq!(
        crate::verify_batch::error_category(&report),
        "HeartbeatExceeded"
    );
}

/// `cS.{u,v} : Sort (imax v (u+1))` with the `imax` node stored as given, as
/// `ReplayLevelSharing`'s `ls_cS` and the decoders keep it: Lean's `mk_imax`
/// rebuilds it to `max v (u+1)`, so whether `instantiate` keeps it for
/// `cS.{u,v}` turns on object sharing, and the Lean checker refuses that
/// instantiation by name (DECISIONS R150).
fn env_with_cs() -> Environment {
    let mut env = env_with_t();
    let (u, v) = (Level::param(n("u")), Level::param(n("v")));
    let stored = Level::IMax(v.into(), Level::succ(u).into());
    env.add_constant_unchecked_for_test(ConstantInfo::new_with_reducibility(
        n("cS"),
        vec![n("u"), n("v")],
        Expr::sort(stored),
        None,
        Reducibility::Opaque,
        ConstantKind::Axiom,
    ));
    env
}

/// `cS.{u,v}` inferred, its error kept or swallowed.
fn infer_cs(tc: &TypeChecker<'_>) -> Result<(), String> {
    let (u, v) = (Level::param(n("u")), Level::param(n("v")));
    tc.infer_type(&Expr::const_(n("cS"), vec![u, v]))
        .map(drop)
        .map_err(|error| format!("infer: {error:?}"))
}

/// A sharing-dependent instantiation leaves a checker refusing everything
/// after it, and [`ReplayChecker::check`] reused one checker across a
/// replay's declarations, so one such refusal refused every later
/// declaration of the lane by the same name (measured 2026-10-20: `clean
/// olean replay --fresh` of the `Eqp` probes refused 64 Init constants,
/// `sorryAx` and `letFun` among them, naming `cS`). The check that met it is
/// refused by name, even when it swallowed the error, and is a verdict, and
/// the next check runs on a checker that refusal did not reach. The control
/// shows the bare checker poisoned, or this pins nothing.
#[test]
fn test_replay_checker_sharing_refusal_decides_no_later_check() {
    let env = env_with_cs();
    let bare = ReplayChecker::new(&env, 0);
    let tc = bare.kernel();
    assert!(infer_cs(tc).is_err_and(|error| error.contains("LevelSharingDependent")));
    tc.reset_local_context();
    tc.reset_heartbeat();
    assert!(
        identity_has_type_t(tc).is_err(),
        "control: the bare checker refuses an honest check after the sharing refusal"
    );

    let mut checker = ReplayChecker::new(&env, 0);
    for first in [
        checker.check(infer_cs),
        checker.check(|tc| {
            let _swallowed = infer_cs(tc);
            Ok(())
        }),
    ] {
        let first = first.expect("the sharing-dependent instantiation is refused");
        assert!(!first.budget_spent(), "{first:?}");
        assert!(first.error().contains("LevelSharingDependent"), "{first:?}");
        assert_eq!(
            checker.check(identity_has_type_t),
            None,
            "the sharing refusal must not decide the next check"
        );
    }
}
