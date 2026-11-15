// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The driver's own contract, measured on source text through the same steps a
//! frontend composes (environment, parse, `FileContext`, loop).

use super::verdict::typecheck_elab_result;
use super::{
    elaborate_decls, module_environment, module_file_context, parse_module, DeclBudgetScope,
    DeclVerdict, DriverOptions, EnvironmentSetup, FailureIsolation, ImportHandling, ModuleReport,
    VerdictKind,
};
use crate::ElabResult;
use crate::RegistrationWarningKind;
use clean_kernel::{Environment, Expr, Name};
use std::path::Path;

fn run(source: &str, options: DriverOptions) -> (ModuleReport, Environment) {
    run_with_budget(source, options, 0)
}

/// `budget` is armed AFTER the environment is built, as every frontend does:
/// the budget bounds the module's declarations, not the prelude.
fn run_with_budget(
    source: &str,
    options: DriverOptions,
    budget: u64,
) -> (ModuleReport, Environment) {
    let _lock = super::module_elaboration_lock();
    let path = Path::new("DriverFixture.lean");
    let mut env = module_environment(EnvironmentSetup::default()).expect("check environment");
    let _budget = DeclBudgetScope::enter(budget);
    let report = parse_module(path, source).1.expect("fixture parses");
    let mut file_ctx = module_file_context(path);
    let report = elaborate_decls(
        &mut env,
        &report.decls,
        source,
        &mut file_ctx,
        options,
        &mut (),
    );
    (report, env)
}

fn kinds(report: &ModuleReport) -> Vec<(String, VerdictKind)> {
    report
        .verdicts
        .iter()
        .map(|DeclVerdict { name, kind, .. }| (name.clone(), kind.clone()))
        .collect()
}

/// The audit's `nsonly` module, which the per-declaration `ElabCtx` loop of
/// `clean lake build` refused with `Unknown identifier: x`: namespace state
/// must survive from one member to the next.
#[test]
fn test_elaborate_decls_namespace_member_sees_earlier_member_passes() {
    let (report, _) = run(
        "namespace A\ndef x : Nat := 1\ndef y : Nat := x + 1\nend A\n",
        DriverOptions::default(),
    );
    assert_eq!(
        kinds(&report),
        vec![
            ("A.x".to_owned(), VerdictKind::Passed),
            ("A.y".to_owned(), VerdictKind::Passed),
        ]
    );
}

/// The audit's `secvar` module: a section `variable` is abstracted into the
/// declaration that uses it, so a later declaration applies it to an argument.
#[test]
fn test_elaborate_decls_section_variable_becomes_a_parameter_passes() {
    let (report, env) = run(
        "section\nvariable (n : Nat)\ndef addn (m : Nat) : Nat := n + m\nend\n\
         theorem addn_one_two : addn 1 2 = 3 := rfl\n",
        DriverOptions::default(),
    );
    assert_eq!(
        kinds(&report),
        vec![
            ("addn".to_owned(), VerdictKind::Passed),
            ("addn_one_two".to_owned(), VerdictKind::Passed),
        ]
    );
    assert!(env.get_const(&Name::from_string("addn")).is_some());
}

/// A failing declaration is recorded and the module keeps going, so every
/// failure is reported — not just the first.
#[test]
fn test_elaborate_decls_failure_does_not_stop_the_module_reports_every_failure() {
    let (report, _) = run(
        "def a : Nat := 1\ndef b : Nat := nope\ndef c : Nat := a\ndef d : Nat := alsoNope\n",
        DriverOptions::default(),
    );
    let got = kinds(&report);
    assert_eq!(
        got,
        vec![
            ("a".to_owned(), VerdictKind::Passed),
            ("b".to_owned(), VerdictKind::ElaborationFailed),
            ("c".to_owned(), VerdictKind::Passed),
            ("d".to_owned(), VerdictKind::ElaborationFailed),
        ]
    );
    let b = &report.verdicts[1];
    assert_eq!(b.line, Some(2), "a verdict carries its declaration's line");
    let detail = b.detail.as_deref().unwrap_or_default();
    assert!(
        detail.starts_with("elaboration error at line 2:") && detail.contains("nope"),
        "the detail is `clean check`'s rendering: {detail}"
    );
}

/// A member of a namespace block that fails is its own verdict; its passing
/// sibling does not inherit the failure.
#[test]
fn test_elaborate_decls_failed_block_member_is_its_own_verdict() {
    let (report, _) = run(
        "namespace T\ndef a : Nat := 1\ndef b : Nat := nope\nend T\n",
        DriverOptions::default(),
    );
    assert_eq!(
        kinds(&report),
        vec![
            ("T.a".to_owned(), VerdictKind::Passed),
            ("T.b".to_owned(), VerdictKind::ElaborationFailed),
        ]
    );
    assert_eq!(report.verdicts[1].line, Some(3), "the member's own line");
}

/// Trust debt is a verdict of its own, not a pass and not a failure.
#[test]
fn test_elaborate_decls_explicit_sorry_is_trust_debt_not_failure() {
    let (report, _) = run("theorem s : 1 = 2 := sorry\n", DriverOptions::default());
    assert_eq!(
        kinds(&report),
        vec![(
            "s".to_owned(),
            VerdictKind::TrustDebt(RegistrationWarningKind::ExplicitSorry)
        )]
    );
    assert!(!report.verdicts[0].kind.is_failure());
}

/// Under `Elaborate` an unresolvable `import` is refused fail-closed like any
/// declaration and named `import`; under `Preloaded` the caller owns the
/// header and the driver skips it without a verdict.
#[test]
fn test_elaborate_decls_import_handling_elaborates_or_skips() {
    let source = "import NoSuchDriverModule.Anywhere\ndef k : Nat := 3\n";
    let (elaborated, _) = run(source, DriverOptions::default());
    assert_eq!(
        kinds(&elaborated),
        vec![
            ("import".to_owned(), VerdictKind::ElaborationFailed),
            ("k".to_owned(), VerdictKind::Passed),
        ]
    );
    let detail = elaborated.verdicts[0].detail.as_deref().unwrap_or_default();
    assert!(detail.contains("NoSuchDriverModule.Anywhere"), "{detail}");

    let (preloaded, _) = run(
        source,
        DriverOptions {
            imports: ImportHandling::Preloaded,
            ..DriverOptions::default()
        },
    );
    assert_eq!(
        kinds(&preloaded),
        vec![("k".to_owned(), VerdictKind::Passed)]
    );
}

/// A declaration that spends the whole budget has no verdict but `Diverged`,
/// even though it would pass with fuel — the fail-closed direction.
#[test]
fn test_elaborate_decls_exhausted_budget_is_diverged_not_passed() {
    let (report, _) = run_with_budget(
        "theorem four : 2 + 2 = 4 := rfl\n",
        DriverOptions::default(),
        1,
    );
    assert_eq!(
        kinds(&report),
        vec![("four".to_owned(), VerdictKind::Diverged)]
    );
    assert!(report.verdicts[0].kind.is_failure());
    assert!(report.peak_decl_ticks >= 1);
}

/// `Rollback` restores the environment a failed declaration saw; `Keep` does
/// not have to. Measured on the one thing both must agree on: the failed
/// declaration itself is never in the environment afterwards.
#[test]
fn test_elaborate_decls_rollback_isolation_leaves_no_failed_name() {
    let source = "def ok : Nat := 1\ndef bad : Nat := nope\n";
    for isolation in [FailureIsolation::Keep, FailureIsolation::Rollback] {
        let (report, env) = run(
            source,
            DriverOptions {
                isolation,
                ..DriverOptions::default()
            },
        );
        assert_eq!(report.verdicts.len(), 2, "{isolation:?}");
        assert!(env.get_const(&Name::from_string("ok")).is_some());
        assert!(env.get_const(&Name::from_string("bad")).is_none());
    }
}

/// Records the hooks a frontend overrides, and stops after `stop_after`
/// declarations.
struct HookObserver {
    stop_after: usize,
    finished: usize,
    warnings_asked: Vec<String>,
}

impl super::ModuleObserver for HookObserver {
    fn after_decl(
        &mut self,
        _file_ctx: &crate::FileContext,
        _decl: &clean_parser::SurfaceDecl,
        _budget: &super::BudgetReading,
    ) {
        self.finished += 1;
    }

    fn leaf_warning(
        &mut self,
        _env: &Environment,
        leaf: &ElabResult,
        driver_default: &dyn Fn() -> Option<crate::RegistrationWarning>,
    ) -> Option<crate::RegistrationWarning> {
        self.warnings_asked.push(
            leaf.declaration_name()
                .map_or_else(String::new, ToString::to_string),
        );
        driver_default()
    }

    fn stop_requested(&self) -> bool {
        self.finished >= self.stop_after
    }
}

/// `stop_requested` ends the module after the declaration it answers for (what
/// `clean check` does after a refused `import`), and `leaf_warning` is asked
/// once per leaf while the driver's own reading stays the default.
#[test]
fn test_elaborate_decls_observer_stop_ends_module_after_that_decl() {
    let source = "def a : Nat := 1\ntheorem s : 1 = 1 := sorry\ndef c : Nat := 3\n";
    let _lock = super::module_elaboration_lock();
    let path = Path::new("DriverStop.lean");
    let mut env = module_environment(EnvironmentSetup::default()).expect("check environment");
    let _budget = DeclBudgetScope::enter(0);
    let parsed = parse_module(path, source).1.expect("fixture parses");
    let mut file_ctx = module_file_context(path);
    let mut observer = HookObserver {
        stop_after: 2,
        finished: 0,
        warnings_asked: Vec::new(),
    };
    let report = elaborate_decls(
        &mut env,
        &parsed.decls,
        source,
        &mut file_ctx,
        DriverOptions::default(),
        &mut observer,
    );
    assert_eq!(
        kinds(&report),
        vec![
            ("a".to_owned(), VerdictKind::Passed),
            (
                "s".to_owned(),
                VerdictKind::TrustDebt(RegistrationWarningKind::ExplicitSorry)
            ),
        ]
    );
    assert_eq!(
        observer.warnings_asked,
        vec!["a".to_owned(), "s".to_owned()]
    );
    assert!(env.get_const(&Name::from_string("a")).is_some());
    assert!(env.get_const(&Name::from_string("c")).is_none());
}

/// A failed `deriving` class is not a failed declaration: Lean 4.8.0 declares
/// the type before it runs the handlers and logs a handler's error
/// (`infer::deriving_log`), so under BOTH isolations `W` is declared and
/// passes, its clause is a separate failed leaf carrying the handler's error,
/// and a later use of `W` passes — the LSP (`Rollback`) agrees with
/// `clean check` (`Keep`), with nothing for `Rollback` to restore. The
/// control: an unknown class is resolved before the type is declared, so
/// `Bad` is never declared and its use is refused under both.
#[test]
fn test_elaborate_decls_failed_deriving_keeps_its_type_under_both_isolations() {
    let source = "structure W where\n  f : Nat → Nat\n  deriving Repr\n\
                  def useW (w : W) : Nat := w.f 0\n\
                  structure Bad where\n  x : Nat\n  deriving NoSuchClass\n\
                  def useBad (b : Bad) : Nat := b.x\n";
    let failed_class =
        crate::derive::builtin_instance_name(&Name::from_string("W"), "Repr").to_string();
    for isolation in [FailureIsolation::Keep, FailureIsolation::Rollback] {
        let (report, env) = run(
            source,
            DriverOptions {
                isolation,
                ..DriverOptions::default()
            },
        );
        assert_eq!(
            kinds(&report),
            vec![
                ("W".to_owned(), VerdictKind::Passed),
                (failed_class.clone(), VerdictKind::ElaborationFailed),
                ("useW".to_owned(), VerdictKind::Passed),
                ("Bad".to_owned(), VerdictKind::ElaborationFailed),
                ("useBad".to_owned(), VerdictKind::ElaborationFailed),
            ],
            "{isolation:?}"
        );
        // The clause's leaf is reported at the structure, with the handler's
        // own error.
        assert_eq!(report.verdicts[1].line, Some(1), "{isolation:?}");
        let detail = report.verdicts[1].detail.as_deref().unwrap_or_default();
        assert!(
            detail.contains("cannot synthesize Repr for field `f`"),
            "{isolation:?}: {detail}"
        );
        let detail = report.verdicts[3].detail.as_deref().unwrap_or_default();
        assert!(detail.contains("NoSuchClass"), "{isolation:?}: {detail}");
        for name in ["W", "W.mk", "W.f", "useW"] {
            assert!(
                env.get_const(&Name::from_string(name)).is_some(),
                "{isolation:?}: `{name}` must be declared"
            );
        }
        for name in [failed_class.as_str(), "Bad", "useBad"] {
            assert!(
                env.get_const(&Name::from_string(name)).is_none(),
                "{isolation:?}: `{name}` must not be declared"
            );
        }
    }
}

#[test]
fn test_typecheck_elab_result_non_prop_theorem_is_rejected() {
    let env = Environment::try_with_prelude().expect("prelude should initialize");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let decl = ElabResult::Theorem {
        name: Name::from_string("bad"),
        universe_params: vec![],
        ty: nat,
        proof: nat_zero,
        modifiers: clean_parser::DeclModifiers::default(),
    };
    let err =
        typecheck_elab_result(&decl, &env).expect_err("theorem with Nat type should be rejected");
    assert!(
        err.contains("type must be a Prop"),
        "expected Prop gate error, got: {err}"
    );
}

#[test]
fn test_typecheck_elab_result_prop_theorem_is_accepted() {
    let env = Environment::try_with_prelude().expect("prelude should initialize");
    // theorem trivial : True := True.intro
    let decl = ElabResult::Theorem {
        name: Name::from_string("trivial"),
        universe_params: vec![],
        ty: Expr::const_(Name::from_string("True"), vec![]),
        proof: Expr::const_(Name::from_string("True.intro"), vec![]),
        modifiers: clean_parser::DeclModifiers::default(),
    };
    let name =
        typecheck_elab_result(&decl, &env).expect("theorem with Prop type should be accepted");
    assert_eq!(name, "trivial");
}

#[test]
fn test_typecheck_elab_result_skipped_is_administrative() {
    let env = Environment::try_with_prelude().expect("prelude should initialize");
    let name = typecheck_elab_result(&ElabResult::Skipped, &env).expect("skipped should succeed");
    assert_eq!(name, "(skipped)");
}

/// The driver's indexed line lookup answers exactly what the walk from byte 0
/// (`source_span`) answers, for top-level declarations and block members alike,
/// across multi-byte characters and blank lines.
#[test]
fn test_source_lines_agree_with_source_span() {
    let source = "-- α β γ\n\ndef a : Nat := 1\n\
                  theorem «weird name» : (1 : Nat) = 1 := rfl\n\
                  namespace N\n  /-- ∀ — docs -/\n  def b : Nat := 2\n\n  def c : Nat := 3\nend N\n\
                  example : True := trivial\n";
    let decls = parse_module(Path::new("Lines.lean"), source)
        .1
        .expect("fixture parses")
        .decls;
    let mut all: Vec<&clean_parser::SurfaceDecl> = Vec::new();
    for decl in &decls {
        all.push(decl);
        if let clean_parser::SurfaceDecl::Namespace { decls: inner, .. } = decl {
            all.extend(inner.iter());
        }
    }
    assert!(all.len() >= 6, "fixture parsed to {} decls", all.len());
    let lines = super::surface::SourceLines::new(source);
    let mut located = 0;
    for decl in all {
        let walked = super::surface_decl_span(decl)
            .and_then(|span| super::source_span(source, span))
            .map(|span| span.line);
        assert_eq!(lines.decl_line(decl), walked, "{decl:?}");
        located += usize::from(walked.is_some());
    }
    assert!(located >= 5, "only {located} declarations were located");
}
