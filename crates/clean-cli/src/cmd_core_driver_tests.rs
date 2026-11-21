// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean check` runs the module driver (`clean_elab::module_driver`), not a
//! loop of its own (roadmap 2026-09-24 lane D): the per-declaration pipeline,
//! the lock and the verdicts are the ones the LSP gets.

use crate::cmd_core::collect_check_outcome;
use clean_elab::module_driver::{
    elaborate_decls, module_elaboration_lock, module_environment, module_file_context,
    parse_module, DeclBudgetScope, DriverOptions, EnvironmentSetup, VerdictKind,
};
use clean_kernel::cli::{PreludeMode, DEFAULT_AUTOMATION_BUDGET, DEFAULT_DECL_BUDGET};
use std::path::Path;
use std::sync::mpsc;
use std::time::{Duration, Instant};

// The census lexes before it counts (CLAUDE.md: a gate reading Rust source
// blanks comments and string literals first), with the one sanctioned lexer,
// `clean_evidence::source_scan::blank_noncode` (design unit EV0). It used to
// include `clean-auto`'s hand-synced copy by `#[path]`; that copy is gone.
use clean_evidence::source_scan::blank_noncode;

/// The identifiers left in `src` once its comments and literals are blanked.
fn code_identifiers(src: &str) -> Vec<String> {
    blank_noncode(src)
        .split(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
        .filter(|token| !token.is_empty())
        .map(str::to_owned)
        .collect()
}

/// The per-declaration elaboration and re-validation entry points a loop of
/// its own would call: every public `elaborate_decl*` of `clean_elab`, the
/// preprocessor, `ElabCtx::elab_decl`, the read-only validator, and the names
/// of the copies lane D deleted.
fn is_loop_entry_point(identifier: &str) -> bool {
    identifier == "elaborate_decl"
        || identifier.starts_with("elaborate_decl_")
        || [
            "preprocess_decl_with_context",
            "elab_decl",
            "validate_decl_read_only",
            "typecheck_elab_result",
            "elab_result_name",
            "process_single_leaf",
        ]
        .contains(&identifier)
}

/// The entry points `src` names in code, in order.
fn loop_entry_points(src: &str) -> Vec<String> {
    code_identifiers(src)
        .into_iter()
        .filter(|identifier| is_loop_entry_point(identifier))
        .collect()
}

/// How often `src` names the driver's `elaborate_decls` in code, however
/// qualified or imported.
fn driver_mentions(src: &str) -> usize {
    code_identifiers(src)
        .iter()
        .filter(|identifier| *identifier == "elaborate_decls")
        .count()
}

/// How often `src` calls `module_driver::elaborate_decls(` in code.
fn driver_calls(src: &str) -> usize {
    blank_noncode(src)
        .matches("module_driver::elaborate_decls(")
        .count()
}

/// The census can fail: it finds a planted call however it is spelled, and
/// only in code — not in a comment, a string or past a char literal.
#[test]
fn test_check_path_census_sees_calls_only_in_code() {
    assert_eq!(
        loop_entry_points(
            "fn f() { clean_elab::elaborate_decl_and_register_with_warning(env, d); \
             let r = elaborate_decl(e, d); ctx.elab_decl(d); }"
        ),
        vec![
            "elaborate_decl_and_register_with_warning",
            "elaborate_decl",
            "elab_decl"
        ]
    );
    // An import is a mention in code too.
    assert_eq!(
        loop_entry_points("use clean_elab::{preprocess_decl_with_context as p};"),
        vec!["preprocess_decl_with_context"]
    );
    // The driver's own entry point is not a per-declaration one.
    assert!(loop_entry_points("module_driver::elaborate_decls(env, ds)").is_empty());
    assert!(loop_entry_points(
        "// elaborate_decl(x)\n/* nested /* elab_decl( */ */ let s = \"preprocess_decl_with_context(\\\" \
         elaborate_decl(\"; let r = r#\"elaborate_decl_capturing_holes(\"#; let b = b\"elab_decl\";"
    )
    .is_empty());
    // A char literal holding a quote must not swallow the code after it.
    assert_eq!(
        loop_entry_points("let q = '\"'; let e = '\\''; elaborate_decl(e, d); let s = \"\";"),
        vec!["elaborate_decl"]
    );
    // A lifetime is not a char literal.
    assert_eq!(
        loop_entry_points("fn g<'a>(x: &'a str) { elab_decl(x) }"),
        vec!["elab_decl"]
    );
    // The driver call is counted only in code: a comment or a string naming
    // it cannot stand in for the call.
    let real = "let r = clean_elab::module_driver::elaborate_decls(&mut env, &ds);";
    assert_eq!((driver_mentions(real), driver_calls(real)), (1, 1));
    let named_only = "// module_driver::elaborate_decls(\n\
                      let s = \"module_driver::elaborate_decls(\"; \
                      let r = r#\"module_driver::elaborate_decls(\"#;";
    assert_eq!(
        (driver_mentions(named_only), driver_calls(named_only)),
        (0, 0)
    );
}

/// Structural: the check path's sources call no per-declaration elaboration
/// or re-validation entry point themselves, and hand the file to
/// `elaborate_decls` exactly once. A second loop growing back in `cmd_core`
/// (the state lane D removed) fails here before it can drift from the driver.
#[test]
fn test_check_path_census_elaborates_only_through_module_driver() {
    let cmd_core = include_str!("cmd_core.rs");
    let observer = include_str!("cmd_core/check_observer.rs");
    for (file, src) in [
        ("cmd_core.rs", cmd_core),
        ("cmd_core/check_observer.rs", observer),
    ] {
        assert_eq!(
            loop_entry_points(src),
            Vec::<String>::new(),
            "{file} names per-declaration entry points itself; `clean check` must \
             elaborate through clean_elab::module_driver::elaborate_decls"
        );
    }
    assert_eq!(
        driver_mentions(cmd_core),
        1,
        "cmd_core.rs must hand each file to the module driver exactly once"
    );
    assert_eq!(
        driver_calls(cmd_core),
        1,
        "the one `elaborate_decls` in cmd_core.rs must be the driver's, called"
    );
    assert_eq!(driver_mentions(observer), 0);
}

/// Run `clean check` on `path` the way the CLI does, answering its pass count.
fn check_passes(path: &Path) -> Result<usize, String> {
    collect_check_outcome(
        path,
        false,
        false,
        PreludeMode::Builtin,
        true,
        false,
        clean_elab::ImportPolicy::default(),
        DEFAULT_DECL_BUDGET,
        DEFAULT_AUTOMATION_BUDGET,
        &[],
    )
    .map(|(outcome, _)| outcome.success_count)
    .map_err(|e| e.to_string())
}

/// Behavioural: `clean check` waits for the driver's `module_elaboration_lock`
/// (the lock `elaborate_decls` requires of its caller), so it cannot run while
/// another frontend in the process — the LSP — is elaborating.
///
/// The window is measured, not guessed: the same check is first timed with
/// nothing held (after a warm-up run, so both runs share the process-wide
/// prelude template), and the lock is then held for several times that. A
/// check that did not take the lock finishes inside the window; one that
/// takes it cannot. Demonstrated by mutation: with the lock acquisition in
/// `collect_check_outcome` removed, this test fails.
#[test]
fn test_check_waits_while_module_elaboration_lock_is_held() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("Locked.lean");
    std::fs::write(&path, "theorem t : 1 = 1 := rfl\n").expect("write fixture");

    assert_eq!(check_passes(&path), Ok(1), "warm-up check");
    let started = Instant::now();
    assert_eq!(check_passes(&path), Ok(1), "unlocked control check");
    let unlocked = started.elapsed();
    let window = (unlocked * 5).clamp(Duration::from_secs(1), Duration::from_secs(60));

    let held = module_elaboration_lock();
    let (done, finished) = mpsc::channel();
    let worker = std::thread::spawn(move || {
        // The receiver may have gone if the assertion below already failed.
        let _ = done.send(check_passes(&path));
    });
    let early = finished.recv_timeout(window);
    assert!(
        early.is_err(),
        "`clean check` finished ({early:?}) within {window:?} while the module driver's \
         lock was held; unlocked, the same check took {unlocked:?}"
    );
    drop(held);
    let passed = finished
        .recv_timeout(Duration::from_secs(600))
        .expect("`clean check` finishes once the lock is released");
    worker.join().expect("worker thread");
    assert_eq!(passed, Ok(1));
}

/// Behavioural: what `clean check` reports is what the driver's own classifier
/// decides on the same module — pass count, failure count, and every
/// elaboration-failure row byte for byte.
#[test]
fn test_check_rows_match_module_driver_verdicts() {
    let source = "namespace A\n\
                  def x : Nat := 1\n\
                  theorem bad : x = 2 := rfl\n\
                  def y : Nat := x + 1\n\
                  end A\n\
                  theorem t : A.y = 2 := rfl\n\
                  theorem s : 1 = 1 := sorry\n\
                  def broken : Nat := undefinedThing\n";
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("Agree.lean");
    std::fs::write(&path, source).expect("write fixture");

    let (outcome, _) = collect_check_outcome(
        &path,
        false,
        false,
        PreludeMode::Builtin,
        true,
        false,
        clean_elab::ImportPolicy::default(),
        DEFAULT_DECL_BUDGET,
        DEFAULT_AUTOMATION_BUDGET,
        &[],
    )
    .expect("check runs");

    let report = {
        let _lock = module_elaboration_lock();
        let mut env = module_environment(EnvironmentSetup::default()).expect("environment");
        let _budget = DeclBudgetScope::enter(DEFAULT_DECL_BUDGET);
        let parsed = parse_module(&path, source).1.expect("fixture parses");
        let mut file_ctx = module_file_context(&path);
        elaborate_decls(
            &mut env,
            &parsed.decls,
            source,
            &mut file_ctx,
            DriverOptions::default(),
            &mut (),
        )
    };

    let passed = report
        .verdicts
        .iter()
        .filter(|v| v.kind == VerdictKind::Passed)
        .count();
    let elaboration_rows: Vec<String> = report
        .verdicts
        .iter()
        .filter(|v| v.kind == VerdictKind::ElaborationFailed)
        .map(|v| format!("{}: {}", v.name, v.detail.as_deref().unwrap_or_default()))
        .collect();
    let trust_debt = report
        .verdicts
        .iter()
        .filter(|v| matches!(v.kind, VerdictKind::TrustDebt(_)))
        .count();

    assert_eq!(
        (passed, elaboration_rows.len(), trust_debt),
        (3, 2, 1),
        "fixture verdicts: {:?}",
        report.verdicts
    );
    assert_eq!(outcome.decl_count, report.verdicts.len());
    assert_eq!(outcome.success_count, passed);
    assert_eq!(outcome.errors, elaboration_rows);
    assert_eq!(outcome.trust_failures.len(), trust_debt);
    assert!(outcome.kernel_failures.is_empty());
    assert!(outcome.diverged.is_empty());
}
