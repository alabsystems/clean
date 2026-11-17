// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::{BinderInfo, Expr};
use std::sync::Arc;

const SOURCE: &str = "prelude\ninductive Token where | one\ndef query (x : Token) : Token := x\n";

fn input<'a>(file: &'a std::path::Path, module: &'a Name) -> ExternalLeanInput<'a> {
    ExternalLeanInput {
        file,
        module,
        imports: &[],
        search_paths: &[],
        world: LeanWorld::Lean435,
    }
}

#[test]
fn test_replayed_context_logical_only_complete_capture_cannot_select_and_native_rechecks_real_readiness(
) {
    let directory = tempfile::tempdir().unwrap();
    let file = directory.path().join("Inspection.lean");
    std::fs::write(&file, SOURCE).unwrap();
    let module = Name::from_string("Inspection");
    let query = Name::from_string("query");
    let inspection = ExternalLeanInspection::elaborate(input(&file, &module)).unwrap();
    assert_eq!(inspection.world(), LeanWorld::Lean435);
    assert!(!inspection.inputs().is_empty());
    assert!(inspection.source_capture().errors.is_empty());
    assert!(inspection.source_capture().snapshot_blake3.is_some());
    assert!(inspection
        .replay_context(std::slice::from_ref(&query))
        .unwrap()
        .replay_verdict()
        .passed(false));
    assert!(inspection.inspect_owned_declaration(&query).is_ok());
    for result in [
        inspection.program.select(&query, 0),
        inspection.program.select_in_runtime_closure(&query, 0),
    ] {
        assert!(
            matches!(result, Err(ExternalLeanError::Compile(ref reason)) if reason.contains("logical inspection"))
        );
    }
    let mut executable = ExternalLeanProgram::elaborate(input(&file, &module)).unwrap();
    assert!(executable.require_native().is_ok());
    assert!(executable.select(&query, 0).is_ok());
    assert!(executable.select_in_runtime_closure(&query, 0).is_ok());
    // Private test-only corruption demonstrates that the usage marker alone
    // cannot bless missing/failed compiler capture. No production mutator exists.
    Arc::get_mut(&mut executable.custody)
        .unwrap()
        .observation
        .errors
        .push("test-only changed capture".into());
    assert!(executable
        .replay_context(std::slice::from_ref(&query))
        .unwrap()
        .replay_verdict()
        .passed(false));
    for result in [
        executable.select(&query, 0),
        executable.select_in_runtime_closure(&query, 0),
    ] {
        assert!(
            matches!(result, Err(ExternalLeanError::Input(ref reason)) if reason.contains("incomplete source snapshot"))
        );
    }
    println!("actual435 logical-only complete capture: no native API; both internal selection doors refuse; executable complete capture selects, changed capture refuses: PASS");
}

#[test]
fn test_replayed_context_default_executable_elaboration_still_refuses_actual_incomplete_init_capture(
) {
    let directory = tempfile::tempdir().unwrap();
    let file = directory.path().join("Incomplete.lean");
    std::fs::write(&file, "def query (x : Nat) : Nat := x\n").unwrap();
    let module = Name::from_string("Incomplete");
    let imports = [Name::from_string("Init")];
    let inspection = ExternalLeanInspection::elaborate(ExternalLeanInput {
        file: &file,
        module: &module,
        imports: &imports,
        search_paths: &[],
        world: LeanWorld::Lean435,
    })
    .expect("actual full-Init logical-only capture must retain diagnostics");
    let query = Name::from_string("query");
    let context = inspection
        .replay_context(std::slice::from_ref(&query))
        .expect("actual Nat identity cone must replay");
    assert!(context.replay_verdict().passed(false));
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let expected = Expr::pi(BinderInfo::Default, nat.clone(), nat);
    let declaration = context.declaration(&query).unwrap();
    context
        .check_expected_type(
            &declaration,
            &[],
            &expected,
            super::super::ReplayContextLimits::default(),
        )
        .expect("full-Init owned query must check against actual Nat arrow type");
    let zero = Expr::nat_lit(0);
    let application = Expr::app(Expr::const_(query.clone(), vec![]), zero.clone());
    assert!(context
        .definitionally_equal(
            &application,
            &zero,
            super::super::ReplayContextLimits::default()
        )
        .expect("full-Init query application must fully check and reduce"));
    println!("actual435 full-Init actual query handle, closed expected type and checked definitional equality: PASS");
    let capture = inspection.source_capture();
    assert!(capture.snapshot_blake3.is_none());
    assert!(!capture.delta_complete);
    assert!(!capture.errors.is_empty());
    assert!(!capture.row_failures.is_empty());
    println!("actual435 full-Init compiler capture: {} typed row failures, {} errors, digest absent, delta incomplete", capture.row_failures.len(), capture.errors.len());
    for failure in capture.row_failures.iter().take(3) {
        println!(
            "actual435 retained compiler row failure: {} {:?}: {}",
            failure.phase, failure.name, failure.reason
        );
    }
    for result in [
        inspection.program.select(&query, 0),
        inspection.program.select_in_runtime_closure(&query, 0),
    ] {
        assert!(
            matches!(result, Err(ExternalLeanError::Compile(ref reason)) if reason.contains("logical inspection"))
        );
    }
    let result = ExternalLeanProgram::elaborate(ExternalLeanInput {
        file: &file,
        module: &module,
        imports: &imports,
        search_paths: &[],
        world: LeanWorld::Lean435,
    });
    assert!(
        matches!(result, Err(ExternalLeanError::Input(ref reason)) if reason.starts_with("incomplete source snapshot:"))
    );
    println!("actual435 default executable constructor: actual incomplete Init compiler capture remains refused: PASS");
}
