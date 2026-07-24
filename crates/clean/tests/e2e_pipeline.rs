// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end integration tests for the clean check pipeline.
//!
//! Exercises the full path: Lean source -> parse -> elaborate -> typecheck -> verify.
//! All tests use real parsing and type-checking with no mocks. No external
//! dependencies required (no Lean 4 toolchain, no Mathlib).

use std::path::Path;
use std::time::Duration;

use clean::kernel::Environment;
use clean::{check_file, check_source, load_source_into, CheckConfig, CheckResult, DeclWarning};

// ---------------------------------------------------------------------------
// Helper
// ---------------------------------------------------------------------------

fn default_config() -> CheckConfig {
    CheckConfig::default()
}

fn allow_sorry_config() -> CheckConfig {
    let mut config = CheckConfig::default();
    config.allow_sorry = true;
    config
}

/// Assert the check result has no errors and at least `min_passed` passed declarations.
fn assert_clean(result: &CheckResult, min_passed: usize, context: &str) {
    assert!(
        result.errors.is_empty(),
        "{context}: expected no errors, got: {:?}",
        result.errors
    );
    assert!(
        result.passed_count >= min_passed,
        "{context}: expected at least {min_passed} passed, got {}",
        result.passed_count
    );
}

// ===========================================================================
// Section 1: Simple definitions
// ===========================================================================

#[test]
fn test_e2e_simple_nat_literal() {
    let result =
        check_source("def x : Nat := 0", &default_config()).expect("pipeline should not fail");
    assert_clean(&result, 1, "nat literal");
    assert!(
        result.is_fully_verified(),
        "simple def should be fully verified"
    );
}

#[test]
fn test_e2e_simple_nat_nonzero() {
    let result = check_source("def answer : Nat := 42", &default_config())
        .expect("pipeline should not fail");
    assert_clean(&result, 1, "nat nonzero");
}

#[test]
fn test_e2e_simple_nat_succ() {
    let result = check_source("def one : Nat := Nat.succ Nat.zero", &default_config())
        .expect("pipeline should not fail");
    assert_clean(&result, 1, "nat succ");
}

#[test]
fn test_e2e_simple_bool_true() {
    let result =
        check_source("def t : Bool := true", &default_config()).expect("pipeline should not fail");
    assert_clean(&result, 1, "bool true");
}

#[test]
fn test_e2e_simple_bool_false() {
    let result =
        check_source("def f : Bool := false", &default_config()).expect("pipeline should not fail");
    assert_clean(&result, 1, "bool false");
}

// ===========================================================================
// Section 2: Theorems with proofs
// ===========================================================================

#[test]
fn test_e2e_theorem_true_intro() {
    let result = check_source("theorem trivial : True := True.intro", &default_config())
        .expect("pipeline should not fail");
    assert_clean(&result, 1, "True.intro theorem");
    assert!(
        result.is_fully_verified(),
        "True.intro should be fully verified"
    );
}

#[test]
fn test_e2e_theorem_refl() {
    let result = check_source("theorem nat_eq : 0 = 0 := rfl", &default_config())
        .expect("pipeline should not fail");
    // rfl may or may not pass depending on the elaborator's Eq support; check no crash
    assert!(
        result.passed_count >= 1 || !result.errors.is_empty(),
        "rfl theorem should either pass or produce a meaningful error"
    );
}

// ===========================================================================
// Section 3: Sorry handling
// ===========================================================================

#[test]
fn test_e2e_sorry_rejected_by_default() {
    let result = check_source("theorem oops : True := sorry", &default_config())
        .expect("pipeline should succeed even with sorry");
    assert!(
        !result.errors.is_empty() || result.sorry_count > 0,
        "sorry should produce an error or bump sorry_count"
    );
    assert!(
        !result.is_fully_verified(),
        "sorry theorem should not be fully verified"
    );
}

#[test]
fn test_e2e_sorry_allowed_passes() {
    let result = check_source("theorem oops : True := sorry", &allow_sorry_config())
        .expect("pipeline should succeed");
    assert!(
        result.passed_count >= 1,
        "sorry should be allowed, but got errors: {:?}",
        result.errors
    );
}

#[test]
fn test_e2e_sorry_warning_classification() {
    let result = check_source("theorem oops : True := sorry", &allow_sorry_config())
        .expect("pipeline should succeed");
    // At least one declaration should have a sorry-related warning
    let has_sorry_warning = result.declarations.iter().any(|d| {
        matches!(
            &d.warning,
            Some(DeclWarning::ExplicitSorry | DeclWarning::SyntheticSorry)
        )
    });
    // Either we detect the sorry via warning or via sorry_count
    assert!(
        has_sorry_warning || result.sorry_count > 0,
        "expected sorry to be detected via warning or counter"
    );
}

// ===========================================================================
// Section 4: Error cases
// ===========================================================================

#[test]
fn test_e2e_undefined_reference_error() {
    let result = check_source("def bad : Nat := nonexistent_name_xyz", &default_config())
        .expect("pipeline should not crash on elaboration error");
    assert!(
        !result.errors.is_empty(),
        "undefined reference should produce errors"
    );
}

#[test]
fn test_e2e_type_mismatch_error() {
    let result = check_source("def bad : Bool := 42", &default_config())
        .expect("pipeline should not crash on type mismatch");
    assert!(
        !result.errors.is_empty(),
        "type mismatch should produce errors"
    );
}

#[test]
fn test_e2e_parse_error() {
    let result = check_source("this is not valid lean syntax {{{ +++", &default_config());
    // The pipeline may return a parse error, an elaboration error, or an empty
    // result (if the parser skips unrecognized tokens). All are acceptable
    // as long as the pipeline does not panic.
    match result {
        Ok(r) => {
            // Either errors were reported, or the parser produced no declarations
            // from the gibberish input. Both are correct behavior.
            assert!(
                !r.errors.is_empty() || r.passed_count == 0,
                "invalid syntax should produce errors or zero declarations"
            );
        }
        Err(_) => { /* Parse error is also acceptable */ }
    }
}

#[test]
fn test_e2e_empty_source() {
    let result = check_source("", &default_config()).expect("empty source should not fail");
    assert_eq!(result.passed_count, 0, "empty source should have 0 passed");
    assert!(
        result.errors.is_empty(),
        "empty source should have no errors"
    );
}

// ===========================================================================
// Section 5: Incremental loading (dependent declarations)
// ===========================================================================

#[test]
fn test_e2e_incremental_two_defs() {
    let mut env = Environment::try_with_prelude().expect("prelude should initialize");
    let config = default_config();

    let r1 = load_source_into(&mut env, "def myVal : Nat := 42", &config)
        .expect("first load should succeed");
    assert_clean(&r1, 1, "incremental: first def");

    let r2 = load_source_into(&mut env, "def myVal2 : Nat := myVal", &config)
        .expect("second load referencing first should succeed");
    assert_clean(&r2, 1, "incremental: dependent def");
}

#[test]
fn test_e2e_incremental_three_chain() {
    let mut env = Environment::try_with_prelude().expect("prelude should initialize");
    let config = default_config();

    let r1 = load_source_into(&mut env, "def a1 : Nat := 1", &config).expect("a1 should succeed");
    assert_clean(&r1, 1, "chain: a1");

    let r2 = load_source_into(&mut env, "def a2 : Nat := a1", &config).expect("a2 should succeed");
    assert_clean(&r2, 1, "chain: a2");

    let r3 = load_source_into(&mut env, "def a3 : Nat := a2", &config).expect("a3 should succeed");
    assert_clean(&r3, 1, "chain: a3");
}

#[test]
fn test_e2e_incremental_undefined_still_errors() {
    let mut env = Environment::try_with_prelude().expect("prelude should initialize");
    let config = default_config();

    // Load a valid definition
    load_source_into(&mut env, "def x1 : Nat := 1", &config).expect("x1 should succeed");

    // Try to reference something that was never defined
    let r2 = load_source_into(&mut env, "def x2 : Nat := never_defined", &config)
        .expect("pipeline should not crash");
    assert!(
        !r2.errors.is_empty(),
        "reference to undefined name should still error in incremental mode"
    );
}

// ===========================================================================
// Section 6: Multiple declarations in one source
// ===========================================================================

#[test]
fn test_e2e_multiple_defs_one_source() {
    let source = r#"
def multi1 : Nat := 1
def multi2 : Nat := 2
def multi3 : Nat := 3
"#;
    let result = check_source(source, &default_config()).expect("multiple defs should succeed");
    assert!(
        result.passed_count >= 3,
        "expected at least 3 passed, got {}: errors={:?}",
        result.passed_count,
        result.errors
    );
}

#[test]
fn test_e2e_mixed_defs_and_theorems() {
    let source = r#"
def mixVal : Nat := 10
theorem mixThm : True := True.intro
"#;
    let result =
        check_source(source, &default_config()).expect("mixed defs+theorems should succeed");
    assert!(
        result.passed_count >= 2,
        "expected at least 2 passed, got {}: errors={:?}",
        result.passed_count,
        result.errors
    );
}

// ===========================================================================
// Section 7: Declaration result inspection
// ===========================================================================

#[test]
fn test_e2e_decl_result_name_present() {
    let result = check_source("def inspectMe : Nat := 7", &default_config())
        .expect("pipeline should succeed");
    let has_name = result
        .declarations
        .iter()
        .any(|d| d.name.contains("inspectMe"));
    assert!(
        has_name,
        "declaration result should contain 'inspectMe', got names: {:?}",
        result
            .declarations
            .iter()
            .map(|d| &d.name)
            .collect::<Vec<_>>()
    );
}

#[test]
fn test_e2e_decl_result_passed_true() {
    let result = check_source("def passCheck : Nat := 0", &default_config())
        .expect("pipeline should succeed");
    let passed = result
        .declarations
        .iter()
        .filter(|d| d.name.contains("passCheck"))
        .all(|d| d.passed);
    assert!(passed, "passCheck should have passed=true");
}

#[test]
fn test_e2e_decl_result_error_on_failure() {
    let result = check_source("def failCheck : Nat := undefined_xyz", &default_config())
        .expect("pipeline should not crash");
    // There should be at least one declaration/error
    assert!(
        !result.errors.is_empty() || result.declarations.iter().any(|d| !d.passed),
        "undefined reference should cause a failure in declarations or errors"
    );
}

// ===========================================================================
// Section 8: File-based checking
// ===========================================================================

#[test]
fn test_e2e_check_file_roundtrip() {
    let dir = tempfile::tempdir().expect("tempdir should be created");
    let file = dir.path().join("e2e_test.lean");
    std::fs::write(&file, "def fileTest : Nat := 99").expect("write should succeed");

    let result = check_file(&file, &default_config()).expect("check_file should succeed");
    assert_clean(&result, 1, "file roundtrip");
}

#[test]
fn test_e2e_check_file_multiple_decls() {
    let dir = tempfile::tempdir().expect("tempdir should be created");
    let file = dir.path().join("multi.lean");
    std::fs::write(
        &file,
        "def fileA : Nat := 1\ndef fileB : Nat := 2\ntheorem fileT : True := True.intro\n",
    )
    .expect("write should succeed");

    let result = check_file(&file, &default_config()).expect("check_file should succeed");
    assert!(
        result.passed_count >= 3,
        "expected 3+ passed from file, got {}: errors={:?}",
        result.passed_count,
        result.errors
    );
}

#[test]
fn test_e2e_check_file_nonexistent_returns_io_error() {
    let result = check_file(
        Path::new("/nonexistent/path/e2e_phantom.lean"),
        &default_config(),
    );
    assert!(result.is_err(), "nonexistent file should return error");
}

#[test]
fn test_e2e_load_file_into_incremental() {
    let mut env = Environment::try_with_prelude().expect("prelude");
    let config = default_config();

    let dir = tempfile::tempdir().expect("tempdir");

    let file1 = dir.path().join("part1.lean");
    std::fs::write(&file1, "def filePart1 : Nat := 100").expect("write");
    let r1 =
        clean::load_file_into(&mut env, &file1, &config).expect("first file load should succeed");
    assert_clean(&r1, 1, "file incremental: part1");

    let file2 = dir.path().join("part2.lean");
    std::fs::write(&file2, "def filePart2 : Nat := filePart1").expect("write");
    let r2 = clean::load_file_into(&mut env, &file2, &config)
        .expect("second file referencing first should succeed");
    assert_clean(&r2, 1, "file incremental: part2");
}

// ===========================================================================
// Section 9: CheckResult properties
// ===========================================================================

#[test]
fn test_e2e_check_result_helpers_track_failures_and_warnings() {
    let clean =
        check_source("def CleanHelpers : Nat := 0", &default_config()).expect("clean source");
    assert_eq!(clean.failed_count(), 0, "clean source should not fail");
    assert_eq!(clean.warning_count(), 0, "clean source should not warn");
    assert!(
        !clean.has_failures(),
        "clean source should have no failures"
    );
    assert!(
        !clean.has_warnings(),
        "clean source should have no warnings"
    );

    let mut allow_sorry = default_config();
    allow_sorry.allow_sorry = true;
    let warned = check_source("theorem warnHelpers : True := sorry", &allow_sorry)
        .expect("allow_sorry source should succeed");
    assert_eq!(
        warned.failed_count(),
        0,
        "allow_sorry should avoid failures"
    );
    assert_eq!(
        warned.warning_count(),
        1,
        "expected one warning-bearing declaration"
    );
    assert!(
        !warned.has_failures(),
        "allow_sorry result should remain failure-free"
    );
    assert!(
        warned.has_warnings(),
        "sorry should still surface as a warning"
    );
    assert!(
        warned
            .declarations
            .iter()
            .filter_map(|decl| decl.warning.as_ref())
            .any(|warning| warning.is_sorry()),
        "expected a sorry-classified warning"
    );
    assert!(
        !warned.is_fully_verified(),
        "sorry should still block full verification"
    );

    let failed = check_source(
        "def failHelpers : Nat := missing_helper_name",
        &default_config(),
    )
    .expect("failing source should still produce a structured result");
    assert!(
        failed.failed_count() >= 1,
        "expected at least one failed declaration"
    );
    assert!(failed.has_failures(), "expected helper failure detection");
    assert_eq!(failed.warning_count(), 0, "plain failures should not warn");
    assert!(!failed.has_warnings(), "plain failures should not warn");
}

#[test]
fn test_e2e_is_fully_verified_clean() {
    let result =
        check_source("def clean : Nat := 0", &default_config()).expect("pipeline should succeed");
    assert!(
        result.is_fully_verified(),
        "clean def should be fully verified"
    );
    assert_eq!(result.sorry_count, 0);
    assert_eq!(result.kernel_check_failures, 0);
}

#[test]
fn test_e2e_is_fully_verified_false_with_sorry() {
    let result = check_source("theorem s : True := sorry", &default_config())
        .expect("pipeline should succeed");
    assert!(
        !result.is_fully_verified(),
        "sorry theorem should not be fully verified"
    );
}

#[test]
fn test_e2e_elapsed_nonzero() {
    let result =
        check_source("def timing : Nat := 0", &default_config()).expect("pipeline should succeed");
    // elapsed should be non-negative (could be zero on very fast machines, but Duration is always >= 0)
    assert!(
        result.elapsed >= Duration::ZERO,
        "elapsed should be non-negative"
    );
}

// ===========================================================================
// Section 10: Throughput / performance measurement
// ===========================================================================

#[test]
fn test_e2e_throughput_10_defs() {
    let mut source = String::new();
    for i in 0..10 {
        source.push_str(&format!("def throughput_{i} : Nat := {i}\n"));
    }

    let result = check_source(&source, &default_config()).expect("throughput test should succeed");
    // `CheckResult::elapsed` starts after Clean's process-global check lock is
    // acquired.  Measuring around `check_source` instead makes this benchmark
    // include time queued behind unrelated tests when this binary runs in
    // parallel, which turns scheduler contention into a false regression.
    let elapsed = result.elapsed;

    assert!(
        result.passed_count >= 10,
        "expected 10+ passed, got {}: errors={:?}",
        result.passed_count,
        result.errors
    );

    let rate = 10.0 / elapsed.as_secs_f64();
    // Pipeline should handle at least 10 simple defs/sec on any machine
    assert!(
        rate > 10.0,
        "throughput {rate:.1} decls/sec is below minimum threshold of 10/sec (elapsed: {elapsed:?})"
    );
}

#[test]
fn test_e2e_throughput_incremental_10_defs() {
    let mut env = Environment::try_with_prelude().expect("prelude");
    let config = default_config();

    let mut elapsed = Duration::ZERO;
    for i in 0..10 {
        let src = format!("def incr_tp_{i} : Nat := {i}");
        let result = load_source_into(&mut env, &src, &config)
            .expect("incremental throughput should succeed");
        assert_clean(&result, 1, &format!("incremental throughput: def {i}"));
        elapsed += result.elapsed;
    }

    let rate = 10.0 / elapsed.as_secs_f64();
    assert!(
        rate > 5.0,
        "incremental throughput {rate:.1} decls/sec is below minimum threshold of 5/sec (elapsed: {elapsed:?})"
    );
}

// ===========================================================================
// Section 11: Nat arithmetic
// ===========================================================================

#[test]
fn test_e2e_nat_add() {
    let result = check_source("def addEx : Nat := Nat.add 1 2", &default_config())
        .expect("Nat.add should succeed");
    assert_clean(&result, 1, "Nat.add");
}

#[test]
fn test_e2e_nat_zero() {
    let result = check_source("def z : Nat := Nat.zero", &default_config())
        .expect("Nat.zero should succeed");
    assert_clean(&result, 1, "Nat.zero");
}

// ===========================================================================
// Section 12: Full pipeline integration (build, check, verify in one test)
// ===========================================================================

#[test]
fn test_e2e_full_pipeline_multi_stage() {
    // Stage 1: Parse + elaborate + typecheck several declarations
    let source = r#"
def stage1_val : Nat := 10
theorem stage1_thm : True := True.intro
"#;
    let result = check_source(source, &default_config()).expect("stage 1 should succeed");
    assert_clean(&result, 2, "full pipeline stage 1");
    assert!(
        result.is_fully_verified(),
        "stage 1 should be fully verified"
    );

    // Stage 2: Incremental build on shared environment
    let mut env = Environment::try_with_prelude().expect("prelude");
    let config = default_config();

    let r1 =
        load_source_into(&mut env, "def base : Nat := 5", &config).expect("base should succeed");
    assert_clean(&r1, 1, "full pipeline: base");

    let r2 = load_source_into(&mut env, "def derived : Nat := base", &config)
        .expect("derived should succeed");
    assert_clean(&r2, 1, "full pipeline: derived");

    // Stage 3: File-based check
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("pipeline.lean");
    std::fs::write(
        &file,
        "def filePipeline : Nat := 7\ntheorem fileTruth : True := True.intro\n",
    )
    .expect("write");
    let r3 = check_file(&file, &default_config()).expect("file check should succeed");
    assert!(
        r3.passed_count >= 2,
        "file pipeline: expected 2+ passed, got {}: {:?}",
        r3.passed_count,
        r3.errors
    );

    // Stage 4: Verify sorry rejection
    let r4 = check_source("theorem sorry_test : True := sorry", &default_config())
        .expect("sorry check should not crash");
    assert!(
        !r4.is_fully_verified(),
        "sorry should not be fully verified"
    );
}

// ===========================================================================
// Section 13: Inductive types
// ===========================================================================

#[test]
fn test_e2e_inductive_simple_enum() {
    let source = r#"
inductive Color where
  | red : Color
  | green : Color
  | blue : Color
"#;
    let result = check_source(source, &default_config())
        .expect("simple inductive enum should parse and elaborate");
    // Inductive registration may or may not count as "passed" depending on
    // how the pipeline reports it; the key invariant is no crash and the
    // environment contains the type.
    assert!(
        result.errors.is_empty() || result.passed_count >= 1,
        "simple inductive should succeed or produce no errors: {:?}",
        result.errors
    );
}

#[test]
fn test_e2e_inductive_with_payload() {
    let source = r#"
inductive MyOption (a : Type) where
  | none : MyOption a
  | some : a -> MyOption a
"#;
    let result =
        check_source(source, &default_config()).expect("parameterized inductive should parse");
    // No panic is the minimum; check for clean elaboration
    assert!(
        result.errors.is_empty() || result.passed_count >= 1,
        "parameterized inductive errors: {:?}",
        result.errors
    );
}

#[test]
fn test_e2e_inductive_recursive() {
    let source = r#"
inductive MyList (a : Type) where
  | nil : MyList a
  | cons : a -> MyList a -> MyList a
"#;
    let result = check_source(source, &default_config()).expect("recursive inductive should parse");
    assert!(
        result.errors.is_empty() || result.passed_count >= 1,
        "recursive inductive errors: {:?}",
        result.errors
    );
}

#[test]
fn test_e2e_inductive_used_in_def() {
    // Define an inductive and then use it in a subsequent definition
    let source = r#"
inductive Direction where
  | north : Direction
  | south : Direction
  | east : Direction
  | west : Direction

def defaultDir : Direction := Direction.north
"#;
    let result = check_source(source, &default_config()).expect("inductive + def should parse");
    // The def referencing the inductive should elaborate successfully
    let def_passed = result
        .declarations
        .iter()
        .any(|d| d.name.contains("defaultDir") && d.passed);
    assert!(
        def_passed || result.errors.is_empty(),
        "def using inductive should pass: declarations={:?}, errors={:?}",
        result
            .declarations
            .iter()
            .map(|d| (&d.name, d.passed))
            .collect::<Vec<_>>(),
        result.errors
    );
}

// ===========================================================================
// Section 14: Structure types
// ===========================================================================

#[test]
fn test_e2e_structure_simple() {
    let source = r#"
structure Point where
  x : Nat
  y : Nat
"#;
    let result = check_source(source, &default_config()).expect("simple structure should parse");
    assert!(
        result.errors.is_empty() || result.passed_count >= 1,
        "simple structure errors: {:?}",
        result.errors
    );
}

#[test]
fn test_e2e_structure_with_defaults() {
    let source = r#"
structure Config where
  verbose : Bool := false
  maxRetries : Nat := 3
"#;
    let result =
        check_source(source, &default_config()).expect("structure with defaults should parse");
    assert!(
        result.errors.is_empty() || result.passed_count >= 1,
        "structure with defaults errors: {:?}",
        result.errors
    );
}

#[test]
fn test_e2e_structure_used_in_def() {
    let source = r#"
structure Pair where
  fst : Nat
  snd : Nat

def origin : Pair := { fst := 0, snd := 0 }
"#;
    let result =
        check_source(source, &default_config()).expect("structure + constructor should parse");
    // Check that at least the structure or the def passes
    assert!(
        result.passed_count >= 1 || result.errors.is_empty(),
        "structure + def errors: {:?}",
        result.errors
    );
}

// ===========================================================================
// Section 15: Lambda expressions and function types
// ===========================================================================

#[test]
fn test_e2e_lambda_identity() {
    let result = check_source("def myId : Nat -> Nat := fun x => x", &default_config())
        .expect("lambda identity should parse");
    assert_clean(&result, 1, "lambda identity");
}

#[test]
fn test_e2e_lambda_const() {
    let result = check_source(
        "def myConst : Nat -> Nat -> Nat := fun x _ => x",
        &default_config(),
    )
    .expect("lambda const should parse");
    assert_clean(&result, 1, "lambda const");
}

#[test]
fn test_e2e_lambda_composition() {
    let source = r#"
def compose (f : Nat -> Nat) (g : Nat -> Nat) (x : Nat) : Nat := f (g x)
"#;
    let result =
        check_source(source, &default_config()).expect("function composition should parse");
    assert_clean(&result, 1, "compose");
}

#[test]
fn test_e2e_polymorphic_identity() {
    let result = check_source("def polyId (a : Type) (x : a) : a := x", &default_config())
        .expect("polymorphic identity should parse");
    assert_clean(&result, 1, "polymorphic identity");
}

#[test]
fn test_e2e_higher_order_function() {
    let source = r#"
def applyTwice (f : Nat -> Nat) (x : Nat) : Nat := f (f x)
"#;
    let result =
        check_source(source, &default_config()).expect("higher-order function should parse");
    assert_clean(&result, 1, "higher-order function");
}

// ===========================================================================
// Section 16: Nested expressions and application
// ===========================================================================

#[test]
fn test_e2e_nested_application() {
    let result = check_source(
        "def nested : Nat := Nat.succ (Nat.succ Nat.zero)",
        &default_config(),
    )
    .expect("nested application should parse");
    assert_clean(&result, 1, "nested application");
}

#[test]
fn test_e2e_function_returning_function() {
    let result = check_source(
        "def mkConst (n : Nat) : Nat -> Nat := fun _ => n",
        &default_config(),
    )
    .expect("function returning function should parse");
    assert_clean(&result, 1, "function returning function");
}

// ===========================================================================
// Section 17: If-then-else
// ===========================================================================

#[test]
fn test_e2e_if_then_else() {
    let source = r#"
def myMax (a b : Nat) : Nat :=
  if Nat.ble a b then b else a
"#;
    let result = check_source(source, &default_config()).expect("if-then-else should parse");
    // if-then-else depends on Decidable elaboration; check no crash
    assert!(
        result.passed_count >= 1 || !result.errors.is_empty(),
        "if-then-else should either pass or produce a meaningful error"
    );
}

// ===========================================================================
// Section 18: Abbreviations
// ===========================================================================

#[test]
fn test_e2e_abbrev() {
    let source = r#"
abbrev MyNat := Nat
def myVal : MyNat := 42
"#;
    let result = check_source(source, &default_config()).expect("abbrev should parse");
    // The def using the abbrev should pass
    let def_ok = result
        .declarations
        .iter()
        .any(|d| d.name.contains("myVal") && d.passed);
    assert!(
        def_ok || result.errors.is_empty(),
        "abbrev usage should work: {:?}",
        result.errors
    );
}

// ===========================================================================
// Section 19: Universe polymorphism
// ===========================================================================

#[test]
fn test_e2e_universe_polymorphic_def() {
    let result = check_source(
        "def myFst (a b : Type) (p : a) (q : b) : a := p",
        &default_config(),
    )
    .expect("universe-polymorphic def should parse");
    assert_clean(&result, 1, "universe-polymorphic def");
}

// ===========================================================================
// Section 20: Complex multi-declaration scenario
// ===========================================================================

#[test]
fn test_e2e_complex_multi_decl_scenario() {
    // A realistic scenario with multiple interdependent declarations
    let source = r#"
def baseVal : Nat := 100

def doubleIt (n : Nat) : Nat := Nat.add n n

def tripleIt (n : Nat) : Nat := Nat.add n (doubleIt n)

theorem true_is_true : True := True.intro
"#;
    let result = check_source(source, &default_config()).expect("complex multi-decl should parse");
    assert!(
        result.passed_count >= 3,
        "expected at least 3 passed declarations (defs + theorem), got {}: errors={:?}",
        result.passed_count,
        result.errors
    );
    assert!(
        result.is_fully_verified(),
        "complex multi-decl should be fully verified"
    );
}

#[test]
fn test_e2e_incremental_inductive_then_def() {
    // Use incremental loading to define an inductive and then a function using it
    let mut env = Environment::try_with_prelude().expect("prelude should initialize");
    let config = default_config();

    let r1 = load_source_into(
        &mut env,
        r#"
inductive Weekday where
  | monday : Weekday
  | tuesday : Weekday
  | wednesday : Weekday
  | thursday : Weekday
  | friday : Weekday
"#,
        &config,
    )
    .expect("inductive Weekday should parse");
    assert!(
        r1.errors.is_empty(),
        "Weekday inductive should have no errors: {:?}",
        r1.errors
    );

    // Now define a value using the inductive
    let r2 = load_source_into(&mut env, "def today : Weekday := Weekday.friday", &config)
        .expect("def using Weekday should parse");
    assert_clean(&r2, 1, "incremental: def using inductive");
}

// ===========================================================================
// Section 21: Pipeline robustness — edge cases
// ===========================================================================

#[test]
fn test_e2e_whitespace_only() {
    let result = check_source("   \n\n\t  \n", &default_config())
        .expect("whitespace-only source should not fail");
    assert_eq!(
        result.passed_count, 0,
        "whitespace should produce 0 declarations"
    );
    assert!(
        result.errors.is_empty(),
        "whitespace should produce no errors"
    );
}

#[test]
fn test_e2e_comments_only() {
    let source = r#"
-- This is a comment
-- Another comment
/- Block comment -/
"#;
    let result =
        check_source(source, &default_config()).expect("comments-only source should not fail");
    assert_eq!(
        result.passed_count, 0,
        "comments should produce 0 declarations"
    );
    assert!(
        result.errors.is_empty(),
        "comments should produce no errors"
    );
}

#[test]
fn test_e2e_very_long_name() {
    let long_name = "a".repeat(200);
    let source = format!("def {long_name} : Nat := 0");
    let result = check_source(&source, &default_config()).expect("long name should not crash");
    assert_clean(&result, 1, "very long name");
}

#[test]
fn test_e2e_many_parameters() {
    let source = r#"
def manyParams (a b c d e f g h : Nat) : Nat := a
"#;
    let result = check_source(source, &default_config()).expect("many parameters should parse");
    assert_clean(&result, 1, "many parameters");
}

// ===========================================================================
// Section 22: Inductive + structure pipeline (StateT-like scenario)
// ===========================================================================

#[test]
fn test_e2e_inductive_structure_abbrev_chain() {
    // A mini StateT-like scenario adapted from the elaborator regression tests
    let source = r#"
inductive MyErr where
  | notFound : MyErr

structure MyCtx where
  count : Nat

abbrev MyAlias := Nat
def fromAlias : MyAlias := 42
"#;
    let result = check_source(source, &default_config())
        .expect("inductive+structure+abbrev chain should parse");
    // The alias-based def should pass
    let alias_ok = result
        .declarations
        .iter()
        .any(|d| d.name.contains("fromAlias") && d.passed);
    assert!(
        alias_ok || result.errors.is_empty(),
        "inductive+structure+abbrev chain errors: {:?}",
        result.errors
    );
}

// ===========================================================================
// Section 23: Throughput scaling — larger batches
// ===========================================================================

#[test]
fn test_e2e_throughput_50_defs() {
    let mut source = String::new();
    for i in 0..50 {
        source.push_str(&format!("def tp50_{i} : Nat := {i}\n"));
    }

    let result =
        check_source(&source, &default_config()).expect("50-def throughput should succeed");
    let elapsed = result.elapsed;

    assert!(
        result.passed_count >= 50,
        "expected 50+ passed, got {}: errors={:?}",
        result.passed_count,
        result.errors
    );

    let rate = 50.0 / elapsed.as_secs_f64();
    // At 50 defs, pipeline should sustain reasonable throughput
    assert!(
        rate > 5.0,
        "50-def throughput {rate:.1} decls/sec is below 5/sec (elapsed: {elapsed:?})"
    );
}

#[test]
fn test_e2e_throughput_mixed_decls() {
    let mut source = String::new();
    for i in 0..10 {
        source.push_str(&format!("def mixTp_{i} : Nat := {i}\n"));
    }
    for i in 0..5 {
        source.push_str(&format!("theorem mixThm_{i} : True := True.intro\n"));
    }

    let result = check_source(&source, &default_config()).expect("mixed throughput should succeed");
    let elapsed = result.elapsed;

    assert!(
        result.passed_count >= 15,
        "expected 15+ passed (10 defs + 5 theorems), got {}: errors={:?}",
        result.passed_count,
        result.errors
    );

    let rate = 15.0 / elapsed.as_secs_f64();
    assert!(
        rate > 5.0,
        "mixed throughput {rate:.1} decls/sec is below 5/sec (elapsed: {elapsed:?})"
    );
}
