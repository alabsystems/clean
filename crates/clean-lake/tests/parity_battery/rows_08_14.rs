// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parity battery rows 08-14: the fail-closed dependency and import rows,
//! the `lake init` templates, strict-lakefile rejection, and the two
//! `lake test` rows. Row semantics are pinned; see `parity_battery.rs`.

use std::fs;

use clean_lake::cli::{run_lake, InitArgs, LakeCommand};
use clean_lake::{
    BuildOptions, LakeConfig, LakeError, LakeManifest, LakefileParseMode, PathPackage, Workspace,
};
use tempfile::TempDir;

use crate::common::*;

// ---------------------------------------------------------------------------
// Row 08 — fail-closed missing dep: no manifest / name absent from manifest
// ---------------------------------------------------------------------------

#[test]
fn row08_fail_closed_missing_dependency() {
    let tmp = TempDir::new().expect("tempdir");
    write_file(
        &tmp.path().join("lakefile.toml"),
        "name = \"orphan\"\n\n\
         [[require]]\nname = \"ghostdep\"\ngit = \"https://example.invalid/ghostdep\"\n\n\
         [[lean_lib]]\nname = \"Orphan\"\n",
    );
    write_file(
        &tmp.path().join("Orphan.lean"),
        "def orphanVal : Nat := 1\n",
    );

    // (a) A declared require with NO manifest refuses to build (the build
    // must not proceed against an unresolved dependency set). Exact variant
    // and message pinned.
    let err = try_build_all(tmp.path()).expect_err("build without a manifest must fail closed");
    assert!(
        matches!(err, LakeError::ManifestMissingForDependencies),
        "pinned error variant, got: {err:?}"
    );
    assert_eq!(
        err.to_string(),
        "lake-manifest.json missing but dependencies are declared"
    );

    // (b) A manifest that does not list the required name fails closed with
    // the dependency's name.
    let mut manifest = LakeManifest::empty();
    manifest.upsert_package(clean_lake::ManifestPackage::Path(PathPackage::new(
        "otherdep", "otherdep",
    )));
    manifest
        .save(&tmp.path().join("lake-manifest.json"))
        .expect("manifest saves");
    let err =
        try_build_all(tmp.path()).expect_err("build with an unsatisfied require must fail closed");
    match err {
        LakeError::DependencyNotFound { name } => assert_eq!(name, "ghostdep"),
        other => panic!("expected DependencyNotFound, got: {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Row 09 — missing stdlib import fails closed; --permissive-imports opt-out
// ---------------------------------------------------------------------------

#[test]
fn row09_missing_stdlib_import_fails_closed_and_permissive_opt_out_continues() {
    let tmp = TempDir::new().expect("tempdir");
    write_file(
        &tmp.path().join("lakefile.toml"),
        "name = \"stdfail\"\n\n[[lean_lib]]\nname = \"Uses\"\n",
    );
    // The imported module cannot exist in ANY toolchain's search paths, so
    // this row is machine-independent (constraint: no dependence on an
    // installed Lean toolchain).
    write_file(
        &tmp.path().join("Uses.lean"),
        "import Init.NoSuchCleanLakeParityModule\ndef usesVal : Type 1 := Type\n",
    );

    // Default: fail-closed. A module must never "build" against a silently
    // incomplete environment; the failure names the import AND the opt-out.
    let result = build_all(tmp.path());
    assert!(
        result.built.is_empty(),
        "nothing may build against a silently incomplete environment: {:?}",
        result.built
    );
    assert_eq!(result.failed.len(), 1, "exactly one failed module");
    let (module, reason) = &result.failed[0];
    assert_eq!(module, "Uses");
    assert!(
        reason.contains("Init.NoSuchCleanLakeParityModule"),
        "failure names the missing import: {reason}"
    );
    assert!(
        reason.contains("--permissive-imports"),
        "failure names the opt-out flag: {reason}"
    );

    // Explicit opt-out: warn and continue.
    let result = build_all_with(
        tmp.path(),
        BuildOptions::new().with_permissive_imports(true),
    );
    assert!(
        result.failed.is_empty(),
        "permissive mode must warn and continue: {:?}",
        result.failed
    );
    assert_eq!(
        result.built,
        vec!["Uses"],
        "module builds under the opt-out"
    );
}

// ---------------------------------------------------------------------------
// Row 10 — lake init lib template builds (toolchain + scaffold pinned)
// ---------------------------------------------------------------------------

#[test]
fn row10_init_lib_template_builds() {
    let tmp = TempDir::new().expect("tempdir");
    let dir = tmp.path().join("mylib");

    let msg = run_lake(&LakeCommand::Init(InitArgs::lib_project(
        Some(dir.clone()),
        "ParityLib",
    )))
    .expect("init lib should succeed");
    assert!(
        msg.contains("ParityLib"),
        "summary names the project: {msg}"
    );

    // Template pins: the toolchain is Clean's own (never a Lean 4 identifier),
    // and the scaffold module carries the pinned starter definition.
    let toolchain = fs::read_to_string(dir.join("lean-toolchain")).expect("toolchain written");
    assert_eq!(toolchain, "clean\n", "pinned init toolchain");
    let module = fs::read_to_string(dir.join("ParityLib.lean")).expect("scaffold written");
    assert!(
        module.contains("def hello := \"world\""),
        "pinned lib scaffold: {module}"
    );

    // The template is not just parseable — it BUILDS.
    let result = build_all(&dir);
    assert_eq!(result.built, vec!["ParityLib"], "scaffold module builds");
    assert!(result.failed.is_empty(), "no failures: {:?}", result.failed);
    let ws = Workspace::load(&dir).expect("workspace reloads");
    assert_olean_triple(&ws, "ParityLib");
}

// ---------------------------------------------------------------------------
// Row 11 — lake init exe template builds (scaffold content pinned)
// ---------------------------------------------------------------------------

#[test]
fn row11_init_exe_template_builds() {
    let tmp = TempDir::new().expect("tempdir");
    let dir = tmp.path().join("myexe");

    run_lake(&LakeCommand::Init(InitArgs::exe_project(
        Some(dir.clone()),
        "parityexe",
    )))
    .expect("init exe should succeed");

    // Scaffold pins: greeting is interpolated (no `{name}` residue — a
    // regression the CLI unit tests also pin) and the root is Main.lean.
    let main_module = fs::read_to_string(dir.join("Main.lean")).expect("scaffold written");
    assert!(
        main_module.contains("Hello, parityexe!"),
        "pinned exe scaffold greeting: {main_module}"
    );
    assert!(
        !main_module.contains("{name}"),
        "template placeholder must be resolved: {main_module}"
    );

    // The template BUILDS (IO.println against the initialized IO ops).
    let result = build_all(&dir);
    assert_eq!(result.built, vec!["Main"], "scaffold root module builds");
    assert!(result.failed.is_empty(), "no failures: {:?}", result.failed);
    let ws = Workspace::load(&dir).expect("workspace reloads");
    assert_olean_triple(&ws, "Main");
}

// ---------------------------------------------------------------------------
// Row 12 — strict-lakefile rejection of an unmodeled top-level construct
// ---------------------------------------------------------------------------

#[test]
fn row12_strict_lakefile_rejects_unmodeled_construct_and_lenient_records_it() {
    // Line 6 is the `target` declaration (pinned below).
    const CONTENT: &str = "import Lake\nopen Lake DSL\n\npackage demo\n\n\
                           target customStep pkg : Unit := do\n  pure ()\n\nlean_lib Demo\n";

    // Strict mode: hard error naming the construct and its line, so
    // programmatic lakefiles can never silently under-parse.
    let result = LakeConfig::parse_with_mode(CONTENT, LakefileParseMode::Strict);
    match result {
        Err(LakeError::UnrecognizedConstructs { count, summary }) => {
            assert_eq!(count, 1, "exactly the target declaration is rejected");
            assert!(
                summary.contains("line 6: `target`"),
                "summary pins construct and line: {summary}"
            );
        }
        other => panic!("expected UnrecognizedConstructs, got: {other:?}"),
    }

    // Lenient control: same content parses, with the skipped construct
    // accounted for EXACTLY once (head line only, no continuation entries).
    let config = LakeConfig::parse(CONTENT).expect("lenient parse should succeed");
    assert_eq!(config.package.name, "demo");
    assert_eq!(
        config.libs.len(),
        1,
        "the lib after the target still parses"
    );
    let heads: Vec<(usize, &str)> = config
        .diagnostics
        .iter()
        .map(|skipped| (skipped.line, skipped.token.as_str()))
        .collect();
    assert_eq!(
        heads,
        vec![(6, "target")],
        "exact skipped-construct account"
    );
}

// ---------------------------------------------------------------------------
// Row 13 — lake test without test targets errors honestly
// ---------------------------------------------------------------------------

#[test]
fn row13_lake_test_without_targets_errors_honestly() {
    let tmp = TempDir::new().expect("tempdir");
    write_file(
        &tmp.path().join("lakefile.lean"),
        "package testless\nlean_lib Testless\n",
    );
    write_file(&tmp.path().join("Testless.lean"), "def t : Nat := 0\n");

    // No lean_test declared: the verb must ERROR, never report a vacuous
    // green test run (the honesty half of the `lake test` contract).
    let err = run_lake(&LakeCommand::Test(test_args(tmp.path(), None)))
        .expect_err("test without test targets must error");
    assert!(
        matches!(err, LakeError::InvalidConfig(_)),
        "pinned error variant, got: {err:?}"
    );
    assert!(
        err.to_string().contains("no test targets defined"),
        "error states the real cause: {err}"
    );
}

// ---------------------------------------------------------------------------
// Row 14 — lake test with a target builds and reports the missing driver
// ---------------------------------------------------------------------------

#[test]
fn row14_lake_test_with_target_builds_and_reports_missing_driver_honestly() {
    let tmp = TempDir::new().expect("tempdir");
    write_file(
        &tmp.path().join("lakefile.lean"),
        "package testpkg\n\nlean_test unit where\n  root := `Test.Unit\n",
    );
    write_file(
        &tmp.path().join("Test/Unit.lean"),
        "def main : IO Unit := pure ()\n",
    );

    // GAP row (pinned, honest): the test target BUILDS, but with no native
    // runtime in this crate no driver binary exists — the summary must say
    // so rather than claim the tests executed. Upgrade this row to spawn the
    // driver and assert its exit code when native emission lands here.
    let msg = run_lake(&LakeCommand::Test(test_args(tmp.path(), Some("unit"))))
        .expect("test should build the target and report the driver state");
    assert!(msg.contains("Running 1 test target(s)"), "summary: {msg}");
    assert!(
        msg.contains("Test 'unit'"),
        "summary names the target: {msg}"
    );
    assert!(
        msg.contains("no native executable artifact was found"),
        "summary must report the missing driver honestly: {msg}"
    );
    assert!(
        !msg.contains("Would run:"),
        "no run command may be claimed without a driver artifact: {msg}"
    );
}
