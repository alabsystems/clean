// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests: parse -> elaborate -> type check
//!
//! These tests verify the end-to-end flow from Lean syntax to kernel type checking.
//! Tests are organized into domain-specific modules:
//!
//! - `basic`: Core expression, lambda, let binding, and simple declaration tests
//! - `type_checking`: Definitional equality, error cases, prop/type distinction
//! - `structures`: Structure elaboration and dependent field tests
//! - `macros`: Macro system end-to-end tests
//! - `tactics`: Arithmetic tactics (mathverse, linarith) and Qq metaprogramming
//! - `matp_bench`: MATP-BENCH regression tests for mathematical problems
//! - `putnam_bench`: PutnamBench baseline compatibility tests (#8)
//! - `regressions`: Issue-specific regression tests

#[path = "integration/common.rs"]
mod common;

#[path = "integration/basic.rs"]
mod basic;
#[path = "integration/import_e2e_class_hierarchy_tests.rs"]
mod import_e2e_class_hierarchy_tests;
#[path = "integration/import_e2e_coercion_tests.rs"]
mod import_e2e_coercion_tests;
#[path = "integration/import_e2e_cross_module_tests.rs"]
mod import_e2e_cross_module_tests;
#[path = "integration/import_e2e_def_unfold_tests.rs"]
mod import_e2e_def_unfold_tests;
#[path = "integration/import_e2e_diamond_instance_tests.rs"]
mod import_e2e_diamond_instance_tests;
#[path = "integration/import_e2e_instance_method_tests.rs"]
mod import_e2e_instance_method_tests;
#[path = "integration/import_e2e_param_recursor_tests.rs"]
mod import_e2e_param_recursor_tests;
#[path = "integration/import_e2e_simp_imported_tests.rs"]
mod import_e2e_simp_imported_tests;
#[path = "integration/import_elab_e2e_tests.rs"]
mod import_elab_e2e_tests;
#[path = "integration/lean4_phase1_compat.rs"]
mod lean4_phase1_compat;
#[path = "integration/macros.rs"]
mod macros;
#[path = "integration/match_universe.rs"]
mod match_universe;
#[path = "integration/matp_bench.rs"]
mod matp_bench;
#[path = "integration/obtain_surface.rs"]
mod obtain_surface;
#[path = "integration/or_pattern_surface.rs"]
mod or_pattern_surface;
#[path = "integration/phase1_corpus_common.rs"]
mod phase1_corpus_common;
#[path = "integration/putnam_bench.rs"]
mod putnam_bench;
#[path = "integration/rcases_clear_surface.rs"]
mod rcases_clear_surface;
#[path = "integration/rcases_surface.rs"]
mod rcases_surface;
#[path = "integration/refine_holes_surface.rs"]
mod refine_holes_surface;
#[path = "integration/regressions.rs"]
mod regressions;
#[path = "integration/rintro_surface.rs"]
mod rintro_surface;
#[path = "integration/rwa_surface.rs"]
mod rwa_surface;
#[path = "integration/structural_recursion.rs"]
mod structural_recursion;
#[path = "integration/structures.rs"]
mod structures;
#[path = "integration/tactics.rs"]
mod tactics;
#[path = "integration/type_checking.rs"]
mod type_checking;

#[cfg(feature = "ay-smt")]
mod smt_api_surface {
    use std::fs;
    use std::path::PathBuf;
    use std::process::{Command, Output};
    use std::time::{SystemTime, UNIX_EPOCH};

    fn clean_elab_metadata_artifact() -> (PathBuf, Vec<PathBuf>) {
        let executable =
            std::env::current_exe().expect("integration test should know its executable path");
        let directory = executable.parent().expect("test executable has a parent");
        let mut directories = Vec::new();
        if directory.file_name().is_some_and(|name| name == "deps") {
            directories.push(directory.to_path_buf());
        } else {
            // Native Targo: <profile>/build/<package>/<unit>/out/<test>.
            // Do not search unrelated profiles, caches or worktrees.
            assert_eq!(directory.file_name().and_then(|n| n.to_str()), Some("out"));
            let package = directory
                .parent()
                .and_then(|p| p.parent())
                .expect("native test output has a package directory");
            assert_eq!(
                package.file_name().and_then(|n| n.to_str()),
                Some("clean-elab")
            );
            let build = package
                .parent()
                .expect("native package has a build directory");
            assert_eq!(build.file_name().and_then(|n| n.to_str()), Some("build"));
            for package in fs::read_dir(build).expect("native build directory is readable") {
                let package = package.expect("native package entry is readable").path();
                if !package.is_dir() {
                    continue;
                }
                for unit in fs::read_dir(package).expect("native package directory is readable") {
                    let output = unit
                        .expect("native unit entry is readable")
                        .path()
                        .join("out");
                    if output.is_dir() {
                        directories.push(output);
                    }
                }
            }
        }
        directories.sort();
        let mut libraries = Vec::new();
        for directory in &directories {
            for entry in fs::read_dir(directory).expect("dependency directory is readable") {
                let path = entry.expect("dependency entry is readable").path();
                if path
                    .file_name()
                    .and_then(|n| n.to_str())
                    .is_some_and(|n| n.starts_with("libclean_elab-"))
                    && path
                        .extension()
                        .is_some_and(|extension| extension == "rlib")
                {
                    libraries.push(path);
                }
            }
        }
        // An arbitrary newest artifact could test a different feature set or
        // source. Refuse ambiguity rather than silently testing another API.
        assert_eq!(
            libraries.len(),
            1,
            "expected exactly one built clean_elab rlib: {libraries:?}"
        );
        (libraries.remove(0), directories)
    }

    fn temp_compile_dir(test_name: &str) -> PathBuf {
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system clock should be after UNIX_EPOCH")
            .as_nanos();
        std::env::temp_dir().join(format!(
            "clean_elab_api_surface_{test_name}_{}_{}",
            std::process::id(),
            nanos
        ))
    }

    fn compile_external_snippet(test_name: &str, source: &str) -> Output {
        let (artifact, dependency_directories) = clean_elab_metadata_artifact();
        let compile_dir = temp_compile_dir(test_name);
        fs::create_dir_all(&compile_dir).expect("compile directory should be creatable");

        let source_path = compile_dir.join("snippet.rs");
        fs::write(&source_path, source).expect("snippet source should be writable");

        // Compile with the same compiler Targo used for this test binary: an
        // unrelated compiler cannot consume the test's rlib metadata. `RUSTC`
        // when exported, else the `trustc` beside `$CARGO` (targo exports its
        // own path), else `trustc` on PATH -- never a stock `rustc` (owner
        // directive 2026-09-28). The snippet is a throwaway API-surface probe,
        // not a verification target, so it opts out of Trust verification.
        let rustc = std::env::var_os("RUSTC").unwrap_or_else(|| {
            std::env::var_os("CARGO")
                .map(|cargo| PathBuf::from(cargo).with_file_name("trustc"))
                .filter(|trustc| trustc.is_file())
                .map_or_else(|| "trustc".into(), PathBuf::into_os_string)
        });
        let mut compiler = Command::new(rustc);
        for directory in dependency_directories {
            compiler
                .arg("-L")
                .arg(format!("dependency={}", directory.display()));
        }
        let output = compiler
            .arg("-Ztrust-verify=off")
            .arg("--crate-type")
            .arg("lib")
            .arg("--edition")
            .arg("2021")
            .arg("--emit")
            .arg("metadata")
            .arg("--error-format=json")
            .arg("--out-dir")
            .arg(&compile_dir)
            .arg(&source_path)
            .arg("--extern")
            .arg(format!("clean_elab={}", artifact.display()))
            .output()
            .expect("Targo's trustc should be runnable from integration tests");

        let _ = fs::remove_dir_all(&compile_dir);
        output
    }

    fn assert_external_error(output: &Output, expected: &[&str]) {
        assert_eq!(
            output.status.code(),
            Some(1),
            "compiler must report a normal error exit"
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        let mut observed = Vec::new();
        for line in stderr.lines() {
            let Ok(diagnostic) = serde_json::from_str::<serde_json::Value>(line) else {
                continue;
            };
            if diagnostic["level"] != "error" {
                continue;
            }
            if let Some(code) = diagnostic["code"]["code"].as_str() {
                assert!(
                    expected.contains(&code),
                    "unrelated compiler error {code}: {stderr}"
                );
                observed.push(code.to_owned());
            }
        }
        assert!(
            !observed.is_empty(),
            "missing expected API error {expected:?}: {stderr}"
        );
    }

    fn assert_external_compile_succeeds(test_name: &str, source: &str) {
        let output = compile_external_snippet(test_name, source);
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        assert!(
            output.status.success(),
            "snippet failed to compile\nsource:\n{source}\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
    }

    #[test]
    fn test_smt_solver_wrapper_types_are_not_nameable_from_public_api() {
        let output = compile_external_snippet(
            "private_solver_wrapper_types",
            r#"
#![allow(unused_imports)]
use clean_elab::tactic::smt::{SmtProveOutcome, SmtSolver};
"#,
        );
        assert_external_error(&output, &["E0432", "E0603"]);
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        assert!(
            !output.status.success(),
            "snippet unexpectedly compiled successfully\nsource:\n{}\nstdout:\n{stdout}\nstderr:\n{stderr}",
            r#"
#![allow(unused_imports)]
use clean_elab::tactic::smt::{SmtProveOutcome, SmtSolver};
"#,
        );
        assert!(
            stderr.contains("SmtSolver"),
            "expected rustc stderr to mention SmtSolver\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(
            stderr.contains("SmtProveOutcome"),
            "expected rustc stderr to mention SmtProveOutcome\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
        assert!(
            stderr.contains("private") || stderr.contains("unresolved imports"),
            "expected rustc stderr to show a privacy/import failure\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
    }

    #[test]
    fn test_smt_translate_internals_are_not_nameable_from_public_api() {
        let cases = [
            (
                "private_smt_translate_translator",
                r#"
#![allow(unused_imports)]
use clean_elab::tactic::smt_translate::SmtLibTranslator;
"#,
                "SmtLibTranslator",
            ),
            (
                "private_smt_translate_sort",
                r#"
#![allow(unused_imports)]
use clean_elab::tactic::smt_translate::SmtSort;
"#,
                "SmtSort",
            ),
            (
                "private_smt_translate_var_decl",
                r#"
#![allow(unused_imports)]
use clean_elab::tactic::smt_translate::SmtVarDecl;
"#,
                "SmtVarDecl",
            ),
            (
                "private_smt_translate_error",
                r#"
#![allow(unused_imports)]
use clean_elab::tactic::smt_translate::TranslateError;
"#,
                "TranslateError",
            ),
        ];

        for (test_name, source, symbol) in cases {
            let output = compile_external_snippet(test_name, source);
            assert_external_error(&output, &["E0432", "E0603"]);
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);

            assert!(
                !output.status.success(),
                "smt_translate internal type should not be importable from external crates\nsource:\n{source}\nstdout:\n{stdout}\nstderr:\n{stderr}"
            );
            assert!(
                stderr.contains(symbol),
                "expected rustc stderr to mention `{symbol}`\nsource:\n{source}\nstdout:\n{stdout}\nstderr:\n{stderr}"
            );
            assert!(
                stderr.contains("private") || stderr.contains("unresolved imports"),
                "expected rustc stderr to show a privacy/import failure\nsource:\n{source}\nstdout:\n{stdout}\nstderr:\n{stderr}"
            );
        }
    }

    #[test]
    fn test_supported_tactic_smt_api_surface_remains_public() {
        assert_external_compile_succeeds(
            "public_smt_api_surface",
            r#"
#![allow(unused_imports)]
use clean_elab::tactic::smt::{
    ay_decide, ay_smt, SmtVerifyPolicy, AyConfig, AyProofConfig,
};
"#,
        );
    }

    #[test]
    fn test_trimmed_ay_config_helpers_are_not_callable_from_public_api() {
        let cases = [
            (
                "trimmed_ay_config_enable_proofs",
                r#"
use clean_elab::tactic::smt::AyConfig;

pub fn attempt_trimmed_helpers() {
    let _ = AyConfig::default().enable_proofs();
}
"#,
                "enable_proofs",
            ),
            (
                "trimmed_ay_config_without_timeout",
                r#"
use clean_elab::tactic::smt::AyConfig;

pub fn attempt_trimmed_helpers() {
    let _ = AyConfig::default().without_timeout();
}
"#,
                "without_timeout",
            ),
            (
                "trimmed_ay_config_trigger_policy",
                r#"
use clean_elab::tactic::smt::AyConfig;

pub fn attempt_trimmed_helpers() {
    let _ = AyConfig::default().trigger_policy();
}
"#,
                "trigger_policy",
            ),
            (
                "trimmed_ay_config_with_trigger_policy",
                r#"
use clean_elab::tactic::smt::AyConfig;

pub fn attempt_trimmed_helpers() {
    let _ = AyConfig::default().with_trigger_policy(panic!());
}
"#,
                "with_trigger_policy",
            ),
        ];

        for (test_name, source, symbol) in cases {
            let output = compile_external_snippet(test_name, source);
            assert_external_error(&output, &["E0599"]);
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);

            assert!(
                !output.status.success(),
                "trimmed AyConfig helper should not be callable from external crates\nsource:\n{source}\nstdout:\n{stdout}\nstderr:\n{stderr}"
            );
            assert!(
                stderr.contains(symbol),
                "expected rustc stderr to mention `{symbol}`\nsource:\n{source}\nstdout:\n{stdout}\nstderr:\n{stderr}"
            );
        }
    }
}
