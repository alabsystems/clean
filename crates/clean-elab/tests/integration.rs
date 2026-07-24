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

    fn clean_elab_metadata_artifact() -> PathBuf {
        let deps_dir = std::env::current_exe()
            .expect("integration test should know its executable path")
            .parent()
            .expect("integration test executable should live under target deps")
            .to_path_buf();
        let mut rlibs = Vec::new();
        let mut rmetas = Vec::new();

        for path in fs::read_dir(&deps_dir)
            .expect("deps directory should be readable")
            .filter_map(Result::ok)
            .map(|entry| entry.path())
        {
            let Some(file_name) = path.file_name().and_then(|name| name.to_str()) else {
                continue;
            };
            if !file_name.starts_with("libclean_elab-") {
                continue;
            }

            match path.extension().and_then(|ext| ext.to_str()) {
                Some("rlib") => rlibs.push(path),
                Some("rmeta") => rmetas.push(path),
                _ => {}
            }
        }

        let sort_by_mtime = |artifacts: &mut Vec<PathBuf>| {
            artifacts.sort_by_key(|path| {
                fs::metadata(path)
                    .and_then(|metadata| metadata.modified())
                    .unwrap_or(UNIX_EPOCH)
            });
        };
        sort_by_mtime(&mut rlibs);
        sort_by_mtime(&mut rmetas);

        rlibs
            .pop()
            .or_else(|| rmetas.pop())
            .expect("clean_elab metadata artifact should exist in deps dir")
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
        let artifact = clean_elab_metadata_artifact();
        let deps_dir = artifact
            .parent()
            .expect("clean_elab artifact should live in deps directory");
        let compile_dir = temp_compile_dir(test_name);
        fs::create_dir_all(&compile_dir).expect("compile directory should be creatable");

        let source_path = compile_dir.join("snippet.rs");
        fs::write(&source_path, source).expect("snippet source should be writable");

        let output = Command::new("rustc")
            .arg("--crate-type")
            .arg("lib")
            .arg("--edition")
            .arg("2021")
            .arg("--emit")
            .arg("metadata")
            .arg("--out-dir")
            .arg(&compile_dir)
            .arg(&source_path)
            .arg("--extern")
            .arg(format!("clean_elab={}", artifact.display()))
            .arg("-L")
            .arg(format!("dependency={}", deps_dir.display()))
            .output()
            .expect("rustc should be runnable from integration tests");

        let _ = fs::remove_dir_all(&compile_dir);
        output
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
