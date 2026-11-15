// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source-level constructor simproc scope, checked against the pinned oracle.
//! The historical world tests use the existing declared 4.8 frontend profile;
//! they make no claim to replay a second installed Lean binary.

use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::{Environment, LeanWorld, Name};
use clean_parser::parse_file;
use std::path::Path;
use std::process::Command;

const POSITIVE: &str = include_str!("fixtures/constructor_simproc/positive.lean");
const NEGATIVE: &[(&str, &str)] = &[
    ("no_implicit_ne", "theorem bad (n : Nat) : (none : Option Nat) ≠ some n := by simp only [reduceCtorEq]"),
    ("erased_ne", "theorem bad (n : Nat) : (none : Option Nat) ≠ some n := by simp [-reduceCtorEq]"),
    ("erased_all", "theorem bad (n : Nat) (h : (none : Option Nat) = some n) : False := by simp_all only [-reduceCtorEq]"),
    ("erased_wildcard", "theorem bad (n : Nat) (h : (none : Option Nat) = some n) : False := by simp only [reduceCtorEq, -reduceCtorEq] at *"),
    ("erased_simpa", "theorem bad (n : Nat) : ((none : Option Nat) = some n) = False := by simpa only [-reduceCtorEq]"),
    ("empty", "theorem bad (n : Nat) (h : (none : Option Nat) = some n) : False := by simp only at h"),
    ("erased_only", "theorem bad (n : Nat) (h : (none : Option Nat) = some n) : False := by simp only [reduceCtorEq, -reduceCtorEq] at h"),
    ("erased_default", "theorem bad (n : Nat) (h : (none : Option Nat) = some n) : False := by simp [-reduceCtorEq] at h"),
    ("same_constructor", "theorem bad (n m : Nat) (h : (some n : Option Nat) = some m) : n = m := by simp only [reduceCtorEq] at h"),
    ("semireducible", "def ctorNone : Option Nat := none\ntheorem bad (n : Nat) (h : ctorNone = some n) : False := by simp only [reduceCtorEq] at h"),
    ("global_shadow", "namespace Shadow\ntheorem reduceCtorEq : True := True.intro\ntheorem bad (n : Nat) (h : (none : Option Nat) = some n) : False := by simp only [reduceCtorEq] at h\nend Shadow"),
    ("false_proof", "theorem bad (n : Nat) : (some n : Option Nat) = none := by simp only [reduceCtorEq]"),
];

fn failure(result: &ElabResult) -> Option<String> {
    match result {
        ElabResult::Failed { error, .. } => Some(error.to_string()),
        ElabResult::Multiple(results) => results.iter().find_map(failure),
        _ => None,
    }
}

fn elaborate(
    source: &str,
    environment_world: Option<&str>,
    explicit_oracle: bool,
) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    if let Some(world) = environment_world {
        clean_olean::declare_environment_world(&mut env, world).map_err(|e| e.to_string())?;
    }
    let mut file = FileContext::new();
    if explicit_oracle {
        let path = Path::new("ConstructorSimproc.lean");
        let choice = clean_olean::source_world_for_file(path, Some(LeanWorld::ORACLE))
            .map_err(|e| e.to_string())?;
        file.set_source_world(path, &choice);
    }
    let decls = parse_file(source).map_err(|e| e.to_string())?;
    assert!(!decls.is_empty());
    for decl in decls {
        let decl = preprocess_decl_with_context(&decl, &mut file);
        let result = elaborate_decl_and_register_with_context(&mut env, &decl, &mut file)
            .map_err(|e| e.to_string())?;
        if let Some(error) = failure(&result) {
            return Err(error);
        }
    }
    Ok(env)
}

fn oracle(source: &str) -> std::process::Output {
    let dir = tempfile::tempdir().expect("oracle directory");
    let path = dir.path().join("Probe.lean");
    std::fs::write(&path, source).expect("oracle source");
    Command::new(clean_olean::pinned_lean_binary().expect("pinned Lean is required"))
        .arg(&path)
        .current_dir(dir.path())
        .output()
        .expect("run pinned Lean")
}

#[test]
fn constructor_simproc_positive_source_matches_pinned_lean() {
    let output = oracle(POSITIVE);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    let env = elaborate(POSITIVE, None, false).expect("positive simproc source");
    for name in [
        "ctorNamed",
        "ctorDefault",
        "ctorRegisteredName",
        "ctorDefaultReadded",
        "ctorNested",
        "ctorReadded",
        "ctorEqFalse",
        "ctorAll",
        "ctorWildcard",
        "ctorSimpa",
        "ctorAlias",
        "ctorLocalShadow",
    ] {
        let n = Name::from_string(name);
        assert!(env.get_const(&n).expect(name).value.is_some());
        let closure = env.axiom_deps(&n).expect("admitted theorem closure");
        assert!(closure.is_empty(), "{name}: {closure:?}");
    }
}

#[test]
fn constructor_simproc_refusals_match_pinned_lean() {
    for (label, source) in NEGATIVE {
        let output = oracle(source);
        assert!(!output.status.success(), "Lean accepted {label}");
        let oracle_error = String::from_utf8_lossy(&output.stdout);
        assert!(
            oracle_error.contains("simp")
                || oracle_error.contains("unsolved goals")
                || (*label == "erased_simpa" && oracle_error.contains("assumption")),
            "{label}: {oracle_error}"
        );
        let error = elaborate(source, None, false)
            .err()
            .unwrap_or_else(|| panic!("Clean accepted {label}"));
        assert!(
            error.contains("progress")
                || error.contains("unsolved")
                || error.contains("Unsolved")
                || (*label == "erased_simpa" && error.contains("hypothesis")),
            "{label}: {error}"
        );
    }
}

#[test]
fn constructor_simproc_uses_selected_world_before_imports() {
    let empty = NEGATIVE
        .iter()
        .find(|(name, _)| *name == "empty")
        .expect("empty-only control")
        .1;
    elaborate(empty, Some("v4.8.0"), false).expect("historical always-on constructor step");
    let error = elaborate(empty, Some("v4.8.0"), true)
        .expect_err("explicit oracle must override the legacy fallback");
    assert!(error.contains("progress"), "{error}");
    elaborate(POSITIVE, Some("v4.8.0"), true)
        .expect("the selected oracle recognizes the builtin name before imports");
    let error = elaborate("theorem bad (n : Nat) (h : (none : Option Nat) = some n) : False := by simp only [reduceCtorEq] at h", Some("v4.8.0"), false)
        .expect_err("4.8 has no reduceCtorEq builtin name");
    assert!(
        error.contains("reduceCtorEq") && (error.contains("Unknown") || error.contains("unknown")),
        "{error}"
    );
}
