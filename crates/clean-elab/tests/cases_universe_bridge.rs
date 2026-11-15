// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Solved elaborator universes must cross the term-to-tactic boundary.
//! The imported oracle is mandatory; no source failure is silently skipped.
use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;
use std::process::Command;

const POSITIVE: &str = include_str!("fixtures/cases_universe_bridge/positive.lean");

fn failure(result: &ElabResult) -> Option<String> {
    match result {
        ElabResult::Failed { error, .. } => Some(error.to_string()),
        ElabResult::Multiple(results) => results.iter().find_map(failure),
        _ => None,
    }
}

fn elaborate(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    let mut context = FileContext::new();
    let decls = parse_file(source).map_err(|e| e.to_string())?;
    assert!(!decls.is_empty());
    for decl in decls {
        let decl = preprocess_decl_with_context(&decl, &mut context);
        let result = elaborate_decl_and_register_with_context(&mut env, &decl, &mut context)
            .map_err(|e| e.to_string())?;
        if let Some(error) = failure(&result) {
            return Err(error);
        }
    }
    Ok(env)
}

fn oracle(source: &str) -> std::process::Output {
    let dir = tempfile::tempdir().expect("oracle directory");
    let file = dir.path().join("Probe.lean");
    std::fs::write(&file, source).expect("write oracle source");
    Command::new(clean_olean::pinned_lean_binary().expect("pinned Lean is required"))
        .arg(file)
        .current_dir(dir.path())
        .output()
        .expect("run pinned Lean")
}

#[test]
fn solved_universes_cross_the_cases_term_bridge() {
    let independent = oracle(POSITIVE);
    assert!(
        independent.status.success(),
        "{}",
        String::from_utf8_lossy(&independent.stdout)
    );
    let env = elaborate(POSITIVE)
        .expect("the elaborated target's solved universes must cross into cases");
    for text in [
        "autoCases",
        "explicitCases",
        "choose",
        "typesCases",
        "nestedCases",
        "matchedCases",
        "inferredHave",
        "inductionTarget",
    ] {
        let name = Name::from_string(text);
        assert!(env.get_const(&name).expect(text).value.is_some());
        assert!(
            env.axiom_deps(&name).expect("axiom closure").is_empty(),
            "{text}"
        );
    }
}

#[test]
fn cases_bridge_preserves_false_proof_and_rigid_universe_refusals() {
    let prefix = POSITIVE
        .split("theorem autoCases")
        .next()
        .expect("pick definition");
    for (label, wrong) in [
        ("false_proof", "theorem bad (xs : List α) (i : Nat) : False := by\n  cases hx : pick xs i with\n  | none => exact True.intro\n  | some a => exact True.intro"),
        ("rigid_universe", "def bad {α : Type u} (xs : List α) (i : Nat) : Type u := by\n  cases hx : pick xs i with\n  | none => exact Type u\n  | some a => exact Type u"),
    ] {
        let source = format!("{prefix}\n{wrong}");
        let independent = oracle(&source);
        assert!(!independent.status.success(), "Lean accepted {label}");
        let error = elaborate(&source).expect_err("wrong branch must be rejected");
        assert!(error.contains("mismatch") || error.contains("Mismatch"), "{label}: {error}");
        if label == "false_proof" {
            assert!(error.contains("True") && error.contains("False"), "{error}");
        }
        eprintln!("{label}: {error}");
    }
}
