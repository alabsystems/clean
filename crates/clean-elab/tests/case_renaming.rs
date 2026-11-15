// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Case names select the last inaccessible locals; alternatives retain field order.
//! The imported oracle is mandatory; no source failure is silently skipped.
use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;
use std::process::Command;

const POSITIVE: &str = include_str!("fixtures/case_renaming/positive.lean");

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
fn case_names_select_last_inaccessible_locals() {
    let independent = oracle(POSITIVE);
    assert!(
        independent.status.success(),
        "{}",
        String::from_utf8_lossy(&independent.stdout)
    );
    let env = elaborate(POSITIVE).expect("case binder proofs");
    for text in [
        "checked_zero",
        "partial_nat",
        "full_nat",
        "alternative_prefix",
        "earlier_field",
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
fn case_names_preserve_refusals() {
    for source in [
        "theorem bad (n : Nat) : n = n := by\n  cases n\n  case zero extra => rfl\n  case succ k => rfl",
        "theorem bad (n : Nat) : n = 0 := by\n  induction n\n  case zero => rfl\n  case succ ih => exact ih",
    ] {
        assert!(!oracle(source).status.success(), "Lean accepted refusal control");
        let error = elaborate(source).expect_err("invalid case must fail");
        assert!(error.contains("too many") || error.contains("mismatch") || error.contains("unify"), "{error}");
    }
}
