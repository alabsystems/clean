// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Generalization preserves explicit, implicit and strict-implicit binder annotations.
//! The imported oracle is mandatory; no source failure is silently skipped.
use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;
use std::process::Command;

const POSITIVE: &str = include_str!("fixtures/induction_binders/positive.lean");

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
fn induction_retains_generalized_binder_annotations() {
    let independent = oracle(POSITIVE);
    assert!(
        independent.status.success(),
        "{}",
        String::from_utf8_lossy(&independent.stdout)
    );
    let env = elaborate(POSITIVE).expect("generalized binders retain their annotation");
    for text in [
        "implicitIH",
        "explicitIH",
        "strictIH",
        "introducedIH",
        "lambdaIH",
        "substitutedIH",
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
fn generalized_binders_do_not_accept_wrong_arguments_or_false_proofs() {
    for source in [
        "theorem bad (n : Nat) (i : Nat) (h : i = 0) : i = 0 := by\n  induction n generalizing i with\n  | zero => exact h\n  | succ n ih => exact ih h",
        "theorem bad (n : Nat) {i : Nat} (h : i = 0) : False := by\n  induction n generalizing i with\n  | zero => exact h\n  | succ n ih => exact ih h",
    ] {
        assert!(!oracle(source).status.success(), "Lean accepted false control");
        let error = elaborate(source).expect_err("invalid proof must be refused");
        assert!(error.contains("mismatch") || error.contains("Mismatch"), "{error}");
    }
}
