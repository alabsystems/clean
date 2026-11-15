// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Recursive simplification preserves polymorphic calls and proof checking.
//! The imported oracle is mandatory; no source failure is silently skipped.
use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;
use std::process::Command;

const POSITIVE: &str = include_str!("fixtures/polymorphic_recursive_simp/positive.lean");

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
fn recursive_simp_uses_declared_universes() {
    let independent = oracle(POSITIVE);
    assert!(
        independent.status.success(),
        "{}",
        String::from_utf8_lossy(&independent.stdout)
    );
    let env = elaborate(POSITIVE).expect("polymorphic recursive proofs");
    for text in ["polyPick_step", "polyPick_levels"] {
        let name = Name::from_string(text);
        assert!(env.get_const(&name).expect(text).value.is_some());
        assert!(
            env.axiom_deps(&name).expect("axiom closure").is_empty(),
            "{text}"
        );
    }
}

#[test]
fn recursive_simp_refuses_false_conclusion() {
    let source = format!("{POSITIVE}\ntheorem bad {{α : Type u}} (x : α) (xs : List α) (i : Nat) (h : polyPick xs i = some x) : polyPick (x :: xs) (Nat.succ i) = none := by\n  simp only [polyPick, h]\n");
    assert!(
        !oracle(&source).status.success(),
        "Lean accepted false control"
    );
    let error = elaborate(&source).expect_err("false recursive conclusion must fail");
    assert!(
        error.contains("unsolved") || error.contains("progress"),
        "{error}"
    );
}
