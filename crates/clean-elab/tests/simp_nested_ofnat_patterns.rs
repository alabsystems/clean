// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
//! Literal normalization applies inside same-head simp patterns too.
use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::{Environment, LeanWorld, Name};
use clean_parser::parse_file_with_diagnostics;
use std::collections::BTreeSet;
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.SimpLemmas\n";
const POSITIVE: &str = r"
theorem literal_index (P : Nat → Prop) (n : Nat) (h : P (n + 1)) : True ∧ P (n + 1) := by
  simp_all only [and_self]
theorem literal_quantified (P : Nat → Prop) (n : Nat) (h : ∀ k, P (k + 1)) : True ∧ P (n + 1) := by
  simp_all only [and_self]
theorem literal_equality (f : Nat → Nat) (n : Nat) (h : ∀ k, f (k + 1) = k) : f (n + 1) = n := by
  simp only [h]
";

fn failure(result: &ElabResult) -> Option<String> {
    match result {
        ElabResult::Failed { error, .. } => Some(error.to_string()),
        ElabResult::Multiple(results) => results.iter().find_map(failure),
        _ => None,
    }
}

fn elaborate(source: &str, targets: &[&str]) -> Result<Environment, String> {
    let report = parse_file_with_diagnostics(source).map_err(|e| e.to_string())?;
    let path = std::path::Path::new("/tmp/clean-simp-literal-patterns.lean");
    let decision = clean_olean::source_world_for_file(path, Some(LeanWorld::ORACLE))
        .map_err(|e| e.to_string())?;
    let (mut env, mut gate) = clean_elab::module_driver::module_environment_for_header_in_world(
        Default::default(),
        &decision,
        &report.header,
    )
    .map_err(|e| e.to_string())?;
    let mut context = FileContext::new();
    context.set_source_world(path, &decision);
    for decl in report.decls {
        let decl = preprocess_decl_with_context(&decl, &mut context);
        let result = elaborate_decl_and_register_with_context(&mut env, &decl, &mut context)
            .map_err(|e| e.to_string())?;
        if let Some(error) = failure(&result) {
            return Err(error);
        }
    }
    let roots: BTreeSet<Name> = targets.iter().map(|n| Name::from_string(n)).collect();
    let checked = gate.check(&env, &roots);
    if !checked.passed(false) {
        return Err(checked.refusal_summary(false));
    }
    Ok(env)
}

fn oracle(source: &str) -> std::process::Output {
    let dir = tempfile::tempdir().expect("oracle directory");
    let file = dir.path().join("Probe.lean");
    std::fs::write(&file, source).expect("write fixture");
    Command::new(clean_olean::pinned_lean_binary().expect("pinned Lean"))
        .arg(file)
        .current_dir(dir.path())
        .output()
        .expect("run Lean")
}

#[test]
fn same_head_literal_patterns_over_genuine_imports() {
    let source = format!("{HEADER}{POSITIVE}");
    let lean = oracle(&source);
    assert!(
        lean.status.success(),
        "{}",
        String::from_utf8_lossy(&lean.stdout)
    );
    let targets = ["literal_index", "literal_quantified", "literal_equality"];
    let env = elaborate(&source, &targets).expect("same-head numeric patterns");
    for target in targets {
        let name = Name::from_string(target);
        assert!(env.get_const(&name).expect(target).value.is_some());
        assert!(env
            .axiom_deps(&name)
            .expect("closure")
            .iter()
            .all(|a| env.is_canonical_foundational_axiom(a)));
    }
}

#[test]
fn literal_normalization_does_not_change_values() {
    for body in [
        "theorem bad (P : Nat → Prop) (n : Nat) (h : P (n + 1)) : True ∧ P (n + 2) := by simp_all only [and_self]",
        "theorem bad (f : Nat → Nat) (n : Nat) (h : ∀ k, f (k + 1) = k) : f (n + 1) = n + 1 := by simp only [h]",
        "theorem bad (P : Nat → Prop) (n : Nat) (h : P (n + 1)) : False := by simp_all only [and_self]",
    ] {
        let source = format!("{HEADER}{body}\n");
        assert!(!oracle(&source).status.success(), "false Lean control accepted");
        assert!(elaborate(&source, &["bad"]).is_err(), "false control accepted: {body}");
    }
}
