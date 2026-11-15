// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! simp_all uses propositional hypotheses and never rewrites a hypothesis by itself.
//! The imported oracle is mandatory; no source failure is silently skipped.
use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;
use std::process::Command;

const POSITIVE: &str = include_str!("fixtures/simp_all_propositions/positive.lean");

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
fn simp_all_uses_propositional_hypotheses() {
    let independent = oracle(POSITIVE);
    assert!(
        independent.status.success(),
        "{}",
        String::from_utf8_lossy(&independent.stdout)
    );
    let env = elaborate(POSITIVE).expect("propositional simp_all proofs");
    for text in [
        "parts",
        "nested",
        "duplicate",
        "shadowed",
        "implication",
        "contradiction",
        "erased_shadow",
        "erased_other",
    ] {
        let name = Name::from_string(text);
        assert!(env.get_const(&name).expect(text).value.is_some());
        let dependencies = env.axiom_deps(&name).expect("axiom closure");
        assert!(
            dependencies
                .iter()
                .all(|a| env.is_canonical_foundational_axiom(a)),
            "{text}: {dependencies:?}"
        );
    }
}

#[test]
fn simp_all_preserves_missing_premises_and_false_goal_refusals() {
    for source in [
        "theorem bad (P Q : Prop) (h : P) : Q := by simp_all only [and_self]",
        "theorem bad (P Q : Prop) (h : P → Q) : Q := by simp_all only [and_self]",
        "theorem bad (P : Prop) (h : P) : False := by simp_all only [and_self]",
        "theorem bad (P Q : Prop) (h : P → Q) (k : Q → P) : P := by simp_all only [and_self]",
        "theorem bad (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by simp_all only [-hp, and_self]",
        "theorem bad (P : Prop) (hp : P) : P := by simp_all only [-hp]",
    ] {
        assert!(
            !oracle(source).status.success(),
            "Lean accepted refusal control"
        );
        let error = match elaborate(source) {
            Ok(_) => panic!("missing or excluded premise must fail: {source}"),
            Err(error) => error,
        };
        assert!(
            error.contains("unsolved") || error.contains("progress"),
            "{error}"
        );
    }
}
