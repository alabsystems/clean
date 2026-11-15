// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
//! Named-argument slots participate in expected-type propagation.
use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::{Environment, LeanWorld, Name};
use clean_parser::parse_file_with_diagnostics;
use std::collections::BTreeSet;
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.Data.List.Basic\n";
const PREAMBLE: &str = r"
namespace Expected

def lookup : List Nat → Nat → Option Nat
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, i + 1 => lookup xs i
inductive At : List Nat → Nat → Nat → Prop where
  | intro {xs i value} : lookup xs i = some value → At xs i value
theorem at_twice {xs i value} (h : lookup xs i = some value) : At xs i value ∧ At xs i value :=
  ⟨At.intro h, At.intro h⟩
";
const POSITIVE: &str = r"
theorem ordinary : At [1] 0 1 ∧ At [1] 0 1 := at_twice rfl
theorem named_value : At [1] 0 1 ∧ At [1] 0 1 := at_twice (value := 1) rfl
theorem named_index : At [1] 0 1 ∧ At [1] 0 1 := at_twice (i := 0) rfl
theorem named_both : At [1] 0 1 ∧ At [1] 0 1 := at_twice (value := 1) (i := 0) rfl
theorem named_explicit : At [1] 0 1 ∧ At [1] 0 1 := @at_twice (xs := [1]) 0 1 rfl
end Expected
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
    let path = std::path::Path::new("/tmp/clean-named-expected-type.lean");
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
fn named_slots_propagate_expected_types() {
    let source = format!("{HEADER}{PREAMBLE}{POSITIVE}");
    let lean = oracle(&source);
    assert!(
        lean.status.success(),
        "{}",
        String::from_utf8_lossy(&lean.stdout)
    );
    let targets = [
        "Expected.ordinary",
        "Expected.named_value",
        "Expected.named_index",
        "Expected.named_both",
        "Expected.named_explicit",
    ];
    let env = elaborate(&source, &targets).expect("expected type across named slots");
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
fn named_slots_still_reject_inconsistent_results() {
    for body in [
        "theorem bad : At [2] 0 2 ∧ At [2] 0 2 := at_twice (value := 1) rfl",
        "theorem bad : At [1] 1 1 ∧ At [1] 1 1 := at_twice (i := 0) rfl",
        "theorem bad : At [] 0 1 ∧ At [] 0 1 := at_twice (value := 1) rfl",
    ] {
        let source = format!("{HEADER}{PREAMBLE}{body}\nend Expected\n");
        assert!(
            !oracle(&source).status.success(),
            "Lean accepted invalid indices"
        );
        assert!(
            elaborate(&source, &["Expected.bad"]).is_err(),
            "invalid result accepted: {body}"
        );
    }
}
