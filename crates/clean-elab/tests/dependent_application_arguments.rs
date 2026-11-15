// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
//! Earlier application arguments determine reductions needed by later ones.
use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::{Environment, LeanWorld, Name};
use clean_parser::parse_file_with_diagnostics;
use std::collections::BTreeSet;
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.Data.List.Basic\n";
const PREAMBLE: &str = r"
namespace Fields
inductive E where
  | atom : Nat → E
  | params : List Nat → E
def lookup : List Nat → Nat
  | [] => 0
  | x :: _ => x
inductive Statement where
  | typed : E → E → Statement
inductive J : Statement → Prop where
  | intro {xs : List Nat} : xs.length = 1 → J (.typed (.params xs) (.atom (lookup xs)))
theorem intro {xs : List Nat} (h : xs.length = 1) : J (.typed (.params xs) (.atom (lookup xs))) := J.intro h
";
const POSITIVE: &str = r"
theorem direct : J (.typed (.params [7]) (.atom 7)) := J.intro rfl
theorem through_theorem : J (.typed (.params [9]) (.atom 9)) := intro rfl
theorem explicit : J (.typed (.params [7]) (.atom 7)) := intro (xs := [_]) rfl
end Fields
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
    let path = std::path::Path::new("/tmp/clean-dependent-app-arguments.lean");
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
    let result = gate.check(&env, &roots);
    if !result.passed(false) {
        return Err(result.refusal_summary(false));
    }
    Ok(env)
}

fn oracle(source: &str) -> std::process::Output {
    let dir = tempfile::tempdir().expect("oracle directory");
    let path = dir.path().join("Probe.lean");
    std::fs::write(&path, source).expect("write source");
    Command::new(clean_olean::pinned_lean_binary().expect("pinned Lean"))
        .arg(path)
        .current_dir(dir.path())
        .output()
        .expect("run Lean")
}

#[test]
fn earlier_arguments_refresh_later_dependent_computations() {
    let source = format!("{HEADER}{PREAMBLE}{POSITIVE}");
    let lean = oracle(&source);
    assert!(
        lean.status.success(),
        "{}",
        String::from_utf8_lossy(&lean.stdout)
    );
    let targets = ["Fields.direct", "Fields.through_theorem", "Fields.explicit"];
    let env = elaborate(&source, &targets).expect("infer list before computing its head");
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
fn dependent_computation_disagreements_remain_rejected() {
    for body in [
        "theorem bad : J (.typed (.params [7]) (.atom 8)) := J.intro rfl",
        "theorem bad : J (.typed (.params [7, 8]) (.atom 7)) := J.intro rfl",
        "theorem bad : J (.typed (.params []) (.atom 0)) := J.intro rfl",
    ] {
        let source = format!("{HEADER}{PREAMBLE}{body}\nend Fields\n");
        assert!(
            !oracle(&source).status.success(),
            "Lean accepted a false control"
        );
        assert!(
            elaborate(&source, &["Fields.bad"]).is_err(),
            "bad dependent result accepted"
        );
    }
}
