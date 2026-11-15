// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
//! Equality proof expressions must rewrite dependent hypotheses through checked elimination.
use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::{Environment, LeanWorld, Name};
use clean_parser::parse_file_with_diagnostics;
use std::collections::BTreeSet;
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.Data.Option.Basic\n";
const PREAMBLE: &str = r"
namespace EquationExpression
structure D where
  n : Nat
def one : D := ⟨1⟩
";
const POSITIVE: &str = r"
theorem direct (d : D) (h : one = d) (hn : d.n = 0) : False := by
  cases h
  cases hn
theorem injected (d : D) (h : some one = some d) (hn : d.n = 0) : False := by
  cases Option.some.inj h
  cases hn
theorem localdef (d : D) (h : some one = some d) (hn : d.n = 0) : False := by
  have h' : one = d := Option.some.inj h
  cases h'
  cases hn
theorem target (d : D) (h : some one = some d) : d.n = 1 := by
  cases Option.some.inj h
  rfl
theorem siblings (d : D) (h : some one = some d) (hn : d.n = 0) : False ∧ False := by
  constructor
  cases Option.some.inj h
  cases hn
  cases Option.some.inj h
  cases hn
end EquationExpression
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
    let path = std::path::Path::new("/tmp/clean-equation-expressions.lean");
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
fn equation_expressions_rewrite_dependent_contexts() {
    let source = format!("{HEADER}{PREAMBLE}{POSITIVE}");
    let lean = oracle(&source);
    assert!(
        lean.status.success(),
        "{}",
        String::from_utf8_lossy(&lean.stdout)
    );
    let targets = [
        "EquationExpression.direct",
        "EquationExpression.injected",
        "EquationExpression.localdef",
        "EquationExpression.target",
        "EquationExpression.siblings",
    ];
    let env = elaborate(&source, &targets)
        .expect("eliminate an equality expression in dependent contexts");
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
fn equation_expressions_do_not_establish_false_conclusions() {
    for body in [
        "theorem bad (d : D) (h : some one = some d) (hn : d.n = 1) : False := by\n  cases Option.some.inj h\n  cases hn",
        "theorem bad (d : D) (h : some one = some d) : d.n = 2 := by\n  cases Option.some.inj h\n  rfl",
    ] {
        let source = format!("{HEADER}{PREAMBLE}{body}\nend EquationExpression\n");
        assert!(
            !oracle(&source).status.success(),
            "Lean accepted a false control"
        );
        assert!(
            elaborate(&source, &["EquationExpression.bad"]).is_err(),
            "false conclusion accepted"
        );
    }
}
