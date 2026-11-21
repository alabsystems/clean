// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
//! Compound indices must constrain branches of indexed case elimination.
use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::{Environment, LeanWorld, Name};
use clean_parser::parse_file_with_diagnostics;
use std::collections::BTreeSet;
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.Data.List.Basic\nimport Init.NotationExtra\n";
const PREAMBLE: &str = r"
namespace IndexCases
inductive Diagonal : Nat → Nat → Prop where
  | same (n : Nat) : Diagonal n n
inductive Witness (a : Nat) : Nat → Prop where
  | mk (m : Nat) (h : a = m) : Witness a m
";
const POSITIVE: &str = r"
theorem nil_auto {α : Type u} {a : α} : ¬ a ∈ ([] : List α) := by
  intro h
  cases h
theorem cons_auto {α : Type u} {a b : α} {l : List α} :
    a ∈ b :: l → a = b ∨ a ∈ l := by
  intro h
  cases h with
  | head => exact Or.inl rfl
  | tail b h => exact Or.inr h
theorem dependent_field {a n : Nat} (h : Witness a (n + 1)) : a = n + 1 := by
  cases h with
  | mk h => exact h
theorem sibling_goals {α : Type u} (a : α) (h : a ∈ ([] : List α)) : False ∧ False := by
  constructor
  cases h
  cases h
theorem diagonal_auto : ¬ Diagonal 0 1 := by
  intro h
  cases h
end IndexCases
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
    let path = std::path::Path::new("/tmp/clean-indexed-cases.lean");
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
fn compound_indices_constrain_case_branches() {
    let source = format!("{HEADER}{PREAMBLE}{POSITIVE}");
    let lean = oracle(&source);
    assert!(
        lean.status.success(),
        "{}",
        String::from_utf8_lossy(&lean.stdout)
    );
    let targets = [
        "IndexCases.nil_auto",
        "IndexCases.cons_auto",
        "IndexCases.diagonal_auto",
        "IndexCases.dependent_field",
        "IndexCases.sibling_goals",
    ];
    let env = elaborate(&source, &targets).expect("retain compound index equations");
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
fn compound_indices_do_not_prove_false_negations() {
    for body in [
        "theorem bad {α : Type u} (a : α) : ¬ a ∈ [a] := by\n  intro h\n  cases h",
        "theorem bad : ¬ Diagonal 0 0 := by\n  intro h\n  cases h",
    ] {
        let source = format!("{HEADER}{PREAMBLE}{body}\nend IndexCases\n");
        assert!(
            !oracle(&source).status.success(),
            "Lean accepted a false control"
        );
        assert!(
            elaborate(&source, &["IndexCases.bad"]).is_err(),
            "false conclusion accepted"
        );
    }
}

#[test]
fn projected_scrutinee_retains_compound_index_equations() {
    let declarations = r"
inductive Listed (a : Nat) : List Nat → Prop where
  | nil : Listed a []
  | cons {b : Nat} {tail : List Nat} : a = b → Listed a (b :: tail)
structure Held (a : Nat) (xs : List Nat) : Prop where
  item : Listed a xs
";
    let positive = format!(
        "{HEADER}{declarations}{}",
        r"
theorem projected (a b : Nat) (h : Held a [b]) : a = b := by
  cases h.item with
  | cons eq => exact eq
"
    );
    let oracle_positive = oracle(&positive);
    assert!(
        oracle_positive.status.success(),
        "{}",
        String::from_utf8_lossy(&oracle_positive.stdout)
    );
    elaborate(&positive, &["projected"]).expect("indexed projection should check");

    let negative = format!(
        "{HEADER}{declarations}{}",
        r"
theorem missingNil (a : Nat) (xs : List Nat) (h : Held a xs) : True := by
  cases h.item with
  | cons _ => exact True.intro
"
    );
    assert!(!oracle(&negative).status.success());
    let refusal = elaborate(&negative, &["missingNil"]).unwrap_err();
    assert!(refusal.contains("Alternative `nil`"), "{refusal}");
}

#[test]
fn explicit_index_equations_are_checked_positive_controls() {
    let source = format!(
        "{HEADER}{PREAMBLE}{}",
        r"
theorem manual {α : Type u} {a : α} : ¬ a ∈ ([] : List α) := by
  intro h
  generalize hx : ([] : List α) = xs at h
  revert hx
  cases h with
  | head => intro hx; cases hx
  | tail b h => intro hx; cases hx
end IndexCases
"
    );
    assert!(oracle(&source).status.success());
    elaborate(&source, &["IndexCases.manual"]).expect("explicit index equality");
}

#[test]
fn indexed_away_fields_still_consume_their_alternative_names() {
    for (tail, body, expected) in [
        ("tail _ member", "exact Or.inr member", true),
        ("tail item member", "exact Or.inr member", true),
        ("@tail item rest member", "exact Or.inr member", true),
        ("tail member", "exact Or.inr member", false),
        ("tail _ member extra", "exact Or.inr member", false),
        ("tail _ member", "exact Or.inl member", false),
    ] {
        let source = format!(
            "{HEADER}theorem slots {{a : Nat}} (h : a ∈ [0, 1]) : a = 0 ∨ a ∈ [1] := by\n  cases h with\n  | head => exact Or.inl rfl\n  | {tail} => {body}\n"
        );
        let lean = oracle(&source);
        assert_eq!(
            lean.status.success(),
            expected,
            "{tail}: {body}\n{}",
            String::from_utf8_lossy(&lean.stdout)
        );
        let checked = elaborate(&source, &["slots"]);
        assert_eq!(
            checked.is_ok(),
            expected,
            "{tail}: {body}\n{:?}",
            checked.err()
        );
    }
}
