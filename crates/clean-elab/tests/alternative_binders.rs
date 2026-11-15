// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Constructor alternatives distinguish explicit fields from implicit binders.
//! The imported oracle is mandatory; no source failure is silently skipped.
use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;
use std::process::Command;

const POSITIVE: &str = include_str!("fixtures/alternative_binders/positive.lean");

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
fn alternatives_name_the_intended_constructor_fields() {
    let independent = oracle(POSITIVE);
    assert!(
        independent.status.success(),
        "{}",
        String::from_utf8_lossy(&independent.stdout)
    );
    let env = elaborate(POSITIVE).expect("alternative binder proofs");
    for text in [
        "case_normal",
        "case_explicit",
        "induction_normal",
        "induction_explicit",
        "recursive_normal",
        "recursive_explicit",
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
fn alternatives_reject_surplus_names_and_wrong_proofs() {
    let setup = POSITIVE
        .split("\ntheorem case_normal")
        .next()
        .expect("fixture prefix");
    for body in [
        "theorem bad (p : Packed) : True := by\n  cases p with\n  | mk flag n h => trivial",
        "theorem bad (p : Packed) : True := by\n  cases p with\n  | @mk flag tag inst n h extra => trivial",
        "theorem bad (p : Packed) : ∃ n : Nat, n = 1 := by\n  cases p with\n  | mk n h => exact ⟨n, h⟩",
        "theorem bad (p : Packed) : False := by\n  cases p with\n  | @mk flag tag inst n h => exact flag",
    ] {
        let source = format!("{setup}\n{body}");
        assert!(!oracle(&source).status.success(), "Lean accepted refusal control");
        let error = match elaborate(&source) {
            Ok(_) => panic!("invalid alternative must fail: {body}"),
            Err(error) => error,
        };
        assert!(error.contains("names") || error.contains("mismatch") || error.contains("unify"), "{error}");
    }
}

const LET_ALIAS_POSITIVE: &str =
    include_str!("fixtures/alternative_binders/let_alias/positive.lean");
const LET_ALIAS_NAMES: &[&str] = &[
    "let_alias_cases_ordinary",
    "let_alias_cases_explicit",
    "let_alias_induction_ordinary",
    "let_alias_induction_explicit",
];

#[test]
fn genuine_let_aliases_survive_constructor_alternative_fields() {
    // Exactly the independently measured source, including its axiom census.
    let mut native_source = LET_ALIAS_POSITIVE.to_owned();
    native_source.push('\n');
    for &name in LET_ALIAS_NAMES {
        native_source.push_str("#print axioms ");
        native_source.push_str(name);
        native_source.push('\n');
    }
    let independent = oracle(&native_source);
    assert!(
        independent.status.success(),
        "stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&independent.stdout),
        String::from_utf8_lossy(&independent.stderr)
    );
    let stdout = String::from_utf8_lossy(&independent.stdout);
    let env = elaborate(LET_ALIAS_POSITIVE).expect("let alias and field-name composition");
    let checker = clean_kernel::TypeChecker::new(&env);
    for &name in LET_ALIAS_NAMES {
        assert!(
            stdout.contains(&format!("'{name}' does not depend on any axioms")),
            "{stdout}"
        );
        let key = Name::from_string(name);
        let declaration = env.get_const(&key).expect("registered composition theorem");
        let proof = declaration.value.as_ref().expect("stored proof body");
        checker
            .check_type(proof, &declaration.type_)
            .expect("independent full kernel check of the closed proof");
        assert!(env.axiom_deps(&key).expect("axiom closure").is_empty());
    }
}

fn assert_let_alias_refusal(source: &str, theorem: &str, category: &str) {
    let independent = oracle(source);
    assert_eq!(
        independent.status.code(),
        Some(1),
        "Lean refusal: {theorem}"
    );
    let native_error = format!(
        "{}\n{}",
        String::from_utf8_lossy(&independent.stdout),
        String::from_utf8_lossy(&independent.stderr)
    )
    .to_ascii_lowercase();
    match category {
        "surplus-name" => assert!(native_error.contains("too many variable names")),
        "wrong-equation" => assert!(native_error.contains("mismatch")),
        _ => panic!("unknown native refusal category"),
    }
    let mut env = Environment::with_prelude();
    let mut context = FileContext::new();
    let declarations = parse_file(source).expect("native-refused source must still parse");
    let mut rejection = None;
    for declaration in declarations {
        let declaration = preprocess_decl_with_context(&declaration, &mut context);
        match elaborate_decl_and_register_with_context(&mut env, &declaration, &mut context) {
            Ok(result) => {
                if let Some(message) = failure(&result) {
                    rejection = Some(message);
                    break;
                }
            }
            Err(error) => {
                rejection = Some(error.to_string());
                break;
            }
        }
    }
    let error = rejection.expect("invalid alias composition must be refused");
    assert!(
        env.get_const(&Name::from_string(theorem)).is_none(),
        "a refused theorem must not register: {theorem}"
    );
    let lower = error.to_ascii_lowercase();
    match category {
        "surplus-name" => assert!(lower.contains("names"), "{error}"),
        "wrong-equation" => assert!(
            lower.contains("mismatch") || lower.contains("unify"),
            "{error}"
        ),
        _ => panic!("unknown refusal category"),
    }
}

#[test]
fn genuine_let_alias_alternatives_refuse_wrong_equations_and_surplus_names() {
    for (theorem, source, category) in [
        (
            "let_alias_cases_ordinary_wrong_equation",
            include_str!("fixtures/alternative_binders/let_alias/let_alias_cases_ordinary_wrong_equation.lean"),
            "wrong-equation",
        ),
        (
            "let_alias_cases_ordinary_surplus",
            include_str!("fixtures/alternative_binders/let_alias/let_alias_cases_ordinary_surplus.lean"),
            "surplus-name",
        ),
        (
            "let_alias_cases_explicit_wrong_equation",
            include_str!("fixtures/alternative_binders/let_alias/let_alias_cases_explicit_wrong_equation.lean"),
            "wrong-equation",
        ),
        (
            "let_alias_cases_explicit_surplus",
            include_str!("fixtures/alternative_binders/let_alias/let_alias_cases_explicit_surplus.lean"),
            "surplus-name",
        ),
        (
            "let_alias_induction_ordinary_wrong_equation",
            include_str!("fixtures/alternative_binders/let_alias/let_alias_induction_ordinary_wrong_equation.lean"),
            "wrong-equation",
        ),
        (
            "let_alias_induction_ordinary_surplus",
            include_str!("fixtures/alternative_binders/let_alias/let_alias_induction_ordinary_surplus.lean"),
            "surplus-name",
        ),
        (
            "let_alias_induction_explicit_wrong_equation",
            include_str!("fixtures/alternative_binders/let_alias/let_alias_induction_explicit_wrong_equation.lean"),
            "wrong-equation",
        ),
        (
            "let_alias_induction_explicit_surplus",
            include_str!("fixtures/alternative_binders/let_alias/let_alias_induction_explicit_surplus.lean"),
            "surplus-name",
        ),
    ] {
        assert_let_alias_refusal(source, theorem, category);
    }
}
