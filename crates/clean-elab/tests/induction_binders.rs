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

#[test]
fn induction_exposes_each_function_field_hypothesis_at_its_own_domain() {
    let source = r#"
inductive Twin where
  | node (left : Bool → Twin) (right : Nat → Twin) : Twin

theorem foldTwin (P : Twin → Prop)
    (step : ∀ (left : Bool → Twin) (right : Nat → Twin),
      (∀ b, P (left b)) → (∀ n, P (right n)) → P (.node left right))
    (set : Twin) : P set := by
  induction set with
  | node left right ihl ihr => exact step left right ihl ihr
"#;
    assert!(oracle(source).status.success());
    let env =
        elaborate(source).expect("function-valued fields have pointwise induction hypotheses");
    let name = Name::from_string("foldTwin");
    assert!(env
        .get_const(&name)
        .expect("source theorem")
        .value
        .is_some());
    assert!(env.axiom_deps(&name).expect("axiom closure").is_empty());

    let swapped = source.replace("step left right ihl ihr", "step left right ihr ihl");
    assert!(!oracle(&swapped).status.success());
    let error = elaborate(&swapped).expect_err("swapped pointwise hypotheses must be refused");
    assert!(error.to_lowercase().contains("mismatch"), "{error}");
}

#[test]
fn direct_induction_hypothesis_remains_a_local_equality_for_simp_only() {
    let source = r#"
inductive T where
  | leaf : T
  | next : T → T

def f (t : T) : Nat := match t with | .leaf => 0 | .next x => Nat.succ (f x)
def g (t : T) : Nat := match t with | .leaf => 0 | .next x => Nat.succ (g x)

theorem same (t : T) : f t = g t := by
  induction t with
  | leaf => rfl
  | next x ih => simp only [f, g, ih]
"#;
    assert!(oracle(source).status.success());
    let env =
        elaborate(source).expect("simp only must be able to rewrite with the direct-field IH");
    let name = Name::from_string("same");
    assert!(env
        .get_const(&name)
        .expect("source theorem")
        .value
        .is_some());
    assert!(env.axiom_deps(&name).expect("axiom closure").is_empty());

    let wrong = source.replace("f t = g t := by", "f t = Nat.succ (g t) := by");
    assert!(!oracle(&wrong).status.success());
    elaborate(&wrong).expect_err("changing the target must still fail");
}
