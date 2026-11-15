// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! G12: the builtin implication simp rules produce kernel-checked proofs.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::{Environment, Name, TypeChecker};
use clean_parser::parse_file;

fn elaborate(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    let mut ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| e.to_string())?;
    for decl in &decls {
        let decl = preprocess_decl_with_context(decl, &mut ctx);
        let result = elaborate_decl_and_register(&mut env, &decl).map_err(|e| e.to_string())?;
        fn failures(result: &ElabResult) -> Result<(), String> {
            match result {
                ElabResult::Failed { error, .. } => Err(error.to_string()),
                ElabResult::Multiple(results) => results.iter().try_for_each(failures),
                _ => Ok(()),
            }
        }
        failures(&result)?;
    }
    Ok(env)
}

fn assert_proof(source: &str, theorem: &str) {
    let env = elaborate(source).unwrap_or_else(|e| panic!("{theorem}: {e}\n{source}"));
    let name = Name::from_string(theorem);
    let info = env.get_const(&name).expect("theorem registered");
    let proof = info.value.as_ref().expect("theorem has a proof");
    let tc = TypeChecker::new(&env);
    let inferred = tc.infer_type(proof).expect("proof type checks");
    assert!(tc.is_def_eq(&inferred, &info.type_), "{theorem}");
    for axiom in env.axiom_deps(&name).expect("axiom closure") {
        assert_eq!(axiom, Name::from_string("propext"), "{theorem}");
    }
}

#[test]
fn simp_closes_implications_with_true_or_false_endpoints() {
    for source in [
        "theorem probe (p : Prop) : p → True := by simp",
        "theorem probe : Nat → True := by simp",
        "theorem probe (p : Prop) : False → p := by simp",
        "theorem probe (p : Prop) : p → True := by simp only [implies_true]",
        "theorem probe (p : Prop) : False → p := by simp only [false_implies]",
        "theorem probe (α : Sort u) : (α → True) = True := implies_true α",
        "theorem probe (p : Prop) : (False → p) = True := false_implies p",
        "theorem probe (α : Sort u) : α → True := by simp",
    ] {
        assert_proof(source, "probe");
    }
}

#[test]
fn cases_simp_bool_match_g12() {
    assert_proof(
        include_str!(
            "../../../reports/trust-ir-semantics-probe/repros/G12-cases-simp-bool-match.lean"
        ),
        "t",
    );
}

#[test]
fn simp_does_not_reverse_implication_endpoints() {
    for source in [
        "theorem bad : (False → True) = False := by simp",
        "theorem bad (p : Prop) : True → p := by simp",
        "theorem bad : Nat → False := by simp",
        include_str!(
            "../../../reports/trust-ir-semantics-probe/repros/G12-cases-simp-bool-match-twin.lean"
        ),
    ] {
        let error = elaborate(source).expect_err("Lean refuses this unprovable implication");
        assert!(!error.contains("sorry"), "{error}");
        assert!(
            error.contains("simp") || error.contains("unsolved"),
            "{error}"
        );
    }
}

/// The real Init census exposed an older `Int.natAbs` spelling difference.
/// Its borrowed-domain metadata must preserve application and dot notation.
#[test]
fn nat_abs_borrowed_domain_preserves_existing_proofs() {
    for source in [
        "theorem probe : Int.natAbs (Int.ofNat 4) = 4 := rfl",
        "theorem probe : Int.natAbs (Int.negSucc 4) = 5 := rfl",
        "theorem probe (n : Nat) : (Int.ofNat n).natAbs = n := rfl",
    ] {
        assert_proof(source, "probe");
    }
    let error = elaborate("theorem bad : Int.natAbs (Int.negSucc 4) = 4 := rfl")
        .expect_err("absolute value of -5 is not 4");
    assert!(error.to_lowercase().contains("mismatch"), "{error}");
    assert!(!error.contains("sorry"), "{error}");
}
