// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact ground term-let/have sources measured on Lean430rc2,435 and436rc2.
//! No pending values or general meta-opacity claim is involved.

use clean_elab::tactic::{builtins::builtin_tactic_patterns, TacticError};
use clean_elab::{elaborate_decl_and_register, ElabError};
use clean_kernel::{Environment, Expr, Name, TypeChecker};
use clean_parser::parse_file_with_tactics;

fn check(source: &str, theorem: &str, wrong_literal: Option<&str>) {
    // The retained native file includes its observer command. Clean's ordinary
    // declaration entry checks the exact preceding theorem, then the same
    // axiom closure through its public Environment API.
    let observer = format!("#print axioms {theorem}\n");
    let declaration = source
        .strip_suffix(&observer)
        .expect("the exact native observer follows the measured theorem");
    let declarations = parse_file_with_tactics(declaration, &builtin_tactic_patterns())
        .expect("the measured ground source must parse");
    assert_eq!(declarations.len(), 1, "one actual theorem must be checked");
    let mut env = Environment::with_prelude();
    let result = elaborate_decl_and_register(&mut env, &declarations[0]);
    let name = Name::from_string(theorem);
    if let Some(literal) = wrong_literal {
        let error = result.expect_err("the measured rfl mismatch must reject");
        let detail = format!("{error:?}");
        assert!(
            matches!(
                error.innermost(),
                ElabError::TacticFailed(TacticError::TypeMismatch { .. })
            ) && detail.contains('n')
                && detail.contains(literal),
            "the refusal must reach the named local/literal equality: {detail}"
        );
        assert!(env.get_const(&name).is_none(), "a refusal cannot register");
        return;
    }
    result.expect("the native-accepted ground theorem must elaborate");
    let info = env.get_const(&name).expect("the theorem must register");
    assert_eq!(info.type_, Expr::const_(Name::from_string("True"), vec![]));
    let proof = info
        .value
        .as_ref()
        .expect("the actual proof must be stored");
    assert!(!proof.has_fvar_quick() && !proof.has_loose_bvars_quick());
    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type_full(proof)
        .expect("strict full proof inference");
    assert!(tc.is_def_eq(&inferred, &info.type_));
    assert!(env
        .axiom_deps(&name)
        .expect("actual axiom closure")
        .is_empty());
}

#[test]
fn genuine_term_let_retains_its_ground_reduction_value() {
    check(
        include_str!("fixtures/term_local_values/term_let_ground_ok.lean"),
        "term_let_ground_ok",
        None,
    );
}

#[test]
fn opaque_term_have_cannot_prove_its_stored_literal_equation() {
    check(
        include_str!("fixtures/term_local_values/term_have_ground_bad.lean"),
        "term_have_ground_bad",
        Some("7"),
    );
}

#[test]
fn genuine_term_let_cannot_prove_a_different_literal_equation() {
    check(
        include_str!("fixtures/term_local_values/term_let_ground_bad.lean"),
        "term_let_ground_bad",
        Some("8"),
    );
}

#[test]
fn opaque_term_have_remains_usable_at_its_own_identity() {
    check(
        include_str!("fixtures/term_local_values/term_have_self_ok.lean"),
        "term_have_self_ok",
        None,
    );
}
