// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Real source callers for focused `rwa`; every accepted root is rechecked.

use clean_kernel::env::{DeclarationVerification, DomainAxiomClosure};
use clean_kernel::{ConstantKind, Environment, ExprKind, Name, TypeChecker};
use clean_parser::parse_file;

use crate::tactic::TacticError;
use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabError, FileContext,
};

const FOCUS_KEEP: &str =
    include_str!("../../../../../tests/fixtures/rwa_focused/focus_keeps_sibling.lean");
const FOCUS_LEAVE: &str =
    include_str!("../../../../../tests/fixtures/rwa_focused/focus_leaves_sibling.lean");
const AT_REWRITTEN: &str =
    include_str!("../../../../../tests/fixtures/rwa_focused/at_rewritten.lean");
const AT_UNRELATED: &str =
    include_str!("../../../../../tests/fixtures/rwa_focused/at_unrelated.lean");
const AT_CONTROL: &str =
    include_str!("../../../../../tests/fixtures/rwa_focused/at_unrelated_control.lean");
const AT_REFL: &str = include_str!("../../../../../tests/fixtures/rwa_focused/at_refl.lean");
const EMPTY_PROOF: &str =
    include_str!("../../../../../tests/fixtures/rwa_focused/empty_with_proof.lean");
const EMPTY_FALSE: &str =
    include_str!("../../../../../tests/fixtures/rwa_focused/empty_without_proof.lean");
const CONDITIONAL_CLOSED: &str =
    include_str!("../../../../../tests/fixtures/rwa_focused/conditional_closed.lean");
const CONDITIONAL_OPEN: &str =
    include_str!("../../../../../tests/fixtures/rwa_focused/conditional_open.lean");
const REDUCIBLE_REFUSAL: &str =
    include_str!("../../../../../tests/fixtures/rwa_focused/reducible_refusal.lean");
const REDUCIBLE_CONTROL: &str =
    include_str!("../../../../../tests/fixtures/rwa_focused/reducible_control.lean");
const SHADOWED_POSITIVE: &str =
    include_str!("../../../../../tests/fixtures/rwa_focused/shadowed_positive.lean");
const SHADOWED_NEGATIVE: &str =
    include_str!("../../../../../tests/fixtures/rwa_focused/shadowed_negative.lean");
const DELTA_THEN_PROOF_TERM: &str =
    include_str!("../../../../../tests/fixtures/rwa_focused/delta_then_proof_term.lean");
const IMPLICIT_LOCAL_EMPTY: &str =
    include_str!("../../../../../tests/fixtures/rwa_focused/implicit_local_empty.lean");
const LEMMA_AT_SHADOWED_POSITIVE: &str =
    include_str!("../../../../../tests/fixtures/rwa_focused/lemma_at_shadowed_positive.lean");
const LEMMA_SHADOWED_NEGATIVE: &str =
    include_str!("../../../../../tests/fixtures/rwa_focused/lemma_shadowed_negative.lean");
const LEMMA_SHADOWED_POSITIVE: &str =
    include_str!("../../../../../tests/fixtures/rwa_focused/lemma_shadowed_positive.lean");
const LEMMA_SHADOWED_TERM_CONTROL: &str =
    include_str!("../../../../../tests/fixtures/rwa_focused/lemma_shadowed_term_control.lean");
const ORDERED_DEPENDENT_LOCAL: &str =
    include_str!("../../../../../tests/fixtures/rwa_focused/ordered_dependent_local.lean");
const ROLLBACK_SOURCE_DRAFT: &str =
    include_str!("../../../../../tests/fixtures/rwa_focused/rollback_source_draft.lean");

fn elaborate(source: &str) -> (Environment, Result<(), ElabError>) {
    let mut env = Environment::with_prelude();
    let mut context = FileContext::new();
    let declarations = parse_file(source).expect("the fixture parses");
    assert!(!declarations.is_empty(), "empty fixture");
    let mut result = Ok(());
    for declaration in declarations {
        result.expect("every preceding setup declaration must register");
        let processed = preprocess_decl_with_context(&declaration, &mut context);
        result = elaborate_decl_and_register_with_context(&mut env, &processed, &mut context)
            .map(|_| ());
    }
    (env, result)
}

fn accepts(source: &str, name: &str) {
    let (env, result) = elaborate(source);
    result.unwrap_or_else(|error| panic!("{name}: {error:?}"));
    let name = Name::from_string(name);
    let root = env.get_const(&name).expect("the actual theorem registers");
    assert_eq!(root.kind, ConstantKind::Theorem);
    assert_eq!(
        env.declaration_verification(&name),
        Some(DeclarationVerification::FullKernelCheck)
    );
    let proof = root.value.as_ref().expect("an actual proof body");
    for expression in [&root.type_, proof] {
        assert!(!expression.has_fvar_quick());
        assert!(!expression.has_expr_mvar_quick());
        assert!(!expression.has_level_mvar_quick());
        assert!(!expression.has_loose_bvars());
    }
    assert!(!proof.collect_constants().contains(&name));
    let mut checker = TypeChecker::new(&env);
    checker.set_level_params(root.level_params.clone());
    let sort = checker
        .infer_type_full(&root.type_)
        .expect("the declared type fully checks");
    assert!(matches!(checker.whnf(&sort).kind(), ExprKind::Sort(_)));
    checker
        .check_type(proof, &root.type_)
        .expect("the actual registered body fully rechecks");
    assert!(!checker.heartbeat_spent());
    assert!(env.axiom_deps(&name).expect("domain closure").is_empty());
    assert!(env
        .foundational_axiom_deps(&name)
        .expect("foundational closure")
        .is_empty());
    let mut computed = DomainAxiomClosure::new();
    assert!(computed.assumptions_of_name(&env, &name).is_empty());
}

enum Refusal {
    Unsolved,
    TypeMismatch,
    NoHypothesis,
}

fn refuses(source: &str, name: &str, expected: Refusal) {
    let (env, result) = elaborate(source);
    let error = result.expect_err("the fixture must refuse at its actual tactic/goal boundary");
    assert!(env.get_const(&Name::from_string(name)).is_none());
    let ElabError::TacticFailed(tactic) = error.innermost() else {
        panic!("{name}: wrong refusal: {error:?}");
    };
    let expected = match expected {
        Refusal::Unsolved => matches!(tactic, TacticError::UnsolvedGoals { count: 1, .. }),
        Refusal::TypeMismatch => matches!(tactic, TacticError::TypeMismatch { .. }),
        Refusal::NoHypothesis => matches!(tactic, TacticError::NoMatchingHypothesis { .. }),
    };
    assert!(expected, "{name}: wrong refusal: {error:?}");
}

#[test]
fn rwa_focus_preserves_the_original_sibling_goal() {
    accepts(FOCUS_KEEP, "rwa_focus_keeps_sibling");
    refuses(FOCUS_LEAVE, "rwa_focus_leaves_sibling", Refusal::Unsolved);
}

#[test]
fn rwa_at_closes_with_the_rewritten_local_or_reducible_reflexivity() {
    accepts(AT_CONTROL, "rwa_at_unrelated_control");
    accepts(AT_REWRITTEN, "rwa_at_rewritten");
    accepts(AT_REFL, "rwa_at_refl");
    refuses(AT_UNRELATED, "rwa_at_unrelated", Refusal::TypeMismatch);
}

#[test]
fn rwa_does_not_replace_reducible_reflexivity_with_full_unfolding() {
    accepts(REDUCIBLE_CONTROL, "rwa_reducible_control");
    refuses(
        REDUCIBLE_REFUSAL,
        "rwa_reducible_refusal",
        Refusal::NoHypothesis,
    );
}

#[test]
fn rwa_closes_supplied_conditions_and_keeps_missing_conditions_visible() {
    accepts(CONDITIONAL_CLOSED, "rwa_conditional_closed");
    refuses(CONDITIONAL_OPEN, "rwa_conditional_open", Refusal::Unsolved);
}

#[test]
fn rwa_with_empty_rules_still_requires_a_real_closing_proof() {
    accepts(EMPTY_PROOF, "rwa_empty_with_proof");
    refuses(
        EMPTY_FALSE,
        "rwa_empty_without_proof",
        Refusal::NoHypothesis,
    );
}

#[test]
fn rwa_shadowed_hypothesis_uses_the_rewritten_local() {
    accepts(SHADOWED_POSITIVE, "rwa_shadowed_positive");
}

#[test]
fn rwa_shadowed_hypothesis_cannot_close_with_an_untouched_local() {
    refuses(
        SHADOWED_NEGATIVE,
        "rwa_shadowed_negative",
        Refusal::TypeMismatch,
    );
}

#[test]
fn rwa_shadowed_rewrite_lemmas_use_the_newest_local() {
    accepts(LEMMA_SHADOWED_POSITIVE, "rwa_lemma_shadowed_positive");
    accepts(LEMMA_AT_SHADOWED_POSITIVE, "rwa_lemma_at_shadowed_positive");
    accepts(
        LEMMA_SHADOWED_TERM_CONTROL,
        "rwa_lemma_shadowed_term_control",
    );
    refuses(
        LEMMA_SHADOWED_NEGATIVE,
        "rwa_lemma_shadowed_negative",
        Refusal::NoHypothesis,
    );
}

#[test]
fn rwa_threads_the_local_identity_through_delta_and_proof_term_rules() {
    accepts(DELTA_THEN_PROOF_TERM, "rwa_delta_then_proof_term");
}

#[test]
fn rwa_empty_rules_preserve_an_implicit_local_function() {
    accepts(IMPLICIT_LOCAL_EMPTY, "rwa_implicit_local_empty");
}

#[test]
fn rwa_keeps_dependent_local_proofs_and_rolls_back_a_failed_rule_sequence() {
    accepts(ORDERED_DEPENDENT_LOCAL, "rwa_ordered_dependent_local");
    accepts(ROLLBACK_SOURCE_DRAFT, "rwa_rollback_source_draft");
}
