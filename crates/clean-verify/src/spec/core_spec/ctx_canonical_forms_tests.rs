// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Fail-closed pins for the context-indexed syntax-directed canonical-forms
//! fragment (the kernel-checked port of
//! `proofs/lean-aristotle/canonical_forms_pi.lean`, port-back Item 4).
//!
//! The pins enforce the SCOPE that is the point of this item: the judgment is
//! the NEW `CtxTyping` (context-indexed, syntax-directed, conv-free) — a
//! different object of study from the spec's context-free `Typing` — the new
//! inductive constants are object-of-study `FoundationalRule` registrations
//! (NOT census axioms), normality is over exactly `beta_reduces_bd`, and
//! every ladder lemma is `DerivedProved` with an empty axiom closure.

use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec_axiom_closure::{computed_axiom_closure, foundational_rule_names};
use crate::test_utils::run_with_stack;
use crate::Specification;

/// Build the substitution subset of the spec (`add_ctx_canonical_forms` is in
/// the Substitution bundle; see `bundles.rs`).
fn build_spec() -> Specification {
    run_with_stack(|| {
        Specification::new_substitution_test_spec().expect("substitution test spec should build")
    })
}

/// The ladder. Each entry must be DerivedProved with a value and empty
/// declared axiom_deps.
const LADDER: &[&str] = &[
    "ctx_is_nil",
    "is_normal_bd",
    "ctx_lookup_not_nil",
    "ctx_typing_normal_canonical",
    "ctx_canonical_forms_pi",
    "ctx_canonical_forms_pi_is_lam",
];

/// The four object-of-study inductives register their full surfaces
/// (type + constructors + recursor).
#[test]
fn test_ctx_canonical_inductive_surfaces_registered() {
    let spec = build_spec();
    for name in [
        "CtxLookup",
        "CtxLookup.here",
        "CtxLookup.there",
        "CtxLookup.rec",
        "CtxTyping",
        "CtxTyping.var",
        "CtxTyping.sort",
        "CtxTyping.pi",
        "CtxTyping.lam",
        "CtxTyping.app",
        // Let promotion (task #28): the dependent let rule.
        "CtxTyping.let_",
        "CtxTyping.rec",
        "CanonAt",
        "CanonAt.lam_pi",
        "CanonAt.sort_sort",
        "CanonAt.pi_sort",
        "CanonAt.rec",
        "IsLamShape",
        "IsLamShape.intro",
        "IsLamShape.rec",
    ] {
        assert!(
            spec.definitions().contains_key(name),
            "{name} should be registered by the ctx_canonical_forms stage"
        );
    }
}

/// RATCHET PIN: the new inductive constants are object-of-study
/// `FoundationalRule` registrations via `add_inductive` — real kernel
/// inductives, NOT census axioms (`is_axiom` false everywhere).
#[test]
fn test_ctx_canonical_inductives_are_not_census_axioms() {
    let spec = build_spec();
    for name in ["CtxLookup", "CtxTyping", "CanonAt", "IsLamShape"] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert!(!def.is_axiom, "{name} must NOT be an axiom");
        assert_eq!(
            def.category,
            AxiomCategory::FoundationalRule,
            "{name} must be an object-of-study FoundationalRule inductive"
        );
    }
    // Constructors and recursors likewise never enter the axiom census.
    for name in [
        "CtxLookup.here",
        "CtxLookup.there",
        "CtxTyping.var",
        "CtxTyping.sort",
        "CtxTyping.pi",
        "CtxTyping.lam",
        "CtxTyping.app",
        "CtxTyping.let_",
        "CanonAt.lam_pi",
        "CanonAt.sort_sort",
        "CanonAt.pi_sort",
        "IsLamShape.intro",
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert!(!def.is_axiom, "{name} must NOT be an axiom");
    }
}

/// FAIL-CLOSED PIN: every ladder lemma is a genuine DerivedProved closed term
/// with an EMPTY declared axiom closure.
#[test]
fn test_ctx_canonical_ladder_all_derived_proved_zero_axiom_deps() {
    let spec = build_spec();
    for name in LADDER {
        let def = spec
            .definitions()
            .get(*name)
            .unwrap_or_else(|| panic!("{name} should be registered by add_ctx_canonical_forms"));
        assert!(!def.is_axiom, "{name} must not be an axiom");
        assert_eq!(
            def.category,
            AxiomCategory::DerivedLemma,
            "{name} must be a DerivedLemma"
        );
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} must be DerivedProved (closed, kernel-checked term)"
        );
        assert!(def.value_src.is_some(), "{name} must carry a closed term");
        assert!(
            def.axiom_deps.is_empty(),
            "{name} must declare an empty axiom closure: {:?}",
            def.axiom_deps
        );
    }
}

/// STATEMENT PIN: the goal theorems are stated over EXACTLY the new
/// context-indexed judgment `CtxTyping` at the empty `ListType KExpr` context
/// and `beta_reduces_bd` normality — and never over the spec's context-free
/// `Typing` judgment.
#[test]
fn test_ctx_canonical_statements_name_exact_judgment() {
    let spec = build_spec();

    let isn = spec
        .definitions()
        .get("is_normal_bd")
        .expect("is_normal_bd should be registered");
    assert_eq!(
        isn.type_src, "KExpr -> Type",
        "is_normal_bd must be a KExpr predicate"
    );
    let isn_val = isn.value_src.as_deref().unwrap_or_default();
    assert!(
        isn_val.contains("beta_reduces_bd e e' -> Empty"),
        "is_normal_bd must be 'no beta_reduces_bd step applies': {isn_val}"
    );

    let main = spec
        .definitions()
        .get("ctx_typing_normal_canonical")
        .expect("ctx_typing_normal_canonical should be registered");
    assert_eq!(
        main.type_src,
        "forall (ctx : ListType KExpr) (e : KExpr) (T : KExpr), \
         CtxTyping ctx e T -> ctx_is_nil ctx -> is_normal_bd e -> CanonAt e T",
        "the induction target must be stated over CtxTyping with ctx_is_nil/is_normal_bd"
    );

    let goal = spec
        .definitions()
        .get("ctx_canonical_forms_pi")
        .expect("ctx_canonical_forms_pi should be registered");
    assert_eq!(
        goal.type_src,
        "forall (e : KExpr) (A : KExpr) (B : KExpr), \
         CtxTyping (ListType.nil KExpr) e (KExpr.pi A B) -> \
         is_normal_bd e -> IsLamShape e",
        "canonical forms must be pinned to CtxTyping at the empty context"
    );

    let bool_pin = spec
        .definitions()
        .get("ctx_canonical_forms_pi_is_lam")
        .expect("ctx_canonical_forms_pi_is_lam should be registered");
    assert!(
        bool_pin
            .type_src
            .contains("Eq Bool (kexpr_is_lam e) Bool.true"),
        "the Bool pin must go through the landed kexpr_is_lam discriminator: {}",
        bool_pin.type_src
    );

    // NEGATIVE PIN: no statement in the ladder mentions the spec's
    // context-free `Typing` judgment (only `CtxTyping` may appear).
    for name in LADDER {
        let def = spec.definitions().get(*name).expect("ladder entry");
        assert!(
            !def.type_src.contains(" Typing ") && !def.type_src.starts_with("Typing "),
            "{name} must not be stated over the context-free Typing judgment: {}",
            def.type_src
        );
    }
}

/// MASQUERADE GUARD (the point of Item 4): the judgment and the goal theorems
/// carry the scope note — syntax-directed, conv-free, conv-extension gated on
/// DefEq-consistency — and disclaim any relation to the context-free Typing.
#[test]
fn test_ctx_canonical_descriptions_carry_scope_notes() {
    let spec = build_spec();

    let judgment = spec
        .definitions()
        .get("CtxTyping")
        .expect("CtxTyping should be registered");
    assert!(
        judgment.description.contains("SYNTAX-DIRECTED")
            && judgment.description.contains("conv-free")
            && judgment.description.contains("DefEq-consistency")
            && judgment.description.contains("no relation between the two"),
        "CtxTyping description must carry the full scope note: {}",
        judgment.description
    );

    for name in ["ctx_typing_normal_canonical", "ctx_canonical_forms_pi"] {
        let def = spec.definitions().get(name).expect("goal lemma");
        assert!(
            def.description.contains("conv-free"),
            "{name} description must state the conv-free scope: {}",
            def.description
        );
        assert!(
            def.description.contains("beta_reduces_bd"),
            "{name} description must name the exact normality relation: {}",
            def.description
        );
    }
    let goal = spec
        .definitions()
        .get("ctx_canonical_forms_pi")
        .expect("goal");
    assert!(
        goal.description.contains("DefEq-consistency")
            && goal.description.contains("not yet in-tree"),
        "the goal must state that the conv-extension is gated on DefEq-consistency: {}",
        goal.description
    );
}

/// KERNEL-GROUND-TRUTH HONESTY PIN: the computed transitive axiom closure of
/// the ladder rests on the FoundationalRule base only.
#[test]
fn test_ctx_canonical_computed_closure_is_foundational_only() {
    let spec = build_spec();
    let foundational = foundational_rule_names(&spec);
    for name in LADDER {
        let closure = computed_axiom_closure(&spec, name);
        let debt: Vec<&String> = closure.difference(&foundational).collect();
        assert!(
            debt.is_empty(),
            "{name} must have an empty non-foundational computed closure, got: {debt:?}"
        );
    }
}

/// The goal theorems re-verify against the live kernel environment.
#[test]
fn test_ctx_canonical_goals_reverify_in_kernel() {
    let spec = build_spec();
    spec.verify_definition("ctx_typing_normal_canonical")
        .expect("ctx_typing_normal_canonical should re-typecheck in the spec environment");
    spec.verify_definition("ctx_canonical_forms_pi")
        .expect("ctx_canonical_forms_pi should re-typecheck in the spec environment");
    spec.verify_definition("ctx_canonical_forms_pi_is_lam")
        .expect("ctx_canonical_forms_pi_is_lam should re-typecheck in the spec environment");
}
