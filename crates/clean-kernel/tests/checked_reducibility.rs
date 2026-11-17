// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Explicit ordinary hints remain metadata, never an admission bypass.
use clean_kernel::env::{MmAxiomOnlyGuard, Reducibility};
use clean_kernel::{
    Declaration, DeclarationVerification, Environment, Expr, Name, ReferenceKernel,
    ReferenceRefusal,
};

fn definition(reducible: bool) -> Declaration {
    Declaration::Definition {
        name: Name::from_string("CheckedHints.d"),
        level_params: vec![],
        type_: Expr::type_(),
        value: Expr::prop(),
        is_reducible: reducible,
    }
}

fn entry() -> ReferenceKernel {
    ReferenceKernel::new(Environment::for_lean_replay()).expect("empty fenced entry")
}

#[test]
fn checked_hint_variants_retain_full_value_and_provenance() {
    for hint in [
        Reducibility::Regular(9),
        Reducibility::Reducible,
        Reducibility::Irreducible,
        Reducibility::Opaque,
    ] {
        let mut env = Environment::for_lean_replay();
        env.add_decl_with_reducibility(definition(hint == Reducibility::Reducible), hint)
            .unwrap();
        let name = Name::from_string("CheckedHints.d");
        let info = env.get_const(&name).unwrap();
        assert_eq!(info.reducibility, hint);
        assert_eq!(info.is_reducible, hint == Reducibility::Reducible);
        assert_eq!(info.value, Some(Expr::prop()));
        assert_eq!(
            env.declaration_verification(&name),
            Some(DeclarationVerification::FullKernelCheck)
        );
    }
}

#[test]
fn ordinary_admission_keeps_its_computed_height() {
    let mut env = Environment::for_lean_replay();
    env.add_decl(definition(false)).unwrap();
    assert_eq!(
        env.get_reducibility(&Name::from_string("CheckedHints.d")),
        Some(Reducibility::Regular(1))
    );
}

#[test]
fn malformed_flag_and_wrong_kind_refuse_before_mutation() {
    let mut env = Environment::for_lean_replay();
    let before = env.content_digest();
    assert!(env
        .add_decl_with_reducibility(definition(true), Reducibility::Regular(9))
        .is_err());
    assert!(env
        .add_decl_with_reducibility(definition(false), Reducibility::Reducible)
        .is_err());
    let ax = Declaration::Axiom {
        name: Name::from_string("CheckedHints.ax"),
        level_params: vec![],
        type_: Expr::type_(),
    };
    assert!(env
        .add_decl_with_reducibility(ax, Reducibility::Opaque)
        .is_err());
    assert_eq!(env.content_digest(), before);
}

#[test]
fn ill_typed_value_refuses_in_both_checked_apis() {
    let mut d = definition(false);
    if let Declaration::Definition { value, .. } = &mut d {
        *value = Expr::type_();
    }
    let mut env = Environment::for_lean_replay();
    let before = env.content_digest();
    assert!(env
        .add_decl_with_reducibility(d.clone(), Reducibility::Regular(9))
        .is_err());
    assert_eq!(env.content_digest(), before);
    let mut k = entry();
    let digest = k.env_digest();
    let content = k.environment().content_digest();
    assert!(k
        .add_checked_with_reducibility(d, Reducibility::Regular(9))
        .is_err());
    assert_eq!(k.env_digest(), digest);
    assert_eq!(k.environment().content_digest(), content);
}

#[test]
fn fenced_tokens_bind_the_exact_hint_including_height() {
    let mut digests = std::collections::HashSet::new();
    let mut environments = std::collections::HashSet::new();
    for hint in [
        Reducibility::Regular(9),
        Reducibility::Regular(10),
        Reducibility::Reducible,
        Reducibility::Irreducible,
        Reducibility::Opaque,
    ] {
        let mut k = entry();
        let token = k
            .add_checked_with_reducibility(definition(hint == Reducibility::Reducible), hint)
            .unwrap();
        assert_eq!(
            k.environment()
                .get_reducibility(&Name::from_string("CheckedHints.d")),
            Some(hint)
        );
        assert!(digests.insert(token.decl_digest()));
        assert!(environments.insert(token.env_digest()));
    }
}

#[test]
fn fenced_hint_path_keeps_two_pass_refusal() {
    let mut k = entry();
    let before = k.env_digest();
    {
        let _scope = MmAxiomOnlyGuard::enter();
        assert!(matches!(
            k.add_checked_with_reducibility(definition(false), Reducibility::Regular(9)),
            Err(ReferenceRefusal::MmTwoPassActive)
        ));
    }
    assert_eq!(k.env_digest(), before);
    assert!(k
        .environment()
        .get_const(&Name::from_string("CheckedHints.d"))
        .is_none());
    k.add_checked_with_reducibility(definition(false), Reducibility::Regular(9))
        .unwrap();
}

#[test]
fn duplicate_hint_cannot_overwrite_a_checked_definition() {
    let mut k = entry();
    k.add_checked_with_reducibility(definition(false), Reducibility::Regular(9))
        .unwrap();
    let before = k.env_digest();
    let content = k.environment().content_digest();
    assert!(k
        .add_checked_with_reducibility(definition(false), Reducibility::Opaque)
        .is_err());
    assert_eq!(k.env_digest(), before);
    assert_eq!(k.environment().content_digest(), content);
}

#[test]
fn fenced_malformed_flags_leave_no_resident_or_receipt_change() {
    let mut k = entry();
    let before = k.env_digest();
    let content = k.environment().content_digest();
    for (decl, hint) in [
        (definition(true), Reducibility::Regular(9)),
        (definition(false), Reducibility::Reducible),
    ] {
        assert!(k.add_checked_with_reducibility(decl, hint).is_err());
        assert_eq!(k.env_digest(), before);
        assert_eq!(k.environment().content_digest(), content);
    }
}
