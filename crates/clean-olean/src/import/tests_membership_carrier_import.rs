// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Faithful typeclass-carrier import: the prelude `Membership` axiom-shim
//! false-positive, retired at the SOURCE.
//!
//! ## History
//!
//! The import prelude (`Environment::try_with_prelude_for_import`) used to
//! pre-register the `Membership` typeclass *carrier head* as an opaque `Axiom`
//! shim so the hand-rolled `Set`/`Multiset`/`Finset` membership instances
//! resolved before any real library loaded. When genuine Lean (`Membership` is
//! a `class`, i.e. an `Inductive`) was imported, its name collided with the
//! shim; the loader kept the shim, and the phantom `Membership` axiom survived
//! in `axiom_deps`, tripping the foundational-only graduation gate.
//!
//! Two fixes landed, in order:
//!
//! 1. The loader learned to DISCHARGE a value-free `Axiom` carrier stub when a
//!    genuine `Inductive` of the same name imports
//!    ([`Environment::discharge_axiom_stub_for_inductive_import`], via
//!    `is_axiom_carrier_stub`/`discharge_carrier_stubs` in `load_register.rs`).
//! 2. `f7aa240c` then retired the shim at the source: `init_set_theory` now
//!    seeds `Membership` as the REAL Lean single-field structure (inductive +
//!    `Membership.mk` + proj-reducible `Membership.mem`), so the phantom axiom
//!    never exists — not even before import. A strictly stronger trust state:
//!    the domain-axiom count is lower and reduction is Lean-faithful.
//!
//! These tests pin the post-`f7aa240c` reality for the `Membership` carrier,
//! and keep the (still-live) discharge path covered end-to-end via a synthetic
//! `PhantomCarrier` stub that does not depend on the prelude.

use super::load_parsed_module;
use crate::expr::{ParsedBinderInfo, ParsedExpr};
use crate::level::ParsedLevel;
use crate::module::{ConstantKind, InductiveValData, ParsedConstant, ParsedModule};
use clean_kernel::env::{ConstantKind as KernelConstantKind, Environment};
use clean_kernel::name::Name;

/// `Type u → Type v → Type (max u v)` — the genuine `Membership` class head
/// type, matching the prelude's seeded class (`set_theory.rs::init_set_theory`).
fn membership_class_type() -> ParsedExpr {
    let type_u = ParsedExpr::Sort(ParsedLevel::Succ(Box::new(ParsedLevel::Param("u".into()))));
    let type_v = ParsedExpr::Sort(ParsedLevel::Succ(Box::new(ParsedLevel::Param("v".into()))));
    let type_max = ParsedExpr::Sort(ParsedLevel::Succ(Box::new(ParsedLevel::Max(
        Box::new(ParsedLevel::Param("u".into())),
        Box::new(ParsedLevel::Param("v".into())),
    ))));
    // (_ : Type u) → (_ : Type v) → Type (max u v)
    ParsedExpr::ForallE(
        "α".into(),
        Box::new(type_u),
        Box::new(ParsedExpr::ForallE(
            "γ".into(),
            Box::new(type_v),
            Box::new(type_max),
            ParsedBinderInfo::Default,
        )),
        ParsedBinderInfo::Default,
    )
}

/// A `ParsedModule` exporting `name` as an `Inductive` class head (plus its
/// single constructor `{name}.mk`), exactly as a real `.olean` serializes a
/// structure/class.
fn class_module_named(name: &str) -> ParsedModule {
    let class = ParsedConstant {
        name: name.into(),
        kind: ConstantKind::Inductive,
        level_params: vec!["u".into(), "v".into()],
        type_: Some(membership_class_type()),
        value: None,
        inductive_val: Some(InductiveValData {
            num_params: 2,
            num_indices: 0,
            all: vec![name.into()],
            ctors: vec![format!("{name}.mk")],
            is_rec: false,
            is_unsafe: false,
            is_reflexive: false,
            is_nested: false,
        }),
        constructor_val: None,
        recursor_val: None,
        hints: None,
        definition_safety: None,
        quot_kind: None,
    };
    ParsedModule {
        const_names: vec![name.into()],
        constants: vec![class],
        extra_const_names: Vec::new(),
        imports: Vec::new(),
        entries: Vec::new(),
        clean_payload: None,
    }
}

/// A `ParsedModule` exporting `name` as a bare value-free `Axiom` with the
/// class-head type — the shape of a carrier stub (or a rogue collision).
fn axiom_module_named(name: &str) -> ParsedModule {
    ParsedModule {
        const_names: vec![name.into()],
        constants: vec![ParsedConstant {
            name: name.into(),
            kind: ConstantKind::Axiom,
            level_params: vec!["u".into(), "v".into()],
            type_: Some(membership_class_type()),
            value: None,
            inductive_val: None,
            constructor_val: None,
            recursor_val: None,
            hints: None,
            definition_safety: None,
            quot_kind: None,
        }],
        extra_const_names: Vec::new(),
        imports: Vec::new(),
        entries: Vec::new(),
        clean_payload: None,
    }
}

/// PRECONDITION (post-`f7aa240c`): the import prelude seeds `Membership` as the
/// GENUINE Lean class — an inductive whose constant entry is a value-free
/// `Definition` — so the phantom-axiom false-positive never exists at all.
#[test]
fn test_import_prelude_seeds_membership_as_genuine_inductive() {
    let env = Environment::try_with_prelude_for_import().expect("import prelude");
    let info = env
        .get_const(&Name::from_string("Membership"))
        .expect("import prelude seeds the Membership carrier head");
    assert_eq!(
        info.kind,
        KernelConstantKind::Definition,
        "since f7aa240c the prelude seeds the genuine Lean class, not an Axiom shim"
    );
    assert!(
        info.value.is_none(),
        "an inductive type constant is value-free"
    );
    assert!(
        env.get_inductive(&Name::from_string("Membership"))
            .is_some(),
        "the prelude registers the genuine Membership inductive"
    );
}

/// Importing the genuine `Membership` class DEDUPS against the prelude's seeded
/// inductive: nothing crashes, nothing is double-registered, and the carrier
/// head stays a non-axiom.
#[test]
fn test_genuine_membership_inductive_import_dedups_against_prelude() {
    let mut env = Environment::try_with_prelude_for_import().expect("import prelude");
    assert!(
        env.get_inductive(&Name::from_string("Membership"))
            .is_some(),
        "prelude already seeds the genuine inductive"
    );

    let summary = load_parsed_module(
        &mut env,
        &class_module_named("Membership"),
        Some("Init.Core".to_string()),
    )
    .expect("genuine Membership class module should load");

    // Still registered through the checked path; still not an axiom.
    assert!(
        env.get_inductive(&Name::from_string("Membership"))
            .is_some(),
        "the genuine Membership class must remain registered as an inductive"
    );
    let info = env
        .get_const(&Name::from_string("Membership"))
        .expect("Membership constant present after import");
    assert_ne!(
        info.kind,
        KernelConstantKind::Axiom,
        "after import, Membership must NOT be an Axiom — no phantom domain axiom"
    );
    assert!(
        summary.duplicate_constants >= 1,
        "the incoming genuine class dedups against the seeded inductive, got {summary:?}"
    );
}

/// The phantom `Membership` axiom appears in NO consumer's `axiom_deps` —
/// neither before nor after importing the genuine class. A theorem-shaped
/// consumer referencing the carrier head reports a foundational-only (empty
/// domain) closure throughout: the accurate verdict, with no import required.
#[test]
fn test_consumer_axiom_deps_excludes_membership_after_import() {
    let mut env = Environment::try_with_prelude_for_import().expect("import prelude");

    let consumer = ParsedModule {
        const_names: vec!["MyConsumer".into()],
        constants: vec![ParsedConstant {
            name: "MyConsumer".into(),
            kind: ConstantKind::Axiom,
            level_params: vec!["u".into(), "v".into()],
            // type references `@Membership.{u,v}` applied to nothing structural —
            // a `const` reference is all `axiom_deps`' const-walk needs.
            type_: Some(ParsedExpr::Const(
                "Membership".into(),
                vec![
                    ParsedLevel::Param("u".into()),
                    ParsedLevel::Param("v".into()),
                ],
            )),
            value: None,
            inductive_val: None,
            constructor_val: None,
            recursor_val: None,
            hints: None,
            definition_safety: None,
            quot_kind: None,
        }],
        extra_const_names: Vec::new(),
        imports: Vec::new(),
        entries: Vec::new(),
        clean_payload: None,
    };
    load_parsed_module(&mut env, &consumer, Some("Consumer".to_string()))
        .expect("consumer module should load");

    let deps_before = env
        .axiom_deps(&Name::from_string("MyConsumer"))
        .expect("consumer present");
    assert!(
        !deps_before.contains(&Name::from_string("Membership")),
        "the prelude seeds Membership as a genuine inductive, so no phantom axiom \
         exists even BEFORE import: {deps_before:?}"
    );

    // Importing the genuine class keeps it that way.
    load_parsed_module(
        &mut env,
        &class_module_named("Membership"),
        Some("Init.Core".to_string()),
    )
    .expect("genuine Membership class module should load");

    let deps_after = env
        .axiom_deps(&Name::from_string("MyConsumer"))
        .expect("consumer present");
    assert!(
        !deps_after.contains(&Name::from_string("Membership")),
        "AFTER import the Membership carrier must still not be an axiom: {deps_after:?}"
    );
}

/// ADVERSARIAL / SOUNDNESS: a rogue same-named `Axiom` must NOT displace the
/// genuine seeded inductive — it is deduplicated, the inductive registration
/// and its non-axiom constant entry are untouched.
#[test]
fn test_colliding_axiom_does_not_displace_genuine_inductive() {
    let mut env = Environment::try_with_prelude_for_import().expect("import prelude");

    let summary = load_parsed_module(
        &mut env,
        &axiom_module_named("Membership"),
        Some("Rogue".to_string()),
    )
    .expect("rogue module should load (deduped, not crash)");

    assert!(
        env.get_inductive(&Name::from_string("Membership"))
            .is_some(),
        "a same-named incoming Axiom must NOT displace the genuine seeded inductive"
    );
    assert_eq!(
        env.get_const(&Name::from_string("Membership"))
            .expect("constant still present")
            .kind,
        KernelConstantKind::Definition,
        "the seeded inductive constant is untouched by the colliding axiom"
    );
    assert!(
        summary.duplicate_constants >= 1,
        "the colliding axiom must be counted as a duplicate, got {summary:?}"
    );
}

/// COVERAGE: the axiom-stub DISCHARGE path (`is_axiom_carrier_stub` +
/// `discharge_carrier_stubs` → `discharge_axiom_stub_for_inductive_import`) is
/// still live code for stubs that arrive VIA IMPORT, even though the prelude no
/// longer manufactures one. Exercise it end-to-end with a synthetic
/// `PhantomCarrier`: first import a bare value-free Axiom stub, then the
/// genuine inductive of the same name — the stub must be discharged and the
/// checked inductive must register. A strict trust improvement: an unchecked
/// assumption is replaced by a kernel-checked declaration; it can never admit
/// a NEW axiom.
#[test]
fn test_axiom_stub_discharged_when_genuine_inductive_imports() {
    let mut env = Environment::try_with_prelude_for_import().expect("import prelude");

    load_parsed_module(
        &mut env,
        &axiom_module_named("PhantomCarrier"),
        Some("StubProvider".to_string()),
    )
    .expect("stub module should load");
    let stub = env
        .get_const(&Name::from_string("PhantomCarrier"))
        .expect("stub registered");
    assert_eq!(
        stub.kind,
        KernelConstantKind::Axiom,
        "precondition: the imported carrier stub is a bare Axiom"
    );
    assert!(
        env.get_inductive(&Name::from_string("PhantomCarrier"))
            .is_none(),
        "precondition: no genuine PhantomCarrier inductive exists yet"
    );

    load_parsed_module(
        &mut env,
        &class_module_named("PhantomCarrier"),
        Some("GenuineProvider".to_string()),
    )
    .expect("genuine class module should load");

    assert!(
        env.get_inductive(&Name::from_string("PhantomCarrier"))
            .is_some(),
        "the genuine inductive must register, discharging the axiom stub"
    );
    assert_ne!(
        env.get_const(&Name::from_string("PhantomCarrier"))
            .expect("constant present")
            .kind,
        KernelConstantKind::Axiom,
        "after discharge, PhantomCarrier must no longer be an Axiom — the phantom \
         domain axiom is retired"
    );
}
