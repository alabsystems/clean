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
        mutual_declarations: None,
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
            mutual_declarations: None,
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
            mutual_declarations: None,
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

/// An axiom stub one imported module declares, and a genuine inductive of the
/// same name another declares: two declarations of one name, whichever loads
/// first. Until module-trust round 29 the stub-first order DISCHARGED the stub
/// (`discharge_carrier_stubs`) and the inductive won, while the other order
/// kept the inductive and dropped the stub — which one a consumer saw
/// depended on import order. Lean refuses both ("environment already
/// contains"), and so does the loader now (`artifact_ledger`). The discharge
/// stays for a stub the checker's own prelude registers, which is not an
/// artifact's.
#[test]
fn test_axiom_stub_and_genuine_inductive_from_two_modules_refuse_the_import() {
    for stub_first in [true, false] {
        let mut env = Environment::try_with_prelude_for_import().expect("import prelude");
        let stub = || axiom_module_named("PhantomCarrier");
        let genuine = || class_module_named("PhantomCarrier");
        let (first, first_name, second, second_name) = if stub_first {
            (stub(), "StubProvider", genuine(), "GenuineProvider")
        } else {
            (genuine(), "GenuineProvider", stub(), "StubProvider")
        };
        load_parsed_module(&mut env, &first, Some(first_name.to_string()))
            .expect("the first module loads");
        let err = load_parsed_module(&mut env, &second, Some(second_name.to_string()))
            .expect_err("a second declaration of PhantomCarrier must refuse the import");
        assert!(
            matches!(
                &err,
                crate::ImportError::ConflictingDeclaration { name, first }
                    if name == "PhantomCarrier" && first == first_name
            ),
            "stub_first={stub_first}: {err}"
        );
    }
}

/// The same pair under `clean olean replay`'s load
/// (`OleanImportPolicy::with_replay_refusals`), where rule 1 records instead of
/// refusing the import: the second declaration of `PhantomCarrier` must be
/// RECORDED as a duplicate for the replay to refuse, never displace the first.
/// Whichever order they load in, the first stays resident and the second is
/// in `shadowed_declarations`. The carrier discharge used to fire in the
/// stub-first order under this policy (it read any value-free axiom as the
/// checker's own carrier stub), so a module's inductive silently replaced an
/// imported axiom and nothing recorded it: `clean olean replay` then admitted
/// `ReplayForgedIndOverAx`'s proof of `False`, which `leanchecker` refuses
/// (`constant has already been declared 'ind_ax_t'`).
#[test]
fn test_axiom_stub_and_genuine_inductive_under_the_replay_load_record_the_duplicate() {
    let policy = crate::OleanImportPolicy::default()
        .with_kernel_only()
        .with_replay_refusals();
    let name = Name::from_string("PhantomCarrier");
    for stub_first in [true, false] {
        let mut env = Environment::for_lean_replay();
        let (first, first_name, second, second_name) = if stub_first {
            (
                axiom_module_named("PhantomCarrier"),
                "StubProvider",
                class_module_named("PhantomCarrier"),
                "GenuineProvider",
            )
        } else {
            (
                class_module_named("PhantomCarrier"),
                "GenuineProvider",
                axiom_module_named("PhantomCarrier"),
                "StubProvider",
            )
        };
        super::load_parsed_module_with_import_policy(
            &mut env,
            &first,
            Some(first_name.to_string()),
            policy,
        )
        .unwrap_or_else(|e| panic!("stub_first={stub_first}: the first module loads: {e}"));
        let summary = super::load_parsed_module_with_import_policy(
            &mut env,
            &second,
            Some(second_name.to_string()),
            policy,
        )
        .unwrap_or_else(|e| panic!("stub_first={stub_first}: the replay load records: {e}"));
        assert!(
            summary
                .shadowed_declarations
                .iter()
                .any(|(n, held_by)| n == &name && held_by.contains(first_name)),
            "stub_first={stub_first}: the second declaration is recorded as held by \
             `{first_name}`: {:?}",
            summary.shadowed_declarations
        );
        assert!(
            !summary.added_names.contains(&name),
            "stub_first={stub_first}: the second declaration is not registered: {:?}",
            summary.added_names
        );
        assert_eq!(
            env.get_inductive(&name).is_some(),
            !stub_first,
            "stub_first={stub_first}: the FIRST declaration stays resident"
        );
    }
}

/// A kernel quotient primitive is never a carrier stub: an incoming inductive
/// of its name is a duplicate, recorded for a Lean-profile re-check to refuse,
/// under every policy. `Environment::for_lean_replay` seeds `Quot.ind` as a
/// value-free axiom with no artifact behind it, which the carrier discharge
/// used to take for a prelude stub: the module's inductive replaced the
/// kernel's `Quot.ind` constant (its `get_quot` record, and so its reduction
/// rule, stayed), with nothing recorded, under the default policy as under the
/// replay's (measured on this test's module before the guard: `now_inductive
/// = true`, `shadowed = []` for both). Lean refuses such a module as already
/// declared once any import has run `init_quot`.
#[test]
fn test_inductive_named_like_a_kernel_quotient_primitive_does_not_displace_it() {
    let name = Name::from_string("Quot.ind");
    for policy in [
        crate::OleanImportPolicy::default(),
        crate::OleanImportPolicy::default()
            .with_kernel_only()
            .with_replay_refusals(),
    ] {
        let mut env = Environment::for_lean_replay();
        assert!(
            env.get_quot(&name).is_some(),
            "the replay env seeds Quot.ind"
        );
        let summary = super::load_parsed_module_with_import_policy(
            &mut env,
            &class_module_named("Quot.ind"),
            Some("Forger".to_string()),
            policy,
        )
        .unwrap_or_else(|e| panic!("{policy:?}: {e}"));
        assert!(
            env.get_inductive(&name).is_none(),
            "{policy:?}: the kernel's Quot.ind must not be displaced"
        );
        assert_eq!(
            env.get_const(&name).map(|c| c.kind),
            Some(KernelConstantKind::Axiom),
            "{policy:?}: Quot.ind is still the kernel's primitive"
        );
        assert!(
            summary
                .shadowed_declarations
                .iter()
                .any(|(n, _)| n == &name),
            "{policy:?}: the incoming inductive is a recorded duplicate: {:?}",
            summary.shadowed_declarations
        );
    }
}
