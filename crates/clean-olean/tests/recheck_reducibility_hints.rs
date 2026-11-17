// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Ordinary source metadata must survive real checked dependency-closed replay.

use clean_kernel::env::{ConstantInfo, ConstantKind, Reducibility, TrustedEnvExt};
use clean_kernel::{Environment, Expr, Name};
use clean_olean::{recheck_closed, reference_base_closed, ClosedRecheckOptions};
use std::collections::BTreeSet;

fn imported_definition(label: &str, hint: Reducibility, value: Expr) -> (Environment, Name) {
    let name = Name::from_string(label);
    let info = ConstantInfo::new_with_reducibility(
        name.clone(),
        vec![],
        Expr::type_(),
        Some(value),
        hint,
        ConstantKind::Definition,
    );
    let mut source = Environment::for_lean_replay();
    // This is deliberately only the untrusted import tier. The replay below
    // must check the actual value, not reuse a trusted fixture admission.
    let refused = source.extend_constants_structural(std::iter::once(info));
    assert!(refused.is_empty(), "valid structural fixture: {refused:?}");
    (source, name)
}

fn assert_metadata(source: &Environment, replayed: &Environment, name: &Name) {
    let expected = source.get_const(name).expect("source definition");
    let actual = replayed.get_const(name).expect("checked replay resident");
    eprintln!(
        "REDUCIBILITY_WITNESS {name}: expected={:?}/{} actual={:?}/{}",
        expected.reducibility, expected.is_reducible, actual.reducibility, actual.is_reducible
    );
    assert_eq!(actual.kind, expected.kind);
    assert_eq!(actual.level_params, expected.level_params);
    assert_eq!(actual.type_, expected.type_);
    assert_eq!(actual.value, expected.value);
    assert_eq!(
        actual.reducibility, expected.reducibility,
        "exact enum/height"
    );
    assert_eq!(
        actual.is_reducible, expected.is_reducible,
        "exact legacy flag"
    );
}

#[test]
fn closed_replay_preserves_non_default_regular_height() {
    let (source, name) = imported_definition(
        "ReplayHints.regular",
        Reducibility::Regular(9),
        Expr::prop(),
    );
    let run = recheck_closed(
        &source,
        &BTreeSet::from([name.clone()]),
        &ClosedRecheckOptions::default(),
    );
    assert!(run.report.passed(), "{:?}", run.report.refusals);
    assert_metadata(&source, &run.replayed, &name);
}

#[test]
fn fenced_replay_preserves_non_default_regular_height() {
    let (source, name) = imported_definition(
        "ReplayHints.fencedRegular",
        Reducibility::Regular(9),
        Expr::prop(),
    );
    let run = reference_base_closed(
        &source,
        &BTreeSet::from([name.clone()]),
        &ClosedRecheckOptions::default(),
    )
    .expect("empty reference base");
    assert!(run.report.passed(), "{:?}", run.report.refusals);
    assert!(run.entry_refusals.is_empty());
    let kernel = run.into_kernel().expect("genuine complete checked replay");
    assert_metadata(&source, kernel.environment(), &name);
}

#[test]
fn closed_replay_preserves_other_definition_hint_variants() {
    for (label, hint) in [
        ("ReplayHints.abbrev", Reducibility::Reducible),
        ("ReplayHints.irreducible", Reducibility::Irreducible),
        ("ReplayHints.opaqueHint", Reducibility::Opaque),
    ] {
        let (source, name) = imported_definition(label, hint, Expr::prop());
        let run = recheck_closed(
            &source,
            &BTreeSet::from([name.clone()]),
            &ClosedRecheckOptions::default(),
        );
        assert!(run.report.passed(), "{:?}", run.report.refusals);
        assert_metadata(&source, &run.replayed, &name);
    }
}

#[test]
fn fenced_replay_preserves_other_definition_hint_variants() {
    for (label, hint) in [
        ("ReplayHints.fencedAbbrev", Reducibility::Reducible),
        ("ReplayHints.fencedIrreducible", Reducibility::Irreducible),
        ("ReplayHints.fencedOpaqueHint", Reducibility::Opaque),
    ] {
        let (source, name) = imported_definition(label, hint, Expr::prop());
        let run = reference_base_closed(
            &source,
            &BTreeSet::from([name.clone()]),
            &ClosedRecheckOptions::default(),
        )
        .expect("empty reference base");
        assert!(run.report.passed(), "{:?}", run.report.refusals);
        assert!(run.entry_refusals.is_empty());
        let kernel = run.into_kernel().expect("genuine complete checked replay");
        assert_metadata(&source, kernel.environment(), &name);
    }
}

#[test]
fn exact_hint_never_admits_an_ill_typed_body() {
    let (source, name) =
        imported_definition("ReplayHints.bad", Reducibility::Regular(9), Expr::type_());
    let targets = BTreeSet::from([name.clone()]);
    let run = recheck_closed(&source, &targets, &ClosedRecheckOptions::default());
    assert!(!run.report.passed());
    assert!(run.replayed.get_const(&name).is_none());
    let fenced = reference_base_closed(&source, &targets, &ClosedRecheckOptions::default())
        .expect("empty reference base");
    assert!(!fenced.report.passed());
    assert!(!fenced.entry_refusals.is_empty());
    assert!(fenced.kernel().environment().get_const(&name).is_none());
    assert!(fenced.into_kernel().is_err());
}

#[test]
fn transitive_dependency_hints_survive_both_replays() {
    let (mut source, dependency) = imported_definition(
        "ReplayHints.dependency",
        Reducibility::Regular(9),
        Expr::prop(),
    );
    let root = Name::from_string("ReplayHints.dependent");
    let dependent = ConstantInfo::new_with_reducibility(
        root.clone(),
        vec![],
        Expr::type_(),
        Some(Expr::const_(dependency.clone(), vec![])),
        Reducibility::Regular(27),
        ConstantKind::Definition,
    );
    assert!(source
        .extend_constants_structural(std::iter::once(dependent))
        .is_empty());
    let targets = BTreeSet::from([root.clone()]);
    let run = recheck_closed(&source, &targets, &ClosedRecheckOptions::default());
    assert!(run.report.passed(), "{:?}", run.report.refusals);
    assert_metadata(&source, &run.replayed, &dependency);
    assert_metadata(&source, &run.replayed, &root);
    let fenced =
        reference_base_closed(&source, &targets, &ClosedRecheckOptions::default()).unwrap();
    assert!(fenced.report.passed(), "{:?}", fenced.report.refusals);
    let kernel = fenced.into_kernel().unwrap();
    assert_metadata(&source, kernel.environment(), &dependency);
    assert_metadata(&source, kernel.environment(), &root);
}
