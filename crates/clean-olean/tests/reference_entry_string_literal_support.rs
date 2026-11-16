// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Literal expansion is an implicit replay dependency, including through Name.
use std::collections::BTreeSet;

use clean_kernel::env::{Environment, TrustedEnvExt};
use clean_kernel::{BinderInfo, Expr, Level, Name};
use clean_olean::recheck_closed::{ClosedRecheckOptions, ClosedRecheckRefusal};
use clean_olean::{load_module_with_deps, reference_base_closed, require_pinned_lean_lib_path};

fn load_fixture() -> Environment {
    let compiled = clean_olean::test_support::compiled_fixture_dir("closed_string_support");
    let lib = require_pinned_lean_lib_path().expect("pinned Lean library");
    let mut loaded = Environment::for_lean_replay();
    load_module_with_deps(&mut loaded, "LiteralSupport", &[compiled, lib])
        .expect("compiled pinned Lean fixture");
    loaded
}

#[test]
fn standalone_literal_and_name_proofs_replay_with_checked_support() {
    let loaded = load_fixture();
    for label in [
        "LiteralSupport.different_names",
        "LiteralSupport.different_strings",
        "LiteralSupport.lookup_found",
    ] {
        let roots = BTreeSet::from([Name::from_string(label)]);
        let checked = reference_base_closed(&loaded, &roots, &ClosedRecheckOptions::default())
            .expect("reference entry");
        assert!(
            checked.report.passed() && checked.entry_refusals.is_empty(),
            "{label}: {} {:?}",
            checked.report.verdict_sentence(),
            checked.entry_refusals
        );
        for support in ["Char.ofNat", "String.ofList"] {
            assert!(
                checked.admitted.contains(&Name::from_string(support)),
                "{label} omitted {support}"
            );
        }
        checked.into_kernel().expect("complete fenced replay");
    }
}

#[test]
fn tampered_implicit_literal_helper_is_refused_by_existing_binding_gate() {
    let mut loaded = load_fixture();
    let name = Name::from_string("String.ofList");
    let mut fake = loaded.get_const(&name).expect("canonical helper").clone();
    let list_char = Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        Expr::const_(Name::from_string("Char"), vec![]),
    );
    fake.value = Some(Expr::lam(
        BinderInfo::Default,
        list_char,
        Expr::str_lit("changed"),
    ));
    let expected_value = fake.value.clone();
    let rejected = loaded.extend_constants_structural(std::iter::once(fake));
    assert!(
        rejected.is_empty(),
        "structural mutation rejected: {rejected:?}"
    );
    assert_eq!(
        loaded.get_const(&name).expect("mutated helper").value,
        expected_value
    );
    let roots = BTreeSet::from([Name::from_string("LiteralSupport.lookup_found")]);
    let checked = reference_base_closed(&loaded, &roots, &ClosedRecheckOptions::default())
        .expect("typed refusal report");
    assert!(!checked.report.passed());
    assert!(
        checked.report.refusals.iter().any(|refusal| matches!(
            refusal,
            ClosedRecheckRefusal::ExtensionBindingMismatch { name, .. } if name == "String.ofList"
        )),
        "tampered helper must hit its pinned binding: {:?}",
        checked.report.refusals
    );
    assert!(
        checked.into_kernel().is_err(),
        "a refused replay cannot yield authority"
    );
}
