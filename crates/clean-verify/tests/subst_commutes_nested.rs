// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::collections::BTreeSet;

use clean_verify::spec::ProofStatus;
use clean_verify::Specification;

fn build_substitution_spec_with_stack() -> Specification {
    clean_verify::test_utils::build_substitution_spec_with_stack()
}

#[test]
fn nested_commutes_bvar_below_is_constructive() {
    let spec = build_substitution_spec_with_stack();
    let name = "instantiate_at_nested_commutes_bvar_below";
    let def = spec
        .definitions()
        .get(name)
        .unwrap_or_else(|| panic!("{name} should exist"));
    assert!(
        def.value_src.is_some(),
        "{name} should have an explicit proof term"
    );
    assert!(!def.is_axiom, "{name} should not be a helper axiom");
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "{name} should be fully constructive"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "{name} should not retain helper blockers: {:?}",
        def.axiom_deps
    );
}

#[test]
fn nested_commutes_bvar_master_flattens_leaf_axioms() {
    let spec = build_substitution_spec_with_stack();
    let name = "instantiate_at_nested_commutes_bvar";
    let def = spec
        .definitions()
        .get(name)
        .unwrap_or_else(|| panic!("{name} should exist"));
    assert!(
        def.value_src.is_some(),
        "{name} should have an explicit proof term"
    );
    assert!(!def.is_axiom, "{name} should not remain a helper axiom");
    let actual = def
        .axiom_deps
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    let expected = BTreeSet::<&str>::new();
    assert_eq!(
        actual, expected,
        "{name} should have empty axiom_deps (all leaf blockers DerivedProved)"
    );
}
