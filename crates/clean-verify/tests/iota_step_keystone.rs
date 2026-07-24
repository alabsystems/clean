// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment C (#2859 computational-iota/delta track) — the KEYSTONE. Pins that
//! the computational reduct `iota_reduct`, the spine/list substrate, the graph
//! predicate `iota_step`, and the determinism lemma `iota_step_deterministic`
//! are registered and kernel-checked, and that `iota_step_deterministic` is
//! DerivedProved with zero axiom_deps.
//!
//! `iota_step_deterministic` is the single new capability the abstract
//! `iota_reduces.mk` (an undirected, non-functional DefEq witness) structurally
//! lacked: two reducts of the same redex are equal, because `iota_reduct` is a
//! total function and `iota_step` is its graph. This is the fact the `par_strips`
//! iota cross-joins (Increment F) need.

use clean_kernel::Name;
use clean_verify::spec::{AxiomCategory, ProofStatus, Specification};
use clean_verify::test_utils::build_spec_with_stack;

fn assert_in_env(spec: &Specification, name: &str) {
    assert!(
        spec.env().get_const(&Name::from_string(name)).is_some(),
        "{name} should be registered in the spec environment"
    );
}

/// The reduct function + spine/list substrate are registered (kernel-checked).
#[test]
fn iota_reduct_and_substrate_registered() {
    let spec = build_spec_with_stack();
    for name in [
        // C.1 substrate
        "opt_bind",
        "list_append",
        "apply_spine",
        "kapp_args",
        "list_tail",
        "list_head",
        "list_drop",
        "list_take",
        "list_length",
        "kexpr_const_name",
        // C.2 reduct
        "iota_reduct",
        // C.3 step
        "iota_step",
    ] {
        assert_in_env(&spec, name);
    }
}

/// The keystone: `iota_step_deterministic` is DerivedProved, zero axiom_deps,
/// and depends on the reduct function + some-injectivity.
#[test]
fn iota_step_deterministic_is_derived_proved() {
    let spec = build_spec_with_stack();
    let def = spec
        .definitions()
        .get("iota_step_deterministic")
        .expect("iota_step_deterministic should be registered");

    assert!(
        !def.is_axiom,
        "iota_step_deterministic must not be an axiom"
    );
    assert_eq!(def.category, AxiomCategory::DerivedLemma);
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "iota_step_deterministic should be DerivedProved (closed, kernel-checked term)"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "iota_step_deterministic should carry zero axiom_deps: {:?}",
        def.axiom_deps
    );

    let deps = def
        .dependencies
        .as_ref()
        .expect("iota_step_deterministic should record dependencies");
    for expected in ["iota_reduct", "option_some_inj"] {
        assert!(
            deps.contains(expected),
            "iota_step_deterministic should depend on {expected}: {deps:?}"
        );
    }

    // Signature surface: it is the determinism of the reduct function.
    assert!(
        def.type_src.contains("iota_reduct env e") && def.type_src.contains("Eq KExpr e1 e2"),
        "iota_step_deterministic signature drift: {}",
        def.type_src
    );
}
