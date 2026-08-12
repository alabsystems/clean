// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! I1 — the KERNEL MARKER, mechanism 3 of the binding invariant.
//!
//! Ruling of record: `docs/design/2026-08-05-i1-ruling-header-elaboration.md`
//! (Trust superproject). Header-first elaboration keeps provisional headers
//! structurally out of the authoritative environment, and that is the real
//! firewall. This file tests the DEFENCE IN DEPTH behind it: if a staging
//! environment ever escaped its batch, the environment must say so rather than
//! look like an ordinary one carrying an author-written assumption.
//!
//! The distinction is not decorative. Both a staged header and an `axiom` block
//! certification, so a test that only checked `is_certified()` would pass with
//! the marker deleted. What must hold is that they are reported DIFFERENTLY: a
//! header grades as `Staged` — a checker state that no one wrote — while an
//! `axiom` grades as a non-foundational assumption the author did write and can
//! be held to.
//!
//!   1. `test_a_staged_header_is_reported_as_staged` — the positive.
//!   2. `test_an_ordinary_axiom_is_not_reported_as_staged` — the CONTROL that
//!      must fail if the marker were applied to every value-free constant,
//!      which would make it meaningless.
//!   3. `test_discharging_a_header_clears_the_marker` — MUST-FAIL control for
//!      the discharge path: after a header is replaced by the real declaration,
//!      the environment must be authoritative again. A marker that could not be
//!      cleared would make every batch permanently untrusted.

use clean_kernel::env::CertificationIssue;
use clean_kernel::env::Environment;
use clean_kernel::{Declaration, Expr, Name};

/// `False`, and a value-free constant of that type — the sharpest possible
/// case, because anything proving `False` must never be certified.
fn false_type() -> Expr {
    Expr::const_(Name::from_string("False"), vec![])
}

fn axiom_decl(name: &str) -> Declaration {
    Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_: false_type(),
    }
}

#[test]
fn test_a_staged_header_is_reported_as_staged() {
    let mut env = Environment::with_prelude();
    env.add_staged_header(axiom_decl("staged_false"))
        .expect("a well-typed signature must stage");

    let name = Name::from_string("staged_false");
    assert!(
        env.is_staged_header(&name),
        "the environment does not know `staged_false` is provisional"
    );
    assert!(
        env.has_staged_headers(),
        "an environment holding a provisional header must report itself as \
         non-authoritative"
    );

    let term = Expr::const_(name.clone(), vec![]);
    let audit = env.audit_certification(&false_type(), &term);
    assert!(
        !audit.is_certified(),
        "CERTIFIED a proof of False that rests on a staged header"
    );
    assert!(
        audit.issues.iter().any(
            |issue| matches!(issue, CertificationIssue::Staged { name: found } if found == &name)
        ),
        "the audit did not report `staged_false` as Staged. Without that arm a \
         staged header is reported as a NonFoundationalAxiom — i.e. as an \
         assumption the author made — which is the misreading staging exists to \
         prevent. Issues: {:?}",
        audit.issues
    );
}

/// CONTROL — the marker must distinguish. If every value-free constant were
/// reported as staged, the classification would carry no information.
#[test]
fn test_an_ordinary_axiom_is_not_reported_as_staged() {
    let mut env = Environment::with_prelude();
    env.add_decl(axiom_decl("written_false"))
        .expect("an axiom must register");

    let name = Name::from_string("written_false");
    assert!(
        !env.is_staged_header(&name),
        "an author-written `axiom` must NOT be marked as a staged header"
    );
    assert!(
        !env.has_staged_headers(),
        "an environment holding only author-written axioms is still \
         authoritative: {:?}",
        env.staged_header_names()
    );

    let term = Expr::const_(name.clone(), vec![]);
    let audit = env.audit_certification(&false_type(), &term);
    assert!(
        !audit.is_certified(),
        "CERTIFIED a proof of False resting on a non-foundational axiom"
    );
    assert!(
        !audit
            .issues
            .iter()
            .any(|issue| matches!(issue, CertificationIssue::Staged { .. })),
        "an author-written `axiom` was reported as Staged: {:?}",
        audit.issues
    );
    assert!(
        audit.issues.iter().any(|issue| matches!(
            issue,
            CertificationIssue::NonFoundationalAxiom { name: found } if found == &name
        )),
        "an author-written `axiom` must still be DISCLOSED by name as a \
         non-foundational assumption: {:?}",
        audit.issues
    );
}

/// MUST-FAIL control for the discharge path. A marker that could not be cleared
/// would make every batch permanently non-authoritative — and `forget_decl` is
/// not enough, because it leaves the marker and the metadata tables behind.
#[test]
fn test_discharging_a_header_clears_the_marker() {
    let mut env = Environment::with_prelude();
    let name = Name::from_string("staged_false");
    env.add_staged_header(axiom_decl("staged_false"))
        .expect("a well-typed signature must stage");

    assert!(
        env.discharge_staged_header(&name),
        "discharging a staged header must succeed"
    );
    assert!(
        !env.has_staged_headers(),
        "the environment still reports staged headers after discharge: {:?}",
        env.staged_header_names()
    );
    assert!(
        env.get_const(&name).is_none(),
        "discharge left the constant behind, so the header is still citable"
    );

    // Fail-closed the other way: discharge must refuse a name that is NOT a
    // staged header, or it becomes a way to delete a kernel-checked
    // declaration.
    env.add_decl(axiom_decl("written_false"))
        .expect("an axiom must register");
    let written = Name::from_string("written_false");
    assert!(
        !env.discharge_staged_header(&written),
        "discharge accepted a name that is not a staged header — that turns a \
         staging helper into a way to remove a checked declaration"
    );
    assert!(
        env.get_const(&written).is_some(),
        "discharge removed an author-written axiom"
    );
}
