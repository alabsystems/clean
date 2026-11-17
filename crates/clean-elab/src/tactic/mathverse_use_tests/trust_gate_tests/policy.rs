// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Test code by its own head: the source gates read a file-level #![cfg(test)]
// as proof (headed_cfg_test in scripts/check_add_decl_ratchet.py).
#![cfg(test)]

use super::*;

#[test]
fn test_trust_gate_strict_rejects_unverified() {
    let gate = TrustGate::Strict;
    assert!(!gate.accepts(ImportConfidence::Unverified));
    assert!(!gate.accepts(ImportConfidence::Translated));
    assert!(!gate.accepts(ImportConfidence::Axiomatized));
    assert!(!gate.accepts(ImportConfidence::SourceVerified));
}

#[test]
fn test_trust_gate_strict_accepts_kernel_verified() {
    let gate = TrustGate::Strict;
    assert!(gate.accepts(ImportConfidence::KernelVerified));
}

#[test]
fn test_trust_gate_relaxed_accepts_source_verified() {
    let gate = TrustGate::Relaxed;
    assert!(gate.accepts(ImportConfidence::KernelVerified));
    assert!(gate.accepts(ImportConfidence::SourceVerified));
    assert!(!gate.accepts(ImportConfidence::Translated));
    assert!(!gate.accepts(ImportConfidence::Unverified));
}

#[test]
fn test_trust_gate_relaxed_foundational_confidence_only_is_kernel_verified() {
    // On confidence alone (the candidate-level pre-filter), RelaxedFoundational
    // is byte-identical to Strict — KernelVerified only. A bare confidence
    // cannot prove a constant is a foundational axiom.
    let gate = TrustGate::RelaxedFoundational;
    assert!(gate.accepts(ImportConfidence::KernelVerified));
    assert!(!gate.accepts(ImportConfidence::SourceVerified));
    assert!(!gate.accepts(ImportConfidence::Translated));
    assert!(!gate.accepts(ImportConfidence::Axiomatized));
    assert!(!gate.accepts(ImportConfidence::Unverified));
}

#[test]
fn test_accepts_dependency_relaxed_foundational_admits_foundational_axiom() {
    let gate = TrustGate::RelaxedFoundational;
    // A genuine foundational axiom: declared as Axiom, name in the kernel's
    // FOUNDATIONAL_AXIOMS allowlist, even though it is not KernelVerified.
    for name in ["propext", "Quot.sound", "Classical.choice"] {
        assert!(
            gate.accepts_dependency(ImportConfidence::Axiomatized, DeclKind::Axiom, name),
            "RelaxedFoundational must admit foundational axiom `{name}`"
        );
        assert!(
            gate.accepts_dependency(ImportConfidence::Unverified, DeclKind::Axiom, name),
            "RelaxedFoundational must admit foundational axiom `{name}` regardless of confidence"
        );
    }
}

#[test]
fn test_accepts_dependency_relaxed_foundational_rejects_domain_axiom() {
    let gate = TrustGate::RelaxedFoundational;
    // A domain-specific axiom (NOT in FOUNDATIONAL_AXIOMS) must be rejected
    // even though it is declared as an Axiom.
    assert!(!gate.accepts_dependency(
        ImportConfidence::Axiomatized,
        DeclKind::Axiom,
        "MyDomain.bigConjecture"
    ));
    // `Rat.left_distrib` is a real ADMITTED_DOMAIN_AXIOMS-class name that
    // `is_foundational_axiom` returns false for: must be rejected.
    assert!(!gate.accepts_dependency(
        ImportConfidence::Axiomatized,
        DeclKind::Axiom,
        "Rat.left_distrib"
    ));
    // Trust markers are never foundational.
    assert!(!gate.accepts_dependency(ImportConfidence::Axiomatized, DeclKind::Axiom, "sorryAx"));
}

#[test]
fn test_accepts_dependency_relaxed_foundational_requires_axiom_kind() {
    let gate = TrustGate::RelaxedFoundational;
    // A NON-axiom declaration that merely shares a foundational name must
    // NOT slip through: the foundational branch requires DeclKind::Axiom.
    // (Only meaningful when not KernelVerified.)
    assert!(!gate.accepts_dependency(ImportConfidence::Axiomatized, DeclKind::Theorem, "propext"));
    assert!(!gate.accepts_dependency(
        ImportConfidence::Axiomatized,
        DeclKind::Definition,
        "Classical.choice"
    ));
}

#[test]
fn test_accepts_dependency_strict_and_relaxed_ignore_foundational_axioms() {
    // Strict / Relaxed must be byte-identical to confidence-only acceptance:
    // a foundational axiom that is NOT KernelVerified is rejected by both
    // (no RelaxedFoundational widening leaks into them).
    assert!(!TrustGate::Strict.accepts_dependency(
        ImportConfidence::Axiomatized,
        DeclKind::Axiom,
        "propext"
    ));
    assert!(!TrustGate::Relaxed.accepts_dependency(
        ImportConfidence::Axiomatized,
        DeclKind::Axiom,
        "propext"
    ));
    // But a KernelVerified dep is accepted by all gates (the shared half).
    for gate in [
        TrustGate::Strict,
        TrustGate::Relaxed,
        TrustGate::RelaxedFoundational,
    ] {
        assert!(gate.accepts_dependency(
            ImportConfidence::KernelVerified,
            DeclKind::Theorem,
            "Some.kv.theorem"
        ));
    }
}
