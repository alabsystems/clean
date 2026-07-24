// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Individual self-verification proof implementations.

use super::{make_axiomatized_header, make_kernel_header, ProofResult};
use crate::trust::header_gate::{GateTrustPolicy, TrustGateEnforcer};
use crate::trust::policy::propagate_axiom_profiles;
use crate::types::{AxiomProfile, MathverseConstantHeader, NO_VALUE};

// ---------------------------------------------------------------------------
// Proof 1: Codec roundtrip
// ---------------------------------------------------------------------------

/// Encode `MathverseConstantHeader` to bytes, decode, and check field equality.
#[must_use]
pub fn verify_codec_roundtrip() -> ProofResult {
    let headers = [
        make_kernel_header(42, 100, 200, AxiomProfile::CHOICE | AxiomProfile::LEM),
        make_axiomatized_header(7, 11, AxiomProfile::HOL_AXIOMS),
        make_kernel_header(0, 0, NO_VALUE, AxiomProfile::NONE),
        make_kernel_header(
            u32::MAX - 1,
            u32::MAX - 2,
            u32::MAX - 3,
            AxiomProfile::new(u64::MAX),
        ),
    ];

    for (i, original) in headers.iter().enumerate() {
        let bytes = original.to_bytes();
        let restored = MathverseConstantHeader::from_bytes(&bytes);
        if !headers_equal(original, &restored) {
            return ProofResult {
                name: "codec_roundtrip".to_owned(),
                passed: false,
                evidence: format!("header[{i}] field mismatch after encode/decode roundtrip"),
            };
        }
    }

    ProofResult {
        name: "codec_roundtrip".to_owned(),
        passed: true,
        evidence: format!(
            "all {} headers survived encode/decode roundtrip",
            headers.len()
        ),
    }
}

fn headers_equal(a: &MathverseConstantHeader, b: &MathverseConstantHeader) -> bool {
    a.name_idx == b.name_idx
        && a.type_idx == b.type_idx
        && a.value_idx == b.value_idx
        && a.source_system == b.source_system
        && a.import_confidence == b.import_confidence
        && a.content_domain == b.content_domain
        && a.axiom_profile == b.axiom_profile
        && a.sidecar_digest == b.sidecar_digest
        && a.provenance_idx == b.provenance_idx
}

// ---------------------------------------------------------------------------
// Proof 2: Hash consing
// ---------------------------------------------------------------------------

/// Structurally equal headers produce identical bytes; different headers differ.
#[must_use]
pub fn verify_hash_consing() -> ProofResult {
    let a = make_kernel_header(10, 20, 30, AxiomProfile::CLASSICAL);
    let b = make_kernel_header(10, 20, 30, AxiomProfile::CLASSICAL);
    let c = make_kernel_header(10, 20, 31, AxiomProfile::CLASSICAL);
    let d = make_kernel_header(10, 20, 30, AxiomProfile::AXIOMATIZED);

    let (bytes_a, bytes_b) = (a.to_bytes(), b.to_bytes());
    let (bytes_c, bytes_d) = (c.to_bytes(), d.to_bytes());

    if bytes_a != bytes_b {
        return fail(
            "hash_consing",
            "structurally equal headers produced different bytes",
        );
    }
    if bytes_a == bytes_c {
        return fail(
            "hash_consing",
            "structurally different headers produced identical bytes",
        );
    }
    if bytes_a == bytes_d {
        return fail(
            "hash_consing",
            "different axiom profiles produced identical bytes",
        );
    }

    ProofResult {
        name: "hash_consing".to_owned(),
        passed: true,
        evidence: "equal headers same bytes, different headers different bytes".to_owned(),
    }
}

// ---------------------------------------------------------------------------
// Proof 3: Topological order
// ---------------------------------------------------------------------------

/// Verify `child_idx < parent_idx` for all dependency references.
#[must_use]
pub fn verify_topological_order() -> ProofResult {
    let valid_deps: Vec<Vec<u32>> = vec![vec![], vec![0], vec![0, 1], vec![1, 2], vec![0, 3]];

    let mut checked = 0usize;
    for (parent_idx, dep_list) in valid_deps.iter().enumerate() {
        for &child_idx in dep_list {
            checked += 1;
            if child_idx >= parent_idx as u32 {
                return fail(
                    "topological_order",
                    &format!("valid graph violated: parent {parent_idx} has dep {child_idx}"),
                );
            }
        }
    }

    // Verify that invalid ordering is detected.
    let invalid_deps: Vec<Vec<u32>> = vec![vec![1], vec![]];
    let found_violation = invalid_deps
        .iter()
        .enumerate()
        .any(|(p, deps)| deps.iter().any(|&c| c >= p as u32));

    if !found_violation {
        return fail(
            "topological_order",
            "failed to detect invalid topological order",
        );
    }

    ProofResult {
        name: "topological_order".to_owned(),
        passed: true,
        evidence: format!("{checked} edges verified; invalid order detected correctly"),
    }
}

// ---------------------------------------------------------------------------
// Proof 4: Axiom profile propagation
// ---------------------------------------------------------------------------

/// Verify `profile(T) = own | union(profile(dep) for dep in deps(T))`.
#[must_use]
pub fn verify_axiom_profile_propagation() -> ProofResult {
    let mut constants = build_propagation_test_graph();
    let deps = vec![vec![], vec![0], vec![0, 1], vec![2]];

    if let Err(e) = propagate_axiom_profiles(&mut constants, &deps) {
        return fail(
            "axiom_profile_propagation",
            &format!("propagation failed: {e}"),
        );
    }

    if let Some(msg) = check_propagation_results(&constants) {
        return fail("axiom_profile_propagation", &msg);
    }

    // Verify idempotency: re-propagating should not change anything.
    let before: Vec<AxiomProfile> = constants.iter().map(|c| c.axiom_profile).collect();
    if let Err(e) = propagate_axiom_profiles(&mut constants, &deps) {
        return fail(
            "axiom_profile_propagation",
            &format!("second propagation failed: {e}"),
        );
    }
    let after: Vec<AxiomProfile> = constants.iter().map(|c| c.axiom_profile).collect();
    if before != after {
        return fail("axiom_profile_propagation", "propagation is not idempotent");
    }

    ProofResult {
        name: "axiom_profile_propagation".to_owned(),
        passed: true,
        evidence: format!(
            "propagation correct for {} constants; idempotent",
            constants.len()
        ),
    }
}

fn build_propagation_test_graph() -> Vec<MathverseConstantHeader> {
    vec![
        make_kernel_header(0, 0, 0, AxiomProfile::CHOICE),
        make_kernel_header(1, 1, 1, AxiomProfile::LEM),
        make_kernel_header(2, 2, 2, AxiomProfile::PROP_EXT),
        make_kernel_header(3, 3, 3, AxiomProfile::AXIOMATIZED),
    ]
}

fn check_propagation_results(constants: &[MathverseConstantHeader]) -> Option<String> {
    let expected = [
        AxiomProfile::CHOICE,
        AxiomProfile::LEM | AxiomProfile::CHOICE,
        AxiomProfile::PROP_EXT | AxiomProfile::CHOICE | AxiomProfile::LEM,
        AxiomProfile::AXIOMATIZED
            | AxiomProfile::PROP_EXT
            | AxiomProfile::CHOICE
            | AxiomProfile::LEM,
    ];
    for (i, (actual, exp)) in constants
        .iter()
        .map(|c| c.axiom_profile)
        .zip(expected.iter())
        .enumerate()
    {
        if actual != *exp {
            return Some(format!(
                "constant[{i}] profile mismatch: got {actual:?}, expected {exp:?}"
            ));
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Proof 5: Trust no leakage
// ---------------------------------------------------------------------------

/// Axiomatized cannot reach kernel-verified under the default (strict) policy.
#[must_use]
pub fn verify_trust_no_leakage() -> ProofResult {
    let strict = GateTrustPolicy::default();

    if let Some(msg) = check_gated_visibility(&strict) {
        return fail("trust_no_leakage", &msg);
    }

    // Verify filter_visible counts.
    let all_headers = build_leakage_test_headers();
    let visible = TrustGateEnforcer::filter_visible(&all_headers, &strict);
    if visible.len() != 2 {
        return fail(
            "trust_no_leakage",
            &format!("filter_visible returned {} (expected 2)", visible.len()),
        );
    }

    ProofResult {
        name: "trust_no_leakage".to_owned(),
        passed: true,
        evidence: format!(
            "strict policy correctly gates {} of {} constants",
            all_headers.len() - visible.len(),
            all_headers.len()
        ),
    }
}

fn check_gated_visibility(policy: &GateTrustPolicy) -> Option<String> {
    let cases: &[(MathverseConstantHeader, bool, &str)] = &[
        (
            make_kernel_header(0, 0, 0, AxiomProfile::NONE),
            true,
            "pure constant",
        ),
        (
            make_axiomatized_header(1, 1, AxiomProfile::NONE),
            false,
            "axiomatized constant",
        ),
        (
            make_kernel_header(2, 2, 2, AxiomProfile::UNIVERSE_INCON),
            false,
            "UNIVERSE_INCON",
        ),
        (
            make_kernel_header(3, 3, 3, AxiomProfile::FLOAT_APPROX),
            false,
            "FLOAT_APPROX",
        ),
        (
            make_kernel_header(4, 4, 4, AxiomProfile::NN_ABSTRACTION),
            false,
            "NN_ABSTRACTION",
        ),
        (
            make_kernel_header(5, 5, 5, AxiomProfile::CHOICE | AxiomProfile::LEM),
            true,
            "non-gated axiom bits",
        ),
    ];
    for (header, expected, label) in cases {
        let actual = TrustGateEnforcer::is_visible(header, policy);
        if actual != *expected {
            let direction = if *expected {
                "not visible"
            } else {
                "visible (leakage!)"
            };
            return Some(format!("{label} is {direction} under strict policy"));
        }
    }
    None
}

fn build_leakage_test_headers() -> Vec<MathverseConstantHeader> {
    vec![
        make_kernel_header(0, 0, 0, AxiomProfile::NONE),
        make_axiomatized_header(1, 1, AxiomProfile::NONE),
        make_kernel_header(2, 2, 2, AxiomProfile::UNIVERSE_INCON),
        make_kernel_header(3, 3, 3, AxiomProfile::FLOAT_APPROX),
        make_kernel_header(4, 4, 4, AxiomProfile::NN_ABSTRACTION),
        make_kernel_header(5, 5, 5, AxiomProfile::CHOICE | AxiomProfile::LEM),
    ]
}

// ---------------------------------------------------------------------------
// Shared helper
// ---------------------------------------------------------------------------

fn fail(name: &str, evidence: &str) -> ProofResult {
    ProofResult {
        name: name.to_owned(),
        passed: false,
        evidence: evidence.to_owned(),
    }
}
