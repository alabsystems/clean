// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn matching_schema_claim_and_actual_encodable_module_have_no_prefix_errors() {
    assert!(observed(&clean()).0.is_empty());
}
#[test]
fn exact_schema_mismatch_keeps_full_u32_and_does_not_skip_actual_digest() {
    let mut b = clean();
    b.schema_version = u32::MAX;
    let (rows, o, _) = observed(&b);
    assert_eq!(rows, vec![E::UnsupportedSchemaVersion(u32::MAX)]);
    assert!(
        o.events
            .iter()
            .any(|p| p.phase == ExecutionPhase::CanonicalDigest)
    );
}
#[test]
fn zero_sha_claim_emits_empty_then_the_actual_digest_mismatch() {
    let mut b = clean();
    b.trust_ir_module_digest = ProofDigest::sha256([0; 32]);
    let actual = b.module.stable_digest();
    assert_eq!(
        observed(&b).0,
        vec![
            E::EmptyDigest {
                field: "trust_ir_module_digest"
            },
            E::TrustIrModuleDigestMismatch {
                expected: actual,
                actual: b.trust_ir_module_digest
            }
        ]
    );
}
#[test]
fn zero_legacy_claim_retains_both_independent_digest_checks_before_mismatch() {
    let mut b = clean();
    b.trust_ir_module_digest = legacy_zero();
    let rows = observed(&b).0;
    assert_eq!(rows.len(), 3);
    assert!(matches!(
        rows[0],
        E::EmptyDigest {
            field: "trust_ir_module_digest"
        }
    ));
    assert!(matches!(
        rows[1],
        E::NonCryptographicDigest {
            field: "trust_ir_module_digest"
        }
    ));
    assert!(matches!(rows[2], E::TrustIrModuleDigestMismatch { .. }));
}
#[test]
fn wrong_nonzero_sha_retains_exact_expected_and_actual_fields() {
    let mut b = clean();
    b.trust_ir_module_digest = ProofDigest::sha256([77; 32]);
    assert_eq!(
        observed(&b).0,
        vec![E::TrustIrModuleDigestMismatch {
            expected: b.module.stable_digest(),
            actual: b.trust_ir_module_digest
        }]
    );
}
#[test]
fn nonzero_legacy_algorithm_error_precedes_actual_sha_comparison() {
    let mut b = clean();
    b.trust_ir_module_digest = ProofDigest::trust_ir_stable("legacy", b"nonzero");
    let rows = observed(&b).0;
    assert!(matches!(
        rows[0],
        E::NonCryptographicDigest {
            field: "trust_ir_module_digest"
        }
    ));
    assert!(matches!(rows[1], E::TrustIrModuleDigestMismatch { .. }));
}
#[test]
fn every_actual_wire_class_is_reported_before_any_digest_mismatch_is_possible() {
    let b = bad();
    let (rows, o, _) = observed(&b);
    let mut expected = vec![E::UnsupportedSchemaVersion(u32::MAX)];
    expected.extend(wire_expected(&b));
    assert_eq!(rows, expected);
    assert!(
        !o.events
            .iter()
            .any(|p| p.phase == ExecutionPhase::CanonicalDigest)
    );
}
#[test]
fn schema_zero_algorithm_and_wire_diagnostics_keep_original_full_order() {
    let mut b = bad();
    b.trust_ir_module_digest = legacy_zero();
    let rows = observed(&b).0;
    let mut expected = vec![
        E::UnsupportedSchemaVersion(u32::MAX),
        E::EmptyDigest {
            field: "trust_ir_module_digest",
        },
        E::NonCryptographicDigest {
            field: "trust_ir_module_digest",
        },
    ];
    expected.extend(wire_expected(&b));
    assert_eq!(rows, expected);
}
#[test]
fn whole_actual_module_name_tamper_changes_computed_digest() {
    let mut b = clean();
    let prior = b.trust_ir_module_digest;
    b.module.name.push('!');
    assert_eq!(
        observed(&b).0,
        vec![E::TrustIrModuleDigestMismatch {
            expected: b.module.stable_digest(),
            actual: prior
        }]
    );
}
#[test]
fn current_v3_debug_path_projection_matches_ordinary_module_identity_exactly() {
    let mut b = clean();
    b.module.files = vec!["first λ\0.rs".into()];
    b.trust_ir_module_digest = b.module.stable_digest();
    assert!(observed(&b).0.is_empty());
    b.module.files[0] = "other 尾\0.rs".into();
    assert_eq!(b.trust_ir_module_digest, b.module.stable_digest());
    assert!(observed(&b).0.is_empty());
}
#[test]
fn matching_identity_prefix_is_not_full_bundle_validation_or_authority() {
    let b = clean();
    assert!(observed(&b).0.is_empty());
    assert!(b.validate().is_err());
    assert!(
        b.validate()
            .unwrap_err()
            .iter()
            .any(|e| matches!(e, E::EmptyRequests))
    );
}
#[test]
fn unencodable_zero_claim_skips_hash_instead_of_panicking_or_inventing_digest() {
    let mut b = bad();
    b.trust_ir_module_digest = ProofDigest::sha256([0; 32]);
    let (rows, o, _) = observed(&b);
    assert!(rows.iter().any(|e| matches!(e, E::EmptyDigest { .. })));
    assert!(
        !rows
            .iter()
            .any(|e| matches!(e, E::TrustIrModuleDigestMismatch { .. }))
    );
    assert!(
        !o.events
            .iter()
            .any(|p| p.phase == ExecutionPhase::CanonicalDigest)
    );
}
