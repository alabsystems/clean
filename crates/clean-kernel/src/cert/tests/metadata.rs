// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::cert::*;

fn sample_metadata() -> ProofArchiveMetadata {
    ProofArchiveMetadata::new(
        "clean-kernel",
        "0.1.0",
        Some("abc123".to_string()),
        1_717_171_717,
        "metadata-test",
        TrustLevel::KernelVerified,
        vec!["clean-kernel".to_string()],
        "Foo.bar",
        42,
    )
}

#[test]
fn test_metadata_new_preserves_backward_compatible_defaults() {
    let metadata = sample_metadata();

    assert_eq!(metadata.archive_format, ArchiveFormat::Binary);
    assert_eq!(metadata.distribution, None);
    assert!(metadata.dependencies.is_empty());
    assert!(metadata.verification_chain.is_empty());
    assert!(metadata.validate_chain().is_ok());
}

#[test]
fn test_metadata_deserializes_missing_new_fields_with_defaults() {
    let json = r#"{
        "prover":"clean-kernel",
        "version":"0.1.0",
        "commit_hash":"abc123",
        "timestamp":1717171717,
        "produced_by":"metadata-test",
        "trust_level":"KernelVerified",
        "trusted_components":["clean-kernel"],
        "theorem_name":"Foo.bar",
        "theorem_type_hash":42
    }"#;

    let metadata: ProofArchiveMetadata =
        serde_json::from_str(json).expect("deserialize metadata with missing new fields");

    assert_eq!(metadata.archive_format, ArchiveFormat::Binary);
    assert_eq!(metadata.distribution, None);
    assert!(metadata.dependencies.is_empty());
    assert!(metadata.verification_chain.is_empty());
}

#[test]
fn test_metadata_validate_chain_accepts_monotonic_steps() {
    let mut metadata = sample_metadata();
    metadata.archive_format = ArchiveFormat::Compact;
    metadata.distribution = Some(DistributionInfo::new("deadbeef", 4_096, "zstd"));
    metadata.dependencies = vec![ArchiveDependency::new(
        "stdlib",
        "1.0.0",
        "feedface",
        TrustLevel::KernelVerified,
    )];
    metadata.verification_chain = vec![
        VerificationStep::new(
            "decode archive",
            "serde-json",
            1_717_171_800,
            TrustLevel::Unverified,
        ),
        VerificationStep::new(
            "kernel replay",
            "clean-kernel",
            1_717_171_900,
            TrustLevel::KernelVerified,
        ),
    ];

    assert!(metadata.validate_chain().is_ok());
}

#[test]
fn test_metadata_validate_chain_rejects_timestamp_regression() {
    let mut metadata = sample_metadata();
    metadata.verification_chain = vec![
        VerificationStep::new("decode archive", "serde-json", 200, TrustLevel::Unverified),
        VerificationStep::new(
            "kernel replay",
            "clean-kernel",
            150,
            TrustLevel::KernelVerified,
        ),
    ];

    let err = metadata
        .validate_chain()
        .expect_err("timestamp regression should fail validation");

    assert_eq!(
        err,
        MetadataValidationError::NonMonotonicTimestamp {
            index: 1,
            previous_timestamp: 200,
            timestamp: 150,
        }
    );
}

#[test]
fn test_metadata_validate_chain_rejects_blank_verifier() {
    let mut metadata = sample_metadata();
    metadata.verification_chain = vec![VerificationStep::new(
        "kernel replay",
        "   ",
        200,
        TrustLevel::KernelVerified,
    )];

    let err = metadata
        .validate_chain()
        .expect_err("blank verifier should fail validation");

    assert_eq!(err, MetadataValidationError::EmptyVerifier { index: 0 });
}

#[test]
fn test_metadata_validate_chain_rejects_blank_step_name() {
    let mut metadata = sample_metadata();
    metadata.verification_chain = vec![VerificationStep::new(
        "   ",
        "clean-kernel",
        200,
        TrustLevel::KernelVerified,
    )];

    let err = metadata
        .validate_chain()
        .expect_err("blank step name should fail validation");

    assert_eq!(err, MetadataValidationError::EmptyStepName { index: 0 });
}
