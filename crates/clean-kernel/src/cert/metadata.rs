// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof archive metadata types.
//!
//! These types capture the provenance and trust posture of serialized proof
//! archives so external tooling can inspect archives without decoding the full
//! certificate payload first.

use serde::{Deserialize, Serialize};

/// Trust level attached to a proof archive.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum TrustLevel {
    /// Verified directly by the kernel.
    KernelVerified,
    /// Backed by an SMT solver or similar external checker.
    SmtBacked,
    /// Depends on an axiom.
    Axiom,
    /// Not independently verified.
    Unverified,
}

/// Dependency metadata attached to a proof archive.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ArchiveDependency {
    /// Dependency name.
    pub name: String,
    /// Dependency version string.
    pub version: String,
    /// Dependency content or provenance hash.
    pub hash: String,
    /// Trust level assigned to the dependency.
    pub trust_level: TrustLevel,
}

impl ArchiveDependency {
    /// Construct archive dependency metadata.
    pub fn new(
        name: impl Into<String>,
        version: impl Into<String>,
        hash: impl Into<String>,
        trust_level: TrustLevel,
    ) -> Self {
        Self {
            name: name.into(),
            version: version.into(),
            hash: hash.into(),
            trust_level,
        }
    }
}

/// A single verification step recorded for a proof archive.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VerificationStep {
    /// Human-readable step name.
    pub step: String,
    /// Tool or component that performed the verification step.
    pub verifier: String,
    /// Unix timestamp in seconds when the step completed.
    pub timestamp: u64,
    /// Trust level established by this step.
    pub trust_level: TrustLevel,
}

impl VerificationStep {
    /// Construct a verification step entry.
    pub fn new(
        step: impl Into<String>,
        verifier: impl Into<String>,
        timestamp: u64,
        trust_level: TrustLevel,
    ) -> Self {
        Self {
            step: step.into(),
            verifier: verifier.into(),
            timestamp,
            trust_level,
        }
    }
}

/// Ordered verification steps attached to an archive.
pub type VerificationChain = Vec<VerificationStep>;

/// Distribution details for a serialized proof archive.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DistributionInfo {
    /// SHA-256 content hash for the serialized archive.
    pub content_hash: String,
    /// Serialized archive size in bytes.
    pub size: u64,
    /// Compression method applied to the archive payload.
    pub compression_method: String,
}

impl DistributionInfo {
    /// Construct distribution metadata.
    pub fn new(
        content_hash: impl Into<String>,
        size: u64,
        compression_method: impl Into<String>,
    ) -> Self {
        Self {
            content_hash: content_hash.into(),
            size,
            compression_method: compression_method.into(),
        }
    }
}

/// Serialized archive encoding format.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Default)]
pub enum ArchiveFormat {
    /// Binary serialization such as bincode.
    #[default]
    Binary,
    /// JSON serialization.
    Json,
    /// Compact custom archive encoding.
    Compact,
}

/// Metadata validation failures for verification chains.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum MetadataValidationError {
    /// A verification step name is blank.
    #[error("verification step {index} has an empty step name")]
    EmptyStepName { index: usize },
    /// A verifier name is blank.
    #[error("verification step {index} has an empty verifier")]
    EmptyVerifier { index: usize },
    /// Verification timestamps must be monotonic.
    #[error(
        "verification step {index} has timestamp {timestamp} earlier than previous timestamp {previous_timestamp}"
    )]
    NonMonotonicTimestamp {
        index: usize,
        previous_timestamp: u64,
        timestamp: u64,
    },
}

/// Metadata describing a serialized proof archive.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofArchiveMetadata {
    /// Name of the prover that produced the archive.
    pub prover: String,
    /// Prover version string.
    pub version: String,
    /// Source-control commit hash for the prover build, if available.
    pub commit_hash: Option<String>,
    /// Unix timestamp in seconds when the archive was produced.
    pub timestamp: u64,
    /// Tool or pipeline that produced the archive.
    pub produced_by: String,
    /// Overall trust level of the archived proof.
    pub trust_level: TrustLevel,
    /// Components trusted during proof production.
    pub trusted_components: Vec<String>,
    /// Fully qualified theorem name.
    pub theorem_name: String,
    /// Hash of the theorem type.
    pub theorem_type_hash: u64,
    /// Archive encoding format.
    #[serde(default)]
    pub archive_format: ArchiveFormat,
    /// Distribution details for the serialized archive, if available.
    #[serde(default)]
    pub distribution: Option<DistributionInfo>,
    /// External archive dependencies and their trust posture.
    #[serde(default)]
    pub dependencies: Vec<ArchiveDependency>,
    /// Ordered verification steps for the archive.
    #[serde(default)]
    pub verification_chain: VerificationChain,
}

impl ProofArchiveMetadata {
    /// Construct proof archive metadata.
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        prover: impl Into<String>,
        version: impl Into<String>,
        commit_hash: Option<String>,
        timestamp: u64,
        produced_by: impl Into<String>,
        trust_level: TrustLevel,
        trusted_components: Vec<String>,
        theorem_name: impl Into<String>,
        theorem_type_hash: u64,
    ) -> Self {
        Self {
            prover: prover.into(),
            version: version.into(),
            commit_hash,
            timestamp,
            produced_by: produced_by.into(),
            trust_level,
            trusted_components,
            theorem_name: theorem_name.into(),
            theorem_type_hash,
            archive_format: ArchiveFormat::default(),
            distribution: None,
            dependencies: Vec::new(),
            verification_chain: Vec::new(),
        }
    }

    /// Validate the recorded verification chain for basic consistency.
    pub fn validate_chain(&self) -> Result<(), MetadataValidationError> {
        let mut previous_timestamp = None;

        for (index, step) in self.verification_chain.iter().enumerate() {
            if step.step.trim().is_empty() {
                return Err(MetadataValidationError::EmptyStepName { index });
            }
            if step.verifier.trim().is_empty() {
                return Err(MetadataValidationError::EmptyVerifier { index });
            }
            if let Some(previous_timestamp) = previous_timestamp {
                if step.timestamp < previous_timestamp {
                    return Err(MetadataValidationError::NonMonotonicTimestamp {
                        index,
                        previous_timestamp,
                        timestamp: step.timestamp,
                    });
                }
            }
            previous_timestamp = Some(step.timestamp);
        }

        Ok(())
    }
}
