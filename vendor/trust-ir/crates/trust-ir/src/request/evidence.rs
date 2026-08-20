// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Result artifact kind carried by a typed native evidence bundle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum NativeEvidenceArtifactKind {
    TrustVcCertificateImport,
    TrustVcMergedCertificate,
    TrustMcHornClauses,
    TrustMcPdrTrace,
    TrustMcModel,
    TrustWpVerificationCondition,
    TrustWpReplayTrace,
    TrustWpAbducedPrecondition,
    ReplayTranscript,
    Other,
    Btor2Trace,
    Btor2Proof,
    NativeCompiledArtifact,
    BackendCapabilityMetadata,
}

impl NativeEvidenceArtifactKind {
    pub const fn code(self) -> &'static str {
        match self {
            NativeEvidenceArtifactKind::TrustVcCertificateImport => "trust_vc_certificate_import",
            NativeEvidenceArtifactKind::TrustVcMergedCertificate => "trust_vc_merged_certificate",
            NativeEvidenceArtifactKind::TrustMcHornClauses => "trust_mc_horn_clauses",
            NativeEvidenceArtifactKind::TrustMcPdrTrace => "trust_mc_pdr_trace",
            NativeEvidenceArtifactKind::TrustMcModel => "trust_mc_model",
            NativeEvidenceArtifactKind::TrustWpVerificationCondition => {
                "trust_wp_verification_condition"
            }
            NativeEvidenceArtifactKind::TrustWpReplayTrace => "trust_wp_replay_trace",
            NativeEvidenceArtifactKind::TrustWpAbducedPrecondition => {
                "trust_wp_abduced_precondition"
            }
            NativeEvidenceArtifactKind::ReplayTranscript => "replay_transcript",
            NativeEvidenceArtifactKind::Other => "other",
            NativeEvidenceArtifactKind::Btor2Trace => "btor2_trace",
            NativeEvidenceArtifactKind::Btor2Proof => "btor2_proof",
            NativeEvidenceArtifactKind::NativeCompiledArtifact => "native_compiled_artifact",
            NativeEvidenceArtifactKind::BackendCapabilityMetadata => "backend_capability_metadata",
        }
    }
}

/// Whether a resolved artifact may be treated as authoritative evidence.
///
/// This is derived by TrustIr during byte resolution. Producers do not set it on
/// attachments, so downstream consumers can fail closed on `informational`
/// without trusting a local string convention.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum NativeEvidenceArtifactAuthority {
    Informational,
    Authoritative,
}

impl NativeEvidenceArtifactAuthority {
    pub const fn code(self) -> &'static str {
        match self {
            NativeEvidenceArtifactAuthority::Informational => "informational",
            NativeEvidenceArtifactAuthority::Authoritative => "authoritative",
        }
    }
}

/// Digest-bound artifact produced by a native verifier run.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeEvidenceArtifact {
    pub name: String,
    pub kind: NativeEvidenceArtifactKind,
    pub digest: ProofDigest,
}

impl NativeEvidenceArtifact {
    pub fn new(
        name: impl Into<String>,
        kind: NativeEvidenceArtifactKind,
        digest: ProofDigest,
    ) -> Self {
        Self {
            name: name.into(),
            kind,
            digest,
        }
    }
}

/// Typed lookup key for verifier artifact byte attachments.
///
/// The key deliberately excludes file paths and display strings. Downstream
/// consumers should resolve artifact bytes by request id, typed artifact kind,
/// digest algorithm, and digest, then pass the resolved bytes to the verifier
/// suite that owns acceptance.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeEvidenceArtifactAttachmentKey {
    pub request: NativeRequestId,
    pub kind: NativeEvidenceArtifactKind,
    pub digest_algorithm: ProofDigestAlgorithm,
    pub digest: ProofDigest,
}

impl NativeEvidenceArtifactAttachmentKey {
    pub const fn new(
        request: NativeRequestId,
        kind: NativeEvidenceArtifactKind,
        digest_algorithm: ProofDigestAlgorithm,
        digest: ProofDigest,
    ) -> Self {
        Self {
            request,
            kind,
            digest_algorithm,
            digest,
        }
    }

    pub const fn for_artifact(request: NativeRequestId, artifact: &NativeEvidenceArtifact) -> Self {
        Self {
            request,
            kind: artifact.kind,
            digest_algorithm: artifact.digest.algorithm,
            digest: artifact.digest,
        }
    }
}

/// Byte attachment for a digest-bound native evidence artifact.
///
/// This is a typed sidecar boundary, not a solver acceptance decision. TrustIr
/// verifies that the bytes match a bundle artifact descriptor and returns the
/// bytes only through a resolved report. The verifier suite named by
/// `owner_suite` remains responsible for interpreting those bytes.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeEvidenceArtifactAttachment {
    pub key: NativeEvidenceArtifactAttachmentKey,
    pub owner_suite: NativeVerifierSuite,
    pub source_identity: String,
    pub bytes: Vec<u8>,
}

impl NativeEvidenceArtifactAttachment {
    pub fn new(
        request: NativeRequestId,
        owner_suite: NativeVerifierSuite,
        kind: NativeEvidenceArtifactKind,
        digest: ProofDigest,
        source_identity: impl Into<String>,
        bytes: impl Into<Vec<u8>>,
    ) -> Self {
        Self {
            key: NativeEvidenceArtifactAttachmentKey::new(request, kind, digest.algorithm, digest),
            owner_suite,
            source_identity: source_identity.into(),
            bytes: bytes.into(),
        }
    }

    pub fn for_artifact(
        request: NativeRequestId,
        owner_suite: NativeVerifierSuite,
        artifact: &NativeEvidenceArtifact,
        source_identity: impl Into<String>,
        bytes: impl Into<Vec<u8>>,
    ) -> Self {
        Self {
            key: NativeEvidenceArtifactAttachmentKey::for_artifact(request, artifact),
            owner_suite,
            source_identity: source_identity.into(),
            bytes: bytes.into(),
        }
    }

    pub fn digest_for_bytes(algorithm: ProofDigestAlgorithm, bytes: &[u8]) -> ProofDigest {
        match algorithm {
            ProofDigestAlgorithm::Sha256 => ProofDigest::sha256(sha256(bytes)),
            ProofDigestAlgorithm::TrustIrStableV1 => {
                ProofDigest::trust_ir_stable("trust_ir.native.evidence.artifact.bytes.v1", bytes)
            }
        }
    }
}

/// Resolution status for a typed native evidence artifact byte attachment.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum NativeEvidenceArtifactResolutionStatus {
    Resolved,
    Blocked,
}

impl NativeEvidenceArtifactResolutionStatus {
    pub const fn code(self) -> &'static str {
        match self {
            NativeEvidenceArtifactResolutionStatus::Resolved => "resolved",
            NativeEvidenceArtifactResolutionStatus::Blocked => "blocked",
        }
    }
}

/// Fail-closed reason for artifact byte attachment resolution.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum NativeEvidenceArtifactResolutionReason {
    Resolved,
    BundleInvalid,
    RequestUnknown,
    MissingEvidenceBundle,
    UnsupportedArtifactKind,
    MissingArtifactDescriptor,
    DigestAlgorithmMismatch,
    NonCryptographicDigestAlgorithm,
    DigestMismatch,
    MissingAttachment,
    DuplicateAttachment,
    OwnerSuiteMismatch,
    InvalidSourceIdentity,
    EmptyBytes,
}

impl NativeEvidenceArtifactResolutionReason {
    pub const fn code(self) -> &'static str {
        match self {
            NativeEvidenceArtifactResolutionReason::Resolved => "resolved",
            NativeEvidenceArtifactResolutionReason::BundleInvalid => "bundle_invalid",
            NativeEvidenceArtifactResolutionReason::RequestUnknown => "request_unknown",
            NativeEvidenceArtifactResolutionReason::MissingEvidenceBundle => {
                "missing_evidence_bundle"
            }
            NativeEvidenceArtifactResolutionReason::UnsupportedArtifactKind => {
                "unsupported_artifact_kind"
            }
            NativeEvidenceArtifactResolutionReason::MissingArtifactDescriptor => {
                "missing_artifact_descriptor"
            }
            NativeEvidenceArtifactResolutionReason::DigestAlgorithmMismatch => {
                "digest_algorithm_mismatch"
            }
            NativeEvidenceArtifactResolutionReason::NonCryptographicDigestAlgorithm => {
                "non_cryptographic_digest_algorithm"
            }
            NativeEvidenceArtifactResolutionReason::DigestMismatch => "digest_mismatch",
            NativeEvidenceArtifactResolutionReason::MissingAttachment => "missing_attachment",
            NativeEvidenceArtifactResolutionReason::DuplicateAttachment => "duplicate_attachment",
            NativeEvidenceArtifactResolutionReason::OwnerSuiteMismatch => "owner_suite_mismatch",
            NativeEvidenceArtifactResolutionReason::InvalidSourceIdentity => {
                "invalid_source_identity"
            }
            NativeEvidenceArtifactResolutionReason::EmptyBytes => "empty_bytes",
        }
    }
}

/// Stable key/value row for artifact authority sidecars.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeEvidenceArtifactAuthorityRow {
    pub key: String,
    pub value: String,
}

impl NativeEvidenceArtifactAuthorityRow {
    pub fn new(key: impl Into<String>, value: impl Into<String>) -> Self {
        Self {
            key: key.into(),
            value: value.into(),
        }
    }

    /// Escaped key for line-oriented `key=value` authority evidence output.
    pub fn escaped_key(&self) -> String {
        escape_manifest_component(&self.key)
    }

    /// Escaped value for line-oriented `key=value` authority evidence output.
    pub fn escaped_value(&self) -> String {
        escape_manifest_component(&self.value)
    }

    /// Stable one-line `key=value` representation.
    ///
    /// Backslash, equals, and control characters are escaped so MCC and schema
    /// consumers can preserve rows without inventing local escaping.
    pub fn to_key_value_line(&self) -> String {
        format!("{}={}", self.escaped_key(), self.escaped_value())
    }
}

/// Stable descriptor for artifact authority evidence row vocabularies.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NativeEvidenceArtifactAuthorityRowDescriptor {
    pub schema: &'static str,
    pub schema_version: u32,
    pub report_row_keys: &'static [&'static str],
    pub resolution_row_keys: &'static [&'static str],
}

impl NativeEvidenceArtifactAuthorityRowDescriptor {
    /// Whether rows exactly match the report row vocabulary and order.
    pub fn report_row_keys_match(&self, rows: &[NativeEvidenceArtifactAuthorityRow]) -> bool {
        artifact_authority_row_keys_match(rows, self.report_row_keys)
    }

    /// Whether rows exactly match the resolution row vocabulary and order.
    pub fn resolution_row_keys_match(&self, rows: &[NativeEvidenceArtifactAuthorityRow]) -> bool {
        artifact_authority_row_keys_match(rows, self.resolution_row_keys)
    }

    /// Emit a compact JSON-free vocabulary manifest for schema generators.
    pub fn manifest_rows(&self) -> Vec<NativeSharedPrimitiveContractManifestRow> {
        let mut rows = Vec::new();
        push_manifest_row(&mut rows, "authority_row_descriptor.schema", self.schema);
        push_manifest_row(
            &mut rows,
            "authority_row_descriptor.schema_version",
            self.schema_version.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "authority_row_descriptor.report_key_count",
            self.report_row_keys.len().to_string(),
        );
        push_manifest_row(
            &mut rows,
            "authority_row_descriptor.resolution_key_count",
            self.resolution_row_keys.len().to_string(),
        );
        for (index, key) in self.report_row_keys.iter().enumerate() {
            push_manifest_row(
                &mut rows,
                format!("authority_row_descriptor.report_key.{index}"),
                *key,
            );
        }
        for (index, key) in self.resolution_row_keys.iter().enumerate() {
            push_manifest_row(
                &mut rows,
                format!("authority_row_descriptor.resolution_key.{index}"),
                *key,
            );
        }
        rows
    }

    /// Emit stable escaped `key=value` vocabulary manifest lines.
    pub fn manifest_key_value_lines(&self) -> Vec<String> {
        self.manifest_rows()
            .into_iter()
            .map(|row| row.to_key_value_line())
            .collect()
    }
}

/// Which artifact authority row vocabulary a validation report observed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeEvidenceArtifactAuthorityRowsKind {
    Report,
    Resolution,
}

impl NativeEvidenceArtifactAuthorityRowsKind {
    pub const fn code(self) -> &'static str {
        match self {
            NativeEvidenceArtifactAuthorityRowsKind::Report => "report",
            NativeEvidenceArtifactAuthorityRowsKind::Resolution => "resolution",
        }
    }
}

/// Producer-owned validation result for forwarded artifact authority rows.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeEvidenceArtifactAuthorityRowsValidationReport {
    pub rows_kind: Option<NativeEvidenceArtifactAuthorityRowsKind>,
    pub valid: bool,
    pub diagnostics: Vec<String>,
}

impl NativeEvidenceArtifactAuthorityRowsValidationReport {
    pub fn is_valid(&self) -> bool {
        self.valid
    }

    pub fn fail_closed(&self) -> bool {
        !self.valid
    }

    pub fn diagnostic_count(&self) -> usize {
        self.diagnostics.len()
    }
}

/// Validate TrustIr-owned artifact authority rows forwarded by downstream sidecars.
pub fn validate_native_evidence_artifact_authority_rows(
    rows: &[NativeEvidenceArtifactAuthorityRow],
) -> NativeEvidenceArtifactAuthorityRowsValidationReport {
    let descriptor = native_evidence_artifact_authority_row_descriptor();
    let rows_kind = if descriptor.resolution_row_keys_match(rows) {
        Some(NativeEvidenceArtifactAuthorityRowsKind::Resolution)
    } else if descriptor.report_row_keys_match(rows) {
        Some(NativeEvidenceArtifactAuthorityRowsKind::Report)
    } else {
        None
    };

    let mut diagnostics = Vec::new();
    if rows_kind.is_none() {
        diagnostics.push(format!(
            "row keys do not match artifact authority report or resolution vocabulary: got {} rows",
            rows.len()
        ));
    }

    let values = artifact_authority_row_values(rows);
    let observed = validate_artifact_authority_common_fields(&values, rows_kind, &mut diagnostics);
    if let (Some(NativeEvidenceArtifactAuthorityRowsKind::Resolution), Some(observed)) =
        (rows_kind, observed)
    {
        validate_artifact_authority_resolution_fields(&values, &observed, &mut diagnostics);
    }

    NativeEvidenceArtifactAuthorityRowsValidationReport {
        rows_kind,
        valid: diagnostics.is_empty(),
        diagnostics,
    }
}

/// Validate escaped `key=value` artifact authority evidence lines.
pub fn validate_native_evidence_artifact_authority_key_value_lines(
    lines: &[String],
) -> NativeEvidenceArtifactAuthorityRowsValidationReport {
    let mut rows = Vec::new();
    let mut diagnostics = Vec::new();
    for (index, line) in lines.iter().enumerate() {
        match parse_artifact_authority_key_value_line(line) {
            Some((key, value)) => rows.push(NativeEvidenceArtifactAuthorityRow::new(key, value)),
            None => diagnostics.push(format!("line {index} is not a valid escaped key=value row")),
        }
    }

    let mut report = validate_native_evidence_artifact_authority_rows(&rows);
    report.diagnostics.splice(0..0, diagnostics);
    report.valid = report.diagnostics.is_empty();
    report
}

/// Stable descriptor for artifact authority evidence row vocabularies.
pub const NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_ROW_DESCRIPTOR:
    NativeEvidenceArtifactAuthorityRowDescriptor = NativeEvidenceArtifactAuthorityRowDescriptor {
    schema: NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_ROW_SCHEMA,
    schema_version: NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_ROW_SCHEMA_VERSION,
    report_row_keys: NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_REPORT_ROW_KEYS,
    resolution_row_keys: NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_RESOLUTION_ROW_KEYS,
};

/// Return the TrustIr-owned artifact authority evidence row descriptor.
pub const fn native_evidence_artifact_authority_row_descriptor()
-> NativeEvidenceArtifactAuthorityRowDescriptor {
    NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_ROW_DESCRIPTOR
}

/// Stable metadata for artifact byte attachment resolution.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeEvidenceArtifactResolutionReport {
    pub schema: String,
    pub schema_version: u32,
    pub request: NativeRequestId,
    pub owner_suite: Option<NativeVerifierSuite>,
    pub required_kind: NativeEvidenceArtifactKind,
    pub digest_algorithm: ProofDigestAlgorithm,
    pub digest: ProofDigest,
    pub artifact_name: Option<String>,
    pub byte_source_identity: Option<String>,
    pub byte_len: Option<usize>,
    pub actual_digest: Option<ProofDigest>,
    pub authority: NativeEvidenceArtifactAuthority,
    pub status: NativeEvidenceArtifactResolutionStatus,
    pub reason: NativeEvidenceArtifactResolutionReason,
}

impl NativeEvidenceArtifactResolutionReport {
    pub const fn authority_code(&self) -> &'static str {
        self.authority.code()
    }

    pub const fn status_code(&self) -> &'static str {
        self.status.code()
    }

    pub const fn reason_code(&self) -> &'static str {
        self.reason.code()
    }

    pub const fn is_resolved(&self) -> bool {
        matches!(
            self.status,
            NativeEvidenceArtifactResolutionStatus::Resolved
        )
    }

    pub const fn is_authoritative(&self) -> bool {
        self.is_resolved()
            && matches!(
                self.authority,
                NativeEvidenceArtifactAuthority::Authoritative
            )
    }

    pub const fn fail_closed(&self) -> bool {
        !self.is_authoritative()
    }

    /// Emit stable JSON-free key/value rows for artifact authority evidence.
    ///
    /// These rows duplicate TrustIr's typed resolution decision as flat strings so
    /// MCC/TY sidecars can publish authority status without rebuilding local
    /// boolean or reason-code policy. Row order is part of the schema version.
    pub fn authority_evidence_rows(&self) -> Vec<NativeEvidenceArtifactAuthorityRow> {
        let mut rows = Vec::new();
        push_artifact_authority_row(
            &mut rows,
            "artifact_authority.schema",
            NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_ROW_SCHEMA,
        );
        push_artifact_authority_row(
            &mut rows,
            "artifact_authority.schema_version",
            NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_ROW_SCHEMA_VERSION.to_string(),
        );
        push_artifact_authority_row(&mut rows, "artifact_resolution.schema", &self.schema);
        push_artifact_authority_row(
            &mut rows,
            "artifact_resolution.schema_version",
            self.schema_version.to_string(),
        );
        push_artifact_authority_row(&mut rows, "request.id", self.request.to_string());
        push_artifact_authority_row(
            &mut rows,
            "owner_suite",
            self.owner_suite
                .map(NativeVerifierSuite::code)
                .unwrap_or("none"),
        );
        push_artifact_authority_row(&mut rows, "artifact.kind", self.required_kind.code());
        push_artifact_authority_row(
            &mut rows,
            "artifact.name",
            self.artifact_name.as_deref().unwrap_or("none"),
        );
        push_artifact_authority_row(
            &mut rows,
            "digest.algorithm",
            proof_digest_algorithm_code(self.digest_algorithm),
        );
        push_artifact_authority_row(&mut rows, "digest", self.digest.to_string());
        push_artifact_authority_row(
            &mut rows,
            "byte.source_identity",
            self.byte_source_identity.as_deref().unwrap_or("none"),
        );
        push_artifact_authority_row(
            &mut rows,
            "byte.len",
            self.byte_len
                .map(|len| len.to_string())
                .unwrap_or_else(|| "none".to_string()),
        );
        push_artifact_authority_row(
            &mut rows,
            "actual_digest",
            self.actual_digest
                .map(|digest| digest.to_string())
                .unwrap_or_else(|| "none".to_string()),
        );
        push_artifact_authority_row(&mut rows, "authority", self.authority_code());
        push_artifact_authority_row(&mut rows, "status", self.status_code());
        push_artifact_authority_row(&mut rows, "reason", self.reason_code());
        push_artifact_authority_row(
            &mut rows,
            "report.is_resolved",
            bool_code(self.is_resolved()),
        );
        push_artifact_authority_row(
            &mut rows,
            "report.is_authoritative",
            bool_code(self.is_authoritative()),
        );
        push_artifact_authority_row(
            &mut rows,
            "report.fail_closed",
            bool_code(self.fail_closed()),
        );
        rows
    }

    /// Emit stable escaped `key=value` authority evidence lines.
    pub fn authority_evidence_key_value_lines(&self) -> Vec<String> {
        self.authority_evidence_rows()
            .into_iter()
            .map(|row| row.to_key_value_line())
            .collect()
    }
}

/// Resolved artifact bytes plus the stable report downstream evidence can carry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeEvidenceArtifactResolution<'a> {
    pub report: NativeEvidenceArtifactResolutionReport,
    pub bytes: Option<&'a [u8]>,
}

impl NativeEvidenceArtifactResolution<'_> {
    pub const fn is_resolved(&self) -> bool {
        self.report.is_resolved() && self.bytes.is_some()
    }
}

impl<'a> NativeEvidenceArtifactResolution<'a> {
    pub const fn is_authoritative(&self) -> bool {
        self.report.is_authoritative() && self.bytes.is_some()
    }

    pub fn authoritative_bytes(&self) -> Option<&'a [u8]> {
        if self.is_authoritative() {
            self.bytes
        } else {
            None
        }
    }

    /// Emit authority evidence rows that include byte-presence and final
    /// resolution-level fail-closed state.
    pub fn authority_evidence_rows(&self) -> Vec<NativeEvidenceArtifactAuthorityRow> {
        let mut rows = self.report.authority_evidence_rows();
        push_artifact_authority_row(
            &mut rows,
            "resolution.bytes_present",
            bool_code(self.bytes.is_some()),
        );
        push_artifact_authority_row(
            &mut rows,
            "resolution.is_resolved",
            bool_code(self.is_resolved()),
        );
        push_artifact_authority_row(
            &mut rows,
            "resolution.is_authoritative",
            bool_code(self.is_authoritative()),
        );
        push_artifact_authority_row(
            &mut rows,
            "resolution.fail_closed",
            bool_code(!self.is_authoritative()),
        );
        push_artifact_authority_row(
            &mut rows,
            "resolution.authoritative_bytes_available",
            bool_code(self.authoritative_bytes().is_some()),
        );
        rows
    }

    /// Emit stable escaped `key=value` authority evidence lines.
    pub fn authority_evidence_key_value_lines(&self) -> Vec<String> {
        self.authority_evidence_rows()
            .into_iter()
            .map(|row| row.to_key_value_line())
            .collect()
    }

    pub(crate) fn with_bytes(mut self, bytes: &'a [u8]) -> Self {
        self.bytes = Some(bytes);
        self
    }
}

/// Required-artifact lookup result that never invents missing descriptor digests.
///
/// This is the downstream-friendly entry point for shared primitive consumers:
/// it ties a requested artifact kind to the concrete artifact descriptor, byte
/// resolution report, actual byte digest, and fail-closed reason TrustIr derived.
/// If the artifact descriptor itself is absent, `artifact_digest()` and
/// `authority_evidence_rows()` return `None` instead of forcing placeholder rows.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeEvidenceArtifactAttachmentResolution<'a> {
    pub request: NativeRequestId,
    pub owner_suite: Option<NativeVerifierSuite>,
    pub required_kind: NativeEvidenceArtifactKind,
    pub artifact: Option<&'a NativeEvidenceArtifact>,
    pub resolution: Option<NativeEvidenceArtifactResolution<'a>>,
    pub status: NativeEvidenceArtifactResolutionStatus,
    pub reason: NativeEvidenceArtifactResolutionReason,
}

impl<'a> NativeEvidenceArtifactAttachmentResolution<'a> {
    pub const fn is_resolved(&self) -> bool {
        matches!(
            self.status,
            NativeEvidenceArtifactResolutionStatus::Resolved
        ) && self.resolution.is_some()
    }

    pub fn is_authoritative(&self) -> bool {
        self.resolution
            .as_ref()
            .is_some_and(NativeEvidenceArtifactResolution::is_authoritative)
    }

    pub fn fail_closed(&self) -> bool {
        !self.is_authoritative()
    }

    pub fn artifact_digest(&self) -> Option<ProofDigest> {
        self.artifact.map(|artifact| artifact.digest).or_else(|| {
            self.resolution
                .as_ref()
                .map(|resolution| resolution.report.digest)
        })
    }

    pub fn actual_digest(&self) -> Option<ProofDigest> {
        self.resolution
            .as_ref()
            .and_then(|resolution| resolution.report.actual_digest)
    }

    pub fn byte_source_identity(&self) -> Option<&str> {
        self.resolution
            .as_ref()
            .and_then(|resolution| resolution.report.byte_source_identity.as_deref())
    }

    pub fn byte_len(&self) -> Option<usize> {
        self.resolution
            .as_ref()
            .and_then(|resolution| resolution.report.byte_len)
    }

    pub fn bytes(&self) -> Option<&'a [u8]> {
        self.resolution
            .as_ref()
            .and_then(|resolution| resolution.bytes)
    }

    pub fn authoritative_bytes(&self) -> Option<&'a [u8]> {
        self.resolution
            .as_ref()
            .and_then(NativeEvidenceArtifactResolution::authoritative_bytes)
    }

    pub const fn status_code(&self) -> &'static str {
        self.status.code()
    }

    pub const fn reason_code(&self) -> &'static str {
        self.reason.code()
    }

    pub fn authority_evidence_rows(&self) -> Option<Vec<NativeEvidenceArtifactAuthorityRow>> {
        self.resolution
            .as_ref()
            .map(NativeEvidenceArtifactResolution::authority_evidence_rows)
    }

    pub fn authority_evidence_key_value_lines(&self) -> Option<Vec<String>> {
        self.resolution
            .as_ref()
            .map(NativeEvidenceArtifactResolution::authority_evidence_key_value_lines)
    }
}

/// TrustVc result evidence bound to a native request.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TrustVcNativeEvidenceBundle {
    pub request: NativeRequestId,
    pub mode: TrustVcVerificationMode,
    pub obligations: Vec<ProofId>,
    pub verifier: NativeToolIdentity,
    pub solvers: Vec<NativeToolIdentity>,
    pub replay: ProofReplayIdentity,
    pub trust_ir_module_digest: ProofDigest,
    pub request_digest: ProofDigest,
    pub artifacts: Vec<NativeEvidenceArtifact>,
}

/// TrustMc result evidence bound to a native request.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TrustMcNativeEvidenceBundle {
    pub request: NativeRequestId,
    pub mode: TrustMcVerificationMode,
    pub obligations: Vec<ProofId>,
    pub verifier: NativeToolIdentity,
    pub solvers: Vec<NativeToolIdentity>,
    pub replay: ProofReplayIdentity,
    pub trust_ir_module_digest: ProofDigest,
    pub request_digest: ProofDigest,
    pub artifacts: Vec<NativeEvidenceArtifact>,
}

/// TrustWp result evidence bound to a native request.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TrustWpNativeEvidenceBundle {
    pub request: NativeRequestId,
    pub mode: TrustWpVerificationMode,
    pub obligations: Vec<ProofId>,
    pub verifier: NativeToolIdentity,
    pub solvers: Vec<NativeToolIdentity>,
    pub replay: ProofReplayIdentity,
    pub trust_ir_module_digest: ProofDigest,
    pub request_digest: ProofDigest,
    pub artifacts: Vec<NativeEvidenceArtifact>,
}

/// One typed native verifier result bundle.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum NativeEvidenceBundle {
    TrustVc(TrustVcNativeEvidenceBundle),
    TrustMc(TrustMcNativeEvidenceBundle),
    TrustWp(TrustWpNativeEvidenceBundle),
}

impl NativeEvidenceBundle {
    pub fn request(&self) -> NativeRequestId {
        match self {
            NativeEvidenceBundle::TrustVc(bundle) => bundle.request,
            NativeEvidenceBundle::TrustMc(bundle) => bundle.request,
            NativeEvidenceBundle::TrustWp(bundle) => bundle.request,
        }
    }

    pub fn verifier_suite(&self) -> NativeVerifierSuite {
        match self {
            NativeEvidenceBundle::TrustVc(_) => NativeVerifierSuite::TrustVc,
            NativeEvidenceBundle::TrustMc(_) => NativeVerifierSuite::TrustMc,
            NativeEvidenceBundle::TrustWp(_) => NativeVerifierSuite::TrustWp,
        }
    }

    pub fn obligations(&self) -> &[ProofId] {
        match self {
            NativeEvidenceBundle::TrustVc(bundle) => &bundle.obligations,
            NativeEvidenceBundle::TrustMc(bundle) => &bundle.obligations,
            NativeEvidenceBundle::TrustWp(bundle) => &bundle.obligations,
        }
    }

    pub fn verifier(&self) -> &NativeToolIdentity {
        match self {
            NativeEvidenceBundle::TrustVc(bundle) => &bundle.verifier,
            NativeEvidenceBundle::TrustMc(bundle) => &bundle.verifier,
            NativeEvidenceBundle::TrustWp(bundle) => &bundle.verifier,
        }
    }

    pub fn solvers(&self) -> &[NativeToolIdentity] {
        match self {
            NativeEvidenceBundle::TrustVc(bundle) => &bundle.solvers,
            NativeEvidenceBundle::TrustMc(bundle) => &bundle.solvers,
            NativeEvidenceBundle::TrustWp(bundle) => &bundle.solvers,
        }
    }

    pub fn replay(&self) -> &ProofReplayIdentity {
        match self {
            NativeEvidenceBundle::TrustVc(bundle) => &bundle.replay,
            NativeEvidenceBundle::TrustMc(bundle) => &bundle.replay,
            NativeEvidenceBundle::TrustWp(bundle) => &bundle.replay,
        }
    }

    pub fn trust_ir_module_digest(&self) -> ProofDigest {
        match self {
            NativeEvidenceBundle::TrustVc(bundle) => bundle.trust_ir_module_digest,
            NativeEvidenceBundle::TrustMc(bundle) => bundle.trust_ir_module_digest,
            NativeEvidenceBundle::TrustWp(bundle) => bundle.trust_ir_module_digest,
        }
    }

    pub fn request_digest(&self) -> ProofDigest {
        match self {
            NativeEvidenceBundle::TrustVc(bundle) => bundle.request_digest,
            NativeEvidenceBundle::TrustMc(bundle) => bundle.request_digest,
            NativeEvidenceBundle::TrustWp(bundle) => bundle.request_digest,
        }
    }

    pub fn artifacts(&self) -> &[NativeEvidenceArtifact] {
        match self {
            NativeEvidenceBundle::TrustVc(bundle) => &bundle.artifacts,
            NativeEvidenceBundle::TrustMc(bundle) => &bundle.artifacts,
            NativeEvidenceBundle::TrustWp(bundle) => &bundle.artifacts,
        }
    }

    /// Build verifier result evidence from an existing typed request.
    ///
    /// This helper binds the evidence to the request's stable digest, expected
    /// verifier, solver identities, replay identity, mode, and obligations. It
    /// fails closed when the request has no replay identity instead of letting
    /// downstream consumers invent one while assembling evidence rows.
    pub fn from_request(
        trust_ir_module_digest: ProofDigest,
        request: &NativeVerificationRequest,
        artifacts: Vec<NativeEvidenceArtifact>,
    ) -> Result<Self, NativeVerificationBundleError> {
        let replay = request.provenance().replay_identity().cloned().ok_or(
            NativeVerificationBundleError::MissingReplayIdentity(request.id()),
        )?;
        let verifier = request.expected_verifier_identity().clone();
        let solvers = request.solver_identities().to_vec();
        let request_digest = request.stable_digest();

        Ok(match request {
            NativeVerificationRequest::TrustVc(request) => {
                NativeEvidenceBundle::TrustVc(TrustVcNativeEvidenceBundle {
                    request: request.id,
                    mode: request.mode,
                    obligations: request.obligations.clone(),
                    verifier,
                    solvers,
                    replay,
                    trust_ir_module_digest,
                    request_digest,
                    artifacts,
                })
            }
            NativeVerificationRequest::TrustMc(request) => {
                NativeEvidenceBundle::TrustMc(TrustMcNativeEvidenceBundle {
                    request: request.id,
                    mode: request.mode,
                    obligations: request.obligations.clone(),
                    verifier,
                    solvers,
                    replay,
                    trust_ir_module_digest,
                    request_digest,
                    artifacts,
                })
            }
            NativeVerificationRequest::TrustWp(request) => {
                NativeEvidenceBundle::TrustWp(TrustWpNativeEvidenceBundle {
                    request: request.id,
                    mode: request.mode,
                    obligations: request.obligations.clone(),
                    verifier,
                    solvers,
                    replay,
                    trust_ir_module_digest,
                    request_digest,
                    artifacts,
                })
            }
        })
    }

    pub fn stable_digest(&self) -> ProofDigest {
        let mut bytes = Vec::new();
        write_native_evidence_bundle_stable(&mut bytes, self);
        ProofDigest::sha256_domain("trust_ir.native.evidence.bundle.v2", &bytes)
    }
}

/// Validated native evidence consumption summary.
///
/// This report is intentionally non-mutating: it records which existing TrustIr
/// proof certificates a validated native evidence bundle consumed. It does not
/// manufacture new certificates from verifier artifacts.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeEvidenceConsumptionReport {
    pub entries: Vec<NativeEvidenceConsumptionEntry>,
}

impl NativeEvidenceConsumptionReport {
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn consumed_certificate_count(&self) -> usize {
        self.entries
            .iter()
            .map(|entry| entry.consumed_certificates.len())
            .sum()
    }
}

/// One validated native evidence bundle and its consumed certificate refs.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeEvidenceConsumptionEntry {
    pub request: NativeRequestId,
    pub suite: NativeVerifierSuite,
    pub evidence_digest: ProofDigest,
    pub obligations: Vec<ProofId>,
    pub consumed_certificates: Vec<ProofCertificateRef>,
    pub artifacts: Vec<NativeEvidenceArtifact>,
}

/// Stable target ABI identity exported with a native transport handoff.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeTargetAbiIdentity {
    pub triple: String,
    pub pointer_size: u32,
    pub endianness: Endianness,
    pub digest: ProofDigest,
}

impl NativeTargetAbiIdentity {
    pub fn from_target_info(target: &TargetInfo) -> Self {
        let mut identity = Self {
            triple: target.triple.clone(),
            pointer_size: target.pointer_size,
            endianness: target.endianness,
            digest: ProofDigest::sha256([0; 32]),
        };
        identity.digest = identity.stable_digest();
        identity
    }

    pub fn stable_digest(&self) -> ProofDigest {
        let mut bytes = Vec::new();
        write_str_stable(&mut bytes, &self.triple);
        write_u32_stable(&mut bytes, self.pointer_size);
        write_endianness_stable(&mut bytes, self.endianness);
        ProofDigest::sha256_domain("trust_ir.native.target_abi_identity.v2", &bytes)
    }
}

/// Stable digest identity for one verifier request.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeRequestDigestIdentity {
    pub request: NativeRequestId,
    pub suite: NativeVerifierSuite,
    pub digest: ProofDigest,
}

/// Stable digest identity for one verifier result evidence bundle.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeEvidenceDigestIdentity {
    pub request: NativeRequestId,
    pub suite: NativeVerifierSuite,
    pub digest: ProofDigest,
}

/// Self-describing contract for native-bundle identity fields consumed by downstream backends.
///
/// The descriptor intentionally names TrustIr-owned bundle, transport, function,
/// and ABI fields separately from compiled-artifact identities that must be
/// supplied by downstream backends such as TrustIr.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NativeBundleIdentityContractDescriptor {
    pub schema: &'static str,
    pub schema_version: u32,
    pub bundle_schema_version: u32,
    pub transport_identity_schema: &'static str,
    pub transport_identity_schema_version: u32,
    pub provided_fields: &'static [&'static str],
    pub digest_contexts: &'static [&'static str],
    pub external_fields: &'static [&'static str],
}

/// Native-bundle identity contract consumed by downstream backends.
pub static NATIVE_BUNDLE_IDENTITY_CONTRACT_DESCRIPTOR: NativeBundleIdentityContractDescriptor =
    NativeBundleIdentityContractDescriptor {
        schema: NATIVE_BUNDLE_IDENTITY_CONTRACT_SCHEMA,
        schema_version: NATIVE_BUNDLE_IDENTITY_CONTRACT_SCHEMA_VERSION,
        bundle_schema_version: NATIVE_VERIFICATION_BUNDLE_SCHEMA_VERSION,
        transport_identity_schema: NATIVE_TRANSPORT_IDENTITY_SCHEMA,
        transport_identity_schema_version: NATIVE_TRANSPORT_IDENTITY_SCHEMA_VERSION,
        provided_fields: NATIVE_BUNDLE_IDENTITY_CONTRACT_PROVIDED_FIELDS,
        digest_contexts: NATIVE_BUNDLE_IDENTITY_CONTRACT_DIGEST_CONTEXTS,
        external_fields: NATIVE_BUNDLE_IDENTITY_CONTRACT_EXTERNAL_FIELDS,
    };

/// Return the native-bundle identity contract consumed by downstream backends.
pub fn native_bundle_identity_contract_descriptor() -> NativeBundleIdentityContractDescriptor {
    NATIVE_BUNDLE_IDENTITY_CONTRACT_DESCRIPTOR
}

/// Typed verifier mode used by a native shared-primitive contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeSharedPrimitiveVerificationMode {
    TrustVc(TrustVcVerificationMode),
    TrustMc(TrustMcVerificationMode),
    TrustWp(TrustWpVerificationMode),
}

impl NativeSharedPrimitiveVerificationMode {
    pub const fn verifier_suite(self) -> NativeVerifierSuite {
        match self {
            NativeSharedPrimitiveVerificationMode::TrustVc(_) => NativeVerifierSuite::TrustVc,
            NativeSharedPrimitiveVerificationMode::TrustMc(_) => NativeVerifierSuite::TrustMc,
            NativeSharedPrimitiveVerificationMode::TrustWp(_) => NativeVerifierSuite::TrustWp,
        }
    }

    pub const fn code(self) -> &'static str {
        match self {
            NativeSharedPrimitiveVerificationMode::TrustVc(
                TrustVcVerificationMode::ImportProofCertificates,
            ) => "trust_vc.import_proof_certificates",
            NativeSharedPrimitiveVerificationMode::TrustVc(
                TrustVcVerificationMode::MergeProofCertificates,
            ) => "trust_vc.merge_proof_certificates",
            NativeSharedPrimitiveVerificationMode::TrustVc(
                TrustVcVerificationMode::DischargeProofObligations,
            ) => "trust_vc.discharge_proof_obligations",
            NativeSharedPrimitiveVerificationMode::TrustMc(
                TrustMcVerificationMode::BoundedModelCheck,
            ) => "trust_mc.bounded_model_check",
            NativeSharedPrimitiveVerificationMode::TrustMc(TrustMcVerificationMode::Chc) => {
                "trust_mc.chc"
            }
            NativeSharedPrimitiveVerificationMode::TrustMc(TrustMcVerificationMode::Pdr) => {
                "trust_mc.pdr"
            }
            NativeSharedPrimitiveVerificationMode::TrustWp(
                TrustWpVerificationMode::WeakestPrecondition,
            ) => "trust_wp.weakest_precondition",
            NativeSharedPrimitiveVerificationMode::TrustWp(
                TrustWpVerificationMode::StrongestPostcondition,
            ) => "trust_wp.strongest_postcondition",
            NativeSharedPrimitiveVerificationMode::TrustWp(TrustWpVerificationMode::Abduction) => {
                "trust_wp.abduction"
            }
        }
    }
}

/// Stable key/value row for JSON-free shared-primitive contract manifests.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeSharedPrimitiveContractManifestRow {
    pub key: String,
    pub value: String,
}

impl NativeSharedPrimitiveContractManifestRow {
    pub fn new(key: impl Into<String>, value: impl Into<String>) -> Self {
        Self {
            key: key.into(),
            value: value.into(),
        }
    }

    /// Escaped key for line-oriented `key=value` manifest output.
    pub fn escaped_key(&self) -> String {
        escape_manifest_component(&self.key)
    }

    /// Escaped value for line-oriented `key=value` manifest output.
    pub fn escaped_value(&self) -> String {
        escape_manifest_component(&self.value)
    }

    /// Stable one-line `key=value` representation.
    ///
    /// Backslash, equals, and control characters are escaped so schema
    /// generators can preserve rows without inventing local escaping.
    pub fn to_key_value_line(&self) -> String {
        format!("{}={}", self.escaped_key(), self.escaped_value())
    }
}

pub(crate) fn push_hardware_vector_operation_status_rows(
    rows: &mut Vec<NativeSharedPrimitiveContractManifestRow>,
    operation_prefix: &str,
    status: HardwareVectorContractStatus,
    reason: HardwareVectorContractReason,
) {
    push_manifest_row(rows, format!("{operation_prefix}.status"), status.code());
    push_manifest_row(rows, format!("{operation_prefix}.reason"), reason.code());
    push_manifest_row(
        rows,
        format!("{operation_prefix}.fail_closed"),
        bool_code(status.fail_closed()),
    );
    if status.fail_closed() {
        push_manifest_row(
            rows,
            format!("{operation_prefix}.consumer_policy"),
            CHC_X86_UNSIGNED_VECTOR_COMPARE_FAIL_CLOSED_POLICY,
        );
    }
}

/// Stable per-operation hardware vector status row without lowering evidence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HardwareVectorOperationStatusRow {
    pub operation: &'static str,
    pub status: HardwareVectorContractStatus,
    pub reason: HardwareVectorContractReason,
}

impl HardwareVectorOperationStatusRow {
    pub const fn fail_closed(self) -> bool {
        self.status.fail_closed()
    }

    fn push_manifest_rows_with_prefix(
        self,
        rows: &mut Vec<NativeSharedPrimitiveContractManifestRow>,
        prefix: &str,
    ) {
        let operation_prefix = format!("{prefix}.operation.{}", self.operation);
        push_hardware_vector_operation_status_rows(
            rows,
            &operation_prefix,
            self.status,
            self.reason,
        );
    }
}

/// Stable per-operation hardware vector lowering row.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HardwareVectorOperationContractRow {
    pub operation: &'static str,
    pub trust_cg_lir_opcode: &'static str,
    pub feature_guard: &'static str,
    pub native_instructions: &'static str,
    pub semantics: &'static str,
    pub composition: &'static str,
}

impl HardwareVectorOperationContractRow {
    fn push_manifest_rows_with_prefix(
        self,
        rows: &mut Vec<NativeSharedPrimitiveContractManifestRow>,
        prefix: &str,
    ) {
        let operation_prefix = format!("{prefix}.operation.{}", self.operation);
        push_hardware_vector_operation_status_rows(
            rows,
            &operation_prefix,
            HardwareVectorContractStatus::Available,
            HardwareVectorContractReason::CanonicalContract,
        );
        if !self.trust_cg_lir_opcode.is_empty() {
            push_manifest_row(
                rows,
                format!("{operation_prefix}.trust_cg_lir_opcode"),
                self.trust_cg_lir_opcode,
            );
        }
        push_manifest_row(
            rows,
            format!("{operation_prefix}.feature_guard"),
            self.feature_guard,
        );
        push_manifest_row(
            rows,
            format!("{operation_prefix}.native_instructions"),
            self.native_instructions,
        );
        push_manifest_row(
            rows,
            format!("{operation_prefix}.semantics"),
            self.semantics,
        );
        if !self.composition.is_empty() {
            push_manifest_row(
                rows,
                format!("{operation_prefix}.composition"),
                self.composition,
            );
        }
    }
}

/// Stable readiness status for a TrustIr-owned hardware vector contract descriptor.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HardwareVectorContractStatus {
    Available,
    Deferred,
    Unavailable,
}

impl HardwareVectorContractStatus {
    /// Stable lower-snake-case status for downstream sidecar rows.
    pub const fn code(self) -> &'static str {
        match self {
            HardwareVectorContractStatus::Available => "available",
            HardwareVectorContractStatus::Deferred => "deferred",
            HardwareVectorContractStatus::Unavailable => "unavailable",
        }
    }

    /// Whether consumers must reject rows with this status.
    pub const fn fail_closed(self) -> bool {
        !matches!(self, HardwareVectorContractStatus::Available)
    }
}

/// Stable reason code for a TrustIr-owned hardware vector contract descriptor.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HardwareVectorContractReason {
    CanonicalContract,
    UnsignedVectorCompareProofBlocked,
    UnsignedVectorCompareUnavailable,
}

impl HardwareVectorContractReason {
    /// Stable lower-snake-case reason for downstream sidecar rows.
    pub const fn code(self) -> &'static str {
        match self {
            HardwareVectorContractReason::CanonicalContract => "canonical_contract",
            HardwareVectorContractReason::UnsignedVectorCompareProofBlocked => {
                "unsigned_vector_compare_proof_blocked"
            }
            HardwareVectorContractReason::UnsignedVectorCompareUnavailable => {
                "unsigned_vector_compare_unavailable"
            }
        }
    }
}

/// Producer-owned descriptor for hardware/vector contract evidence rows.
///
/// CHC/HWMCC consumers can emit these compact rows directly instead of
/// reconstructing vector type names, mask semantics, or readiness strings from
/// TrustIr IR fixtures. The descriptor is informational; production proof/replay
/// acceptance still belongs to the relevant solver or hardware lane.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HardwareVectorContractDescriptor {
    pub schema: &'static str,
    pub schema_version: u32,
    pub source_package: &'static str,
    pub target_family: &'static str,
    pub hardware_model: &'static str,
    pub contract_name: &'static str,
    pub value_ty: &'static str,
    pub logical_mask_ty: &'static str,
    pub physical_mask_ty: &'static str,
    pub element_ty: &'static str,
    pub element_bits: u32,
    pub lane_count: u32,
    pub total_bits: u32,
    pub mask_semantics: &'static str,
    pub operations: &'static [&'static str],
    pub mul_feature_guard: &'static str,
    pub mul_native_instruction: &'static str,
    pub mul_semantics: &'static str,
    pub lane_pack_lir_opcode: &'static str,
    pub lane_pack_feature_guard: &'static str,
    pub lane_pack_native_instructions: &'static str,
    pub lane_pack_semantics: &'static str,
    pub status: HardwareVectorContractStatus,
    pub reason: HardwareVectorContractReason,
}

impl HardwareVectorContractDescriptor {
    /// Stable status code for downstream sidecar rows.
    pub const fn status_code(self) -> &'static str {
        self.status.code()
    }

    /// Stable reason code for downstream sidecar rows.
    pub const fn reason_code(self) -> &'static str {
        self.reason.code()
    }

    /// Whether consumers must fail closed for this descriptor alone.
    pub const fn fail_closed(self) -> bool {
        self.status.fail_closed()
    }

    fn operation_contracts(self) -> &'static [HardwareVectorOperationContractRow] {
        match self.contract_name {
            "chc_x86.v4_i32" => CHC_X86_V4_I32_OPERATION_CONTRACT_ROWS,
            "chc_x86.v2_i64" => CHC_X86_V2_I64_OPERATION_CONTRACT_ROWS,
            "chc_x86.v16_i8" => CHC_X86_V16_I8_OPERATION_CONTRACT_ROWS,
            "chc_x86.v8_i16" => CHC_X86_V8_I16_OPERATION_CONTRACT_ROWS,
            _ => &[],
        }
    }

    fn operation_status_rows(self) -> &'static [HardwareVectorOperationStatusRow] {
        match self.contract_name {
            "chc_x86.v4_i32" => CHC_X86_V4_I32_OPERATION_STATUS_ROWS,
            "chc_x86.v2_i64" => CHC_X86_V2_I64_OPERATION_STATUS_ROWS,
            "chc_x86.v16_i8" => CHC_X86_V16_I8_OPERATION_STATUS_ROWS,
            "chc_x86.v8_i16" => CHC_X86_V8_I16_OPERATION_STATUS_ROWS,
            _ => &[],
        }
    }

    pub(crate) fn emits_legacy_operation_rows(self, operation: &str) -> bool {
        match operation {
            "binop.mul" => !self.mul_feature_guard.is_empty(),
            "pack_lanes" => !self.lane_pack_lir_opcode.is_empty(),
            _ => false,
        }
    }

    fn push_manifest_rows_with_prefix(
        self,
        rows: &mut Vec<NativeSharedPrimitiveContractManifestRow>,
        prefix: &str,
    ) {
        push_manifest_row(rows, format!("{prefix}.schema"), self.schema);
        push_manifest_row(
            rows,
            format!("{prefix}.schema_version"),
            self.schema_version.to_string(),
        );
        push_manifest_row(
            rows,
            format!("{prefix}.source.package"),
            self.source_package,
        );
        push_manifest_row(rows, format!("{prefix}.target.family"), self.target_family);
        push_manifest_row(
            rows,
            format!("{prefix}.hardware_model"),
            self.hardware_model,
        );
        push_manifest_row(rows, format!("{prefix}.contract.name"), self.contract_name);
        push_manifest_row(rows, format!("{prefix}.status"), self.status_code());
        push_manifest_row(rows, format!("{prefix}.reason"), self.reason_code());
        push_manifest_row(
            rows,
            format!("{prefix}.fail_closed"),
            bool_code(self.fail_closed()),
        );
        push_manifest_row(rows, format!("{prefix}.value_ty"), self.value_ty);
        push_manifest_row(
            rows,
            format!("{prefix}.logical_mask_ty"),
            self.logical_mask_ty,
        );
        push_manifest_row(
            rows,
            format!("{prefix}.physical_mask_ty"),
            self.physical_mask_ty,
        );
        push_manifest_row(rows, format!("{prefix}.element_ty"), self.element_ty);
        push_manifest_row(
            rows,
            format!("{prefix}.element_bits"),
            self.element_bits.to_string(),
        );
        push_manifest_row(
            rows,
            format!("{prefix}.lane_count"),
            self.lane_count.to_string(),
        );
        push_manifest_row(
            rows,
            format!("{prefix}.total_bits"),
            self.total_bits.to_string(),
        );
        push_manifest_row(
            rows,
            format!("{prefix}.mask_semantics"),
            self.mask_semantics,
        );
        push_manifest_row(
            rows,
            format!("{prefix}.operation_count"),
            self.operations.len().to_string(),
        );
        for (index, operation) in self.operations.iter().enumerate() {
            push_manifest_row(rows, format!("{prefix}.operation.{index}"), *operation);
        }
        if !self.mul_feature_guard.is_empty() {
            let operation_prefix = format!("{prefix}.operation.binop.mul");
            push_hardware_vector_operation_status_rows(
                rows,
                &operation_prefix,
                HardwareVectorContractStatus::Available,
                HardwareVectorContractReason::CanonicalContract,
            );
            push_manifest_row(
                rows,
                format!("{operation_prefix}.feature_guard"),
                self.mul_feature_guard,
            );
            push_manifest_row(
                rows,
                format!("{operation_prefix}.native_instruction"),
                self.mul_native_instruction,
            );
            push_manifest_row(
                rows,
                format!("{operation_prefix}.semantics"),
                self.mul_semantics,
            );
        }
        if !self.lane_pack_lir_opcode.is_empty() {
            let operation_prefix = format!("{prefix}.operation.pack_lanes");
            push_hardware_vector_operation_status_rows(
                rows,
                &operation_prefix,
                HardwareVectorContractStatus::Available,
                HardwareVectorContractReason::CanonicalContract,
            );
            push_manifest_row(
                rows,
                format!("{operation_prefix}.trust_cg_lir_opcode"),
                self.lane_pack_lir_opcode,
            );
            push_manifest_row(
                rows,
                format!("{operation_prefix}.feature_guard"),
                self.lane_pack_feature_guard,
            );
            push_manifest_row(
                rows,
                format!("{operation_prefix}.native_instructions"),
                self.lane_pack_native_instructions,
            );
            push_manifest_row(
                rows,
                format!("{operation_prefix}.semantics"),
                self.lane_pack_semantics,
            );
            push_manifest_row(
                rows,
                format!("{prefix}.trust_cg_x86_vector.generic_feature_guard"),
                CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
            );
            push_manifest_row(
                rows,
                format!("{prefix}.trust_cg_x86_vector.current_feature_guard"),
                CHC_X86_TRUST_CG_CURRENT_VECTOR_FEATURE_GUARD,
            );
            push_manifest_row(
                rows,
                format!("{prefix}.trust_cg_x86_vector.host_jit_feature_guard"),
                CHC_X86_TRUST_CG_HOST_JIT_VECTOR_FEATURE_GUARD,
            );
        }
        for contract in self.operation_contracts() {
            if self.emits_legacy_operation_rows(contract.operation) {
                continue;
            }
            contract.push_manifest_rows_with_prefix(rows, prefix);
        }
        for status_row in self.operation_status_rows() {
            status_row.push_manifest_rows_with_prefix(rows, prefix);
        }
    }

    /// Emit stable JSON-free rows for this hardware/vector contract descriptor.
    pub fn manifest_rows(self) -> Vec<NativeSharedPrimitiveContractManifestRow> {
        let mut rows = Vec::new();
        push_manifest_row(
            &mut rows,
            "hardware_vector_contract.manifest.schema",
            HARDWARE_VECTOR_CONTRACT_MANIFEST_SCHEMA,
        );
        push_manifest_row(
            &mut rows,
            "hardware_vector_contract.manifest.schema_version",
            HARDWARE_VECTOR_CONTRACT_MANIFEST_SCHEMA_VERSION.to_string(),
        );
        self.push_manifest_rows_with_prefix(&mut rows, "hardware_vector_contract");
        rows
    }

    /// Emit stable escaped `key=value` lines for this descriptor.
    pub fn manifest_key_value_lines(self) -> Vec<String> {
        self.manifest_rows()
            .into_iter()
            .map(|row| row.to_key_value_line())
            .collect()
    }

    /// Number of stable rows emitted by [`Self::manifest_rows`].
    pub fn manifest_row_count(self) -> usize {
        self.manifest_rows().len()
    }

    /// Stable typed digest over [`Self::manifest_key_value_text`].
    pub fn manifest_digest(self) -> ProofDigest {
        manifest_key_value_lines_digest(&self.manifest_key_value_lines())
    }

    /// Stable `sha256:<hex>` digest string over [`Self::manifest_key_value_text`].
    pub fn manifest_sha256(self) -> String {
        self.manifest_digest().to_string()
    }

    /// Emit stable line-oriented manifest text for this descriptor.
    pub fn manifest_key_value_text(self) -> String {
        format!("{}\n", self.manifest_key_value_lines().join("\n"))
    }
}

/// Producer-owned readiness status for the aggregate TY manifest.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TySharedPrimitiveManifestStatus {
    Available,
}

impl TySharedPrimitiveManifestStatus {
    /// Stable lower-snake-case status for downstream sidecar rows.
    pub const fn code(self) -> &'static str {
        match self {
            TySharedPrimitiveManifestStatus::Available => "available",
        }
    }
}

/// Producer-owned reason for the aggregate TY manifest status.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TySharedPrimitiveManifestReason {
    ProducerOwnedRowsAvailable,
}

impl TySharedPrimitiveManifestReason {
    /// Stable lower-snake-case reason for downstream sidecar rows.
    pub const fn code(self) -> &'static str {
        match self {
            TySharedPrimitiveManifestReason::ProducerOwnedRowsAvailable => {
                "producer_owned_rows_available"
            }
        }
    }
}

/// Aggregate producer manifest for TY shared-primitive sidecars.
///
/// This is the stable discovery surface for downstream sidecars that need the
/// native semantic bridge proof identity, Petri/TrustMc proof-evidence identity,
/// and CHC x86 hardware vector contract row families without locally
/// synthesizing readiness strings or copying row helper names.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TySharedPrimitiveManifest {
    pub schema: &'static str,
    pub schema_version: u32,
    pub source_package: &'static str,
    pub source_package_version: &'static str,
    pub status: TySharedPrimitiveManifestStatus,
    pub reason: TySharedPrimitiveManifestReason,
}

impl TySharedPrimitiveManifest {
    /// Stable status code for downstream sidecar rows.
    pub const fn status_code(self) -> &'static str {
        self.status.code()
    }

    /// Stable reason code for downstream sidecar rows.
    pub const fn reason_code(self) -> &'static str {
        self.reason.code()
    }

    /// Whether downstream consumers must fail closed for this producer manifest.
    pub const fn fail_closed(self) -> bool {
        !matches!(self.status, TySharedPrimitiveManifestStatus::Available)
    }

    /// Emit stable JSON-free rows for the aggregate TY producer manifest.
    pub fn manifest_rows(self) -> Vec<NativeSharedPrimitiveContractManifestRow> {
        let mut rows = Vec::new();
        push_manifest_row(
            &mut rows,
            "ty_shared_primitive_manifest.schema",
            self.schema,
        );
        push_manifest_row(
            &mut rows,
            "ty_shared_primitive_manifest.schema_version",
            self.schema_version.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "ty_shared_primitive_manifest.source.package",
            self.source_package,
        );
        push_manifest_row(
            &mut rows,
            "ty_shared_primitive_manifest.source.package_version",
            self.source_package_version,
        );
        push_manifest_row(
            &mut rows,
            "ty_shared_primitive_manifest.status",
            self.status_code(),
        );
        push_manifest_row(
            &mut rows,
            "ty_shared_primitive_manifest.reason",
            self.reason_code(),
        );
        push_manifest_row(
            &mut rows,
            "ty_shared_primitive_manifest.fail_closed",
            bool_code(self.fail_closed()),
        );
        push_manifest_row(
            &mut rows,
            "ty_shared_primitive_manifest.component_count",
            TY_SHARED_PRIMITIVE_MANIFEST_COMPONENT_NAMES
                .len()
                .to_string(),
        );

        push_ty_shared_primitive_component_rows(
            &mut rows,
            0,
            TY_SHARED_PRIMITIVE_MANIFEST_COMPONENT_NAMES[0],
            "runtime_report",
            "proof_identity_replay",
            NATIVE_SEMANTIC_BRIDGE_PROOF_IDENTITY_SCHEMA,
            NATIVE_SEMANTIC_BRIDGE_PROOF_IDENTITY_SCHEMA_VERSION,
            "NativeSemanticBridgeReport::proof_identity_rows()",
            "NativeSemanticBridgeReport::proof_identity_key_value_lines()",
            "NativeSemanticBridgeReport::proof_identity_key_value_text()",
            "NativeSemanticBridgeReport::proof_identity_replay_report()",
            "NativeSemanticBridgeProofIdentityReplayReport::compact_health_summary_rows()",
            "NativeSemanticBridgeProofIdentityReplayReport::compact_health_summary_key_value_lines()",
            "NativeSemanticBridgeProofIdentityReplayReport::component_health_summary_rows()",
            "NativeSemanticBridgeProofIdentityReplayReport::component_health_summary_key_value_lines()",
            None,
        );
        push_ty_shared_primitive_component_rows(
            &mut rows,
            1,
            TY_SHARED_PRIMITIVE_MANIFEST_COMPONENT_NAMES[1],
            "runtime_report",
            "proof_evidence_identity_replay",
            PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_SCHEMA,
            PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_SCHEMA_VERSION,
            "PetriSuccessorTrustMcChcProofHandoffReport::proof_evidence_identity_rows()",
            "PetriSuccessorTrustMcChcProofHandoffReport::proof_evidence_identity_key_value_lines()",
            "PetriSuccessorTrustMcChcProofHandoffReport::proof_evidence_identity_key_value_text()",
            "PetriSuccessorTrustMcChcProofHandoffReport::proof_evidence_identity_replay_report()",
            "PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport::compact_health_summary_rows()",
            "PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport::compact_health_summary_key_value_lines()",
            "PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport::component_health_summary_rows()",
            "PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport::component_health_summary_key_value_lines()",
            None,
        );
        push_ty_shared_primitive_component_rows(
            &mut rows,
            2,
            TY_SHARED_PRIMITIVE_MANIFEST_COMPONENT_NAMES[2],
            "static_descriptor",
            "hardware_vector_contract",
            HARDWARE_VECTOR_CONTRACT_SCHEMA,
            HARDWARE_VECTOR_CONTRACT_SCHEMA_VERSION,
            "chc_x86_hardware_vector_contract_manifest_rows()",
            "chc_x86_hardware_vector_contract_manifest_key_value_lines()",
            "chc_x86_hardware_vector_contract_manifest_key_value_text()",
            "none",
            "none",
            "none",
            "none",
            "none",
            Some(chc_x86_hardware_vector_contract_descriptors().len()),
        );

        let hardware_rows = chc_x86_hardware_vector_contract_manifest_rows();
        push_manifest_row(
            &mut rows,
            "ty_shared_primitive_manifest.hardware_vector_contract_row_count",
            hardware_rows.len().to_string(),
        );
        for (index, row) in hardware_rows.iter().enumerate() {
            push_manifest_row(
                &mut rows,
                format!("ty_shared_primitive_manifest.hardware_vector_contract_row.{index}.key"),
                row.key.as_str(),
            );
            push_manifest_row(
                &mut rows,
                format!("ty_shared_primitive_manifest.hardware_vector_contract_row.{index}.value"),
                row.value.as_str(),
            );
        }

        rows
    }

    /// Emit stable escaped `key=value` rows for the aggregate manifest.
    pub fn manifest_key_value_lines(self) -> Vec<String> {
        self.manifest_rows()
            .into_iter()
            .map(|row| row.to_key_value_line())
            .collect()
    }

    /// Number of stable rows emitted by [`Self::manifest_rows`].
    pub fn manifest_row_count(self) -> usize {
        self.manifest_rows().len()
    }

    /// Stable typed digest over [`Self::manifest_key_value_text`].
    pub fn manifest_digest(self) -> ProofDigest {
        manifest_key_value_lines_digest(&self.manifest_key_value_lines())
    }

    /// Stable `sha256:<hex>` digest string over [`Self::manifest_key_value_text`].
    pub fn manifest_sha256(self) -> String {
        self.manifest_digest().to_string()
    }

    /// Emit stable line-oriented text for the aggregate manifest.
    pub fn manifest_key_value_text(self) -> String {
        format!("{}\n", self.manifest_key_value_lines().join("\n"))
    }
}

/// Generic role an emitted artifact plays at a shared-primitive acceptance boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeSharedPrimitiveArtifactRole {
    /// Solver input bytes, such as clauses, verification conditions, or queries.
    SolverInput,
    /// Replay/proof transcript bytes used to validate the solver run.
    ReplayTranscript,
    /// Solver-produced witness/model/counterexample bytes.
    SolverWitness,
    /// Imported or merged proof certificate bytes.
    ProofCertificate,
    /// Domain-specific bytes whose role is named by the enclosing contract.
    Other,
}

impl NativeSharedPrimitiveArtifactRole {
    pub const fn code(self) -> &'static str {
        match self {
            NativeSharedPrimitiveArtifactRole::SolverInput => "solver_input",
            NativeSharedPrimitiveArtifactRole::ReplayTranscript => "replay_transcript",
            NativeSharedPrimitiveArtifactRole::SolverWitness => "solver_witness",
            NativeSharedPrimitiveArtifactRole::ProofCertificate => "proof_certificate",
            NativeSharedPrimitiveArtifactRole::Other => "other",
        }
    }
}

/// Artifact-byte validation requirement for a solver-owned shared primitive.
///
/// This is generic metadata for downstream promotion gates. It names the role,
/// TrustIr artifact kind, digest algorithm, and owner suite that must validate the
/// bytes without interpreting the solver result in TrustIr.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NativeSharedPrimitiveArtifactRequirement {
    pub role: NativeSharedPrimitiveArtifactRole,
    pub kind: NativeEvidenceArtifactKind,
    pub digest_algorithm: ProofDigestAlgorithm,
    pub owner_suite: NativeVerifierSuite,
    pub requires_emitted_solver_artifact: bool,
}

impl NativeSharedPrimitiveArtifactRequirement {
    /// Stable role code for JSON/evidence rows.
    pub const fn role_code(self) -> &'static str {
        self.role.code()
    }

    /// Whether an emitted artifact has the kind and digest form this gate requires.
    ///
    /// This deliberately checks artifact identity metadata only. The owner suite
    /// still validates the artifact bytes and decides production acceptance.
    pub fn accepts_artifact_identity(self, artifact: &NativeEvidenceArtifact) -> bool {
        artifact.kind == self.kind
            && artifact.digest.algorithm == self.digest_algorithm
            && (!self.requires_emitted_solver_artifact || !artifact.digest.is_zero())
    }
}

/// Solver-owned evidence identities required by a shared primitive.
///
/// The strings in this descriptor name public solver APIs and schemas. TrustIr
/// uses them as typed references at promotion boundaries; it does not interpret
/// the solver's capability rows, model-blocking evidence, or acceptance result.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NativeSharedPrimitiveSolverEvidenceDescriptor {
    pub owner_suite: NativeVerifierSuite,
    pub solver_capability_descriptor_schema: &'static str,
    pub solver_capability_descriptor_schema_version: u32,
    pub model_blocking_clause_schema: &'static str,
    pub model_blocking_clause_schema_version: u32,
    pub model_blocking_clause_evidence_schema: &'static str,
    pub model_blocking_clause_evidence_schema_version: u32,
    pub solve_decision_profile_model_consumer_schema: &'static str,
    pub solve_decision_profile_model_consumer_schema_version: u32,
    pub acceptance_report_api_name: &'static str,
    pub consumer_acceptance_api_name: &'static str,
}

impl NativeSharedPrimitiveSolverEvidenceDescriptor {
    /// Schema for the solver-owned capability descriptor.
    pub const fn capability_descriptor_schema(self) -> &'static str {
        self.solver_capability_descriptor_schema
    }

    /// Schema for the solver-owned model-blocking clause.
    pub const fn model_blocking_clause_schema(self) -> &'static str {
        self.model_blocking_clause_schema
    }

    /// Schema for compact solver-owned model-blocking evidence.
    pub const fn model_blocking_clause_evidence_schema(self) -> &'static str {
        self.model_blocking_clause_evidence_schema
    }

    /// Schema for the solver-owned solve-decision model-consumer boundary.
    pub const fn solve_decision_profile_model_consumer_schema(self) -> &'static str {
        self.solve_decision_profile_model_consumer_schema
    }

    /// Public solver APIs that own production acceptance.
    pub const fn acceptance_api_names(self) -> (&'static str, &'static str) {
        (
            self.acceptance_report_api_name,
            self.consumer_acceptance_api_name,
        )
    }
}

/// Reusable contract descriptor for native shared primitives with solver-owned acceptance.
///
/// This is intentionally policy-light: it names TrustIr-owned handoff schemas,
/// typed verifier mode, artifact prerequisites, and the downstream acceptance
/// owner/API without interpreting the solver result. Downstream consumers use
/// this descriptor to derive fail-closed promotion gates; it is not itself an
/// acceptance decision.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NativeSharedPrimitiveContractDescriptor {
    pub schema: &'static str,
    pub schema_version: u32,
    pub contract_schema: &'static str,
    pub contract_schema_version: u32,
    pub formula_schema: &'static str,
    pub readiness_report_schema: &'static str,
    pub readiness_report_schema_version: u32,
    pub verifier_suite: NativeVerifierSuite,
    pub verification_mode: NativeSharedPrimitiveVerificationMode,
    pub required_artifact_kinds: &'static [NativeEvidenceArtifactKind],
    pub optional_artifact_kinds: &'static [NativeEvidenceArtifactKind],
    /// Solver-owned artifact-byte validation requirements for production promotion.
    ///
    /// Prefer this typed requirement list over reconstructing roles, digest
    /// algorithms, owner suites, or emitted-artifact policy from artifact kinds.
    pub required_artifact_requirements: &'static [NativeSharedPrimitiveArtifactRequirement],
    /// Whether production promotion requires bytes emitted by the solver lane.
    pub production_requires_emitted_solver_artifacts: bool,
    pub requires_solver_acceptance: bool,
    pub model_acceptance_report_api_name: &'static str,
    pub consumer_acceptance_api_name: &'static str,
    pub production_acceptance_owner_suite: NativeVerifierSuite,
    pub solver_evidence_descriptor: NativeSharedPrimitiveSolverEvidenceDescriptor,
}

impl NativeSharedPrimitiveContractDescriptor {
    /// Required artifact-byte validation rules for production promotion.
    pub const fn production_required_artifact_requirements(
        self,
    ) -> &'static [NativeSharedPrimitiveArtifactRequirement] {
        self.required_artifact_requirements
    }

    /// Whether production promotion requires solver-emitted artifact bytes.
    pub const fn production_requires_emitted_solver_artifacts(self) -> bool {
        self.production_requires_emitted_solver_artifacts
    }

    /// Iterate over distinct generic artifact roles required for production promotion.
    pub fn production_required_artifact_roles(
        self,
    ) -> impl Iterator<Item = NativeSharedPrimitiveArtifactRole> {
        let requirements = self.required_artifact_requirements;
        requirements
            .iter()
            .enumerate()
            .filter_map(move |(index, requirement)| {
                if requirements[..index]
                    .iter()
                    .any(|previous| previous.role == requirement.role)
                {
                    None
                } else {
                    Some(requirement.role)
                }
            })
    }

    /// Iterate over distinct verifier suites that own production artifact validation.
    pub fn production_artifact_owner_suites(self) -> impl Iterator<Item = NativeVerifierSuite> {
        let requirements = self.required_artifact_requirements;
        requirements
            .iter()
            .enumerate()
            .filter_map(move |(index, requirement)| {
                if requirements[..index]
                    .iter()
                    .any(|previous| previous.owner_suite == requirement.owner_suite)
                {
                    None
                } else {
                    Some(requirement.owner_suite)
                }
            })
    }

    /// Return the production artifact requirement for a generic artifact role.
    pub fn production_required_artifact_requirement_for_role(
        self,
        role: NativeSharedPrimitiveArtifactRole,
    ) -> Option<&'static NativeSharedPrimitiveArtifactRequirement> {
        self.required_artifact_requirements
            .iter()
            .find(|requirement| requirement.role == role)
    }

    /// Return the production artifact requirement for a TrustIr artifact kind.
    pub fn production_required_artifact_requirement_for_kind(
        self,
        kind: NativeEvidenceArtifactKind,
    ) -> Option<&'static NativeSharedPrimitiveArtifactRequirement> {
        self.required_artifact_requirements
            .iter()
            .find(|requirement| requirement.kind == kind)
    }

    /// Iterate over production artifact requirements owned by a verifier suite.
    pub fn production_artifact_requirements_for_owner_suite(
        self,
        owner_suite: NativeVerifierSuite,
    ) -> impl Iterator<Item = &'static NativeSharedPrimitiveArtifactRequirement> {
        self.required_artifact_requirements
            .iter()
            .filter(move |requirement| requirement.owner_suite == owner_suite)
    }

    /// Digest algorithm required for a production artifact kind, if required.
    pub fn production_artifact_digest_algorithm(
        self,
        kind: NativeEvidenceArtifactKind,
    ) -> Option<ProofDigestAlgorithm> {
        self.production_required_artifact_requirement_for_kind(kind)
            .map(|requirement| requirement.digest_algorithm)
    }

    /// Owner suite responsible for validating a production artifact kind.
    pub fn production_artifact_owner_suite(
        self,
        kind: NativeEvidenceArtifactKind,
    ) -> Option<NativeVerifierSuite> {
        self.production_required_artifact_requirement_for_kind(kind)
            .map(|requirement| requirement.owner_suite)
    }

    /// Emit stable JSON-free key/value rows for schema and MCC sidecar consumers.
    ///
    /// Rows deliberately duplicate the descriptor's typed fields as flat strings
    /// so non-Rust consumers can validate vocabularies without hardcoding TrustIr
    /// constants. Row order is part of the manifest schema version; repeated
    /// keys are ordered repeated fields, and artifact requirement rows are
    /// indexed in descriptor order.
    pub fn manifest_rows(self) -> Vec<NativeSharedPrimitiveContractManifestRow> {
        let mut rows = Vec::new();
        push_manifest_row(
            &mut rows,
            "manifest.schema",
            NATIVE_SHARED_PRIMITIVE_CONTRACT_MANIFEST_SCHEMA,
        );
        push_manifest_row(
            &mut rows,
            "manifest.schema_version",
            NATIVE_SHARED_PRIMITIVE_CONTRACT_MANIFEST_SCHEMA_VERSION.to_string(),
        );
        push_manifest_row(&mut rows, "contract.schema", self.contract_schema);
        push_manifest_row(
            &mut rows,
            "contract.schema_version",
            self.contract_schema_version.to_string(),
        );
        push_manifest_row(&mut rows, "shared_primitive.schema", self.schema);
        push_manifest_row(
            &mut rows,
            "shared_primitive.schema_version",
            self.schema_version.to_string(),
        );
        push_manifest_row(&mut rows, "formula.schema", self.formula_schema);
        push_manifest_row(
            &mut rows,
            "readiness_report.schema",
            self.readiness_report_schema,
        );
        push_manifest_row(
            &mut rows,
            "readiness_report.schema_version",
            self.readiness_report_schema_version.to_string(),
        );
        push_manifest_row(&mut rows, "verifier_suite", self.verifier_suite.code());
        push_manifest_row(
            &mut rows,
            "verification_mode",
            self.verification_mode.code(),
        );
        push_manifest_row(
            &mut rows,
            "production.requires_solver_acceptance",
            bool_code(self.requires_solver_acceptance),
        );
        push_manifest_row(
            &mut rows,
            "production.requires_emitted_solver_artifacts",
            bool_code(self.production_requires_emitted_solver_artifacts),
        );
        push_manifest_row(
            &mut rows,
            "production.acceptance_report_api",
            self.production_acceptance_report_api_name(),
        );
        push_manifest_row(
            &mut rows,
            "production.consumer_acceptance_api",
            self.production_consumer_acceptance_api_name(),
        );
        push_manifest_row(
            &mut rows,
            "production.acceptance_owner_suite",
            self.production_acceptance_owner_suite().code(),
        );
        push_manifest_row(
            &mut rows,
            "production.solver_evidence.owner_suite",
            self.solver_evidence_descriptor.owner_suite.code(),
        );
        push_manifest_row(
            &mut rows,
            "production.solver_evidence.capability_descriptor.schema",
            self.solver_evidence_descriptor
                .solver_capability_descriptor_schema,
        );
        push_manifest_row(
            &mut rows,
            "production.solver_evidence.capability_descriptor.schema_version",
            self.solver_evidence_descriptor
                .solver_capability_descriptor_schema_version
                .to_string(),
        );
        push_manifest_row(
            &mut rows,
            "production.solver_evidence.model_blocking_clause.schema",
            self.solver_evidence_descriptor.model_blocking_clause_schema,
        );
        push_manifest_row(
            &mut rows,
            "production.solver_evidence.model_blocking_clause.schema_version",
            self.solver_evidence_descriptor
                .model_blocking_clause_schema_version
                .to_string(),
        );
        push_manifest_row(
            &mut rows,
            "production.solver_evidence.model_blocking_clause_evidence.schema",
            self.solver_evidence_descriptor
                .model_blocking_clause_evidence_schema,
        );
        push_manifest_row(
            &mut rows,
            "production.solver_evidence.model_blocking_clause_evidence.schema_version",
            self.solver_evidence_descriptor
                .model_blocking_clause_evidence_schema_version
                .to_string(),
        );
        push_manifest_row(
            &mut rows,
            "production.solver_evidence.solve_decision_profile_model_consumer.schema",
            self.solver_evidence_descriptor
                .solve_decision_profile_model_consumer_schema,
        );
        push_manifest_row(
            &mut rows,
            "production.solver_evidence.solve_decision_profile_model_consumer.schema_version",
            self.solver_evidence_descriptor
                .solve_decision_profile_model_consumer_schema_version
                .to_string(),
        );
        push_manifest_row(
            &mut rows,
            "production.solver_evidence.acceptance_report_api",
            self.solver_evidence_descriptor.acceptance_report_api_name,
        );
        push_manifest_row(
            &mut rows,
            "production.solver_evidence.consumer_acceptance_api",
            self.solver_evidence_descriptor.consumer_acceptance_api_name,
        );

        for role in self.production_required_artifact_roles() {
            push_manifest_row(&mut rows, "production.artifact_role", role.code());
        }
        for owner_suite in self.production_artifact_owner_suites() {
            push_manifest_row(
                &mut rows,
                "production.artifact_owner_suite",
                owner_suite.code(),
            );
        }
        for (index, requirement) in self.required_artifact_requirements.iter().enumerate() {
            let prefix = format!("production.artifact_requirement.{index}");
            push_manifest_row(&mut rows, format!("{prefix}.role"), requirement.role_code());
            push_manifest_row(&mut rows, format!("{prefix}.kind"), requirement.kind.code());
            push_manifest_row(
                &mut rows,
                format!("{prefix}.digest_algorithm"),
                proof_digest_algorithm_code(requirement.digest_algorithm),
            );
            push_manifest_row(
                &mut rows,
                format!("{prefix}.owner_suite"),
                requirement.owner_suite.code(),
            );
            push_manifest_row(
                &mut rows,
                format!("{prefix}.requires_emitted_solver_artifact"),
                bool_code(requirement.requires_emitted_solver_artifact),
            );
        }

        rows
    }

    /// Emit stable escaped `key=value` manifest lines in [`Self::manifest_rows`] order.
    ///
    /// This is the no-JSON transport form for consumers that need a compact
    /// line-oriented manifest. Preserve duplicate lines and their order.
    pub fn manifest_key_value_lines(self) -> Vec<String> {
        self.manifest_rows()
            .into_iter()
            .map(|row| row.to_key_value_line())
            .collect()
    }

    /// Number of stable rows emitted by [`Self::manifest_rows`].
    pub fn manifest_row_count(self) -> usize {
        self.manifest_rows().len()
    }

    /// Stable typed digest over [`Self::manifest_key_value_text`].
    pub fn manifest_digest(self) -> ProofDigest {
        manifest_key_value_lines_digest(&self.manifest_key_value_lines())
    }

    /// Stable `sha256:<hex>` digest string over [`Self::manifest_key_value_text`].
    pub fn manifest_sha256(self) -> String {
        self.manifest_digest().to_string()
    }

    /// Emit stable line-oriented manifest text for this descriptor.
    pub fn manifest_key_value_text(self) -> String {
        format!("{}\n", self.manifest_key_value_lines().join("\n"))
    }

    /// Solver-owned report/facade API that decides production acceptance.
    ///
    /// Prefer this solver-neutral accessor in new downstream consumers. The
    /// backing field keeps its historical `model_acceptance` name for Petri/TrustMc
    /// compatibility, but hardware replay and MCC symbolic-execution lanes
    /// should not infer acceptance from that field name or rebuild solver policy.
    pub const fn production_acceptance_report_api_name(self) -> &'static str {
        self.model_acceptance_report_api_name
    }

    /// Consumer-facing API that converts the solver-owned report into accept/reject.
    pub const fn production_consumer_acceptance_api_name(self) -> &'static str {
        self.consumer_acceptance_api_name
    }

    /// Whether promotion to production requires a solver-owned acceptance report.
    pub const fn production_acceptance_requires_solver(self) -> bool {
        self.requires_solver_acceptance
    }

    /// Solver/verifier suite that owns the production acceptance boundary.
    pub const fn production_acceptance_owner_suite(self) -> NativeVerifierSuite {
        self.production_acceptance_owner_suite
    }

    /// Solver-owned capability/evidence identities required at production promotion.
    pub const fn production_solver_evidence_descriptor(
        self,
    ) -> NativeSharedPrimitiveSolverEvidenceDescriptor {
        self.solver_evidence_descriptor
    }

    /// Schema for the solver-owned capability descriptor required at production promotion.
    pub const fn production_solver_capability_descriptor_schema(self) -> &'static str {
        self.solver_evidence_descriptor
            .solver_capability_descriptor_schema
    }

    /// Schema for the solver-owned model-blocking clause required at production promotion.
    pub const fn production_model_blocking_clause_schema(self) -> &'static str {
        self.solver_evidence_descriptor.model_blocking_clause_schema
    }

    /// Schema for compact solver-owned model-blocking evidence.
    pub const fn production_model_blocking_clause_evidence_schema(self) -> &'static str {
        self.solver_evidence_descriptor
            .model_blocking_clause_evidence_schema
    }

    /// Schema for the solver-owned solve-decision model-consumer boundary.
    pub const fn production_solve_decision_profile_model_consumer_schema(self) -> &'static str {
        self.solver_evidence_descriptor
            .solve_decision_profile_model_consumer_schema
    }
}

/// Descriptor for Petri native bundle and solver-evidence handoff rows.
///
/// This is a composition point for downstream TY consumers. It names the
/// TrustIr bundle identity surface, artifact authority row vocabulary, Petri/TrustMc
/// shared primitive contract, and AY-owned solver evidence identities without
/// interpreting solver results or duplicating AY acceptance policy.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PetriNativeVerificationBundleHandoffDescriptor {
    pub schema: &'static str,
    pub schema_version: u32,
    pub source_package: &'static str,
    pub source_package_version: &'static str,
    pub bundle_identity_contract: NativeBundleIdentityContractDescriptor,
    pub artifact_authority_row_descriptor: NativeEvidenceArtifactAuthorityRowDescriptor,
    pub shared_primitive_contract: NativeSharedPrimitiveContractDescriptor,
    pub solver_evidence_descriptor: NativeSharedPrimitiveSolverEvidenceDescriptor,
    pub expected_bundle_identity_fields: &'static [&'static str],
    pub downstream_consumer_responsibilities: &'static [&'static str],
}

/// Stable section/kind for normalized Petri native handoff rows.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PetriNativeVerificationBundleHandoffRowKind {
    Descriptor,
    Source,
    BundleIdentity,
    ArtifactAuthority,
    SharedPrimitiveContract,
    SolverEvidence,
    DownstreamResponsibility,
    Other,
}

impl PetriNativeVerificationBundleHandoffRowKind {
    /// Stable lower-snake-case row kind for sidecar and schema consumers.
    pub const fn code(self) -> &'static str {
        match self {
            PetriNativeVerificationBundleHandoffRowKind::Descriptor => "descriptor",
            PetriNativeVerificationBundleHandoffRowKind::Source => "source",
            PetriNativeVerificationBundleHandoffRowKind::BundleIdentity => "bundle_identity",
            PetriNativeVerificationBundleHandoffRowKind::ArtifactAuthority => "artifact_authority",
            PetriNativeVerificationBundleHandoffRowKind::SharedPrimitiveContract => {
                "shared_primitive_contract"
            }
            PetriNativeVerificationBundleHandoffRowKind::SolverEvidence => "solver_evidence",
            PetriNativeVerificationBundleHandoffRowKind::DownstreamResponsibility => {
                "downstream_responsibility"
            }
            PetriNativeVerificationBundleHandoffRowKind::Other => "other",
        }
    }
}

/// Normalized Petri native handoff row ready for direct sidecar emission.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeVerificationBundleHandoffRow {
    pub row_kind: PetriNativeVerificationBundleHandoffRowKind,
    pub row_kind_code: &'static str,
    pub key: String,
    pub value: String,
}

impl PetriNativeVerificationBundleHandoffRow {
    pub fn new(
        row_kind: PetriNativeVerificationBundleHandoffRowKind,
        key: impl Into<String>,
        value: impl Into<String>,
    ) -> Self {
        Self {
            row_kind,
            row_kind_code: row_kind.code(),
            key: key.into(),
            value: value.into(),
        }
    }

    /// Escaped key for line-oriented normalized handoff output.
    pub fn escaped_key(&self) -> String {
        escape_manifest_component(&self.key)
    }

    /// Escaped value for line-oriented normalized handoff output.
    pub fn escaped_value(&self) -> String {
        escape_manifest_component(&self.value)
    }

    /// Stable one-line representation with row kind, key, and value columns.
    pub fn to_normalized_line(&self) -> String {
        format!(
            "row_kind={}\tkey={}\tvalue={}",
            self.row_kind_code,
            self.escaped_key(),
            self.escaped_value()
        )
    }
}

/// Required normalized handoff row identity.
///
/// `ordinal` disambiguates repeated manifest keys within a row kind. Consumers
/// can treat `(row_kind, key, ordinal)` as the deterministic required-row id.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeVerificationBundleHandoffRequiredRow {
    pub row_kind: PetriNativeVerificationBundleHandoffRowKind,
    pub row_kind_code: &'static str,
    pub key: String,
    pub ordinal: usize,
}

impl PetriNativeVerificationBundleHandoffRequiredRow {
    fn new(
        row_kind: PetriNativeVerificationBundleHandoffRowKind,
        key: String,
        ordinal: usize,
    ) -> Self {
        Self {
            row_kind,
            row_kind_code: row_kind.code(),
            key,
            ordinal,
        }
    }
}

/// Completeness status for normalized Petri handoff rows.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PetriNativeVerificationBundleHandoffCompletenessStatus {
    Complete,
    Incomplete,
}

impl PetriNativeVerificationBundleHandoffCompletenessStatus {
    /// Stable lower-snake-case status for sidecar consumers.
    pub const fn code(self) -> &'static str {
        match self {
            PetriNativeVerificationBundleHandoffCompletenessStatus::Complete => "complete",
            PetriNativeVerificationBundleHandoffCompletenessStatus::Incomplete => "incomplete",
        }
    }
}

/// Structured completeness report for downstream Petri handoff rows.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeVerificationBundleHandoffCompletenessReport {
    pub status: PetriNativeVerificationBundleHandoffCompletenessStatus,
    pub status_code: &'static str,
    pub required_rows: Vec<PetriNativeVerificationBundleHandoffRequiredRow>,
    pub missing_rows: Vec<PetriNativeVerificationBundleHandoffRequiredRow>,
    pub missing_row_kinds: Vec<PetriNativeVerificationBundleHandoffRowKind>,
    pub required_row_count: usize,
    pub present_required_row_count: usize,
}

impl PetriNativeVerificationBundleHandoffCompletenessReport {
    /// Whether every required row kind/key/ordinal is present.
    pub const fn is_complete(&self) -> bool {
        matches!(
            self.status,
            PetriNativeVerificationBundleHandoffCompletenessStatus::Complete
        )
    }

    /// Whether downstream admission must fail closed.
    pub const fn fail_closed(&self) -> bool {
        !self.is_complete()
    }
}

/// Canonical replay identity for a Petri native handoff manifest.
///
/// The digest is over deterministic, escaped text that includes the handoff
/// descriptor schema, completeness counters, required-row identities, missing
/// rows, and observed normalized rows in descriptor order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeVerificationBundleHandoffManifestIdentity {
    pub schema: &'static str,
    pub schema_version: u32,
    pub descriptor_schema: &'static str,
    pub descriptor_schema_version: u32,
    pub source_package: &'static str,
    pub source_package_version: &'static str,
    pub digest_context: &'static str,
    pub digest_algorithm: ProofDigestAlgorithm,
    pub digest: ProofDigest,
    pub canonical_text: String,
    pub completeness_status: PetriNativeVerificationBundleHandoffCompletenessStatus,
    pub completeness_status_code: &'static str,
    pub observed_row_count: usize,
    pub required_row_count: usize,
    pub present_required_row_count: usize,
    pub missing_row_count: usize,
    pub missing_rows: Vec<PetriNativeVerificationBundleHandoffRequiredRow>,
    pub missing_row_kinds: Vec<PetriNativeVerificationBundleHandoffRowKind>,
    pub extra_row_count: usize,
}

/// Missing-row diagnostic reconstructed from manifest identity key/value rows.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeVerificationBundleHandoffManifestIdentityMissingRowDiagnostic {
    pub row_kind_code: String,
    pub key: String,
    pub ordinal: usize,
}

/// Row round-trip status for Petri handoff manifest identity evidence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PetriNativeVerificationBundleHandoffManifestIdentityRoundTripStatus {
    Valid,
    Invalid,
}

impl PetriNativeVerificationBundleHandoffManifestIdentityRoundTripStatus {
    /// Stable lower-snake-case status for downstream replay checks.
    pub const fn code(self) -> &'static str {
        match self {
            PetriNativeVerificationBundleHandoffManifestIdentityRoundTripStatus::Valid => "valid",
            PetriNativeVerificationBundleHandoffManifestIdentityRoundTripStatus::Invalid => {
                "invalid"
            }
        }
    }
}

/// Deterministic validation report for manifest identity key/value rows.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeVerificationBundleHandoffManifestIdentityRoundTripReport {
    pub status: PetriNativeVerificationBundleHandoffManifestIdentityRoundTripStatus,
    pub status_code: &'static str,
    pub fail_closed: bool,
    pub expected_row_count: usize,
    pub observed_row_count: usize,
    pub unique_key_count: usize,
    pub duplicate_keys: Vec<String>,
    pub missing_keys: Vec<String>,
    pub unexpected_keys: Vec<String>,
    pub mismatched_value_keys: Vec<String>,
    pub invalid_bool_keys: Vec<String>,
    pub invalid_usize_keys: Vec<String>,
    pub reconstructed_schema: Option<String>,
    pub reconstructed_schema_version: Option<usize>,
    pub reconstructed_digest_context: Option<String>,
    pub reconstructed_digest: Option<String>,
    pub reconstructed_completeness_status_code: Option<String>,
    pub reconstructed_fail_closed: Option<bool>,
    pub reconstructed_missing_row_count: Option<usize>,
    pub reconstructed_missing_row_kind_count: Option<usize>,
    pub reconstructed_missing_row_kinds: Vec<String>,
    pub reconstructed_missing_rows:
        Vec<PetriNativeVerificationBundleHandoffManifestIdentityMissingRowDiagnostic>,
}

impl PetriNativeVerificationBundleHandoffManifestIdentity {
    /// Whether the identity covers every required handoff row.
    pub const fn is_complete(&self) -> bool {
        matches!(
            self.completeness_status,
            PetriNativeVerificationBundleHandoffCompletenessStatus::Complete
        )
    }

    /// Whether downstream admission must fail closed for this row set.
    pub const fn fail_closed(&self) -> bool {
        !self.is_complete()
    }

    /// Stable key/value rows for downstream persistence and replay snapshots.
    pub fn key_value_rows(&self) -> Vec<NativeSharedPrimitiveContractManifestRow> {
        let mut rows = Vec::new();
        push_manifest_row(&mut rows, "manifest_identity.schema", self.schema);
        push_manifest_row(
            &mut rows,
            "manifest_identity.schema_version",
            self.schema_version.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "manifest_identity.descriptor.schema",
            self.descriptor_schema,
        );
        push_manifest_row(
            &mut rows,
            "manifest_identity.descriptor.schema_version",
            self.descriptor_schema_version.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "manifest_identity.source.package",
            self.source_package,
        );
        push_manifest_row(
            &mut rows,
            "manifest_identity.source.package_version",
            self.source_package_version,
        );
        push_manifest_row(
            &mut rows,
            "manifest_identity.digest.context",
            self.digest_context,
        );
        push_manifest_row(
            &mut rows,
            "manifest_identity.digest.algorithm",
            proof_digest_algorithm_code(self.digest_algorithm),
        );
        push_manifest_row(
            &mut rows,
            "manifest_identity.digest",
            self.digest.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "manifest_identity.completeness.status",
            self.completeness_status_code,
        );
        push_manifest_row(
            &mut rows,
            "manifest_identity.fail_closed",
            bool_code(self.fail_closed()),
        );
        push_manifest_row(
            &mut rows,
            "manifest_identity.rows.observed_count",
            self.observed_row_count.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "manifest_identity.rows.required_count",
            self.required_row_count.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "manifest_identity.rows.present_required_count",
            self.present_required_row_count.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "manifest_identity.rows.missing_count",
            self.missing_row_count.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "manifest_identity.rows.extra_count",
            self.extra_row_count.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "manifest_identity.missing_row_kind_count",
            self.missing_row_kinds.len().to_string(),
        );
        for (index, row_kind) in self.missing_row_kinds.iter().enumerate() {
            push_manifest_row(
                &mut rows,
                format!("manifest_identity.missing_row_kind.{index}"),
                row_kind.code(),
            );
        }
        for (index, missing) in self.missing_rows.iter().enumerate() {
            push_manifest_row(
                &mut rows,
                format!("manifest_identity.missing_row.{index}.row_kind"),
                missing.row_kind_code,
            );
            push_manifest_row(
                &mut rows,
                format!("manifest_identity.missing_row.{index}.key"),
                &missing.key,
            );
            push_manifest_row(
                &mut rows,
                format!("manifest_identity.missing_row.{index}.ordinal"),
                missing.ordinal.to_string(),
            );
        }

        rows
    }

    /// Stable escaped `key=value` lines for manifest identity persistence.
    pub fn key_value_lines(&self) -> Vec<String> {
        self.key_value_rows()
            .into_iter()
            .map(|row| row.to_key_value_line())
            .collect()
    }

    /// Stable line-oriented text for downstream replay comparisons.
    pub fn key_value_text(&self) -> String {
        format!("{}\n", self.key_value_lines().join("\n"))
    }

    /// Validate that observed key/value rows round-trip to this manifest identity.
    pub fn round_trip_report(
        &self,
        rows: &[NativeSharedPrimitiveContractManifestRow],
    ) -> PetriNativeVerificationBundleHandoffManifestIdentityRoundTripReport {
        let expected_rows = self.key_value_rows();
        let expected_by_key = expected_rows
            .iter()
            .map(|row| (row.key.as_str(), row.value.as_str()))
            .collect::<BTreeMap<_, _>>();
        let mut observed_by_key = BTreeMap::<&str, Vec<&str>>::new();
        for row in rows {
            observed_by_key
                .entry(row.key.as_str())
                .or_default()
                .push(row.value.as_str());
        }

        let (duplicate_keys, missing_keys, unexpected_keys, mismatched_value_keys) =
            replay_key_diagnostics(&expected_by_key, &observed_by_key);

        let mut invalid_usize_keys = Vec::new();
        let mut invalid_bool_keys = Vec::new();
        let reconstructed_schema =
            observed_single_value(&observed_by_key, "manifest_identity.schema").map(str::to_string);
        let reconstructed_schema_version = observed_usize_value(
            &observed_by_key,
            "manifest_identity.schema_version",
            &mut invalid_usize_keys,
        );
        let reconstructed_digest_context =
            observed_single_value(&observed_by_key, "manifest_identity.digest.context")
                .map(str::to_string);
        let reconstructed_digest =
            observed_single_value(&observed_by_key, "manifest_identity.digest").map(str::to_string);
        let reconstructed_completeness_status_code =
            observed_single_value(&observed_by_key, "manifest_identity.completeness.status")
                .map(str::to_string);
        let reconstructed_fail_closed = observed_bool_value(
            &observed_by_key,
            "manifest_identity.fail_closed",
            &mut invalid_bool_keys,
        );
        let reconstructed_missing_row_count = observed_usize_value(
            &observed_by_key,
            "manifest_identity.rows.missing_count",
            &mut invalid_usize_keys,
        );
        let reconstructed_missing_row_kind_count = observed_usize_value(
            &observed_by_key,
            "manifest_identity.missing_row_kind_count",
            &mut invalid_usize_keys,
        );

        let reconstructed_missing_row_kinds = (0..reconstructed_missing_row_kind_count
            .unwrap_or(0))
            .filter_map(|index| {
                observed_single_value(
                    &observed_by_key,
                    &format!("manifest_identity.missing_row_kind.{index}"),
                )
                .map(str::to_string)
            })
            .collect::<Vec<_>>();
        let reconstructed_missing_rows = (0..reconstructed_missing_row_count.unwrap_or(0))
            .filter_map(|index| {
                let row_kind_code = observed_single_value(
                    &observed_by_key,
                    &format!("manifest_identity.missing_row.{index}.row_kind"),
                )?;
                let key = observed_single_value(
                    &observed_by_key,
                    &format!("manifest_identity.missing_row.{index}.key"),
                )?;
                let ordinal_key = format!("manifest_identity.missing_row.{index}.ordinal");
                let ordinal =
                    observed_usize_value(&observed_by_key, &ordinal_key, &mut invalid_usize_keys)?;

                Some(
                    PetriNativeVerificationBundleHandoffManifestIdentityMissingRowDiagnostic {
                        row_kind_code: row_kind_code.to_string(),
                        key: key.to_string(),
                        ordinal,
                    },
                )
            })
            .collect::<Vec<_>>();

        let status = if rows.len() == expected_rows.len()
            && duplicate_keys.is_empty()
            && missing_keys.is_empty()
            && unexpected_keys.is_empty()
            && mismatched_value_keys.is_empty()
            && invalid_bool_keys.is_empty()
            && invalid_usize_keys.is_empty()
        {
            PetriNativeVerificationBundleHandoffManifestIdentityRoundTripStatus::Valid
        } else {
            PetriNativeVerificationBundleHandoffManifestIdentityRoundTripStatus::Invalid
        };
        let fail_closed = !matches!(
            status,
            PetriNativeVerificationBundleHandoffManifestIdentityRoundTripStatus::Valid
        ) || reconstructed_fail_closed.unwrap_or(true);

        PetriNativeVerificationBundleHandoffManifestIdentityRoundTripReport {
            status,
            status_code: status.code(),
            fail_closed,
            expected_row_count: expected_rows.len(),
            observed_row_count: rows.len(),
            unique_key_count: observed_by_key.len(),
            duplicate_keys,
            missing_keys,
            unexpected_keys,
            mismatched_value_keys,
            invalid_bool_keys,
            invalid_usize_keys,
            reconstructed_schema,
            reconstructed_schema_version,
            reconstructed_digest_context,
            reconstructed_digest,
            reconstructed_completeness_status_code,
            reconstructed_fail_closed,
            reconstructed_missing_row_count,
            reconstructed_missing_row_kind_count,
            reconstructed_missing_row_kinds,
            reconstructed_missing_rows,
        }
    }
}

/// Self-audit status for the default Petri native handoff contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PetriNativeVerificationBundleHandoffContractHealthStatus {
    Healthy,
    Inconsistent,
}

impl PetriNativeVerificationBundleHandoffContractHealthStatus {
    /// Stable lower-snake-case status for downstream health checks.
    pub const fn code(self) -> &'static str {
        match self {
            PetriNativeVerificationBundleHandoffContractHealthStatus::Healthy => "healthy",
            PetriNativeVerificationBundleHandoffContractHealthStatus::Inconsistent => {
                "inconsistent"
            }
        }
    }
}

/// Compact self-audit report for the Petri native handoff contract.
///
/// This report is intentionally limited to schema/version agreement, row-count
/// agreement, completeness agreement, and manifest-identity persistence text.
/// Downstream TY adapters can mirror this check without reconstructing
/// TrustIr's normalized-row internals.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeVerificationBundleHandoffContractHealthReport {
    pub status: PetriNativeVerificationBundleHandoffContractHealthStatus,
    pub status_code: &'static str,
    pub descriptor_schema: &'static str,
    pub descriptor_schema_version: u32,
    pub manifest_identity_schema: &'static str,
    pub manifest_identity_schema_version: u32,
    pub manifest_row_count: usize,
    pub normalized_row_count: usize,
    pub required_row_count: usize,
    pub completeness_required_row_count: usize,
    pub completeness_present_required_row_count: usize,
    pub completeness_missing_row_count: usize,
    pub manifest_identity_observed_row_count: usize,
    pub manifest_identity_required_row_count: usize,
    pub manifest_identity_present_required_row_count: usize,
    pub manifest_identity_missing_row_count: usize,
    pub manifest_identity_extra_row_count: usize,
    pub manifest_identity_key_value_row_count: usize,
    pub manifest_identity_key_value_line_count: usize,
    pub manifest_identity_key_value_text_line_count: usize,
    pub manifest_identity_digest: ProofDigest,
    pub schema_version_rows_agree: bool,
    pub row_counts_agree: bool,
    pub completeness_agrees: bool,
    pub manifest_identity_digest_agrees: bool,
    pub manifest_identity_key_values_agree: bool,
}

impl PetriNativeVerificationBundleHandoffContractHealthReport {
    /// Whether all handoff contract surfaces agree.
    pub const fn is_healthy(&self) -> bool {
        matches!(
            self.status,
            PetriNativeVerificationBundleHandoffContractHealthStatus::Healthy
        )
    }

    /// Whether downstream admission must fail closed for this contract state.
    pub const fn fail_closed(&self) -> bool {
        !self.is_healthy()
    }

    /// Stable key/value rows for downstream health-report persistence.
    pub fn key_value_rows(&self) -> Vec<NativeSharedPrimitiveContractManifestRow> {
        let mut rows = Vec::new();
        push_manifest_row(&mut rows, "contract_health.status", self.status_code);
        push_manifest_row(
            &mut rows,
            "contract_health.fail_closed",
            bool_code(self.fail_closed()),
        );
        push_manifest_row(
            &mut rows,
            "contract_health.descriptor.schema",
            self.descriptor_schema,
        );
        push_manifest_row(
            &mut rows,
            "contract_health.descriptor.schema_version",
            self.descriptor_schema_version.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "contract_health.manifest_identity.schema",
            self.manifest_identity_schema,
        );
        push_manifest_row(
            &mut rows,
            "contract_health.manifest_identity.schema_version",
            self.manifest_identity_schema_version.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "contract_health.count.manifest_rows",
            self.manifest_row_count.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "contract_health.count.normalized_rows",
            self.normalized_row_count.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "contract_health.count.required_rows",
            self.required_row_count.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "contract_health.count.completeness.required_rows",
            self.completeness_required_row_count.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "contract_health.count.completeness.present_required_rows",
            self.completeness_present_required_row_count.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "contract_health.count.completeness.missing_rows",
            self.completeness_missing_row_count.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "contract_health.count.manifest_identity.observed_rows",
            self.manifest_identity_observed_row_count.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "contract_health.count.manifest_identity.required_rows",
            self.manifest_identity_required_row_count.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "contract_health.count.manifest_identity.present_required_rows",
            self.manifest_identity_present_required_row_count
                .to_string(),
        );
        push_manifest_row(
            &mut rows,
            "contract_health.count.manifest_identity.missing_rows",
            self.manifest_identity_missing_row_count.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "contract_health.count.manifest_identity.extra_rows",
            self.manifest_identity_extra_row_count.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "contract_health.count.manifest_identity.key_value_rows",
            self.manifest_identity_key_value_row_count.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "contract_health.count.manifest_identity.key_value_lines",
            self.manifest_identity_key_value_line_count.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "contract_health.count.manifest_identity.key_value_text_lines",
            self.manifest_identity_key_value_text_line_count.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "contract_health.manifest_identity.digest",
            self.manifest_identity_digest.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "contract_health.agreement.schema_version_rows",
            bool_code(self.schema_version_rows_agree),
        );
        push_manifest_row(
            &mut rows,
            "contract_health.agreement.row_counts",
            bool_code(self.row_counts_agree),
        );
        push_manifest_row(
            &mut rows,
            "contract_health.agreement.completeness",
            bool_code(self.completeness_agrees),
        );
        push_manifest_row(
            &mut rows,
            "contract_health.agreement.manifest_identity_digest",
            bool_code(self.manifest_identity_digest_agrees),
        );
        push_manifest_row(
            &mut rows,
            "contract_health.agreement.manifest_identity_key_values",
            bool_code(self.manifest_identity_key_values_agree),
        );

        rows
    }

    /// Stable escaped `key=value` health-report rows for sidecar persistence.
    pub fn key_value_lines(&self) -> Vec<String> {
        self.key_value_rows()
            .into_iter()
            .map(|row| row.to_key_value_line())
            .collect()
    }

    /// Stable line-oriented health-report text for replay comparisons.
    pub fn key_value_text(&self) -> String {
        format!("{}\n", self.key_value_lines().join("\n"))
    }
}

/// One fixture listed in the Petri handoff diagnostic fixture manifest.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestEntry {
    pub fixture_name: &'static str,
    pub expected_completeness_status_code: &'static str,
    pub expected_manifest_identity_status_code: &'static str,
    pub expected_contract_health_status_code: &'static str,
    pub expected_accepted: bool,
    pub expected_fail_closed: bool,
    pub handoff_schema: &'static str,
    pub handoff_schema_version: u32,
    pub manifest_identity_schema: &'static str,
    pub manifest_identity_schema_version: u32,
}

/// Deterministic manifest of TrustIr-owned Petri handoff diagnostic fixtures.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeVerificationBundleHandoffDiagnosticFixtureManifest {
    pub schema: &'static str,
    pub schema_version: u32,
    pub source_package: &'static str,
    pub source_package_version: &'static str,
    pub fixtures: Vec<PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestEntry>,
}

/// Round-trip status for Petri handoff diagnostic fixture manifest rows.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestRoundTripStatus {
    Valid,
    Invalid,
}

impl PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestRoundTripStatus {
    /// Stable lower-snake-case status for downstream replay checks.
    pub const fn code(self) -> &'static str {
        match self {
            PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestRoundTripStatus::Valid => {
                "valid"
            }
            PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestRoundTripStatus::Invalid => {
                "invalid"
            }
        }
    }
}

/// Deterministic validation report for fixture manifest key/value rows.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestRoundTripReport {
    pub status: PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestRoundTripStatus,
    pub status_code: &'static str,
    pub fail_closed: bool,
    pub expected_row_count: usize,
    pub observed_row_count: usize,
    pub unique_key_count: usize,
    pub duplicate_keys: Vec<String>,
    pub missing_keys: Vec<String>,
    pub unexpected_keys: Vec<String>,
    pub mismatched_value_keys: Vec<String>,
    pub invalid_bool_keys: Vec<String>,
    pub reconstructed_fixture_names: Vec<String>,
    pub reconstructed_completeness_status_codes: Vec<String>,
    pub reconstructed_manifest_identity_status_codes: Vec<String>,
    pub reconstructed_contract_health_status_codes: Vec<String>,
    pub reconstructed_accepted_values: Vec<bool>,
    pub reconstructed_fail_closed_values: Vec<bool>,
}

impl PetriNativeVerificationBundleHandoffDiagnosticFixtureManifest {
    /// Stable key/value rows for fixture discovery in downstream tests.
    pub fn key_value_rows(&self) -> Vec<NativeSharedPrimitiveContractManifestRow> {
        let mut rows = Vec::new();
        push_manifest_row(&mut rows, "fixture_manifest.schema", self.schema);
        push_manifest_row(
            &mut rows,
            "fixture_manifest.schema_version",
            self.schema_version.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "fixture_manifest.source.package",
            self.source_package,
        );
        push_manifest_row(
            &mut rows,
            "fixture_manifest.source.package_version",
            self.source_package_version,
        );
        push_manifest_row(
            &mut rows,
            "fixture_manifest.fixture_count",
            self.fixtures.len().to_string(),
        );
        for (index, fixture) in self.fixtures.iter().enumerate() {
            push_manifest_row(
                &mut rows,
                format!("fixture_manifest.fixture.{index}.name"),
                fixture.fixture_name,
            );
            push_manifest_row(
                &mut rows,
                format!("fixture_manifest.fixture.{index}.expected.completeness_status"),
                fixture.expected_completeness_status_code,
            );
            push_manifest_row(
                &mut rows,
                format!("fixture_manifest.fixture.{index}.expected.manifest_identity_status"),
                fixture.expected_manifest_identity_status_code,
            );
            push_manifest_row(
                &mut rows,
                format!("fixture_manifest.fixture.{index}.expected.contract_health_status"),
                fixture.expected_contract_health_status_code,
            );
            push_manifest_row(
                &mut rows,
                format!("fixture_manifest.fixture.{index}.expected.accepted"),
                bool_code(fixture.expected_accepted),
            );
            push_manifest_row(
                &mut rows,
                format!("fixture_manifest.fixture.{index}.expected.fail_closed"),
                bool_code(fixture.expected_fail_closed),
            );
            push_manifest_row(
                &mut rows,
                format!("fixture_manifest.fixture.{index}.schema.handoff"),
                fixture.handoff_schema,
            );
            push_manifest_row(
                &mut rows,
                format!("fixture_manifest.fixture.{index}.schema.handoff_version"),
                fixture.handoff_schema_version.to_string(),
            );
            push_manifest_row(
                &mut rows,
                format!("fixture_manifest.fixture.{index}.schema.manifest_identity"),
                fixture.manifest_identity_schema,
            );
            push_manifest_row(
                &mut rows,
                format!("fixture_manifest.fixture.{index}.schema.manifest_identity_version"),
                fixture.manifest_identity_schema_version.to_string(),
            );
        }

        rows
    }

    /// Stable escaped `key=value` fixture manifest rows for downstream tests.
    pub fn key_value_lines(&self) -> Vec<String> {
        self.key_value_rows()
            .into_iter()
            .map(|row| row.to_key_value_line())
            .collect()
    }

    /// Stable line-oriented fixture manifest text for replay comparisons.
    pub fn key_value_text(&self) -> String {
        format!("{}\n", self.key_value_lines().join("\n"))
    }

    /// Validate that observed key/value rows round-trip to this fixture manifest.
    pub fn round_trip_report(
        &self,
        rows: &[NativeSharedPrimitiveContractManifestRow],
    ) -> PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestRoundTripReport {
        let expected_rows = self.key_value_rows();
        let expected_by_key = expected_rows
            .iter()
            .map(|row| (row.key.as_str(), row.value.as_str()))
            .collect::<BTreeMap<_, _>>();
        let mut observed_by_key = BTreeMap::<&str, Vec<&str>>::new();
        for row in rows {
            observed_by_key
                .entry(row.key.as_str())
                .or_default()
                .push(row.value.as_str());
        }

        let (duplicate_keys, missing_keys, unexpected_keys, mismatched_value_keys) =
            replay_key_diagnostics(&expected_by_key, &observed_by_key);

        let reconstructed_fixture_names = self
            .fixtures
            .iter()
            .enumerate()
            .filter_map(|(index, _)| {
                observed_single_value(
                    &observed_by_key,
                    &format!("fixture_manifest.fixture.{index}.name"),
                )
                .map(str::to_string)
            })
            .collect::<Vec<_>>();
        let reconstructed_completeness_status_codes = self
            .fixtures
            .iter()
            .enumerate()
            .filter_map(|(index, _)| {
                observed_single_value(
                    &observed_by_key,
                    &format!("fixture_manifest.fixture.{index}.expected.completeness_status"),
                )
                .map(str::to_string)
            })
            .collect::<Vec<_>>();
        let reconstructed_manifest_identity_status_codes = self
            .fixtures
            .iter()
            .enumerate()
            .filter_map(|(index, _)| {
                observed_single_value(
                    &observed_by_key,
                    &format!("fixture_manifest.fixture.{index}.expected.manifest_identity_status"),
                )
                .map(str::to_string)
            })
            .collect::<Vec<_>>();
        let reconstructed_contract_health_status_codes = self
            .fixtures
            .iter()
            .enumerate()
            .filter_map(|(index, _)| {
                observed_single_value(
                    &observed_by_key,
                    &format!("fixture_manifest.fixture.{index}.expected.contract_health_status"),
                )
                .map(str::to_string)
            })
            .collect::<Vec<_>>();
        let (reconstructed_accepted_values, mut accepted_bool_errors) =
            reconstructed_bool_fixture_values(&observed_by_key, self.fixtures.len(), "accepted");
        let (reconstructed_fail_closed_values, mut fail_closed_bool_errors) =
            reconstructed_bool_fixture_values(&observed_by_key, self.fixtures.len(), "fail_closed");
        let mut invalid_bool_keys = Vec::new();
        invalid_bool_keys.append(&mut accepted_bool_errors);
        invalid_bool_keys.append(&mut fail_closed_bool_errors);

        let status = if rows.len() == expected_rows.len()
            && duplicate_keys.is_empty()
            && missing_keys.is_empty()
            && unexpected_keys.is_empty()
            && mismatched_value_keys.is_empty()
            && invalid_bool_keys.is_empty()
        {
            PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestRoundTripStatus::Valid
        } else {
            PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestRoundTripStatus::Invalid
        };

        PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestRoundTripReport {
            status,
            status_code: status.code(),
            fail_closed: !matches!(
                status,
                PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestRoundTripStatus::Valid
            ),
            expected_row_count: expected_rows.len(),
            observed_row_count: rows.len(),
            unique_key_count: observed_by_key.len(),
            duplicate_keys,
            missing_keys,
            unexpected_keys,
            mismatched_value_keys,
            invalid_bool_keys,
            reconstructed_fixture_names,
            reconstructed_completeness_status_codes,
            reconstructed_manifest_identity_status_codes,
            reconstructed_contract_health_status_codes,
            reconstructed_accepted_values,
            reconstructed_fail_closed_values,
        }
    }
}

/// Diagnostic fixture with the healthy default Petri handoff row set.
///
/// This is intended for downstream positive replay tests. It packages the
/// default normalized rows together with the TrustIr-owned completeness,
/// manifest-identity, and contract-health evidence that should be accepted by
/// consumers before native Petri admission.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeVerificationBundleHandoffHealthyDiagnosticFixture {
    pub fixture_name: &'static str,
    pub normalized_rows: Vec<PetriNativeVerificationBundleHandoffRow>,
    pub completeness_report: PetriNativeVerificationBundleHandoffCompletenessReport,
    pub manifest_identity: PetriNativeVerificationBundleHandoffManifestIdentity,
    pub manifest_identity_rows: Vec<NativeSharedPrimitiveContractManifestRow>,
    pub contract_health_report: PetriNativeVerificationBundleHandoffContractHealthReport,
    pub contract_health_rows: Vec<NativeSharedPrimitiveContractManifestRow>,
}

impl PetriNativeVerificationBundleHandoffHealthyDiagnosticFixture {
    /// Whether all packaged TrustIr handoff evidence is internally healthy.
    pub fn is_healthy(&self) -> bool {
        self.completeness_report.is_complete()
            && self.manifest_identity.is_complete()
            && self.contract_health_report.is_healthy()
    }

    /// Whether downstream replay tests should accept this fixture's row set.
    pub fn accepted(&self) -> bool {
        self.is_healthy()
            && !self.completeness_report.fail_closed()
            && !self.manifest_identity.fail_closed()
            && !self.contract_health_report.fail_closed()
    }

    /// Whether downstream admission must fail closed for this fixture.
    pub fn fail_closed(&self) -> bool {
        !self.accepted()
    }
}

/// Diagnostic fixture with a deterministic incomplete Petri handoff row set.
///
/// This is intended for downstream fail-closed replay tests. It deliberately
/// omits a bundle-identity row and a AY solver-evidence row, then carries the
/// expected TrustIr completeness, manifest-identity, and health failure evidence
/// for that observed row set.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeVerificationBundleHandoffIncompleteDiagnosticFixture {
    pub fixture_name: &'static str,
    pub missing_row_keys: &'static [&'static str],
    pub normalized_rows: Vec<PetriNativeVerificationBundleHandoffRow>,
    pub completeness_report: PetriNativeVerificationBundleHandoffCompletenessReport,
    pub manifest_identity: PetriNativeVerificationBundleHandoffManifestIdentity,
    pub contract_health_report: PetriNativeVerificationBundleHandoffContractHealthReport,
}

impl PetriNativeVerificationBundleHandoffIncompleteDiagnosticFixture {
    /// Whether the fixture represents a fail-closed handoff state.
    pub const fn fail_closed(&self) -> bool {
        self.completeness_report.fail_closed()
            || self.manifest_identity.fail_closed()
            || self.contract_health_report.fail_closed()
    }
}

/// Aggregate discovery surface for Petri native handoff replay contracts.
///
/// Downstream TY consumers can import this single surface to discover the
/// descriptor, normalized-row, required-row, manifest-identity, health-report,
/// fixture, fixture-manifest, and round-trip validator helpers that TrustIr owns.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PetriNativeVerificationBundleHandoffReplayContractSurface {
    pub schema: &'static str,
    pub schema_version: u32,
    pub source_package: &'static str,
    pub source_package_version: &'static str,
    pub helper_names: &'static [&'static str],
    pub schema_names: &'static [&'static str],
    pub schema_values: &'static [&'static str],
    pub fixture_names: &'static [&'static str],
    pub validator_names: &'static [&'static str],
}

/// Round-trip status for Petri handoff replay contract surface rows.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripStatus {
    Valid,
    Invalid,
}

impl PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripStatus {
    /// Stable lower-snake-case status for downstream replay checks.
    pub const fn code(self) -> &'static str {
        match self {
            PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripStatus::Valid => {
                "valid"
            }
            PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripStatus::Invalid => {
                "invalid"
            }
        }
    }
}

/// Deterministic validation report for replay contract surface key/value rows.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport {
    pub status: PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripStatus,
    pub status_code: &'static str,
    pub fail_closed: bool,
    pub expected_row_count: usize,
    pub observed_row_count: usize,
    pub unique_key_count: usize,
    pub duplicate_keys: Vec<String>,
    pub missing_keys: Vec<String>,
    pub unexpected_keys: Vec<String>,
    pub mismatched_value_keys: Vec<String>,
    pub invalid_usize_keys: Vec<String>,
    pub invalid_lines: Vec<String>,
    pub reconstructed_schema: Option<String>,
    pub reconstructed_schema_version: Option<usize>,
    pub reconstructed_helper_names: Vec<String>,
    pub reconstructed_schema_names: Vec<String>,
    pub reconstructed_schema_values: Vec<String>,
    pub reconstructed_fixture_count: Option<usize>,
    pub reconstructed_fixture_names: Vec<String>,
    pub reconstructed_validator_names: Vec<String>,
    pub schema_header_matches: bool,
    pub schema_name_value_rows_agree: bool,
    pub helper_names_match: bool,
    pub fixture_count_matches: bool,
    pub fixture_names_match: bool,
    pub validator_names_match: bool,
}

/// Deterministic validation report for persisted replay contract report rows.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReportKeyValueRoundTripReport
{
    pub status: PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripStatus,
    pub status_code: &'static str,
    pub fail_closed: bool,
    pub expected_row_count: usize,
    pub observed_row_count: usize,
    pub unique_key_count: usize,
    pub duplicate_keys: Vec<String>,
    pub missing_keys: Vec<String>,
    pub unexpected_keys: Vec<String>,
    pub mismatched_value_keys: Vec<String>,
    pub invalid_lines: Vec<String>,
}

/// Binding status between replay-report JSON and the handoff manifest identity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingStatus {
    Bound,
    Mismatched,
}

impl PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingStatus {
    /// Stable lower-snake-case status for downstream admission checks.
    pub const fn code(self) -> &'static str {
        match self {
            PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingStatus::Bound => {
                "bound"
            }
            PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingStatus::Mismatched => {
                "mismatched"
            }
        }
    }
}

/// Deterministic report tying compact replay JSON to the handoff identity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingReport {
    pub schema: &'static str,
    pub schema_version: u32,
    pub status: PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingStatus,
    pub status_code: &'static str,
    pub fail_closed: bool,
    pub json_manifest_schema: &'static str,
    pub json_manifest_schema_version: u32,
    pub json_manifest_text_digest_context: &'static str,
    pub json_manifest_text_digest: ProofDigest,
    pub round_trip_report_identity_digest_context: &'static str,
    pub round_trip_report_identity_digest: ProofDigest,
    pub manifest_identity_schema: &'static str,
    pub manifest_identity_schema_version: u32,
    pub manifest_identity_digest_context: &'static str,
    pub manifest_identity_digest: ProofDigest,
    pub report_valid: bool,
    pub replay_surface_schema_matches: bool,
    pub handoff_schema_listed_by_surface: bool,
    pub manifest_identity_schema_listed_by_surface: bool,
    pub manifest_identity_complete: bool,
    pub manifest_identity_descriptor_matches: bool,
    pub manifest_identity_source_matches: bool,
    pub manifest_identity_digest_matches_canonical_text: bool,
}

impl PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingReport {
    /// Whether replay-report JSON belongs to the same Petri handoff surface.
    pub const fn is_bound(&self) -> bool {
        matches!(
            self.status,
            PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingStatus::Bound
        )
    }

    /// Stable key/value rows for downstream JSON-to-handoff admission.
    pub fn key_value_rows(&self) -> Vec<NativeSharedPrimitiveContractManifestRow> {
        let mut rows = Vec::new();
        push_manifest_row(&mut rows, "json_manifest_binding.schema", self.schema);
        push_manifest_row(
            &mut rows,
            "json_manifest_binding.schema_version",
            self.schema_version.to_string(),
        );
        push_manifest_row(&mut rows, "json_manifest_binding.status", self.status_code);
        push_manifest_row(
            &mut rows,
            "json_manifest_binding.fail_closed",
            bool_code(self.fail_closed),
        );
        push_manifest_row(&mut rows, "json_manifest.schema", self.json_manifest_schema);
        push_manifest_row(
            &mut rows,
            "json_manifest.schema_version",
            self.json_manifest_schema_version.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "json_manifest.text_digest.context",
            self.json_manifest_text_digest_context,
        );
        push_manifest_row(
            &mut rows,
            "json_manifest.text_digest.algorithm",
            proof_digest_algorithm_code(self.json_manifest_text_digest.algorithm),
        );
        push_manifest_row(
            &mut rows,
            "json_manifest.text_digest",
            self.json_manifest_text_digest.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "round_trip_report.identity_digest.context",
            self.round_trip_report_identity_digest_context,
        );
        push_manifest_row(
            &mut rows,
            "round_trip_report.identity_digest.algorithm",
            proof_digest_algorithm_code(self.round_trip_report_identity_digest.algorithm),
        );
        push_manifest_row(
            &mut rows,
            "round_trip_report.identity_digest",
            self.round_trip_report_identity_digest.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "manifest_identity.schema",
            self.manifest_identity_schema,
        );
        push_manifest_row(
            &mut rows,
            "manifest_identity.schema_version",
            self.manifest_identity_schema_version.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "manifest_identity.digest.context",
            self.manifest_identity_digest_context,
        );
        push_manifest_row(
            &mut rows,
            "manifest_identity.digest.algorithm",
            proof_digest_algorithm_code(self.manifest_identity_digest.algorithm),
        );
        push_manifest_row(
            &mut rows,
            "manifest_identity.digest",
            self.manifest_identity_digest.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "json_manifest_binding.check.report_valid",
            bool_code(self.report_valid),
        );
        push_manifest_row(
            &mut rows,
            "json_manifest_binding.check.replay_surface_schema_matches",
            bool_code(self.replay_surface_schema_matches),
        );
        push_manifest_row(
            &mut rows,
            "json_manifest_binding.check.handoff_schema_listed_by_surface",
            bool_code(self.handoff_schema_listed_by_surface),
        );
        push_manifest_row(
            &mut rows,
            "json_manifest_binding.check.manifest_identity_schema_listed_by_surface",
            bool_code(self.manifest_identity_schema_listed_by_surface),
        );
        push_manifest_row(
            &mut rows,
            "json_manifest_binding.check.manifest_identity_complete",
            bool_code(self.manifest_identity_complete),
        );
        push_manifest_row(
            &mut rows,
            "json_manifest_binding.check.manifest_identity_descriptor_matches",
            bool_code(self.manifest_identity_descriptor_matches),
        );
        push_manifest_row(
            &mut rows,
            "json_manifest_binding.check.manifest_identity_source_matches",
            bool_code(self.manifest_identity_source_matches),
        );
        push_manifest_row(
            &mut rows,
            "json_manifest_binding.check.manifest_identity_digest_matches_canonical_text",
            bool_code(self.manifest_identity_digest_matches_canonical_text),
        );

        rows
    }

    /// Stable escaped `key=value` binding rows for sidecar persistence.
    pub fn key_value_lines(&self) -> Vec<String> {
        self.key_value_rows()
            .into_iter()
            .map(|row| row.to_key_value_line())
            .collect()
    }

    /// Stable line-oriented binding report text for replay comparisons.
    pub fn key_value_text(&self) -> String {
        format!("{}\n", self.key_value_lines().join("\n"))
    }
}

/// Canonical fixture binding replay-report JSON to Petri handoff identity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingFixture {
    pub fixture_name: &'static str,
    pub expected_status_code: &'static str,
    pub expected_fail_closed: bool,
    pub compact_json_text: String,
    pub round_trip_report: PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport,
    pub manifest_identity: PetriNativeVerificationBundleHandoffManifestIdentity,
    pub binding_report: PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingReport,
    pub binding_rows: Vec<NativeSharedPrimitiveContractManifestRow>,
}

impl PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingFixture {
    /// Whether downstream admission should accept this fixture's binding.
    pub fn accepted(&self) -> bool {
        self.binding_report.is_bound()
            && self.binding_report.status_code == self.expected_status_code
            && self.binding_report.fail_closed == self.expected_fail_closed
            && !self.expected_fail_closed
    }

    /// Whether downstream admission must fail closed for this fixture.
    pub fn fail_closed(&self) -> bool {
        !self.accepted()
    }

    /// Stable fixture rows wrapping the binding rows and source identities.
    pub fn key_value_rows(&self) -> Vec<NativeSharedPrimitiveContractManifestRow> {
        let mut rows = Vec::new();
        push_manifest_row(
            &mut rows,
            "json_manifest_binding_fixture.name",
            self.fixture_name,
        );
        push_manifest_row(
            &mut rows,
            "json_manifest_binding_fixture.expected.status",
            self.expected_status_code,
        );
        push_manifest_row(
            &mut rows,
            "json_manifest_binding_fixture.expected.fail_closed",
            bool_code(self.expected_fail_closed),
        );
        push_manifest_row(
            &mut rows,
            "json_manifest_binding_fixture.observed.status",
            self.binding_report.status_code,
        );
        push_manifest_row(
            &mut rows,
            "json_manifest_binding_fixture.observed.fail_closed",
            bool_code(self.binding_report.fail_closed),
        );
        push_manifest_row(
            &mut rows,
            "json_manifest_binding_fixture.accepted",
            bool_code(self.accepted()),
        );
        push_manifest_row(
            &mut rows,
            "json_manifest_binding_fixture.fail_closed",
            bool_code(self.fail_closed()),
        );
        push_manifest_row(
            &mut rows,
            "json_manifest_binding_fixture.compact_json_text_digest.context",
            PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_JSON_MANIFEST_BINDING_DIGEST_CONTEXT,
        );
        push_manifest_row(
            &mut rows,
            "json_manifest_binding_fixture.compact_json_text_digest",
            self.binding_report.json_manifest_text_digest.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "json_manifest_binding_fixture.round_trip_report_identity_digest",
            self.round_trip_report.identity_digest().to_string(),
        );
        push_manifest_row(
            &mut rows,
            "json_manifest_binding_fixture.manifest_identity_digest",
            self.manifest_identity.digest.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "json_manifest_binding_fixture.binding_row_count",
            self.binding_rows.len().to_string(),
        );
        for (index, row) in self.binding_rows.iter().enumerate() {
            push_manifest_row(
                &mut rows,
                format!("json_manifest_binding_fixture.binding_row.{index}.key"),
                &row.key,
            );
            push_manifest_row(
                &mut rows,
                format!("json_manifest_binding_fixture.binding_row.{index}.value"),
                &row.value,
            );
        }

        rows
    }

    /// Stable escaped `key=value` fixture rows for downstream replay tests.
    pub fn key_value_lines(&self) -> Vec<String> {
        self.key_value_rows()
            .into_iter()
            .map(|row| row.to_key_value_line())
            .collect()
    }

    /// Stable line-oriented fixture text for downstream replay tests.
    pub fn key_value_text(&self) -> String {
        format!("{}\n", self.key_value_lines().join("\n"))
    }
}

impl PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport {
    /// Total count of compact row diagnostics represented by this report.
    pub fn diagnostic_count(&self) -> usize {
        self.duplicate_keys.len()
            + self.missing_keys.len()
            + self.unexpected_keys.len()
            + self.mismatched_value_keys.len()
            + self.invalid_usize_keys.len()
            + self.invalid_lines.len()
    }

    /// Stable canonical text for compact report identity comparisons.
    pub fn canonical_identity_text(&self) -> String {
        let mut lines = Vec::new();
        push_manifest_identity_line(
            &mut lines,
            "round_trip_report.schema",
            PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_ROUND_TRIP_REPORT_SCHEMA,
        );
        push_manifest_identity_line(
            &mut lines,
            "round_trip_report.schema_version",
            PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_ROUND_TRIP_REPORT_SCHEMA_VERSION
                .to_string(),
        );
        push_manifest_identity_line(&mut lines, "round_trip_report.status", self.status_code);
        push_manifest_identity_line(
            &mut lines,
            "round_trip_report.fail_closed",
            bool_code(self.fail_closed),
        );
        push_manifest_identity_line(
            &mut lines,
            "round_trip_report.surface.schema",
            self.reconstructed_schema.as_deref().unwrap_or("<missing>"),
        );
        push_manifest_identity_line(
            &mut lines,
            "round_trip_report.surface.schema_version",
            self.reconstructed_schema_version
                .map(|version| version.to_string())
                .unwrap_or_else(|| "<missing>".to_string()),
        );
        push_manifest_identity_line(
            &mut lines,
            "round_trip_report.count.expected_rows",
            self.expected_row_count.to_string(),
        );
        push_manifest_identity_line(
            &mut lines,
            "round_trip_report.count.observed_rows",
            self.observed_row_count.to_string(),
        );
        push_manifest_identity_line(
            &mut lines,
            "round_trip_report.count.unique_keys",
            self.unique_key_count.to_string(),
        );
        push_manifest_identity_line(
            &mut lines,
            "round_trip_report.count.helpers",
            self.reconstructed_helper_names.len().to_string(),
        );
        push_manifest_identity_line(
            &mut lines,
            "round_trip_report.count.validators",
            self.reconstructed_validator_names.len().to_string(),
        );
        push_manifest_identity_line(
            &mut lines,
            "round_trip_report.count.fixtures",
            self.reconstructed_fixture_count
                .unwrap_or(self.reconstructed_fixture_names.len())
                .to_string(),
        );
        push_manifest_identity_line(
            &mut lines,
            "round_trip_report.count.diagnostics",
            self.diagnostic_count().to_string(),
        );
        push_manifest_identity_line(
            &mut lines,
            "round_trip_report.agreement.schema_header",
            bool_code(self.schema_header_matches),
        );
        push_manifest_identity_line(
            &mut lines,
            "round_trip_report.agreement.schema_name_value_rows",
            bool_code(self.schema_name_value_rows_agree),
        );
        push_manifest_identity_line(
            &mut lines,
            "round_trip_report.agreement.helper_names",
            bool_code(self.helper_names_match),
        );
        push_manifest_identity_line(
            &mut lines,
            "round_trip_report.agreement.fixture_count",
            bool_code(self.fixture_count_matches),
        );
        push_manifest_identity_line(
            &mut lines,
            "round_trip_report.agreement.fixture_names",
            bool_code(self.fixture_names_match),
        );
        push_manifest_identity_line(
            &mut lines,
            "round_trip_report.agreement.validator_names",
            bool_code(self.validator_names_match),
        );
        push_replay_contract_report_diagnostic_lines(
            &mut lines,
            "duplicate_key",
            &self.duplicate_keys,
        );
        push_replay_contract_report_diagnostic_lines(&mut lines, "missing_key", &self.missing_keys);
        push_replay_contract_report_diagnostic_lines(
            &mut lines,
            "unexpected_key",
            &self.unexpected_keys,
        );
        push_replay_contract_report_diagnostic_lines(
            &mut lines,
            "mismatched_value_key",
            &self.mismatched_value_keys,
        );
        push_replay_contract_report_diagnostic_lines(
            &mut lines,
            "invalid_usize_key",
            &self.invalid_usize_keys,
        );
        push_replay_contract_report_diagnostic_lines(
            &mut lines,
            "invalid_line",
            &self.invalid_lines,
        );

        format!("{}\n", lines.join("\n"))
    }

    /// Stable digest over the compact round-trip report identity text.
    pub fn identity_digest(&self) -> ProofDigest {
        ProofDigest::sha256_domain(
            PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_ROUND_TRIP_REPORT_DIGEST_CONTEXT,
            self.canonical_identity_text().as_bytes(),
        )
    }

    /// Stable one-line JSON manifest for non-Rust downstream admission checks.
    pub fn compact_manifest_json_text(&self) -> String {
        let digest = self.identity_digest();
        let fixture_count = self
            .reconstructed_fixture_count
            .unwrap_or(self.reconstructed_fixture_names.len());
        let surface_schema_version = self
            .reconstructed_schema_version
            .map(|version| version.to_string())
            .unwrap_or_else(|| "null".to_string());
        format!(
            "{{\"schema\":{},\"schema_version\":{},\"identity_text\":{},\"identity_digest_context\":{},\"identity_digest_algorithm\":{},\"identity_digest\":{},\"status\":{},\"fail_closed\":{},\"surface_schema\":{},\"surface_schema_version\":{},\"expected_row_count\":{},\"observed_row_count\":{},\"unique_key_count\":{},\"helper_count\":{},\"validator_count\":{},\"fixture_count\":{},\"diagnostic_count\":{}}}\n",
            json_string_literal(
                PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_ROUND_TRIP_REPORT_SCHEMA
            ),
            PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_ROUND_TRIP_REPORT_SCHEMA_VERSION,
            json_string_literal(&self.canonical_identity_text()),
            json_string_literal(
                PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_ROUND_TRIP_REPORT_DIGEST_CONTEXT
            ),
            json_string_literal(proof_digest_algorithm_code(digest.algorithm)),
            json_string_literal(&digest.to_string()),
            json_string_literal(self.status_code),
            bool_code(self.fail_closed),
            json_string_literal(self.reconstructed_schema.as_deref().unwrap_or("")),
            surface_schema_version,
            self.expected_row_count,
            self.observed_row_count,
            self.unique_key_count,
            self.reconstructed_helper_names.len(),
            self.reconstructed_validator_names.len(),
            fixture_count,
            self.diagnostic_count()
        )
    }

    /// Bind this compact JSON report to a Petri handoff manifest identity.
    pub fn compact_manifest_handoff_identity_report(
        &self,
        manifest_identity: &PetriNativeVerificationBundleHandoffManifestIdentity,
    ) -> PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingReport {
        let json_manifest_text = self.compact_manifest_json_text();
        let json_manifest_text_digest = ProofDigest::sha256_domain(
            PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_JSON_MANIFEST_BINDING_DIGEST_CONTEXT,
            json_manifest_text.as_bytes(),
        );
        let round_trip_report_identity_digest = self.identity_digest();
        let manifest_identity_digest_matches_canonical_text = manifest_identity.digest
            == ProofDigest::sha256_domain(
                PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_DIGEST_CONTEXT,
                manifest_identity.canonical_text.as_bytes(),
            );
        let report_valid = matches!(
            self.status,
            PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripStatus::Valid
        ) && !self.fail_closed;
        let replay_surface_schema_matches = self.reconstructed_schema.as_deref()
            == Some(PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_SURFACE_SCHEMA);
        let handoff_schema_listed_by_surface = self
            .reconstructed_schema_values
            .iter()
            .any(|schema| schema == PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SCHEMA);
        let manifest_identity_schema_listed_by_surface =
            self.reconstructed_schema_values.iter().any(|schema| {
                schema == PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_SCHEMA
            });
        let manifest_identity_complete =
            manifest_identity.is_complete() && !manifest_identity.fail_closed();
        let manifest_identity_descriptor_matches = manifest_identity.schema
            == PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_SCHEMA
            && manifest_identity.schema_version
                == PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_SCHEMA_VERSION
            && manifest_identity.descriptor_schema
                == PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SCHEMA
            && manifest_identity.descriptor_schema_version
                == PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SCHEMA_VERSION
            && manifest_identity.digest_context
                == PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_DIGEST_CONTEXT;
        let manifest_identity_source_matches = manifest_identity.source_package
            == PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SOURCE_PACKAGE
            && manifest_identity.source_package_version
                == PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SOURCE_PACKAGE_VERSION;

        let status = if report_valid
            && replay_surface_schema_matches
            && handoff_schema_listed_by_surface
            && manifest_identity_schema_listed_by_surface
            && manifest_identity_complete
            && manifest_identity_descriptor_matches
            && manifest_identity_source_matches
            && manifest_identity_digest_matches_canonical_text
        {
            PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingStatus::Bound
        } else {
            PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingStatus::Mismatched
        };

        PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingReport {
            schema: PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_JSON_MANIFEST_BINDING_SCHEMA,
            schema_version:
                PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_JSON_MANIFEST_BINDING_SCHEMA_VERSION,
            status,
            status_code: status.code(),
            fail_closed: !matches!(
                status,
                PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingStatus::Bound
            ),
            json_manifest_schema:
                PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_ROUND_TRIP_REPORT_SCHEMA,
            json_manifest_schema_version:
                PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_ROUND_TRIP_REPORT_SCHEMA_VERSION,
            json_manifest_text_digest_context:
                PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_JSON_MANIFEST_BINDING_DIGEST_CONTEXT,
            json_manifest_text_digest,
            round_trip_report_identity_digest_context:
                PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_ROUND_TRIP_REPORT_DIGEST_CONTEXT,
            round_trip_report_identity_digest,
            manifest_identity_schema:
                PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_SCHEMA,
            manifest_identity_schema_version:
                PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_SCHEMA_VERSION,
            manifest_identity_digest_context:
                PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_DIGEST_CONTEXT,
            manifest_identity_digest: manifest_identity.digest,
            report_valid,
            replay_surface_schema_matches,
            handoff_schema_listed_by_surface,
            manifest_identity_schema_listed_by_surface,
            manifest_identity_complete,
            manifest_identity_descriptor_matches,
            manifest_identity_source_matches,
            manifest_identity_digest_matches_canonical_text,
        }
    }

    /// Stable key/value rows for downstream persistence of this report summary.
    pub fn key_value_rows(&self) -> Vec<NativeSharedPrimitiveContractManifestRow> {
        let digest = self.identity_digest();
        let fixture_count = self
            .reconstructed_fixture_count
            .unwrap_or(self.reconstructed_fixture_names.len());
        let mut rows = Vec::new();
        push_manifest_row(
            &mut rows,
            "round_trip_report.schema",
            PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_ROUND_TRIP_REPORT_SCHEMA,
        );
        push_manifest_row(
            &mut rows,
            "round_trip_report.schema_version",
            PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_ROUND_TRIP_REPORT_SCHEMA_VERSION
                .to_string(),
        );
        push_manifest_row(&mut rows, "round_trip_report.status", self.status_code);
        push_manifest_row(
            &mut rows,
            "round_trip_report.fail_closed",
            bool_code(self.fail_closed),
        );
        push_manifest_row(
            &mut rows,
            "round_trip_report.surface.schema",
            self.reconstructed_schema.as_deref().unwrap_or(""),
        );
        push_manifest_row(
            &mut rows,
            "round_trip_report.surface.schema_version",
            self.reconstructed_schema_version
                .map(|version| version.to_string())
                .unwrap_or_default(),
        );
        push_manifest_row(
            &mut rows,
            "round_trip_report.count.expected_rows",
            self.expected_row_count.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "round_trip_report.count.observed_rows",
            self.observed_row_count.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "round_trip_report.count.unique_keys",
            self.unique_key_count.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "round_trip_report.count.helpers",
            self.reconstructed_helper_names.len().to_string(),
        );
        push_manifest_row(
            &mut rows,
            "round_trip_report.count.validators",
            self.reconstructed_validator_names.len().to_string(),
        );
        push_manifest_row(
            &mut rows,
            "round_trip_report.count.fixtures",
            fixture_count.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "round_trip_report.count.diagnostics",
            self.diagnostic_count().to_string(),
        );
        push_manifest_row(
            &mut rows,
            "round_trip_report.diagnostic.duplicate_keys",
            self.duplicate_keys.len().to_string(),
        );
        push_manifest_row(
            &mut rows,
            "round_trip_report.diagnostic.missing_keys",
            self.missing_keys.len().to_string(),
        );
        push_manifest_row(
            &mut rows,
            "round_trip_report.diagnostic.unexpected_keys",
            self.unexpected_keys.len().to_string(),
        );
        push_manifest_row(
            &mut rows,
            "round_trip_report.diagnostic.mismatched_value_keys",
            self.mismatched_value_keys.len().to_string(),
        );
        push_manifest_row(
            &mut rows,
            "round_trip_report.diagnostic.invalid_usize_keys",
            self.invalid_usize_keys.len().to_string(),
        );
        push_manifest_row(
            &mut rows,
            "round_trip_report.diagnostic.invalid_lines",
            self.invalid_lines.len().to_string(),
        );
        push_manifest_row(
            &mut rows,
            "round_trip_report.digest.context",
            PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_ROUND_TRIP_REPORT_DIGEST_CONTEXT,
        );
        push_manifest_row(
            &mut rows,
            "round_trip_report.digest.algorithm",
            proof_digest_algorithm_code(digest.algorithm),
        );
        push_manifest_row(&mut rows, "round_trip_report.digest", digest.to_string());

        rows
    }

    /// Stable escaped `key=value` rows for downstream report persistence.
    pub fn key_value_lines(&self) -> Vec<String> {
        self.key_value_rows()
            .into_iter()
            .map(|row| row.to_key_value_line())
            .collect()
    }

    /// Stable line-oriented report text for replay comparisons.
    pub fn key_value_text(&self) -> String {
        format!("{}\n", self.key_value_lines().join("\n"))
    }

    /// Validate persisted report summary rows against this report.
    pub fn key_value_round_trip_report(
        &self,
        rows: &[NativeSharedPrimitiveContractManifestRow],
    ) -> PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReportKeyValueRoundTripReport{
        self.key_value_round_trip_report_with_invalid_lines(rows, Vec::new())
    }

    /// Validate persisted report summary `key=value` lines against this report.
    pub fn key_value_line_round_trip_report(
        &self,
        lines: &[String],
    ) -> PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReportKeyValueRoundTripReport{
        let mut invalid_lines = Vec::new();
        let mut rows = Vec::new();
        for (index, line) in lines.iter().enumerate() {
            if let Some((key, value)) = line.split_once('=') {
                rows.push(NativeSharedPrimitiveContractManifestRow::new(key, value));
            } else {
                invalid_lines.push(format!("{index}:{line}"));
            }
        }

        self.key_value_round_trip_report_with_invalid_lines(&rows, invalid_lines)
    }

    fn key_value_round_trip_report_with_invalid_lines(
        &self,
        rows: &[NativeSharedPrimitiveContractManifestRow],
        invalid_lines: Vec<String>,
    ) -> PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReportKeyValueRoundTripReport{
        let expected_rows = self.key_value_rows();
        let expected_by_key = expected_rows
            .iter()
            .map(|row| (row.key.as_str(), row.value.as_str()))
            .collect::<BTreeMap<_, _>>();
        let mut observed_by_key = BTreeMap::<&str, Vec<&str>>::new();
        for row in rows {
            observed_by_key
                .entry(row.key.as_str())
                .or_default()
                .push(row.value.as_str());
        }

        let (duplicate_keys, missing_keys, unexpected_keys, mismatched_value_keys) =
            replay_key_diagnostics(&expected_by_key, &observed_by_key);
        let status = if rows.len() == expected_rows.len()
            && duplicate_keys.is_empty()
            && missing_keys.is_empty()
            && unexpected_keys.is_empty()
            && mismatched_value_keys.is_empty()
            && invalid_lines.is_empty()
        {
            PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripStatus::Valid
        } else {
            PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripStatus::Invalid
        };

        PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReportKeyValueRoundTripReport {
            status,
            status_code: status.code(),
            fail_closed: !matches!(
                status,
                PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripStatus::Valid
            ),
            expected_row_count: expected_rows.len(),
            observed_row_count: rows.len(),
            unique_key_count: observed_by_key.len(),
            duplicate_keys,
            missing_keys,
            unexpected_keys,
            mismatched_value_keys,
            invalid_lines,
        }
    }
}

impl PetriNativeVerificationBundleHandoffReplayContractSurface {
    /// Stable key/value rows naming every downstream replay import.
    pub fn key_value_rows(&self) -> Vec<NativeSharedPrimitiveContractManifestRow> {
        let mut rows = Vec::new();
        push_manifest_row(&mut rows, "replay_contract_surface.schema", self.schema);
        push_manifest_row(
            &mut rows,
            "replay_contract_surface.schema_version",
            self.schema_version.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "replay_contract_surface.source.package",
            self.source_package,
        );
        push_manifest_row(
            &mut rows,
            "replay_contract_surface.source.package_version",
            self.source_package_version,
        );
        push_manifest_row(
            &mut rows,
            "replay_contract_surface.helper_count",
            self.helper_names.len().to_string(),
        );
        for (index, helper_name) in self.helper_names.iter().enumerate() {
            push_manifest_row(
                &mut rows,
                format!("replay_contract_surface.helper.{index}.name"),
                *helper_name,
            );
        }
        push_manifest_row(
            &mut rows,
            "replay_contract_surface.schema_count",
            self.schema_names.len().to_string(),
        );
        for (index, schema_name) in self.schema_names.iter().enumerate() {
            push_manifest_row(
                &mut rows,
                format!("replay_contract_surface.schema.{index}.name"),
                *schema_name,
            );
            if let Some(schema_value) = self.schema_values.get(index) {
                push_manifest_row(
                    &mut rows,
                    format!("replay_contract_surface.schema.{index}.value"),
                    *schema_value,
                );
            }
        }
        push_manifest_row(
            &mut rows,
            "replay_contract_surface.fixture_count",
            self.fixture_names.len().to_string(),
        );
        for (index, fixture_name) in self.fixture_names.iter().enumerate() {
            push_manifest_row(
                &mut rows,
                format!("replay_contract_surface.fixture.{index}.name"),
                *fixture_name,
            );
        }
        push_manifest_row(
            &mut rows,
            "replay_contract_surface.validator_count",
            self.validator_names.len().to_string(),
        );
        for (index, validator_name) in self.validator_names.iter().enumerate() {
            push_manifest_row(
                &mut rows,
                format!("replay_contract_surface.validator.{index}.name"),
                *validator_name,
            );
        }

        rows
    }

    /// Stable escaped `key=value` rows for downstream import manifests.
    pub fn key_value_lines(&self) -> Vec<String> {
        self.key_value_rows()
            .into_iter()
            .map(|row| row.to_key_value_line())
            .collect()
    }

    /// Stable line-oriented import-surface text for sidecar snapshots.
    pub fn key_value_text(&self) -> String {
        format!("{}\n", self.key_value_lines().join("\n"))
    }

    /// Validate that observed key/value rows round-trip to this import surface.
    pub fn round_trip_report(
        &self,
        rows: &[NativeSharedPrimitiveContractManifestRow],
    ) -> PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport {
        self.round_trip_report_with_invalid_lines(rows, Vec::new())
    }

    /// Validate that emitted `key=value` lines round-trip to this import surface.
    pub fn round_trip_report_for_key_value_lines(
        &self,
        lines: &[String],
    ) -> PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport {
        let mut invalid_lines = Vec::new();
        let mut rows = Vec::new();
        for (index, line) in lines.iter().enumerate() {
            if let Some((key, value)) = line.split_once('=') {
                rows.push(NativeSharedPrimitiveContractManifestRow::new(key, value));
            } else {
                invalid_lines.push(format!("{index}:{line}"));
            }
        }

        self.round_trip_report_with_invalid_lines(&rows, invalid_lines)
    }

    fn round_trip_report_with_invalid_lines(
        &self,
        rows: &[NativeSharedPrimitiveContractManifestRow],
        invalid_lines: Vec<String>,
    ) -> PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport {
        let expected_rows = self.key_value_rows();
        let expected_by_key = expected_rows
            .iter()
            .map(|row| (row.key.as_str(), row.value.as_str()))
            .collect::<BTreeMap<_, _>>();
        let mut observed_by_key = BTreeMap::<&str, Vec<&str>>::new();
        for row in rows {
            observed_by_key
                .entry(row.key.as_str())
                .or_default()
                .push(row.value.as_str());
        }

        let (duplicate_keys, missing_keys, unexpected_keys, mismatched_value_keys) =
            replay_key_diagnostics(&expected_by_key, &observed_by_key);

        let mut invalid_usize_keys = Vec::new();
        let reconstructed_schema =
            observed_single_value(&observed_by_key, "replay_contract_surface.schema")
                .map(str::to_string);
        let reconstructed_schema_version = observed_usize_value(
            &observed_by_key,
            "replay_contract_surface.schema_version",
            &mut invalid_usize_keys,
        );
        let reconstructed_helper_count = observed_usize_value(
            &observed_by_key,
            "replay_contract_surface.helper_count",
            &mut invalid_usize_keys,
        );
        let reconstructed_schema_count = observed_usize_value(
            &observed_by_key,
            "replay_contract_surface.schema_count",
            &mut invalid_usize_keys,
        );
        let reconstructed_fixture_count = observed_usize_value(
            &observed_by_key,
            "replay_contract_surface.fixture_count",
            &mut invalid_usize_keys,
        );
        let reconstructed_validator_count = observed_usize_value(
            &observed_by_key,
            "replay_contract_surface.validator_count",
            &mut invalid_usize_keys,
        );

        let reconstructed_helper_names = reconstructed_indexed_string_values(
            &observed_by_key,
            "replay_contract_surface.helper",
            "name",
            reconstructed_helper_count.unwrap_or(0),
        );
        let reconstructed_schema_names = reconstructed_indexed_string_values(
            &observed_by_key,
            "replay_contract_surface.schema",
            "name",
            reconstructed_schema_count.unwrap_or(0),
        );
        let reconstructed_schema_values = reconstructed_indexed_string_values(
            &observed_by_key,
            "replay_contract_surface.schema",
            "value",
            reconstructed_schema_count.unwrap_or(0),
        );
        let reconstructed_fixture_names = reconstructed_indexed_string_values(
            &observed_by_key,
            "replay_contract_surface.fixture",
            "name",
            reconstructed_fixture_count.unwrap_or(0),
        );
        let reconstructed_validator_names = reconstructed_indexed_string_values(
            &observed_by_key,
            "replay_contract_surface.validator",
            "name",
            reconstructed_validator_count.unwrap_or(0),
        );

        let schema_header_matches = reconstructed_schema.as_deref() == Some(self.schema)
            && reconstructed_schema_version == Some(self.schema_version as usize);
        let schema_name_value_rows_agree =
            string_values_match_static(&reconstructed_schema_names, self.schema_names)
                && string_values_match_static(&reconstructed_schema_values, self.schema_values);
        let helper_names_match =
            string_values_match_static(&reconstructed_helper_names, self.helper_names);
        let fixture_count_matches = reconstructed_fixture_count == Some(self.fixture_names.len());
        let fixture_names_match =
            string_values_match_static(&reconstructed_fixture_names, self.fixture_names);
        let validator_names_match =
            string_values_match_static(&reconstructed_validator_names, self.validator_names);

        let status = if rows.len() == expected_rows.len()
            && duplicate_keys.is_empty()
            && missing_keys.is_empty()
            && unexpected_keys.is_empty()
            && mismatched_value_keys.is_empty()
            && invalid_usize_keys.is_empty()
            && invalid_lines.is_empty()
            && schema_header_matches
            && schema_name_value_rows_agree
            && helper_names_match
            && fixture_count_matches
            && fixture_names_match
            && validator_names_match
        {
            PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripStatus::Valid
        } else {
            PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripStatus::Invalid
        };

        PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport {
            status,
            status_code: status.code(),
            fail_closed: !matches!(
                status,
                PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripStatus::Valid
            ),
            expected_row_count: expected_rows.len(),
            observed_row_count: rows.len(),
            unique_key_count: observed_by_key.len(),
            duplicate_keys,
            missing_keys,
            unexpected_keys,
            mismatched_value_keys,
            invalid_usize_keys,
            invalid_lines,
            reconstructed_schema,
            reconstructed_schema_version,
            reconstructed_helper_names,
            reconstructed_schema_names,
            reconstructed_schema_values,
            reconstructed_fixture_count,
            reconstructed_fixture_names,
            reconstructed_validator_names,
            schema_header_matches,
            schema_name_value_rows_agree,
            helper_names_match,
            fixture_count_matches,
            fixture_names_match,
            validator_names_match,
        }
    }
}

impl PetriNativeVerificationBundleHandoffDescriptor {
    /// Emit stable key/value rows for Petri native bundle handoff consumers.
    ///
    /// Rows intentionally compose existing TrustIr descriptors instead of asking
    /// TY to parse prose or rebuild schema vocabularies locally.
    pub fn manifest_rows(self) -> Vec<NativeSharedPrimitiveContractManifestRow> {
        let mut rows = Vec::new();
        push_manifest_row(&mut rows, "handoff.schema", self.schema);
        push_manifest_row(
            &mut rows,
            "handoff.schema_version",
            self.schema_version.to_string(),
        );
        push_manifest_row(&mut rows, "source.package", self.source_package);
        push_manifest_row(
            &mut rows,
            "source.package_version",
            self.source_package_version,
        );
        push_manifest_row(
            &mut rows,
            "bundle_identity.schema",
            self.bundle_identity_contract.schema,
        );
        push_manifest_row(
            &mut rows,
            "bundle_identity.schema_version",
            self.bundle_identity_contract.schema_version.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "bundle_identity.bundle_schema_version",
            self.bundle_identity_contract
                .bundle_schema_version
                .to_string(),
        );
        push_manifest_row(
            &mut rows,
            "bundle_identity.transport_identity.schema",
            self.bundle_identity_contract.transport_identity_schema,
        );
        push_manifest_row(
            &mut rows,
            "bundle_identity.transport_identity.schema_version",
            self.bundle_identity_contract
                .transport_identity_schema_version
                .to_string(),
        );
        push_manifest_row(
            &mut rows,
            "bundle_identity.expected_field_count",
            self.expected_bundle_identity_fields.len().to_string(),
        );
        for (index, field) in self.expected_bundle_identity_fields.iter().enumerate() {
            push_manifest_row(
                &mut rows,
                format!("bundle_identity.expected_field.{index}"),
                *field,
            );
        }

        push_manifest_row(
            &mut rows,
            "artifact_authority.schema",
            self.artifact_authority_row_descriptor.schema,
        );
        push_manifest_row(
            &mut rows,
            "artifact_authority.schema_version",
            self.artifact_authority_row_descriptor
                .schema_version
                .to_string(),
        );
        push_manifest_row(
            &mut rows,
            "artifact_authority.report_key_count",
            self.artifact_authority_row_descriptor
                .report_row_keys
                .len()
                .to_string(),
        );
        for (index, key) in self
            .artifact_authority_row_descriptor
            .report_row_keys
            .iter()
            .enumerate()
        {
            push_manifest_row(
                &mut rows,
                format!("artifact_authority.report_key.{index}"),
                *key,
            );
        }
        push_manifest_row(
            &mut rows,
            "artifact_authority.resolution_key_count",
            self.artifact_authority_row_descriptor
                .resolution_row_keys
                .len()
                .to_string(),
        );
        for (index, key) in self
            .artifact_authority_row_descriptor
            .resolution_row_keys
            .iter()
            .enumerate()
        {
            push_manifest_row(
                &mut rows,
                format!("artifact_authority.resolution_key.{index}"),
                *key,
            );
        }

        for row in self.shared_primitive_contract.manifest_rows() {
            push_manifest_row(
                &mut rows,
                format!("shared_primitive_contract.{}", row.key),
                row.value,
            );
        }

        push_manifest_row(
            &mut rows,
            "solver_evidence.owner_suite",
            self.solver_evidence_descriptor.owner_suite.code(),
        );
        push_manifest_row(
            &mut rows,
            "solver_evidence.capability_descriptor.schema",
            self.solver_evidence_descriptor
                .solver_capability_descriptor_schema,
        );
        push_manifest_row(
            &mut rows,
            "solver_evidence.capability_descriptor.schema_version",
            self.solver_evidence_descriptor
                .solver_capability_descriptor_schema_version
                .to_string(),
        );
        push_manifest_row(
            &mut rows,
            "solver_evidence.model_blocking_clause.schema",
            self.solver_evidence_descriptor.model_blocking_clause_schema,
        );
        push_manifest_row(
            &mut rows,
            "solver_evidence.model_blocking_clause.schema_version",
            self.solver_evidence_descriptor
                .model_blocking_clause_schema_version
                .to_string(),
        );
        push_manifest_row(
            &mut rows,
            "solver_evidence.model_blocking_clause_evidence.schema",
            self.solver_evidence_descriptor
                .model_blocking_clause_evidence_schema,
        );
        push_manifest_row(
            &mut rows,
            "solver_evidence.model_blocking_clause_evidence.schema_version",
            self.solver_evidence_descriptor
                .model_blocking_clause_evidence_schema_version
                .to_string(),
        );
        push_manifest_row(
            &mut rows,
            "solver_evidence.solve_decision_profile_model_consumer.schema",
            self.solver_evidence_descriptor
                .solve_decision_profile_model_consumer_schema,
        );
        push_manifest_row(
            &mut rows,
            "solver_evidence.solve_decision_profile_model_consumer.schema_version",
            self.solver_evidence_descriptor
                .solve_decision_profile_model_consumer_schema_version
                .to_string(),
        );
        push_manifest_row(
            &mut rows,
            "solver_evidence.acceptance_report_api",
            self.solver_evidence_descriptor.acceptance_report_api_name,
        );
        push_manifest_row(
            &mut rows,
            "solver_evidence.consumer_acceptance_api",
            self.solver_evidence_descriptor.consumer_acceptance_api_name,
        );

        push_manifest_row(
            &mut rows,
            "downstream.consumer_responsibility_count",
            self.downstream_consumer_responsibilities.len().to_string(),
        );
        for (index, responsibility) in self.downstream_consumer_responsibilities.iter().enumerate()
        {
            push_manifest_row(
                &mut rows,
                format!("downstream.consumer_responsibility.{index}"),
                *responsibility,
            );
        }

        rows
    }

    /// Emit stable escaped `key=value` manifest lines for Petri handoff consumers.
    pub fn manifest_key_value_lines(self) -> Vec<String> {
        self.manifest_rows()
            .into_iter()
            .map(|row| row.to_key_value_line())
            .collect()
    }

    /// Deterministic required-row list for normalized Petri handoff sidecars.
    pub fn required_normalized_rows(self) -> Vec<PetriNativeVerificationBundleHandoffRequiredRow> {
        let mut seen =
            BTreeMap::<(PetriNativeVerificationBundleHandoffRowKind, String), usize>::new();
        self.normalized_rows()
            .into_iter()
            .map(|row| {
                let key = (row.row_kind, row.key.clone());
                let ordinal = seen.get(&key).copied().unwrap_or(0);
                seen.insert(key, ordinal + 1);
                PetriNativeVerificationBundleHandoffRequiredRow::new(row.row_kind, row.key, ordinal)
            })
            .collect()
    }

    /// Validate normalized rows against the deterministic required row list.
    ///
    /// The check is intentionally structural: it requires the expected row kind,
    /// key, and occurrence ordinal to be present, but it leaves solver result
    /// interpretation and artifact acceptance to the owning descriptors.
    pub fn validate_normalized_rows(
        self,
        rows: &[PetriNativeVerificationBundleHandoffRow],
    ) -> PetriNativeVerificationBundleHandoffCompletenessReport {
        let required_rows = self.required_normalized_rows();
        let mut observed_counts =
            BTreeMap::<(PetriNativeVerificationBundleHandoffRowKind, String), usize>::new();
        for row in rows {
            let key = (row.row_kind, row.key.clone());
            let count = observed_counts.get(&key).copied().unwrap_or(0);
            observed_counts.insert(key, count + 1);
        }

        let mut missing_rows = Vec::new();
        let mut present_required_row_count = 0;
        for required in &required_rows {
            let count = observed_counts
                .get(&(required.row_kind, required.key.clone()))
                .copied()
                .unwrap_or(0);
            if count > required.ordinal {
                present_required_row_count += 1;
            } else {
                missing_rows.push(required.clone());
            }
        }

        let mut missing_row_kinds = Vec::new();
        for missing in &missing_rows {
            if !missing_row_kinds.contains(&missing.row_kind) {
                missing_row_kinds.push(missing.row_kind);
            }
        }

        let status = if missing_rows.is_empty() {
            PetriNativeVerificationBundleHandoffCompletenessStatus::Complete
        } else {
            PetriNativeVerificationBundleHandoffCompletenessStatus::Incomplete
        };

        PetriNativeVerificationBundleHandoffCompletenessReport {
            status,
            status_code: status.code(),
            required_row_count: required_rows.len(),
            present_required_row_count,
            required_rows,
            missing_rows,
            missing_row_kinds,
        }
    }

    /// Emit normalized rows with explicit row kinds for direct sidecar generation.
    ///
    /// The row order matches [`Self::manifest_rows`] exactly. Consumers that need
    /// categorical rows should use `row_kind_code` instead of inferring sections
    /// from key prefixes.
    pub fn normalized_rows(self) -> Vec<PetriNativeVerificationBundleHandoffRow> {
        self.manifest_rows()
            .into_iter()
            .map(|row| {
                let row_kind = petri_native_handoff_row_kind_for_key(&row.key);
                PetriNativeVerificationBundleHandoffRow::new(row_kind, row.key, row.value)
            })
            .collect()
    }

    /// Emit stable line-oriented normalized rows for sidecar snapshots.
    pub fn normalized_key_value_lines(self) -> Vec<String> {
        self.normalized_rows()
            .into_iter()
            .map(|row| row.to_normalized_line())
            .collect()
    }

    /// Canonical manifest identity for this descriptor's full normalized row set.
    pub fn manifest_identity(self) -> PetriNativeVerificationBundleHandoffManifestIdentity {
        let rows = self.normalized_rows();
        self.manifest_identity_for_rows(&rows)
    }

    /// Canonical manifest identity for an observed normalized row set.
    ///
    /// This is intended for replay/sidecar consumers: missing required rows are
    /// represented in both the completeness status and the canonical text that
    /// feeds the stable digest.
    pub fn manifest_identity_for_rows(
        self,
        rows: &[PetriNativeVerificationBundleHandoffRow],
    ) -> PetriNativeVerificationBundleHandoffManifestIdentity {
        let report = self.validate_normalized_rows(rows);
        let (canonical_text, extra_row_count) =
            petri_native_handoff_canonical_manifest_text(self, rows, &report);
        let digest = ProofDigest::sha256_domain(
            PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_DIGEST_CONTEXT,
            canonical_text.as_bytes(),
        );

        PetriNativeVerificationBundleHandoffManifestIdentity {
            schema: PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_SCHEMA,
            schema_version:
                PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_SCHEMA_VERSION,
            descriptor_schema: self.schema,
            descriptor_schema_version: self.schema_version,
            source_package: self.source_package,
            source_package_version: self.source_package_version,
            digest_context:
                PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_DIGEST_CONTEXT,
            digest_algorithm: digest.algorithm,
            digest,
            canonical_text,
            completeness_status: report.status,
            completeness_status_code: report.status_code,
            observed_row_count: rows.len(),
            required_row_count: report.required_row_count,
            present_required_row_count: report.present_required_row_count,
            missing_row_count: report.missing_rows.len(),
            missing_rows: report.missing_rows,
            missing_row_kinds: report.missing_row_kinds,
            extra_row_count,
        }
    }

    /// Canonical manifest text for this descriptor's full normalized row set.
    pub fn canonical_manifest_text(self) -> String {
        self.manifest_identity().canonical_text
    }

    /// Canonical manifest text for an observed normalized row set.
    pub fn canonical_manifest_text_for_rows(
        self,
        rows: &[PetriNativeVerificationBundleHandoffRow],
    ) -> String {
        self.manifest_identity_for_rows(rows).canonical_text
    }

    /// Self-audit the default handoff descriptor surface.
    pub fn contract_health_report(
        self,
    ) -> PetriNativeVerificationBundleHandoffContractHealthReport {
        let normalized_rows = self.normalized_rows();
        self.contract_health_report_for_rows(&normalized_rows)
    }

    /// Self-audit an observed normalized handoff row set against this descriptor.
    pub fn contract_health_report_for_rows(
        self,
        normalized_rows: &[PetriNativeVerificationBundleHandoffRow],
    ) -> PetriNativeVerificationBundleHandoffContractHealthReport {
        let manifest_rows = self.manifest_rows();
        let required_rows = self.required_normalized_rows();
        let completeness_report = self.validate_normalized_rows(normalized_rows);
        let manifest_identity = self.manifest_identity_for_rows(normalized_rows);
        let manifest_identity_key_value_rows = manifest_identity.key_value_rows();
        let manifest_identity_key_value_lines = manifest_identity.key_value_lines();
        let manifest_identity_key_value_text = manifest_identity.key_value_text();
        let manifest_identity_key_value_text_line_count =
            manifest_identity_key_value_text.lines().count();

        let descriptor_schema_version = self.schema_version.to_string();
        let manifest_identity_schema_version = manifest_identity.schema_version.to_string();
        let manifest_identity_descriptor_schema_version =
            manifest_identity.descriptor_schema_version.to_string();
        let manifest_identity_digest = manifest_identity.digest.to_string();
        let observed_row_count = manifest_identity.observed_row_count.to_string();
        let required_row_count = manifest_identity.required_row_count.to_string();
        let present_required_row_count = manifest_identity.present_required_row_count.to_string();
        let missing_row_count = manifest_identity.missing_row_count.to_string();
        let extra_row_count = manifest_identity.extra_row_count.to_string();
        let manifest_identity_digest_agrees = manifest_identity.digest
            == ProofDigest::sha256_domain(
                PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_DIGEST_CONTEXT,
                manifest_identity.canonical_text.as_bytes(),
            );

        let schema_version_rows_agree = manifest_row_value(&manifest_rows, "handoff.schema")
            == Some(self.schema)
            && manifest_row_value(&manifest_rows, "handoff.schema_version")
                == Some(descriptor_schema_version.as_str())
            && manifest_row_value(
                &manifest_identity_key_value_rows,
                "manifest_identity.schema",
            ) == Some(manifest_identity.schema)
            && manifest_row_value(
                &manifest_identity_key_value_rows,
                "manifest_identity.schema_version",
            ) == Some(manifest_identity_schema_version.as_str())
            && manifest_row_value(
                &manifest_identity_key_value_rows,
                "manifest_identity.descriptor.schema",
            ) == Some(self.schema)
            && manifest_row_value(
                &manifest_identity_key_value_rows,
                "manifest_identity.descriptor.schema_version",
            ) == Some(manifest_identity_descriptor_schema_version.as_str());

        let row_counts_agree = manifest_rows.len() == normalized_rows.len()
            && normalized_rows.len() == required_rows.len()
            && required_rows.len() == completeness_report.required_row_count
            && completeness_report.required_row_count
                == completeness_report.present_required_row_count
            && manifest_identity.observed_row_count == normalized_rows.len()
            && manifest_identity.required_row_count == required_rows.len()
            && manifest_identity.present_required_row_count == required_rows.len()
            && manifest_identity.missing_row_count == 0
            && manifest_identity.extra_row_count == 0;

        let completeness_agrees = completeness_report.is_complete()
            && !completeness_report.fail_closed()
            && manifest_identity.is_complete()
            && !manifest_identity.fail_closed()
            && completeness_report.status_code == manifest_identity.completeness_status_code
            && completeness_report.missing_rows.is_empty()
            && completeness_report.missing_row_kinds.is_empty()
            && manifest_identity.missing_rows.is_empty()
            && manifest_identity.missing_row_kinds.is_empty();

        let expected_identity_key_value_lines = manifest_identity_key_value_rows
            .iter()
            .map(|row| row.to_key_value_line())
            .collect::<Vec<_>>();
        let expected_identity_key_value_text =
            format!("{}\n", expected_identity_key_value_lines.join("\n"));
        let manifest_identity_key_values_agree = manifest_identity_key_value_lines
            == expected_identity_key_value_lines
            && manifest_identity_key_value_text == expected_identity_key_value_text
            && manifest_identity_key_value_text_line_count
                == manifest_identity_key_value_lines.len()
            && manifest_row_value(
                &manifest_identity_key_value_rows,
                "manifest_identity.digest",
            ) == Some(manifest_identity_digest.as_str())
            && manifest_row_value(
                &manifest_identity_key_value_rows,
                "manifest_identity.completeness.status",
            ) == Some(manifest_identity.completeness_status_code)
            && manifest_row_value(
                &manifest_identity_key_value_rows,
                "manifest_identity.fail_closed",
            ) == Some(bool_code(manifest_identity.fail_closed()))
            && manifest_row_value(
                &manifest_identity_key_value_rows,
                "manifest_identity.rows.observed_count",
            ) == Some(observed_row_count.as_str())
            && manifest_row_value(
                &manifest_identity_key_value_rows,
                "manifest_identity.rows.required_count",
            ) == Some(required_row_count.as_str())
            && manifest_row_value(
                &manifest_identity_key_value_rows,
                "manifest_identity.rows.present_required_count",
            ) == Some(present_required_row_count.as_str())
            && manifest_row_value(
                &manifest_identity_key_value_rows,
                "manifest_identity.rows.missing_count",
            ) == Some(missing_row_count.as_str())
            && manifest_row_value(
                &manifest_identity_key_value_rows,
                "manifest_identity.rows.extra_count",
            ) == Some(extra_row_count.as_str());

        let status = if schema_version_rows_agree
            && row_counts_agree
            && completeness_agrees
            && manifest_identity_digest_agrees
            && manifest_identity_key_values_agree
        {
            PetriNativeVerificationBundleHandoffContractHealthStatus::Healthy
        } else {
            PetriNativeVerificationBundleHandoffContractHealthStatus::Inconsistent
        };

        PetriNativeVerificationBundleHandoffContractHealthReport {
            status,
            status_code: status.code(),
            descriptor_schema: self.schema,
            descriptor_schema_version: self.schema_version,
            manifest_identity_schema: manifest_identity.schema,
            manifest_identity_schema_version: manifest_identity.schema_version,
            manifest_row_count: manifest_rows.len(),
            normalized_row_count: normalized_rows.len(),
            required_row_count: required_rows.len(),
            completeness_required_row_count: completeness_report.required_row_count,
            completeness_present_required_row_count: completeness_report.present_required_row_count,
            completeness_missing_row_count: completeness_report.missing_rows.len(),
            manifest_identity_observed_row_count: manifest_identity.observed_row_count,
            manifest_identity_required_row_count: manifest_identity.required_row_count,
            manifest_identity_present_required_row_count: manifest_identity
                .present_required_row_count,
            manifest_identity_missing_row_count: manifest_identity.missing_row_count,
            manifest_identity_extra_row_count: manifest_identity.extra_row_count,
            manifest_identity_key_value_row_count: manifest_identity_key_value_rows.len(),
            manifest_identity_key_value_line_count: manifest_identity_key_value_lines.len(),
            manifest_identity_key_value_text_line_count,
            manifest_identity_digest: manifest_identity.digest,
            schema_version_rows_agree,
            row_counts_agree,
            completeness_agrees,
            manifest_identity_digest_agrees,
            manifest_identity_key_values_agree,
        }
    }
}

pub(crate) fn manifest_row_value<'a>(
    rows: &'a [NativeSharedPrimitiveContractManifestRow],
    key: &str,
) -> Option<&'a str> {
    rows.iter()
        .find(|row| row.key == key)
        .map(|row| row.value.as_str())
}

#[derive(Debug)]
pub(crate) struct PetriNativeHandoffObservedRow<'a> {
    row_kind: PetriNativeVerificationBundleHandoffRowKind,
    row_kind_code: &'static str,
    key: &'a str,
    value: &'a str,
    ordinal: usize,
}

pub(crate) fn petri_native_handoff_canonical_manifest_text(
    descriptor: PetriNativeVerificationBundleHandoffDescriptor,
    rows: &[PetriNativeVerificationBundleHandoffRow],
    report: &PetriNativeVerificationBundleHandoffCompletenessReport,
) -> (String, usize) {
    let mut lines = Vec::new();
    push_manifest_identity_line(
        &mut lines,
        "identity.schema",
        PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_SCHEMA,
    );
    push_manifest_identity_line(
        &mut lines,
        "identity.schema_version",
        PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_SCHEMA_VERSION.to_string(),
    );
    push_manifest_identity_line(
        &mut lines,
        "identity.digest_context",
        PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_DIGEST_CONTEXT,
    );
    push_manifest_identity_line(&mut lines, "descriptor.schema", descriptor.schema);
    push_manifest_identity_line(
        &mut lines,
        "descriptor.schema_version",
        descriptor.schema_version.to_string(),
    );
    push_manifest_identity_line(&mut lines, "source.package", descriptor.source_package);
    push_manifest_identity_line(
        &mut lines,
        "source.package_version",
        descriptor.source_package_version,
    );
    push_manifest_identity_line(&mut lines, "completeness.status", report.status_code);
    push_manifest_identity_line(&mut lines, "rows.observed_count", rows.len().to_string());
    push_manifest_identity_line(
        &mut lines,
        "rows.required_count",
        report.required_row_count.to_string(),
    );
    push_manifest_identity_line(
        &mut lines,
        "rows.present_required_count",
        report.present_required_row_count.to_string(),
    );
    push_manifest_identity_line(
        &mut lines,
        "rows.missing_count",
        report.missing_rows.len().to_string(),
    );

    for (index, required) in report.required_rows.iter().enumerate() {
        push_manifest_identity_line(
            &mut lines,
            format!("required.{index}.row_kind"),
            required.row_kind_code,
        );
        push_manifest_identity_line(&mut lines, format!("required.{index}.key"), &required.key);
        push_manifest_identity_line(
            &mut lines,
            format!("required.{index}.ordinal"),
            required.ordinal.to_string(),
        );
    }

    for (index, missing) in report.missing_rows.iter().enumerate() {
        push_manifest_identity_line(
            &mut lines,
            format!("missing.{index}.row_kind"),
            missing.row_kind_code,
        );
        push_manifest_identity_line(&mut lines, format!("missing.{index}.key"), &missing.key);
        push_manifest_identity_line(
            &mut lines,
            format!("missing.{index}.ordinal"),
            missing.ordinal.to_string(),
        );
    }

    let canonical_rows_source = descriptor.normalized_rows();
    let canonical_rows = petri_native_handoff_observed_rows_with_ordinals(&canonical_rows_source);
    let observed_rows = petri_native_handoff_observed_rows_with_ordinals(rows);
    let mut used_observed_rows = BTreeSet::new();
    let mut observed_index = 0;

    for canonical_row in &canonical_rows {
        if let Some((observed_position, _)) =
            observed_rows
                .iter()
                .enumerate()
                .find(|(position, observed_row)| {
                    !used_observed_rows.contains(position)
                        && observed_row.row_kind == canonical_row.row_kind
                        && observed_row.key == canonical_row.key
                        && observed_row.value == canonical_row.value
                })
        {
            push_manifest_identity_observed_row(&mut lines, "row", observed_index, canonical_row);
            observed_index += 1;
            used_observed_rows.insert(observed_position);
        }
    }

    let mut extra_rows = observed_rows
        .iter()
        .enumerate()
        .filter(|(position, _)| !used_observed_rows.contains(position))
        .map(|(_, row)| row)
        .collect::<Vec<_>>();
    extra_rows.sort_by(|left, right| {
        left.row_kind_code
            .cmp(right.row_kind_code)
            .then_with(|| left.key.cmp(right.key))
            .then_with(|| left.ordinal.cmp(&right.ordinal))
            .then_with(|| left.value.cmp(right.value))
    });

    push_manifest_identity_line(&mut lines, "rows.extra_count", extra_rows.len().to_string());
    for (index, row) in extra_rows.iter().enumerate() {
        push_manifest_identity_observed_row(&mut lines, "extra_row", index, row);
    }

    (format!("{}\n", lines.join("\n")), extra_rows.len())
}

pub(crate) fn petri_native_handoff_observed_rows_with_ordinals(
    rows: &[PetriNativeVerificationBundleHandoffRow],
) -> Vec<PetriNativeHandoffObservedRow<'_>> {
    let mut observed_counts =
        BTreeMap::<(PetriNativeVerificationBundleHandoffRowKind, String), usize>::new();
    rows.iter()
        .map(|row| {
            let key = (row.row_kind, row.key.clone());
            let ordinal = observed_counts.get(&key).copied().unwrap_or(0);
            observed_counts.insert(key, ordinal + 1);
            PetriNativeHandoffObservedRow {
                row_kind: row.row_kind,
                row_kind_code: row.row_kind_code,
                key: &row.key,
                value: &row.value,
                ordinal,
            }
        })
        .collect()
}

pub(crate) fn push_manifest_identity_observed_row(
    lines: &mut Vec<String>,
    prefix: &str,
    index: usize,
    row: &PetriNativeHandoffObservedRow<'_>,
) {
    push_manifest_identity_line(
        lines,
        format!("{prefix}.{index}.row_kind"),
        row.row_kind_code,
    );
    push_manifest_identity_line(lines, format!("{prefix}.{index}.key"), row.key);
    push_manifest_identity_line(
        lines,
        format!("{prefix}.{index}.ordinal"),
        row.ordinal.to_string(),
    );
    push_manifest_identity_line(lines, format!("{prefix}.{index}.value"), row.value);
}

pub(crate) fn push_manifest_identity_line(
    lines: &mut Vec<String>,
    key: impl AsRef<str>,
    value: impl AsRef<str>,
) {
    lines.push(format!(
        "{}={}",
        escape_manifest_component(key.as_ref()),
        escape_manifest_component(value.as_ref())
    ));
}

pub(crate) fn push_replay_contract_report_diagnostic_lines(
    lines: &mut Vec<String>,
    diagnostic_name: &str,
    values: &[String],
) {
    push_manifest_identity_line(
        lines,
        format!("round_trip_report.diagnostic.{diagnostic_name}.count"),
        values.len().to_string(),
    );
    for (index, value) in values.iter().enumerate() {
        push_manifest_identity_line(
            lines,
            format!("round_trip_report.diagnostic.{diagnostic_name}.{index}"),
            value,
        );
    }
}

pub(crate) fn petri_native_handoff_row_kind_for_key(
    key: &str,
) -> PetriNativeVerificationBundleHandoffRowKind {
    if key.starts_with("handoff.") {
        PetriNativeVerificationBundleHandoffRowKind::Descriptor
    } else if key.starts_with("source.") {
        PetriNativeVerificationBundleHandoffRowKind::Source
    } else if key.starts_with("bundle_identity.") {
        PetriNativeVerificationBundleHandoffRowKind::BundleIdentity
    } else if key.starts_with("artifact_authority.") {
        PetriNativeVerificationBundleHandoffRowKind::ArtifactAuthority
    } else if key.starts_with("shared_primitive_contract.") {
        PetriNativeVerificationBundleHandoffRowKind::SharedPrimitiveContract
    } else if key.starts_with("solver_evidence.") {
        PetriNativeVerificationBundleHandoffRowKind::SolverEvidence
    } else if key.starts_with("downstream.") {
        PetriNativeVerificationBundleHandoffRowKind::DownstreamResponsibility
    } else {
        PetriNativeVerificationBundleHandoffRowKind::Other
    }
}

pub(crate) fn push_manifest_row(
    rows: &mut Vec<NativeSharedPrimitiveContractManifestRow>,
    key: impl Into<String>,
    value: impl Into<String>,
) {
    rows.push(NativeSharedPrimitiveContractManifestRow::new(key, value));
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn push_ty_shared_primitive_component_rows(
    rows: &mut Vec<NativeSharedPrimitiveContractManifestRow>,
    index: usize,
    name: &str,
    row_source: &str,
    row_family: &str,
    schema: &str,
    schema_version: u32,
    rows_api: &str,
    key_value_lines_api: &str,
    key_value_text_api: &str,
    replay_report_api: &str,
    compact_health_summary_rows_api: &str,
    compact_health_summary_key_value_lines_api: &str,
    component_health_summary_rows_api: &str,
    component_health_summary_key_value_lines_api: &str,
    static_contract_count: Option<usize>,
) {
    let prefix = format!("ty_shared_primitive_manifest.component.{index}");
    push_manifest_row(rows, format!("{prefix}.name"), name);
    push_manifest_row(rows, format!("{prefix}.row_source"), row_source);
    push_manifest_row(rows, format!("{prefix}.row_family"), row_family);
    push_manifest_row(rows, format!("{prefix}.schema"), schema);
    push_manifest_row(
        rows,
        format!("{prefix}.schema_version"),
        schema_version.to_string(),
    );
    push_manifest_row(
        rows,
        format!("{prefix}.producer_rows_ready"),
        bool_code(true),
    );
    push_manifest_row(
        rows,
        format!("{prefix}.downstream_row_synthesis_required"),
        bool_code(false),
    );
    push_manifest_row(rows, format!("{prefix}.status"), "available");
    push_manifest_row(
        rows,
        format!("{prefix}.reason"),
        "producer_owned_rows_available",
    );
    push_manifest_row(rows, format!("{prefix}.fail_closed"), bool_code(false));
    push_manifest_row(rows, format!("{prefix}.rows_api"), rows_api);
    push_manifest_row(
        rows,
        format!("{prefix}.key_value_lines_api"),
        key_value_lines_api,
    );
    push_manifest_row(
        rows,
        format!("{prefix}.key_value_text_api"),
        key_value_text_api,
    );
    push_manifest_row(
        rows,
        format!("{prefix}.replay_report_api"),
        replay_report_api,
    );
    push_manifest_row(
        rows,
        format!("{prefix}.compact_health_summary_rows_api"),
        compact_health_summary_rows_api,
    );
    push_manifest_row(
        rows,
        format!("{prefix}.compact_health_summary_key_value_lines_api"),
        compact_health_summary_key_value_lines_api,
    );
    push_manifest_row(
        rows,
        format!("{prefix}.component_health_summary_rows_api"),
        component_health_summary_rows_api,
    );
    push_manifest_row(
        rows,
        format!("{prefix}.component_health_summary_key_value_lines_api"),
        component_health_summary_key_value_lines_api,
    );
    if let Some(static_contract_count) = static_contract_count {
        push_manifest_row(
            rows,
            format!("{prefix}.static_contract_count"),
            static_contract_count.to_string(),
        );
    }
}

pub(crate) fn push_replay_component_health_summary_rows(
    rows: &mut Vec<NativeSharedPrimitiveContractManifestRow>,
    prefix: &str,
    component: &str,
    value: impl Into<String>,
    matches_expected: bool,
) {
    push_manifest_row(rows, format!("{prefix}.component.{component}.value"), value);
    push_manifest_row(
        rows,
        format!("{prefix}.component.{component}.matches"),
        bool_code(matches_expected),
    );
}

pub(crate) fn push_optional_u32_manifest_row(
    rows: &mut Vec<NativeSharedPrimitiveContractManifestRow>,
    key: impl Into<String>,
    value: Option<u32>,
) {
    push_manifest_row(
        rows,
        key,
        value
            .map(|value| value.to_string())
            .unwrap_or_else(|| "none".to_string()),
    );
}

pub(crate) fn push_optional_digest_manifest_row(
    rows: &mut Vec<NativeSharedPrimitiveContractManifestRow>,
    key: impl Into<String>,
    value: Option<ProofDigest>,
) {
    push_manifest_row(
        rows,
        key,
        value
            .map(|digest| digest.to_string())
            .unwrap_or_else(|| "none".to_string()),
    );
}

pub(crate) fn push_optional_artifact_manifest_rows(
    rows: &mut Vec<NativeSharedPrimitiveContractManifestRow>,
    prefix: &str,
    artifact: Option<&NativeEvidenceArtifact>,
) {
    push_manifest_row(
        rows,
        format!("{prefix}.present"),
        bool_code(artifact.is_some()),
    );
    push_manifest_row(
        rows,
        format!("{prefix}.name"),
        artifact
            .map(|artifact| artifact.name.as_str())
            .unwrap_or("none"),
    );
    push_manifest_row(
        rows,
        format!("{prefix}.kind"),
        artifact
            .map(|artifact| artifact.kind.code())
            .unwrap_or("none"),
    );
    push_optional_digest_manifest_row(
        rows,
        format!("{prefix}.digest"),
        artifact.map(|artifact| artifact.digest),
    );
}

pub(crate) fn push_artifact_authority_row(
    rows: &mut Vec<NativeEvidenceArtifactAuthorityRow>,
    key: impl Into<String>,
    value: impl Into<String>,
) {
    rows.push(NativeEvidenceArtifactAuthorityRow::new(key, value));
}

pub(crate) fn artifact_authority_row_keys_match(
    rows: &[NativeEvidenceArtifactAuthorityRow],
    expected_keys: &[&str],
) -> bool {
    rows.len() == expected_keys.len()
        && rows
            .iter()
            .zip(expected_keys.iter())
            .all(|(row, expected_key)| row.key == *expected_key)
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct ObservedArtifactAuthorityRows<'a> {
    digest: &'a str,
    actual_digest: &'a str,
    byte_len: Option<usize>,
    byte_source_identity: &'a str,
    status_resolved: bool,
    authority_authoritative: bool,
    report_is_resolved: bool,
    report_is_authoritative: bool,
    report_fail_closed: bool,
}

pub(crate) fn artifact_authority_row_values(
    rows: &[NativeEvidenceArtifactAuthorityRow],
) -> BTreeMap<&str, &str> {
    rows.iter()
        .map(|row| (row.key.as_str(), row.value.as_str()))
        .collect()
}

pub(crate) fn validate_artifact_authority_common_fields<'a>(
    values: &'a BTreeMap<&'a str, &'a str>,
    rows_kind: Option<NativeEvidenceArtifactAuthorityRowsKind>,
    diagnostics: &mut Vec<String>,
) -> Option<ObservedArtifactAuthorityRows<'a>> {
    require_artifact_authority_value(
        values,
        "artifact_authority.schema",
        NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_ROW_SCHEMA,
        diagnostics,
    );
    require_artifact_authority_u32_value(
        values,
        "artifact_authority.schema_version",
        NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_ROW_SCHEMA_VERSION,
        diagnostics,
    );
    require_artifact_authority_value(
        values,
        "artifact_resolution.schema",
        NATIVE_EVIDENCE_ARTIFACT_RESOLUTION_SCHEMA,
        diagnostics,
    );
    require_artifact_authority_u32_value(
        values,
        "artifact_resolution.schema_version",
        NATIVE_EVIDENCE_ARTIFACT_RESOLUTION_SCHEMA_VERSION,
        diagnostics,
    );
    validate_artifact_authority_u32(values, "request.id", diagnostics);
    validate_artifact_authority_allowed_value(
        values,
        "owner_suite",
        native_verifier_suite_code_is_valid,
        diagnostics,
    );
    validate_artifact_authority_allowed_value(
        values,
        "artifact.kind",
        native_evidence_artifact_kind_code_is_valid,
        diagnostics,
    );
    let digest_algorithm = artifact_authority_value(values, "digest.algorithm", diagnostics)?;
    if !proof_digest_algorithm_code_is_valid(digest_algorithm) {
        diagnostics.push(format!(
            "digest.algorithm has unsupported value `{digest_algorithm}`"
        ));
    }
    let digest = artifact_authority_value(values, "digest", diagnostics)?;
    if !proof_digest_string_matches_algorithm(digest, digest_algorithm) {
        diagnostics.push(format!(
            "digest `{digest}` does not match digest.algorithm `{digest_algorithm}`"
        ));
    }
    let actual_digest = artifact_authority_value(values, "actual_digest", diagnostics)?;
    if actual_digest != "none"
        && !proof_digest_string_matches_algorithm(actual_digest, digest_algorithm)
    {
        diagnostics.push(format!(
            "actual_digest `{actual_digest}` does not match digest.algorithm `{digest_algorithm}`"
        ));
    }

    let byte_source_identity =
        artifact_authority_value(values, "byte.source_identity", diagnostics)?;
    let byte_len = validate_artifact_authority_optional_usize(values, "byte.len", diagnostics);
    let authority = artifact_authority_value(values, "authority", diagnostics)?;
    let status = artifact_authority_value(values, "status", diagnostics)?;
    let reason = artifact_authority_value(values, "reason", diagnostics)?;
    validate_artifact_authority_allowed_value(
        values,
        "authority",
        native_evidence_artifact_authority_code_is_valid,
        diagnostics,
    );
    validate_artifact_authority_allowed_value(
        values,
        "status",
        native_evidence_artifact_resolution_status_code_is_valid,
        diagnostics,
    );
    validate_artifact_authority_allowed_value(
        values,
        "reason",
        native_evidence_artifact_resolution_reason_code_is_valid,
        diagnostics,
    );

    let report_is_resolved =
        validate_artifact_authority_bool(values, "report.is_resolved", diagnostics)?;
    let report_is_authoritative =
        validate_artifact_authority_bool(values, "report.is_authoritative", diagnostics)?;
    let report_fail_closed =
        validate_artifact_authority_bool(values, "report.fail_closed", diagnostics)?;

    let status_resolved = status == NativeEvidenceArtifactResolutionStatus::Resolved.code();
    let authority_authoritative =
        authority == NativeEvidenceArtifactAuthority::Authoritative.code();
    let reason_resolved = reason == NativeEvidenceArtifactResolutionReason::Resolved.code();
    if report_is_resolved != status_resolved {
        diagnostics.push("report.is_resolved disagrees with status".to_string());
    }
    if report_is_authoritative != (status_resolved && authority_authoritative) {
        diagnostics.push("report.is_authoritative disagrees with status/authority".to_string());
    }
    if report_fail_closed == report_is_authoritative {
        diagnostics
            .push("report.fail_closed must be the inverse of report.is_authoritative".to_string());
    }
    if status_resolved {
        if !reason_resolved {
            diagnostics
                .push("resolved artifact authority rows must use reason=resolved".to_string());
        }
        if !authority_authoritative {
            diagnostics.push(
                "resolved artifact authority rows must use authority=authoritative".to_string(),
            );
        }
        if actual_digest != digest {
            diagnostics
                .push("resolved artifact authority rows must set actual_digest=digest".to_string());
        }
        if byte_source_identity == "none" {
            diagnostics.push(
                "resolved artifact authority rows must carry byte.source_identity".to_string(),
            );
        }
        if byte_len.is_none_or(|len| len == 0) {
            diagnostics.push(
                "resolved artifact authority rows must carry a positive byte.len".to_string(),
            );
        }
    } else {
        if reason_resolved {
            diagnostics
                .push("blocked artifact authority rows must not use reason=resolved".to_string());
        }
        if authority_authoritative {
            diagnostics.push(
                "blocked artifact authority rows must not use authority=authoritative".to_string(),
            );
        }
    }

    rows_kind?;

    Some(ObservedArtifactAuthorityRows {
        digest,
        actual_digest,
        byte_len,
        byte_source_identity,
        status_resolved,
        authority_authoritative,
        report_is_resolved,
        report_is_authoritative,
        report_fail_closed,
    })
}

pub(crate) fn validate_artifact_authority_resolution_fields(
    values: &BTreeMap<&str, &str>,
    observed: &ObservedArtifactAuthorityRows<'_>,
    diagnostics: &mut Vec<String>,
) {
    let Some(bytes_present) =
        validate_artifact_authority_bool(values, "resolution.bytes_present", diagnostics)
    else {
        return;
    };
    let Some(resolution_is_resolved) =
        validate_artifact_authority_bool(values, "resolution.is_resolved", diagnostics)
    else {
        return;
    };
    let Some(resolution_is_authoritative) =
        validate_artifact_authority_bool(values, "resolution.is_authoritative", diagnostics)
    else {
        return;
    };
    let Some(resolution_fail_closed) =
        validate_artifact_authority_bool(values, "resolution.fail_closed", diagnostics)
    else {
        return;
    };
    let Some(authoritative_bytes_available) = validate_artifact_authority_bool(
        values,
        "resolution.authoritative_bytes_available",
        diagnostics,
    ) else {
        return;
    };

    let expected_resolved = observed.report_is_resolved && bytes_present;
    let expected_authoritative = observed.report_is_authoritative && bytes_present;
    if resolution_is_resolved != expected_resolved {
        diagnostics.push(
            "resolution.is_resolved disagrees with report.is_resolved/bytes_present".to_string(),
        );
    }
    if resolution_is_authoritative != expected_authoritative {
        diagnostics.push(
            "resolution.is_authoritative disagrees with report.is_authoritative/bytes_present"
                .to_string(),
        );
    }
    if resolution_fail_closed == resolution_is_authoritative {
        diagnostics.push(
            "resolution.fail_closed must be the inverse of resolution.is_authoritative".to_string(),
        );
    }
    if authoritative_bytes_available != resolution_is_authoritative {
        diagnostics.push(
            "resolution.authoritative_bytes_available must match resolution.is_authoritative"
                .to_string(),
        );
    }
    if resolution_is_authoritative {
        if !observed.status_resolved || !observed.authority_authoritative {
            diagnostics.push(
                "authoritative resolution rows require resolved authoritative report rows"
                    .to_string(),
            );
        }
        if observed.actual_digest != observed.digest {
            diagnostics.push(
                "authoritative resolution rows must preserve actual_digest=digest".to_string(),
            );
        }
        if observed.byte_source_identity == "none" || observed.byte_len.is_none_or(|len| len == 0) {
            diagnostics.push(
                "authoritative resolution rows must carry byte identity and positive length"
                    .to_string(),
            );
        }
    }
    if observed.report_fail_closed && resolution_is_authoritative {
        diagnostics.push(
            "fail-closed report rows cannot produce authoritative resolution rows".to_string(),
        );
    }
}

pub(crate) fn require_artifact_authority_value(
    values: &BTreeMap<&str, &str>,
    key: &str,
    expected: &str,
    diagnostics: &mut Vec<String>,
) {
    match values.get(key).copied() {
        Some(value) if value == expected => {}
        Some(value) => diagnostics.push(format!("{key} expected `{expected}`, got `{value}`")),
        None => diagnostics.push(format!("missing required key `{key}`")),
    }
}

pub(crate) fn require_artifact_authority_u32_value(
    values: &BTreeMap<&str, &str>,
    key: &str,
    expected: u32,
    diagnostics: &mut Vec<String>,
) {
    match values
        .get(key)
        .copied()
        .and_then(|value| value.parse::<u32>().ok())
    {
        Some(value) if value == expected => {}
        Some(value) => diagnostics.push(format!("{key} expected `{expected}`, got `{value}`")),
        None => diagnostics.push(format!("{key} is missing or not a u32")),
    }
}

pub(crate) fn artifact_authority_value<'a>(
    values: &'a BTreeMap<&'a str, &'a str>,
    key: &str,
    diagnostics: &mut Vec<String>,
) -> Option<&'a str> {
    match values.get(key).copied() {
        Some(value) => Some(value),
        None => {
            diagnostics.push(format!("missing required key `{key}`"));
            None
        }
    }
}

pub(crate) fn validate_artifact_authority_u32(
    values: &BTreeMap<&str, &str>,
    key: &str,
    diagnostics: &mut Vec<String>,
) -> Option<u32> {
    match values.get(key).copied() {
        Some(value) => match value.parse::<u32>() {
            Ok(parsed) => Some(parsed),
            Err(_) => {
                diagnostics.push(format!("{key} is not a u32: `{value}`"));
                None
            }
        },
        None => {
            diagnostics.push(format!("missing required key `{key}`"));
            None
        }
    }
}

pub(crate) fn validate_artifact_authority_optional_usize(
    values: &BTreeMap<&str, &str>,
    key: &str,
    diagnostics: &mut Vec<String>,
) -> Option<usize> {
    match values.get(key).copied() {
        Some("none") => None,
        Some(value) => match value.parse::<usize>() {
            Ok(parsed) => Some(parsed),
            Err(_) => {
                diagnostics.push(format!("{key} is not `none` or a usize: `{value}`"));
                None
            }
        },
        None => {
            diagnostics.push(format!("missing required key `{key}`"));
            None
        }
    }
}

pub(crate) fn validate_artifact_authority_bool(
    values: &BTreeMap<&str, &str>,
    key: &str,
    diagnostics: &mut Vec<String>,
) -> Option<bool> {
    match values.get(key).copied() {
        Some("true") => Some(true),
        Some("false") => Some(false),
        Some(value) => {
            diagnostics.push(format!("{key} is not a bool: `{value}`"));
            None
        }
        None => {
            diagnostics.push(format!("missing required key `{key}`"));
            None
        }
    }
}

pub(crate) fn validate_artifact_authority_allowed_value(
    values: &BTreeMap<&str, &str>,
    key: &str,
    valid: fn(&str) -> bool,
    diagnostics: &mut Vec<String>,
) {
    if let Some(value) = values.get(key).copied()
        && !valid(value)
    {
        diagnostics.push(format!("{key} has unsupported value `{value}`"));
    }
}

pub(crate) fn proof_digest_algorithm_code_is_valid(value: &str) -> bool {
    matches!(value, "sha256" | "trust_ir-stable-v1")
}

pub(crate) fn proof_digest_string_matches_algorithm(value: &str, algorithm: &str) -> bool {
    let Some((actual_algorithm, hex)) = value.split_once(':') else {
        return false;
    };
    actual_algorithm == algorithm
        && hex.len() == 64
        && hex.bytes().all(|byte| byte.is_ascii_hexdigit())
}

pub(crate) fn native_verifier_suite_code_is_valid(value: &str) -> bool {
    matches!(
        value,
        "none"
            | "unknown"
            | "trust_vc"
            | "trust_mc"
            | "trust_wp"
            | "ay"
            | "trust"
            | "trust-ir"
            | "other"
    )
}

pub(crate) fn native_evidence_artifact_kind_code_is_valid(value: &str) -> bool {
    matches!(
        value,
        "trust_vc_certificate_import"
            | "trust_vc_merged_certificate"
            | "trust_mc_horn_clauses"
            | "trust_mc_pdr_trace"
            | "trust_mc_model"
            | "trust_wp_verification_condition"
            | "trust_wp_replay_trace"
            | "trust_wp_abduced_precondition"
            | "replay_transcript"
            | "other"
            | "btor2_trace"
            | "btor2_proof"
            | "native_compiled_artifact"
            | "backend_capability_metadata"
    )
}

pub(crate) fn native_evidence_artifact_authority_code_is_valid(value: &str) -> bool {
    matches!(value, "informational" | "authoritative")
}

pub(crate) fn native_evidence_artifact_resolution_status_code_is_valid(value: &str) -> bool {
    matches!(value, "resolved" | "blocked")
}

pub(crate) fn native_evidence_artifact_resolution_reason_code_is_valid(value: &str) -> bool {
    matches!(
        value,
        "resolved"
            | "bundle_invalid"
            | "request_unknown"
            | "missing_evidence_bundle"
            | "unsupported_artifact_kind"
            | "missing_artifact_descriptor"
            | "digest_algorithm_mismatch"
            | "digest_mismatch"
            | "missing_attachment"
            | "duplicate_attachment"
            | "owner_suite_mismatch"
            | "invalid_source_identity"
            | "empty_bytes"
    )
}

pub(crate) fn parse_artifact_authority_key_value_line(line: &str) -> Option<(String, String)> {
    let mut key = String::new();
    let mut value = String::new();
    let mut in_value = false;
    let mut escaped = false;
    for ch in line.chars() {
        let target = if in_value { &mut value } else { &mut key };
        if escaped {
            match ch {
                '\\' => target.push('\\'),
                '=' => target.push('='),
                'n' => target.push('\n'),
                'r' => target.push('\r'),
                't' => target.push('\t'),
                other => target.push(other),
            }
            escaped = false;
            continue;
        }
        match ch {
            '\\' => escaped = true,
            '=' if !in_value => in_value = true,
            other => target.push(other),
        }
    }
    if escaped || !in_value {
        return None;
    }
    Some((key, value))
}

pub(crate) fn escape_manifest_component(value: &str) -> String {
    let mut escaped = String::new();
    for ch in value.chars() {
        match ch {
            '\\' => escaped.push_str("\\\\"),
            '=' => escaped.push_str("\\="),
            '\n' => escaped.push_str("\\n"),
            '\r' => escaped.push_str("\\r"),
            '\t' => escaped.push_str("\\t"),
            _ if ch.is_control() => escaped.extend(ch.escape_default()),
            _ => escaped.push(ch),
        }
    }
    escaped
}

pub(crate) fn manifest_key_value_lines_digest(lines: &[String]) -> ProofDigest {
    let mut text = lines.join("\n");
    text.push('\n');
    ProofDigest::sha256(sha256(text.as_bytes()))
}

pub(crate) fn json_string_literal(value: &str) -> String {
    let mut escaped = String::new();
    escaped.push('"');
    for ch in value.chars() {
        match ch {
            '"' => escaped.push_str("\\\""),
            '\\' => escaped.push_str("\\\\"),
            '\n' => escaped.push_str("\\n"),
            '\r' => escaped.push_str("\\r"),
            '\t' => escaped.push_str("\\t"),
            '\u{08}' => escaped.push_str("\\b"),
            '\u{0c}' => escaped.push_str("\\f"),
            _ if ch.is_control() => {
                let _ = write!(escaped, "\\u{:04x}", ch as u32);
            }
            _ => escaped.push(ch),
        }
    }
    escaped.push('"');
    escaped
}

pub(crate) fn sha256(input: &[u8]) -> [u8; 32] {
    sha256_parts(&[input])
}

/// SHA-256 over a logical concatenation without allocating/copying that
/// concatenation. Security identities use this for domain framing so a large
/// proof payload is not duplicated merely to prepend its domain and lengths.
pub(crate) fn sha256_parts(parts: &[&[u8]]) -> [u8; 32] {
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];
    let mut state = [
        0x6a09e667u32,
        0xbb67ae85,
        0x3c6ef372,
        0xa54ff53a,
        0x510e527f,
        0x9b05688c,
        0x1f83d9ab,
        0x5be0cd19,
    ];

    let total_bytes = parts.iter().try_fold(0_u64, |total, part| {
        let part_len = u64::try_from(part.len()).ok()?;
        total.checked_add(part_len)
    });
    let total_bits = total_bytes
        .and_then(|bytes| bytes.checked_mul(8))
        .expect("SHA-256 input exceeds canonical 64-bit bit-length framing");

    let mut block = [0_u8; 64];
    let mut used = 0_usize;
    for mut input in parts.iter().copied() {
        if used != 0 {
            let take = (64 - used).min(input.len());
            block[used..used + take].copy_from_slice(&input[..take]);
            used += take;
            input = &input[take..];
            if used == 64 {
                sha256_compress(&mut state, &block, &K);
                block = [0_u8; 64];
                used = 0;
            }
        }

        while input.len() >= 64 {
            block.copy_from_slice(&input[..64]);
            sha256_compress(&mut state, &block, &K);
            block = [0_u8; 64];
            input = &input[64..];
        }
        if !input.is_empty() {
            block[..input.len()].copy_from_slice(input);
            used = input.len();
        }
    }

    block[used] = 0x80;
    if used >= 56 {
        sha256_compress(&mut state, &block, &K);
        block = [0_u8; 64];
    }
    block[56..64].copy_from_slice(&total_bits.to_be_bytes());
    sha256_compress(&mut state, &block, &K);

    let mut out = [0u8; 32];
    for (index, word) in state.iter().enumerate() {
        out[index * 4..index * 4 + 4].copy_from_slice(&word.to_be_bytes());
    }
    out
}

pub(crate) fn sha256_compress(state: &mut [u32; 8], block: &[u8; 64], constants: &[u32; 64]) {
    let mut words = [0u32; 64];
    for (index, word) in words.iter_mut().take(16).enumerate() {
        let offset = index * 4;
        *word = u32::from_be_bytes([
            block[offset],
            block[offset + 1],
            block[offset + 2],
            block[offset + 3],
        ]);
    }
    for index in 16..64 {
        let s0 = words[index - 15].rotate_right(7)
            ^ words[index - 15].rotate_right(18)
            ^ (words[index - 15] >> 3);
        let s1 = words[index - 2].rotate_right(17)
            ^ words[index - 2].rotate_right(19)
            ^ (words[index - 2] >> 10);
        words[index] = words[index - 16]
            .wrapping_add(s0)
            .wrapping_add(words[index - 7])
            .wrapping_add(s1);
    }

    let mut a = state[0];
    let mut b = state[1];
    let mut c = state[2];
    let mut d = state[3];
    let mut e = state[4];
    let mut f = state[5];
    let mut g = state[6];
    let mut h = state[7];

    for index in 0..64 {
        let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
        let choice = (e & f) ^ ((!e) & g);
        let temp1 = h
            .wrapping_add(s1)
            .wrapping_add(choice)
            .wrapping_add(constants[index])
            .wrapping_add(words[index]);
        let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
        let majority = (a & b) ^ (a & c) ^ (b & c);
        let temp2 = s0.wrapping_add(majority);

        h = g;
        g = f;
        f = e;
        e = d.wrapping_add(temp1);
        d = c;
        c = b;
        b = a;
        a = temp1.wrapping_add(temp2);
    }

    state[0] = state[0].wrapping_add(a);
    state[1] = state[1].wrapping_add(b);
    state[2] = state[2].wrapping_add(c);
    state[3] = state[3].wrapping_add(d);
    state[4] = state[4].wrapping_add(e);
    state[5] = state[5].wrapping_add(f);
    state[6] = state[6].wrapping_add(g);
    state[7] = state[7].wrapping_add(h);
}

pub(crate) const fn bool_code(value: bool) -> &'static str {
    if value { "true" } else { "false" }
}

pub(crate) const fn native_bundle_producer_code(producer: NativeBundleProducer) -> &'static str {
    match producer {
        NativeBundleProducer::TRust => "trust",
        NativeBundleProducer::TSwift => "tswift",
        NativeBundleProducer::TC => "tc",
        NativeBundleProducer::TrustIr => "trust-ir",
    }
}

pub(crate) const fn native_adapter_input_code(input: &NativeAdapterInput) -> &'static str {
    match input {
        NativeAdapterInput::RustMir { .. } => "rust_mir",
        NativeAdapterInput::TrustIrModule => "trust_ir_module",
    }
}

pub(crate) fn observed_single_value<'a>(
    rows: &'a BTreeMap<&'a str, Vec<&'a str>>,
    key: &str,
) -> Option<&'a str> {
    rows.get(key).and_then(|values| values.first().copied())
}

/// Shared replay-report key diagnostics (audit #97): the byte-identical
/// duplicate / missing / unexpected / mismatched-value computation that the ~10
/// `*_replay_report` round-trip validators across the replay-report families
/// (semantic-bridge, Petri-successor, transport-identity, bundle-handoff) each
/// performed inline. Returns the four diagnostic key vectors in the SAME order
/// the families produced them, so the reconstructed reports are byte-for-byte
/// identical — only the family-specific field reconstruction differs and stays
/// local to each validator. (The public report TYPES and their JSON layouts are
/// part of the cross-repo contract and are intentionally NOT unified.)
pub(crate) fn replay_key_diagnostics(
    expected_by_key: &BTreeMap<&str, &str>,
    observed_by_key: &BTreeMap<&str, Vec<&str>>,
) -> (Vec<String>, Vec<String>, Vec<String>, Vec<String>) {
    let duplicate_keys = observed_by_key
        .iter()
        .filter(|(_, values)| values.len() > 1)
        .map(|(key, _)| (*key).to_string())
        .collect::<Vec<_>>();
    let missing_keys = expected_by_key
        .keys()
        .filter(|key| !observed_by_key.contains_key(**key))
        .map(|key| (*key).to_string())
        .collect::<Vec<_>>();
    let unexpected_keys = observed_by_key
        .keys()
        .filter(|key| !expected_by_key.contains_key(**key))
        .map(|key| (*key).to_string())
        .collect::<Vec<_>>();
    let mismatched_value_keys = expected_by_key
        .iter()
        .filter(|(key, expected_value)| {
            observed_by_key
                .get(**key)
                .and_then(|values| values.first())
                .is_some_and(|observed_value| observed_value != *expected_value)
        })
        .map(|(key, _)| (*key).to_string())
        .collect::<Vec<_>>();
    (
        duplicate_keys,
        missing_keys,
        unexpected_keys,
        mismatched_value_keys,
    )
}

pub(crate) fn observed_bool_value(
    rows: &BTreeMap<&str, Vec<&str>>,
    key: &str,
    invalid_keys: &mut Vec<String>,
) -> Option<bool> {
    match observed_single_value(rows, key) {
        Some("true") => Some(true),
        Some("false") => Some(false),
        Some(_) => {
            invalid_keys.push(key.to_string());
            None
        }
        None => None,
    }
}

pub(crate) fn observed_usize_value(
    rows: &BTreeMap<&str, Vec<&str>>,
    key: &str,
    invalid_keys: &mut Vec<String>,
) -> Option<usize> {
    observed_single_value(rows, key).and_then(|value| match value.parse::<usize>() {
        Ok(parsed) => Some(parsed),
        Err(_) => {
            invalid_keys.push(key.to_string());
            None
        }
    })
}

pub(crate) fn reconstructed_indexed_string_values(
    rows: &BTreeMap<&str, Vec<&str>>,
    prefix: &str,
    field_name: &str,
    count: usize,
) -> Vec<String> {
    (0..count)
        .filter_map(|index| {
            observed_single_value(rows, &format!("{prefix}.{index}.{field_name}"))
                .map(str::to_string)
        })
        .collect()
}

pub(crate) fn string_values_match_static(observed: &[String], expected: &[&str]) -> bool {
    observed.len() == expected.len()
        && observed
            .iter()
            .zip(expected.iter())
            .all(|(observed, expected)| observed == expected)
}

pub(crate) fn reconstructed_bool_fixture_values<'a>(
    rows: &'a BTreeMap<&'a str, Vec<&'a str>>,
    fixture_count: usize,
    field_name: &str,
) -> (Vec<bool>, Vec<String>) {
    let mut values = Vec::new();
    let mut invalid_keys = Vec::new();
    for index in 0..fixture_count {
        let key = format!("fixture_manifest.fixture.{index}.expected.{field_name}");
        match observed_single_value(rows, &key) {
            Some("true") => values.push(true),
            Some("false") => values.push(false),
            Some(_) => invalid_keys.push(key),
            None => {}
        }
    }

    (values, invalid_keys)
}

pub(crate) const fn proof_digest_algorithm_code(algorithm: ProofDigestAlgorithm) -> &'static str {
    match algorithm {
        ProofDigestAlgorithm::Sha256 => "sha256",
        ProofDigestAlgorithm::TrustIrStableV1 => "trust_ir-stable-v1",
    }
}

pub(crate) const fn proof_status_code(status: ProofStatus) -> &'static str {
    match status {
        ProofStatus::Pending => "pending",
        ProofStatus::Discharged => "discharged",
        ProofStatus::Failed => "failed",
        ProofStatus::Trusted => "trusted",
        ProofStatus::Certified => "certified",
    }
}

/// Per-operation lowering rows for the canonical `<4 x i32>` x86 contract.
pub const CHC_X86_V4_I32_OPERATION_CONTRACT_ROWS: &[HardwareVectorOperationContractRow] = &[
    HardwareVectorOperationContractRow {
        operation: "const.integer_mask.zero",
        trust_cg_lir_opcode: CHC_X86_V4_I32_ZERO_LIR_OPCODE,
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: "pxor",
        semantics: "all_lanes_i32_zero_mask",
        composition: "zero_vector_or_deferred_zero_base_lane_insert",
    },
    HardwareVectorOperationContractRow {
        operation: "const.integer_mask.all_ones",
        trust_cg_lir_opcode: "",
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: "pcmpeqd",
        semantics: "all_lanes_i32_all_ones_mask_self_compare",
        composition: "",
    },
    HardwareVectorOperationContractRow {
        operation: "const.bool_mask",
        trust_cg_lir_opcode: "",
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: "pxor;pcmpeqd;mov_imm_all_ones;movd_to_xmm;pshufd",
        semantics: "logical_v4_bool_lanes_materialized_as_i32_zero_or_all_ones_masks",
        composition: "bool_false_to_zero;bool_true_to_all_ones;mask_to_bits_compare_masks_only",
    },
    HardwareVectorOperationContractRow {
        operation: "pack_lanes",
        trust_cg_lir_opcode: CHC_X86_V4_I32_LANE_PACK_LIR_OPCODE,
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: CHC_X86_V4_I32_LANE_PACK_NATIVE_INSTRUCTIONS,
        semantics: CHC_X86_V4_I32_LANE_PACK_SEMANTICS,
        composition: "",
    },
    HardwareVectorOperationContractRow {
        operation: "icmp.ne",
        trust_cg_lir_opcode: CHC_X86_V4_I32_ICMP_LIR_OPCODE,
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: "pcmpeqd;pcmpeqd;pxor",
        semantics: "lane_wise_i32_not_equal_mask",
        composition: "not(pcmpeqd(lhs,rhs))",
    },
    HardwareVectorOperationContractRow {
        operation: "binop.add",
        trust_cg_lir_opcode: "",
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: "paddd",
        semantics: "lane_wise_i32_wrapping_add",
        composition: "",
    },
    HardwareVectorOperationContractRow {
        operation: "binop.sub",
        trust_cg_lir_opcode: "",
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: "psubd",
        semantics: "lane_wise_i32_wrapping_sub",
        composition: "",
    },
    HardwareVectorOperationContractRow {
        operation: "binop.mul",
        trust_cg_lir_opcode: "",
        feature_guard: CHC_X86_V4_I32_MUL_FEATURE_GUARD,
        native_instructions: CHC_X86_V4_I32_MUL_NATIVE_INSTRUCTION,
        semantics: CHC_X86_V4_I32_MUL_SEMANTICS,
        composition: "direct_pmulld_or_scalarized_sse2_pmuludq_fallback",
    },
    HardwareVectorOperationContractRow {
        operation: "select",
        trust_cg_lir_opcode: CHC_X86_VECTOR_SELECT_LIR_OPCODE,
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: "pand;pandn;por",
        semantics: "lane_wise_v128_mask_select",
        composition: "or(and(mask,true),andnot(mask,false));v128_bool_select_may_expand_to_pblendvb_when_x86.sse4.1_available",
    },
    HardwareVectorOperationContractRow {
        operation: "icmp.eq",
        trust_cg_lir_opcode: CHC_X86_V4_I32_ICMP_LIR_OPCODE,
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: "pcmpeqd",
        semantics: "lane_wise_i32_equal_mask",
        composition: "pcmpeqd(lhs,rhs)",
    },
    HardwareVectorOperationContractRow {
        operation: "extract_element",
        trust_cg_lir_opcode: CHC_X86_V4_I32_EXTRACT_ELEMENT_LIR_OPCODE,
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: CHC_X86_V4_I32_EXTRACT_ELEMENT_NATIVE_INSTRUCTIONS,
        semantics: CHC_X86_V4_I32_EXTRACT_ELEMENT_SEMANTICS,
        composition: "constant_lane_0_to_3",
    },
    HardwareVectorOperationContractRow {
        operation: "insert_element",
        trust_cg_lir_opcode: CHC_X86_V4_I32_INSERT_ELEMENT_LIR_OPCODE,
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: CHC_X86_V4_I32_INSERT_ELEMENT_NATIVE_INSTRUCTIONS,
        semantics: CHC_X86_V4_I32_INSERT_ELEMENT_SEMANTICS,
        composition: "",
    },
    HardwareVectorOperationContractRow {
        operation: "icmp.slt",
        trust_cg_lir_opcode: CHC_X86_V4_I32_ICMP_LIR_OPCODE,
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: "pcmpgtd",
        semantics: "lane_wise_signed_i32_less_than_mask",
        composition: "pcmpgtd(rhs,lhs)",
    },
    HardwareVectorOperationContractRow {
        operation: "icmp.sle",
        trust_cg_lir_opcode: CHC_X86_V4_I32_ICMP_LIR_OPCODE,
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: "pcmpgtd;pcmpeqd;por",
        semantics: "lane_wise_signed_i32_less_equal_mask",
        composition: "or(pcmpgtd(rhs,lhs),pcmpeqd(lhs,rhs))",
    },
    HardwareVectorOperationContractRow {
        operation: "icmp.sgt",
        trust_cg_lir_opcode: CHC_X86_V4_I32_ICMP_LIR_OPCODE,
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: "pcmpgtd",
        semantics: "lane_wise_signed_i32_greater_than_mask",
        composition: "pcmpgtd(lhs,rhs)",
    },
    HardwareVectorOperationContractRow {
        operation: "icmp.sge",
        trust_cg_lir_opcode: CHC_X86_V4_I32_ICMP_LIR_OPCODE,
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: "pcmpgtd;pcmpeqd;por",
        semantics: "lane_wise_signed_i32_greater_equal_mask",
        composition: "or(pcmpgtd(lhs,rhs),pcmpeqd(lhs,rhs))",
    },
    HardwareVectorOperationContractRow {
        operation: "binop.shl",
        trust_cg_lir_opcode: "",
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: CHC_X86_V4_I32_SHIFT_NATIVE_INSTRUCTIONS,
        semantics: CHC_X86_V4_I32_SHIFT_REASSEMBLY_SEMANTICS,
        composition: CHC_X86_V4_I32_SHIFT_PROOF_CONDITION,
    },
    HardwareVectorOperationContractRow {
        operation: "binop.lshr",
        trust_cg_lir_opcode: "",
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: CHC_X86_V4_I32_SHIFT_NATIVE_INSTRUCTIONS,
        semantics: CHC_X86_V4_I32_SHIFT_REASSEMBLY_SEMANTICS,
        composition: CHC_X86_V4_I32_SHIFT_PROOF_CONDITION,
    },
    HardwareVectorOperationContractRow {
        operation: "binop.ashr",
        trust_cg_lir_opcode: "",
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: CHC_X86_V4_I32_SHIFT_NATIVE_INSTRUCTIONS,
        semantics: CHC_X86_V4_I32_SHIFT_REASSEMBLY_SEMANTICS,
        composition: CHC_X86_V4_I32_SHIFT_PROOF_CONDITION,
    },
];

/// Per-operation lowering rows for the canonical `<2 x i64>` x86 contract.
pub const CHC_X86_V2_I64_OPERATION_CONTRACT_ROWS: &[HardwareVectorOperationContractRow] = &[
    HardwareVectorOperationContractRow {
        operation: "const.integer_mask.zero",
        trust_cg_lir_opcode: CHC_X86_V2_I64_ZERO_LIR_OPCODE,
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: "pxor",
        semantics: "all_lanes_i64_zero_mask",
        composition: "zero_vector_or_deferred_zero_base_lane_insert",
    },
    HardwareVectorOperationContractRow {
        operation: "const.integer_mask.all_ones",
        trust_cg_lir_opcode: "",
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: "pcmpeqd",
        semantics: "all_lanes_i64_all_ones_mask_self_compare",
        composition: "",
    },
    HardwareVectorOperationContractRow {
        operation: "const.bool_mask",
        trust_cg_lir_opcode: "",
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: "pxor;pcmpeqd;mov_imm_all_ones;movq_to_xmm;punpcklqdq",
        semantics: "logical_v2_bool_lanes_materialized_as_i64_zero_or_all_ones_masks",
        composition: "bool_false_to_zero;bool_true_to_all_ones;mask_to_bits_compare_masks_only",
    },
    HardwareVectorOperationContractRow {
        operation: "pack_lanes",
        trust_cg_lir_opcode: CHC_X86_V2_I64_LANE_PACK_LIR_OPCODE,
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: CHC_X86_V2_I64_LANE_PACK_NATIVE_INSTRUCTIONS,
        semantics: CHC_X86_V2_I64_LANE_PACK_SEMANTICS,
        composition: "",
    },
    HardwareVectorOperationContractRow {
        operation: "icmp.ne",
        trust_cg_lir_opcode: CHC_X86_V2_I64_ICMP_LIR_OPCODE,
        feature_guard: CHC_X86_V2_I64_ICMP_EQ_NE_FEATURE_GUARD,
        native_instructions: "pcmpeqq;pcmpeqd;pxor",
        semantics: "lane_wise_i64_not_equal_mask",
        composition: "not(pcmpeqq(lhs,rhs))",
    },
    HardwareVectorOperationContractRow {
        operation: "binop.add",
        trust_cg_lir_opcode: "V2I64Add",
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: "paddq",
        semantics: "lane_wise_i64_wrapping_add",
        composition: "",
    },
    HardwareVectorOperationContractRow {
        operation: "binop.sub",
        trust_cg_lir_opcode: "V2I64Sub",
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: "psubq",
        semantics: "lane_wise_i64_wrapping_sub",
        composition: "",
    },
    HardwareVectorOperationContractRow {
        operation: "select",
        trust_cg_lir_opcode: CHC_X86_VECTOR_SELECT_LIR_OPCODE,
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: "pand;pandn;por",
        semantics: "lane_wise_v128_mask_select",
        composition: "or(and(mask,true),andnot(mask,false));v128_bool_select_may_expand_to_pblendvb_when_x86.sse4.1_available",
    },
    HardwareVectorOperationContractRow {
        operation: "icmp.eq",
        trust_cg_lir_opcode: CHC_X86_V2_I64_ICMP_LIR_OPCODE,
        feature_guard: CHC_X86_V2_I64_ICMP_EQ_NE_FEATURE_GUARD,
        native_instructions: "pcmpeqq",
        semantics: "lane_wise_i64_equal_mask",
        composition: "pcmpeqq(lhs,rhs)",
    },
    HardwareVectorOperationContractRow {
        operation: "insert_element",
        trust_cg_lir_opcode: CHC_X86_V2_I64_INSERT_ELEMENT_LIR_OPCODE,
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: CHC_X86_V2_I64_INSERT_ELEMENT_NATIVE_INSTRUCTIONS,
        semantics: CHC_X86_V2_I64_INSERT_ELEMENT_SEMANTICS,
        composition: "",
    },
    HardwareVectorOperationContractRow {
        operation: "icmp.slt",
        trust_cg_lir_opcode: CHC_X86_V2_I64_ICMP_LIR_OPCODE,
        feature_guard: CHC_X86_V2_I64_ICMP_SIGNED_ORDER_FEATURE_GUARD,
        native_instructions: "pcmpgtq",
        semantics: "lane_wise_signed_i64_less_than_mask",
        composition: "pcmpgtq(rhs,lhs)",
    },
    HardwareVectorOperationContractRow {
        operation: "icmp.sle",
        trust_cg_lir_opcode: CHC_X86_V2_I64_ICMP_LIR_OPCODE,
        feature_guard: CHC_X86_V2_I64_ICMP_SIGNED_ORDER_FEATURE_GUARD,
        native_instructions: "pcmpgtq;pcmpeqq;por",
        semantics: "lane_wise_signed_i64_less_equal_mask",
        composition: "or(pcmpgtq(rhs,lhs),pcmpeqq(lhs,rhs))",
    },
    HardwareVectorOperationContractRow {
        operation: "icmp.sgt",
        trust_cg_lir_opcode: CHC_X86_V2_I64_ICMP_LIR_OPCODE,
        feature_guard: CHC_X86_V2_I64_ICMP_SIGNED_ORDER_FEATURE_GUARD,
        native_instructions: "pcmpgtq",
        semantics: "lane_wise_signed_i64_greater_than_mask",
        composition: "pcmpgtq(lhs,rhs)",
    },
    HardwareVectorOperationContractRow {
        operation: "icmp.sge",
        trust_cg_lir_opcode: CHC_X86_V2_I64_ICMP_LIR_OPCODE,
        feature_guard: CHC_X86_V2_I64_ICMP_SIGNED_ORDER_FEATURE_GUARD,
        native_instructions: "pcmpgtq;pcmpeqq;por",
        semantics: "lane_wise_signed_i64_greater_equal_mask",
        composition: "or(pcmpgtq(lhs,rhs),pcmpeqq(lhs,rhs))",
    },
    HardwareVectorOperationContractRow {
        operation: "extract_element",
        trust_cg_lir_opcode: CHC_X86_V2_I64_EXTRACT_ELEMENT_LIR_OPCODE,
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: CHC_X86_V2_I64_EXTRACT_ELEMENT_NATIVE_INSTRUCTIONS,
        semantics: CHC_X86_V2_I64_EXTRACT_ELEMENT_SEMANTICS,
        composition: "constant_lane_0_or_1",
    },
];

/// Per-operation lowering rows for the canonical `<16 x i8>` x86 narrow
/// compare-mask contract.
pub const CHC_X86_V16_I8_OPERATION_CONTRACT_ROWS: &[HardwareVectorOperationContractRow] = &[
    HardwareVectorOperationContractRow {
        operation: "icmp.eq",
        trust_cg_lir_opcode: "",
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: "pcmpeqb",
        semantics: "lane_wise_i8_equal_compare_mask_all_zero_or_all_ones_bytes",
        composition: "pcmpeqb(lhs,rhs)",
    },
    HardwareVectorOperationContractRow {
        operation: "icmp.ne",
        trust_cg_lir_opcode: "",
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: "pcmpeqb;pcmpeqb;pxor",
        semantics: "lane_wise_i8_not_equal_compare_mask_all_zero_or_all_ones_bytes",
        composition: "not(pcmpeqb(lhs,rhs))",
    },
    HardwareVectorOperationContractRow {
        operation: "icmp.slt",
        trust_cg_lir_opcode: "",
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: "pcmpgtb",
        semantics: "lane_wise_signed_i8_less_than_compare_mask_all_zero_or_all_ones_bytes",
        composition: "pcmpgtb(rhs,lhs)",
    },
    HardwareVectorOperationContractRow {
        operation: "icmp.sle",
        trust_cg_lir_opcode: "",
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: "pcmpgtb;pcmpeqb;por",
        semantics: "lane_wise_signed_i8_less_equal_compare_mask_all_zero_or_all_ones_bytes",
        composition: "or(pcmpgtb(rhs,lhs),pcmpeqb(lhs,rhs))",
    },
    HardwareVectorOperationContractRow {
        operation: "icmp.sgt",
        trust_cg_lir_opcode: "",
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: "pcmpgtb",
        semantics: "lane_wise_signed_i8_greater_than_compare_mask_all_zero_or_all_ones_bytes",
        composition: "pcmpgtb(lhs,rhs)",
    },
    HardwareVectorOperationContractRow {
        operation: "icmp.sge",
        trust_cg_lir_opcode: "",
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: "pcmpgtb;pcmpeqb;por",
        semantics: "lane_wise_signed_i8_greater_equal_compare_mask_all_zero_or_all_ones_bytes",
        composition: "or(pcmpgtb(lhs,rhs),pcmpeqb(lhs,rhs))",
    },
    HardwareVectorOperationContractRow {
        operation: "vector.mask_to_bits",
        trust_cg_lir_opcode: "",
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: "pmovmskb",
        semantics: CHC_X86_V16_I8_MASK_TO_BITS_SEMANTICS,
        composition: CHC_X86_V16_I8_MASK_TO_BITS_COMPOSITION,
    },
];

/// Per-operation lowering rows for the canonical `<8 x i16>` x86 narrow
/// compare-mask contract.
pub const CHC_X86_V8_I16_OPERATION_CONTRACT_ROWS: &[HardwareVectorOperationContractRow] = &[
    HardwareVectorOperationContractRow {
        operation: "icmp.eq",
        trust_cg_lir_opcode: "",
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: "pcmpeqw",
        semantics: "lane_wise_i16_equal_compare_mask_all_zero_or_all_ones_words",
        composition: "pcmpeqw(lhs,rhs)",
    },
    HardwareVectorOperationContractRow {
        operation: "icmp.ne",
        trust_cg_lir_opcode: "",
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: "pcmpeqw;pcmpeqw;pxor",
        semantics: "lane_wise_i16_not_equal_compare_mask_all_zero_or_all_ones_words",
        composition: "not(pcmpeqw(lhs,rhs))",
    },
    HardwareVectorOperationContractRow {
        operation: "icmp.slt",
        trust_cg_lir_opcode: "",
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: "pcmpgtw",
        semantics: "lane_wise_signed_i16_less_than_compare_mask_all_zero_or_all_ones_words",
        composition: "pcmpgtw(rhs,lhs)",
    },
    HardwareVectorOperationContractRow {
        operation: "icmp.sle",
        trust_cg_lir_opcode: "",
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: "pcmpgtw;pcmpeqw;por",
        semantics: "lane_wise_signed_i16_less_equal_compare_mask_all_zero_or_all_ones_words",
        composition: "or(pcmpgtw(rhs,lhs),pcmpeqw(lhs,rhs))",
    },
    HardwareVectorOperationContractRow {
        operation: "icmp.sgt",
        trust_cg_lir_opcode: "",
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: "pcmpgtw",
        semantics: "lane_wise_signed_i16_greater_than_compare_mask_all_zero_or_all_ones_words",
        composition: "pcmpgtw(lhs,rhs)",
    },
    HardwareVectorOperationContractRow {
        operation: "icmp.sge",
        trust_cg_lir_opcode: "",
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: "pcmpgtw;pcmpeqw;por",
        semantics: "lane_wise_signed_i16_greater_equal_compare_mask_all_zero_or_all_ones_words",
        composition: "or(pcmpgtw(lhs,rhs),pcmpeqw(lhs,rhs))",
    },
    HardwareVectorOperationContractRow {
        operation: "vector.mask_to_bits",
        trust_cg_lir_opcode: "",
        feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        native_instructions: "pmovmskb",
        semantics: CHC_X86_V8_I16_MASK_TO_BITS_SEMANTICS,
        composition: CHC_X86_V8_I16_MASK_TO_BITS_COMPOSITION,
    },
];

/// Fail-closed status rows for unsigned `<4 x i32>` vector compares.
pub const CHC_X86_V4_I32_OPERATION_STATUS_ROWS: &[HardwareVectorOperationStatusRow] = &[
    HardwareVectorOperationStatusRow {
        operation: "icmp.ult",
        status: HardwareVectorContractStatus::Deferred,
        reason: HardwareVectorContractReason::UnsignedVectorCompareProofBlocked,
    },
    HardwareVectorOperationStatusRow {
        operation: "icmp.ule",
        status: HardwareVectorContractStatus::Deferred,
        reason: HardwareVectorContractReason::UnsignedVectorCompareProofBlocked,
    },
    HardwareVectorOperationStatusRow {
        operation: "icmp.ugt",
        status: HardwareVectorContractStatus::Deferred,
        reason: HardwareVectorContractReason::UnsignedVectorCompareProofBlocked,
    },
    HardwareVectorOperationStatusRow {
        operation: "icmp.uge",
        status: HardwareVectorContractStatus::Deferred,
        reason: HardwareVectorContractReason::UnsignedVectorCompareProofBlocked,
    },
];

/// Fail-closed status rows for unsigned `<2 x i64>` vector compares.
pub const CHC_X86_V2_I64_OPERATION_STATUS_ROWS: &[HardwareVectorOperationStatusRow] = &[
    HardwareVectorOperationStatusRow {
        operation: "icmp.ult",
        status: HardwareVectorContractStatus::Unavailable,
        reason: HardwareVectorContractReason::UnsignedVectorCompareUnavailable,
    },
    HardwareVectorOperationStatusRow {
        operation: "icmp.ule",
        status: HardwareVectorContractStatus::Unavailable,
        reason: HardwareVectorContractReason::UnsignedVectorCompareUnavailable,
    },
    HardwareVectorOperationStatusRow {
        operation: "icmp.ugt",
        status: HardwareVectorContractStatus::Unavailable,
        reason: HardwareVectorContractReason::UnsignedVectorCompareUnavailable,
    },
    HardwareVectorOperationStatusRow {
        operation: "icmp.uge",
        status: HardwareVectorContractStatus::Unavailable,
        reason: HardwareVectorContractReason::UnsignedVectorCompareUnavailable,
    },
];

/// Fail-closed status rows for unsigned `<16 x i8>` vector compares.
pub const CHC_X86_V16_I8_OPERATION_STATUS_ROWS: &[HardwareVectorOperationStatusRow] = &[
    HardwareVectorOperationStatusRow {
        operation: "icmp.ult",
        status: HardwareVectorContractStatus::Unavailable,
        reason: HardwareVectorContractReason::UnsignedVectorCompareUnavailable,
    },
    HardwareVectorOperationStatusRow {
        operation: "icmp.ule",
        status: HardwareVectorContractStatus::Unavailable,
        reason: HardwareVectorContractReason::UnsignedVectorCompareUnavailable,
    },
    HardwareVectorOperationStatusRow {
        operation: "icmp.ugt",
        status: HardwareVectorContractStatus::Unavailable,
        reason: HardwareVectorContractReason::UnsignedVectorCompareUnavailable,
    },
    HardwareVectorOperationStatusRow {
        operation: "icmp.uge",
        status: HardwareVectorContractStatus::Unavailable,
        reason: HardwareVectorContractReason::UnsignedVectorCompareUnavailable,
    },
];

/// Fail-closed status rows for unsigned `<8 x i16>` vector compares.
pub const CHC_X86_V8_I16_OPERATION_STATUS_ROWS: &[HardwareVectorOperationStatusRow] = &[
    HardwareVectorOperationStatusRow {
        operation: "icmp.ult",
        status: HardwareVectorContractStatus::Unavailable,
        reason: HardwareVectorContractReason::UnsignedVectorCompareUnavailable,
    },
    HardwareVectorOperationStatusRow {
        operation: "icmp.ule",
        status: HardwareVectorContractStatus::Unavailable,
        reason: HardwareVectorContractReason::UnsignedVectorCompareUnavailable,
    },
    HardwareVectorOperationStatusRow {
        operation: "icmp.ugt",
        status: HardwareVectorContractStatus::Unavailable,
        reason: HardwareVectorContractReason::UnsignedVectorCompareUnavailable,
    },
    HardwareVectorOperationStatusRow {
        operation: "icmp.uge",
        status: HardwareVectorContractStatus::Unavailable,
        reason: HardwareVectorContractReason::UnsignedVectorCompareUnavailable,
    },
];

/// Canonical `<4 x i32>` CHC x86 hardware vector contract descriptor.
pub const CHC_X86_V4_I32_HARDWARE_VECTOR_CONTRACT_DESCRIPTOR: HardwareVectorContractDescriptor =
    HardwareVectorContractDescriptor {
        schema: HARDWARE_VECTOR_CONTRACT_SCHEMA,
        schema_version: HARDWARE_VECTOR_CONTRACT_SCHEMA_VERSION,
        source_package: CHC_X86_HARDWARE_VECTOR_CONTRACT_SOURCE_PACKAGE,
        target_family: CHC_X86_HARDWARE_VECTOR_CONTRACT_TARGET_FAMILY,
        hardware_model: CHC_X86_HARDWARE_VECTOR_CONTRACT_HARDWARE_MODEL,
        contract_name: "chc_x86.v4_i32",
        value_ty: "<4 x i32>",
        logical_mask_ty: "<4 x bool>",
        physical_mask_ty: "<4 x i32>",
        element_ty: "i32",
        element_bits: 32,
        lane_count: 4,
        total_bits: 128,
        mask_semantics: CHC_X86_HARDWARE_VECTOR_CONTRACT_MASK_SEMANTICS,
        operations: CHC_X86_V4_I32_HARDWARE_VECTOR_CONTRACT_OPERATIONS,
        mul_feature_guard: CHC_X86_V4_I32_MUL_FEATURE_GUARD,
        mul_native_instruction: CHC_X86_V4_I32_MUL_NATIVE_INSTRUCTION,
        mul_semantics: CHC_X86_V4_I32_MUL_SEMANTICS,
        lane_pack_lir_opcode: CHC_X86_V4_I32_LANE_PACK_LIR_OPCODE,
        lane_pack_feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        lane_pack_native_instructions: CHC_X86_V4_I32_LANE_PACK_NATIVE_INSTRUCTIONS,
        lane_pack_semantics: CHC_X86_V4_I32_LANE_PACK_SEMANTICS,
        status: HardwareVectorContractStatus::Available,
        reason: HardwareVectorContractReason::CanonicalContract,
    };

/// Canonical `<2 x i64>` CHC x86 hardware vector contract descriptor.
pub const CHC_X86_V2_I64_HARDWARE_VECTOR_CONTRACT_DESCRIPTOR: HardwareVectorContractDescriptor =
    HardwareVectorContractDescriptor {
        schema: HARDWARE_VECTOR_CONTRACT_SCHEMA,
        schema_version: HARDWARE_VECTOR_CONTRACT_SCHEMA_VERSION,
        source_package: CHC_X86_HARDWARE_VECTOR_CONTRACT_SOURCE_PACKAGE,
        target_family: CHC_X86_HARDWARE_VECTOR_CONTRACT_TARGET_FAMILY,
        hardware_model: CHC_X86_HARDWARE_VECTOR_CONTRACT_HARDWARE_MODEL,
        contract_name: "chc_x86.v2_i64",
        value_ty: "<2 x i64>",
        logical_mask_ty: "<2 x bool>",
        physical_mask_ty: "<2 x i64>",
        element_ty: "i64",
        element_bits: 64,
        lane_count: 2,
        total_bits: 128,
        mask_semantics: CHC_X86_HARDWARE_VECTOR_CONTRACT_MASK_SEMANTICS,
        operations: CHC_X86_V2_I64_HARDWARE_VECTOR_CONTRACT_OPERATIONS,
        mul_feature_guard: "",
        mul_native_instruction: "",
        mul_semantics: "",
        lane_pack_lir_opcode: CHC_X86_V2_I64_LANE_PACK_LIR_OPCODE,
        lane_pack_feature_guard: CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
        lane_pack_native_instructions: CHC_X86_V2_I64_LANE_PACK_NATIVE_INSTRUCTIONS,
        lane_pack_semantics: CHC_X86_V2_I64_LANE_PACK_SEMANTICS,
        status: HardwareVectorContractStatus::Available,
        reason: HardwareVectorContractReason::CanonicalContract,
    };

/// Canonical `<16 x i8>` CHC x86 hardware vector contract descriptor.
pub const CHC_X86_V16_I8_HARDWARE_VECTOR_CONTRACT_DESCRIPTOR: HardwareVectorContractDescriptor =
    HardwareVectorContractDescriptor {
        schema: HARDWARE_VECTOR_CONTRACT_SCHEMA,
        schema_version: HARDWARE_VECTOR_CONTRACT_SCHEMA_VERSION,
        source_package: CHC_X86_HARDWARE_VECTOR_CONTRACT_SOURCE_PACKAGE,
        target_family: CHC_X86_HARDWARE_VECTOR_CONTRACT_TARGET_FAMILY,
        hardware_model: CHC_X86_HARDWARE_VECTOR_CONTRACT_HARDWARE_MODEL,
        contract_name: "chc_x86.v16_i8",
        value_ty: "<16 x i8>",
        logical_mask_ty: "<16 x bool>",
        physical_mask_ty: "<16 x i8>",
        element_ty: "i8",
        element_bits: 8,
        lane_count: 16,
        total_bits: 128,
        mask_semantics: CHC_X86_HARDWARE_VECTOR_CONTRACT_MASK_SEMANTICS,
        operations: CHC_X86_V16_I8_HARDWARE_VECTOR_CONTRACT_OPERATIONS,
        mul_feature_guard: "",
        mul_native_instruction: "",
        mul_semantics: "",
        lane_pack_lir_opcode: "",
        lane_pack_feature_guard: "",
        lane_pack_native_instructions: "",
        lane_pack_semantics: "",
        status: HardwareVectorContractStatus::Available,
        reason: HardwareVectorContractReason::CanonicalContract,
    };

/// Canonical `<8 x i16>` CHC x86 hardware vector contract descriptor.
pub const CHC_X86_V8_I16_HARDWARE_VECTOR_CONTRACT_DESCRIPTOR: HardwareVectorContractDescriptor =
    HardwareVectorContractDescriptor {
        schema: HARDWARE_VECTOR_CONTRACT_SCHEMA,
        schema_version: HARDWARE_VECTOR_CONTRACT_SCHEMA_VERSION,
        source_package: CHC_X86_HARDWARE_VECTOR_CONTRACT_SOURCE_PACKAGE,
        target_family: CHC_X86_HARDWARE_VECTOR_CONTRACT_TARGET_FAMILY,
        hardware_model: CHC_X86_HARDWARE_VECTOR_CONTRACT_HARDWARE_MODEL,
        contract_name: "chc_x86.v8_i16",
        value_ty: "<8 x i16>",
        logical_mask_ty: "<8 x bool>",
        physical_mask_ty: "<8 x i16>",
        element_ty: "i16",
        element_bits: 16,
        lane_count: 8,
        total_bits: 128,
        mask_semantics: CHC_X86_HARDWARE_VECTOR_CONTRACT_MASK_SEMANTICS,
        operations: CHC_X86_V8_I16_HARDWARE_VECTOR_CONTRACT_OPERATIONS,
        mul_feature_guard: "",
        mul_native_instruction: "",
        mul_semantics: "",
        lane_pack_lir_opcode: "",
        lane_pack_feature_guard: "",
        lane_pack_native_instructions: "",
        lane_pack_semantics: "",
        status: HardwareVectorContractStatus::Available,
        reason: HardwareVectorContractReason::CanonicalContract,
    };

/// Return the canonical CHC x86 hardware vector contract descriptors.
pub const fn chc_x86_hardware_vector_contract_descriptors() -> [HardwareVectorContractDescriptor; 4]
{
    [
        CHC_X86_V4_I32_HARDWARE_VECTOR_CONTRACT_DESCRIPTOR,
        CHC_X86_V2_I64_HARDWARE_VECTOR_CONTRACT_DESCRIPTOR,
        CHC_X86_V16_I8_HARDWARE_VECTOR_CONTRACT_DESCRIPTOR,
        CHC_X86_V8_I16_HARDWARE_VECTOR_CONTRACT_DESCRIPTOR,
    ]
}

/// Emit one deterministic manifest for all canonical CHC x86 vector contracts.
pub fn chc_x86_hardware_vector_contract_manifest_rows()
-> Vec<NativeSharedPrimitiveContractManifestRow> {
    let descriptors = chc_x86_hardware_vector_contract_descriptors();
    let mut rows = Vec::new();
    push_manifest_row(
        &mut rows,
        "hardware_vector_contract_set.manifest.schema",
        HARDWARE_VECTOR_CONTRACT_MANIFEST_SCHEMA,
    );
    push_manifest_row(
        &mut rows,
        "hardware_vector_contract_set.manifest.schema_version",
        HARDWARE_VECTOR_CONTRACT_MANIFEST_SCHEMA_VERSION.to_string(),
    );
    push_manifest_row(
        &mut rows,
        "hardware_vector_contract_set.source.package",
        CHC_X86_HARDWARE_VECTOR_CONTRACT_SOURCE_PACKAGE,
    );
    push_manifest_row(
        &mut rows,
        "hardware_vector_contract_set.name",
        CHC_X86_HARDWARE_VECTOR_CONTRACT_SET_NAME,
    );
    push_manifest_row(
        &mut rows,
        "hardware_vector_contract_set.target.family",
        CHC_X86_HARDWARE_VECTOR_CONTRACT_TARGET_FAMILY,
    );
    push_manifest_row(
        &mut rows,
        "hardware_vector_contract_set.contract_count",
        descriptors.len().to_string(),
    );
    for (index, descriptor) in descriptors.iter().enumerate() {
        descriptor.push_manifest_rows_with_prefix(
            &mut rows,
            &format!("hardware_vector_contract_set.contract.{index}"),
        );
    }
    rows
}

/// Emit stable escaped `key=value` rows for all canonical CHC x86 vector contracts.
pub fn chc_x86_hardware_vector_contract_manifest_key_value_lines() -> Vec<String> {
    chc_x86_hardware_vector_contract_manifest_rows()
        .into_iter()
        .map(|row| row.to_key_value_line())
        .collect()
}

/// Emit stable line-oriented manifest text for all canonical CHC x86 vector contracts.
pub fn chc_x86_hardware_vector_contract_manifest_key_value_text() -> String {
    format!(
        "{}\n",
        chc_x86_hardware_vector_contract_manifest_key_value_lines().join("\n")
    )
}

/// Return the canonical CHC x86 vector-contract manifest row count.
pub fn chc_x86_hardware_vector_contract_manifest_row_count() -> usize {
    chc_x86_hardware_vector_contract_manifest_rows().len()
}

/// Return the canonical CHC x86 vector-contract manifest digest.
pub fn chc_x86_hardware_vector_contract_manifest_digest() -> ProofDigest {
    manifest_key_value_lines_digest(&chc_x86_hardware_vector_contract_manifest_key_value_lines())
}

/// Return the canonical CHC x86 vector-contract manifest digest as `sha256:<hex>`.
pub fn chc_x86_hardware_vector_contract_manifest_sha256() -> String {
    chc_x86_hardware_vector_contract_manifest_digest().to_string()
}

/// Aggregate TY shared-primitive producer manifest.
pub const TY_SHARED_PRIMITIVE_MANIFEST: TySharedPrimitiveManifest = TySharedPrimitiveManifest {
    schema: TY_SHARED_PRIMITIVE_MANIFEST_SCHEMA,
    schema_version: TY_SHARED_PRIMITIVE_MANIFEST_SCHEMA_VERSION,
    source_package: TY_SHARED_PRIMITIVE_MANIFEST_SOURCE_PACKAGE,
    source_package_version: TY_SHARED_PRIMITIVE_MANIFEST_SOURCE_PACKAGE_VERSION,
    status: TySharedPrimitiveManifestStatus::Available,
    reason: TySharedPrimitiveManifestReason::ProducerOwnedRowsAvailable,
};

/// Return the aggregate TY shared-primitive producer manifest.
pub const fn ty_shared_primitive_manifest() -> TySharedPrimitiveManifest {
    TY_SHARED_PRIMITIVE_MANIFEST
}

/// Emit stable rows for the aggregate TY shared-primitive producer manifest.
pub fn ty_shared_primitive_manifest_rows() -> Vec<NativeSharedPrimitiveContractManifestRow> {
    TY_SHARED_PRIMITIVE_MANIFEST.manifest_rows()
}

/// Emit stable escaped `key=value` rows for the aggregate TY manifest.
pub fn ty_shared_primitive_manifest_key_value_lines() -> Vec<String> {
    TY_SHARED_PRIMITIVE_MANIFEST.manifest_key_value_lines()
}

/// Emit stable line-oriented text for the aggregate TY manifest.
pub fn ty_shared_primitive_manifest_key_value_text() -> String {
    TY_SHARED_PRIMITIVE_MANIFEST.manifest_key_value_text()
}

/// Return the aggregate TY shared-primitive manifest row count.
pub fn ty_shared_primitive_manifest_row_count() -> usize {
    TY_SHARED_PRIMITIVE_MANIFEST.manifest_row_count()
}

/// Return the aggregate TY shared-primitive manifest digest.
pub fn ty_shared_primitive_manifest_digest() -> ProofDigest {
    TY_SHARED_PRIMITIVE_MANIFEST.manifest_digest()
}

/// Return the aggregate TY shared-primitive manifest digest as `sha256:<hex>`.
pub fn ty_shared_primitive_manifest_sha256() -> String {
    TY_SHARED_PRIMITIVE_MANIFEST.manifest_sha256()
}

/// AY-owned solver evidence identities required for Petri/TrustMc production acceptance.
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_SOLVER_EVIDENCE_DESCRIPTOR:
    NativeSharedPrimitiveSolverEvidenceDescriptor = NativeSharedPrimitiveSolverEvidenceDescriptor {
    owner_suite: NativeVerifierSuite::AY,
    solver_capability_descriptor_schema: AY_SOLVER_CAPABILITY_DESCRIPTOR_SCHEMA,
    solver_capability_descriptor_schema_version: AY_SOLVER_CAPABILITY_DESCRIPTOR_SCHEMA_VERSION,
    model_blocking_clause_schema: AY_MODEL_BLOCKING_CLAUSE_SCHEMA,
    model_blocking_clause_schema_version: AY_MODEL_BLOCKING_CLAUSE_SCHEMA_VERSION,
    model_blocking_clause_evidence_schema: AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA,
    model_blocking_clause_evidence_schema_version: AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA_VERSION,
    solve_decision_profile_model_consumer_schema: AY_SOLVE_DECISION_PROFILE_MODEL_CONSUMER_SCHEMA,
    solve_decision_profile_model_consumer_schema_version:
        AY_SOLVE_DECISION_PROFILE_MODEL_CONSUMER_SCHEMA_VERSION,
    acceptance_report_api_name: PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_ACCEPTANCE_REPORT_API_NAME,
    consumer_acceptance_api_name: PETRI_SUCCESSOR_TRUST_MC_CHC_CONSUMER_ACCEPTANCE_API_NAME,
};

/// Shared primitive contract for Petri successor TrustMc CHC model acceptance.
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_SHARED_PRIMITIVE_CONTRACT_DESCRIPTOR:
    NativeSharedPrimitiveContractDescriptor = NativeSharedPrimitiveContractDescriptor {
    schema: NATIVE_SHARED_PRIMITIVE_CONTRACT_SCHEMA,
    schema_version: NATIVE_SHARED_PRIMITIVE_CONTRACT_SCHEMA_VERSION,
    contract_schema: PETRI_SUCCESSOR_TRUST_MC_CHC_CONTRACT_SCHEMA,
    contract_schema_version: PETRI_SUCCESSOR_TRUST_MC_CHC_CONTRACT_SCHEMA_VERSION,
    formula_schema: PETRI_SUCCESSOR_PLAN_CACHE_EQUIVALENCE_SCHEMA,
    readiness_report_schema: PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_VALIDATION_READINESS_SCHEMA,
    readiness_report_schema_version:
        PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_VALIDATION_READINESS_SCHEMA_VERSION,
    verifier_suite: PETRI_SUCCESSOR_TRUST_MC_CHC_CONTRACT_VERIFIER_SUITE,
    verification_mode: NativeSharedPrimitiveVerificationMode::TrustMc(
        PETRI_SUCCESSOR_TRUST_MC_CHC_CONTRACT_VERIFICATION_MODE,
    ),
    required_artifact_kinds:
        PETRI_SUCCESSOR_TRUST_MC_CHC_PRODUCTION_ACCEPTANCE_REQUIRED_ARTIFACT_KINDS,
    optional_artifact_kinds:
        PETRI_SUCCESSOR_TRUST_MC_CHC_PRODUCTION_ACCEPTANCE_OPTIONAL_ARTIFACT_KINDS,
    required_artifact_requirements:
        PETRI_SUCCESSOR_TRUST_MC_CHC_PRODUCTION_ACCEPTANCE_REQUIRED_ARTIFACT_REQUIREMENTS,
    production_requires_emitted_solver_artifacts:
        PETRI_SUCCESSOR_TRUST_MC_CHC_PRODUCTION_REQUIRES_EMITTED_SOLVER_ARTIFACTS,
    requires_solver_acceptance:
        PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_VALIDATION_REQUIRES_SOLVER_ACCEPTANCE,
    model_acceptance_report_api_name: PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_ACCEPTANCE_REPORT_API_NAME,
    consumer_acceptance_api_name: PETRI_SUCCESSOR_TRUST_MC_CHC_CONSUMER_ACCEPTANCE_API_NAME,
    production_acceptance_owner_suite:
        PETRI_SUCCESSOR_TRUST_MC_CHC_PRODUCTION_ACCEPTANCE_OWNER_SUITE,
    solver_evidence_descriptor: PETRI_SUCCESSOR_TRUST_MC_CHC_SOLVER_EVIDENCE_DESCRIPTOR,
};

/// Return the Petri successor TrustMc CHC shared primitive contract descriptor.
///
/// Prefer this shared descriptor, or
/// [`PetriSuccessorTrustMcChcContractDescriptor::shared_primitive_contract`],
/// when downstream code needs promotion gates for Petri/TrustMc model acceptance.
/// It carries the readiness schema, required artifacts, AY-owned acceptance
/// APIs, and solver-acceptance requirement without making the acceptance
/// decision in TrustIr.
pub const fn petri_successor_trust_mc_chc_shared_primitive_contract_descriptor()
-> NativeSharedPrimitiveContractDescriptor {
    PETRI_SUCCESSOR_TRUST_MC_CHC_SHARED_PRIMITIVE_CONTRACT_DESCRIPTOR
}

/// Emit stable rows for the Petri successor TrustMc CHC shared-primitive contract.
pub fn petri_successor_trust_mc_chc_shared_primitive_contract_manifest_rows()
-> Vec<NativeSharedPrimitiveContractManifestRow> {
    PETRI_SUCCESSOR_TRUST_MC_CHC_SHARED_PRIMITIVE_CONTRACT_DESCRIPTOR.manifest_rows()
}

/// Emit stable escaped `key=value` rows for the Petri successor TrustMc CHC contract.
pub fn petri_successor_trust_mc_chc_shared_primitive_contract_manifest_key_value_lines()
-> Vec<String> {
    PETRI_SUCCESSOR_TRUST_MC_CHC_SHARED_PRIMITIVE_CONTRACT_DESCRIPTOR.manifest_key_value_lines()
}

/// Emit stable line-oriented manifest text for the Petri successor TrustMc CHC contract.
pub fn petri_successor_trust_mc_chc_shared_primitive_contract_manifest_key_value_text() -> String {
    PETRI_SUCCESSOR_TRUST_MC_CHC_SHARED_PRIMITIVE_CONTRACT_DESCRIPTOR.manifest_key_value_text()
}

/// Return the Petri successor TrustMc CHC contract manifest row count.
pub fn petri_successor_trust_mc_chc_shared_primitive_contract_manifest_row_count() -> usize {
    PETRI_SUCCESSOR_TRUST_MC_CHC_SHARED_PRIMITIVE_CONTRACT_DESCRIPTOR.manifest_row_count()
}

/// Return the Petri successor TrustMc CHC contract manifest digest.
pub fn petri_successor_trust_mc_chc_shared_primitive_contract_manifest_digest() -> ProofDigest {
    PETRI_SUCCESSOR_TRUST_MC_CHC_SHARED_PRIMITIVE_CONTRACT_DESCRIPTOR.manifest_digest()
}

/// Return the Petri successor TrustMc CHC contract manifest digest as `sha256:<hex>`.
pub fn petri_successor_trust_mc_chc_shared_primitive_contract_manifest_sha256() -> String {
    PETRI_SUCCESSOR_TRUST_MC_CHC_SHARED_PRIMITIVE_CONTRACT_DESCRIPTOR.manifest_sha256()
}

/// Petri native bundle handoff descriptor consumed by downstream backends.
///
/// This is a `static`, rather than a `const`, because copying the deeply nested
/// descriptor through constant evaluation forces rustc to materialize a huge
/// type-level valtree at every use. Keeping one immutable object preserves the
/// same process-lifetime identity while retaining rustc's normal 100k valtree
/// resource bound for every crate.
pub static PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_DESCRIPTOR:
    PetriNativeVerificationBundleHandoffDescriptor =
    PetriNativeVerificationBundleHandoffDescriptor {
        schema: PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SCHEMA,
        schema_version: PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SCHEMA_VERSION,
        source_package: PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SOURCE_PACKAGE,
        source_package_version: PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SOURCE_PACKAGE_VERSION,
        bundle_identity_contract: NATIVE_BUNDLE_IDENTITY_CONTRACT_DESCRIPTOR,
        artifact_authority_row_descriptor: NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_ROW_DESCRIPTOR,
        shared_primitive_contract:
            PETRI_SUCCESSOR_TRUST_MC_CHC_SHARED_PRIMITIVE_CONTRACT_DESCRIPTOR,
        solver_evidence_descriptor: PETRI_SUCCESSOR_TRUST_MC_CHC_SOLVER_EVIDENCE_DESCRIPTOR,
        expected_bundle_identity_fields: NATIVE_BUNDLE_IDENTITY_CONTRACT_PROVIDED_FIELDS,
        downstream_consumer_responsibilities:
            PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_DOWNSTREAM_CONSUMER_RESPONSIBILITIES,
    };

/// Aggregate Petri handoff replay contract import surface consumed downstream.
pub const PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_SURFACE:
    PetriNativeVerificationBundleHandoffReplayContractSurface =
    PetriNativeVerificationBundleHandoffReplayContractSurface {
        schema: PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_SURFACE_SCHEMA,
        schema_version:
            PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_SURFACE_SCHEMA_VERSION,
        source_package: PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SOURCE_PACKAGE,
        source_package_version: PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SOURCE_PACKAGE_VERSION,
        helper_names: PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_HELPER_NAMES,
        schema_names: PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_SCHEMA_NAMES,
        schema_values: PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_SCHEMA_VALUES,
        fixture_names: PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_FIXTURE_NAMES,
        validator_names: PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_VALIDATOR_NAMES,
    };

/// Return the Petri native bundle handoff descriptor consumed by downstream backends.
pub fn petri_native_verification_bundle_handoff_descriptor()
-> PetriNativeVerificationBundleHandoffDescriptor {
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_DESCRIPTOR
}

/// Return the aggregate Petri handoff replay contract import surface.
pub const fn petri_native_verification_bundle_handoff_replay_contract_surface()
-> PetriNativeVerificationBundleHandoffReplayContractSurface {
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_SURFACE
}

/// Self-audit the default Petri native handoff descriptor consumed downstream.
pub fn petri_native_verification_bundle_handoff_contract_health_report()
-> PetriNativeVerificationBundleHandoffContractHealthReport {
    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_DESCRIPTOR.contract_health_report()
}

/// Return the TrustIr-owned Petri handoff diagnostic fixture manifest.
pub fn petri_native_verification_bundle_handoff_diagnostic_fixture_manifest()
-> PetriNativeVerificationBundleHandoffDiagnosticFixtureManifest {
    PetriNativeVerificationBundleHandoffDiagnosticFixtureManifest {
        schema: PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_DIAGNOSTIC_FIXTURE_MANIFEST_SCHEMA,
        schema_version:
            PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_DIAGNOSTIC_FIXTURE_MANIFEST_SCHEMA_VERSION,
        source_package: PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SOURCE_PACKAGE,
        source_package_version: PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SOURCE_PACKAGE_VERSION,
        fixtures: vec![
            PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestEntry {
                fixture_name:
                    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_HEALTHY_DIAGNOSTIC_FIXTURE_NAME,
                expected_completeness_status_code: "complete",
                expected_manifest_identity_status_code: "complete",
                expected_contract_health_status_code: "healthy",
                expected_accepted: true,
                expected_fail_closed: false,
                handoff_schema: PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SCHEMA,
                handoff_schema_version: PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SCHEMA_VERSION,
                manifest_identity_schema:
                    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_SCHEMA,
                manifest_identity_schema_version:
                    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_SCHEMA_VERSION,
            },
            PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestEntry {
                fixture_name:
                    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_INCOMPLETE_DIAGNOSTIC_FIXTURE_NAME,
                expected_completeness_status_code: "incomplete",
                expected_manifest_identity_status_code: "incomplete",
                expected_contract_health_status_code: "inconsistent",
                expected_accepted: false,
                expected_fail_closed: true,
                handoff_schema: PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SCHEMA,
                handoff_schema_version: PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SCHEMA_VERSION,
                manifest_identity_schema:
                    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_SCHEMA,
                manifest_identity_schema_version:
                    PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_SCHEMA_VERSION,
            },
        ],
    }
}

/// Return the healthy default Petri handoff fixture for downstream replay tests.
pub fn petri_native_verification_bundle_handoff_healthy_diagnostic_fixture()
-> PetriNativeVerificationBundleHandoffHealthyDiagnosticFixture {
    let descriptor = PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_DESCRIPTOR;
    let normalized_rows = descriptor.normalized_rows();
    let completeness_report = descriptor.validate_normalized_rows(&normalized_rows);
    let manifest_identity = descriptor.manifest_identity_for_rows(&normalized_rows);
    let manifest_identity_rows = manifest_identity.key_value_rows();
    let contract_health_report = descriptor.contract_health_report_for_rows(&normalized_rows);
    let contract_health_rows = contract_health_report.key_value_rows();

    PetriNativeVerificationBundleHandoffHealthyDiagnosticFixture {
        fixture_name: PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_HEALTHY_DIAGNOSTIC_FIXTURE_NAME,
        normalized_rows,
        completeness_report,
        manifest_identity,
        manifest_identity_rows,
        contract_health_report,
        contract_health_rows,
    }
}

/// Return an intentionally incomplete Petri handoff fixture for downstream replay tests.
pub fn petri_native_verification_bundle_handoff_incomplete_diagnostic_fixture()
-> PetriNativeVerificationBundleHandoffIncompleteDiagnosticFixture {
    let descriptor = PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_DESCRIPTOR;
    let normalized_rows = descriptor
        .normalized_rows()
        .into_iter()
        .filter(|row| {
            !PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_INCOMPLETE_DIAGNOSTIC_MISSING_ROW_KEYS
                .contains(&row.key.as_str())
        })
        .collect::<Vec<_>>();
    let completeness_report = descriptor.validate_normalized_rows(&normalized_rows);
    let manifest_identity = descriptor.manifest_identity_for_rows(&normalized_rows);
    let contract_health_report = descriptor.contract_health_report_for_rows(&normalized_rows);

    PetriNativeVerificationBundleHandoffIncompleteDiagnosticFixture {
        fixture_name: PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_INCOMPLETE_DIAGNOSTIC_FIXTURE_NAME,
        missing_row_keys:
            PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_INCOMPLETE_DIAGNOSTIC_MISSING_ROW_KEYS,
        normalized_rows,
        completeness_report,
        manifest_identity,
        contract_health_report,
    }
}

/// Return a healthy replay JSON binding fixture for downstream tests.
pub fn petri_native_verification_bundle_handoff_replay_contract_json_manifest_binding_healthy_fixture()
-> PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingFixture {
    petri_native_verification_bundle_handoff_replay_contract_json_manifest_binding_fixture(
        PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_JSON_MANIFEST_BINDING_HEALTHY_FIXTURE_NAME,
        false,
    )
}

/// Return a stale replay JSON binding fixture for downstream fail-closed tests.
pub fn petri_native_verification_bundle_handoff_replay_contract_json_manifest_binding_stale_fixture()
-> PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingFixture {
    petri_native_verification_bundle_handoff_replay_contract_json_manifest_binding_fixture(
        PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_JSON_MANIFEST_BINDING_STALE_FIXTURE_NAME,
        true,
    )
}

pub(crate) fn petri_native_verification_bundle_handoff_replay_contract_json_manifest_binding_fixture(
    fixture_name: &'static str,
    stale_manifest_identity_digest: bool,
) -> PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingFixture {
    let descriptor = PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_DESCRIPTOR;
    let surface = PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_SURFACE;
    let round_trip_report = surface.round_trip_report(&surface.key_value_rows());
    let compact_json_text = round_trip_report.compact_manifest_json_text();
    let mut manifest_identity = descriptor.manifest_identity();
    if stale_manifest_identity_digest {
        manifest_identity.digest = round_trip_report.identity_digest();
    }
    let binding_report =
        round_trip_report.compact_manifest_handoff_identity_report(&manifest_identity);
    let binding_rows = binding_report.key_value_rows();
    let expected_status_code = binding_report.status_code;
    let expected_fail_closed = binding_report.fail_closed;

    PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingFixture {
        fixture_name,
        expected_status_code,
        expected_fail_closed,
        compact_json_text,
        round_trip_report,
        manifest_identity,
        binding_report,
        binding_rows,
    }
}

/// Self-describing Petri successor TrustMc CHC report contract.
///
/// This descriptor gives downstream AY, TrustIr, MCC, and TY adapters one
/// stable TrustIr-owned surface for report schemas, field names, and fail-closed
/// status/reason vocabularies.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PetriSuccessorTrustMcChcContractDescriptor {
    pub schema: &'static str,
    pub schema_version: u32,
    pub formula_schema: &'static str,
    pub binding_report_schema: &'static str,
    pub binding_report_schema_version: u32,
    pub proof_handoff_report_schema: &'static str,
    pub proof_handoff_report_schema_version: u32,
    pub proof_evidence_identity_schema: &'static str,
    pub proof_evidence_identity_schema_version: u32,
    pub proof_evidence_identity_digest_context: &'static str,
    pub proof_evidence_identity_replay_report_schema: &'static str,
    pub proof_evidence_identity_replay_report_schema_version: u32,
    pub model_validation_readiness_report_schema: &'static str,
    pub model_validation_readiness_report_schema_version: u32,
    pub verifier_suite: NativeVerifierSuite,
    pub verification_mode: TrustMcVerificationMode,
    pub binding_required_artifact_kinds: &'static [NativeEvidenceArtifactKind],
    pub proof_handoff_required_artifact_kinds: &'static [NativeEvidenceArtifactKind],
    pub proof_handoff_optional_artifact_kinds: &'static [NativeEvidenceArtifactKind],
    pub model_validation_required_artifact_kinds: &'static [NativeEvidenceArtifactKind],
    pub production_acceptance_required_artifact_kinds: &'static [NativeEvidenceArtifactKind],
    pub model_validation_requires_solver_acceptance: bool,
    pub model_acceptance_report_api_name: &'static str,
    pub consumer_acceptance_api_name: &'static str,
    pub production_acceptance_owner_suite: NativeVerifierSuite,
    /// Policy-light downstream promotion contract for solver-owned acceptance.
    ///
    /// Consumers should prefer this field over reconstructing required
    /// artifacts, readiness schema, acceptance APIs, owner suite, or
    /// solver-acceptance requirements from Petri-specific report fields.
    pub shared_primitive_contract: NativeSharedPrimitiveContractDescriptor,
    pub provided_fields: &'static [&'static str],
    pub binding_status_codes: &'static [&'static str],
    pub binding_reason_codes: &'static [&'static str],
    pub proof_handoff_status_codes: &'static [&'static str],
    pub proof_handoff_reason_codes: &'static [&'static str],
    pub model_validation_readiness_status_codes: &'static [&'static str],
    pub model_validation_readiness_reason_codes: &'static [&'static str],
}

/// Petri successor TrustMc CHC contract consumed by downstream backends.
pub const PETRI_SUCCESSOR_TRUST_MC_CHC_CONTRACT_DESCRIPTOR:
    PetriSuccessorTrustMcChcContractDescriptor = PetriSuccessorTrustMcChcContractDescriptor {
    schema: PETRI_SUCCESSOR_TRUST_MC_CHC_CONTRACT_SCHEMA,
    schema_version: PETRI_SUCCESSOR_TRUST_MC_CHC_CONTRACT_SCHEMA_VERSION,
    formula_schema: PETRI_SUCCESSOR_PLAN_CACHE_EQUIVALENCE_SCHEMA,
    binding_report_schema: PETRI_SUCCESSOR_TRUST_MC_CHC_BINDING_SCHEMA,
    binding_report_schema_version: PETRI_SUCCESSOR_TRUST_MC_CHC_BINDING_SCHEMA_VERSION,
    proof_handoff_report_schema: PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_HANDOFF_SCHEMA,
    proof_handoff_report_schema_version: PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_HANDOFF_SCHEMA_VERSION,
    proof_evidence_identity_schema: PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_SCHEMA,
    proof_evidence_identity_schema_version:
        PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_SCHEMA_VERSION,
    proof_evidence_identity_digest_context:
        PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_DIGEST_CONTEXT,
    proof_evidence_identity_replay_report_schema:
        PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_REPLAY_REPORT_SCHEMA,
    proof_evidence_identity_replay_report_schema_version:
        PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_REPLAY_REPORT_SCHEMA_VERSION,
    model_validation_readiness_report_schema:
        PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_VALIDATION_READINESS_SCHEMA,
    model_validation_readiness_report_schema_version:
        PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_VALIDATION_READINESS_SCHEMA_VERSION,
    verifier_suite: PETRI_SUCCESSOR_TRUST_MC_CHC_CONTRACT_VERIFIER_SUITE,
    verification_mode: PETRI_SUCCESSOR_TRUST_MC_CHC_CONTRACT_VERIFICATION_MODE,
    binding_required_artifact_kinds: PETRI_SUCCESSOR_TRUST_MC_CHC_BINDING_REQUIRED_ARTIFACT_KINDS,
    proof_handoff_required_artifact_kinds:
        PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_HANDOFF_REQUIRED_ARTIFACT_KINDS,
    proof_handoff_optional_artifact_kinds:
        PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_HANDOFF_OPTIONAL_ARTIFACT_KINDS,
    model_validation_required_artifact_kinds:
        PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_VALIDATION_REQUIRED_ARTIFACT_KINDS,
    production_acceptance_required_artifact_kinds:
        PETRI_SUCCESSOR_TRUST_MC_CHC_PRODUCTION_ACCEPTANCE_REQUIRED_ARTIFACT_KINDS,
    model_validation_requires_solver_acceptance:
        PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_VALIDATION_REQUIRES_SOLVER_ACCEPTANCE,
    model_acceptance_report_api_name: PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_ACCEPTANCE_REPORT_API_NAME,
    consumer_acceptance_api_name: PETRI_SUCCESSOR_TRUST_MC_CHC_CONSUMER_ACCEPTANCE_API_NAME,
    production_acceptance_owner_suite:
        PETRI_SUCCESSOR_TRUST_MC_CHC_PRODUCTION_ACCEPTANCE_OWNER_SUITE,
    shared_primitive_contract: PETRI_SUCCESSOR_TRUST_MC_CHC_SHARED_PRIMITIVE_CONTRACT_DESCRIPTOR,
    provided_fields: PETRI_SUCCESSOR_TRUST_MC_CHC_CONTRACT_PROVIDED_FIELDS,
    binding_status_codes: PETRI_SUCCESSOR_TRUST_MC_CHC_BINDING_STATUS_CODES,
    binding_reason_codes: PETRI_SUCCESSOR_TRUST_MC_CHC_BINDING_REASON_CODES,
    proof_handoff_status_codes: PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_HANDOFF_STATUS_CODES,
    proof_handoff_reason_codes: PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_HANDOFF_REASON_CODES,
    model_validation_readiness_status_codes:
        PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_VALIDATION_READINESS_STATUS_CODES,
    model_validation_readiness_reason_codes:
        PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_VALIDATION_READINESS_REASON_CODES,
};

/// Return the Petri successor TrustMc CHC report contract for downstream backends.
pub const fn petri_successor_trust_mc_chc_contract_descriptor()
-> PetriSuccessorTrustMcChcContractDescriptor {
    PETRI_SUCCESSOR_TRUST_MC_CHC_CONTRACT_DESCRIPTOR
}

/// Transport/digest/ABI identity for a native verification bundle.
///
/// This is a read-only handoff view for downstream consumers that need to bind
/// admissions to TrustIr-owned digest facts without re-deriving private guesses.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeTransportIdentity {
    pub schema: String,
    pub schema_version: u32,
    pub bundle_schema_version: u32,
    pub producer: NativeBundleProducer,
    pub input: NativeAdapterInput,
    pub source_digest: Option<ProofDigest>,
    pub trust_ir_module_digest: ProofDigest,
    pub compiler_facts_digest: ProofDigest,
    pub lineage_digest: ProofDigest,
    pub bundle_digest: ProofDigest,
    pub target_abi: Option<NativeTargetAbiIdentity>,
    pub request_digests: Vec<NativeRequestDigestIdentity>,
    pub evidence_digests: Vec<NativeEvidenceDigestIdentity>,
}

impl NativeTransportIdentity {
    pub fn from_bundle(bundle: &NativeVerificationBundle) -> Self {
        let mut request_digests: Vec<_> = bundle
            .requests
            .iter()
            .map(|request| NativeRequestDigestIdentity {
                request: request.id(),
                suite: request.verifier_suite(),
                digest: request.stable_digest(),
            })
            .collect();
        request_digests.sort_by_key(|entry| (entry.request, entry.suite));

        let mut evidence_digests: Vec<_> = bundle
            .evidence_bundles
            .iter()
            .map(|evidence| NativeEvidenceDigestIdentity {
                request: evidence.request(),
                suite: evidence.verifier_suite(),
                digest: evidence.stable_digest(),
            })
            .collect();
        evidence_digests.sort_by_key(|entry| (entry.request, entry.suite));

        Self {
            schema: NATIVE_TRANSPORT_IDENTITY_SCHEMA.to_string(),
            schema_version: NATIVE_TRANSPORT_IDENTITY_SCHEMA_VERSION,
            bundle_schema_version: bundle.schema_version,
            producer: bundle.producer,
            input: bundle.input,
            source_digest: bundle.source_digest(),
            trust_ir_module_digest: bundle.trust_ir_module_digest,
            compiler_facts_digest: bundle.compiler_facts.stable_digest(),
            lineage_digest: bundle.lineage.stable_digest(),
            bundle_digest: bundle.stable_digest(),
            target_abi: bundle.target_abi_identity(),
            request_digests,
            evidence_digests,
        }
    }

    pub fn stable_digest(&self) -> ProofDigest {
        let mut bytes = Vec::new();
        write_str_stable(&mut bytes, &self.schema);
        write_u32_stable(&mut bytes, self.schema_version);
        write_u32_stable(&mut bytes, self.bundle_schema_version);
        write_bundle_producer_stable(&mut bytes, self.producer);
        write_adapter_input_stable(&mut bytes, &self.input);
        write_option_digest_stable(&mut bytes, self.source_digest);
        write_digest_stable(&mut bytes, &self.trust_ir_module_digest);
        write_digest_stable(&mut bytes, &self.compiler_facts_digest);
        write_digest_stable(&mut bytes, &self.lineage_digest);
        write_digest_stable(&mut bytes, &self.bundle_digest);
        match &self.target_abi {
            None => write_u8_stable(&mut bytes, 0),
            Some(target_abi) => {
                write_u8_stable(&mut bytes, 1);
                write_target_abi_identity_stable(&mut bytes, target_abi);
            }
        }

        let mut request_digests: Vec<&NativeRequestDigestIdentity> =
            self.request_digests.iter().collect();
        request_digests.sort_by_key(|entry| (entry.request, entry.suite));
        write_len_stable(&mut bytes, request_digests.len());
        for entry in request_digests {
            write_u32_stable(&mut bytes, entry.request.index());
            write_verifier_suite_stable(&mut bytes, entry.suite);
            write_digest_stable(&mut bytes, &entry.digest);
        }

        let mut evidence_digests: Vec<&NativeEvidenceDigestIdentity> =
            self.evidence_digests.iter().collect();
        evidence_digests.sort_by_key(|entry| (entry.request, entry.suite));
        write_len_stable(&mut bytes, evidence_digests.len());
        for entry in evidence_digests {
            write_u32_stable(&mut bytes, entry.request.index());
            write_verifier_suite_stable(&mut bytes, entry.suite);
            write_digest_stable(&mut bytes, &entry.digest);
        }

        ProofDigest::sha256_domain("trust_ir.native.transport_identity.v2", &bytes)
    }

    /// Emit stable transport identity rows for sidecar persistence.
    pub fn identity_rows(&self) -> Vec<NativeSharedPrimitiveContractManifestRow> {
        let mut rows = Vec::new();
        let identity_digest = self.stable_digest();

        push_manifest_row(&mut rows, "transport_identity.schema", self.schema.as_str());
        push_manifest_row(
            &mut rows,
            "transport_identity.schema_version",
            self.schema_version.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "transport_identity.digest.context",
            NATIVE_TRANSPORT_IDENTITY_SCHEMA,
        );
        push_manifest_row(
            &mut rows,
            "transport_identity.digest.algorithm",
            proof_digest_algorithm_code(identity_digest.algorithm),
        );
        push_manifest_row(
            &mut rows,
            "transport_identity.digest",
            identity_digest.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "transport_identity.bundle.schema_version",
            self.bundle_schema_version.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "transport_identity.producer",
            native_bundle_producer_code(self.producer),
        );
        push_manifest_row(
            &mut rows,
            "transport_identity.input.kind",
            native_adapter_input_code(&self.input),
        );
        push_optional_digest_manifest_row(
            &mut rows,
            "transport_identity.input.rust_mir.body_digest",
            match self.input {
                NativeAdapterInput::RustMir { body_digest } => Some(body_digest),
                NativeAdapterInput::TrustIrModule => None,
            },
        );
        push_optional_digest_manifest_row(
            &mut rows,
            "transport_identity.source_digest",
            self.source_digest,
        );
        push_manifest_row(
            &mut rows,
            "transport_identity.trust_ir_module_digest",
            self.trust_ir_module_digest.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "transport_identity.compiler_facts_digest",
            self.compiler_facts_digest.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "transport_identity.lineage_digest",
            self.lineage_digest.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "transport_identity.bundle_digest",
            self.bundle_digest.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "transport_identity.target_abi.present",
            bool_code(self.target_abi.is_some()),
        );
        push_manifest_row(
            &mut rows,
            "transport_identity.target_abi.triple",
            self.target_abi
                .as_ref()
                .map(|target_abi| target_abi.triple.as_str())
                .unwrap_or("none"),
        );
        push_manifest_row(
            &mut rows,
            "transport_identity.target_abi.pointer_size",
            self.target_abi
                .as_ref()
                .map(|target_abi| target_abi.pointer_size.to_string())
                .unwrap_or_else(|| "none".to_string()),
        );
        push_manifest_row(
            &mut rows,
            "transport_identity.target_abi.endianness",
            self.target_abi
                .as_ref()
                .map(|target_abi| target_abi.endianness.to_string())
                .unwrap_or_else(|| "none".to_string()),
        );
        push_optional_digest_manifest_row(
            &mut rows,
            "transport_identity.target_abi.digest",
            self.target_abi.as_ref().map(|target_abi| target_abi.digest),
        );

        let mut request_digests = self.request_digests.iter().collect::<Vec<_>>();
        request_digests.sort_by_key(|entry| (entry.request, entry.suite));
        push_manifest_row(
            &mut rows,
            "transport_identity.request_digest.count",
            request_digests.len().to_string(),
        );
        for (index, entry) in request_digests.iter().enumerate() {
            push_manifest_row(
                &mut rows,
                format!("transport_identity.request_digest.{index}.request"),
                entry.request.index().to_string(),
            );
            push_manifest_row(
                &mut rows,
                format!("transport_identity.request_digest.{index}.suite"),
                entry.suite.code(),
            );
            push_manifest_row(
                &mut rows,
                format!("transport_identity.request_digest.{index}.digest"),
                entry.digest.to_string(),
            );
        }

        let mut evidence_digests = self.evidence_digests.iter().collect::<Vec<_>>();
        evidence_digests.sort_by_key(|entry| (entry.request, entry.suite));
        push_manifest_row(
            &mut rows,
            "transport_identity.evidence_digest.count",
            evidence_digests.len().to_string(),
        );
        for (index, entry) in evidence_digests.iter().enumerate() {
            push_manifest_row(
                &mut rows,
                format!("transport_identity.evidence_digest.{index}.request"),
                entry.request.index().to_string(),
            );
            push_manifest_row(
                &mut rows,
                format!("transport_identity.evidence_digest.{index}.suite"),
                entry.suite.code(),
            );
            push_manifest_row(
                &mut rows,
                format!("transport_identity.evidence_digest.{index}.digest"),
                entry.digest.to_string(),
            );
        }

        rows
    }

    /// Emit escaped `key=value` transport identity rows.
    pub fn identity_key_value_lines(&self) -> Vec<String> {
        self.identity_rows()
            .into_iter()
            .map(|row| row.to_key_value_line())
            .collect()
    }

    /// Emit stable line-oriented transport identity text.
    pub fn identity_key_value_text(&self) -> String {
        format!("{}\n", self.identity_key_value_lines().join("\n"))
    }

    /// Validate persisted transport identity rows against this identity.
    pub fn identity_replay_report(
        &self,
        rows: &[NativeSharedPrimitiveContractManifestRow],
    ) -> NativeTransportIdentityReplayReport {
        self.identity_replay_report_with_invalid_lines(rows, Vec::new())
    }

    /// Validate persisted transport identity `key=value` lines.
    pub fn identity_replay_report_for_key_value_lines(
        &self,
        lines: &[String],
    ) -> NativeTransportIdentityReplayReport {
        let mut invalid_lines = Vec::new();
        let mut rows = Vec::new();
        for (index, line) in lines.iter().enumerate() {
            if let Some((key, value)) = line.split_once('=') {
                rows.push(NativeSharedPrimitiveContractManifestRow::new(key, value));
            } else {
                invalid_lines.push(format!("{index}:{line}"));
            }
        }

        self.identity_replay_report_with_invalid_lines(&rows, invalid_lines)
    }

    /// Validate persisted transport identity line-oriented text.
    pub fn identity_replay_report_for_key_value_text(
        &self,
        text: &str,
    ) -> NativeTransportIdentityReplayReport {
        let lines = text.lines().map(str::to_string).collect::<Vec<_>>();
        self.identity_replay_report_for_key_value_lines(&lines)
    }

    fn identity_replay_report_with_invalid_lines(
        &self,
        rows: &[NativeSharedPrimitiveContractManifestRow],
        invalid_lines: Vec<String>,
    ) -> NativeTransportIdentityReplayReport {
        let expected_rows = self.identity_rows();
        let expected_by_key = expected_rows
            .iter()
            .map(|row| (row.key.as_str(), row.value.as_str()))
            .collect::<BTreeMap<_, _>>();
        let mut observed_by_key = BTreeMap::<&str, Vec<&str>>::new();
        for row in rows {
            observed_by_key
                .entry(row.key.as_str())
                .or_default()
                .push(row.value.as_str());
        }

        let (duplicate_keys, missing_keys, unexpected_keys, mismatched_value_keys) =
            replay_key_diagnostics(&expected_by_key, &observed_by_key);

        let mut invalid_bool_keys = Vec::new();
        let mut invalid_usize_keys = Vec::new();
        let reconstructed_schema =
            observed_single_value(&observed_by_key, "transport_identity.schema")
                .map(str::to_string);
        let reconstructed_schema_version = observed_usize_value(
            &observed_by_key,
            "transport_identity.schema_version",
            &mut invalid_usize_keys,
        );
        let reconstructed_identity_digest =
            observed_single_value(&observed_by_key, "transport_identity.digest")
                .map(str::to_string);
        let reconstructed_bundle_digest =
            observed_single_value(&observed_by_key, "transport_identity.bundle_digest")
                .map(str::to_string);
        let reconstructed_request_digest_count = observed_usize_value(
            &observed_by_key,
            "transport_identity.request_digest.count",
            &mut invalid_usize_keys,
        );
        let reconstructed_evidence_digest_count = observed_usize_value(
            &observed_by_key,
            "transport_identity.evidence_digest.count",
            &mut invalid_usize_keys,
        );

        {
            let key = "transport_identity.bundle.schema_version";
            let _ = observed_usize_value(&observed_by_key, key, &mut invalid_usize_keys);
        }
        if observed_single_value(
            &observed_by_key,
            "transport_identity.target_abi.pointer_size",
        )
        .is_some_and(|value| value != "none")
        {
            let _ = observed_usize_value(
                &observed_by_key,
                "transport_identity.target_abi.pointer_size",
                &mut invalid_usize_keys,
            );
        }
        let _ = observed_bool_value(
            &observed_by_key,
            "transport_identity.target_abi.present",
            &mut invalid_bool_keys,
        );
        for index in 0..reconstructed_request_digest_count.unwrap_or(0) {
            let key = format!("transport_identity.request_digest.{index}.request");
            let _ = observed_usize_value(&observed_by_key, &key, &mut invalid_usize_keys);
        }
        for index in 0..reconstructed_evidence_digest_count.unwrap_or(0) {
            let key = format!("transport_identity.evidence_digest.{index}.request");
            let _ = observed_usize_value(&observed_by_key, &key, &mut invalid_usize_keys);
        }

        let expected_identity_digest = self.stable_digest().to_string();
        let expected_bundle_digest = self.bundle_digest.to_string();
        let schema_matches = reconstructed_schema.as_deref()
            == Some(NATIVE_TRANSPORT_IDENTITY_SCHEMA)
            && reconstructed_schema_version
                == Some(NATIVE_TRANSPORT_IDENTITY_SCHEMA_VERSION as usize);
        let identity_digest_matches =
            reconstructed_identity_digest.as_deref() == Some(expected_identity_digest.as_str());
        let bundle_digest_matches =
            reconstructed_bundle_digest.as_deref() == Some(expected_bundle_digest.as_str());
        let request_digest_count_matches =
            reconstructed_request_digest_count == Some(self.request_digests.len());
        let evidence_digest_count_matches =
            reconstructed_evidence_digest_count == Some(self.evidence_digests.len());

        let status = if rows.len() == expected_rows.len()
            && duplicate_keys.is_empty()
            && missing_keys.is_empty()
            && unexpected_keys.is_empty()
            && mismatched_value_keys.is_empty()
            && invalid_bool_keys.is_empty()
            && invalid_usize_keys.is_empty()
            && invalid_lines.is_empty()
            && schema_matches
            && identity_digest_matches
            && bundle_digest_matches
            && request_digest_count_matches
            && evidence_digest_count_matches
        {
            NativeTransportIdentityReplayStatus::Replayable
        } else {
            NativeTransportIdentityReplayStatus::Invalid
        };

        NativeTransportIdentityReplayReport {
            status,
            status_code: status.code(),
            fail_closed: !matches!(status, NativeTransportIdentityReplayStatus::Replayable),
            expected_row_count: expected_rows.len(),
            observed_row_count: rows.len(),
            unique_key_count: observed_by_key.len(),
            duplicate_keys,
            missing_keys,
            unexpected_keys,
            mismatched_value_keys,
            invalid_bool_keys,
            invalid_usize_keys,
            invalid_lines,
            reconstructed_schema,
            reconstructed_schema_version,
            reconstructed_identity_digest,
            reconstructed_bundle_digest,
            reconstructed_request_digest_count,
            reconstructed_evidence_digest_count,
            schema_matches,
            identity_digest_matches,
            bundle_digest_matches,
            request_digest_count_matches,
            evidence_digest_count_matches,
        }
    }
}

/// Replay-validation status for persisted transport identity rows.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum NativeTransportIdentityReplayStatus {
    Replayable,
    Invalid,
}

impl NativeTransportIdentityReplayStatus {
    pub const fn code(self) -> &'static str {
        match self {
            NativeTransportIdentityReplayStatus::Replayable => "replayable",
            NativeTransportIdentityReplayStatus::Invalid => "invalid",
        }
    }

    pub const fn name(self) -> &'static str {
        match self {
            NativeTransportIdentityReplayStatus::Replayable => "transport identity rows replayable",
            NativeTransportIdentityReplayStatus::Invalid => "transport identity rows invalid",
        }
    }
}

impl core::fmt::Display for NativeTransportIdentityReplayStatus {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.code())
    }
}

/// Round-trip status for persisted transport identity health summaries.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum NativeTransportIdentityReplayHealthSummaryRoundTripStatus {
    Valid,
    Invalid,
}

impl NativeTransportIdentityReplayHealthSummaryRoundTripStatus {
    pub const fn code(self) -> &'static str {
        match self {
            NativeTransportIdentityReplayHealthSummaryRoundTripStatus::Valid => "valid",
            NativeTransportIdentityReplayHealthSummaryRoundTripStatus::Invalid => "invalid",
        }
    }

    pub const fn name(self) -> &'static str {
        match self {
            NativeTransportIdentityReplayHealthSummaryRoundTripStatus::Valid => {
                "transport identity replay health summary valid"
            }
            NativeTransportIdentityReplayHealthSummaryRoundTripStatus::Invalid => {
                "transport identity replay health summary invalid"
            }
        }
    }
}

impl core::fmt::Display for NativeTransportIdentityReplayHealthSummaryRoundTripStatus {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.code())
    }
}

/// Validation report for persisted transport identity health summaries.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeTransportIdentityReplayHealthSummaryRoundTripReport {
    pub status: NativeTransportIdentityReplayHealthSummaryRoundTripStatus,
    pub status_code: &'static str,
    pub fail_closed: bool,
    pub expected_row_count: usize,
    pub observed_row_count: usize,
    pub unique_key_count: usize,
    pub duplicate_keys: Vec<String>,
    pub missing_keys: Vec<String>,
    pub unexpected_keys: Vec<String>,
    pub mismatched_value_keys: Vec<String>,
    pub invalid_bool_keys: Vec<String>,
    pub invalid_usize_keys: Vec<String>,
    pub invalid_lines: Vec<String>,
    pub reconstructed_schema: Option<String>,
    pub reconstructed_schema_version: Option<usize>,
    pub reconstructed_status: Option<String>,
    pub reconstructed_fail_closed: Option<bool>,
    pub reconstructed_diagnostic_count: Option<usize>,
    pub schema_matches: bool,
    pub status_matches: bool,
    pub fail_closed_matches: bool,
    pub diagnostic_count_matches: bool,
}

impl NativeTransportIdentityReplayHealthSummaryRoundTripReport {
    pub fn is_valid(&self) -> bool {
        matches!(
            self.status,
            NativeTransportIdentityReplayHealthSummaryRoundTripStatus::Valid
        ) && !self.fail_closed
    }

    pub fn diagnostic_count(&self) -> usize {
        self.duplicate_keys.len()
            + self.missing_keys.len()
            + self.unexpected_keys.len()
            + self.mismatched_value_keys.len()
            + self.invalid_bool_keys.len()
            + self.invalid_usize_keys.len()
            + self.invalid_lines.len()
    }
}

/// Validation report for persisted transport identity rows.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeTransportIdentityReplayReport {
    pub status: NativeTransportIdentityReplayStatus,
    pub status_code: &'static str,
    pub fail_closed: bool,
    pub expected_row_count: usize,
    pub observed_row_count: usize,
    pub unique_key_count: usize,
    pub duplicate_keys: Vec<String>,
    pub missing_keys: Vec<String>,
    pub unexpected_keys: Vec<String>,
    pub mismatched_value_keys: Vec<String>,
    pub invalid_bool_keys: Vec<String>,
    pub invalid_usize_keys: Vec<String>,
    pub invalid_lines: Vec<String>,
    pub reconstructed_schema: Option<String>,
    pub reconstructed_schema_version: Option<usize>,
    pub reconstructed_identity_digest: Option<String>,
    pub reconstructed_bundle_digest: Option<String>,
    pub reconstructed_request_digest_count: Option<usize>,
    pub reconstructed_evidence_digest_count: Option<usize>,
    pub schema_matches: bool,
    pub identity_digest_matches: bool,
    pub bundle_digest_matches: bool,
    pub request_digest_count_matches: bool,
    pub evidence_digest_count_matches: bool,
}

impl NativeTransportIdentityReplayReport {
    pub fn is_replayable(&self) -> bool {
        matches!(self.status, NativeTransportIdentityReplayStatus::Replayable) && !self.fail_closed
    }

    pub fn diagnostic_count(&self) -> usize {
        self.duplicate_keys.len()
            + self.missing_keys.len()
            + self.unexpected_keys.len()
            + self.mismatched_value_keys.len()
            + self.invalid_bool_keys.len()
            + self.invalid_usize_keys.len()
            + self.invalid_lines.len()
    }

    /// Emit deterministic health rows for transport identity sidecar persistence.
    pub fn compact_health_summary_rows(&self) -> Vec<NativeSharedPrimitiveContractManifestRow> {
        let mut rows = Vec::new();
        push_manifest_row(
            &mut rows,
            "transport_identity_replay_report.schema",
            NATIVE_TRANSPORT_IDENTITY_SCHEMA,
        );
        push_manifest_row(
            &mut rows,
            "transport_identity_replay_report.schema_version",
            NATIVE_TRANSPORT_IDENTITY_SCHEMA_VERSION.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "transport_identity_replay_report.status",
            self.status_code,
        );
        push_manifest_row(
            &mut rows,
            "transport_identity_replay_report.fail_closed",
            bool_code(self.fail_closed),
        );
        push_manifest_row(
            &mut rows,
            "transport_identity_replay_report.count.expected_rows",
            self.expected_row_count.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "transport_identity_replay_report.count.observed_rows",
            self.observed_row_count.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "transport_identity_replay_report.count.unique_keys",
            self.unique_key_count.to_string(),
        );
        push_manifest_row(
            &mut rows,
            "transport_identity_replay_report.count.diagnostics",
            self.diagnostic_count().to_string(),
        );
        push_manifest_row(
            &mut rows,
            "transport_identity_replay_report.reconstructed.schema",
            self.reconstructed_schema.as_deref().unwrap_or("none"),
        );
        push_manifest_row(
            &mut rows,
            "transport_identity_replay_report.reconstructed.schema_version",
            self.reconstructed_schema_version
                .map(|version| version.to_string())
                .unwrap_or_else(|| "none".to_string()),
        );
        push_manifest_row(
            &mut rows,
            "transport_identity_replay_report.reconstructed.identity_digest",
            self.reconstructed_identity_digest
                .as_deref()
                .unwrap_or("none"),
        );
        push_manifest_row(
            &mut rows,
            "transport_identity_replay_report.reconstructed.bundle_digest",
            self.reconstructed_bundle_digest
                .as_deref()
                .unwrap_or("none"),
        );
        push_manifest_row(
            &mut rows,
            "transport_identity_replay_report.reconstructed.request_digest.count",
            self.reconstructed_request_digest_count
                .map(|count| count.to_string())
                .unwrap_or_else(|| "none".to_string()),
        );
        push_manifest_row(
            &mut rows,
            "transport_identity_replay_report.reconstructed.evidence_digest.count",
            self.reconstructed_evidence_digest_count
                .map(|count| count.to_string())
                .unwrap_or_else(|| "none".to_string()),
        );
        push_manifest_row(
            &mut rows,
            "transport_identity_replay_report.agreement.schema",
            bool_code(self.schema_matches),
        );
        push_manifest_row(
            &mut rows,
            "transport_identity_replay_report.agreement.identity_digest",
            bool_code(self.identity_digest_matches),
        );
        push_manifest_row(
            &mut rows,
            "transport_identity_replay_report.agreement.bundle_digest",
            bool_code(self.bundle_digest_matches),
        );
        push_manifest_row(
            &mut rows,
            "transport_identity_replay_report.agreement.request_digest_count",
            bool_code(self.request_digest_count_matches),
        );
        push_manifest_row(
            &mut rows,
            "transport_identity_replay_report.agreement.evidence_digest_count",
            bool_code(self.evidence_digest_count_matches),
        );
        push_manifest_row(
            &mut rows,
            "transport_identity_replay_report.diagnostic.duplicate_keys",
            self.duplicate_keys.len().to_string(),
        );
        push_manifest_row(
            &mut rows,
            "transport_identity_replay_report.diagnostic.missing_keys",
            self.missing_keys.len().to_string(),
        );
        push_manifest_row(
            &mut rows,
            "transport_identity_replay_report.diagnostic.unexpected_keys",
            self.unexpected_keys.len().to_string(),
        );
        push_manifest_row(
            &mut rows,
            "transport_identity_replay_report.diagnostic.mismatched_value_keys",
            self.mismatched_value_keys.len().to_string(),
        );
        push_manifest_row(
            &mut rows,
            "transport_identity_replay_report.diagnostic.invalid_bool_keys",
            self.invalid_bool_keys.len().to_string(),
        );
        push_manifest_row(
            &mut rows,
            "transport_identity_replay_report.diagnostic.invalid_usize_keys",
            self.invalid_usize_keys.len().to_string(),
        );
        push_manifest_row(
            &mut rows,
            "transport_identity_replay_report.diagnostic.invalid_lines",
            self.invalid_lines.len().to_string(),
        );

        rows
    }

    /// Emit escaped `key=value` rows for transport health persistence.
    pub fn compact_health_summary_key_value_lines(&self) -> Vec<String> {
        self.compact_health_summary_rows()
            .into_iter()
            .map(|row| row.to_key_value_line())
            .collect()
    }

    /// Emit stable line-oriented transport replay health text.
    pub fn compact_health_summary_key_value_text(&self) -> String {
        format!(
            "{}\n",
            self.compact_health_summary_key_value_lines().join("\n")
        )
    }

    /// Emit compact JSON for non-Rust sidecar validation.
    pub fn compact_health_summary_json_text(&self) -> String {
        let optional_string = |value: Option<&str>| {
            value
                .map(json_string_literal)
                .unwrap_or_else(|| "null".to_string())
        };
        let optional_usize = |value: Option<usize>| {
            value
                .map(|value| value.to_string())
                .unwrap_or_else(|| "null".to_string())
        };

        format!(
            "{{\"schema\":{},\"schema_version\":{},\"status\":{},\"fail_closed\":{},\"expected_row_count\":{},\"observed_row_count\":{},\"unique_key_count\":{},\"diagnostic_count\":{},\"reconstructed_schema\":{},\"reconstructed_schema_version\":{},\"reconstructed_identity_digest\":{},\"reconstructed_bundle_digest\":{},\"reconstructed_request_digest_count\":{},\"reconstructed_evidence_digest_count\":{},\"schema_matches\":{},\"identity_digest_matches\":{},\"bundle_digest_matches\":{},\"request_digest_count_matches\":{},\"evidence_digest_count_matches\":{},\"duplicate_key_count\":{},\"missing_key_count\":{},\"unexpected_key_count\":{},\"mismatched_value_key_count\":{},\"invalid_bool_key_count\":{},\"invalid_usize_key_count\":{},\"invalid_line_count\":{}}}\n",
            json_string_literal(NATIVE_TRANSPORT_IDENTITY_SCHEMA),
            NATIVE_TRANSPORT_IDENTITY_SCHEMA_VERSION,
            json_string_literal(self.status_code),
            bool_code(self.fail_closed),
            self.expected_row_count,
            self.observed_row_count,
            self.unique_key_count,
            self.diagnostic_count(),
            optional_string(self.reconstructed_schema.as_deref()),
            optional_usize(self.reconstructed_schema_version),
            optional_string(self.reconstructed_identity_digest.as_deref()),
            optional_string(self.reconstructed_bundle_digest.as_deref()),
            optional_usize(self.reconstructed_request_digest_count),
            optional_usize(self.reconstructed_evidence_digest_count),
            bool_code(self.schema_matches),
            bool_code(self.identity_digest_matches),
            bool_code(self.bundle_digest_matches),
            bool_code(self.request_digest_count_matches),
            bool_code(self.evidence_digest_count_matches),
            self.duplicate_keys.len(),
            self.missing_keys.len(),
            self.unexpected_keys.len(),
            self.mismatched_value_keys.len(),
            self.invalid_bool_keys.len(),
            self.invalid_usize_keys.len(),
            self.invalid_lines.len()
        )
    }

    /// Validate persisted transport health rows against this replay report.
    pub fn compact_health_summary_round_trip_report(
        &self,
        rows: &[NativeSharedPrimitiveContractManifestRow],
    ) -> NativeTransportIdentityReplayHealthSummaryRoundTripReport {
        self.compact_health_summary_round_trip_report_with_invalid_lines(rows, Vec::new())
    }

    /// Validate persisted transport health `key=value` lines.
    pub fn compact_health_summary_round_trip_report_for_key_value_lines(
        &self,
        lines: &[String],
    ) -> NativeTransportIdentityReplayHealthSummaryRoundTripReport {
        let mut invalid_lines = Vec::new();
        let mut rows = Vec::new();
        for (index, line) in lines.iter().enumerate() {
            if let Some((key, value)) = line.split_once('=') {
                rows.push(NativeSharedPrimitiveContractManifestRow::new(key, value));
            } else {
                invalid_lines.push(format!("{index}:{line}"));
            }
        }

        self.compact_health_summary_round_trip_report_with_invalid_lines(&rows, invalid_lines)
    }

    /// Validate persisted transport health line-oriented text.
    pub fn compact_health_summary_round_trip_report_for_key_value_text(
        &self,
        text: &str,
    ) -> NativeTransportIdentityReplayHealthSummaryRoundTripReport {
        let lines = text.lines().map(str::to_string).collect::<Vec<_>>();
        self.compact_health_summary_round_trip_report_for_key_value_lines(&lines)
    }

    fn compact_health_summary_round_trip_report_with_invalid_lines(
        &self,
        rows: &[NativeSharedPrimitiveContractManifestRow],
        invalid_lines: Vec<String>,
    ) -> NativeTransportIdentityReplayHealthSummaryRoundTripReport {
        let expected_rows = self.compact_health_summary_rows();
        let expected_by_key = expected_rows
            .iter()
            .map(|row| (row.key.as_str(), row.value.as_str()))
            .collect::<BTreeMap<_, _>>();
        let mut observed_by_key = BTreeMap::<&str, Vec<&str>>::new();
        for row in rows {
            observed_by_key
                .entry(row.key.as_str())
                .or_default()
                .push(row.value.as_str());
        }

        let (duplicate_keys, missing_keys, unexpected_keys, mismatched_value_keys) =
            replay_key_diagnostics(&expected_by_key, &observed_by_key);

        let mut invalid_bool_keys = Vec::new();
        let mut invalid_usize_keys = Vec::new();
        let reconstructed_schema =
            observed_single_value(&observed_by_key, "transport_identity_replay_report.schema")
                .map(str::to_string);
        let reconstructed_schema_version = observed_usize_value(
            &observed_by_key,
            "transport_identity_replay_report.schema_version",
            &mut invalid_usize_keys,
        );
        let reconstructed_status =
            observed_single_value(&observed_by_key, "transport_identity_replay_report.status")
                .map(str::to_string);
        let reconstructed_fail_closed = observed_bool_value(
            &observed_by_key,
            "transport_identity_replay_report.fail_closed",
            &mut invalid_bool_keys,
        );
        let reconstructed_diagnostic_count = observed_usize_value(
            &observed_by_key,
            "transport_identity_replay_report.count.diagnostics",
            &mut invalid_usize_keys,
        );

        for key in [
            "transport_identity_replay_report.count.expected_rows",
            "transport_identity_replay_report.count.observed_rows",
            "transport_identity_replay_report.count.unique_keys",
            "transport_identity_replay_report.reconstructed.schema_version",
            "transport_identity_replay_report.reconstructed.request_digest.count",
            "transport_identity_replay_report.reconstructed.evidence_digest.count",
            "transport_identity_replay_report.diagnostic.duplicate_keys",
            "transport_identity_replay_report.diagnostic.missing_keys",
            "transport_identity_replay_report.diagnostic.unexpected_keys",
            "transport_identity_replay_report.diagnostic.mismatched_value_keys",
            "transport_identity_replay_report.diagnostic.invalid_bool_keys",
            "transport_identity_replay_report.diagnostic.invalid_usize_keys",
            "transport_identity_replay_report.diagnostic.invalid_lines",
        ] {
            let _ = observed_usize_value(&observed_by_key, key, &mut invalid_usize_keys);
        }

        for key in [
            "transport_identity_replay_report.agreement.schema",
            "transport_identity_replay_report.agreement.identity_digest",
            "transport_identity_replay_report.agreement.bundle_digest",
            "transport_identity_replay_report.agreement.request_digest_count",
            "transport_identity_replay_report.agreement.evidence_digest_count",
        ] {
            let _ = observed_bool_value(&observed_by_key, key, &mut invalid_bool_keys);
        }

        let schema_matches = reconstructed_schema.as_deref()
            == Some(NATIVE_TRANSPORT_IDENTITY_SCHEMA)
            && reconstructed_schema_version
                == Some(NATIVE_TRANSPORT_IDENTITY_SCHEMA_VERSION as usize);
        let status_matches = reconstructed_status.as_deref() == Some(self.status_code);
        let fail_closed_matches = reconstructed_fail_closed == Some(self.fail_closed);
        let diagnostic_count_matches =
            reconstructed_diagnostic_count == Some(self.diagnostic_count());

        let status = if rows.len() == expected_rows.len()
            && duplicate_keys.is_empty()
            && missing_keys.is_empty()
            && unexpected_keys.is_empty()
            && mismatched_value_keys.is_empty()
            && invalid_bool_keys.is_empty()
            && invalid_usize_keys.is_empty()
            && invalid_lines.is_empty()
            && schema_matches
            && status_matches
            && fail_closed_matches
            && diagnostic_count_matches
        {
            NativeTransportIdentityReplayHealthSummaryRoundTripStatus::Valid
        } else {
            NativeTransportIdentityReplayHealthSummaryRoundTripStatus::Invalid
        };

        NativeTransportIdentityReplayHealthSummaryRoundTripReport {
            status,
            status_code: status.code(),
            fail_closed: !matches!(
                status,
                NativeTransportIdentityReplayHealthSummaryRoundTripStatus::Valid
            ),
            expected_row_count: expected_rows.len(),
            observed_row_count: rows.len(),
            unique_key_count: observed_by_key.len(),
            duplicate_keys,
            missing_keys,
            unexpected_keys,
            mismatched_value_keys,
            invalid_bool_keys,
            invalid_usize_keys,
            invalid_lines,
            reconstructed_schema,
            reconstructed_schema_version,
            reconstructed_status,
            reconstructed_fail_closed,
            reconstructed_diagnostic_count,
            schema_matches,
            status_matches,
            fail_closed_matches,
            diagnostic_count_matches,
        }
    }
}
