// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use std::sync::Arc;

/// Native request bundle produced by a frontend and consumed by proof tools.
///
/// The bundle carries the TrustIr module, the persisted proof-lineage sidecar, and
/// typed TrustVc/TrustMc/TrustWp requests. It deliberately does not alter the `.tmbc`
/// module format.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct NativeVerificationBundle {
    pub schema_version: u32,
    pub producer: NativeBundleProducer,
    pub input: NativeAdapterInput,
    #[cfg_attr(feature = "serde", serde(default))]
    pub provenance: NativeBundleProvenance,
    #[cfg_attr(feature = "serde", serde(default))]
    pub serialization: NativeSerializationPolicy,
    #[cfg_attr(feature = "serde", serde(default))]
    pub diagnostics: NativeDiagnosticsPolicy,
    pub trust_ir_module_digest: ProofDigest,
    #[cfg_attr(feature = "serde", serde(default))]
    pub compiler_facts: NativeCompilerFacts,
    pub module: Module,
    pub lineage: ProofLineageManifest,
    pub requests: Vec<NativeVerificationRequest>,
    /// Native verifier result evidence bound back to typed requests.
    ///
    /// Producers may leave this empty while routing a request-only handoff to a
    /// verifier. Release/admission consumers must require matching evidence
    /// bundles for the requests they are admitting.
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Vec::is_empty")
    )]
    pub evidence_bundles: Vec<NativeEvidenceBundle>,
    /// Private, transient identity shared with a source-generation authority.
    ///
    /// The field is skipped by serde and its `Clone` implementation deliberately
    /// clears the identity. Keeping it private prevents safe downstream code from
    /// transplanting a live identity onto a decoded or independently constructed
    /// bundle.
    #[cfg_attr(feature = "serde", serde(skip))]
    source_generation_live: SourceGenerationLiveMarker,
}

#[derive(Debug, Default)]
struct SourceGenerationLiveMarker(Option<Arc<SourceGenerationNonce>>);

#[derive(Debug)]
struct SourceGenerationNonce;

impl SourceGenerationLiveMarker {
    fn mint() -> (Self, Arc<SourceGenerationNonce>) {
        let nonce = Arc::new(SourceGenerationNonce);
        (Self(Some(Arc::clone(&nonce))), nonce)
    }

    fn matches(&self, nonce: &Arc<SourceGenerationNonce>) -> bool {
        self.0.as_ref().is_some_and(|live| Arc::ptr_eq(live, nonce))
    }
}

impl Clone for SourceGenerationLiveMarker {
    fn clone(&self) -> Self {
        // A clone is new storage, not the exact live bundle instance certified
        // by the trusted producer seam. Never duplicate transient authority.
        Self::default()
    }
}

impl PartialEq for SourceGenerationLiveMarker {
    fn eq(&self, _other: &Self) -> bool {
        // Transient authority is deliberately excluded from content equality.
        true
    }
}

/// Error returned when a trusted producer cannot mint source-generation
/// authority for a native bundle.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SourceGenerationAuthorityMintError {
    /// The bundle failed its ordinary native-bundle validation.
    InvalidBundle(Vec<NativeVerificationBundleError>),
    /// Authority is one-shot: this exact live bundle already has an identity.
    AlreadyMinted,
}

impl core::fmt::Display for SourceGenerationAuthorityMintError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::InvalidBundle(errors) => {
                write!(
                    f,
                    "source-generation bundle failed validation: {} error(s)",
                    errors.len()
                )
            }
            Self::AlreadyMinted => {
                f.write_str("source-generation authority was already minted for this bundle")
            }
        }
    }
}

impl std::error::Error for SourceGenerationAuthorityMintError {}

/// Non-serializable capability proving that one exact
/// [`NativeVerificationBundle`] instance came through a trusted live
/// source-generation seam.
///
/// The capability is bound both to a private allocation identity and to the
/// bundle's full canonical digest. The identity is erased by cloning and every
/// serialization path, while the digest makes post-mint content mutation fail
/// closed. The type is neither `Clone` nor serializable.
#[derive(Debug)]
pub struct SourceGenerationAuthority {
    nonce: Arc<SourceGenerationNonce>,
    bundle_digest: ProofDigest,
}

impl SourceGenerationAuthority {
    /// Mint one authority for a bundle built directly from live source lowering.
    ///
    /// The method validates the bundle, installs a private one-shot identity, and
    /// binds the returned capability to the bundle's complete canonical digest.
    ///
    /// # Trust boundary
    ///
    /// The caller must be the audited producer boundary that has just lowered
    /// live compiler source into `bundle`. In particular, callers must not invoke
    /// this method for a bundle obtained from bytes, IPC, a cache, or any other
    /// unauthenticated input. This is an explicit *semantic* TCB seam. It is a
    /// safe Rust function because violating the contract cannot cause memory
    /// unsafety; the constellation's call-site gate must nevertheless treat each
    /// invocation as an authority issuer. Safe code cannot construct or
    /// transplant the private identity except through this conspicuous method.
    pub fn mint_from_live_lowering(
        bundle: &mut NativeVerificationBundle,
    ) -> Result<Self, SourceGenerationAuthorityMintError> {
        if bundle.source_generation_live.0.is_some() {
            return Err(SourceGenerationAuthorityMintError::AlreadyMinted);
        }
        bundle
            .validate()
            .map_err(SourceGenerationAuthorityMintError::InvalidBundle)?;
        let bundle_digest = bundle.stable_digest();
        let (marker, nonce) = SourceGenerationLiveMarker::mint();
        bundle.source_generation_live = marker;
        Ok(Self {
            nonce,
            bundle_digest,
        })
    }

    /// Whether this authority still belongs to this exact, valid bundle.
    #[must_use]
    pub fn authorizes_bundle(&self, bundle: &NativeVerificationBundle) -> bool {
        bundle.source_generation_live.matches(&self.nonce)
            && self.bundle_digest == bundle.stable_digest()
            && bundle.validate().is_ok()
    }
}

impl NativeVerificationBundle {
    pub const SCHEMA_VERSION: u32 = NATIVE_VERIFICATION_BUNDLE_SCHEMA_VERSION;

    pub fn new(
        producer: NativeBundleProducer,
        input: NativeAdapterInput,
        trust_ir_module_digest: ProofDigest,
        module: Module,
        lineage: ProofLineageManifest,
    ) -> Self {
        Self {
            schema_version: Self::SCHEMA_VERSION,
            producer,
            input,
            provenance: NativeBundleProvenance::default(),
            serialization: NativeSerializationPolicy::default(),
            diagnostics: NativeDiagnosticsPolicy::default(),
            trust_ir_module_digest,
            compiler_facts: NativeCompilerFacts::default(),
            module,
            lineage,
            requests: Vec::new(),
            evidence_bundles: Vec::new(),
            source_generation_live: SourceGenerationLiveMarker::default(),
        }
    }

    pub fn validate(&self) -> Result<(), Vec<NativeVerificationBundleError>> {
        let mut errors = Vec::new();

        // EXACT-match by design (NOT a `MIN_READ_VERSION..=SCHEMA_VERSION` range
        // like the on-disk binary codec). The native verification bundle is a
        // *synchronized cross-repo contract* between the producers (tRust/ty)
        // and the consumers (ay/TrustCg) in one coordinated release — an
        // in-memory handshake, not a persisted artifact that must read older
        // files. A version mismatch means the peers are out of sync and must be
        // rejected, not silently best-effort-upgraded. Any future migration path
        // must be designed jointly with those repos (a unilateral accept-range
        // here could admit a bundle a peer cannot honor). Contrast `binary.rs`,
        // which DOES read old on-disk modules via its MIN_READ_VERSION range.
        if self.schema_version != Self::SCHEMA_VERSION {
            errors.push(NativeVerificationBundleError::UnsupportedSchemaVersion(
                self.schema_version,
            ));
        }
        if self.trust_ir_module_digest.is_zero() {
            errors.push(NativeVerificationBundleError::EmptyDigest {
                field: "trust_ir_module_digest",
            });
        }
        if self.trust_ir_module_digest.algorithm != ProofDigestAlgorithm::Sha256 {
            errors.push(NativeVerificationBundleError::NonCryptographicDigest {
                field: "trust_ir_module_digest",
            });
        }
        let actual_module_digest = self.module.stable_digest();
        if self.trust_ir_module_digest != actual_module_digest {
            errors.push(NativeVerificationBundleError::TrustIrModuleDigestMismatch {
                expected: actual_module_digest,
                actual: self.trust_ir_module_digest,
            });
        }
        if let Some(source_digest) = self.source_digest()
            && source_digest.is_zero()
        {
            errors.push(NativeVerificationBundleError::EmptyDigest {
                field: "input.rust_mir.body_digest",
            });
        }
        if self
            .source_digest()
            .is_some_and(|digest| digest.algorithm != ProofDigestAlgorithm::Sha256)
        {
            errors.push(NativeVerificationBundleError::NonCryptographicDigest {
                field: "input.source_digest",
            });
        }
        if self.requests.is_empty() {
            errors.push(NativeVerificationBundleError::EmptyRequests);
        }
        self.validate_provenance(&mut errors);
        self.validate_serialization(&mut errors);
        validate_bundle_diagnostics(&self.diagnostics, &mut errors);

        if let Err(lineage_errors) = self.lineage.validate_against(
            &self.module.proof_obligations,
            &self.module.proof_certificates,
        ) {
            errors.push(NativeVerificationBundleError::Lineage(lineage_errors));
        }

        self.validate_lineage_digests(&mut errors);
        self.validate_compiler_facts(&mut errors);
        self.validate_requests(&mut errors);
        self.validate_evidence_bundles(&mut errors);

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    pub fn stable_digest(&self) -> ProofDigest {
        let mut bytes = Vec::new();
        write_u32_stable(&mut bytes, self.schema_version);
        write_bundle_producer_stable(&mut bytes, self.producer);
        write_adapter_input_stable(&mut bytes, &self.input);
        write_bundle_provenance_stable(&mut bytes, &self.provenance);
        write_serialization_policy_stable(&mut bytes, &self.serialization);
        write_diagnostics_policy_stable(&mut bytes, &self.diagnostics);
        write_digest_stable(&mut bytes, &self.trust_ir_module_digest);
        write_digest_stable(&mut bytes, &self.compiler_facts.stable_digest());
        write_digest_stable(&mut bytes, &self.lineage.stable_digest());

        let mut requests: Vec<&NativeVerificationRequest> = self.requests.iter().collect();
        requests.sort_by_key(|request| (request.id(), native_request_variant_tag(request)));
        write_len_stable(&mut bytes, requests.len());
        for request in requests {
            write_digest_stable(&mut bytes, &request.stable_digest());
        }

        let mut evidence_bundles: Vec<&NativeEvidenceBundle> =
            self.evidence_bundles.iter().collect();
        evidence_bundles.sort_by_key(|bundle| {
            (
                bundle.request(),
                native_evidence_bundle_variant_tag(bundle),
                native_evidence_bundle_mode_tag(bundle),
            )
        });
        write_len_stable(&mut bytes, evidence_bundles.len());
        for evidence in evidence_bundles {
            write_digest_stable(&mut bytes, &evidence.stable_digest());
        }

        ProofDigest::sha256_domain("trust_ir.native.verification.bundle.v6", &bytes)
    }

    /// Return the transport/digest/ABI identity exported to native consumers.
    pub fn transport_identity(&self) -> NativeTransportIdentity {
        NativeTransportIdentity::from_bundle(self)
    }

    /// Return the target ABI identity carried by this bundle's TrustIr module.
    pub fn target_abi_identity(&self) -> Option<NativeTargetAbiIdentity> {
        self.module
            .target_info
            .as_ref()
            .map(NativeTargetAbiIdentity::from_target_info)
    }

    /// Return validated native evidence consumption records.
    ///
    /// The helper fails closed by running full bundle validation first. It
    /// reports supplied evidence entries only; release/admission gates that
    /// require verifier results must also require a matching entry for each
    /// request they admit. TrustVc entries return the certificate refs already
    /// attached to the corresponding request and module. TrustMc and TrustWp entries
    /// return artifacts and obligations only; turning those artifacts into proof
    /// certificates remains a verifier-specific step.
    pub fn native_evidence_consumption_report(
        &self,
    ) -> Result<NativeEvidenceConsumptionReport, Vec<NativeVerificationBundleError>> {
        self.validate()?;

        let requests: BTreeMap<NativeRequestId, &NativeVerificationRequest> = self
            .requests
            .iter()
            .map(|request| (request.id(), request))
            .collect();

        let entries = self
            .evidence_bundles
            .iter()
            .filter_map(|evidence| {
                let request = requests.get(&evidence.request()).copied()?;
                let consumed_certificates = consumed_certificates_for_evidence(request, evidence);
                Some(NativeEvidenceConsumptionEntry {
                    request: evidence.request(),
                    suite: evidence.verifier_suite(),
                    evidence_digest: evidence.stable_digest(),
                    obligations: evidence.obligations().to_vec(),
                    consumed_certificates,
                    artifacts: evidence.artifacts().to_vec(),
                })
            })
            .collect();

        Ok(NativeEvidenceConsumptionReport { entries })
    }

    /// Build a typed evidence bundle for one request in this native bundle.
    ///
    /// The returned evidence uses this bundle's TrustIr module digest and the
    /// request's stable digest/provenance, avoiding downstream reconstruction
    /// of evidence identity fields.
    pub fn evidence_bundle_for_request(
        &self,
        request: &NativeVerificationRequest,
        artifacts: Vec<NativeEvidenceArtifact>,
    ) -> Result<NativeEvidenceBundle, NativeVerificationBundleError> {
        NativeEvidenceBundle::from_request(self.trust_ir_module_digest, request, artifacts)
    }

    /// Resolve artifact bytes for a digest-bound native evidence artifact.
    ///
    /// Resolution is keyed by request id, artifact kind, digest algorithm, and
    /// digest. TrustIr verifies that the key names an artifact descriptor already
    /// attached to a matching evidence bundle and that exactly one byte
    /// attachment matches the same identity. The returned bytes are available
    /// only when the report is `resolved`; verifier-specific acceptance remains
    /// owned by the attachment's verifier suite.
    pub fn resolve_evidence_artifact_attachment<'a>(
        &self,
        key: NativeEvidenceArtifactAttachmentKey,
        attachments: &'a [NativeEvidenceArtifactAttachment],
    ) -> NativeEvidenceArtifactResolution<'a> {
        if key.digest_algorithm != key.digest.algorithm {
            return native_evidence_artifact_resolution(
                key,
                None,
                None,
                None,
                None,
                Some(key.digest),
                None,
                NativeEvidenceArtifactResolutionStatus::Blocked,
                NativeEvidenceArtifactResolutionReason::DigestAlgorithmMismatch,
            );
        }

        // Artifact byte identity crosses an untrusted attachment boundary.
        // The legacy structural checksum is collision-prone and must never
        // select authoritative bytes, even when descriptor and key agree on it.
        if key.digest_algorithm != ProofDigestAlgorithm::Sha256 {
            return native_evidence_artifact_resolution(
                key,
                None,
                None,
                None,
                None,
                Some(key.digest),
                None,
                NativeEvidenceArtifactResolutionStatus::Blocked,
                NativeEvidenceArtifactResolutionReason::NonCryptographicDigestAlgorithm,
            );
        }

        if self.validate().is_err() {
            return native_evidence_artifact_resolution(
                key,
                None,
                None,
                None,
                None,
                Some(key.digest),
                None,
                NativeEvidenceArtifactResolutionStatus::Blocked,
                NativeEvidenceArtifactResolutionReason::BundleInvalid,
            );
        }

        let Some(request) = self
            .requests
            .iter()
            .find(|request| request.id() == key.request)
        else {
            return native_evidence_artifact_resolution(
                key,
                None,
                None,
                None,
                None,
                Some(key.digest),
                None,
                NativeEvidenceArtifactResolutionStatus::Blocked,
                NativeEvidenceArtifactResolutionReason::RequestUnknown,
            );
        };
        let owner_suite = request.verifier_suite();

        let Some(evidence) = self.evidence_bundles.iter().find(|evidence| {
            evidence.request() == key.request && evidence.verifier_suite() == owner_suite
        }) else {
            return native_evidence_artifact_resolution(
                key,
                Some(owner_suite),
                None,
                None,
                None,
                Some(key.digest),
                None,
                NativeEvidenceArtifactResolutionStatus::Blocked,
                NativeEvidenceArtifactResolutionReason::MissingEvidenceBundle,
            );
        };

        if !evidence_artifact_matches_bundle(evidence, key.kind) {
            return native_evidence_artifact_resolution(
                key,
                Some(owner_suite),
                None,
                None,
                None,
                Some(key.digest),
                None,
                NativeEvidenceArtifactResolutionStatus::Blocked,
                NativeEvidenceArtifactResolutionReason::UnsupportedArtifactKind,
            );
        }

        let same_kind: Vec<_> = evidence
            .artifacts()
            .iter()
            .filter(|artifact| artifact.kind == key.kind)
            .collect();
        let Some(first_same_kind) = same_kind.first().copied() else {
            return native_evidence_artifact_resolution(
                key,
                Some(owner_suite),
                None,
                None,
                None,
                Some(key.digest),
                None,
                NativeEvidenceArtifactResolutionStatus::Blocked,
                NativeEvidenceArtifactResolutionReason::MissingArtifactDescriptor,
            );
        };
        let Some(first_same_algorithm) = same_kind
            .iter()
            .copied()
            .find(|artifact| artifact.digest.algorithm == key.digest_algorithm)
        else {
            return native_evidence_artifact_resolution(
                key,
                Some(owner_suite),
                Some(first_same_kind.name.clone()),
                None,
                None,
                Some(first_same_kind.digest),
                None,
                NativeEvidenceArtifactResolutionStatus::Blocked,
                NativeEvidenceArtifactResolutionReason::DigestAlgorithmMismatch,
            );
        };
        let artifact = same_kind
            .iter()
            .copied()
            .find(|artifact| artifact.digest == key.digest)
            .unwrap_or(first_same_algorithm);

        if artifact.digest.algorithm != key.digest_algorithm {
            return native_evidence_artifact_resolution(
                key,
                Some(owner_suite),
                Some(artifact.name.clone()),
                None,
                None,
                Some(artifact.digest),
                None,
                NativeEvidenceArtifactResolutionStatus::Blocked,
                NativeEvidenceArtifactResolutionReason::DigestAlgorithmMismatch,
            );
        }
        if artifact.digest != key.digest {
            return native_evidence_artifact_resolution(
                key,
                Some(owner_suite),
                Some(artifact.name.clone()),
                None,
                None,
                Some(artifact.digest),
                None,
                NativeEvidenceArtifactResolutionStatus::Blocked,
                NativeEvidenceArtifactResolutionReason::DigestMismatch,
            );
        }

        let mut matching_attachments = attachments
            .iter()
            .filter(|attachment| attachment.key == key);
        let Some(attachment) = matching_attachments.next() else {
            return native_evidence_artifact_resolution(
                key,
                Some(owner_suite),
                Some(artifact.name.clone()),
                None,
                None,
                Some(artifact.digest),
                None,
                NativeEvidenceArtifactResolutionStatus::Blocked,
                NativeEvidenceArtifactResolutionReason::MissingAttachment,
            );
        };
        if matching_attachments.next().is_some() {
            return native_evidence_artifact_resolution(
                key,
                Some(owner_suite),
                Some(artifact.name.clone()),
                Some(attachment.source_identity.clone()),
                Some(attachment.bytes.len()),
                Some(artifact.digest),
                None,
                NativeEvidenceArtifactResolutionStatus::Blocked,
                NativeEvidenceArtifactResolutionReason::DuplicateAttachment,
            );
        }

        if attachment.owner_suite != owner_suite {
            return native_evidence_artifact_resolution(
                key,
                Some(owner_suite),
                Some(artifact.name.clone()),
                Some(attachment.source_identity.clone()),
                Some(attachment.bytes.len()),
                Some(artifact.digest),
                None,
                NativeEvidenceArtifactResolutionStatus::Blocked,
                NativeEvidenceArtifactResolutionReason::OwnerSuiteMismatch,
            );
        }
        if attachment.source_identity.trim().is_empty() {
            return native_evidence_artifact_resolution(
                key,
                Some(owner_suite),
                Some(artifact.name.clone()),
                Some(attachment.source_identity.clone()),
                Some(attachment.bytes.len()),
                Some(artifact.digest),
                None,
                NativeEvidenceArtifactResolutionStatus::Blocked,
                NativeEvidenceArtifactResolutionReason::InvalidSourceIdentity,
            );
        }
        if attachment.bytes.is_empty() {
            return native_evidence_artifact_resolution(
                key,
                Some(owner_suite),
                Some(artifact.name.clone()),
                Some(attachment.source_identity.clone()),
                Some(0),
                Some(artifact.digest),
                None,
                NativeEvidenceArtifactResolutionStatus::Blocked,
                NativeEvidenceArtifactResolutionReason::EmptyBytes,
            );
        }

        let actual_digest = NativeEvidenceArtifactAttachment::digest_for_bytes(
            key.digest_algorithm,
            &attachment.bytes,
        );
        if actual_digest != key.digest {
            return native_evidence_artifact_resolution(
                key,
                Some(owner_suite),
                Some(artifact.name.clone()),
                Some(attachment.source_identity.clone()),
                Some(attachment.bytes.len()),
                Some(artifact.digest),
                Some(actual_digest),
                NativeEvidenceArtifactResolutionStatus::Blocked,
                NativeEvidenceArtifactResolutionReason::DigestMismatch,
            );
        }

        native_evidence_artifact_resolution(
            key,
            Some(owner_suite),
            Some(artifact.name.clone()),
            Some(attachment.source_identity.clone()),
            Some(attachment.bytes.len()),
            Some(artifact.digest),
            Some(actual_digest),
            NativeEvidenceArtifactResolutionStatus::Resolved,
            NativeEvidenceArtifactResolutionReason::Resolved,
        )
        .with_bytes(&attachment.bytes)
    }

    /// Resolve one required artifact kind without requiring downstream code to
    /// synthesize a digest key first.
    ///
    /// When a descriptor for `required_kind` exists, this delegates to
    /// [`Self::resolve_evidence_artifact_attachment`] with the descriptor's real
    /// digest and returns the byte-backed resolution. When the descriptor is
    /// missing, the returned value carries `MissingArtifactDescriptor` and no
    /// digest/row payload, so consumers can fail closed without publishing
    /// placeholder digest rows.
    pub fn resolve_evidence_artifact_attachment_for_kind<'a>(
        &'a self,
        request: NativeRequestId,
        required_kind: NativeEvidenceArtifactKind,
        attachments: &'a [NativeEvidenceArtifactAttachment],
    ) -> NativeEvidenceArtifactAttachmentResolution<'a> {
        if self.validate().is_err() {
            return native_evidence_artifact_attachment_resolution(
                request,
                None,
                required_kind,
                None,
                None,
                NativeEvidenceArtifactResolutionStatus::Blocked,
                NativeEvidenceArtifactResolutionReason::BundleInvalid,
            );
        }

        let Some(native_request) = self
            .requests
            .iter()
            .find(|native_request| native_request.id() == request)
        else {
            return native_evidence_artifact_attachment_resolution(
                request,
                None,
                required_kind,
                None,
                None,
                NativeEvidenceArtifactResolutionStatus::Blocked,
                NativeEvidenceArtifactResolutionReason::RequestUnknown,
            );
        };
        let owner_suite = native_request.verifier_suite();

        let Some(evidence) = self.evidence_bundles.iter().find(|evidence| {
            evidence.request() == request && evidence.verifier_suite() == owner_suite
        }) else {
            return native_evidence_artifact_attachment_resolution(
                request,
                Some(owner_suite),
                required_kind,
                None,
                None,
                NativeEvidenceArtifactResolutionStatus::Blocked,
                NativeEvidenceArtifactResolutionReason::MissingEvidenceBundle,
            );
        };

        if !evidence_artifact_matches_bundle(evidence, required_kind) {
            return native_evidence_artifact_attachment_resolution(
                request,
                Some(owner_suite),
                required_kind,
                None,
                None,
                NativeEvidenceArtifactResolutionStatus::Blocked,
                NativeEvidenceArtifactResolutionReason::UnsupportedArtifactKind,
            );
        }

        let Some(artifact) = evidence
            .artifacts()
            .iter()
            .find(|artifact| artifact.kind == required_kind)
        else {
            return native_evidence_artifact_attachment_resolution(
                request,
                Some(owner_suite),
                required_kind,
                None,
                None,
                NativeEvidenceArtifactResolutionStatus::Blocked,
                NativeEvidenceArtifactResolutionReason::MissingArtifactDescriptor,
            );
        };

        let resolution = self.resolve_evidence_artifact_attachment(
            NativeEvidenceArtifactAttachmentKey::for_artifact(request, artifact),
            attachments,
        );
        let status = resolution.report.status;
        let reason = resolution.report.reason;

        native_evidence_artifact_attachment_resolution(
            request,
            Some(owner_suite),
            required_kind,
            Some(artifact),
            Some(resolution),
            status,
            reason,
        )
    }

    /// Resolve a stable set of required artifact kinds for one request.
    ///
    /// The result order matches `required_kinds`, making this suitable for
    /// forwarding producer-owned evidence into package sidecars without local
    /// sorting or row-shape reconstruction.
    pub fn resolve_evidence_artifact_attachments_for_kinds<'a>(
        &'a self,
        request: NativeRequestId,
        required_kinds: &[NativeEvidenceArtifactKind],
        attachments: &'a [NativeEvidenceArtifactAttachment],
    ) -> Vec<NativeEvidenceArtifactAttachmentResolution<'a>> {
        required_kinds
            .iter()
            .copied()
            .map(|required_kind| {
                self.resolve_evidence_artifact_attachment_for_kind(
                    request,
                    required_kind,
                    attachments,
                )
            })
            .collect()
    }

    /// Report whether a native entry function has TrustIr-owned semantic
    /// successor authority.
    ///
    /// The report is derived from existing module obligations, obligation
    /// sources, and verifier evidence. It never trusts a producer-authored
    /// status bit: invalid bundles, pending/trusted proofs, function mismatches,
    /// and missing verifier evidence all return a blocked report.
    pub fn native_semantic_bridge_report(
        &self,
        bridge: NativeSemanticBridge,
    ) -> NativeSemanticBridgeReport {
        if self.validate().is_err() {
            return native_semantic_bridge_report(
                bridge,
                None,
                None,
                None,
                NativeSemanticBridgeEvidenceStatus::Missing,
                NativeSemanticBridgeStatus::Blocked,
                NativeSemanticBridgeReason::BundleInvalid,
            );
        }

        if self.module.function_by_id(bridge.function).is_none() {
            return native_semantic_bridge_report(
                bridge,
                None,
                None,
                None,
                NativeSemanticBridgeEvidenceStatus::Missing,
                NativeSemanticBridgeStatus::Blocked,
                NativeSemanticBridgeReason::MissingFunction,
            );
        }

        let formula_obligations: Vec<&ProofObligation> = self
            .module
            .proof_obligations
            .iter()
            .filter(|obligation| {
                obligation
                    .formula
                    .as_ref()
                    .is_some_and(|formula| formula.schema == bridge.formula_schema)
            })
            .collect();

        if formula_obligations.is_empty() {
            return native_semantic_bridge_report(
                bridge,
                None,
                None,
                None,
                NativeSemanticBridgeEvidenceStatus::Missing,
                NativeSemanticBridgeStatus::Blocked,
                NativeSemanticBridgeReason::MissingProofObligation,
            );
        }

        let sourced_obligations: Vec<(&ProofObligation, &NativeObligationSource)> =
            formula_obligations
                .iter()
                .filter_map(|obligation| {
                    self.obligation_source(obligation.id)
                        .map(|source| (*obligation, source))
                })
                .collect();

        if sourced_obligations.is_empty() {
            return native_semantic_bridge_report(
                bridge,
                formula_obligations.first().copied(),
                None,
                None,
                NativeSemanticBridgeEvidenceStatus::Missing,
                NativeSemanticBridgeStatus::Blocked,
                NativeSemanticBridgeReason::MissingObligationSource,
            );
        }

        let Some((obligation, source)) = sourced_obligations
            .iter()
            .copied()
            .find(|(_, source)| source.function == Some(bridge.function))
        else {
            return native_semantic_bridge_report(
                bridge,
                Some(sourced_obligations[0].0),
                None,
                None,
                NativeSemanticBridgeEvidenceStatus::Missing,
                NativeSemanticBridgeStatus::Blocked,
                NativeSemanticBridgeReason::FunctionMismatch,
            );
        };

        let proof_digest = Some(native_semantic_bridge_proof_digest(obligation));
        if source.function != Some(bridge.function) {
            return native_semantic_bridge_report(
                bridge,
                Some(obligation),
                proof_digest,
                None,
                NativeSemanticBridgeEvidenceStatus::Missing,
                NativeSemanticBridgeStatus::Blocked,
                NativeSemanticBridgeReason::FunctionMismatch,
            );
        }
        if obligation.kind != ObligationKind::TranslationValidation {
            return native_semantic_bridge_report(
                bridge,
                Some(obligation),
                proof_digest,
                None,
                NativeSemanticBridgeEvidenceStatus::Missing,
                NativeSemanticBridgeStatus::Blocked,
                NativeSemanticBridgeReason::UnsupportedObligationKind,
            );
        }
        match obligation.status {
            ProofStatus::Discharged | ProofStatus::Certified
                if native_authority_replayed(obligation, &self.module.proof_certificates) => {}
            ProofStatus::Pending => {
                return native_semantic_bridge_report(
                    bridge,
                    Some(obligation),
                    proof_digest,
                    None,
                    NativeSemanticBridgeEvidenceStatus::Missing,
                    NativeSemanticBridgeStatus::Blocked,
                    NativeSemanticBridgeReason::ProofPending,
                );
            }
            ProofStatus::Failed => {
                return native_semantic_bridge_report(
                    bridge,
                    Some(obligation),
                    proof_digest,
                    None,
                    NativeSemanticBridgeEvidenceStatus::Missing,
                    NativeSemanticBridgeStatus::Blocked,
                    NativeSemanticBridgeReason::ProofFailed,
                );
            }
            ProofStatus::Trusted | ProofStatus::Discharged | ProofStatus::Certified => {
                return native_semantic_bridge_report(
                    bridge,
                    Some(obligation),
                    proof_digest,
                    None,
                    NativeSemanticBridgeEvidenceStatus::Missing,
                    NativeSemanticBridgeStatus::Blocked,
                    NativeSemanticBridgeReason::TrustedProofNotAdmitted,
                );
            }
        }

        let evidence_digest = self
            .evidence_bundles
            .iter()
            .filter(|evidence| evidence.obligations().contains(&obligation.id))
            .map(NativeEvidenceBundle::stable_digest)
            .min();
        let Some(evidence_digest) = evidence_digest else {
            return native_semantic_bridge_report(
                bridge,
                Some(obligation),
                proof_digest,
                None,
                NativeSemanticBridgeEvidenceStatus::Missing,
                NativeSemanticBridgeStatus::Blocked,
                NativeSemanticBridgeReason::MissingEvidence,
            );
        };

        native_semantic_bridge_report(
            bridge,
            Some(obligation),
            proof_digest,
            Some(evidence_digest),
            NativeSemanticBridgeEvidenceStatus::Present,
            NativeSemanticBridgeStatus::Represented,
            NativeSemanticBridgeReason::Represented,
        )
    }

    /// Report canonical Petri successor plan-cache semantic equivalence for a
    /// native function without requiring downstream consumers to hardcode the
    /// relation/formula pair.
    pub fn petri_successor_semantic_bridge_report(
        &self,
        function: FuncId,
    ) -> NativeSemanticBridgeReport {
        self.native_semantic_bridge_report(
            NativeSemanticBridge::petri_successor_plan_cache_equivalence(function),
        )
    }

    /// Report the typed TrustMc CHC request/evidence/artifact binding for a Petri
    /// successor semantic bridge.
    ///
    /// This helper is fail-closed: the report is bound only when the canonical
    /// Petri successor bridge is represented, a matching TrustMc CHC request exists,
    /// the matching evidence bundle derives from that request, and a TrustMc
    /// Horn-clause artifact is present.
    pub fn petri_successor_trust_mc_chc_binding_report(
        &self,
        function: FuncId,
    ) -> PetriSuccessorTrustMcChcBindingReport {
        let semantic_bridge_report = self.petri_successor_semantic_bridge_report(function);

        if self.validate().is_err() {
            return petri_successor_trust_mc_chc_binding_report(
                function,
                semantic_bridge_report,
                None,
                None,
                None,
                None,
                None,
                PetriSuccessorTrustMcChcBindingStatus::Blocked,
                PetriSuccessorTrustMcChcBindingReason::BundleInvalid,
            );
        }

        if !semantic_bridge_report.represents_petri_successor_plan_cache_equivalence() {
            return petri_successor_trust_mc_chc_binding_report(
                function,
                semantic_bridge_report,
                None,
                None,
                None,
                None,
                None,
                PetriSuccessorTrustMcChcBindingStatus::Blocked,
                PetriSuccessorTrustMcChcBindingReason::SemanticBridgeBlocked,
            );
        }

        let Some(proof_obligation) = semantic_bridge_report.proof_obligation else {
            return petri_successor_trust_mc_chc_binding_report(
                function,
                semantic_bridge_report,
                None,
                None,
                None,
                None,
                None,
                PetriSuccessorTrustMcChcBindingStatus::Blocked,
                PetriSuccessorTrustMcChcBindingReason::MissingBridgeProofObligation,
            );
        };

        let Some(request) = self.requests.iter().find(|request| {
            matches!(
                request,
                NativeVerificationRequest::TrustMc(TrustMcNativeRequest {
                    mode: TrustMcVerificationMode::Chc,
                    function: request_function,
                    obligations,
                    ..
                }) if *request_function == function && obligations.contains(&proof_obligation)
            )
        }) else {
            return petri_successor_trust_mc_chc_binding_report(
                function,
                semantic_bridge_report,
                None,
                None,
                None,
                None,
                None,
                PetriSuccessorTrustMcChcBindingStatus::Blocked,
                PetriSuccessorTrustMcChcBindingReason::MissingTrustMcChcRequest,
            );
        };

        let request_digest = request.stable_digest();
        let Some(evidence) = self.evidence_bundles.iter().find(|evidence| {
            matches!(
                evidence,
                NativeEvidenceBundle::TrustMc(TrustMcNativeEvidenceBundle {
                    request: evidence_request,
                    mode: TrustMcVerificationMode::Chc,
                    ..
                }) if *evidence_request == request.id()
            )
        }) else {
            return petri_successor_trust_mc_chc_binding_report(
                function,
                semantic_bridge_report,
                Some(request.id()),
                Some(request_digest),
                None,
                None,
                None,
                PetriSuccessorTrustMcChcBindingStatus::Blocked,
                PetriSuccessorTrustMcChcBindingReason::MissingTrustMcChcEvidence,
            );
        };

        let evidence_digest = evidence.stable_digest();
        let Ok(expected_evidence) =
            self.evidence_bundle_for_request(request, evidence.artifacts().to_vec())
        else {
            return petri_successor_trust_mc_chc_binding_report(
                function,
                semantic_bridge_report,
                Some(request.id()),
                Some(request_digest),
                Some(evidence_digest),
                None,
                None,
                PetriSuccessorTrustMcChcBindingStatus::Blocked,
                PetriSuccessorTrustMcChcBindingReason::EvidenceBindingMismatch,
            );
        };
        let expected_evidence_digest = expected_evidence.stable_digest();
        if expected_evidence_digest != evidence_digest {
            return petri_successor_trust_mc_chc_binding_report(
                function,
                semantic_bridge_report,
                Some(request.id()),
                Some(request_digest),
                Some(evidence_digest),
                Some(expected_evidence_digest),
                None,
                PetriSuccessorTrustMcChcBindingStatus::Blocked,
                PetriSuccessorTrustMcChcBindingReason::EvidenceBindingMismatch,
            );
        }

        let horn_clause_artifact = evidence
            .artifacts()
            .iter()
            .filter(|artifact| artifact.kind == NativeEvidenceArtifactKind::TrustMcHornClauses)
            .min()
            .cloned();
        let Some(horn_clause_artifact) = horn_clause_artifact else {
            return petri_successor_trust_mc_chc_binding_report(
                function,
                semantic_bridge_report,
                Some(request.id()),
                Some(request_digest),
                Some(evidence_digest),
                Some(expected_evidence_digest),
                None,
                PetriSuccessorTrustMcChcBindingStatus::Blocked,
                PetriSuccessorTrustMcChcBindingReason::MissingHornClauseArtifact,
            );
        };

        petri_successor_trust_mc_chc_binding_report(
            function,
            semantic_bridge_report,
            Some(request.id()),
            Some(request_digest),
            Some(evidence_digest),
            Some(expected_evidence_digest),
            Some(horn_clause_artifact),
            PetriSuccessorTrustMcChcBindingStatus::Bound,
            PetriSuccessorTrustMcChcBindingReason::Bound,
        )
    }

    /// Report whether Petri successor TrustMc CHC evidence is ready for proof
    /// handoff.
    ///
    /// This helper builds on [`Self::petri_successor_trust_mc_chc_binding_report`].
    /// It is ready only when the binding is bound and the matching TrustMc CHC
    /// evidence carries a replay transcript artifact whose digest matches the
    /// typed replay identity. Optional model artifacts are surfaced for
    /// downstream validation, but their presence alone never marks a handoff
    /// ready.
    pub fn petri_successor_trust_mc_chc_proof_handoff_report(
        &self,
        function: FuncId,
    ) -> PetriSuccessorTrustMcChcProofHandoffReport {
        let binding_report = self.petri_successor_trust_mc_chc_binding_report(function);
        let proof_identity_digest = Some(
            binding_report
                .semantic_bridge_report
                .proof_identity_digest(),
        );

        if !binding_report.is_bound() {
            return petri_successor_trust_mc_chc_proof_handoff_report(
                function,
                binding_report,
                proof_identity_digest,
                None,
                None,
                None,
                None,
                Vec::new(),
                PetriSuccessorTrustMcChcProofHandoffStatus::Blocked,
                PetriSuccessorTrustMcChcProofHandoffReason::BindingBlocked,
            );
        }

        let Some(request) = binding_report.request else {
            return petri_successor_trust_mc_chc_proof_handoff_report(
                function,
                binding_report,
                proof_identity_digest,
                None,
                None,
                None,
                None,
                Vec::new(),
                PetriSuccessorTrustMcChcProofHandoffStatus::Blocked,
                PetriSuccessorTrustMcChcProofHandoffReason::MissingTrustMcChcEvidence,
            );
        };

        let Some(evidence) = self.evidence_bundles.iter().find(|evidence| {
            matches!(
                evidence,
                NativeEvidenceBundle::TrustMc(TrustMcNativeEvidenceBundle {
                    request: evidence_request,
                    mode: TrustMcVerificationMode::Chc,
                    ..
                }) if *evidence_request == request
            )
        }) else {
            return petri_successor_trust_mc_chc_proof_handoff_report(
                function,
                binding_report,
                proof_identity_digest,
                None,
                None,
                None,
                None,
                Vec::new(),
                PetriSuccessorTrustMcChcProofHandoffStatus::Blocked,
                PetriSuccessorTrustMcChcProofHandoffReason::MissingTrustMcChcEvidence,
            );
        };

        let replay = evidence.replay().clone();
        let solver_identities = evidence.solvers().to_vec();
        let Some(replay_transcript_digest) = replay.transcript_digest else {
            return petri_successor_trust_mc_chc_proof_handoff_report(
                function,
                binding_report,
                proof_identity_digest,
                Some(replay),
                None,
                None,
                None,
                solver_identities,
                PetriSuccessorTrustMcChcProofHandoffStatus::Blocked,
                PetriSuccessorTrustMcChcProofHandoffReason::MissingReplayTranscriptDigest,
            );
        };

        let replay_transcript_artifact = evidence
            .artifacts()
            .iter()
            .filter(|artifact| artifact.kind == NativeEvidenceArtifactKind::ReplayTranscript)
            .find(|artifact| artifact.digest == replay_transcript_digest)
            .or_else(|| {
                evidence
                    .artifacts()
                    .iter()
                    .filter(|artifact| {
                        artifact.kind == NativeEvidenceArtifactKind::ReplayTranscript
                    })
                    .min()
            })
            .cloned();
        let model_artifact = evidence
            .artifacts()
            .iter()
            .filter(|artifact| artifact.kind == NativeEvidenceArtifactKind::TrustMcModel)
            .min()
            .cloned();

        let Some(replay_transcript_artifact) = replay_transcript_artifact else {
            return petri_successor_trust_mc_chc_proof_handoff_report(
                function,
                binding_report,
                proof_identity_digest,
                Some(replay),
                Some(replay_transcript_digest),
                None,
                model_artifact,
                solver_identities,
                PetriSuccessorTrustMcChcProofHandoffStatus::Blocked,
                PetriSuccessorTrustMcChcProofHandoffReason::MissingReplayTranscriptArtifact,
            );
        };

        if replay_transcript_artifact.digest != replay_transcript_digest {
            return petri_successor_trust_mc_chc_proof_handoff_report(
                function,
                binding_report,
                proof_identity_digest,
                Some(replay),
                Some(replay_transcript_digest),
                Some(replay_transcript_artifact),
                model_artifact,
                solver_identities,
                PetriSuccessorTrustMcChcProofHandoffStatus::Blocked,
                PetriSuccessorTrustMcChcProofHandoffReason::ReplayTranscriptDigestMismatch,
            );
        }

        petri_successor_trust_mc_chc_proof_handoff_report(
            function,
            binding_report,
            proof_identity_digest,
            Some(replay),
            Some(replay_transcript_digest),
            Some(replay_transcript_artifact),
            model_artifact,
            solver_identities,
            PetriSuccessorTrustMcChcProofHandoffStatus::Ready,
            PetriSuccessorTrustMcChcProofHandoffReason::Ready,
        )
    }

    /// Report whether Petri successor TrustMc CHC model evidence is ready for
    /// solver-owned validation.
    ///
    /// TrustIr does not validate solver models. This helper only reports the
    /// typed handoff inputs and remains fail-closed for acceptance until a
    /// solver-owned validation result is attached by downstream code.
    pub fn petri_successor_trust_mc_chc_model_validation_readiness_report(
        &self,
        function: FuncId,
    ) -> PetriSuccessorTrustMcChcModelValidationReadinessReport {
        let proof_handoff_report = self.petri_successor_trust_mc_chc_proof_handoff_report(function);

        if !proof_handoff_report.is_ready() {
            return petri_successor_trust_mc_chc_model_validation_readiness_report(
                function,
                proof_handoff_report,
                None,
                None,
                Vec::new(),
                false,
                PetriSuccessorTrustMcChcModelValidationReadinessStatus::Blocked,
                PetriSuccessorTrustMcChcModelValidationReadinessReason::ProofHandoffBlocked,
            );
        }

        let solver_identities = proof_handoff_report.solver_identities.clone();
        let model_artifact = proof_handoff_report.model_artifact.clone();
        let Some(model_artifact) = model_artifact else {
            return petri_successor_trust_mc_chc_model_validation_readiness_report(
                function,
                proof_handoff_report,
                None,
                None,
                solver_identities,
                false,
                PetriSuccessorTrustMcChcModelValidationReadinessStatus::Blocked,
                PetriSuccessorTrustMcChcModelValidationReadinessReason::MissingModelArtifact,
            );
        };
        let model_artifact_digest = model_artifact.digest;

        petri_successor_trust_mc_chc_model_validation_readiness_report(
            function,
            proof_handoff_report,
            Some(model_artifact),
            Some(model_artifact_digest),
            solver_identities,
            false,
            PetriSuccessorTrustMcChcModelValidationReadinessStatus::ReadyForSolverValidation,
            PetriSuccessorTrustMcChcModelValidationReadinessReason::SolverValidationRequired,
        )
    }

    /// Admit Petri successor semantic bridge proof artifacts for native use.
    ///
    /// Admission requires the typed proof handoff to be ready and every
    /// production-required artifact kind to resolve to authoritative bytes.
    /// Metadata-only evidence bundles, missing descriptors, stale bytes, and
    /// missing attachments all return blocked reports with the first TrustIr-owned
    /// artifact resolution reason preserved.
    pub fn petri_successor_semantic_bridge_proof_admission_report<'a>(
        &'a self,
        function: FuncId,
        attachments: &'a [NativeEvidenceArtifactAttachment],
    ) -> PetriSuccessorSemanticBridgeProofAdmissionReport<'a> {
        let proof_handoff_report = self.petri_successor_trust_mc_chc_proof_handoff_report(function);
        let required_artifact_kinds =
            PETRI_SUCCESSOR_TRUST_MC_CHC_PRODUCTION_ACCEPTANCE_REQUIRED_ARTIFACT_KINDS.to_vec();

        if !proof_handoff_report.is_ready() {
            return petri_successor_semantic_bridge_proof_admission_report(
                function,
                proof_handoff_report,
                required_artifact_kinds,
                Vec::new(),
                None,
                None,
                PetriSuccessorSemanticBridgeProofAdmissionStatus::Blocked,
                PetriSuccessorSemanticBridgeProofAdmissionReason::ProofHandoffBlocked,
            );
        }

        let Some(request) = proof_handoff_report.binding_report.request else {
            return petri_successor_semantic_bridge_proof_admission_report(
                function,
                proof_handoff_report,
                required_artifact_kinds,
                Vec::new(),
                None,
                None,
                PetriSuccessorSemanticBridgeProofAdmissionStatus::Blocked,
                PetriSuccessorSemanticBridgeProofAdmissionReason::ProofHandoffBlocked,
            );
        };

        let artifact_resolutions = self.resolve_evidence_artifact_attachments_for_kinds(
            request,
            &required_artifact_kinds,
            attachments,
        );
        let blocked_artifact = artifact_resolutions
            .iter()
            .find(|resolution| !resolution.is_authoritative())
            .map(|resolution| (resolution.required_kind, resolution.reason));
        if let Some((blocked_artifact_kind, blocked_artifact_reason)) = blocked_artifact {
            return petri_successor_semantic_bridge_proof_admission_report(
                function,
                proof_handoff_report,
                required_artifact_kinds,
                artifact_resolutions,
                Some(blocked_artifact_kind),
                Some(blocked_artifact_reason),
                PetriSuccessorSemanticBridgeProofAdmissionStatus::Blocked,
                PetriSuccessorSemanticBridgeProofAdmissionReason::ArtifactResolutionBlocked,
            );
        }

        petri_successor_semantic_bridge_proof_admission_report(
            function,
            proof_handoff_report,
            required_artifact_kinds,
            artifact_resolutions,
            None,
            None,
            PetriSuccessorSemanticBridgeProofAdmissionStatus::Admitted,
            PetriSuccessorSemanticBridgeProofAdmissionReason::Admitted,
        )
    }

    pub fn obligation_source(&self, obligation: ProofId) -> Option<&NativeObligationSource> {
        self.compiler_facts.obligation_source(obligation)
    }

    pub fn monomorphization(
        &self,
        id: NativeMonomorphizationId,
    ) -> Option<&NativeMonomorphizationFact> {
        self.compiler_facts.monomorphization(id)
    }

    pub fn monomorphization_by_stable_digest(
        &self,
        digest: ProofDigest,
    ) -> Option<&NativeMonomorphizationFact> {
        self.compiler_facts
            .monomorphization_by_stable_digest(digest)
    }

    pub fn obligation_source_by_public_id(
        &self,
        public_obligation_id: &str,
    ) -> Option<&NativeObligationSource> {
        self.compiler_facts
            .obligation_source_by_public_id(public_obligation_id)
    }

    pub fn obligations_for_assertion(&self, assertion_id: NativeAssertionId) -> Vec<ProofId> {
        self.compiler_facts.obligations_for_assertion(assertion_id)
    }

    /// Return the frontend source digest when this bundle was emitted from one.
    pub fn source_digest(&self) -> Option<ProofDigest> {
        match self.input {
            NativeAdapterInput::RustMir { body_digest } => Some(body_digest),
            NativeAdapterInput::TrustIrModule => None,
        }
    }

    fn validate_provenance(&self, errors: &mut Vec<NativeVerificationBundleError>) {
        if self.provenance.producer_version.is_empty() {
            errors.push(NativeVerificationBundleError::EmptyProvenanceField(
                "provenance.producer_version",
            ));
        }
        if let Some(source_digest) = self.provenance.source_digest {
            if source_digest.is_zero() {
                errors.push(NativeVerificationBundleError::EmptyDigest {
                    field: "provenance.source_digest",
                });
            }
            if source_digest.algorithm != ProofDigestAlgorithm::Sha256 {
                errors.push(NativeVerificationBundleError::NonCryptographicDigest {
                    field: "provenance.source_digest",
                });
            }
            if let Some(input_digest) = self.source_digest()
                && input_digest != source_digest
            {
                errors.push(NativeVerificationBundleError::InputDigestMismatch {
                    field: "provenance.source_digest",
                    expected: input_digest,
                    actual: source_digest,
                });
            }
        }
        for tool in &self.provenance.toolchain {
            validate_tool_identity("provenance.toolchain", tool, errors);
        }
    }

    fn validate_serialization(&self, errors: &mut Vec<NativeVerificationBundleError>) {
        if self.serialization.schema_version != Self::SCHEMA_VERSION {
            errors.push(
                NativeVerificationBundleError::UnsupportedSerializationSchemaVersion(
                    self.serialization.schema_version,
                ),
            );
        }
        if !self.serialization.canonical_order {
            errors.push(NativeVerificationBundleError::NonCanonicalSerialization(
                "serialization.canonical_order",
            ));
        }
        if !self.serialization.sort_unordered_sets {
            errors.push(NativeVerificationBundleError::NonCanonicalSerialization(
                "serialization.sort_unordered_sets",
            ));
        }
        if !self.serialization.messagepack_named_fields {
            errors.push(NativeVerificationBundleError::NonCanonicalSerialization(
                "serialization.messagepack_named_fields",
            ));
        }
        if self.serialization.unknown_fields != NativeUnknownFieldPolicy::Reject {
            errors.push(NativeVerificationBundleError::NonCanonicalSerialization(
                "serialization.unknown_fields",
            ));
        }
    }

    fn validate_lineage_digests(&self, errors: &mut Vec<NativeVerificationBundleError>) {
        if let Some(source_digest) = self.source_digest() {
            let found = self
                .lineage
                .nodes
                .iter()
                .any(|node| node.source_module == source_digest);
            if !found {
                errors.push(NativeVerificationBundleError::SourceDigestNotInLineage(
                    source_digest,
                ));
            }
        }

        let found_trust_ir = self
            .lineage
            .nodes
            .iter()
            .any(|node| node.target_module == self.trust_ir_module_digest);
        if !found_trust_ir {
            errors.push(NativeVerificationBundleError::TrustIrDigestNotInLineage(
                self.trust_ir_module_digest,
            ));
        }
    }

    fn validate_compiler_facts(&self, errors: &mut Vec<NativeVerificationBundleError>) {
        let known_obligations: BTreeSet<ProofId> =
            self.module.proof_obligations.iter().map(|o| o.id).collect();
        let known_functions: BTreeSet<FuncId> = self
            .module
            .functions
            .iter()
            .map(|function| function.id)
            .collect();
        let mut adt_fact_ids = BTreeSet::new();
        let mut fat_pointer_fact_ids = BTreeSet::new();
        let mut fat_pointer_facts = BTreeMap::new();
        let mut trait_object_metadata_fact_ids = BTreeSet::new();
        let mut trait_object_metadata_facts = BTreeMap::new();
        let mut pointer_offset_fact_ids = BTreeSet::new();
        let mut pointer_offset_facts = BTreeMap::new();
        let mut cast_fact_ids = BTreeSet::new();
        let mut cast_facts = BTreeMap::new();
        let mut monomorphization_ids = BTreeSet::new();
        let mut monomorphization_facts = BTreeMap::new();
        let mut monomorphization_digests = BTreeMap::new();
        let mut monomorphization_symbols = BTreeMap::new();

        for fact in &self.compiler_facts.adt_layouts {
            if !adt_fact_ids.insert(fact.id) {
                errors.push(NativeVerificationBundleError::DuplicateCompilerFactId(
                    fact.id,
                ));
            }
            validate_adt_layout_fact(&self.module, fact, errors);
        }

        for fact in &self.compiler_facts.fat_pointers {
            if !fat_pointer_fact_ids.insert(fact.id) {
                errors.push(NativeVerificationBundleError::DuplicateCompilerFactId(
                    fact.id,
                ));
            }
            fat_pointer_facts.insert(fact.id, fact);
            validate_fat_pointer_fact(&self.module, fact, errors);
        }

        for fact in &self.compiler_facts.trait_object_metadata {
            if !trait_object_metadata_fact_ids.insert(fact.id) {
                errors.push(NativeVerificationBundleError::DuplicateCompilerFactId(
                    fact.id,
                ));
            }
            trait_object_metadata_facts.insert(fact.id, fact);
            validate_trait_object_metadata_fact(
                &self.module,
                fact,
                &known_functions,
                &known_obligations,
                errors,
            );
        }

        for fact in &self.compiler_facts.pointer_offsets {
            if !pointer_offset_fact_ids.insert(fact.id) {
                errors.push(NativeVerificationBundleError::DuplicateCompilerFactId(
                    fact.id,
                ));
            }
            pointer_offset_facts.insert(fact.id, fact);
            validate_pointer_offset_fact(
                &self.module,
                fact,
                &known_functions,
                &known_obligations,
                errors,
            );
        }

        for fact in &self.compiler_facts.casts {
            if !cast_fact_ids.insert(fact.id) {
                errors.push(NativeVerificationBundleError::DuplicateCompilerFactId(
                    fact.id,
                ));
            }
            cast_facts.insert(fact.id, fact);
            validate_cast_fact(
                &self.module,
                fact,
                &known_functions,
                &known_obligations,
                errors,
            );
        }

        for fact in &self.compiler_facts.monomorphizations {
            if !monomorphization_ids.insert(fact.id) {
                errors.push(NativeVerificationBundleError::DuplicateMonomorphizationId(
                    fact.id,
                ));
            }
            monomorphization_facts.insert(fact.id, fact);
            if monomorphization_digests
                .insert(fact.stable_digest, fact.id)
                .is_some()
            {
                errors.push(NativeVerificationBundleError::InvalidCompilerFact {
                    fact: NativeCompilerFactRef::Monomorphization(fact.id),
                    field: "stable_digest.duplicate",
                });
            }
            if monomorphization_symbols
                .insert(fact.symbol.as_str(), fact.id)
                .is_some()
            {
                errors.push(NativeVerificationBundleError::InvalidCompilerFact {
                    fact: NativeCompilerFactRef::Monomorphization(fact.id),
                    field: "symbol.duplicate",
                });
            }
            if !valid_monomorphization_identity_text(&fact.source_item) {
                errors.push(NativeVerificationBundleError::InvalidCompilerFact {
                    fact: NativeCompilerFactRef::Monomorphization(fact.id),
                    field: "source_item",
                });
            }
            if !valid_monomorphization_identity_text(&fact.symbol) {
                errors.push(NativeVerificationBundleError::InvalidCompilerFact {
                    fact: NativeCompilerFactRef::Monomorphization(fact.id),
                    field: "symbol",
                });
            }
            if fact.stable_digest.is_zero() {
                errors.push(NativeVerificationBundleError::InvalidCompilerFact {
                    fact: NativeCompilerFactRef::Monomorphization(fact.id),
                    field: "stable_digest",
                });
            }
            if fact.stable_digest.algorithm != ProofDigestAlgorithm::Sha256 {
                errors.push(NativeVerificationBundleError::InvalidCompilerFact {
                    fact: NativeCompilerFactRef::Monomorphization(fact.id),
                    field: "stable_digest.algorithm",
                });
            }
            if let Some(function) = fact.function
                && !known_functions.contains(&function)
            {
                errors.push(NativeVerificationBundleError::UnknownCompilerFactFunction {
                    fact: NativeCompilerFactRef::Monomorphization(fact.id),
                    function,
                });
            }
            for arg in &fact.generic_args {
                let ty = match arg {
                    NativeGenericArg::Ty(ty) | NativeGenericArg::Const { ty, .. } => Some(ty),
                    NativeGenericArg::LifetimeErased | NativeGenericArg::Placeholder { .. } => None,
                };
                if ty.is_some_and(Ty::contains_error) {
                    errors.push(NativeVerificationBundleError::InvalidCompilerFact {
                        fact: NativeCompilerFactRef::Monomorphization(fact.id),
                        field: "generic_args[].ty",
                    });
                }
                if let NativeGenericArg::Const { ty, value } = arg
                    && !value.value_matches_ty(ty)
                {
                    errors.push(NativeVerificationBundleError::InvalidCompilerFact {
                        fact: NativeCompilerFactRef::Monomorphization(fact.id),
                        field: "generic_args[].const",
                    });
                }
            }
        }

        let mut mapped_obligations = BTreeSet::new();
        let mut mapped_public_obligations = BTreeMap::new();
        for source in &self.compiler_facts.obligation_sources {
            if !mapped_obligations.insert(source.obligation) {
                errors.push(NativeVerificationBundleError::DuplicateObligationSource(
                    source.obligation,
                ));
            }
            if !known_obligations.contains(&source.obligation) {
                errors.push(NativeVerificationBundleError::UnknownObligationSource(
                    source.obligation,
                ));
            }
            if !canonical_public_obligation_id(&source.public_obligation_id) {
                errors.push(NativeVerificationBundleError::InvalidPublicObligationId {
                    obligation: source.obligation,
                });
            }
            if let Some(first_obligation) = mapped_public_obligations
                .insert(source.public_obligation_id.as_str(), source.obligation)
                && first_obligation != source.obligation
            {
                errors.push(
                    NativeVerificationBundleError::DuplicatePublicObligationSource {
                        public_obligation_id: source.public_obligation_id.clone(),
                        first_obligation,
                        duplicate_obligation: source.obligation,
                    },
                );
            }
            if let Some(function) = source.function
                && !known_functions.contains(&function)
            {
                errors.push(
                    NativeVerificationBundleError::UnknownObligationSourceFunction {
                        obligation: source.obligation,
                        function,
                    },
                );
            }
            if let Some(monomorphization) = source.monomorphization
                && !monomorphization_ids.contains(&monomorphization)
            {
                errors.push(NativeVerificationBundleError::UnknownMonomorphization {
                    obligation: source.obligation,
                    monomorphization,
                });
            }
            if let Some(monomorphization) = source.monomorphization
                && let Some(fact) = monomorphization_facts.get(&monomorphization)
            {
                validate_obligation_source_fact_function(
                    source,
                    NativeCompilerFactRef::Monomorphization(monomorphization),
                    fact.function,
                    errors,
                );
            }
            let mut source_facts = BTreeSet::new();
            for fact in &source.facts {
                if !source_facts.insert(*fact) {
                    errors.push(NativeVerificationBundleError::InvalidCompilerFact {
                        fact: *fact,
                        field: "obligation_sources[].facts.duplicate",
                    });
                }
            }
            match source.monomorphization {
                Some(monomorphization)
                    if !source_facts
                        .contains(&NativeCompilerFactRef::Monomorphization(monomorphization)) =>
                {
                    errors.push(NativeVerificationBundleError::InvalidCompilerFact {
                        fact: NativeCompilerFactRef::Monomorphization(monomorphization),
                        field: "obligation_sources[].facts.monomorphization",
                    });
                }
                None => {
                    for fact in &source_facts {
                        if matches!(fact, NativeCompilerFactRef::Monomorphization(_)) {
                            errors.push(NativeVerificationBundleError::InvalidCompilerFact {
                                fact: *fact,
                                field: "obligation_sources[].monomorphization",
                            });
                        }
                    }
                }
                Some(_) => {}
            }
            if source.cause == NativeObligationCause::CastCheck
                && !obligation_source_has_bound_cast_fact(source, &cast_facts)
            {
                errors.push(
                    NativeVerificationBundleError::MissingObligationSourceCastFact {
                        obligation: source.obligation,
                    },
                );
            }
            if source.cause == NativeObligationCause::PointerOffset
                && !obligation_source_has_bound_pointer_offset_fact(source, &pointer_offset_facts)
            {
                errors.push(
                    NativeVerificationBundleError::MissingObligationSourcePointerOffsetFact {
                        obligation: source.obligation,
                    },
                );
            }
            for fact in &source.facts {
                if let NativeCompilerFactRef::Monomorphization(actual) = fact
                    && let Some(expected) = source.monomorphization
                    && expected != *actual
                {
                    errors.push(
                        NativeVerificationBundleError::ObligationSourceFactMonomorphizationMismatch {
                            obligation: source.obligation,
                            expected,
                            actual: *actual,
                        },
                    );
                }
                let known = match fact {
                    NativeCompilerFactRef::AdtLayout(id) => adt_fact_ids.contains(id),
                    NativeCompilerFactRef::FatPointer(id) => fat_pointer_fact_ids.contains(id),
                    NativeCompilerFactRef::TraitObjectMetadata(id) => {
                        trait_object_metadata_fact_ids.contains(id)
                    }
                    NativeCompilerFactRef::PointerOffset(id) => {
                        pointer_offset_fact_ids.contains(id)
                    }
                    NativeCompilerFactRef::Cast(id) => cast_fact_ids.contains(id),
                    NativeCompilerFactRef::Monomorphization(id) => {
                        monomorphization_ids.contains(id)
                    }
                };
                if !known {
                    errors.push(
                        NativeVerificationBundleError::UnknownCompilerFactReference {
                            obligation: source.obligation,
                            fact: *fact,
                        },
                    );
                }
                let facts = NativeFactMapCollection {
                    fat_pointer_facts: &fat_pointer_facts,
                    trait_object_metadata_facts: &trait_object_metadata_facts,
                    pointer_offset_facts: &pointer_offset_facts,
                    cast_facts: &cast_facts,
                    monomorphization_facts: &monomorphization_facts,
                };
                validate_obligation_source_fact_binding(source, *fact, &facts, errors);
            }
            validate_trait_object_metadata_source_coverage(
                source,
                &fat_pointer_facts,
                &trait_object_metadata_facts,
                errors,
            );
        }

        for request in &self.requests {
            for obligation in request.obligations() {
                if !mapped_obligations.contains(obligation) {
                    errors.push(NativeVerificationBundleError::MissingObligationSource {
                        request: request.id(),
                        obligation: *obligation,
                    });
                }
                let Some(proof_obligation) = self
                    .module
                    .proof_obligations
                    .iter()
                    .find(|candidate| candidate.id == *obligation)
                else {
                    continue;
                };
                let Some(embedded) = &proof_obligation.source else {
                    errors.push(
                        NativeVerificationBundleError::MissingEmbeddedObligationSource {
                            request: request.id(),
                            obligation: *obligation,
                        },
                    );
                    continue;
                };
                for (field, value) in [
                    ("source_id", embedded.source_id.as_str()),
                    ("assertion_id", embedded.assertion_id.as_str()),
                ] {
                    if !crate::proof::is_valid_proof_obligation_source_text_id(value) {
                        errors.push(
                            NativeVerificationBundleError::InvalidEmbeddedObligationSource {
                                request: request.id(),
                                obligation: *obligation,
                                field,
                            },
                        );
                    }
                }
                if let Some(range) = embedded.range {
                    if (range.file as usize) >= self.module.files.len() {
                        errors.push(
                            NativeVerificationBundleError::InvalidEmbeddedObligationSource {
                                request: request.id(),
                                obligation: *obligation,
                                field: "range.file",
                            },
                        );
                    }
                    if range.start_line == 0 || range.end_line == 0 {
                        errors.push(
                            NativeVerificationBundleError::InvalidEmbeddedObligationSource {
                                request: request.id(),
                                obligation: *obligation,
                                field: "range.line",
                            },
                        );
                    }
                    if (range.end_line, range.end_col) < (range.start_line, range.start_col) {
                        errors.push(
                            NativeVerificationBundleError::InvalidEmbeddedObligationSource {
                                request: request.id(),
                                obligation: *obligation,
                                field: "range.order",
                            },
                        );
                    }
                    if let Some(sidecar_span) = self
                        .obligation_source(*obligation)
                        .and_then(|source| source.span)
                    {
                        let embedded_start = SourceSpan {
                            file: range.file,
                            line: range.start_line,
                            col: range.start_col,
                        };
                        if embedded_start != sidecar_span {
                            errors.push(
                                NativeVerificationBundleError::EmbeddedObligationSourceSpanMismatch {
                                    request: request.id(),
                                    obligation: *obligation,
                                    expected: sidecar_span,
                                    actual: embedded_start,
                                },
                            );
                        }
                    }
                }
                let Some(public) = &embedded.public else {
                    errors.push(
                        NativeVerificationBundleError::MissingEmbeddedPublicObligationIdentity {
                            request: request.id(),
                            obligation: *obligation,
                        },
                    );
                    continue;
                };
                if !crate::proof::is_canonical_public_obligation_id(&public.obligation_id) {
                    errors.push(
                        NativeVerificationBundleError::InvalidEmbeddedObligationSource {
                            request: request.id(),
                            obligation: *obligation,
                            field: "public.obligation_id",
                        },
                    );
                }
                if public.semantic_digest.algorithm != ProofDigestAlgorithm::Sha256 {
                    errors.push(
                        NativeVerificationBundleError::InvalidEmbeddedObligationSource {
                            request: request.id(),
                            obligation: *obligation,
                            field: "public.semantic_digest.algorithm",
                        },
                    );
                }
                if public.semantic_digest.is_zero() {
                    errors.push(
                        NativeVerificationBundleError::InvalidEmbeddedObligationSource {
                            request: request.id(),
                            obligation: *obligation,
                            field: "public.semantic_digest",
                        },
                    );
                }
                if let Some(sidecar) = self.obligation_source(*obligation)
                    && sidecar.public_obligation_id != public.obligation_id
                {
                    errors.push(
                        NativeVerificationBundleError::EmbeddedPublicObligationIdMismatch {
                            request: request.id(),
                            obligation: *obligation,
                            expected: sidecar.public_obligation_id.clone(),
                            actual: public.obligation_id.clone(),
                        },
                    );
                }
            }
        }
    }

    fn validate_requests(&self, errors: &mut Vec<NativeVerificationBundleError>) {
        let known_obligations: BTreeSet<ProofId> =
            self.module.proof_obligations.iter().map(|o| o.id).collect();
        let known_obligation_status: BTreeMap<ProofId, ProofStatus> = self
            .module
            .proof_obligations
            .iter()
            .map(|obligation| (obligation.id, obligation.status))
            .collect();
        let known_certificates: BTreeSet<ProofCertificateRef> = self
            .module
            .proof_certificates
            .iter()
            .map(ProofCertificate::lineage_ref)
            .collect();
        let known_certificate_evidence: BTreeMap<ProofCertificateRef, &ProofCertificate> = self
            .module
            .proof_certificates
            .iter()
            .map(|cert| (cert.lineage_ref(), cert))
            .collect();
        // Obligations whose strong (`Discharged`/`Certified`) status is backed
        // by a lineage-bound `CleanCic` certificate AND was rechecked by a
        // kernel in this process.
        // In a kernel-less build this set is deliberately empty: a lineage
        // digest is identity/binding metadata, not proof authority.
        let replayed_authority: BTreeSet<ProofId> = self
            .module
            .proof_obligations
            .iter()
            .filter(|obligation| {
                matches!(
                    obligation.status,
                    ProofStatus::Discharged | ProofStatus::Certified
                ) && native_authority_replayed(obligation, &self.module.proof_certificates)
            })
            .map(|obligation| obligation.id)
            .collect();
        let manifest_roots: BTreeSet<ProofLineageId> = self.lineage.roots.iter().copied().collect();
        let lineage_nodes: BTreeMap<ProofLineageId, &crate::ProofLineageNode> = self
            .lineage
            .nodes
            .iter()
            .map(|node| (node.id, node))
            .collect();

        let mut request_ids = BTreeSet::new();
        for request in &self.requests {
            let request_id = request.id();
            if !request_ids.insert(request_id) {
                errors.push(NativeVerificationBundleError::DuplicateRequestId(
                    request_id,
                ));
            }

            if request.obligations().is_empty() {
                errors.push(NativeVerificationBundleError::EmptyRequestObligations(
                    request_id,
                ));
            }
            if request.lineage_roots().is_empty() {
                errors.push(NativeVerificationBundleError::EmptyLineageRoots(request_id));
            }
            validate_diagnostics(request_id, request.diagnostics(), errors);
            if request.provenance().verifier_suite != request.verifier_suite() {
                errors.push(NativeVerificationBundleError::VerifierSuiteMismatch {
                    request: request_id,
                    expected: request.verifier_suite(),
                    actual: request.provenance().verifier_suite,
                });
            }
            validate_tool_identity(
                "request.provenance.expected_verifier",
                request.provenance().expected_verifier(),
                errors,
            );
            validate_expected_verifier_identity(
                request_id,
                request.verifier_suite(),
                request.provenance().expected_verifier(),
                errors,
            );
            if request.solver_identities().is_empty() {
                errors.push(NativeVerificationBundleError::EmptyProvenanceField(
                    "request.provenance.solvers",
                ));
            }
            for solver in request.solver_identities() {
                validate_tool_identity("request.provenance.solvers", solver, errors);
            }
            match request.provenance().replay_identity() {
                Some(replay) => {
                    validate_replay_identity(request_id, request.verifier_suite(), replay, errors);
                }
                None => errors.push(NativeVerificationBundleError::MissingReplayIdentity(
                    request_id,
                )),
            }

            let mut request_obligations = BTreeSet::new();
            for obligation in request.obligations() {
                if !request_obligations.insert(*obligation) {
                    errors.push(NativeVerificationBundleError::DuplicateRequestObligation {
                        request: request_id,
                        obligation: *obligation,
                    });
                }
                if !known_obligations.contains(obligation) {
                    errors.push(NativeVerificationBundleError::UnknownRequestObligation {
                        request: request_id,
                        obligation: *obligation,
                    });
                }
            }
            validate_replay_context(
                request_id,
                &request_obligations,
                &self.compiler_facts,
                request.provenance().replay_context(),
                errors,
            );

            let mut request_lineage_roots = BTreeSet::new();
            for root in request.lineage_roots() {
                if !request_lineage_roots.insert(*root) {
                    errors.push(NativeVerificationBundleError::DuplicateRequestLineageRoot {
                        request: request_id,
                        root: *root,
                    });
                }
                if !manifest_roots.contains(root) {
                    errors.push(NativeVerificationBundleError::UnknownLineageRoot {
                        request: request_id,
                        root: *root,
                    });
                }
                if let Some(root_node) = lineage_nodes.get(root)
                    && root_node.target_module != self.trust_ir_module_digest
                {
                    errors.push(
                        NativeVerificationBundleError::RequestLineageRootTargetMismatch {
                            request: request_id,
                            root: *root,
                            expected: self.trust_ir_module_digest,
                            actual: root_node.target_module,
                        },
                    );
                }
            }

            let (_, lineage_certificates, lineage_sources) =
                lineage_closure(&self.lineage, request.lineage_roots());
            let (source_bound_obligations, source_bound_certificates) =
                source_bound_lineage_membership(
                    &self.lineage,
                    request.lineage_roots(),
                    self.source_digest(),
                );
            if let Some(source_digest) = self.source_digest()
                && !lineage_sources.contains(&source_digest)
            {
                errors.push(
                    NativeVerificationBundleError::RequestSourceDigestNotInLineage {
                        request: request_id,
                        source: source_digest,
                    },
                );
            }
            for obligation in &request_obligations {
                if !source_bound_obligations.contains(obligation) {
                    errors.push(
                        NativeVerificationBundleError::RequestObligationNotInLineage {
                            request: request_id,
                            obligation: *obligation,
                        },
                    );
                }
                if let Some(source) = self.obligation_source(*obligation)
                    && source.span.is_none()
                {
                    errors.push(NativeVerificationBundleError::MissingObligationSourceSpan {
                        request: request_id,
                        obligation: *obligation,
                    });
                }
                if let Some(source) = self.obligation_source(*obligation)
                    && source.assertion_id.is_none()
                {
                    errors.push(
                        NativeVerificationBundleError::MissingObligationSourceAssertion {
                            request: request_id,
                            obligation: *obligation,
                        },
                    );
                }
            }

            if let Some(function) = request.function()
                && self.module.function_by_id(function).is_none()
            {
                errors.push(NativeVerificationBundleError::MissingFunction {
                    request: request_id,
                    function,
                });
            }
            if let Some(function) = request.function() {
                for obligation in &request_obligations {
                    let Some(source) = self.obligation_source(*obligation) else {
                        continue;
                    };
                    match source.function {
                        Some(actual) if actual == function => {}
                        actual => {
                            errors.push(
                                NativeVerificationBundleError::RequestObligationFunctionMismatch {
                                    request: request_id,
                                    obligation: *obligation,
                                    expected: function,
                                    actual,
                                },
                            );
                        }
                    }
                }
            }

            let mut request_certificates = BTreeSet::new();
            for cert in request.certificates() {
                if !request_certificates.insert((cert.obligation, cert.prover.clone())) {
                    errors.push(NativeVerificationBundleError::DuplicateRequestCertificate {
                        request: request_id,
                        obligation: cert.obligation,
                        prover: cert.prover.clone(),
                    });
                }
                if !known_certificates.contains(cert) {
                    if known_certificates.iter().any(|known| {
                        known.obligation == cert.obligation && known.prover == cert.prover
                    }) {
                        errors.push(NativeVerificationBundleError::CertificateDigestMismatch {
                            request: request_id,
                            obligation: cert.obligation,
                            prover: cert.prover.clone(),
                        });
                    } else {
                        errors.push(NativeVerificationBundleError::MissingCertificate {
                            request: request_id,
                            obligation: cert.obligation,
                            prover: cert.prover.clone(),
                        });
                    }
                }

                if !request_obligations.contains(&cert.obligation) {
                    errors.push(
                        NativeVerificationBundleError::CertificateObligationNotRequested {
                            request: request_id,
                            obligation: cert.obligation,
                        },
                    );
                }
                if !source_bound_certificates.contains(cert) {
                    errors.push(NativeVerificationBundleError::CertificateNotInLineage {
                        request: request_id,
                        obligation: cert.obligation,
                        prover: cert.prover.clone(),
                    });
                }
                validate_certificate_prover_suite(
                    request_id,
                    request.verifier_suite(),
                    cert,
                    errors,
                );
            }

            match request {
                NativeVerificationRequest::TrustVc(trust_vc) => {
                    validate_trust_vc_request(
                        trust_vc,
                        &known_certificate_evidence,
                        &known_obligation_status,
                        &replayed_authority,
                        &lineage_certificates,
                        errors,
                    );
                }
                NativeVerificationRequest::TrustMc(trust_mc) => {
                    validate_trust_mc_request(trust_mc, errors);
                }
                NativeVerificationRequest::TrustWp(trust_wp) => {
                    validate_trust_wp_request(trust_wp, errors);
                }
            }
        }
    }

    fn validate_evidence_bundles(&self, errors: &mut Vec<NativeVerificationBundleError>) {
        let requests: BTreeMap<NativeRequestId, &NativeVerificationRequest> = self
            .requests
            .iter()
            .map(|request| (request.id(), request))
            .collect();
        let mut seen = BTreeSet::new();

        for evidence in &self.evidence_bundles {
            let request_id = evidence.request();
            let suite = evidence.verifier_suite();
            if !seen.insert((
                request_id,
                native_evidence_bundle_variant_tag(evidence),
                native_evidence_bundle_mode_tag(evidence),
            )) {
                errors.push(NativeVerificationBundleError::DuplicateEvidenceBundle {
                    request: request_id,
                    suite,
                });
            }

            let Some(request) = requests.get(&request_id).copied() else {
                errors.push(NativeVerificationBundleError::EvidenceRequestUnknown {
                    request: request_id,
                    suite,
                });
                continue;
            };

            if request.verifier_suite() != suite
                || native_request_mode_tag(request) != native_evidence_bundle_mode_tag(evidence)
            {
                errors.push(NativeVerificationBundleError::EvidenceRequestMismatch {
                    request: request_id,
                    expected: request.verifier_suite(),
                    actual: suite,
                });
            }

            if evidence.trust_ir_module_digest() != self.trust_ir_module_digest {
                errors.push(
                    NativeVerificationBundleError::EvidenceTrustIrModuleDigestMismatch {
                        request: request_id,
                        expected: self.trust_ir_module_digest,
                        actual: evidence.trust_ir_module_digest(),
                    },
                );
            }

            let expected_request_digest = request.stable_digest();
            if evidence.request_digest() != expected_request_digest {
                errors.push(
                    NativeVerificationBundleError::EvidenceRequestDigestMismatch {
                        request: request_id,
                        expected: expected_request_digest,
                        actual: evidence.request_digest(),
                    },
                );
            }

            validate_evidence_provenance_binding(request, evidence, errors);
            validate_tool_identity("evidence.verifier", evidence.verifier(), errors);
            validate_expected_verifier_identity(request_id, suite, evidence.verifier(), errors);
            if evidence.solvers().is_empty() {
                errors.push(NativeVerificationBundleError::EmptyProvenanceField(
                    "evidence.solvers",
                ));
            }
            for solver in evidence.solvers() {
                validate_tool_identity("evidence.solvers", solver, errors);
            }
            validate_replay_identity(request_id, suite, evidence.replay(), errors);
            validate_evidence_obligations(request, evidence, errors);
            validate_evidence_artifacts(evidence, errors);
        }
    }
}

/// Native-bundle evidence replay capability. Today only obligation-bound
/// CleanCic terms can qualify, and only when `clean-expr` supplies the real
/// kernel. SAT replay establishes only an embedded CNF, not the CNF↔program
/// semantic binding, so it deliberately is not an authority adapter here.
struct NativeProofAuthority;

impl crate::proof::ProofAuthorityRechecker for NativeProofAuthority {
    fn replays_authority(
        &self,
        obligation: &ProofObligation,
        certificate: &ProofCertificate,
    ) -> bool {
        #[cfg(feature = "clean-expr")]
        {
            let clean = crate::proof::CleanCicProofAuthorityRechecker {
                clean_cic: &crate::clean_expr_lowering::contract::KernelCleanCicRechecker,
            };
            if clean.replays_authority(obligation, certificate) {
                return true;
            }
        }
        #[cfg(not(feature = "clean-expr"))]
        let _ = (obligation, certificate);
        false
    }
}

fn native_authority_replayed(
    obligation: &ProofObligation,
    certificates: &[ProofCertificate],
) -> bool {
    crate::proof::obligation_has_replayed_authority(obligation, certificates, &NativeProofAuthority)
}

pub(crate) fn native_semantic_bridge_report(
    bridge: NativeSemanticBridge,
    proof_obligation: Option<&ProofObligation>,
    proof_digest: Option<ProofDigest>,
    evidence_digest: Option<ProofDigest>,
    evidence_status: NativeSemanticBridgeEvidenceStatus,
    status: NativeSemanticBridgeStatus,
    reason: NativeSemanticBridgeReason,
) -> NativeSemanticBridgeReport {
    let proof_digest =
        proof_digest.or_else(|| proof_obligation.map(native_semantic_bridge_proof_digest));
    NativeSemanticBridgeReport {
        schema: NATIVE_SEMANTIC_BRIDGE_SCHEMA.to_string(),
        schema_version: NATIVE_SEMANTIC_BRIDGE_SCHEMA_VERSION,
        bridge_digest: bridge.stable_digest(),
        bridge,
        proof_obligation: proof_obligation.map(|obligation| obligation.id),
        proof_digest,
        proof_status: proof_obligation.map(|obligation| obligation.status),
        evidence_digest,
        evidence_status,
        status,
        reason,
    }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn native_evidence_artifact_resolution<'a>(
    key: NativeEvidenceArtifactAttachmentKey,
    owner_suite: Option<NativeVerifierSuite>,
    artifact_name: Option<String>,
    byte_source_identity: Option<String>,
    byte_len: Option<usize>,
    digest: Option<ProofDigest>,
    actual_digest: Option<ProofDigest>,
    status: NativeEvidenceArtifactResolutionStatus,
    reason: NativeEvidenceArtifactResolutionReason,
) -> NativeEvidenceArtifactResolution<'a> {
    NativeEvidenceArtifactResolution {
        report: NativeEvidenceArtifactResolutionReport {
            schema: NATIVE_EVIDENCE_ARTIFACT_RESOLUTION_SCHEMA.to_string(),
            schema_version: NATIVE_EVIDENCE_ARTIFACT_RESOLUTION_SCHEMA_VERSION,
            request: key.request,
            owner_suite,
            required_kind: key.kind,
            digest_algorithm: key.digest_algorithm,
            digest: digest.unwrap_or(key.digest),
            artifact_name,
            byte_source_identity,
            byte_len,
            actual_digest,
            authority: match status {
                NativeEvidenceArtifactResolutionStatus::Resolved => {
                    NativeEvidenceArtifactAuthority::Authoritative
                }
                NativeEvidenceArtifactResolutionStatus::Blocked => {
                    NativeEvidenceArtifactAuthority::Informational
                }
            },
            status,
            reason,
        },
        bytes: None,
    }
}

pub(crate) fn native_evidence_artifact_attachment_resolution<'a>(
    request: NativeRequestId,
    owner_suite: Option<NativeVerifierSuite>,
    required_kind: NativeEvidenceArtifactKind,
    artifact: Option<&'a NativeEvidenceArtifact>,
    resolution: Option<NativeEvidenceArtifactResolution<'a>>,
    status: NativeEvidenceArtifactResolutionStatus,
    reason: NativeEvidenceArtifactResolutionReason,
) -> NativeEvidenceArtifactAttachmentResolution<'a> {
    NativeEvidenceArtifactAttachmentResolution {
        request,
        owner_suite,
        required_kind,
        artifact,
        resolution,
        status,
        reason,
    }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn petri_successor_trust_mc_chc_binding_report(
    function: FuncId,
    semantic_bridge_report: NativeSemanticBridgeReport,
    request: Option<NativeRequestId>,
    request_digest: Option<ProofDigest>,
    evidence_digest: Option<ProofDigest>,
    expected_evidence_digest: Option<ProofDigest>,
    horn_clause_artifact: Option<NativeEvidenceArtifact>,
    status: PetriSuccessorTrustMcChcBindingStatus,
    reason: PetriSuccessorTrustMcChcBindingReason,
) -> PetriSuccessorTrustMcChcBindingReport {
    PetriSuccessorTrustMcChcBindingReport {
        schema: PETRI_SUCCESSOR_TRUST_MC_CHC_BINDING_SCHEMA.to_string(),
        schema_version: PETRI_SUCCESSOR_TRUST_MC_CHC_BINDING_SCHEMA_VERSION,
        function,
        semantic_bridge_report,
        request,
        request_digest,
        evidence_digest,
        expected_evidence_digest,
        horn_clause_artifact,
        status,
        reason,
    }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn petri_successor_trust_mc_chc_proof_handoff_report(
    function: FuncId,
    binding_report: PetriSuccessorTrustMcChcBindingReport,
    proof_identity_digest: Option<ProofDigest>,
    replay: Option<ProofReplayIdentity>,
    replay_transcript_digest: Option<ProofDigest>,
    replay_transcript_artifact: Option<NativeEvidenceArtifact>,
    model_artifact: Option<NativeEvidenceArtifact>,
    solver_identities: Vec<NativeToolIdentity>,
    status: PetriSuccessorTrustMcChcProofHandoffStatus,
    reason: PetriSuccessorTrustMcChcProofHandoffReason,
) -> PetriSuccessorTrustMcChcProofHandoffReport {
    PetriSuccessorTrustMcChcProofHandoffReport {
        schema: PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_HANDOFF_SCHEMA.to_string(),
        schema_version: PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_HANDOFF_SCHEMA_VERSION,
        function,
        binding_report,
        proof_identity_digest,
        replay,
        replay_transcript_digest,
        replay_transcript_artifact,
        model_artifact,
        solver_identities,
        status,
        reason,
    }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn petri_successor_trust_mc_chc_model_validation_readiness_report(
    function: FuncId,
    proof_handoff_report: PetriSuccessorTrustMcChcProofHandoffReport,
    model_artifact: Option<NativeEvidenceArtifact>,
    model_artifact_digest: Option<ProofDigest>,
    solver_identities: Vec<NativeToolIdentity>,
    model_validated: bool,
    status: PetriSuccessorTrustMcChcModelValidationReadinessStatus,
    reason: PetriSuccessorTrustMcChcModelValidationReadinessReason,
) -> PetriSuccessorTrustMcChcModelValidationReadinessReport {
    PetriSuccessorTrustMcChcModelValidationReadinessReport {
        schema: PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_VALIDATION_READINESS_SCHEMA.to_string(),
        schema_version: PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_VALIDATION_READINESS_SCHEMA_VERSION,
        function,
        proof_handoff_report,
        model_artifact,
        model_artifact_digest,
        solver_identities,
        model_validated,
        status,
        reason,
    }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn petri_successor_semantic_bridge_proof_admission_report<'a>(
    function: FuncId,
    proof_handoff_report: PetriSuccessorTrustMcChcProofHandoffReport,
    required_artifact_kinds: Vec<NativeEvidenceArtifactKind>,
    artifact_resolutions: Vec<NativeEvidenceArtifactAttachmentResolution<'a>>,
    blocked_artifact_kind: Option<NativeEvidenceArtifactKind>,
    blocked_artifact_reason: Option<NativeEvidenceArtifactResolutionReason>,
    status: PetriSuccessorSemanticBridgeProofAdmissionStatus,
    reason: PetriSuccessorSemanticBridgeProofAdmissionReason,
) -> PetriSuccessorSemanticBridgeProofAdmissionReport<'a> {
    PetriSuccessorSemanticBridgeProofAdmissionReport {
        schema: PETRI_SUCCESSOR_SEMANTIC_BRIDGE_PROOF_ADMISSION_SCHEMA.to_string(),
        schema_version: PETRI_SUCCESSOR_SEMANTIC_BRIDGE_PROOF_ADMISSION_SCHEMA_VERSION,
        function,
        proof_handoff_report,
        required_artifact_kinds,
        artifact_resolutions,
        blocked_artifact_kind,
        blocked_artifact_reason,
        status,
        reason,
    }
}

pub(crate) fn native_semantic_bridge_proof_digest(obligation: &ProofObligation) -> ProofDigest {
    let mut bytes = Vec::new();
    write_u32_stable(&mut bytes, obligation.id.index());
    write_obligation_kind_stable(&mut bytes, &obligation.kind);
    write_proof_status_stable(&mut bytes, obligation.status);
    match &obligation.formula {
        None => write_u8_stable(&mut bytes, 0),
        Some(formula) => {
            write_u8_stable(&mut bytes, 1);
            write_proof_formula_stable(&mut bytes, formula);
        }
    }
    crate::proof::write_proof_obligation_source_identity_stable(
        &mut bytes,
        obligation.source.as_ref(),
    );
    ProofDigest::sha256_domain(
        "trust_ir.native.semantic_bridge.proof_obligation.v3",
        &bytes,
    )
}

pub(crate) fn native_semantic_bridge_proof_identity_digest(
    report: &NativeSemanticBridgeReport,
) -> ProofDigest {
    let mut bytes = Vec::new();
    write_u32_stable(
        &mut bytes,
        NATIVE_SEMANTIC_BRIDGE_PROOF_IDENTITY_SCHEMA_VERSION,
    );
    write_str_stable(&mut bytes, &report.schema);
    write_u32_stable(&mut bytes, report.schema_version);
    write_digest_stable(&mut bytes, &report.bridge_digest);
    write_option_u32_stable(&mut bytes, report.proof_obligation.map(ProofId::index));
    write_option_digest_stable(&mut bytes, report.proof_digest);
    write_option_proof_status_stable(&mut bytes, report.proof_status);
    write_option_digest_stable(&mut bytes, report.evidence_digest);
    write_semantic_bridge_evidence_status_stable(&mut bytes, report.evidence_status);
    write_semantic_bridge_status_stable(&mut bytes, report.status);
    write_semantic_bridge_reason_stable(&mut bytes, report.reason);
    ProofDigest::sha256_domain(NATIVE_SEMANTIC_BRIDGE_PROOF_IDENTITY_SCHEMA, &bytes)
}

pub(crate) fn petri_successor_trust_mc_chc_proof_evidence_identity_digest(
    report: &PetriSuccessorTrustMcChcProofHandoffReport,
) -> ProofDigest {
    let mut bytes = Vec::new();
    let semantic_bridge_report = &report.binding_report.semantic_bridge_report;
    let mut solver_identities = report.solver_identities.clone();
    solver_identities.sort();

    write_u32_stable(
        &mut bytes,
        PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_SCHEMA_VERSION,
    );
    write_str_stable(
        &mut bytes,
        PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_SCHEMA,
    );
    write_u32_stable(&mut bytes, report.function.index());
    write_str_stable(&mut bytes, &semantic_bridge_report.schema);
    write_u32_stable(&mut bytes, semantic_bridge_report.schema_version);
    write_digest_stable(&mut bytes, &semantic_bridge_report.proof_identity_digest());
    write_str_stable(&mut bytes, semantic_bridge_report.status_code());
    write_str_stable(&mut bytes, semantic_bridge_report.reason_code());
    write_str_stable(&mut bytes, semantic_bridge_report.evidence_status_code());
    write_str_stable(&mut bytes, &report.binding_report.schema);
    write_u32_stable(&mut bytes, report.binding_report.schema_version);
    write_str_stable(&mut bytes, report.binding_report.status_code());
    write_str_stable(&mut bytes, report.binding_report.reason_code());
    write_bool_stable(&mut bytes, report.binding_report.fail_closed());
    write_option_u32_stable(
        &mut bytes,
        report.binding_report.request.map(NativeRequestId::index),
    );
    write_option_digest_stable(&mut bytes, report.binding_report.request_digest);
    write_option_digest_stable(&mut bytes, report.binding_report.evidence_digest);
    write_option_digest_stable(&mut bytes, report.binding_report.expected_evidence_digest);
    match &report.binding_report.horn_clause_artifact {
        None => write_u8_stable(&mut bytes, 0),
        Some(artifact) => {
            write_u8_stable(&mut bytes, 1);
            write_evidence_artifact_stable(&mut bytes, artifact);
        }
    }
    write_str_stable(&mut bytes, &report.schema);
    write_u32_stable(&mut bytes, report.schema_version);
    write_str_stable(&mut bytes, report.status_code());
    write_str_stable(&mut bytes, report.reason_code());
    write_bool_stable(&mut bytes, report.fail_closed());
    write_option_digest_stable(&mut bytes, report.proof_identity_digest);
    match &report.replay {
        None => write_u8_stable(&mut bytes, 0),
        Some(replay) => {
            write_u8_stable(&mut bytes, 1);
            write_replay_identity_stable(&mut bytes, replay);
        }
    }
    write_option_digest_stable(&mut bytes, report.replay_transcript_digest);
    match &report.replay_transcript_artifact {
        None => write_u8_stable(&mut bytes, 0),
        Some(artifact) => {
            write_u8_stable(&mut bytes, 1);
            write_evidence_artifact_stable(&mut bytes, artifact);
        }
    }
    match &report.model_artifact {
        None => write_u8_stable(&mut bytes, 0),
        Some(artifact) => {
            write_u8_stable(&mut bytes, 1);
            write_evidence_artifact_stable(&mut bytes, artifact);
        }
    }
    write_tool_identities_stable(&mut bytes, &solver_identities);

    ProofDigest::sha256_domain(
        PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_DIGEST_CONTEXT,
        &bytes,
    )
}

fn canonical_public_obligation_id(value: &str) -> bool {
    crate::proof::is_canonical_public_obligation_id(value)
}

fn valid_monomorphization_identity_text(value: &str) -> bool {
    !value.is_empty() && value.trim() == value && !value.chars().any(char::is_control)
}

/// Native bundle validation errors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NativeVerificationBundleError {
    UnsupportedSchemaVersion(u32),
    UnsupportedSerializationSchemaVersion(u32),
    EmptyRequests,
    EmptyDigest {
        field: &'static str,
    },
    NonCryptographicDigest {
        field: &'static str,
    },
    /// The producer-supplied module identity does not hash the embedded module's
    /// canonical bytes. A lineage that repeats the same false digest cannot
    /// make the relabeling authoritative.
    TrustIrModuleDigestMismatch {
        expected: ProofDigest,
        actual: ProofDigest,
    },
    EmptyProvenanceField(&'static str),
    InvalidToolIdentityField {
        field: &'static str,
        component: &'static str,
    },
    InputDigestMismatch {
        field: &'static str,
        expected: ProofDigest,
        actual: ProofDigest,
    },
    NonCanonicalSerialization(&'static str),
    InvalidBundleDiagnosticsPolicy {
        field: &'static str,
    },
    InvalidDiagnosticsPolicy {
        request: NativeRequestId,
        field: &'static str,
    },
    VerifierSuiteMismatch {
        request: NativeRequestId,
        expected: NativeVerifierSuite,
        actual: NativeVerifierSuite,
    },
    ExpectedVerifierIdentityMismatch {
        request: NativeRequestId,
        suite: NativeVerifierSuite,
        verifier: String,
        canonical: String,
    },
    SourceDigestNotInLineage(ProofDigest),
    TrustIrDigestNotInLineage(ProofDigest),
    Lineage(Vec<ProofLineageError>),
    DuplicateRequestId(NativeRequestId),
    EmptyRequestObligations(NativeRequestId),
    DuplicateRequestObligation {
        request: NativeRequestId,
        obligation: ProofId,
    },
    UnknownRequestObligation {
        request: NativeRequestId,
        obligation: ProofId,
    },
    EmptyLineageRoots(NativeRequestId),
    DuplicateRequestLineageRoot {
        request: NativeRequestId,
        root: ProofLineageId,
    },
    UnknownLineageRoot {
        request: NativeRequestId,
        root: ProofLineageId,
    },
    RequestLineageRootTargetMismatch {
        request: NativeRequestId,
        root: ProofLineageId,
        expected: ProofDigest,
        actual: ProofDigest,
    },
    RequestSourceDigestNotInLineage {
        request: NativeRequestId,
        source: ProofDigest,
    },
    RequestObligationNotInLineage {
        request: NativeRequestId,
        obligation: ProofId,
    },
    MissingFunction {
        request: NativeRequestId,
        function: FuncId,
    },
    RequestObligationFunctionMismatch {
        request: NativeRequestId,
        obligation: ProofId,
        expected: FuncId,
        actual: Option<FuncId>,
    },
    MissingCertificate {
        request: NativeRequestId,
        obligation: ProofId,
        prover: String,
    },
    CertificateDigestMismatch {
        request: NativeRequestId,
        obligation: ProofId,
        prover: String,
    },
    CertificateObligationNotRequested {
        request: NativeRequestId,
        obligation: ProofId,
    },
    DuplicateRequestCertificate {
        request: NativeRequestId,
        obligation: ProofId,
        prover: String,
    },
    CertificateNotInLineage {
        request: NativeRequestId,
        obligation: ProofId,
        prover: String,
    },
    CertificateVerifierSuiteMismatch {
        request: NativeRequestId,
        expected: NativeVerifierSuite,
        obligation: ProofId,
        prover: String,
        canonical: String,
    },
    MissingTrustVcEvidenceForObligation {
        request: NativeRequestId,
        obligation: ProofId,
    },
    TrustedCertificateRejected {
        request: NativeRequestId,
        obligation: ProofId,
        prover: String,
    },
    TrustVcCertificateNotDischarged {
        request: NativeRequestId,
        obligation: ProofId,
        prover: String,
        status: ProofStatus,
    },
    MissingReplayIdentity(NativeRequestId),
    MissingReplayTranscriptDigest(NativeRequestId),
    InvalidReplayIdentity {
        request: NativeRequestId,
        field: &'static str,
    },
    ReplayIdentityVerifierSuiteMismatch {
        request: NativeRequestId,
        expected: NativeVerifierSuite,
        engine: String,
        canonical: String,
    },
    DuplicateReplayAtomId {
        request: NativeRequestId,
        atom: NativeReplayAtomId,
    },
    InvalidReplayAtom {
        request: NativeRequestId,
        atom: NativeReplayAtomId,
        field: &'static str,
    },
    ReplayAtomDigestMismatch {
        request: NativeRequestId,
        atom: NativeReplayAtomId,
        expected: ProofDigest,
        actual: ProofDigest,
    },
    ReplayAtomObligationNotRequested {
        request: NativeRequestId,
        atom: NativeReplayAtomId,
        obligation: ProofId,
    },
    ReplayAtomAssertionMismatch {
        request: NativeRequestId,
        atom: NativeReplayAtomId,
        obligation: ProofId,
        expected: Option<NativeAssertionId>,
        actual: NativeAssertionId,
    },
    ReplayAtomSourceSpanMismatch {
        request: NativeRequestId,
        atom: NativeReplayAtomId,
        obligation: ProofId,
        expected: SourceSpan,
        actual: SourceSpan,
    },
    UnsupportedNativeRequestMode {
        request: NativeRequestId,
        reason: NativeUnsupportedModeReason,
        detail: String,
    },
    MissingTrustWpStrongestPostconditionContext(NativeRequestId),
    InvalidTrustMcBmcOptions {
        request: NativeRequestId,
        field: &'static str,
    },
    InvalidTrustMcChcOptions {
        request: NativeRequestId,
        field: &'static str,
    },
    InvalidTrustWpOptions {
        request: NativeRequestId,
        field: &'static str,
    },
    DuplicateCompilerFactId(NativeCompilerFactId),
    DuplicateMonomorphizationId(NativeMonomorphizationId),
    InvalidCompilerFact {
        fact: NativeCompilerFactRef,
        field: &'static str,
    },
    UnknownCompilerFactFunction {
        fact: NativeCompilerFactRef,
        function: FuncId,
    },
    UnknownCompilerFactObligation {
        fact: NativeCompilerFactRef,
        obligation: ProofId,
    },
    DuplicateObligationSource(ProofId),
    InvalidPublicObligationId {
        obligation: ProofId,
    },
    DuplicatePublicObligationSource {
        public_obligation_id: String,
        first_obligation: ProofId,
        duplicate_obligation: ProofId,
    },
    UnknownObligationSource(ProofId),
    UnknownObligationSourceFunction {
        obligation: ProofId,
        function: FuncId,
    },
    MissingObligationSource {
        request: NativeRequestId,
        obligation: ProofId,
    },
    MissingEmbeddedObligationSource {
        request: NativeRequestId,
        obligation: ProofId,
    },
    MissingEmbeddedPublicObligationIdentity {
        request: NativeRequestId,
        obligation: ProofId,
    },
    InvalidEmbeddedObligationSource {
        request: NativeRequestId,
        obligation: ProofId,
        field: &'static str,
    },
    EmbeddedPublicObligationIdMismatch {
        request: NativeRequestId,
        obligation: ProofId,
        expected: String,
        actual: String,
    },
    EmbeddedObligationSourceSpanMismatch {
        request: NativeRequestId,
        obligation: ProofId,
        expected: SourceSpan,
        actual: SourceSpan,
    },
    MissingObligationSourceSpan {
        request: NativeRequestId,
        obligation: ProofId,
    },
    MissingObligationSourceAssertion {
        request: NativeRequestId,
        obligation: ProofId,
    },
    UnknownMonomorphization {
        obligation: ProofId,
        monomorphization: NativeMonomorphizationId,
    },
    UnknownCompilerFactReference {
        obligation: ProofId,
        fact: NativeCompilerFactRef,
    },
    MissingObligationSourceCastFact {
        obligation: ProofId,
    },
    MissingObligationSourcePointerOffsetFact {
        obligation: ProofId,
    },
    MissingObligationSourceTraitObjectMetadataFact {
        obligation: ProofId,
        fat_pointer: NativeCompilerFactId,
    },
    ObligationSourceFactMonomorphizationMismatch {
        obligation: ProofId,
        expected: NativeMonomorphizationId,
        actual: NativeMonomorphizationId,
    },
    ObligationSourceFactFunctionMismatch {
        obligation: ProofId,
        fact: NativeCompilerFactRef,
        expected: Option<FuncId>,
        actual: Option<FuncId>,
    },
    ObligationSourceFactObligationMismatch {
        obligation: ProofId,
        fact: NativeCompilerFactRef,
    },
    DuplicateEvidenceBundle {
        request: NativeRequestId,
        suite: NativeVerifierSuite,
    },
    EvidenceRequestUnknown {
        request: NativeRequestId,
        suite: NativeVerifierSuite,
    },
    EvidenceRequestMismatch {
        request: NativeRequestId,
        expected: NativeVerifierSuite,
        actual: NativeVerifierSuite,
    },
    EvidenceTrustIrModuleDigestMismatch {
        request: NativeRequestId,
        expected: ProofDigest,
        actual: ProofDigest,
    },
    EvidenceRequestDigestMismatch {
        request: NativeRequestId,
        expected: ProofDigest,
        actual: ProofDigest,
    },
    EvidenceProvenanceMismatch {
        request: NativeRequestId,
        field: &'static str,
    },
    EvidenceObligationMismatch {
        request: NativeRequestId,
        obligation: ProofId,
    },
    MissingEvidenceArtifacts {
        request: NativeRequestId,
        suite: NativeVerifierSuite,
    },
    DuplicateEvidenceArtifact {
        request: NativeRequestId,
        name: String,
    },
    InvalidEvidenceArtifact {
        request: NativeRequestId,
        name: String,
        field: &'static str,
    },
    EvidenceArtifactSuiteMismatch {
        request: NativeRequestId,
        suite: NativeVerifierSuite,
        kind: NativeEvidenceArtifactKind,
    },
}

impl core::fmt::Display for NativeVerificationBundleError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            NativeVerificationBundleError::UnsupportedSchemaVersion(version) => {
                write!(
                    f,
                    "unsupported native verification bundle schema version {version}"
                )
            }
            NativeVerificationBundleError::UnsupportedSerializationSchemaVersion(version) => {
                write!(
                    f,
                    "unsupported native verification serialization schema version {version}"
                )
            }
            NativeVerificationBundleError::EmptyRequests => {
                f.write_str("native verification bundle has no requests")
            }
            NativeVerificationBundleError::EmptyDigest { field } => {
                write!(f, "native verification bundle has empty {field} digest")
            }
            NativeVerificationBundleError::NonCryptographicDigest { field } => write!(
                f,
                "native verification bundle uses a non-cryptographic {field} digest"
            ),
            NativeVerificationBundleError::TrustIrModuleDigestMismatch { expected, actual } => {
                write!(
                    f,
                    "native verification bundle claims TrustIr module digest {actual}, but the embedded module hashes to {expected}"
                )
            }
            NativeVerificationBundleError::EmptyProvenanceField(field) => {
                write!(f, "native verification bundle has empty {field}")
            }
            NativeVerificationBundleError::InvalidToolIdentityField { field, component } => {
                write!(
                    f,
                    "native verification bundle has invalid {field}.{component}"
                )
            }
            NativeVerificationBundleError::InputDigestMismatch {
                field,
                expected,
                actual,
            } => write!(
                f,
                "native verification bundle {field} digest {actual} does not match input digest {expected}"
            ),
            NativeVerificationBundleError::NonCanonicalSerialization(field) => write!(
                f,
                "native verification bundle requires canonical serialization field {field}"
            ),
            NativeVerificationBundleError::InvalidBundleDiagnosticsPolicy { field } => write!(
                f,
                "native verification bundle has invalid diagnostics policy field {field}"
            ),
            NativeVerificationBundleError::InvalidDiagnosticsPolicy { request, field } => write!(
                f,
                "native verification request {request} has invalid diagnostics policy field {field}"
            ),
            NativeVerificationBundleError::VerifierSuiteMismatch {
                request,
                expected,
                actual,
            } => write!(
                f,
                "native verification request {request} has verifier suite {actual}, expected {expected}"
            ),
            NativeVerificationBundleError::ExpectedVerifierIdentityMismatch {
                request,
                suite,
                verifier,
                canonical,
            } => write!(
                f,
                "native verification request {request} expected verifier {verifier:?} normalizes to {canonical:?}, outside {suite} suite"
            ),
            NativeVerificationBundleError::SourceDigestNotInLineage(digest) => {
                write!(
                    f,
                    "native source digest {digest} is not bound by proof lineage"
                )
            }
            NativeVerificationBundleError::TrustIrDigestNotInLineage(digest) => {
                write!(
                    f,
                    "TrustIr module digest {digest} is not bound by proof lineage"
                )
            }
            NativeVerificationBundleError::Lineage(errors) => {
                write!(
                    f,
                    "proof lineage validation failed with {} error(s)",
                    errors.len()
                )
            }
            NativeVerificationBundleError::DuplicateRequestId(id) => {
                write!(f, "native verification request {id} is duplicated")
            }
            NativeVerificationBundleError::EmptyRequestObligations(id) => {
                write!(f, "native verification request {id} binds no obligations")
            }
            NativeVerificationBundleError::DuplicateRequestObligation {
                request,
                obligation,
            } => write!(
                f,
                "native verification request {request} repeats obligation {obligation}"
            ),
            NativeVerificationBundleError::UnknownRequestObligation {
                request,
                obligation,
            } => write!(
                f,
                "native verification request {request} references unknown obligation {obligation}"
            ),
            NativeVerificationBundleError::EmptyLineageRoots(id) => {
                write!(f, "native verification request {id} has no lineage roots")
            }
            NativeVerificationBundleError::DuplicateRequestLineageRoot { request, root } => {
                write!(
                    f,
                    "native verification request {request} repeats lineage root {root}"
                )
            }
            NativeVerificationBundleError::UnknownLineageRoot { request, root } => write!(
                f,
                "native verification request {request} references unknown lineage root {root}"
            ),
            NativeVerificationBundleError::RequestLineageRootTargetMismatch {
                request,
                root,
                expected,
                actual,
            } => write!(
                f,
                "native verification request {request} lineage root {root} targets {actual}, expected TrustIr module digest {expected}"
            ),
            NativeVerificationBundleError::RequestSourceDigestNotInLineage { request, source } => {
                write!(
                    f,
                    "native verification request {request} lineage roots do not bind source digest {source}"
                )
            }
            NativeVerificationBundleError::RequestObligationNotInLineage {
                request,
                obligation,
            } => write!(
                f,
                "native verification request {request} obligation {obligation} is not bound by its lineage roots"
            ),
            NativeVerificationBundleError::MissingFunction { request, function } => write!(
                f,
                "native verification request {request} references missing function {function}"
            ),
            NativeVerificationBundleError::RequestObligationFunctionMismatch {
                request,
                obligation,
                expected,
                actual: Some(actual),
            } => write!(
                f,
                "native verification request {request} obligation {obligation} maps to function {actual}, expected request function {expected}"
            ),
            NativeVerificationBundleError::RequestObligationFunctionMismatch {
                request,
                obligation,
                expected,
                actual: None,
            } => write!(
                f,
                "native verification request {request} obligation {obligation} has no source-mapped function, expected request function {expected}"
            ),
            NativeVerificationBundleError::MissingCertificate {
                request,
                obligation,
                prover,
            } => write!(
                f,
                "native verification request {request} references missing certificate {obligation}/{prover}"
            ),
            NativeVerificationBundleError::CertificateDigestMismatch {
                request,
                obligation,
                prover,
            } => write!(
                f,
                "native verification request {request} has stale certificate digest for {obligation}/{prover}"
            ),
            NativeVerificationBundleError::CertificateObligationNotRequested {
                request,
                obligation,
            } => write!(
                f,
                "native verification request {request} references certificate for unrequested obligation {obligation}"
            ),
            NativeVerificationBundleError::DuplicateRequestCertificate {
                request,
                obligation,
                prover,
            } => write!(
                f,
                "native verification request {request} repeats certificate attachment {obligation}/{prover}"
            ),
            NativeVerificationBundleError::CertificateNotInLineage {
                request,
                obligation,
                prover,
            } => write!(
                f,
                "native verification request {request} certificate {obligation}/{prover} is not bound by its lineage roots"
            ),
            NativeVerificationBundleError::CertificateVerifierSuiteMismatch {
                request,
                expected,
                obligation,
                prover,
                canonical,
            } => write!(
                f,
                "native verification request {request} certificate {obligation}/{prover} normalizes to {canonical:?}, outside {expected} suite"
            ),
            NativeVerificationBundleError::MissingTrustVcEvidenceForObligation {
                request,
                obligation,
            } => write!(
                f,
                "native verification request {request} has no TrustVc certificate evidence for obligation {obligation}"
            ),
            NativeVerificationBundleError::TrustedCertificateRejected {
                request,
                obligation,
                prover,
            } => write!(
                f,
                "native verification request {request} rejects trusted certificate evidence {obligation}/{prover}"
            ),
            NativeVerificationBundleError::TrustVcCertificateNotDischarged {
                request,
                obligation,
                prover,
                status,
            } => write!(
                f,
                "native verification request {request} rejects TrustVc certificate evidence {obligation}/{prover} with non-discharged status {status}"
            ),
            NativeVerificationBundleError::MissingReplayIdentity(request) => write!(
                f,
                "native verification request {request} requires a replay identity"
            ),
            NativeVerificationBundleError::MissingReplayTranscriptDigest(request) => write!(
                f,
                "native verification request {request} requires a replay transcript digest"
            ),
            NativeVerificationBundleError::InvalidReplayIdentity { request, field } => write!(
                f,
                "native verification request {request} has invalid replay identity field {field}"
            ),
            NativeVerificationBundleError::ReplayIdentityVerifierSuiteMismatch {
                request,
                expected,
                engine,
                canonical,
            } => write!(
                f,
                "native verification request {request} replay engine {engine:?} normalizes to {canonical:?}, outside {expected} suite"
            ),
            NativeVerificationBundleError::DuplicateReplayAtomId { request, atom } => write!(
                f,
                "native verification request {request} repeats replay atom {atom}"
            ),
            NativeVerificationBundleError::InvalidReplayAtom {
                request,
                atom,
                field,
            } => write!(
                f,
                "native verification request {request} replay atom {atom} has invalid field {field}"
            ),
            NativeVerificationBundleError::ReplayAtomDigestMismatch {
                request,
                atom,
                expected,
                actual,
            } => write!(
                f,
                "native verification request {request} replay atom {atom} has payload digest {actual}, expected {expected}"
            ),
            NativeVerificationBundleError::ReplayAtomObligationNotRequested {
                request,
                atom,
                obligation,
            } => write!(
                f,
                "native verification request {request} replay atom {atom} references unrequested obligation {obligation}"
            ),
            NativeVerificationBundleError::ReplayAtomAssertionMismatch {
                request,
                atom,
                obligation,
                expected,
                actual,
            } => write!(
                f,
                "native verification request {request} replay atom {atom} assertion id {actual} does not match obligation {obligation} source assertion {expected:?}"
            ),
            NativeVerificationBundleError::ReplayAtomSourceSpanMismatch {
                request,
                atom,
                obligation,
                expected,
                actual,
            } => write!(
                f,
                "native verification request {request} replay atom {atom} span {actual:?} does not match obligation {obligation} source span {expected:?}"
            ),
            NativeVerificationBundleError::UnsupportedNativeRequestMode {
                request,
                reason,
                detail,
            } => write!(
                f,
                "native verification request {request} carries unsupported-mode reason {reason:?}: {detail}"
            ),
            NativeVerificationBundleError::MissingTrustWpStrongestPostconditionContext(request) => {
                write!(
                    f,
                    "native verification request {request} requires TrustWp strongest-postcondition replay atoms"
                )
            }
            NativeVerificationBundleError::InvalidTrustMcBmcOptions { request, field } => write!(
                f,
                "native verification request {request} has invalid TrustMc BMC option {field}"
            ),
            NativeVerificationBundleError::InvalidTrustMcChcOptions { request, field } => write!(
                f,
                "native verification request {request} has invalid TrustMc CHC/PDR option {field}"
            ),
            NativeVerificationBundleError::InvalidTrustWpOptions { request, field } => write!(
                f,
                "native verification request {request} has invalid TrustWp option {field}"
            ),
            NativeVerificationBundleError::DuplicateCompilerFactId(id) => {
                write!(f, "native verification compiler fact id {id} is duplicated")
            }
            NativeVerificationBundleError::DuplicateMonomorphizationId(id) => write!(
                f,
                "native verification monomorphization id {id} is duplicated"
            ),
            NativeVerificationBundleError::InvalidCompilerFact { fact, field } => write!(
                f,
                "native verification compiler fact {fact:?} has invalid field {field}"
            ),
            NativeVerificationBundleError::UnknownCompilerFactFunction { fact, function } => {
                write!(
                    f,
                    "native verification compiler fact {fact:?} references missing function {function}"
                )
            }
            NativeVerificationBundleError::UnknownCompilerFactObligation { fact, obligation } => {
                write!(
                    f,
                    "native verification compiler fact {fact:?} references unknown obligation {obligation}"
                )
            }
            NativeVerificationBundleError::DuplicateObligationSource(obligation) => write!(
                f,
                "native verification obligation {obligation} has duplicate source mappings"
            ),
            NativeVerificationBundleError::InvalidPublicObligationId { obligation } => write!(
                f,
                "native verification obligation {obligation} has an empty or non-canonical public obligation id"
            ),
            NativeVerificationBundleError::DuplicatePublicObligationSource {
                public_obligation_id,
                first_obligation,
                duplicate_obligation,
            } => write!(
                f,
                "native verification public obligation id {public_obligation_id:?} aliases native obligations {first_obligation} and {duplicate_obligation}"
            ),
            NativeVerificationBundleError::UnknownObligationSource(obligation) => write!(
                f,
                "native verification source mapping references unknown obligation {obligation}"
            ),
            NativeVerificationBundleError::UnknownObligationSourceFunction {
                obligation,
                function,
            } => write!(
                f,
                "native verification obligation {obligation} source mapping references missing function {function}"
            ),
            NativeVerificationBundleError::MissingObligationSource {
                request,
                obligation,
            } => write!(
                f,
                "native verification request {request} obligation {obligation} has no source mapping"
            ),
            NativeVerificationBundleError::MissingEmbeddedObligationSource {
                request,
                obligation,
            } => write!(
                f,
                "native verification request {request} obligation {obligation} has no embedded source identity"
            ),
            NativeVerificationBundleError::MissingEmbeddedPublicObligationIdentity {
                request,
                obligation,
            } => write!(
                f,
                "native verification request {request} obligation {obligation} has no embedded public identity"
            ),
            NativeVerificationBundleError::InvalidEmbeddedObligationSource {
                request,
                obligation,
                field,
            } => write!(
                f,
                "native verification request {request} obligation {obligation} has invalid embedded source field {field}"
            ),
            NativeVerificationBundleError::EmbeddedPublicObligationIdMismatch {
                request,
                obligation,
                expected,
                actual,
            } => write!(
                f,
                "native verification request {request} obligation {obligation} embeds public id {actual:?}, but its compiler source row names {expected:?}"
            ),
            NativeVerificationBundleError::EmbeddedObligationSourceSpanMismatch {
                request,
                obligation,
                expected,
                actual,
            } => write!(
                f,
                "native verification request {request} obligation {obligation} embeds start {}:{}:{}, but its compiler source row names {}:{}:{}",
                actual.file, actual.line, actual.col, expected.file, expected.line, expected.col,
            ),
            NativeVerificationBundleError::MissingObligationSourceSpan {
                request,
                obligation,
            } => write!(
                f,
                "native verification request {request} obligation {obligation} has no source span"
            ),
            NativeVerificationBundleError::MissingObligationSourceAssertion {
                request,
                obligation,
            } => write!(
                f,
                "native verification request {request} obligation {obligation} has no source assertion id"
            ),
            NativeVerificationBundleError::UnknownMonomorphization {
                obligation,
                monomorphization,
            } => write!(
                f,
                "native verification obligation {obligation} references unknown monomorphization {monomorphization}"
            ),
            NativeVerificationBundleError::UnknownCompilerFactReference { obligation, fact } => {
                write!(
                    f,
                    "native verification obligation {obligation} references unknown compiler fact {fact:?}"
                )
            }
            NativeVerificationBundleError::MissingObligationSourceCastFact { obligation } => {
                write!(
                    f,
                    "native verification cast-check obligation {obligation} has no bound cast fact"
                )
            }
            NativeVerificationBundleError::MissingObligationSourcePointerOffsetFact {
                obligation,
            } => {
                write!(
                    f,
                    "native verification pointer-offset obligation {obligation} has no bound pointer offset fact"
                )
            }
            NativeVerificationBundleError::MissingObligationSourceTraitObjectMetadataFact {
                obligation,
                fat_pointer,
            } => {
                write!(
                    f,
                    "native verification obligation {obligation} references trait-object fat pointer fact {fat_pointer} without a matching vtable/upcast metadata identity fact"
                )
            }
            NativeVerificationBundleError::ObligationSourceFactMonomorphizationMismatch {
                obligation,
                expected,
                actual,
            } => write!(
                f,
                "native verification obligation {obligation} source mapping references monomorphization fact {actual}, expected {expected}"
            ),
            NativeVerificationBundleError::ObligationSourceFactFunctionMismatch {
                obligation,
                fact,
                expected,
                actual,
            } => write!(
                f,
                "native verification obligation {obligation} source mapping references compiler fact {fact:?} scoped to {actual:?}, expected {expected:?}"
            ),
            NativeVerificationBundleError::ObligationSourceFactObligationMismatch {
                obligation,
                fact,
            } => write!(
                f,
                "native verification obligation {obligation} source mapping references compiler fact {fact:?} that does not bind the obligation"
            ),
            NativeVerificationBundleError::DuplicateEvidenceBundle { request, suite } => write!(
                f,
                "native verification evidence for request {request}/{suite} is duplicated"
            ),
            NativeVerificationBundleError::EvidenceRequestUnknown { request, suite } => write!(
                f,
                "native verification evidence for request {request}/{suite} has no matching request"
            ),
            NativeVerificationBundleError::EvidenceRequestMismatch {
                request,
                expected,
                actual,
            } => write!(
                f,
                "native verification evidence for request {request} has suite {actual}, expected {expected}"
            ),
            NativeVerificationBundleError::EvidenceTrustIrModuleDigestMismatch {
                request,
                expected,
                actual,
            } => write!(
                f,
                "native verification evidence for request {request} targets TrustIr module digest {actual}, expected {expected}"
            ),
            NativeVerificationBundleError::EvidenceRequestDigestMismatch {
                request,
                expected,
                actual,
            } => write!(
                f,
                "native verification evidence for request {request} binds request digest {actual}, expected {expected}"
            ),
            NativeVerificationBundleError::EvidenceProvenanceMismatch { request, field } => write!(
                f,
                "native verification evidence for request {request} has {field} not bound to request provenance"
            ),
            NativeVerificationBundleError::EvidenceObligationMismatch {
                request,
                obligation,
            } => write!(
                f,
                "native verification evidence for request {request} has mismatched obligation {obligation}"
            ),
            NativeVerificationBundleError::MissingEvidenceArtifacts { request, suite } => write!(
                f,
                "native verification evidence for request {request}/{suite} has no artifacts"
            ),
            NativeVerificationBundleError::DuplicateEvidenceArtifact { request, name } => write!(
                f,
                "native verification evidence for request {request} repeats artifact {name:?}"
            ),
            NativeVerificationBundleError::InvalidEvidenceArtifact {
                request,
                name,
                field,
            } => write!(
                f,
                "native verification evidence for request {request} artifact {name:?} has invalid field {field}"
            ),
            NativeVerificationBundleError::EvidenceArtifactSuiteMismatch {
                request,
                suite,
                kind,
            } => write!(
                f,
                "native verification evidence for request {request}/{suite} has cross-suite artifact kind {kind:?}"
            ),
        }
    }
}

impl std::error::Error for NativeVerificationBundleError {}
