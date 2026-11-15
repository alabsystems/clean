// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Exhaustive proof-table transport for IR transformations.
//!
//! A transformation may rewrite code, renumber functions/sites, discharge an
//! open obligation, or invalidate a fact.  Before this protocol, those actions
//! had no shared ledger: a pass could mutate a [`crate::Module`] while leaving
//! its proof table looking authoritative.  [`ProofTableTransformTransaction`]
//! binds both exact modules and accounts for every source and target obligation
//! with one explicit disposition.
//!
//! This is deliberately a **table-transport verifier**, not a theorem that the
//! code rewrite is semantics-preserving.  A transform-specific verifier must
//! still validate its function/block/instruction maps and semantic rewrite.
//! Both source and target modules must also pass independent structural/site
//! validation, and every retained strong source fact must already have
//! consumer-replayed authority. Only the conjunction of those prerequisites,
//! the transform-specific verifier, and this exhaustive transaction may
//! authorize a proof-preserving legalization, optimization, or link.

use super::evidence::{
    ModuleProofAuthority, ProofCertificate, ProofCertificateRef, ProofDigest,
    RejectingModuleProofAuthority, write_digest_stable, write_len_stable, write_str_stable,
    write_u8_stable, write_u32_stable,
};
use super::lineage::{ProofTransform, write_certificate_ref_stable, write_transform_stable};
use super::obligations::{ProofObligation, ProofStatus};
use crate::Module;
use crate::value::ProofId;
use std::collections::{BTreeMap, BTreeSet};

/// Wire/semantic version for [`ProofTableTransformTransaction`].
pub const PROOF_TABLE_TRANSFORM_SCHEMA_VERSION: u32 = 1;

/// Bound untrusted producer explanations without restricting structured proof
/// identity.  These strings are diagnostics, never authority.
pub const PROOF_TRANSFORM_TEXT_MAX_BYTES: usize = 4096;

/// What one transform did with one source proof obligation.
///
/// `Preserved` is byte-for-byte proof-table identity. `Remapped` may change
/// only structural coordinates (`ProofId`, `FuncId`, `ObligationSite`) while
/// retaining an open, non-faith-stamped claim. `Discharged` must name one exact
/// target certificate that an injected authority replays against the target
/// obligation. `Invalidated` deliberately carries no target fact.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ProofObligationDisposition {
    Preserved {
        target: ProofId,
    },
    Remapped {
        target: ProofId,
    },
    Discharged {
        target: ProofId,
        certificate: ProofCertificateRef,
    },
    Invalidated {
        reason: String,
    },
}

impl ProofObligationDisposition {
    fn target(&self) -> Option<ProofId> {
        match self {
            Self::Preserved { target }
            | Self::Remapped { target }
            | Self::Discharged { target, .. } => Some(*target),
            Self::Invalidated { .. } => None,
        }
    }
}

/// One source obligation and its unique transform disposition.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ProofObligationTransform {
    pub source: ProofId,
    pub disposition: ProofObligationDisposition,
}

/// A target obligation with no source-table predecessor.
///
/// Newly introduced `Pending`/`Failed` obligations carry no certificate.
/// Strong introduced obligations must name the sole exact target certificate
/// and pass injected authority replay. `Trusted` introduction is forbidden.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct IntroducedProofObligation {
    pub target: ProofId,
    pub justification: String,
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub certificate: Option<ProofCertificateRef>,
}

/// Canonical, digest-bound proof-table transaction proposal.
///
/// Fields are private so ordinary producers use [`Self::new`], which binds the
/// exact module digests and canonicalizes row order. Serialized input remains
/// untrusted; [`Self::validate`] or [`Self::validate_with_authority`] must be
/// called after decoding.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ProofTableTransformTransaction {
    schema_version: u32,
    transform: ProofTransform,
    source_module: ProofDigest,
    target_module: ProofDigest,
    obligations: Vec<ProofObligationTransform>,
    introduced: Vec<IntroducedProofObligation>,
}

impl ProofTableTransformTransaction {
    pub fn new(
        transform: ProofTransform,
        source: &Module,
        target: &Module,
        mut obligations: Vec<ProofObligationTransform>,
        mut introduced: Vec<IntroducedProofObligation>,
    ) -> Self {
        obligations.sort_by_key(|row| row.source.index());
        introduced.sort_by_key(|row| row.target.index());
        Self {
            schema_version: PROOF_TABLE_TRANSFORM_SCHEMA_VERSION,
            transform,
            source_module: source.stable_digest(),
            target_module: target.stable_digest(),
            obligations,
            introduced,
        }
    }

    pub const fn schema_version(&self) -> u32 {
        self.schema_version
    }

    pub fn transform(&self) -> &ProofTransform {
        &self.transform
    }

    pub const fn source_module(&self) -> ProofDigest {
        self.source_module
    }

    pub const fn target_module(&self) -> ProofDigest {
        self.target_module
    }

    pub fn obligations(&self) -> &[ProofObligationTransform] {
        &self.obligations
    }

    pub fn introduced(&self) -> &[IntroducedProofObligation] {
        &self.introduced
    }

    /// Stable identity for the transaction itself. Only canonical validated
    /// row order is meaningful; [`Self::new`] emits that order and validation
    /// rejects a non-canonical decoded carrier.
    pub fn stable_digest(&self) -> ProofDigest {
        let mut bytes = Vec::new();
        write_u32_stable(&mut bytes, self.schema_version);
        write_transform_stable(&mut bytes, &self.transform);
        write_digest_stable(&mut bytes, &self.source_module);
        write_digest_stable(&mut bytes, &self.target_module);
        write_len_stable(&mut bytes, self.obligations.len());
        for row in &self.obligations {
            write_u32_stable(&mut bytes, row.source.index());
            match &row.disposition {
                ProofObligationDisposition::Preserved { target } => {
                    write_u8_stable(&mut bytes, 0);
                    write_u32_stable(&mut bytes, target.index());
                }
                ProofObligationDisposition::Remapped { target } => {
                    write_u8_stable(&mut bytes, 1);
                    write_u32_stable(&mut bytes, target.index());
                }
                ProofObligationDisposition::Discharged {
                    target,
                    certificate,
                } => {
                    write_u8_stable(&mut bytes, 2);
                    write_u32_stable(&mut bytes, target.index());
                    write_certificate_ref_stable(&mut bytes, certificate);
                }
                ProofObligationDisposition::Invalidated { reason } => {
                    write_u8_stable(&mut bytes, 3);
                    write_str_stable(&mut bytes, reason);
                }
            }
        }
        write_len_stable(&mut bytes, self.introduced.len());
        for row in &self.introduced {
            write_u32_stable(&mut bytes, row.target.index());
            write_str_stable(&mut bytes, &row.justification);
            match &row.certificate {
                None => write_u8_stable(&mut bytes, 0),
                Some(certificate) => {
                    write_u8_stable(&mut bytes, 1);
                    write_certificate_ref_stable(&mut bytes, certificate);
                }
            }
        }
        ProofDigest::sha256_domain("trust_ir.proof.table_transform.v1", &bytes)
    }

    /// Structural validation uses a rejecting proof-authority capability.
    /// Consequently, a producer cannot turn a status/certificate payload into
    /// a newly discharged fact merely by serializing this transaction.
    pub fn validate(
        &self,
        source: &Module,
        target: &Module,
    ) -> Result<ProofTableTransformValidation, Vec<ProofTableTransformError>> {
        self.validate_with_authority(source, target, &RejectingModuleProofAuthority)
    }

    /// Validate exhaustive table transport and replay every newly strong fact
    /// through the supplied consumer-owned authority.
    ///
    /// Success does **not** validate the code rewrite. A transform-specific
    /// semantic verifier must separately bind its code/ID/site map to these
    /// same source and target module digests. Nor does this call validate
    /// module structure or mint authority for pre-existing strong source
    /// facts: callers must independently validate both modules and replay the
    /// source authority before constructing an authorizing higher-level owner.
    pub fn validate_with_authority(
        &self,
        source: &Module,
        target: &Module,
        authority: &dyn ModuleProofAuthority,
    ) -> Result<ProofTableTransformValidation, Vec<ProofTableTransformError>> {
        let mut errors = Vec::new();
        if self.schema_version != PROOF_TABLE_TRANSFORM_SCHEMA_VERSION {
            errors.push(ProofTableTransformError::UnsupportedSchema {
                found: self.schema_version,
            });
        }
        validate_transform_identity(&self.transform, &mut errors);
        if self.source_module != source.stable_digest() {
            errors.push(ProofTableTransformError::SourceDigestMismatch);
        }
        if self.target_module != target.stable_digest() {
            errors.push(ProofTableTransformError::TargetDigestMismatch);
        }
        if !strictly_ordered_sources(&self.obligations) {
            errors.push(ProofTableTransformError::NonCanonicalSourceOrder);
        }
        if !strictly_ordered_introductions(&self.introduced) {
            errors.push(ProofTableTransformError::NonCanonicalTargetOrder);
        }

        // Do not even index certificate evidence for a carrier that fails its
        // cheap envelope checks. In particular, a wrong-digest or
        // non-canonical transaction must not be able to trigger an injected
        // solver/kernel authority.
        if !errors.is_empty() {
            return Err(errors);
        }

        let source_table = obligation_table(source, true, &mut errors);
        let target_table = obligation_table(target, false, &mut errors);
        if !errors.is_empty() {
            return Err(errors);
        }
        // Group certificates once, but compute their potentially large
        // evidence identities lazily. Invalidated/open rows only need an
        // emptiness check and should not serialize unrelated CIC/SMT payloads.
        // Relevant rows are unique, so each required identity is still hashed
        // at most once per source/target side during this validation.
        let source_certificates = CertificateIndex::new(source);
        let target_certificates = CertificateIndex::new(target);
        let mut seen_source = BTreeSet::new();
        let mut seen_target = BTreeSet::new();
        let mut replay_jobs = Vec::new();
        let mut validation = ProofTableTransformValidation {
            // Hash only after validation succeeds. A decoded, non-canonical
            // carrier may contain oversized repeated rows or diagnostic text;
            // copying all of it into the digest preimage before rejecting the
            // carrier would amplify untrusted memory use.
            transaction_digest: ProofDigest::zero(),
            preserved: 0,
            remapped: 0,
            discharged: 0,
            invalidated: 0,
            introduced: 0,
        };

        for row in &self.obligations {
            if !seen_source.insert(row.source) {
                errors.push(ProofTableTransformError::DuplicateSourceDisposition {
                    source: row.source,
                });
                continue;
            }
            let Some(source_obligation) = source_table.get(&row.source).copied() else {
                errors
                    .push(ProofTableTransformError::UnknownSourceObligation { source: row.source });
                continue;
            };
            if let Some(target_id) = row.disposition.target()
                && !seen_target.insert(target_id)
            {
                errors.push(ProofTableTransformError::DuplicateTargetDisposition {
                    target: target_id,
                });
                continue;
            }

            match &row.disposition {
                ProofObligationDisposition::Preserved { target: target_id } => {
                    validation.preserved += 1;
                    let Some(target_obligation) = target_table.get(target_id).copied() else {
                        errors.push(ProofTableTransformError::UnknownTargetObligation {
                            target: *target_id,
                        });
                        continue;
                    };
                    if source_obligation != target_obligation {
                        errors.push(ProofTableTransformError::PreservedObligationChanged {
                            source: row.source,
                            target: *target_id,
                        });
                    }
                    if !certificate_refs_match(
                        source_certificates.for_obligation(row.source),
                        target_certificates.for_obligation(*target_id),
                    ) {
                        errors.push(ProofTableTransformError::PreservedCertificatesChanged {
                            source: row.source,
                            target: *target_id,
                        });
                    }
                }
                ProofObligationDisposition::Remapped { target: target_id } => {
                    validation.remapped += 1;
                    let Some(target_obligation) = target_table.get(target_id).copied() else {
                        errors.push(ProofTableTransformError::UnknownTargetObligation {
                            target: *target_id,
                        });
                        continue;
                    };
                    if !claims_match_except_transport(source_obligation, target_obligation)
                        || source_obligation.status != target_obligation.status
                    {
                        errors.push(ProofTableTransformError::RemappedClaimChanged {
                            source: row.source,
                            target: *target_id,
                        });
                    }
                    if !matches!(
                        source_obligation.status,
                        ProofStatus::Pending | ProofStatus::Failed
                    ) {
                        errors.push(ProofTableTransformError::RemappedStrongOrTrusted {
                            source: row.source,
                            target: *target_id,
                            status: source_obligation.status,
                        });
                    }
                    if !source_certificates.for_obligation(row.source).is_empty()
                        || !target_certificates.for_obligation(*target_id).is_empty()
                    {
                        errors.push(ProofTableTransformError::RemappedCertificatesPresent {
                            source: row.source,
                            target: *target_id,
                        });
                    }
                }
                ProofObligationDisposition::Discharged {
                    target: target_id,
                    certificate,
                } => {
                    validation.discharged += 1;
                    let Some(target_obligation) = target_table.get(target_id).copied() else {
                        errors.push(ProofTableTransformError::UnknownTargetObligation {
                            target: *target_id,
                        });
                        continue;
                    };
                    if source_obligation.status != ProofStatus::Pending
                        || !claims_match_except_transport(source_obligation, target_obligation)
                    {
                        errors.push(ProofTableTransformError::InvalidDischargeTransition {
                            source: row.source,
                            target: *target_id,
                        });
                    }
                    if !target_obligation.status.is_discharged_tier() {
                        errors.push(ProofTableTransformError::TargetNotStrong {
                            target: *target_id,
                            status: target_obligation.status,
                        });
                    }
                    if !source_certificates.for_obligation(row.source).is_empty() {
                        errors.push(ProofTableTransformError::DischargeSourceHasCertificates {
                            source: row.source,
                        });
                    }
                    if let Some(exact) = validate_exact_authority_certificate(
                        target_obligation,
                        certificate,
                        &target_certificates,
                        &mut errors,
                    ) {
                        replay_jobs.push((*target_id, target_obligation, exact));
                    }
                }
                ProofObligationDisposition::Invalidated { reason } => {
                    validation.invalidated += 1;
                    validate_text("invalidation reason", reason, &mut errors);
                }
            }
        }

        for row in &self.introduced {
            validation.introduced += 1;
            validate_text(
                "introduction justification",
                &row.justification,
                &mut errors,
            );
            if !seen_target.insert(row.target) {
                errors.push(ProofTableTransformError::DuplicateTargetDisposition {
                    target: row.target,
                });
                continue;
            }
            let Some(target_obligation) = target_table.get(&row.target).copied() else {
                errors
                    .push(ProofTableTransformError::UnknownTargetObligation { target: row.target });
                continue;
            };
            match target_obligation.status {
                ProofStatus::Pending | ProofStatus::Failed => {
                    if row.certificate.is_some()
                        || !target_certificates.for_obligation(row.target).is_empty()
                    {
                        errors.push(ProofTableTransformError::OpenIntroductionHasCertificate {
                            target: row.target,
                        });
                    }
                }
                ProofStatus::Discharged | ProofStatus::Certified => match &row.certificate {
                    Some(certificate) => {
                        if let Some(exact) = validate_exact_authority_certificate(
                            target_obligation,
                            certificate,
                            &target_certificates,
                            &mut errors,
                        ) {
                            replay_jobs.push((row.target, target_obligation, exact));
                        }
                    }
                    None => errors.push(
                        ProofTableTransformError::StrongIntroductionMissingCertificate {
                            target: row.target,
                        },
                    ),
                },
                ProofStatus::Trusted => {
                    errors
                        .push(ProofTableTransformError::TrustedIntroduction { target: row.target });
                }
            }
        }

        for source_id in source_table.keys() {
            if !seen_source.contains(source_id) {
                errors.push(ProofTableTransformError::MissingSourceDisposition {
                    source: *source_id,
                });
            }
        }
        for target_id in target_table.keys() {
            if !seen_target.contains(target_id) {
                errors.push(ProofTableTransformError::MissingTargetDisposition {
                    target: *target_id,
                });
            }
        }

        if !errors.is_empty() {
            return Err(errors);
        }

        // Authority replay is deliberately the last phase. It can invoke a
        // solver or proof kernel, so malformed tables and inexact certificate
        // sets must be rejected before the first replay. Fail fast on the first
        // authority rejection; later rows cannot rescue the transaction.
        for (target_id, obligation, certificate) in replay_jobs {
            if !authority.replays_authority(target, obligation, certificate) {
                errors
                    .push(ProofTableTransformError::AuthorityReplayRejected { target: target_id });
                break;
            }
        }
        if !errors.is_empty() {
            return Err(errors);
        }

        validation.transaction_digest = self.stable_digest();
        Ok(validation)
    }
}

/// Non-authorizing census returned by successful table-transport validation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProofTableTransformValidation {
    pub transaction_digest: ProofDigest,
    pub preserved: usize,
    pub remapped: usize,
    pub discharged: usize,
    pub invalidated: usize,
    pub introduced: usize,
}

/// Typed failure modes for exhaustive proof-table transport.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofTableTransformError {
    UnsupportedSchema {
        found: u32,
    },
    EmptyTransformField {
        field: &'static str,
    },
    TransformFieldTooLong {
        field: &'static str,
    },
    SourceDigestMismatch,
    TargetDigestMismatch,
    NonCanonicalSourceOrder,
    NonCanonicalTargetOrder,
    DuplicateSourceObligation {
        source: ProofId,
    },
    DuplicateTargetObligation {
        target: ProofId,
    },
    DuplicateSourceDisposition {
        source: ProofId,
    },
    DuplicateTargetDisposition {
        target: ProofId,
    },
    UnknownSourceObligation {
        source: ProofId,
    },
    UnknownTargetObligation {
        target: ProofId,
    },
    MissingSourceDisposition {
        source: ProofId,
    },
    MissingTargetDisposition {
        target: ProofId,
    },
    PreservedObligationChanged {
        source: ProofId,
        target: ProofId,
    },
    PreservedCertificatesChanged {
        source: ProofId,
        target: ProofId,
    },
    RemappedClaimChanged {
        source: ProofId,
        target: ProofId,
    },
    RemappedStrongOrTrusted {
        source: ProofId,
        target: ProofId,
        status: ProofStatus,
    },
    RemappedCertificatesPresent {
        source: ProofId,
        target: ProofId,
    },
    InvalidDischargeTransition {
        source: ProofId,
        target: ProofId,
    },
    TargetNotStrong {
        target: ProofId,
        status: ProofStatus,
    },
    DischargeSourceHasCertificates {
        source: ProofId,
    },
    CertificateNotUnique {
        target: ProofId,
    },
    CertificateSetNotExact {
        target: ProofId,
    },
    AuthorityReplayRejected {
        target: ProofId,
    },
    EmptyText {
        field: &'static str,
    },
    TextTooLong {
        field: &'static str,
    },
    OpenIntroductionHasCertificate {
        target: ProofId,
    },
    StrongIntroductionMissingCertificate {
        target: ProofId,
    },
    TrustedIntroduction {
        target: ProofId,
    },
}

impl core::fmt::Display for ProofTableTransformError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "proof-table transform transaction rejected: {self:?}")
    }
}

impl std::error::Error for ProofTableTransformError {}

fn validate_transform_identity(
    transform: &ProofTransform,
    errors: &mut Vec<ProofTableTransformError>,
) {
    for (field, value) in [
        ("name", transform.name.as_str()),
        ("producer", transform.producer.as_str()),
        ("version", transform.version.as_str()),
    ] {
        if value.trim().is_empty() {
            errors.push(ProofTableTransformError::EmptyTransformField { field });
        } else if value.len() > PROOF_TRANSFORM_TEXT_MAX_BYTES {
            errors.push(ProofTableTransformError::TransformFieldTooLong { field });
        }
    }
}

fn validate_text(field: &'static str, value: &str, errors: &mut Vec<ProofTableTransformError>) {
    if value.trim().is_empty() {
        errors.push(ProofTableTransformError::EmptyText { field });
    } else if value.len() > PROOF_TRANSFORM_TEXT_MAX_BYTES {
        errors.push(ProofTableTransformError::TextTooLong { field });
    }
}

fn strictly_ordered_sources(rows: &[ProofObligationTransform]) -> bool {
    rows.windows(2)
        .all(|window| window[0].source < window[1].source)
}

fn strictly_ordered_introductions(rows: &[IntroducedProofObligation]) -> bool {
    rows.windows(2)
        .all(|window| window[0].target < window[1].target)
}

fn obligation_table<'a>(
    module: &'a Module,
    source: bool,
    errors: &mut Vec<ProofTableTransformError>,
) -> BTreeMap<ProofId, &'a ProofObligation> {
    let mut table = BTreeMap::new();
    for obligation in &module.proof_obligations {
        if table.insert(obligation.id, obligation).is_some() {
            errors.push(if source {
                ProofTableTransformError::DuplicateSourceObligation {
                    source: obligation.id,
                }
            } else {
                ProofTableTransformError::DuplicateTargetObligation {
                    target: obligation.id,
                }
            });
        }
    }
    table
}

fn claims_match_except_transport(source: &ProofObligation, target: &ProofObligation) -> bool {
    source.kind == target.kind
        && source.description == target.description
        && source.formula == target.formula
        && source.source == target.source
}

struct CertificateIndex<'a> {
    by_obligation: BTreeMap<ProofId, Vec<&'a ProofCertificate>>,
}

impl<'a> CertificateIndex<'a> {
    fn new(module: &'a Module) -> Self {
        let mut by_obligation: BTreeMap<ProofId, Vec<&'a ProofCertificate>> = BTreeMap::new();
        for certificate in &module.proof_certificates {
            by_obligation
                .entry(certificate.obligation)
                .or_default()
                .push(certificate);
        }
        Self { by_obligation }
    }

    fn for_obligation(&self, obligation: ProofId) -> &[&'a ProofCertificate] {
        self.by_obligation
            .get(&obligation)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }
}

fn certificate_refs_match(left: &[&ProofCertificate], right: &[&ProofCertificate]) -> bool {
    if left.len() != right.len() {
        return false;
    }
    let mut left: Vec<_> = left
        .iter()
        .map(|certificate| certificate.lineage_ref())
        .collect();
    let mut right: Vec<_> = right
        .iter()
        .map(|certificate| certificate.lineage_ref())
        .collect();
    left.sort_unstable();
    right.sort_unstable();
    left == right
}

fn validate_exact_authority_certificate<'module>(
    obligation: &ProofObligation,
    expected: &ProofCertificateRef,
    certificates: &CertificateIndex<'module>,
    errors: &mut Vec<ProofTableTransformError>,
) -> Option<&'module ProofCertificate> {
    let entries = certificates.for_obligation(obligation.id);
    if entries.len() != 1 {
        errors.push(ProofTableTransformError::CertificateSetNotExact {
            target: obligation.id,
        });
        return None;
    }
    let exact = entries[0];
    if expected.obligation != obligation.id || exact.lineage_ref() != *expected {
        errors.push(ProofTableTransformError::CertificateNotUnique {
            target: obligation.id,
        });
        return None;
    }
    Some(exact)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::proof::{ObligationKind, ObligationSite, ProofEvidence, ProofTransformStage};
    use crate::value::{BlockId, FuncId};
    use std::cell::Cell;

    fn transform() -> ProofTransform {
        ProofTransform::new(
            ProofTransformStage::TrustIrOptimization,
            "proof-aware-mem2reg",
            "trust-ir",
            "1",
        )
    }

    fn obligation(id: u32, status: ProofStatus) -> ProofObligation {
        ProofObligation::new(
            ProofId::new(id),
            ObligationKind::BoundsCheck,
            status,
            "index is in bounds",
        )
    }

    fn has_error(
        result: &Result<ProofTableTransformValidation, Vec<ProofTableTransformError>>,
        predicate: impl Fn(&ProofTableTransformError) -> bool,
    ) -> bool {
        result
            .as_ref()
            .err()
            .is_some_and(|errors| errors.iter().any(predicate))
    }

    struct ReplayTestCertificate;

    impl ModuleProofAuthority for ReplayTestCertificate {
        fn replays_authority(
            &self,
            module: &Module,
            obligation: &ProofObligation,
            certificate: &ProofCertificate,
        ) -> bool {
            module.name == "target"
                && certificate.obligation == obligation.id
                && matches!(&certificate.evidence, ProofEvidence::SmtProof(bytes) if bytes == b"replayed")
        }
    }

    struct CountingAuthority {
        calls: Cell<usize>,
        accepts: bool,
    }

    impl CountingAuthority {
        fn new(accepts: bool) -> Self {
            Self {
                calls: Cell::new(0),
                accepts,
            }
        }
    }

    impl ModuleProofAuthority for CountingAuthority {
        fn replays_authority(
            &self,
            _module: &Module,
            _obligation: &ProofObligation,
            _certificate: &ProofCertificate,
        ) -> bool {
            self.calls.set(self.calls.get() + 1);
            self.accepts
        }
    }

    #[test]
    fn exact_preservation_covers_tables_and_certificates() {
        let mut source = Module::new("source");
        source
            .proof_obligations
            .push(obligation(7, ProofStatus::Trusted));
        source.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(7),
            prover: "audit".into(),
            evidence: ProofEvidence::Trusted("manual".into()),
            assurance: None,
        });
        let mut target = source.clone();
        target.name = "target".into();
        let transaction = ProofTableTransformTransaction::new(
            transform(),
            &source,
            &target,
            vec![ProofObligationTransform {
                source: ProofId::new(7),
                disposition: ProofObligationDisposition::Preserved {
                    target: ProofId::new(7),
                },
            }],
            vec![],
        );
        let validation = transaction
            .validate(&source, &target)
            .expect("exact preservation is structural, not newly minted authority");
        assert_eq!(validation.preserved, 1);
        assert_eq!(validation.transaction_digest, transaction.stable_digest());
    }

    #[test]
    fn pending_claim_may_remap_only_structural_coordinates() {
        let mut source = Module::new("source");
        source.proof_obligations.push(
            obligation(7, ProofStatus::Pending)
                .with_function(FuncId::new(3))
                .with_site(ObligationSite::new(FuncId::new(3), BlockId::new(4), 9)),
        );
        let mut target = Module::new("target");
        target.proof_obligations.push(
            obligation(2, ProofStatus::Pending)
                .with_function(FuncId::new(8))
                .with_site(ObligationSite::new(FuncId::new(8), BlockId::new(1), 5)),
        );
        let transaction = ProofTableTransformTransaction::new(
            transform(),
            &source,
            &target,
            vec![ProofObligationTransform {
                source: ProofId::new(7),
                disposition: ProofObligationDisposition::Remapped {
                    target: ProofId::new(2),
                },
            }],
            vec![],
        );
        let validation = transaction.validate(&source, &target).unwrap();
        assert_eq!(validation.remapped, 1);

        target.proof_obligations[0].description = "different claim".into();
        assert!(has_error(
            &transaction.validate(&source, &target),
            |error| matches!(error, ProofTableTransformError::TargetDigestMismatch)
        ));
    }

    #[test]
    fn strong_remap_is_rejected_instead_of_laundered() {
        let mut source = Module::new("source");
        source
            .proof_obligations
            .push(obligation(0, ProofStatus::Discharged));
        let mut target = Module::new("target");
        target
            .proof_obligations
            .push(obligation(1, ProofStatus::Discharged));
        let transaction = ProofTableTransformTransaction::new(
            transform(),
            &source,
            &target,
            vec![ProofObligationTransform {
                source: ProofId::new(0),
                disposition: ProofObligationDisposition::Remapped {
                    target: ProofId::new(1),
                },
            }],
            vec![],
        );
        assert!(has_error(
            &transaction.validate(&source, &target),
            |error| matches!(
                error,
                ProofTableTransformError::RemappedStrongOrTrusted { .. }
            )
        ));
    }

    #[test]
    fn discharge_requires_consumer_owned_replay() {
        let mut source = Module::new("source");
        source
            .proof_obligations
            .push(obligation(4, ProofStatus::Pending));
        let mut target = Module::new("target");
        target
            .proof_obligations
            .push(obligation(9, ProofStatus::Discharged));
        target.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(9),
            prover: "test-replay".into(),
            evidence: ProofEvidence::SmtProof(b"replayed".to_vec()),
            assurance: None,
        });
        let certificate = target.proof_certificates[0].lineage_ref();
        let transaction = ProofTableTransformTransaction::new(
            transform(),
            &source,
            &target,
            vec![ProofObligationTransform {
                source: ProofId::new(4),
                disposition: ProofObligationDisposition::Discharged {
                    target: ProofId::new(9),
                    certificate,
                },
            }],
            vec![],
        );
        assert!(has_error(
            &transaction.validate(&source, &target),
            |error| matches!(
                error,
                ProofTableTransformError::AuthorityReplayRejected { .. }
            )
        ));
        let validation = transaction
            .validate_with_authority(&source, &target, &ReplayTestCertificate)
            .unwrap();
        assert_eq!(validation.discharged, 1);
    }

    #[test]
    fn malformed_carriers_never_invoke_expensive_authority() {
        let mut source = Module::new("source");
        source
            .proof_obligations
            .push(obligation(4, ProofStatus::Pending));
        let mut target = Module::new("target");
        target
            .proof_obligations
            .push(obligation(9, ProofStatus::Discharged));
        target.proof_certificates.extend([
            ProofCertificate {
                obligation: ProofId::new(9),
                prover: "first".into(),
                evidence: ProofEvidence::SmtProof(b"first".to_vec()),
                assurance: None,
            },
            ProofCertificate {
                obligation: ProofId::new(9),
                prover: "extra".into(),
                evidence: ProofEvidence::SmtProof(b"extra".to_vec()),
                assurance: None,
            },
        ]);
        let certificate = target.proof_certificates[0].lineage_ref();
        let transaction = ProofTableTransformTransaction::new(
            transform(),
            &source,
            &target,
            vec![ProofObligationTransform {
                source: ProofId::new(4),
                disposition: ProofObligationDisposition::Discharged {
                    target: ProofId::new(9),
                    certificate,
                },
            }],
            vec![],
        );

        let authority = CountingAuthority::new(true);
        let result = transaction.validate_with_authority(&source, &target, &authority);
        assert!(has_error(&result, |error| matches!(
            error,
            ProofTableTransformError::CertificateSetNotExact { .. }
        )));
        assert_eq!(authority.calls.get(), 0);

        let mut wrong_envelope = transaction;
        wrong_envelope.source_module = ProofDigest::zero();
        let result = wrong_envelope.validate_with_authority(&source, &target, &authority);
        assert!(has_error(&result, |error| matches!(
            error,
            ProofTableTransformError::SourceDigestMismatch
        )));
        assert_eq!(authority.calls.get(), 0);
    }

    #[test]
    fn authority_replay_fails_fast_after_structural_admission() {
        let mut source = Module::new("source");
        let mut target = Module::new("target");
        let mut rows = Vec::new();
        for id in 0..2 {
            source
                .proof_obligations
                .push(obligation(id, ProofStatus::Pending));
            target
                .proof_obligations
                .push(obligation(id + 10, ProofStatus::Discharged));
            target.proof_certificates.push(ProofCertificate {
                obligation: ProofId::new(id + 10),
                prover: format!("proof-{id}"),
                evidence: ProofEvidence::SmtProof(vec![id as u8]),
                assurance: None,
            });
            rows.push(ProofObligationTransform {
                source: ProofId::new(id),
                disposition: ProofObligationDisposition::Discharged {
                    target: ProofId::new(id + 10),
                    certificate: target.proof_certificates[id as usize].lineage_ref(),
                },
            });
        }
        let transaction =
            ProofTableTransformTransaction::new(transform(), &source, &target, rows, vec![]);
        let authority = CountingAuthority::new(false);

        assert!(has_error(
            &transaction.validate_with_authority(&source, &target, &authority),
            |error| matches!(
                error,
                ProofTableTransformError::AuthorityReplayRejected { .. }
            )
        ));
        assert_eq!(authority.calls.get(), 1);
    }

    #[test]
    fn invalidation_and_pending_introduction_are_explicit_and_exhaustive() {
        let mut source = Module::new("source");
        source
            .proof_obligations
            .push(obligation(1, ProofStatus::Certified));
        let mut target = Module::new("target");
        target
            .proof_obligations
            .push(obligation(5, ProofStatus::Pending));
        let transaction = ProofTableTransformTransaction::new(
            transform(),
            &source,
            &target,
            vec![ProofObligationTransform {
                source: ProofId::new(1),
                disposition: ProofObligationDisposition::Invalidated {
                    reason: "rewritten site requires a fresh proof".into(),
                },
            }],
            vec![IntroducedProofObligation {
                target: ProofId::new(5),
                justification: "new legalization guard".into(),
                certificate: None,
            }],
        );
        let validation = transaction.validate(&source, &target).unwrap();
        assert_eq!(validation.invalidated, 1);
        assert_eq!(validation.introduced, 1);
    }

    #[test]
    fn missing_rows_and_duplicate_target_coverage_fail_closed() {
        let mut source = Module::new("source");
        source
            .proof_obligations
            .push(obligation(1, ProofStatus::Pending));
        let mut target = Module::new("target");
        target
            .proof_obligations
            .push(obligation(2, ProofStatus::Pending));
        let missing =
            ProofTableTransformTransaction::new(transform(), &source, &target, vec![], vec![]);
        let result = missing.validate(&source, &target);
        assert!(has_error(&result, |error| matches!(
            error,
            ProofTableTransformError::MissingSourceDisposition { .. }
        )));
        assert!(has_error(&result, |error| matches!(
            error,
            ProofTableTransformError::MissingTargetDisposition { .. }
        )));

        let duplicate = ProofTableTransformTransaction::new(
            transform(),
            &source,
            &target,
            vec![ProofObligationTransform {
                source: ProofId::new(1),
                disposition: ProofObligationDisposition::Remapped {
                    target: ProofId::new(2),
                },
            }],
            vec![IntroducedProofObligation {
                target: ProofId::new(2),
                justification: "duplicate".into(),
                certificate: None,
            }],
        );
        assert!(has_error(
            &duplicate.validate(&source, &target),
            |error| matches!(
                error,
                ProofTableTransformError::DuplicateTargetDisposition { .. }
            )
        ));
    }

    #[test]
    fn trusted_introduction_is_never_a_transform_escape_hatch() {
        let source = Module::new("source");
        let mut target = Module::new("target");
        target
            .proof_obligations
            .push(obligation(3, ProofStatus::Trusted));
        let transaction = ProofTableTransformTransaction::new(
            transform(),
            &source,
            &target,
            vec![],
            vec![IntroducedProofObligation {
                target: ProofId::new(3),
                justification: "trust me".into(),
                certificate: None,
            }],
        );
        assert!(has_error(
            &transaction.validate(&source, &target),
            |error| matches!(error, ProofTableTransformError::TrustedIntroduction { .. })
        ));
    }

    #[test]
    fn constructor_canonicalizes_rows_and_digest_binds_disposition() {
        let mut source = Module::new("source");
        source.proof_obligations.extend([
            obligation(9, ProofStatus::Pending),
            obligation(2, ProofStatus::Pending),
        ]);
        let target = Module::new("target");
        let first = ProofTableTransformTransaction::new(
            transform(),
            &source,
            &target,
            vec![
                ProofObligationTransform {
                    source: ProofId::new(9),
                    disposition: ProofObligationDisposition::Invalidated {
                        reason: "nine".into(),
                    },
                },
                ProofObligationTransform {
                    source: ProofId::new(2),
                    disposition: ProofObligationDisposition::Invalidated {
                        reason: "two".into(),
                    },
                },
            ],
            vec![],
        );
        assert_eq!(first.obligations()[0].source, ProofId::new(2));
        assert_eq!(first.obligations()[1].source, ProofId::new(9));
        first.validate(&source, &target).unwrap();

        let mut changed = first.clone();
        changed.obligations[0].disposition = ProofObligationDisposition::Invalidated {
            reason: "different".into(),
        };
        assert_ne!(first.stable_digest(), changed.stable_digest());
    }

    #[cfg(feature = "serde")]
    #[test]
    fn serialized_transaction_round_trips_but_noncanonical_input_fails_closed() {
        let mut source = Module::new("source");
        source.proof_obligations.extend([
            obligation(9, ProofStatus::Pending),
            obligation(2, ProofStatus::Pending),
        ]);
        let target = Module::new("target");
        let transaction = ProofTableTransformTransaction::new(
            transform(),
            &source,
            &target,
            vec![
                ProofObligationTransform {
                    source: ProofId::new(9),
                    disposition: ProofObligationDisposition::Invalidated {
                        reason: "removed nine".into(),
                    },
                },
                ProofObligationTransform {
                    source: ProofId::new(2),
                    disposition: ProofObligationDisposition::Invalidated {
                        reason: "removed two".into(),
                    },
                },
            ],
            vec![],
        );
        let json = serde_json::to_string(&transaction).unwrap();
        let mut decoded: ProofTableTransformTransaction = serde_json::from_str(&json).unwrap();
        assert_eq!(decoded, transaction);
        decoded.validate(&source, &target).unwrap();

        decoded.obligations.swap(0, 1);
        assert!(has_error(
            &decoded.validate(&source, &target),
            |error| matches!(error, ProofTableTransformError::NonCanonicalSourceOrder)
        ));
    }

    #[test]
    fn diagnostic_text_must_contain_non_whitespace_content() {
        let mut source = Module::new("source");
        source
            .proof_obligations
            .push(obligation(1, ProofStatus::Pending));
        let target = Module::new("target");
        let transaction = ProofTableTransformTransaction::new(
            transform(),
            &source,
            &target,
            vec![ProofObligationTransform {
                source: ProofId::new(1),
                disposition: ProofObligationDisposition::Invalidated {
                    reason: " \n\t".into(),
                },
            }],
            vec![],
        );
        assert!(has_error(
            &transaction.validate(&source, &target),
            |error| matches!(error, ProofTableTransformError::EmptyText { .. })
        ));
    }
}
