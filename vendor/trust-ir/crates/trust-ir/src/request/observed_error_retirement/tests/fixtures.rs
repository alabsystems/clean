// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
pub(super) fn label() -> String {
    let mut text = String::with_capacity(8193);
    text.push_str(&"λ🦀\0".repeat(390));
    text
}
pub(super) fn strings() -> Vec<E> {
    let request = NativeRequestId::new(2);
    let obligation = ProofId::new(3);
    let suite = Suite::TrustMc;
    vec![
        E::TrustIrModuleHasNoWireIdentity {
            location: label(),
            construct: "wire",
        },
        E::RustReferenceAsPermissionBorrow { location: label() },
        E::ExpectedVerifierIdentityMismatch {
            request,
            suite,
            verifier: label(),
            canonical: label(),
        },
        E::MissingCertificate {
            request,
            obligation,
            prover: label(),
        },
        E::CertificateDigestMismatch {
            request,
            obligation,
            prover: label(),
        },
        E::DuplicateRequestCertificate {
            request,
            obligation,
            prover: label(),
        },
        E::CertificateNotInLineage {
            request,
            obligation,
            prover: label(),
        },
        E::CertificateVerifierSuiteMismatch {
            request,
            expected: suite,
            obligation,
            prover: label(),
            canonical: label(),
        },
        E::TrustedCertificateRejected {
            request,
            obligation,
            prover: label(),
        },
        E::TrustVcCertificateNotDischarged {
            request,
            obligation,
            prover: label(),
            status: ProofStatus::Certified,
        },
        E::ReplayIdentityVerifierSuiteMismatch {
            request,
            expected: suite,
            engine: label(),
            canonical: label(),
        },
        E::UnsupportedNativeRequestMode {
            request,
            reason: super::super::super::NativeUnsupportedModeReason::Other,
            detail: label(),
        },
        E::DuplicatePublicObligationSource {
            public_obligation_id: label(),
            first_obligation: obligation,
            duplicate_obligation: obligation,
        },
        E::EmbeddedPublicObligationIdMismatch {
            request,
            obligation,
            expected: label(),
            actual: label(),
        },
        E::DuplicateEvidenceArtifact {
            request,
            name: label(),
        },
        E::InvalidEvidenceArtifact {
            request,
            name: label(),
            field: "digest",
        },
        E::TrustVcDischargeRequestCarriesCertificate {
            request,
            obligation,
            prover: label(),
        },
    ]
}
pub(super) fn languages() -> BTreeSet<NativeSourceLanguage> {
    use NativeSourceLanguage::*;
    [Unknown, Rust, Swift, C, TrustIr, Other, Lean, Clean]
        .into_iter()
        .collect()
}
pub(super) fn collections() -> Vec<E> {
    vec![
        E::BundlePrimaryLanguageUncovered {
            primary: NativeSourceLanguage::Rust,
            source_languages: languages(),
        },
        E::BundleLanguageUncovered {
            producer: Some(Producer::Other(label())),
            functions: (0..110).map(FuncId::new).collect(),
            source_languages: languages(),
        },
        E::BundleImportLanguageUncovered {
            import: crate::value::ImportId::new(4),
            name: label(),
            producer: Some(Producer::Other(label())),
            source_languages: languages(),
        },
        E::Lineage(lineage()),
    ]
}
pub(super) fn lineage() -> Vec<ProofLineageError> {
    let node = ProofLineageId::new(7);
    let obligation = ProofId::new(8);
    vec![
        ProofLineageError::DuplicateCertificate {
            node,
            obligation,
            prover: label(),
        },
        ProofLineageError::DuplicateCertificateIdentity {
            node,
            obligation,
            prover: label(),
        },
        ProofLineageError::MissingCertificate {
            node,
            obligation,
            prover: label(),
        },
        ProofLineageError::CertificateDigestMismatch {
            node,
            obligation,
            prover: label(),
        },
        ProofLineageError::MissingDependency {
            node,
            dependency: node,
        },
        ProofLineageError::EmptyRoots,
    ]
}
pub(super) fn sites() -> Vec<E> {
    vec![
        E::FormulaTextsDisagree {
            site: FormulaSite::Obligation(ProofId::new(1)),
        },
        E::FormulaTextsDisagree {
            site: FormulaSite::SummaryClause {
                function: FuncId::new(4),
                clause: "ensures",
                index: usize::MAX,
            },
        },
        E::FormulaTextsDisagree {
            site: FormulaSite::SpecInvariant {
                machine: label(),
                invariant: label(),
            },
        },
        E::FormulaTextsDisagree {
            site: FormulaSite::SpecTemporal {
                machine: label(),
                property: label(),
            },
        },
    ]
}
pub(super) fn all() -> Vec<E> {
    let mut rows = strings();
    rows.extend(collections());
    rows.extend(sites());
    rows.push(E::EmptyRequests);
    rows.push(E::DuplicateModuleObligationId(ProofId::new(u32::MAX)));
    rows
}
