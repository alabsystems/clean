// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
// This registry enumerates every actual variant and every field. The macro
// only expands that explicit exhaustive match, avoiding duplicate disposal
// machinery. There is no wildcard drop and Copy payloads are type-checked.
macro_rules! retirement_match {
    ($method:ident, $kind:ty, $w:ident; $( $pattern:pat => $body:block ),* $(,)?) => {
        impl<O: ExecutionObserver> Work<'_, '_, O> {
            pub(super) fn $method(&mut self, value: $kind) {
                self.record(1, size_of::<$kind>());
                let $w = self;
                match value { $( $pattern => $body, )* }
                $w.poll();
            }
        }
    };
}
retirement_match!(bundle, E, w;
E::TrustIrModuleHasNoWireIdentity { location, construct } => { w.text(location); w.fixed(construct); },
E::RustReferenceAsPermissionBorrow { location } => { w.text(location); },
E::BundlePrimaryLanguageUncovered { primary, source_languages } => { w.fixed(primary); w.languages(source_languages); },
E::BundleLanguageUncovered { producer, functions, source_languages } => { w.producer(producer); w.copy_rows(functions); w.languages(source_languages); },
E::BundleImportLanguageUncovered { import, name, producer, source_languages } => { w.fixed(import); w.text(name); w.producer(producer); w.languages(source_languages); },
E::ExpectedVerifierIdentityMismatch { request, suite, verifier, canonical } => { w.fixed(request); w.fixed(suite); w.text(verifier); w.text(canonical); },
E::Lineage(v) => { w.lineage_rows(v); },
E::MissingCertificate { request, obligation, prover } => { w.fixed(request); w.fixed(obligation); w.text(prover); },
E::CertificateDigestMismatch { request, obligation, prover } => { w.fixed(request); w.fixed(obligation); w.text(prover); },
E::DuplicateRequestCertificate { request, obligation, prover } => { w.fixed(request); w.fixed(obligation); w.text(prover); },
E::CertificateNotInLineage { request, obligation, prover } => { w.fixed(request); w.fixed(obligation); w.text(prover); },
E::CertificateVerifierSuiteMismatch { request, expected, obligation, prover, canonical } => { w.fixed(request); w.fixed(expected); w.fixed(obligation); w.text(prover); w.text(canonical); },
E::TrustedCertificateRejected { request, obligation, prover } => { w.fixed(request); w.fixed(obligation); w.text(prover); },
E::TrustVcCertificateNotDischarged { request, obligation, prover, status } => { w.fixed(request); w.fixed(obligation); w.text(prover); w.fixed(status); },
E::ReplayIdentityVerifierSuiteMismatch { request, expected, engine, canonical } => { w.fixed(request); w.fixed(expected); w.text(engine); w.text(canonical); },
E::UnsupportedNativeRequestMode { request, reason, detail } => { w.fixed(request); w.fixed(reason); w.text(detail); },
E::DuplicatePublicObligationSource { public_obligation_id, first_obligation, duplicate_obligation } => { w.text(public_obligation_id); w.fixed(first_obligation); w.fixed(duplicate_obligation); },
E::EmbeddedPublicObligationIdMismatch { request, obligation, expected, actual } => { w.fixed(request); w.fixed(obligation); w.text(expected); w.text(actual); },
E::DuplicateEvidenceArtifact { request, name } => { w.fixed(request); w.text(name); },
E::InvalidEvidenceArtifact { request, name, field } => { w.fixed(request); w.text(name); w.fixed(field); },
E::TrustVcDischargeRequestCarriesCertificate { request, obligation, prover } => { w.fixed(request); w.fixed(obligation); w.text(prover); },
E::FormulaTextsDisagree { site } => { w.formula(site); },
E::UnsupportedSchemaVersion(a) |
E::UnsupportedSerializationSchemaVersion(a) => { w.fixed((a,)); },
E::EmptyRequests => { w.fixed(()); },
E::EmptyDigest { field: a } |
E::NonCryptographicDigest { field: a } |
E::EmptyProvenanceField(a) |
E::NonCanonicalSerialization(a) |
E::InvalidBundleDiagnosticsPolicy { field: a } => { w.fixed((a,)); },
E::TrustIrModuleDigestMismatch { expected: a, actual: b } => { w.fixed((a,b)); },
E::InvalidToolIdentityField { field: a, component: b } => { w.fixed((a,b)); },
E::InputDigestMismatch { field: a, expected: b, actual: c } => { w.fixed((a,b,c)); },
E::InvalidDiagnosticsPolicy { request: a, field: b } |
E::InvalidReplayIdentity { request: a, field: b } |
E::InvalidTrustMcBmcOptions { request: a, field: b } |
E::InvalidTrustMcChcOptions { request: a, field: b } |
E::InvalidTrustWpOptions { request: a, field: b } |
E::EvidenceProvenanceMismatch { request: a, field: b } => { w.fixed((a,b)); },
E::VerifierSuiteMismatch { request: a, expected: b, actual: c } |
E::EvidenceRequestMismatch { request: a, expected: b, actual: c } => { w.fixed((a,b,c)); },
E::SourceDigestNotInLineage(a) |
E::TrustIrDigestNotInLineage(a) => { w.fixed((a,)); },
E::DuplicateRequestId(a) |
E::EmptyRequestObligations(a) |
E::EmptyLineageRoots(a) |
E::MissingReplayIdentity(a) |
E::MissingReplayTranscriptDigest(a) |
E::MissingTrustWpStrongestPostconditionContext(a) |
E::MissingTrustVcDischargeFunction(a) => { w.fixed((a,)); },
E::DuplicateRequestObligation { request: a, obligation: b } |
E::UnknownRequestObligation { request: a, obligation: b } |
E::RequestObligationNotInLineage { request: a, obligation: b } |
E::CertificateObligationNotRequested { request: a, obligation: b } |
E::MissingTrustVcEvidenceForObligation { request: a, obligation: b } |
E::MissingObligationSource { request: a, obligation: b } |
E::MissingEmbeddedObligationSource { request: a, obligation: b } |
E::MissingEmbeddedPublicObligationIdentity { request: a, obligation: b } |
E::MissingObligationSourceSpan { request: a, obligation: b } |
E::MissingObligationSourceAssertion { request: a, obligation: b } |
E::EvidenceObligationMismatch { request: a, obligation: b } => { w.fixed((a,b)); },
E::DuplicateRequestLineageRoot { request: a, root: b } |
E::UnknownLineageRoot { request: a, root: b } => { w.fixed((a,b)); },
E::RequestLineageRootTargetMismatch { request: a, root: b, expected: c, actual: d } => { w.fixed((a,b,c,d)); },
E::RequestSourceDigestNotInLineage { request: a, source: b } => { w.fixed((a,b)); },
E::MissingFunction { request: a, function: b } => { w.fixed((a,b)); },
E::RequestObligationFunctionMismatch { request: a, obligation: b, expected: c, actual: d } |
E::TrustVcDischargeObligationNotSitedInFunction { request: a, obligation: b, expected: c, actual: d } => { w.fixed((a,b,c,d)); },
E::DuplicateReplayAtomId { request: a, atom: b } => { w.fixed((a,b)); },
E::InvalidReplayAtom { request: a, atom: b, field: c } => { w.fixed((a,b,c)); },
E::ReplayAtomDigestMismatch { request: a, atom: b, expected: c, actual: d } => { w.fixed((a,b,c,d)); },
E::ReplayAtomObligationNotRequested { request: a, atom: b, obligation: c } => { w.fixed((a,b,c)); },
E::ReplayAtomAssertionMismatch { request: a, atom: b, obligation: c, expected: d, actual: e } => { w.fixed((a,b,c,d,e)); },
E::ReplayAtomSourceSpanMismatch { request: a, atom: b, obligation: c, expected: d, actual: e } => { w.fixed((a,b,c,d,e)); },
E::DuplicateModuleObligationId(a) => { w.fixed((a,)); },
E::DuplicateCompilerFactId(a) => { w.fixed((a,)); },
E::DuplicateMonomorphizationId(a) => { w.fixed((a,)); },
E::InvalidCompilerFact { fact: a, field: b } => { w.fixed((a,b)); },
E::UnknownCompilerFactFunction { fact: a, function: b } => { w.fixed((a,b)); },
E::UnknownCompilerFactObligation { fact: a, obligation: b } => { w.fixed((a,b)); },
E::DuplicateObligationSource(a) |
E::InvalidPublicObligationId { obligation: a } |
E::UnknownObligationSource(a) |
E::MissingObligationSourceCastFact { obligation: a } |
E::MissingObligationSourcePointerOffsetFact { obligation: a } => { w.fixed((a,)); },
E::UnknownObligationSourceFunction { obligation: a, function: b } => { w.fixed((a,b)); },
E::InvalidEmbeddedObligationSource { request: a, obligation: b, field: c } => { w.fixed((a,b,c)); },
E::EmbeddedObligationSourceSpanMismatch { request: a, obligation: b, expected: c, actual: d } => { w.fixed((a,b,c,d)); },
E::UnknownMonomorphization { obligation: a, monomorphization: b } => { w.fixed((a,b)); },
E::UnknownCompilerFactReference { obligation: a, fact: b } |
E::ObligationSourceFactObligationMismatch { obligation: a, fact: b } => { w.fixed((a,b)); },
E::MissingObligationSourceTraitObjectMetadataFact { obligation: a, fat_pointer: b } => { w.fixed((a,b)); },
E::ObligationSourceFactMonomorphizationMismatch { obligation: a, expected: b, actual: c } => { w.fixed((a,b,c)); },
E::ObligationSourceFactFunctionMismatch { obligation: a, fact: b, expected: c, actual: d } => { w.fixed((a,b,c,d)); },
E::DuplicateEvidenceBundle { request: a, suite: b } |
E::EvidenceRequestUnknown { request: a, suite: b } |
E::MissingEvidenceArtifacts { request: a, suite: b } => { w.fixed((a,b)); },
E::EvidenceTrustIrModuleDigestMismatch { request: a, expected: b, actual: c } |
E::EvidenceRequestDigestMismatch { request: a, expected: b, actual: c } => { w.fixed((a,b,c)); },
E::EvidenceArtifactSuiteMismatch { request: a, suite: b, kind: c } => { w.fixed((a,b,c)); },
E::TrustVcObligationBothImportedAndDischarged { obligation: a, importing: b, discharging: c } => { w.fixed((a,b,c)); },
);
