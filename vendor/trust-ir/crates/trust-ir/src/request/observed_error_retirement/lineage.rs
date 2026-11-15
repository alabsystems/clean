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
retirement_match!(lineage, ProofLineageError, w;
ProofLineageError::DuplicateCertificate { node, obligation, prover } => { w.fixed(node); w.fixed(obligation); w.text(prover); },
ProofLineageError::DuplicateCertificateIdentity { node, obligation, prover } => { w.fixed(node); w.fixed(obligation); w.text(prover); },
ProofLineageError::MissingCertificate { node, obligation, prover } => { w.fixed(node); w.fixed(obligation); w.text(prover); },
ProofLineageError::CertificateDigestMismatch { node, obligation, prover } => { w.fixed(node); w.fixed(obligation); w.text(prover); },
ProofLineageError::UnsupportedSchemaVersion(a) => { w.fixed((a,)); },
ProofLineageError::EmptyManifest |
ProofLineageError::EmptyRoots => { w.fixed(()); },
ProofLineageError::DuplicateNodeId(a) |
ProofLineageError::MissingReplayIdentity(a) |
ProofLineageError::EmptyObligations(a) |
ProofLineageError::Cycle { node: a } |
ProofLineageError::MissingRoot(a) |
ProofLineageError::DuplicateRoot(a) => { w.fixed((a,)); },
ProofLineageError::EmptyTransformField { node: a, field: b } |
ProofLineageError::EmptyDigest { node: a, field: b } |
ProofLineageError::NonCryptographicDigest { node: a, field: b } |
ProofLineageError::InvalidReplayIdentity { node: a, field: b } => { w.fixed((a,b)); },
ProofLineageError::DuplicateObligation { node: a, obligation: b } |
ProofLineageError::CertificateObligationNotBound { node: a, obligation: b } |
ProofLineageError::UnknownObligation { node: a, obligation: b } => { w.fixed((a,b)); },
ProofLineageError::MissingDependency { node: a, dependency: b } |
ProofLineageError::DuplicateDependency { node: a, dependency: b } => { w.fixed((a,b)); },
ProofLineageError::DependencyDigestMismatch { node: a, dependency: b, node_source: c, dependency_target: d } => { w.fixed((a,b,c,d)); },
);
