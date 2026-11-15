// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
pub(super) fn clean() -> NativeVerificationBundle {
    let mut b = crate::request::tests::native_bundle();
    b.module = Module::new("identity-prefix");
    b.compiler_facts = super::super::super::NativeCompilerFacts::default();
    b.requests.clear();
    b.evidence_bundles.clear();
    b.trust_ir_module_digest = b.module.stable_digest();
    b
}
pub(super) fn bad() -> NativeVerificationBundle {
    let mut b = clean();
    b.schema_version = u32::MAX;
    b.module.types.push(Ty::Error);
    b.module.completeness = Some(ModuleCompleteness::Complete);
    b
}
pub(super) fn legacy_zero() -> ProofDigest {
    ProofDigest {
        algorithm: ProofDigestAlgorithm::TrustIrStableV1,
        bytes: [0; 32],
    }
}
pub(super) fn wire_expected(b: &NativeVerificationBundle) -> Vec<E> {
    b.module
        .wire_image_refusals()
        .iter()
        .map(|row| {
            let (location, construct) =
                super::super::super::bundle::wire_identity_site_original_for_observed_tests(
                    &b.module, row,
                );
            E::TrustIrModuleHasNoWireIdentity {
                location,
                construct,
            }
        })
        .collect()
}
