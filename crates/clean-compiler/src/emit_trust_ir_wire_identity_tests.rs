// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Transport controls only. Synthetic certificates below grant no proof
//! authority; successful serialization is not certificate validation.

use super::*;
use crate::emit_trust_ir_link::{link_imported_modules, LinkError, LinkedArtifact, WantedSymbol};
use trust_ir::{
    CertificateBinding, CleanCicKernelRecheck, ModuleCompleteness, Producer, ProofCertificate,
    ProofDigest, ProofEvidence, ProofId, UnloweredRow,
};

fn plain_module() -> Module {
    let mut builder = ModuleBuilder::new_with_target_info("wire_fixture", host_target_info());
    let signature = builder.add_func_type(vec![], vec![Ty::U64]);
    let mut function = builder.function("return_seven", signature);
    function.set_producer(Producer::Clean);
    let entry = function.create_block();
    function.switch_to_block(entry);
    let value = function.iconst(Ty::U64, 7);
    function.ret(vec![value]);
    function.build();
    builder.build().expect("ModuleBuilder::build: test fixture")
}

fn synthetic_recheck_module(binding: Option<Box<CertificateBinding>>) -> Module {
    let mut module = plain_module();
    module.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(73),
        prover: "synthetic transport fixture; not certified".into(),
        evidence: ProofEvidence::CleanCic {
            term: vec![1, 2],
            context: vec![3],
            lineage: ProofDigest::trust_ir_stable("synthetic.transport", b"lineage"),
            kernel_recheck: Some(CleanCicKernelRecheck {
                module: "TransportFixture".into(),
                theorems: vec![],
                anchor: "transport-fixture".into(),
                allowed_axioms: vec![],
                binding,
            }),
        },
        assurance: None,
    });
    module
}

fn completeness_cases() -> Vec<ModuleCompleteness> {
    let missing = UnloweredRow {
        symbol: "missing_definition".into(),
        display_path: Some("fixture::missing_definition".into()),
        reason: "synthetic unsupported body".into(),
    };
    vec![
        ModuleCompleteness::Complete,
        ModuleCompleteness::Partial(vec![missing.clone()]),
        ModuleCompleteness::Partial(vec![]),
        ModuleCompleteness::Partial(vec![missing.clone(), missing.clone()]),
        ModuleCompleteness::Partial(vec![UnloweredRow {
            symbol: "return_seven".into(),
            ..missing.clone()
        }]),
        ModuleCompleteness::Partial(vec![UnloweredRow {
            reason: String::new(),
            ..missing
        }]),
    ]
}

/// A synthetic certificate carrying a `CertificateBinding`. Transport only:
/// its digests name nothing, and no validator is asked about it.
fn synthetic_bound_recheck_module() -> Module {
    synthetic_recheck_module(Some(Box::new(CertificateBinding::new(
        ProofDigest::trust_ir_stable("synthetic.transport", b"environment"),
        ProofDigest::trust_ir_stable("synthetic.transport", b"statement"),
    ))))
}

/// Every module the pinned writer refuses an identity: the malformed and
/// unencodable completeness claims. A bound certificate is NOT among them
/// since trust-ir wire v61 (`certificate-binding`), whose carrier writes
/// `CleanCicKernelRecheck.binding`; it round-trips below instead.
fn refused_modules() -> Vec<(Module, &'static str)> {
    completeness_cases()
        .into_iter()
        .enumerate()
        .map(|(index, claim)| {
            let mut module = plain_module();
            module.completeness = Some(claim);
            let errors = validate_module(&module);
            if matches!(index, 0 | 1 | 5) {
                assert!(errors.is_empty(), "valid claim fixture: {errors:?}");
            } else {
                assert!(
                    !errors.is_empty(),
                    "malformed claim fixture must be nonvacuous"
                );
            }
            (module, "Module.completeness")
        })
        .collect()
}

fn assert_roundtrip(module: &Module) {
    let before = module.clone();
    let functions = module.functions.as_ptr();
    let raw = serialize_module_bytes(module).expect("unclaimed module is encodable");
    assert_eq!(
        raw,
        trust_ir::binary::serialize_module(module).expect("serialize_module: test fixture")
    );
    assert_eq!(deserialize_module_bytes(&raw).unwrap(), before);
    let tmbc = serialize_tmbc(module).expect("unclaimed module has a tMBC image");
    assert_eq!(&tmbc[..8], b"tMBC\x01\0\0\0");
    assert_eq!(&tmbc[8..], raw);
    assert_eq!(deserialize_module_bytes(&tmbc[8..]).unwrap(), before);
    assert_eq!(
        module_stable_digest_string(module).unwrap(),
        module.stable_digest().to_string()
    );
    assert_eq!(module, &before);
    assert_eq!(module.functions.as_ptr(), functions);
}

#[test]
fn wire_identity_none_and_unbound_certificate_roundtrip_without_claims() {
    let module = plain_module();
    assert!(validate_module(&module).is_empty());
    assert!(module.completeness.is_none());
    assert_roundtrip(&module);
    // This second fixture only checks lossless transport, not proof validity.
    assert_roundtrip(&synthetic_recheck_module(None));
}

/// A bound certificate has a wire identity at the pin (trust-ir v61,
/// `certificate-binding`): the pinned boundary names no blocker, and every
/// public helper transports it losslessly — the binding included — at the
/// carrier's version. Transport only, like the unbound control above.
#[test]
fn wire_identity_bound_certificate_roundtrips_at_the_binding_version() {
    let module = synthetic_bound_recheck_module();
    assert_eq!(trust_ir_build::wire_identity_blocker(&module), None);
    assert_roundtrip(&module);
    let raw = serialize_module_bytes(&module).expect("a bound certificate is encodable");
    assert_eq!(
        u32::from_le_bytes(raw[8..12].try_into().expect("header")),
        trust_ir::binary::CERTIFICATE_BINDING_FORMAT_VERSION,
        "the binding selects its carrier's version"
    );
    assert_ne!(
        raw,
        serialize_module_bytes(&synthetic_recheck_module(None)).expect("unbound twin encodes"),
        "the binding is in the bytes, not dropped"
    );
}

#[test]
fn wire_identity_all_claims_refuse_without_erasure_or_panic() {
    for (module, construct) in refused_modules() {
        let before = module.clone();
        let functions = module.functions.as_ptr();
        let upstream = trust_ir_build::wire_identity_blocker(&module)
            .expect("the pinned canonical boundary must reject the fixture");
        let outcomes = std::panic::catch_unwind(|| {
            [
                serialize_module_bytes(&module).map(|_| ()),
                serialize_tmbc(&module).map(|_| ()),
                module_stable_digest_string(&module).map(|_| ()),
            ]
        })
        .expect("public helpers must refuse before infallible serialization/digest");
        for outcome in outcomes {
            let error = outcome.expect_err("no sentinel bytes or digest may escape");
            let TrustIrError::NoWireIdentity(reason) = error else {
                panic!("expected structured canonical no-wire refusal: {error}");
            };
            assert_eq!(reason, upstream);
            assert!(reason.to_string().contains(construct), "{reason}");
        }
        assert_eq!(module, before);
        assert_eq!(module.functions.as_ptr(), functions);
    }
}

#[test]
fn wire_identity_link_none_keeps_real_identity_only_import() {
    let mut client = ModuleBuilder::new_with_target_info("client", host_target_info())
        .build()
        .expect("ModuleBuilder::build: test fixture");
    let artifact = LinkedArtifact {
        path: "synthetic dependency".into(),
        module: plain_module(),
    };
    let before = artifact.module.clone();
    let report = link_imported_modules(
        &mut client,
        std::slice::from_ref(&artifact),
        &[WantedSymbol::identity_only("return_seven")],
    )
    .expect("an ordinary dependency must still produce its real import row");
    assert_eq!(report.imports.len(), 1);
    assert_eq!(report.identity_only.len(), 1);
    assert!(report.proved.is_empty(), "no certificate was supplied");
    assert_eq!(client.imports.len(), 1);
    assert!(client.completeness.is_none());
    assert_eq!(artifact.module, before);
}

#[test]
fn wire_identity_link_refuses_client_and_dependency_before_hashing() {
    for (module, construct) in refused_modules() {
        let before = module.clone();
        for claimed_client in [false, true] {
            let ordinary = ModuleBuilder::new_with_target_info("client", host_target_info())
                .build()
                .expect("ModuleBuilder::build: test fixture");
            let mut client = if claimed_client {
                module.clone()
            } else {
                ordinary
            };
            let artifact = LinkedArtifact {
                path: "synthetic dependency".into(),
                module: if claimed_client {
                    plain_module()
                } else {
                    module.clone()
                },
            };
            let client_before = client.clone();
            let artifact_before = artifact.module.clone();
            let functions = client.functions.as_ptr();
            let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                link_imported_modules(
                    &mut client,
                    std::slice::from_ref(&artifact),
                    &[WantedSymbol::identity_only("return_seven")],
                )
            }))
            .expect("linking must refuse before an infallible digest can panic");
            let error = outcome.expect_err("unsupported metadata cannot be discarded by linking");
            assert!(matches!(error, LinkError::ConsumerRefused(_)));
            assert!(error.to_string().contains(construct), "{error}");
            assert_eq!(client, client_before);
            assert_eq!(client.functions.as_ptr(), functions);
            assert_eq!(artifact.module, artifact_before);
        }
        assert_eq!(module, before);
    }
}
