// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for the native verification request module.

use super::*;
use crate::ProofLineageNode;
use crate::{
    Block, BlockId, FuncTy, Function, ICmpOp, InstrNode, ObligationKind, ProofEvidence,
    ProofFormula, ProofObligation, ProofObligationSourceIdentity, ProofObligationSourceRange,
    ProofReplayIdentity, ProofStatus, ProofTransform, ProofTransformStage,
    PublicObligationIdentity, Ty, ValueId,
};

/// Known-answer tests for the hand-rolled SHA-256 (the digest behind every
/// manifest/proof identity). Vectors are from FIPS 180-4 / the NIST CAVP
/// test set. Without these, a regression in the bit-twiddling core would go
/// undetected until two independently-computed identities silently diverged.
#[test]
fn sha256_known_answer_vectors() {
    fn hex(bytes: &[u8; 32]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }
    // Empty input.
    assert_eq!(
        hex(&sha256(b"")),
        "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
    );
    // "abc" (FIPS 180-4 single-block example).
    assert_eq!(
        hex(&sha256(b"abc")),
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    );
    // 56-byte message crossing the multi-block / length-padding boundary.
    assert_eq!(
        hex(&sha256(
            b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
        )),
        "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
    );
    // Exactly one block (64 bytes of 'a') exercises the padding-overflow path.
    assert_eq!(
        hex(&sha256(&[b'a'; 64])),
        "ffe054fe7ae0cb6dc65c3af9b61d5209f439851db43d0ba5997337df154668eb"
    );

    // The zero-copy multipart path must be byte-identical at every split,
    // especially around the 56-byte padding and 64-byte compression edges.
    let message: Vec<u8> = (0_u8..=129).collect();
    let expected = sha256(&message);
    for split in 0..=message.len() {
        assert_eq!(
            sha256_parts(&[&message[..split], b"", &message[split..]]),
            expected,
            "multipart SHA-256 drift at split {split}"
        );
    }
}

fn digest(seed: u8) -> ProofDigest {
    ProofDigest::sha256([seed; 32])
}

#[test]
fn native_bundle_rejects_noncryptographic_transport_identity() {
    let mut bundle = native_bundle();
    bundle.trust_ir_module_digest =
        ProofDigest::trust_ir_stable("legacy.module.identity", b"module");
    let errors = bundle
        .validate()
        .expect_err("legacy module identity must fail closed");
    assert!(errors.iter().any(|error| matches!(
        error,
        NativeVerificationBundleError::NonCryptographicDigest {
            field: "trust_ir_module_digest"
        }
    )));
}

#[test]
fn native_bundle_rejects_module_tamper_even_when_lineage_repeats_forged_digest() {
    let mut bundle = native_bundle();
    bundle.module.name.push_str("-tampered");

    // An attacker controls both serialized fields and can repeat one arbitrary
    // SHA value in the bundle and lineage. Admission must recompute from the
    // embedded module rather than accepting that internally-consistent label.
    let forged = digest(0xFE);
    bundle.trust_ir_module_digest = forged;
    for node in &mut bundle.lineage.nodes {
        if bundle.lineage.roots.contains(&node.id) {
            node.target_module = forged;
        }
    }

    let expected = bundle.module.stable_digest();
    let errors = bundle
        .validate()
        .expect_err("module relabeling must fail closed");
    assert!(errors.iter().any(|error| matches!(
        error,
        NativeVerificationBundleError::TrustIrModuleDigestMismatch {
            expected: found_expected,
            actual,
        } if *found_expected == expected && *actual == forged
    )));
}

#[test]
fn artifact_resolution_rejects_noncryptographic_digest_before_lookup() {
    let bundle = native_bundle();
    let legacy = ProofDigest::trust_ir_stable("legacy.artifact.identity", b"artifact");
    let key = NativeEvidenceArtifactAttachmentKey::new(
        NativeRequestId::new(0),
        NativeEvidenceArtifactKind::TrustVcCertificateImport,
        legacy.algorithm,
        legacy,
    );
    let resolution = bundle.resolve_evidence_artifact_attachment(key, &[]);
    assert!(resolution.report.fail_closed());
    assert_eq!(
        resolution.report.reason,
        NativeEvidenceArtifactResolutionReason::NonCryptographicDigestAlgorithm
    );
}

fn native_bundle() -> NativeVerificationBundle {
    let source_digest = digest(0xA1);
    let mut module = Module::new("trust_native_request");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I32],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut function = Function::new(FuncId::new(0), "checked_add", ft, BlockId::new(0));
    function
        .blocks
        .push(Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::I32));
    module.add_function(function);
    let source_file = module.intern_file("checked_add.rs");

    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::MemorySafety,
            ProofStatus::Discharged,
            "borrow projection stays in bounds",
        )
        .with_formula(ProofFormula::smtlib2("mir_borrow_in_bounds", "Bool"))
        .with_source(
            ProofObligationSourceIdentity::new("rust:checked_add", "assertion:6")
                .with_range(ProofObligationSourceRange {
                    file: source_file,
                    start_line: 12,
                    start_col: 5,
                    end_line: 12,
                    end_col: 6,
                })
                .with_public(PublicObligationIdentity {
                    obligation_id: "vc:checked_add:borrow-check:0".to_string(),
                    semantic_digest: ProofDigest::sha256_domain(
                        "trust-ir.test.public-obligation.v1",
                        b"borrow-check:0",
                    ),
                }),
        ),
    );
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(1),
            ObligationKind::TranslationValidation,
            ProofStatus::Pending,
            "rustc MIR lowering preserves checked_add",
        )
        .with_formula(ProofFormula::new(
            PETRI_SUCCESSOR_PLAN_CACHE_EQUIVALENCE_SCHEMA,
            "trust_ir_checked_add_equiv",
        ))
        .with_source(
            ProofObligationSourceIdentity::new("rust:checked_add", "assertion:7")
                .with_range(ProofObligationSourceRange {
                    file: source_file,
                    start_line: 13,
                    start_col: 9,
                    end_line: 13,
                    end_col: 10,
                })
                .with_public(PublicObligationIdentity {
                    obligation_id: "vc:checked_add:assert:1".to_string(),
                    semantic_digest: ProofDigest::sha256_domain(
                        "trust-ir.test.public-obligation.v1",
                        b"assert:1",
                    ),
                }),
        ),
    );

    let cert = ProofCertificate {
        obligation: ProofId::new(0),
        prover: "trust_vc".to_string(),
        evidence: ProofEvidence::LeanProof("exact TrustVc.MIR.borrow_sound".to_string()),
    };
    module.proof_certificates.push(cert.clone());
    let trust_ir_digest = module.stable_digest();

    let mut lineage_node = ProofLineageNode::new(
        ProofLineageId::new(0),
        ProofTransform::new(
            ProofTransformStage::Frontend,
            "rustc-mir-to-trust_ir",
            "tRust",
            "native-request-schema-v1",
        ),
        source_digest,
        trust_ir_digest,
    );
    lineage_node.obligations.push(ProofId::new(0));
    lineage_node.obligations.push(ProofId::new(1));
    lineage_node.certificates.push(cert.lineage_ref());
    lineage_node.replay = Some(
        ProofReplayIdentity::new("trust-full-verify", "trust verify --emit-trust_ir-bundle")
            .with_transcript_digest(ProofDigest::sha256_domain("trust.transcript.v1", b"ok")),
    );

    let lineage = ProofLineageManifest {
        schema_version: ProofLineageManifest::SCHEMA_VERSION,
        nodes: vec![lineage_node],
        roots: vec![ProofLineageId::new(0)],
    };

    let mut bundle = NativeVerificationBundle::new(
        NativeBundleProducer::TRust,
        NativeAdapterInput::RustMir {
            body_digest: source_digest,
        },
        trust_ir_digest,
        module,
        lineage,
    );
    bundle.provenance = NativeBundleProvenance {
        producer_version: "trust-test@1".to_string(),
        source_language: NativeSourceLanguage::Rust,
        source_artifact: Some("checked_add.rs".to_string()),
        source_digest: Some(source_digest),
        toolchain: vec![
            NativeToolIdentity::new("rustc").with_version("1.92.0-nightly"),
            NativeToolIdentity::new("tRust")
                .with_version("native-request-schema-v1")
                .with_revision("test-rev"),
        ],
    };
    bundle
        .compiler_facts
        .monomorphizations
        .push(NativeMonomorphizationFact {
            id: NativeMonomorphizationId::new(0),
            source_item: "checked_add".to_string(),
            symbol: "_RNvCs_test_checked_add".to_string(),
            generic_args: vec![NativeGenericArg::Ty(Ty::I32)],
            function: Some(FuncId::new(0)),
            stable_digest: ProofDigest::sha256_domain(
                "trust.monomorphization.v1",
                b"checked_add::<i32>",
            ),
        });
    bundle
        .compiler_facts
        .obligation_sources
        .push(NativeObligationSource {
            obligation: ProofId::new(0),
            public_obligation_id: "vc:checked_add:borrow-check:0".to_string(),
            function: Some(FuncId::new(0)),
            span: Some(SourceSpan {
                file: 0,
                line: 12,
                col: 5,
            }),
            assertion_id: Some(NativeAssertionId::new(6)),
            cause: NativeObligationCause::BorrowCheck,
            monomorphization: Some(NativeMonomorphizationId::new(0)),
            facts: vec![NativeCompilerFactRef::Monomorphization(
                NativeMonomorphizationId::new(0),
            )],
        });
    bundle
        .compiler_facts
        .obligation_sources
        .push(NativeObligationSource {
            obligation: ProofId::new(1),
            public_obligation_id: "vc:checked_add:assert:1".to_string(),
            function: Some(FuncId::new(0)),
            span: Some(SourceSpan {
                file: 0,
                line: 13,
                col: 9,
            }),
            assertion_id: Some(NativeAssertionId::new(7)),
            cause: NativeObligationCause::Assert,
            monomorphization: Some(NativeMonomorphizationId::new(0)),
            facts: vec![NativeCompilerFactRef::Monomorphization(
                NativeMonomorphizationId::new(0),
            )],
        });
    bundle
        .requests
        .push(NativeVerificationRequest::TrustVc(TrustVcNativeRequest {
            id: NativeRequestId::new(0),
            mode: TrustVcVerificationMode::ImportProofCertificates,
            obligations: vec![ProofId::new(0)],
            certificates: vec![cert.lineage_ref()],
            lineage_roots: vec![ProofLineageId::new(0)],
            options: TrustVcRequestOptions::default(),
            diagnostics: NativeDiagnosticsPolicy::default(),
            provenance: NativeRequestProvenance::new(
                NativeVerifierSuite::TrustVc,
                NativeToolIdentity::new("trust_vc").with_version("semantics-v1"),
            )
            .with_solver(NativeToolIdentity::new("lean4").with_version("4.18.0"))
            .with_replay(
                ProofReplayIdentity::new("trust_vc", "trust_vc import --native-bundle")
                    .with_transcript_digest(ProofDigest::sha256_domain(
                        "trust_vc.native.replay.v1",
                        b"trust_vc-import",
                    )),
            ),
            // Stays None: this fixture's obligation sources are hand-built, so a
            // Some(_) here would newly arm the `MissingFunction` /
            // `RequestObligationFunctionMismatch` checks in bundle.rs.
            function: None,
        }));
    bundle
        .requests
        .push(NativeVerificationRequest::TrustMc(TrustMcNativeRequest {
            id: NativeRequestId::new(1),
            mode: TrustMcVerificationMode::Chc,
            function: FuncId::new(0),
            obligations: vec![ProofId::new(1)],
            lineage_roots: vec![ProofLineageId::new(0)],
            options: TrustMcRequestOptions {
                chc: TrustMcChcOptions {
                    emit_horn_clauses: true,
                    ..TrustMcChcOptions::default()
                },
                ..TrustMcRequestOptions::default()
            },
            diagnostics: NativeDiagnosticsPolicy::default(),
            provenance: NativeRequestProvenance::new(
                NativeVerifierSuite::TrustMc,
                NativeToolIdentity::new("trust_mc").with_version("chc-v1"),
            )
            .with_solver(NativeToolIdentity::new("z3").with_version("4.13.0"))
            .with_replay(
                ProofReplayIdentity::new("trust_mc", "trust_mc --chc checked_add")
                    .with_transcript_digest(ProofDigest::sha256_domain(
                        "trust_mc.native.replay.v1",
                        b"trust_mc-chc",
                    )),
            ),
        }));
    bundle
        .requests
        .push(NativeVerificationRequest::TrustWp(TrustWpNativeRequest {
            id: NativeRequestId::new(2),
            mode: TrustWpVerificationMode::WeakestPrecondition,
            function: FuncId::new(0),
            obligations: vec![ProofId::new(0), ProofId::new(1)],
            lineage_roots: vec![ProofLineageId::new(0)],
            options: TrustWpRequestOptions::default(),
            diagnostics: NativeDiagnosticsPolicy::default(),
            provenance: NativeRequestProvenance::new(
                NativeVerifierSuite::TrustWp,
                NativeToolIdentity::new("trust_wp").with_version("wp-v1"),
            )
            .with_solver(NativeToolIdentity::new("trust_wp-vcgen").with_version("wp-v1"))
            .with_replay(
                ProofReplayIdentity::new("trust_wp", "trust_wp wp checked_add")
                    .with_transcript_digest(ProofDigest::sha256_domain(
                        "trust_wp.native.replay.v1",
                        b"trust_wp-wp",
                    )),
            ),
        }));
    bundle
}

fn source_generation_authority_bundle() -> NativeVerificationBundle {
    let mut bundle = native_bundle();
    remove_unreplayed_trust_vc_fixture(&mut bundle);
    bundle
}

#[test]
fn source_generation_authority_is_one_shot_instance_and_content_bound() {
    let mut bundle = source_generation_authority_bundle();
    bundle.validate().expect("authority fixture must be valid");

    let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle)
        .expect("the audited live producer seam should mint once");
    assert!(authority.authorizes_bundle(&bundle));

    let same_content_new_instance = bundle.clone();
    assert_eq!(same_content_new_instance, bundle);
    assert!(
        !authority.authorizes_bundle(&same_content_new_instance),
        "Clone must erase the private live-instance identity"
    );
    assert!(
        !authority.authorizes_bundle(&source_generation_authority_bundle()),
        "equal independently constructed content must not accept a transplanted authority"
    );

    assert!(
        matches!(
            SourceGenerationAuthority::mint_from_live_lowering(&mut bundle),
            Err(SourceGenerationAuthorityMintError::AlreadyMinted)
        ),
        "the issuer is one-shot for an exact live bundle"
    );

    bundle.provenance.source_artifact = Some("renamed_checked_add.rs".to_string());
    bundle
        .validate()
        .expect("the content mutation remains structurally valid");
    assert!(
        !authority.authorizes_bundle(&bundle),
        "post-mint canonical content mutation must invalidate authority"
    );
}

#[test]
fn source_generation_authority_invalid_mint_fails_without_poisoning_bundle() {
    let mut bundle = source_generation_authority_bundle();
    let requests = core::mem::take(&mut bundle.requests);
    let error = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle)
        .expect_err("invalid bundles cannot receive source authority");
    assert!(matches!(
        error,
        SourceGenerationAuthorityMintError::InvalidBundle(errors)
            if errors.contains(&NativeVerificationBundleError::EmptyRequests)
    ));

    bundle.requests = requests;
    let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle)
        .expect("a failed validation must not consume the one-shot issuer");
    assert!(authority.authorizes_bundle(&bundle));
}

#[test]
#[cfg(feature = "serde")]
fn source_generation_authority_does_not_survive_serde_round_trip() {
    let mut bundle = source_generation_authority_bundle();
    let authority = SourceGenerationAuthority::mint_from_live_lowering(&mut bundle)
        .expect("the audited live producer seam should mint");
    let encoded = serde_json::to_vec(&bundle).expect("serialize native bundle");
    let decoded: NativeVerificationBundle =
        serde_json::from_slice(&encoded).expect("deserialize native bundle");

    assert_eq!(decoded, bundle, "transient identity is not bundle content");
    decoded
        .validate()
        .expect("round-tripped content remains valid");
    assert!(
        !authority.authorizes_bundle(&decoded),
        "a retained token must not authorize a byte-round-tripped bundle instance"
    );
}

fn refresh_native_bundle_module_identity(bundle: &mut NativeVerificationBundle) {
    let digest = bundle.module.stable_digest();
    bundle.trust_ir_module_digest = digest;
    for node in &mut bundle.lineage.nodes {
        if bundle.lineage.roots.contains(&node.id) {
            node.target_module = digest;
        }
    }
    for evidence in &mut bundle.evidence_bundles {
        match evidence {
            NativeEvidenceBundle::TrustVc(evidence) => evidence.trust_ir_module_digest = digest,
            NativeEvidenceBundle::TrustMc(evidence) => evidence.trust_ir_module_digest = digest,
            NativeEvidenceBundle::TrustWp(evidence) => evidence.trust_ir_module_digest = digest,
        }
    }
}

/// Remove the deliberately unreplayable TrustVc request from the common test
/// fixture when a test is exercising an independent TrustMc/TrustWp or
/// compiler-fact surface.  The fixture's TrustVc certificate is opaque
/// `LeanProof` metadata, so the public validator must reject it now that
/// `Discharged` is not authority.  Keeping that request in unrelated tests
/// would make them stop at the authority boundary before reaching the surface
/// they intend to cover.
fn remove_unreplayed_trust_vc_fixture(bundle: &mut NativeVerificationBundle) {
    bundle
        .requests
        .retain(|request| request.id() != NativeRequestId::new(0));
    bundle
        .evidence_bundles
        .retain(|evidence| evidence.request() != NativeRequestId::new(0));
    refresh_native_bundle_module_identity(bundle);
}

fn assert_unreplayed_trust_vc_rejected(bundle: &NativeVerificationBundle) {
    let errors = bundle
        .validate()
        .expect_err("opaque TrustVc evidence must not authorize Discharged");
    assert!(
        errors.iter().any(|error| matches!(
            error,
            NativeVerificationBundleError::TrustVcCertificateNotDischarged {
                request: NativeRequestId(0),
                obligation: ProofId(0),
                prover,
                status: ProofStatus::Discharged,
            } if prover == "trust_vc"
        )),
        "missing fail-closed TrustVc authority diagnostic: {errors:?}"
    );
}

fn add_native_direct_enum_fact(bundle: &mut NativeVerificationBundle) {
    let enum_id = EnumId::new(bundle.module.enums.len() as u32);
    bundle.module.add_enum(crate::EnumDef {
        id: enum_id,
        name: "NativeDirect".to_string(),
        variants: vec![
            crate::EnumVariant {
                name: "A".to_string(),
                fields: vec![],
                field_names: Vec::new(),
            },
            crate::EnumVariant {
                name: "B".to_string(),
                fields: vec![],
                field_names: Vec::new(),
            },
        ],
        discriminants: Vec::new(),
        repr: None,
        layout: None,
    });
    bundle.compiler_facts.adt_layouts.push(NativeAdtLayoutFact {
        id: NativeCompilerFactId::new(20),
        ty: Ty::Enum(enum_id),
        layout: TyLayoutShape {
            size_bits: 32,
            align_bits: Some(32),
            kind: TyLayoutKind::Enum {
                id: enum_id,
                variants: 2,
            },
        },
        enum_layout: Some(NativeEnumLayoutFact {
            enum_id,
            tag_encoding: NativeEnumTagEncoding::Direct,
            tag_bits: Some(32),
            discriminant_offset_bits: Some(0),
            niche: None,
            variants: vec![
                NativeEnumVariantLayoutFact {
                    variant_index: 0,
                    name: "A".to_string(),
                    discriminant: Some(0),
                    fields: vec![],
                    size_bits: 0,
                    align_bits: None,
                },
                NativeEnumVariantLayoutFact {
                    variant_index: 1,
                    name: "B".to_string(),
                    discriminant: Some(1),
                    fields: vec![],
                    size_bits: 0,
                    align_bits: None,
                },
            ],
        }),
    });
}

fn add_native_niche_enum_fact(bundle: &mut NativeVerificationBundle) {
    let enum_id = EnumId::new(bundle.module.enums.len() as u32);
    let payload_ty = Ty::PtrConst(Box::new(Ty::U8));
    bundle.module.add_enum(crate::EnumDef {
        id: enum_id,
        name: "NativeOptionPtr".to_string(),
        variants: vec![
            crate::EnumVariant {
                name: "None".to_string(),
                fields: vec![],
                field_names: Vec::new(),
            },
            crate::EnumVariant {
                name: "Some".to_string(),
                fields: vec![payload_ty.clone()],
                field_names: Vec::new(),
            },
        ],
        discriminants: Vec::new(),
        repr: None,
        layout: None,
    });
    bundle.compiler_facts.adt_layouts.push(NativeAdtLayoutFact {
        id: NativeCompilerFactId::new(21),
        ty: Ty::Enum(enum_id),
        layout: TyLayoutShape {
            size_bits: 64,
            align_bits: Some(64),
            kind: TyLayoutKind::Enum {
                id: enum_id,
                variants: 2,
            },
        },
        enum_layout: Some(NativeEnumLayoutFact {
            enum_id,
            tag_encoding: NativeEnumTagEncoding::Niche,
            tag_bits: None,
            discriminant_offset_bits: None,
            niche: Some(NativeEnumNicheFact {
                variant_index: 1,
                field: Some(0),
                valid_range: NativeIntegerRange {
                    start: 1,
                    end: i128::MAX,
                },
            }),
            variants: vec![
                NativeEnumVariantLayoutFact {
                    variant_index: 0,
                    name: "None".to_string(),
                    discriminant: None,
                    fields: vec![],
                    size_bits: 0,
                    align_bits: None,
                },
                NativeEnumVariantLayoutFact {
                    variant_index: 1,
                    name: "Some".to_string(),
                    discriminant: None,
                    fields: vec![FieldOffsetShape {
                        field: 0,
                        name: "0".to_string(),
                        ty_shape: payload_ty.shape(),
                        offset_bits: Some(0),
                    }],
                    size_bits: 64,
                    align_bits: Some(64),
                },
            ],
        }),
    });
}

fn enum_layout_mut(bundle: &mut NativeVerificationBundle) -> &mut NativeEnumLayoutFact {
    bundle.compiler_facts.adt_layouts[0]
        .enum_layout
        .as_mut()
        .expect("enum layout fact")
}

fn assert_invalid_compiler_fact_field(
    bundle: NativeVerificationBundle,
    expected_field: &'static str,
) {
    let errors = bundle.validate().expect_err("invalid enum layout rejected");
    assert!(
        errors.iter().any(|err| matches!(
            err,
            NativeVerificationBundleError::InvalidCompilerFact { field, .. }
                if *field == expected_field
        )),
        "missing InvalidCompilerFact field {expected_field}: {errors:?}"
    );
}

#[test]
fn native_bundle_accepts_direct_tag_enum_layout_fact() {
    let mut bundle = native_bundle();
    add_native_direct_enum_fact(&mut bundle);
    remove_unreplayed_trust_vc_fixture(&mut bundle);
    refresh_native_bundle_module_identity(&mut bundle);

    bundle
        .validate()
        .expect("frontend-supplied direct enum layout evidence accepted");
}

#[test]
fn native_bundle_accepts_niche_enum_layout_fact() {
    let mut bundle = native_bundle();
    add_native_niche_enum_fact(&mut bundle);
    remove_unreplayed_trust_vc_fixture(&mut bundle);
    refresh_native_bundle_module_identity(&mut bundle);

    bundle
        .validate()
        .expect("frontend-supplied niche enum layout evidence accepted");
}

#[test]
fn native_bundle_rejects_invalid_enum_layout_facts() {
    let mut missing_direct_tag = native_bundle();
    add_native_direct_enum_fact(&mut missing_direct_tag);
    enum_layout_mut(&mut missing_direct_tag).tag_bits = None;
    assert_invalid_compiler_fact_field(missing_direct_tag, "enum_layout.tag_bits");

    let mut duplicate_discriminants = native_bundle();
    add_native_direct_enum_fact(&mut duplicate_discriminants);
    enum_layout_mut(&mut duplicate_discriminants).variants[1].discriminant = Some(0);
    assert_invalid_compiler_fact_field(duplicate_discriminants, "enum_layout.variant.discriminant");

    let mut missing_discriminant = native_bundle();
    add_native_direct_enum_fact(&mut missing_discriminant);
    enum_layout_mut(&mut missing_discriminant).variants[1].discriminant = None;
    assert_invalid_compiler_fact_field(missing_discriminant, "enum_layout.variant.discriminant");

    let mut missing_niche = native_bundle();
    add_native_niche_enum_fact(&mut missing_niche);
    enum_layout_mut(&mut missing_niche).niche = None;
    assert_invalid_compiler_fact_field(missing_niche, "enum_layout.niche");

    let mut empty_niche_range = native_bundle();
    add_native_niche_enum_fact(&mut empty_niche_range);
    enum_layout_mut(&mut empty_niche_range)
        .niche
        .as_mut()
        .expect("niche")
        .valid_range = NativeIntegerRange { start: 2, end: 1 };
    assert_invalid_compiler_fact_field(empty_niche_range, "enum_layout.niche.valid_range");

    let mut missing_niche_variant = native_bundle();
    add_native_niche_enum_fact(&mut missing_niche_variant);
    enum_layout_mut(&mut missing_niche_variant)
        .niche
        .as_mut()
        .expect("niche")
        .variant_index = 99;
    assert_invalid_compiler_fact_field(missing_niche_variant, "enum_layout.niche.variant_index");

    let mut missing_niche_field = native_bundle();
    add_native_niche_enum_fact(&mut missing_niche_field);
    enum_layout_mut(&mut missing_niche_field)
        .niche
        .as_mut()
        .expect("niche")
        .field = Some(1);
    assert_invalid_compiler_fact_field(missing_niche_field, "enum_layout.niche.field");

    let mut untagged_with_tag = native_bundle();
    add_native_direct_enum_fact(&mut untagged_with_tag);
    let untagged_layout = enum_layout_mut(&mut untagged_with_tag);
    untagged_layout.tag_encoding = NativeEnumTagEncoding::Untagged;
    untagged_layout.niche = Some(NativeEnumNicheFact {
        variant_index: 0,
        field: None,
        valid_range: NativeIntegerRange { start: 0, end: 0 },
    });
    assert_invalid_compiler_fact_field(untagged_with_tag, "enum_layout.tag_bits");

    let mut field_shape_mismatch = native_bundle();
    add_native_niche_enum_fact(&mut field_shape_mismatch);
    enum_layout_mut(&mut field_shape_mismatch).variants[1].fields[0].ty_shape = TyShape::Bool;
    assert_invalid_compiler_fact_field(field_shape_mismatch, "enum_layout.variant.fields.ty_shape");

    let mut variant_too_large = native_bundle();
    add_native_niche_enum_fact(&mut variant_too_large);
    enum_layout_mut(&mut variant_too_large).variants[1].size_bits = 128;
    assert_invalid_compiler_fact_field(variant_too_large, "layout.size_bits");

    let mut variant_overaligned = native_bundle();
    add_native_niche_enum_fact(&mut variant_overaligned);
    enum_layout_mut(&mut variant_overaligned).variants[1].align_bits = Some(128);
    assert_invalid_compiler_fact_field(variant_overaligned, "layout.align_bits");
}

fn native_evidence_bundles(bundle: &NativeVerificationBundle) -> Vec<NativeEvidenceBundle> {
    vec![
        bundle
            .evidence_bundle_for_request(
                &bundle.requests[0],
                vec![NativeEvidenceArtifact::new(
                    "trust_vc-import.lean",
                    NativeEvidenceArtifactKind::TrustVcCertificateImport,
                    digest(0xC0),
                )],
            )
            .expect("TrustVc evidence"),
        bundle
            .evidence_bundle_for_request(
                &bundle.requests[1],
                vec![NativeEvidenceArtifact::new(
                    "trust_mc-chc.smt2",
                    NativeEvidenceArtifactKind::TrustMcHornClauses,
                    digest(0xC1),
                )],
            )
            .expect("TrustMc evidence"),
        bundle
            .evidence_bundle_for_request(
                &bundle.requests[2],
                vec![NativeEvidenceArtifact::new(
                    "trust_wp-wp.vc",
                    NativeEvidenceArtifactKind::TrustWpVerificationCondition,
                    digest(0xC2),
                )],
            )
            .expect("TrustWp evidence"),
    ]
}

fn petri_successor_trust_mc_bundle_with_artifacts(
    horn_bytes: &[u8],
    replay_bytes: &[u8],
    model_bytes: &[u8],
) -> (NativeVerificationBundle, Vec<NativeEvidenceArtifact>) {
    let mut bundle = native_bundle();
    bundle.module.proof_obligations[1].status = ProofStatus::Discharged;

    let replay_digest = NativeEvidenceArtifactAttachment::digest_for_bytes(
        ProofDigestAlgorithm::Sha256,
        replay_bytes,
    );
    if let NativeVerificationRequest::TrustMc(request) = &mut bundle.requests[1] {
        request.provenance.replay = Some(
            ProofReplayIdentity::new("trust_mc", "trust_mc --chc checked_add")
                .with_transcript_digest(replay_digest),
        );
    } else {
        panic!("TrustMc request");
    }

    let artifacts = vec![
        NativeEvidenceArtifact::new(
            "trust_mc-chc.smt2",
            NativeEvidenceArtifactKind::TrustMcHornClauses,
            NativeEvidenceArtifactAttachment::digest_for_bytes(
                ProofDigestAlgorithm::Sha256,
                horn_bytes,
            ),
        ),
        NativeEvidenceArtifact::new(
            "trust_mc-replay.json",
            NativeEvidenceArtifactKind::ReplayTranscript,
            replay_digest,
        ),
        NativeEvidenceArtifact::new(
            "trust_mc-model.json",
            NativeEvidenceArtifactKind::TrustMcModel,
            NativeEvidenceArtifactAttachment::digest_for_bytes(
                ProofDigestAlgorithm::Sha256,
                model_bytes,
            ),
        ),
    ];
    bundle.evidence_bundles = vec![
        bundle
            .evidence_bundle_for_request(&bundle.requests[1], artifacts.clone())
            .expect("TrustMc evidence"),
    ];
    remove_unreplayed_trust_vc_fixture(&mut bundle);

    (bundle, artifacts)
}

fn petri_successor_trust_mc_artifact_attachments(
    artifacts: &[NativeEvidenceArtifact],
    horn_bytes: &[u8],
    replay_bytes: &[u8],
    model_bytes: &[u8],
) -> Vec<NativeEvidenceArtifactAttachment> {
    vec![
        NativeEvidenceArtifactAttachment::for_artifact(
            NativeRequestId::new(1),
            NativeVerifierSuite::TrustMc,
            &artifacts[0],
            "memory:trust_mc-horn-clauses",
            horn_bytes.to_vec(),
        ),
        NativeEvidenceArtifactAttachment::for_artifact(
            NativeRequestId::new(1),
            NativeVerifierSuite::TrustMc,
            &artifacts[1],
            "memory:trust_mc-replay",
            replay_bytes.to_vec(),
        ),
        NativeEvidenceArtifactAttachment::for_artifact(
            NativeRequestId::new(1),
            NativeVerifierSuite::TrustMc,
            &artifacts[2],
            "memory:trust_mc-model",
            model_bytes.to_vec(),
        ),
    ]
}

#[test]
fn native_bundle_rejects_unreplayed_typed_trust_vc_request() {
    assert_unreplayed_trust_vc_rejected(&native_bundle());
}

#[test]
fn native_bundle_rejects_invalid_or_aliased_public_obligation_ids() {
    let mut aliased = native_bundle();
    let first_public_id = aliased.compiler_facts.obligation_sources[0]
        .public_obligation_id
        .clone();
    aliased.compiler_facts.obligation_sources[1].public_obligation_id = first_public_id.clone();
    let errors = aliased
        .validate()
        .expect_err("one public proof unit must not alias two native obligations");
    assert!(errors.iter().any(|error| matches!(
        error,
        NativeVerificationBundleError::DuplicatePublicObligationSource {
            public_obligation_id,
            first_obligation: ProofId(0),
            duplicate_obligation: ProofId(1),
        } if public_obligation_id == &first_public_id
    )));

    for invalid in [
        String::new(),
        " leading".to_string(),
        "internal space".to_string(),
        "line\nbreak".to_string(),
        "non-ascii-é".to_string(),
        "query?component".to_string(),
        "fragment#component".to_string(),
        "x".repeat(NATIVE_PUBLIC_OBLIGATION_ID_MAX_BYTES + 1),
    ] {
        let mut bundle = native_bundle();
        bundle.compiler_facts.obligation_sources[0].public_obligation_id = invalid;
        let errors = bundle
            .validate()
            .expect_err("non-canonical public obligation identity must fail closed");
        assert!(errors.iter().any(|error| matches!(
            error,
            NativeVerificationBundleError::InvalidPublicObligationId {
                obligation: ProofId(0)
            }
        )));
    }
}

#[test]
#[cfg(feature = "serde")]
fn native_obligation_source_serde_requires_public_obligation_id() {
    let bundle = native_bundle();
    let mut value = serde_json::to_value(&bundle).expect("native bundle serializes");
    value["compiler_facts"]["obligation_sources"][0]
        .as_object_mut()
        .expect("obligation source object")
        .remove("public_obligation_id");

    let error = serde_json::from_value::<NativeVerificationBundle>(value)
        .expect_err("schema-v5 source identity must not receive a compatibility default");
    assert!(error.to_string().contains("public_obligation_id"));
}

#[test]
fn native_bundle_validates_typed_result_evidence_bundles() {
    let mut bundle = native_bundle();
    bundle.evidence_bundles = native_evidence_bundles(&bundle);
    assert_unreplayed_trust_vc_rejected(&bundle);
    remove_unreplayed_trust_vc_fixture(&mut bundle);

    bundle
        .validate()
        .expect("remaining typed TrustMc/TrustWp evidence bundles validate");
}

#[test]
fn native_evidence_bundle_helper_binds_request_identity() {
    let bundle = native_bundle();
    let evidence = bundle
        .evidence_bundle_for_request(
            &bundle.requests[1],
            vec![NativeEvidenceArtifact::new(
                "trust_mc-chc.smt2",
                NativeEvidenceArtifactKind::TrustMcHornClauses,
                digest(0xC1),
            )],
        )
        .expect("TrustMc evidence");

    let NativeVerificationRequest::TrustMc(request) = &bundle.requests[1] else {
        panic!("TrustMc request")
    };
    let NativeEvidenceBundle::TrustMc(trust_mc_evidence) = &evidence else {
        panic!("TrustMc evidence")
    };

    assert_eq!(trust_mc_evidence.request, request.id);
    assert_eq!(trust_mc_evidence.mode, request.mode);
    assert_eq!(trust_mc_evidence.obligations, request.obligations);
    assert_eq!(
        trust_mc_evidence.verifier,
        request.provenance.expected_verifier
    );
    assert_eq!(trust_mc_evidence.solvers, request.provenance.solvers);
    assert_eq!(
        Some(&trust_mc_evidence.replay),
        request.provenance.replay.as_ref()
    );
    assert_eq!(
        trust_mc_evidence.trust_ir_module_digest,
        bundle.trust_ir_module_digest
    );
    assert_eq!(
        trust_mc_evidence.request_digest,
        bundle.requests[1].stable_digest()
    );
    assert_eq!(
        trust_mc_evidence.artifacts[0].kind,
        NativeEvidenceArtifactKind::TrustMcHornClauses
    );

    let mut with_evidence = bundle.clone();
    with_evidence.evidence_bundles = vec![evidence];
    remove_unreplayed_trust_vc_fixture(&mut with_evidence);
    let report = with_evidence
        .native_evidence_consumption_report()
        .expect("helper evidence validates");
    assert_eq!(report.entries.len(), 1);
    assert_eq!(report.entries[0].request, request.id);
    assert_eq!(report.entries[0].suite, NativeVerifierSuite::TrustMc);
}

#[test]
fn native_evidence_artifact_attachment_resolves_trust_mc_chc_bytes_by_identity() {
    let mut bundle = native_bundle();
    let request = NativeRequestId::new(1);
    let artifacts_and_bytes = [
        (
            "trust_mc-chc.smt2",
            NativeEvidenceArtifactKind::TrustMcHornClauses,
            "memory:trust_mc-horn-clauses",
            b"(set-logic HORN)\n(assert true)\n".as_slice(),
        ),
        (
            "trust_mc-replay.json",
            NativeEvidenceArtifactKind::ReplayTranscript,
            "memory:trust_mc-replay",
            br#"{"engine":"trust_mc","status":"unsafe"}"#.as_slice(),
        ),
        (
            "trust_mc-model.json",
            NativeEvidenceArtifactKind::TrustMcModel,
            "memory:trust_mc-model",
            br##"{"x":"#x01"}"##.as_slice(),
        ),
        (
            "btor2-trace.json",
            NativeEvidenceArtifactKind::Btor2Trace,
            "memory:btor2-trace",
            br#"{"bad_state":3}"#.as_slice(),
        ),
        (
            "btor2-proof.lfsc",
            NativeEvidenceArtifactKind::Btor2Proof,
            "memory:btor2-proof",
            b"(check-proof btor2)\n".as_slice(),
        ),
        (
            "successor-native.dylib",
            NativeEvidenceArtifactKind::NativeCompiledArtifact,
            "memory:native-compiled-artifact",
            b"\x7fMACHO-native-successor".as_slice(),
        ),
        (
            "backend-capability.jsonl",
            NativeEvidenceArtifactKind::BackendCapabilityMetadata,
            "memory:backend-capability",
            br#"{"backend":"petri","status":"ready"}"#.as_slice(),
        ),
    ];
    assert_eq!(NativeEvidenceArtifactKind::Btor2Trace.code(), "btor2_trace");
    assert_eq!(NativeEvidenceArtifactKind::Btor2Proof.code(), "btor2_proof");
    assert_eq!(
        NativeEvidenceArtifactKind::NativeCompiledArtifact.code(),
        "native_compiled_artifact"
    );
    assert_eq!(
        NativeEvidenceArtifactKind::BackendCapabilityMetadata.code(),
        "backend_capability_metadata"
    );
    let artifacts: Vec<_> = artifacts_and_bytes
        .iter()
        .map(|(name, kind, _, bytes)| {
            NativeEvidenceArtifact::new(
                *name,
                *kind,
                NativeEvidenceArtifactAttachment::digest_for_bytes(
                    ProofDigestAlgorithm::Sha256,
                    bytes,
                ),
            )
        })
        .collect();
    let attachments: Vec<_> = artifacts
        .iter()
        .zip(artifacts_and_bytes.iter())
        .map(|(artifact, (_, _, source, bytes))| {
            NativeEvidenceArtifactAttachment::for_artifact(
                request,
                NativeVerifierSuite::TrustMc,
                artifact,
                *source,
                bytes.to_vec(),
            )
        })
        .collect();
    bundle.evidence_bundles = vec![
        bundle
            .evidence_bundle_for_request(&bundle.requests[1], artifacts.clone())
            .expect("TrustMc evidence"),
    ];
    remove_unreplayed_trust_vc_fixture(&mut bundle);
    bundle.validate().expect("bundle validates");

    assert_eq!(
        NativeEvidenceArtifactAttachment::digest_for_bytes(ProofDigestAlgorithm::Sha256, b"abc"),
        ProofDigest::sha256([
            0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea, 0x41, 0x41, 0x40, 0xde, 0x5d, 0xae,
            0x22, 0x23, 0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c, 0xb4, 0x10, 0xff, 0x61,
            0xf2, 0x00, 0x15, 0xad,
        ])
    );

    for (artifact, (_, kind, source, bytes)) in artifacts.iter().zip(artifacts_and_bytes) {
        let key = NativeEvidenceArtifactAttachmentKey::for_artifact(request, artifact);
        assert_eq!(key.kind, kind);
        assert_eq!(key.digest_algorithm, ProofDigestAlgorithm::Sha256);

        let resolution = bundle.resolve_evidence_artifact_attachment(key, &attachments);

        assert!(resolution.is_resolved());
        assert_eq!(resolution.bytes, Some(bytes));
        assert_eq!(
            resolution.report.schema,
            NATIVE_EVIDENCE_ARTIFACT_RESOLUTION_SCHEMA
        );
        assert_eq!(
            resolution.report.schema_version,
            NATIVE_EVIDENCE_ARTIFACT_RESOLUTION_SCHEMA_VERSION
        );
        assert_eq!(resolution.report.status_code(), "resolved");
        assert_eq!(resolution.report.reason_code(), "resolved");
        assert_eq!(resolution.report.authority_code(), "authoritative");
        assert_eq!(
            resolution.report.authority,
            NativeEvidenceArtifactAuthority::Authoritative
        );
        assert_eq!(resolution.report.request, request);
        assert_eq!(
            resolution.report.owner_suite,
            Some(NativeVerifierSuite::TrustMc)
        );
        assert_eq!(resolution.report.required_kind, kind);
        assert_eq!(
            resolution.report.byte_source_identity.as_deref(),
            Some(source)
        );
        assert_eq!(resolution.report.byte_len, Some(bytes.len()));
        assert_eq!(resolution.report.digest, artifact.digest);
        assert_eq!(resolution.report.actual_digest, Some(artifact.digest));
    }
}

#[test]
fn native_evidence_artifact_authority_examples_cover_btor2_native_and_metadata() {
    let mut bundle = native_bundle();
    let request = NativeRequestId::new(1);
    let artifact_cases = [
        (
            "btor2-trace.json",
            NativeEvidenceArtifactKind::Btor2Trace,
            "sidecar:btor2-trace",
            br#"{"step":0,"state":"unsafe"}"#.as_slice(),
        ),
        (
            "btor2-proof.lfsc",
            NativeEvidenceArtifactKind::Btor2Proof,
            "sidecar:btor2-proof",
            b"(btor2-proof accepted)\n".as_slice(),
        ),
        (
            "petri-successor-native.dylib",
            NativeEvidenceArtifactKind::NativeCompiledArtifact,
            "sidecar:native-compiled-artifact",
            b"\x7fMACHO-petri-successor-native".as_slice(),
        ),
        (
            "petri.backend-capability.jsonl",
            NativeEvidenceArtifactKind::BackendCapabilityMetadata,
            "sidecar:backend-capability",
            br#"{"artifact":"backend-capability","status":"ready"}"#.as_slice(),
        ),
    ];
    let artifacts: Vec<_> = artifact_cases
        .iter()
        .map(|(name, kind, _, bytes)| {
            NativeEvidenceArtifact::new(
                *name,
                *kind,
                NativeEvidenceArtifactAttachment::digest_for_bytes(
                    ProofDigestAlgorithm::Sha256,
                    bytes,
                ),
            )
        })
        .collect();
    let attachments: Vec<_> = artifacts
        .iter()
        .zip(artifact_cases.iter())
        .map(|(artifact, (_, _, source, bytes))| {
            NativeEvidenceArtifactAttachment::for_artifact(
                request,
                NativeVerifierSuite::TrustMc,
                artifact,
                *source,
                bytes.to_vec(),
            )
        })
        .collect();
    bundle.evidence_bundles = vec![
        bundle
            .evidence_bundle_for_request(&bundle.requests[1], artifacts.clone())
            .expect("TrustMc evidence"),
    ];
    remove_unreplayed_trust_vc_fixture(&mut bundle);
    bundle.validate().expect("bundle validates");

    for (artifact, (_, expected_kind, source, expected_bytes)) in
        artifacts.iter().zip(artifact_cases)
    {
        let key = NativeEvidenceArtifactAttachmentKey::for_artifact(request, artifact);

        let authoritative = bundle.resolve_evidence_artifact_attachment(key, &attachments);

        assert!(authoritative.is_resolved());
        assert!(authoritative.is_authoritative());
        assert_eq!(authoritative.authoritative_bytes(), Some(expected_bytes));
        assert_eq!(authoritative.report.required_kind, expected_kind);
        assert_eq!(authoritative.report.authority_code(), "authoritative");
        assert_eq!(authoritative.report.status_code(), "resolved");
        assert_eq!(authoritative.report.reason_code(), "resolved");
        assert_eq!(
            authoritative.report.byte_source_identity.as_deref(),
            Some(source)
        );

        let missing = bundle.resolve_evidence_artifact_attachment(key, &[]);
        assert!(!missing.is_resolved());
        assert!(!missing.is_authoritative());
        assert_eq!(missing.authoritative_bytes(), None);
        assert!(missing.report.fail_closed());
        assert_eq!(missing.report.authority_code(), "informational");
        assert_eq!(missing.report.reason_code(), "missing_attachment");

        let stale_attachment = NativeEvidenceArtifactAttachment::for_artifact(
            request,
            NativeVerifierSuite::TrustMc,
            artifact,
            source,
            b"stale sidecar bytes".to_vec(),
        );
        let stale_attachments = [stale_attachment];
        let stale = bundle.resolve_evidence_artifact_attachment(key, &stale_attachments);
        assert!(!stale.is_authoritative());
        assert_eq!(stale.authoritative_bytes(), None);
        assert!(stale.report.fail_closed());
        assert_eq!(stale.report.authority_code(), "informational");
        assert_eq!(stale.report.reason_code(), "digest_mismatch");
        assert_ne!(stale.report.actual_digest, Some(artifact.digest));
    }
}

#[test]
fn native_evidence_artifact_authority_rows_are_downstream_ready() {
    let mut bundle = native_bundle();
    let request = NativeRequestId::new(1);
    let artifact_cases = [
        (
            "btor2-trace.json",
            NativeEvidenceArtifactKind::Btor2Trace,
            "sidecar:btor2-trace",
            br#"{"trace":"unsafe"}"#.as_slice(),
        ),
        (
            "btor2-proof.lfsc",
            NativeEvidenceArtifactKind::Btor2Proof,
            "sidecar:btor2-proof",
            b"(btor2-proof authoritative)\n".as_slice(),
        ),
        (
            "petri-successor-native.dylib",
            NativeEvidenceArtifactKind::NativeCompiledArtifact,
            "sidecar:native-compiled-artifact",
            b"\x7fMACHO-petri-successor-native".as_slice(),
        ),
        (
            "petri.backend-capability.jsonl",
            NativeEvidenceArtifactKind::BackendCapabilityMetadata,
            "sidecar:backend=capability\nmetadata",
            br#"{"backend":"petri","authority":"ready"}"#.as_slice(),
        ),
    ];
    let artifacts: Vec<_> = artifact_cases
        .iter()
        .map(|(name, kind, _, bytes)| {
            NativeEvidenceArtifact::new(
                *name,
                *kind,
                NativeEvidenceArtifactAttachment::digest_for_bytes(
                    ProofDigestAlgorithm::Sha256,
                    bytes,
                ),
            )
        })
        .collect();
    let attachments: Vec<_> = artifacts
        .iter()
        .zip(artifact_cases.iter())
        .map(|(artifact, (_, _, source, bytes))| {
            NativeEvidenceArtifactAttachment::for_artifact(
                request,
                NativeVerifierSuite::TrustMc,
                artifact,
                *source,
                bytes.to_vec(),
            )
        })
        .collect();
    bundle.evidence_bundles = vec![
        bundle
            .evidence_bundle_for_request(&bundle.requests[1], artifacts.clone())
            .expect("TrustMc evidence"),
    ];
    remove_unreplayed_trust_vc_fixture(&mut bundle);
    bundle.validate().expect("bundle validates");

    for (artifact, (name, expected_kind, source, expected_bytes)) in
        artifacts.iter().zip(artifact_cases)
    {
        let key = NativeEvidenceArtifactAttachmentKey::for_artifact(request, artifact);
        let resolution = bundle.resolve_evidence_artifact_attachment(key, &attachments);
        let rows = resolution.authority_evidence_rows();
        let rows_by_key: BTreeMap<_, _> = rows
            .iter()
            .map(|row| (row.key.as_str(), row.value.as_str()))
            .collect();

        assert_eq!(
            rows[0].to_key_value_line(),
            format!(
                "artifact_authority.schema={}",
                NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_ROW_SCHEMA
            )
        );
        assert_eq!(
            rows_by_key["artifact_authority.schema_version"],
            NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_ROW_SCHEMA_VERSION.to_string()
        );
        assert_eq!(
            rows_by_key["artifact_resolution.schema"],
            NATIVE_EVIDENCE_ARTIFACT_RESOLUTION_SCHEMA
        );
        assert_eq!(
            rows_by_key["artifact_resolution.schema_version"],
            NATIVE_EVIDENCE_ARTIFACT_RESOLUTION_SCHEMA_VERSION.to_string()
        );
        assert_eq!(rows_by_key["request.id"], request.to_string());
        assert_eq!(
            rows_by_key["owner_suite"],
            NativeVerifierSuite::TrustMc.code()
        );
        assert_eq!(rows_by_key["artifact.kind"], expected_kind.code());
        assert_eq!(rows_by_key["artifact.name"], name);
        assert_eq!(rows_by_key["digest.algorithm"], "sha256");
        assert_eq!(rows_by_key["digest"], artifact.digest.to_string());
        assert_eq!(rows_by_key["byte.source_identity"], source);
        assert_eq!(rows_by_key["byte.len"], expected_bytes.len().to_string());
        assert_eq!(rows_by_key["actual_digest"], artifact.digest.to_string());
        assert_eq!(rows_by_key["authority"], "authoritative");
        assert_eq!(rows_by_key["status"], "resolved");
        assert_eq!(rows_by_key["reason"], "resolved");
        assert_eq!(rows_by_key["report.is_authoritative"], "true");
        assert_eq!(rows_by_key["report.fail_closed"], "false");
        assert_eq!(rows_by_key["resolution.bytes_present"], "true");
        assert_eq!(rows_by_key["resolution.is_authoritative"], "true");
        assert_eq!(rows_by_key["resolution.fail_closed"], "false");
        assert_eq!(
            rows_by_key["resolution.authoritative_bytes_available"],
            "true"
        );

        let lines = resolution.authority_evidence_key_value_lines();
        assert_eq!(lines.len(), rows.len());
        assert!(lines.iter().all(|line| !line.contains('\n')));
        assert!(lines.iter().all(|line| !line.contains('\t')));
        assert!(
            lines
                .iter()
                .any(|line| { line == &format!("artifact.kind={}", expected_kind.code()) })
        );
        if expected_kind == NativeEvidenceArtifactKind::BackendCapabilityMetadata {
            assert!(lines.iter().any(|line| {
                line == "byte.source_identity=sidecar:backend\\=capability\\nmetadata"
            }));
        }

        let missing = bundle.resolve_evidence_artifact_attachment(key, &[]);
        let missing_rows = missing.authority_evidence_rows();
        let missing_by_key: BTreeMap<_, _> = missing_rows
            .iter()
            .map(|row| (row.key.as_str(), row.value.as_str()))
            .collect();
        assert_eq!(missing_by_key["artifact.kind"], expected_kind.code());
        assert_eq!(missing_by_key["artifact.name"], name);
        assert_eq!(missing_by_key["authority"], "informational");
        assert_eq!(missing_by_key["status"], "blocked");
        assert_eq!(missing_by_key["reason"], "missing_attachment");
        assert_eq!(missing_by_key["report.fail_closed"], "true");
        assert_eq!(missing_by_key["resolution.bytes_present"], "false");
        assert_eq!(missing_by_key["resolution.is_authoritative"], "false");
        assert_eq!(missing_by_key["resolution.fail_closed"], "true");
        assert_eq!(
            missing_by_key["resolution.authoritative_bytes_available"],
            "false"
        );
    }
}

#[test]
fn native_evidence_artifact_authority_row_descriptor_matches_emitted_rows() {
    let descriptor = native_evidence_artifact_authority_row_descriptor();

    assert_eq!(
        descriptor,
        NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_ROW_DESCRIPTOR
    );
    assert_eq!(
        descriptor.schema,
        NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_ROW_SCHEMA
    );
    assert_eq!(
        descriptor.schema_version,
        NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_ROW_SCHEMA_VERSION
    );
    assert_eq!(
        descriptor.report_row_keys,
        NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_REPORT_ROW_KEYS
    );
    assert_eq!(
        descriptor.resolution_row_keys,
        NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_RESOLUTION_ROW_KEYS
    );
    assert_eq!(
        descriptor.report_row_keys.len(),
        19,
        "report row vocabulary count is schema-versioned"
    );
    assert_eq!(
        descriptor.resolution_row_keys.len(),
        24,
        "resolution row vocabulary count is schema-versioned"
    );
    assert_eq!(
        &descriptor.resolution_row_keys[..descriptor.report_row_keys.len()],
        descriptor.report_row_keys
    );
    let report_keys: BTreeSet<_> = descriptor.report_row_keys.iter().copied().collect();
    assert_eq!(report_keys.len(), descriptor.report_row_keys.len());
    let resolution_keys: BTreeSet<_> = descriptor.resolution_row_keys.iter().copied().collect();
    assert_eq!(resolution_keys.len(), descriptor.resolution_row_keys.len());

    let mut bundle = native_bundle();
    let request = NativeRequestId::new(1);
    let bytes = br#"{"backend":"petri","authority":"ready"}"#;
    let artifact = NativeEvidenceArtifact::new(
        "petri.backend-capability.jsonl",
        NativeEvidenceArtifactKind::BackendCapabilityMetadata,
        NativeEvidenceArtifactAttachment::digest_for_bytes(ProofDigestAlgorithm::Sha256, bytes),
    );
    let attachment = NativeEvidenceArtifactAttachment::for_artifact(
        request,
        NativeVerifierSuite::TrustMc,
        &artifact,
        "sidecar:backend-capability",
        bytes.to_vec(),
    );
    bundle.evidence_bundles = vec![
        bundle
            .evidence_bundle_for_request(&bundle.requests[1], vec![artifact.clone()])
            .expect("TrustMc evidence"),
    ];
    remove_unreplayed_trust_vc_fixture(&mut bundle);
    bundle.validate().expect("bundle validates");

    let key = NativeEvidenceArtifactAttachmentKey::for_artifact(request, &artifact);
    let attachments = [attachment];
    let resolution = bundle.resolve_evidence_artifact_attachment(key, &attachments);
    let report_rows = resolution.report.authority_evidence_rows();
    let resolution_rows = resolution.authority_evidence_rows();

    assert!(descriptor.report_row_keys_match(&report_rows));
    assert!(descriptor.resolution_row_keys_match(&resolution_rows));
    let mut reordered_rows = resolution_rows.clone();
    reordered_rows.swap(0, 1);
    assert!(!descriptor.resolution_row_keys_match(&reordered_rows));
    let mut truncated_rows = resolution_rows.clone();
    truncated_rows.pop();
    assert!(!descriptor.resolution_row_keys_match(&truncated_rows));

    let manifest_lines = descriptor.manifest_key_value_lines();
    assert_eq!(
        manifest_lines[0],
        format!(
            "authority_row_descriptor.schema={}",
            NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_ROW_SCHEMA
        )
    );
    assert_eq!(
        manifest_lines[1],
        format!(
            "authority_row_descriptor.schema_version={}",
            NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_ROW_SCHEMA_VERSION
        )
    );
    assert_eq!(
        manifest_lines[2],
        format!(
            "authority_row_descriptor.report_key_count={}",
            descriptor.report_row_keys.len()
        )
    );
    assert_eq!(
        manifest_lines[3],
        format!(
            "authority_row_descriptor.resolution_key_count={}",
            descriptor.resolution_row_keys.len()
        )
    );
    assert_eq!(
        manifest_lines.len(),
        4 + descriptor.report_row_keys.len() + descriptor.resolution_row_keys.len()
    );
    assert_eq!(
        manifest_lines[4],
        "authority_row_descriptor.report_key.0=artifact_authority.schema"
    );
    assert_eq!(
        manifest_lines.last().map(String::as_str),
        Some("authority_row_descriptor.resolution_key.23=resolution.authoritative_bytes_available")
    );
}

#[test]
fn native_evidence_artifact_authority_key_value_lines_validate_mixed_resolutions() {
    fn assert_lines_match_descriptor(
        descriptor: NativeEvidenceArtifactAuthorityRowDescriptor,
        lines: &[String],
    ) {
        assert_eq!(lines.len(), descriptor.resolution_row_keys.len());
        for (line, key) in lines.iter().zip(descriptor.resolution_row_keys.iter()) {
            let prefix = format!("{key}=");
            assert!(
                line.starts_with(&prefix),
                "authority line `{line}` did not match descriptor key `{key}`"
            );
        }
    }

    fn line_value<'a>(lines: &'a [String], key: &str) -> &'a str {
        let prefix = format!("{key}=");
        lines
            .iter()
            .find_map(|line| line.strip_prefix(&prefix))
            .unwrap_or_else(|| panic!("missing authority line for key `{key}`"))
    }

    let descriptor = native_evidence_artifact_authority_row_descriptor();
    let mut bundle = native_bundle();
    let request = NativeRequestId::new(1);
    let trace_bytes = br#"{"trace":"accepted"}"#.as_slice();
    let native_bytes = b"\x7fMACHO-petri-successor-native".as_slice();
    let metadata_bytes = br#"{"backend":"petri","status":"ready"}"#.as_slice();
    let artifact_cases = [
        (
            "btor2-trace.json",
            NativeEvidenceArtifactKind::Btor2Trace,
            trace_bytes,
        ),
        (
            "petri-successor-native.dylib",
            NativeEvidenceArtifactKind::NativeCompiledArtifact,
            native_bytes,
        ),
        (
            "petri.backend-capability.jsonl",
            NativeEvidenceArtifactKind::BackendCapabilityMetadata,
            metadata_bytes,
        ),
    ];
    let artifacts: Vec<_> = artifact_cases
        .iter()
        .map(|(name, kind, bytes)| {
            NativeEvidenceArtifact::new(
                *name,
                *kind,
                NativeEvidenceArtifactAttachment::digest_for_bytes(
                    ProofDigestAlgorithm::Sha256,
                    bytes,
                ),
            )
        })
        .collect();
    bundle.evidence_bundles = vec![
        bundle
            .evidence_bundle_for_request(&bundle.requests[1], artifacts.clone())
            .expect("TrustMc evidence"),
    ];
    remove_unreplayed_trust_vc_fixture(&mut bundle);
    bundle.validate().expect("bundle validates");

    let authoritative_trace = NativeEvidenceArtifactAttachment::for_artifact(
        request,
        NativeVerifierSuite::TrustMc,
        &artifacts[0],
        "sidecar:btor2-trace",
        trace_bytes.to_vec(),
    );
    let stale_metadata = NativeEvidenceArtifactAttachment::for_artifact(
        request,
        NativeVerifierSuite::TrustMc,
        &artifacts[2],
        "sidecar:backend-capability",
        b"stale backend capability bytes".to_vec(),
    );
    let mixed_attachments = [authoritative_trace, stale_metadata];

    let trace_resolution = bundle.resolve_evidence_artifact_attachment(
        NativeEvidenceArtifactAttachmentKey::for_artifact(request, &artifacts[0]),
        &mixed_attachments,
    );
    let native_resolution = bundle.resolve_evidence_artifact_attachment(
        NativeEvidenceArtifactAttachmentKey::for_artifact(request, &artifacts[1]),
        &mixed_attachments,
    );
    let metadata_resolution = bundle.resolve_evidence_artifact_attachment(
        NativeEvidenceArtifactAttachmentKey::for_artifact(request, &artifacts[2]),
        &mixed_attachments,
    );

    let trace_lines = trace_resolution.authority_evidence_key_value_lines();
    let native_lines = native_resolution.authority_evidence_key_value_lines();
    let metadata_lines = metadata_resolution.authority_evidence_key_value_lines();

    for lines in [&trace_lines, &native_lines, &metadata_lines] {
        assert_lines_match_descriptor(descriptor, lines);
        assert_eq!(
            line_value(lines, "artifact_authority.schema"),
            NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_ROW_SCHEMA
        );
        assert_eq!(
            line_value(lines, "artifact_authority.schema_version"),
            NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_ROW_SCHEMA_VERSION.to_string()
        );
    }

    assert_eq!(line_value(&trace_lines, "artifact.kind"), "btor2_trace");
    assert_eq!(line_value(&trace_lines, "authority"), "authoritative");
    assert_eq!(line_value(&trace_lines, "status"), "resolved");
    assert_eq!(line_value(&trace_lines, "reason"), "resolved");
    assert_eq!(line_value(&trace_lines, "resolution.bytes_present"), "true");
    assert_eq!(
        line_value(&trace_lines, "resolution.is_authoritative"),
        "true"
    );
    assert_eq!(line_value(&trace_lines, "resolution.fail_closed"), "false");
    assert_eq!(
        line_value(&trace_lines, "resolution.authoritative_bytes_available"),
        "true"
    );

    assert_eq!(
        line_value(&native_lines, "artifact.kind"),
        "native_compiled_artifact"
    );
    assert_eq!(line_value(&native_lines, "authority"), "informational");
    assert_eq!(line_value(&native_lines, "status"), "blocked");
    assert_eq!(line_value(&native_lines, "reason"), "missing_attachment");
    assert_eq!(
        line_value(&native_lines, "resolution.bytes_present"),
        "false"
    );
    assert_eq!(
        line_value(&native_lines, "resolution.is_authoritative"),
        "false"
    );
    assert_eq!(line_value(&native_lines, "resolution.fail_closed"), "true");
    assert_eq!(
        line_value(&native_lines, "resolution.authoritative_bytes_available"),
        "false"
    );

    assert_eq!(
        line_value(&metadata_lines, "artifact.kind"),
        "backend_capability_metadata"
    );
    assert_eq!(line_value(&metadata_lines, "authority"), "informational");
    assert_eq!(line_value(&metadata_lines, "status"), "blocked");
    assert_eq!(line_value(&metadata_lines, "reason"), "digest_mismatch");
    assert_eq!(
        line_value(&metadata_lines, "byte.source_identity"),
        "sidecar:backend-capability"
    );
    assert_eq!(
        line_value(&metadata_lines, "resolution.bytes_present"),
        "false"
    );
    assert_eq!(
        line_value(&metadata_lines, "resolution.is_authoritative"),
        "false"
    );
    assert_eq!(
        line_value(&metadata_lines, "resolution.fail_closed"),
        "true"
    );
    assert_eq!(
        line_value(&metadata_lines, "resolution.authoritative_bytes_available"),
        "false"
    );
}

#[test]
fn native_evidence_artifact_authority_validators_fail_closed_on_mutations() {
    fn set_row(rows: &mut [NativeEvidenceArtifactAuthorityRow], key: &str, value: &str) {
        let row = rows
            .iter_mut()
            .find(|row| row.key == key)
            .unwrap_or_else(|| panic!("missing authority row `{key}`"));
        row.value = value.to_string();
    }

    let mut bundle = native_bundle();
    let request = NativeRequestId::new(1);
    let bytes = br#"{"backend":"petri","authority":"ready"}"#.as_slice();
    let artifact = NativeEvidenceArtifact::new(
        "petri.backend-capability.jsonl",
        NativeEvidenceArtifactKind::BackendCapabilityMetadata,
        NativeEvidenceArtifactAttachment::digest_for_bytes(ProofDigestAlgorithm::Sha256, bytes),
    );
    let attachment = NativeEvidenceArtifactAttachment::for_artifact(
        request,
        NativeVerifierSuite::TrustMc,
        &artifact,
        "sidecar:backend=capability\nmetadata",
        bytes.to_vec(),
    );
    bundle.evidence_bundles = vec![
        bundle
            .evidence_bundle_for_request(&bundle.requests[1], vec![artifact])
            .expect("TrustMc evidence"),
    ];
    remove_unreplayed_trust_vc_fixture(&mut bundle);
    bundle.validate().expect("bundle validates");

    let attachments = [attachment];
    let resolution = bundle.resolve_evidence_artifact_attachment(
        NativeEvidenceArtifactAttachmentKey {
            request,
            kind: NativeEvidenceArtifactKind::BackendCapabilityMetadata,
            digest_algorithm: ProofDigestAlgorithm::Sha256,
            digest: NativeEvidenceArtifactAttachment::digest_for_bytes(
                ProofDigestAlgorithm::Sha256,
                bytes,
            ),
        },
        &attachments,
    );
    let report_rows = resolution.report.authority_evidence_rows();
    let rows = resolution.authority_evidence_rows();
    let lines = resolution.authority_evidence_key_value_lines();

    let report_validation = validate_native_evidence_artifact_authority_rows(&report_rows);
    assert!(report_validation.is_valid(), "{report_validation:?}");
    assert_eq!(
        report_validation.rows_kind,
        Some(NativeEvidenceArtifactAuthorityRowsKind::Report)
    );
    assert!(!report_validation.fail_closed());

    let row_validation = validate_native_evidence_artifact_authority_rows(&rows);
    assert!(row_validation.is_valid(), "{row_validation:?}");
    assert_eq!(
        row_validation.rows_kind,
        Some(NativeEvidenceArtifactAuthorityRowsKind::Resolution)
    );

    let line_validation = validate_native_evidence_artifact_authority_key_value_lines(&lines);
    assert!(line_validation.is_valid(), "{line_validation:?}");
    assert_eq!(
        line_validation.rows_kind,
        Some(NativeEvidenceArtifactAuthorityRowsKind::Resolution)
    );

    let mut wrong_schema = rows.clone();
    set_row(
        &mut wrong_schema,
        "artifact_authority.schema",
        "trust_ir.wrong",
    );
    let validation = validate_native_evidence_artifact_authority_rows(&wrong_schema);
    assert!(validation.fail_closed());
    assert!(validation.diagnostic_count() > 0);

    let mut wrong_order = rows.clone();
    wrong_order.swap(0, 1);
    let validation = validate_native_evidence_artifact_authority_rows(&wrong_order);
    assert!(validation.fail_closed());
    assert_eq!(validation.rows_kind, None);

    let mut bad_bool = rows.clone();
    set_row(&mut bad_bool, "resolution.fail_closed", "maybe");
    assert!(validate_native_evidence_artifact_authority_rows(&bad_bool).fail_closed());

    let mut bad_len = rows.clone();
    set_row(&mut bad_len, "byte.len", "not-a-number");
    assert!(validate_native_evidence_artifact_authority_rows(&bad_len).fail_closed());

    let mut bad_digest = rows.clone();
    set_row(
        &mut bad_digest,
        "actual_digest",
        "sha256:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
    );
    assert!(validate_native_evidence_artifact_authority_rows(&bad_digest).fail_closed());

    let mut malformed_lines = lines.clone();
    malformed_lines[0] = "artifact_authority.schema".to_string();
    assert!(
        validate_native_evidence_artifact_authority_key_value_lines(&malformed_lines).fail_closed()
    );
}

#[test]
fn native_evidence_artifact_authority_descriptor_identity_guards_generated_validation() {
    fn generated_validator_accepts(
        descriptor: NativeEvidenceArtifactAuthorityRowDescriptor,
        rows: &[NativeEvidenceArtifactAuthorityRow],
        lines: &[String],
    ) -> bool {
        if descriptor.schema != NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_ROW_SCHEMA
            || descriptor.schema_version != NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_ROW_SCHEMA_VERSION
        {
            return false;
        }
        if !descriptor.resolution_row_keys_match(rows) {
            return false;
        }
        let schema_line = format!("artifact_authority.schema={}", descriptor.schema);
        let schema_version_line = format!(
            "artifact_authority.schema_version={}",
            descriptor.schema_version
        );
        lines.first().map(String::as_str) == Some(schema_line.as_str())
            && lines.get(1).map(String::as_str) == Some(schema_version_line.as_str())
            && lines.len() == descriptor.resolution_row_keys.len()
    }

    let descriptor = native_evidence_artifact_authority_row_descriptor();
    let mut bundle = native_bundle();
    let request = NativeRequestId::new(1);
    let bytes = br#"{"trace":"accepted"}"#.as_slice();
    let artifact = NativeEvidenceArtifact::new(
        "btor2-trace.json",
        NativeEvidenceArtifactKind::Btor2Trace,
        NativeEvidenceArtifactAttachment::digest_for_bytes(ProofDigestAlgorithm::Sha256, bytes),
    );
    let attachment = NativeEvidenceArtifactAttachment::for_artifact(
        request,
        NativeVerifierSuite::TrustMc,
        &artifact,
        "sidecar:btor2-trace",
        bytes.to_vec(),
    );
    bundle.evidence_bundles = vec![
        bundle
            .evidence_bundle_for_request(&bundle.requests[1], vec![artifact.clone()])
            .expect("TrustMc evidence"),
    ];
    remove_unreplayed_trust_vc_fixture(&mut bundle);
    bundle.validate().expect("bundle validates");

    let attachments = [attachment];
    let resolution = bundle.resolve_evidence_artifact_attachment(
        NativeEvidenceArtifactAttachmentKey::for_artifact(request, &artifact),
        &attachments,
    );
    let rows = resolution.authority_evidence_rows();
    let lines = resolution.authority_evidence_key_value_lines();

    assert!(descriptor.resolution_row_keys_match(&rows));
    assert!(generated_validator_accepts(descriptor, &rows, &lines));
    assert_eq!(
        lines.first().map(String::as_str),
        Some("artifact_authority.schema=trust_ir.native.evidence.artifact_authority_row.v1")
    );
    assert_eq!(
        lines.get(1).map(String::as_str),
        Some("artifact_authority.schema_version=1")
    );

    let wrong_schema = NativeEvidenceArtifactAuthorityRowDescriptor {
        schema: NATIVE_EVIDENCE_ARTIFACT_RESOLUTION_SCHEMA,
        ..descriptor
    };
    assert!(wrong_schema.resolution_row_keys_match(&rows));
    assert!(!generated_validator_accepts(wrong_schema, &rows, &lines));

    let wrong_version = NativeEvidenceArtifactAuthorityRowDescriptor {
        schema_version: NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_ROW_SCHEMA_VERSION + 1,
        ..descriptor
    };
    assert!(wrong_version.resolution_row_keys_match(&rows));
    assert!(!generated_validator_accepts(wrong_version, &rows, &lines));

    let mut wrong_line_identity = lines.clone();
    wrong_line_identity[0] =
        "artifact_authority.schema=trust_ir.native.evidence.artifact_resolution.v1".to_string();
    assert!(descriptor.resolution_row_keys_match(&rows));
    assert!(!generated_validator_accepts(
        descriptor,
        &rows,
        &wrong_line_identity
    ));
}

#[test]
fn native_evidence_artifact_attachment_fails_closed_for_wrong_bindings() {
    let mut bundle = native_bundle();
    let request = NativeRequestId::new(1);
    let bytes = b"(set-logic HORN)\n(assert true)\n";
    let digest =
        NativeEvidenceArtifactAttachment::digest_for_bytes(ProofDigestAlgorithm::Sha256, bytes);
    let artifact = NativeEvidenceArtifact::new(
        "trust_mc-chc.smt2",
        NativeEvidenceArtifactKind::TrustMcHornClauses,
        digest,
    );
    bundle.evidence_bundles = vec![
        bundle
            .evidence_bundle_for_request(&bundle.requests[1], vec![artifact.clone()])
            .expect("TrustMc evidence"),
    ];
    remove_unreplayed_trust_vc_fixture(&mut bundle);
    bundle.validate().expect("bundle validates");
    let key = NativeEvidenceArtifactAttachmentKey::for_artifact(request, &artifact);
    let good = NativeEvidenceArtifactAttachment::for_artifact(
        request,
        NativeVerifierSuite::TrustMc,
        &artifact,
        "memory:trust_mc-horn-clauses",
        bytes.to_vec(),
    );

    let missing = bundle.resolve_evidence_artifact_attachment(key, &[]);
    assert!(missing.report.fail_closed());
    assert_eq!(missing.bytes, None);
    assert_eq!(missing.report.reason_code(), "missing_attachment");
    assert_eq!(missing.report.authority_code(), "informational");

    let duplicate_attachments = [good.clone(), good.clone()];
    let duplicate = bundle.resolve_evidence_artifact_attachment(key, &duplicate_attachments);
    assert!(duplicate.report.fail_closed());
    assert_eq!(duplicate.report.reason_code(), "duplicate_attachment");

    let wrong_suite = NativeEvidenceArtifactAttachment {
        owner_suite: NativeVerifierSuite::TrustVc,
        ..good.clone()
    };
    let wrong_suite_attachments = [wrong_suite];
    let suite_report = bundle.resolve_evidence_artifact_attachment(key, &wrong_suite_attachments);
    assert!(suite_report.report.fail_closed());
    assert_eq!(suite_report.report.reason_code(), "owner_suite_mismatch");

    let wrong_request = NativeEvidenceArtifactAttachment::for_artifact(
        NativeRequestId::new(2),
        NativeVerifierSuite::TrustMc,
        &artifact,
        "memory:trust_mc-horn-clauses",
        bytes.to_vec(),
    );
    let wrong_request_attachments = [wrong_request];
    let cross_request =
        bundle.resolve_evidence_artifact_attachment(key, &wrong_request_attachments);
    assert!(cross_request.report.fail_closed());
    assert_eq!(cross_request.report.reason_code(), "missing_attachment");

    let stale_bytes = NativeEvidenceArtifactAttachment::for_artifact(
        request,
        NativeVerifierSuite::TrustMc,
        &artifact,
        "memory:trust_mc-horn-clauses",
        b"(assert false)\n".to_vec(),
    );
    let stale_attachments = [stale_bytes];
    let stale_report = bundle.resolve_evidence_artifact_attachment(key, &stale_attachments);
    assert!(stale_report.report.fail_closed());
    assert_eq!(stale_report.report.reason_code(), "digest_mismatch");
    assert_eq!(
        stale_report.report.authority,
        NativeEvidenceArtifactAuthority::Informational
    );
    assert_ne!(stale_report.report.actual_digest, Some(digest));

    let wrong_algorithm_key = NativeEvidenceArtifactAttachmentKey::new(
        request,
        NativeEvidenceArtifactKind::TrustMcHornClauses,
        ProofDigestAlgorithm::TrustIrStableV1,
        ProofDigest::trust_ir_stable("test.trust_mc.horn", bytes),
    );
    let wrong_algorithm_attachments = [good.clone()];
    let wrong_algorithm = bundle
        .resolve_evidence_artifact_attachment(wrong_algorithm_key, &wrong_algorithm_attachments);
    assert!(wrong_algorithm.report.fail_closed());
    assert_eq!(
        wrong_algorithm.report.reason_code(),
        "non_cryptographic_digest_algorithm"
    );

    let unsupported_kind_key = NativeEvidenceArtifactAttachmentKey::new(
        request,
        NativeEvidenceArtifactKind::TrustVcCertificateImport,
        digest.algorithm,
        digest,
    );
    let unsupported_kind_attachments = [good];
    let unsupported_kind = bundle
        .resolve_evidence_artifact_attachment(unsupported_kind_key, &unsupported_kind_attachments);
    assert!(unsupported_kind.report.fail_closed());
    assert_eq!(
        unsupported_kind.report.reason_code(),
        "unsupported_artifact_kind"
    );
}

#[test]
fn native_evidence_artifact_attachment_resolves_required_kinds_with_real_digests() {
    let mut bundle = native_bundle();
    let request = NativeRequestId::new(1);
    let horn_bytes = b"(set-logic HORN)\n(assert true)\n".as_slice();
    let replay_bytes = br#"{"replay":"accepted"}"#.as_slice();
    let model_bytes = br#"{"model":"accepted"}"#.as_slice();
    let stale_model_bytes = br#"{"model":"stale"}"#.as_slice();
    let artifacts = vec![
        NativeEvidenceArtifact::new(
            "trust_mc-chc.smt2",
            NativeEvidenceArtifactKind::TrustMcHornClauses,
            NativeEvidenceArtifactAttachment::digest_for_bytes(
                ProofDigestAlgorithm::Sha256,
                horn_bytes,
            ),
        ),
        NativeEvidenceArtifact::new(
            "trust_mc-replay.json",
            NativeEvidenceArtifactKind::ReplayTranscript,
            NativeEvidenceArtifactAttachment::digest_for_bytes(
                ProofDigestAlgorithm::Sha256,
                replay_bytes,
            ),
        ),
        NativeEvidenceArtifact::new(
            "trust_mc-model.json",
            NativeEvidenceArtifactKind::TrustMcModel,
            NativeEvidenceArtifactAttachment::digest_for_bytes(
                ProofDigestAlgorithm::Sha256,
                model_bytes,
            ),
        ),
    ];
    bundle.evidence_bundles = vec![
        bundle
            .evidence_bundle_for_request(&bundle.requests[1], artifacts.clone())
            .expect("TrustMc evidence"),
    ];
    remove_unreplayed_trust_vc_fixture(&mut bundle);
    bundle.validate().expect("bundle validates");
    let horn_attachment = NativeEvidenceArtifactAttachment::for_artifact(
        request,
        NativeVerifierSuite::TrustMc,
        &artifacts[0],
        "memory:trust_mc-horn-clauses",
        horn_bytes.to_vec(),
    );
    let stale_model_attachment = NativeEvidenceArtifactAttachment::for_artifact(
        request,
        NativeVerifierSuite::TrustMc,
        &artifacts[2],
        "memory:trust_mc-model",
        stale_model_bytes.to_vec(),
    );
    let attachments = [horn_attachment, stale_model_attachment];

    let resolutions = bundle.resolve_evidence_artifact_attachments_for_kinds(
        request,
        PETRI_SUCCESSOR_TRUST_MC_CHC_PRODUCTION_ACCEPTANCE_REQUIRED_ARTIFACT_KINDS,
        &attachments,
    );

    assert_eq!(resolutions.len(), 3);
    assert_eq!(
        resolutions
            .iter()
            .map(|resolution| resolution.required_kind)
            .collect::<Vec<_>>(),
        PETRI_SUCCESSOR_TRUST_MC_CHC_PRODUCTION_ACCEPTANCE_REQUIRED_ARTIFACT_KINDS
    );

    let horn = &resolutions[0];
    assert!(horn.is_authoritative());
    assert!(!horn.fail_closed());
    assert_eq!(horn.status_code(), "resolved");
    assert_eq!(horn.reason_code(), "resolved");
    assert_eq!(horn.artifact_digest(), Some(artifacts[0].digest));
    assert_eq!(horn.actual_digest(), Some(artifacts[0].digest));
    assert_eq!(horn.bytes(), Some(horn_bytes));
    assert_eq!(horn.authoritative_bytes(), Some(horn_bytes));
    assert_eq!(
        horn.byte_source_identity(),
        Some("memory:trust_mc-horn-clauses")
    );
    assert!(
        native_evidence_artifact_authority_row_descriptor()
            .resolution_row_keys_match(&horn.authority_evidence_rows().expect("authority rows"))
    );

    let replay = &resolutions[1];
    assert_eq!(
        replay.required_kind,
        NativeEvidenceArtifactKind::ReplayTranscript
    );
    assert!(!replay.is_authoritative());
    assert!(replay.fail_closed());
    assert_eq!(replay.status_code(), "blocked");
    assert_eq!(replay.reason_code(), "missing_attachment");
    assert_eq!(replay.artifact_digest(), Some(artifacts[1].digest));
    assert_eq!(replay.actual_digest(), None);
    assert_eq!(replay.bytes(), None);
    assert_eq!(replay.authoritative_bytes(), None);
    assert!(
        native_evidence_artifact_authority_row_descriptor()
            .resolution_row_keys_match(&replay.authority_evidence_rows().expect("authority rows"))
    );

    let model = &resolutions[2];
    assert_eq!(
        model.required_kind,
        NativeEvidenceArtifactKind::TrustMcModel
    );
    assert!(!model.is_authoritative());
    assert!(model.fail_closed());
    assert_eq!(model.reason_code(), "digest_mismatch");
    assert_eq!(model.artifact_digest(), Some(artifacts[2].digest));
    assert_eq!(
        model.actual_digest(),
        Some(NativeEvidenceArtifactAttachment::digest_for_bytes(
            ProofDigestAlgorithm::Sha256,
            stale_model_bytes
        ))
    );
    assert_eq!(model.byte_len(), Some(stale_model_bytes.len()));
    assert_eq!(model.bytes(), None);
    assert_eq!(model.authoritative_bytes(), None);
}

#[test]
fn native_evidence_artifact_attachment_kind_resolution_omits_placeholder_digest_rows() {
    let mut bundle = native_bundle();
    let request = NativeRequestId::new(1);
    let horn_bytes = b"(set-logic HORN)\n(assert true)\n";
    let horn_artifact = NativeEvidenceArtifact::new(
        "trust_mc-chc.smt2",
        NativeEvidenceArtifactKind::TrustMcHornClauses,
        NativeEvidenceArtifactAttachment::digest_for_bytes(
            ProofDigestAlgorithm::Sha256,
            horn_bytes,
        ),
    );
    bundle.evidence_bundles = vec![
        bundle
            .evidence_bundle_for_request(&bundle.requests[1], vec![horn_artifact])
            .expect("TrustMc evidence"),
    ];
    remove_unreplayed_trust_vc_fixture(&mut bundle);
    bundle.validate().expect("bundle validates");

    let missing = bundle.resolve_evidence_artifact_attachment_for_kind(
        request,
        NativeEvidenceArtifactKind::TrustMcModel,
        &[],
    );

    assert_eq!(missing.owner_suite, Some(NativeVerifierSuite::TrustMc));
    assert_eq!(
        missing.required_kind,
        NativeEvidenceArtifactKind::TrustMcModel
    );
    assert_eq!(missing.status_code(), "blocked");
    assert_eq!(missing.reason_code(), "missing_artifact_descriptor");
    assert!(missing.fail_closed());
    assert_eq!(missing.artifact, None);
    assert_eq!(missing.resolution, None);
    assert_eq!(missing.artifact_digest(), None);
    assert_eq!(missing.actual_digest(), None);
    assert_eq!(missing.bytes(), None);
    assert_eq!(missing.authoritative_bytes(), None);
    assert_eq!(missing.authority_evidence_rows(), None);
    assert_eq!(missing.authority_evidence_key_value_lines(), None);
}

#[test]
fn native_evidence_bundle_helper_fails_closed_without_replay_identity() {
    let bundle = native_bundle();
    let mut request = bundle.requests[1].clone();
    if let NativeVerificationRequest::TrustMc(request) = &mut request {
        request.provenance.replay = None;
    } else {
        panic!("TrustMc request");
    }

    let error =
        NativeEvidenceBundle::from_request(bundle.trust_ir_module_digest, &request, Vec::new())
            .expect_err("missing replay identity rejected");

    assert_eq!(
        error,
        NativeVerificationBundleError::MissingReplayIdentity(NativeRequestId::new(1))
    );
}

#[test]
fn native_evidence_consumption_report_rejects_unreplayed_certificate_refs() {
    let mut bundle = native_bundle();
    bundle.evidence_bundles = native_evidence_bundles(&bundle);

    let errors = bundle
        .native_evidence_consumption_report()
        .expect_err("unreplayed TrustVc certificate must not be consumable");
    assert!(errors.iter().any(|error| matches!(
        error,
        NativeVerificationBundleError::TrustVcCertificateNotDischarged {
            request: NativeRequestId(0),
            obligation: ProofId(0),
            status: ProofStatus::Discharged,
            ..
        }
    )));
}

#[test]
fn native_transport_identity_exposes_bundle_digests_and_target_abi() {
    let mut bundle = native_bundle();
    bundle.module.target_info = Some(TargetInfo {
        triple: "x86_64-unknown-linux-gnu".to_string(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    let updated_module_digest = bundle.module.stable_digest();
    bundle.trust_ir_module_digest = updated_module_digest;
    for root in &mut bundle.lineage.nodes {
        if bundle.lineage.roots.contains(&root.id) {
            root.target_module = updated_module_digest;
        }
    }
    bundle.evidence_bundles = native_evidence_bundles(&bundle);

    let identity = bundle.transport_identity();

    assert_eq!(identity.schema, NATIVE_TRANSPORT_IDENTITY_SCHEMA);
    assert_eq!(
        identity.schema_version,
        NATIVE_TRANSPORT_IDENTITY_SCHEMA_VERSION
    );
    assert_eq!(identity.bundle_schema_version, bundle.schema_version);
    assert_eq!(identity.producer, NativeBundleProducer::TRust);
    assert_eq!(identity.source_digest, Some(digest(0xA1)));
    assert_eq!(identity.trust_ir_module_digest, updated_module_digest);
    assert_eq!(
        identity.compiler_facts_digest,
        bundle.compiler_facts.stable_digest()
    );
    assert_eq!(identity.lineage_digest, bundle.lineage.stable_digest());
    assert_eq!(identity.bundle_digest, bundle.stable_digest());
    assert!(!identity.stable_digest().is_zero());
    assert_eq!(identity.request_digests.len(), 3);
    assert_eq!(identity.evidence_digests.len(), 3);
    assert_eq!(
        identity.request_digests[1].digest,
        bundle.requests[1].stable_digest()
    );

    let target_abi = identity.target_abi.expect("target ABI identity");
    assert_eq!(target_abi.triple, "x86_64-unknown-linux-gnu");
    assert_eq!(target_abi.pointer_size, 8);
    assert_eq!(target_abi.endianness, Endianness::Little);
    assert_eq!(target_abi.digest, target_abi.stable_digest());
    assert!(!target_abi.digest.is_zero());
}

#[test]
fn native_transport_identity_rows_are_sidecar_ready() {
    let mut bundle = native_bundle();
    bundle.module.target_info = Some(TargetInfo {
        triple: "x86_64-unknown-linux-gnu".to_string(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    bundle.evidence_bundles = native_evidence_bundles(&bundle);

    let identity = bundle.transport_identity();
    let rows = identity.identity_rows();
    let lines = identity.identity_key_value_lines();
    let text = identity.identity_key_value_text();
    let values: BTreeMap<_, _> = rows
        .iter()
        .map(|row| (row.key.clone(), row.value.clone()))
        .collect();
    let keys: BTreeSet<_> = rows.iter().map(|row| row.key.as_str()).collect();
    let identity_digest = identity.stable_digest().to_string();
    let bundle_digest = identity.bundle_digest.to_string();
    let target_abi_digest = identity
        .target_abi
        .as_ref()
        .expect("target ABI identity")
        .digest
        .to_string();
    let row_replay = identity.identity_replay_report(&rows);
    let line_replay = identity.identity_replay_report_for_key_value_lines(&lines);
    let text_replay = identity.identity_replay_report_for_key_value_text(&text);
    let summary_rows = row_replay.compact_health_summary_rows();
    let summary_lines = row_replay.compact_health_summary_key_value_lines();
    let summary_json: serde_json::Value =
        serde_json::from_str(&row_replay.compact_health_summary_json_text())
            .expect("compact transport identity health JSON should parse");
    let summary_row_round_trip = row_replay.compact_health_summary_round_trip_report(&summary_rows);
    let summary_line_round_trip =
        row_replay.compact_health_summary_round_trip_report_for_key_value_lines(&summary_lines);
    let summary_text_round_trip = row_replay
        .compact_health_summary_round_trip_report_for_key_value_text(
            &row_replay.compact_health_summary_key_value_text(),
        );
    let summary_values: BTreeMap<_, _> = summary_rows
        .iter()
        .map(|row| (row.key.as_str(), row.value.as_str()))
        .collect();

    assert_eq!(
        keys.len(),
        rows.len(),
        "transport identity rows must use unique keys"
    );
    assert_eq!(text, format!("{}\n", lines.join("\n")));
    assert_eq!(row_replay, line_replay);
    assert_eq!(row_replay, text_replay);
    assert_eq!(
        row_replay.status,
        NativeTransportIdentityReplayStatus::Replayable
    );
    assert!(row_replay.is_replayable());
    assert!(!row_replay.fail_closed);
    assert_eq!(row_replay.diagnostic_count(), 0);
    assert!(row_replay.schema_matches);
    assert!(row_replay.identity_digest_matches);
    assert!(row_replay.bundle_digest_matches);
    assert!(row_replay.request_digest_count_matches);
    assert!(row_replay.evidence_digest_count_matches);
    assert_eq!(summary_row_round_trip, summary_line_round_trip);
    assert_eq!(summary_row_round_trip, summary_text_round_trip);
    assert_eq!(
        summary_row_round_trip.status,
        NativeTransportIdentityReplayHealthSummaryRoundTripStatus::Valid
    );
    assert!(summary_row_round_trip.is_valid());
    assert!(!summary_row_round_trip.fail_closed);
    assert_eq!(summary_row_round_trip.diagnostic_count(), 0);
    assert!(summary_row_round_trip.schema_matches);
    assert!(summary_row_round_trip.status_matches);
    assert!(summary_row_round_trip.fail_closed_matches);
    assert!(summary_row_round_trip.diagnostic_count_matches);
    assert_eq!(
        values.get("transport_identity.schema").map(String::as_str),
        Some(NATIVE_TRANSPORT_IDENTITY_SCHEMA)
    );
    assert_eq!(
        values.get("transport_identity.digest").map(String::as_str),
        Some(identity_digest.as_str())
    );
    assert_eq!(
        values
            .get("transport_identity.digest.algorithm")
            .map(String::as_str),
        Some("sha256")
    );
    assert_eq!(
        values
            .get("transport_identity.bundle_digest")
            .map(String::as_str),
        Some(bundle_digest.as_str())
    );
    assert_eq!(
        values
            .get("transport_identity.producer")
            .map(String::as_str),
        Some("trust")
    );
    assert_eq!(
        values
            .get("transport_identity.input.kind")
            .map(String::as_str),
        Some("rust_mir")
    );
    assert_eq!(
        values
            .get("transport_identity.target_abi.present")
            .map(String::as_str),
        Some("true")
    );
    assert_eq!(
        values
            .get("transport_identity.target_abi.triple")
            .map(String::as_str),
        Some("x86_64-unknown-linux-gnu")
    );
    assert_eq!(
        values
            .get("transport_identity.target_abi.pointer_size")
            .map(String::as_str),
        Some("8")
    );
    assert_eq!(
        values
            .get("transport_identity.target_abi.endianness")
            .map(String::as_str),
        Some("little")
    );
    assert_eq!(
        values
            .get("transport_identity.target_abi.digest")
            .map(String::as_str),
        Some(target_abi_digest.as_str())
    );
    assert_eq!(
        values
            .get("transport_identity.request_digest.count")
            .map(String::as_str),
        Some("3")
    );
    assert_eq!(
        values
            .get("transport_identity.evidence_digest.count")
            .map(String::as_str),
        Some("3")
    );
    assert_eq!(
        row_replay.compact_health_summary_key_value_text(),
        format!("{}\n", summary_lines.join("\n"))
    );
    assert_eq!(
        summary_values
            .get("transport_identity_replay_report.schema")
            .copied(),
        Some(NATIVE_TRANSPORT_IDENTITY_SCHEMA)
    );
    assert_eq!(
        summary_values
            .get("transport_identity_replay_report.status")
            .copied(),
        Some("replayable")
    );
    assert_eq!(
        summary_values
            .get("transport_identity_replay_report.fail_closed")
            .copied(),
        Some("false")
    );
    assert_eq!(
        summary_values
            .get("transport_identity_replay_report.count.diagnostics")
            .copied(),
        Some("0")
    );
    assert_eq!(
        summary_values
            .get("transport_identity_replay_report.reconstructed.identity_digest")
            .copied(),
        Some(identity_digest.as_str())
    );
    assert_eq!(
        summary_values
            .get("transport_identity_replay_report.agreement.identity_digest")
            .copied(),
        Some("true")
    );
    assert_eq!(
        summary_json
            .get("schema")
            .and_then(serde_json::Value::as_str),
        summary_values
            .get("transport_identity_replay_report.schema")
            .copied()
    );
    assert_eq!(
        summary_json
            .get("status")
            .and_then(serde_json::Value::as_str),
        summary_values
            .get("transport_identity_replay_report.status")
            .copied()
    );
    assert_eq!(
        summary_json
            .get("fail_closed")
            .and_then(serde_json::Value::as_bool),
        Some(false)
    );
    assert_eq!(
        summary_json
            .get("diagnostic_count")
            .and_then(serde_json::Value::as_u64),
        Some(0)
    );
    assert_eq!(
        summary_json
            .get("reconstructed_identity_digest")
            .and_then(serde_json::Value::as_str),
        Some(identity_digest.as_str())
    );

    let no_target_identity = native_bundle().transport_identity();
    let no_target_values: BTreeMap<_, _> = no_target_identity
        .identity_rows()
        .iter()
        .map(|row| (row.key.clone(), row.value.clone()))
        .collect();
    let no_target_replay =
        no_target_identity.identity_replay_report(&no_target_identity.identity_rows());
    assert!(no_target_replay.is_replayable());
    assert_eq!(
        no_target_values
            .get("transport_identity.target_abi.present")
            .map(String::as_str),
        Some("false")
    );
    assert_eq!(
        no_target_values
            .get("transport_identity.target_abi.pointer_size")
            .map(String::as_str),
        Some("none")
    );
}

#[test]
fn native_transport_identity_replay_report_fails_closed_on_bad_text() {
    let mut bundle = native_bundle();
    bundle.module.target_info = Some(TargetInfo {
        triple: "x86_64-unknown-linux-gnu".to_string(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    bundle.evidence_bundles = native_evidence_bundles(&bundle);
    let identity = bundle.transport_identity();
    let mut lines = identity.identity_key_value_lines();
    lines[0] = "malformed transport identity line".to_string();
    if let Some(line) = lines
        .iter_mut()
        .find(|line| line.starts_with("transport_identity.schema_version="))
    {
        *line = "transport_identity.schema_version=not_usize".to_string();
    }
    if let Some(line) = lines
        .iter_mut()
        .find(|line| line.starts_with("transport_identity.target_abi.present="))
    {
        *line = "transport_identity.target_abi.present=not_bool".to_string();
    }
    if let Some(line) = lines
        .iter_mut()
        .find(|line| line.starts_with("transport_identity.request_digest.0.request="))
    {
        *line = "transport_identity.request_digest.0.request=not_usize".to_string();
    }
    if let Some(line) = lines
        .iter_mut()
        .find(|line| line.starts_with("transport_identity.trust_ir_module_digest="))
    {
        *line = format!("transport_identity.trust_ir_module_digest={}", digest(0xDE));
    }
    lines.push(format!(
        "transport_identity.bundle_digest={}",
        identity.bundle_digest
    ));
    lines.push("transport_identity.extra=unexpected".to_string());

    let validation = identity.identity_replay_report_for_key_value_lines(&lines);

    assert_eq!(
        validation.status,
        NativeTransportIdentityReplayStatus::Invalid
    );
    assert!(!validation.is_replayable());
    assert!(validation.fail_closed);
    assert_eq!(validation.invalid_lines.len(), 1);
    assert!(
        validation
            .missing_keys
            .contains(&"transport_identity.schema".to_string())
    );
    assert!(
        validation
            .duplicate_keys
            .contains(&"transport_identity.bundle_digest".to_string())
    );
    assert!(
        validation
            .unexpected_keys
            .contains(&"transport_identity.extra".to_string())
    );
    assert!(
        validation
            .mismatched_value_keys
            .contains(&"transport_identity.trust_ir_module_digest".to_string())
    );
    assert!(
        validation
            .invalid_usize_keys
            .contains(&"transport_identity.schema_version".to_string())
    );
    assert!(
        validation
            .invalid_usize_keys
            .contains(&"transport_identity.request_digest.0.request".to_string())
    );
    assert!(
        validation
            .invalid_bool_keys
            .contains(&"transport_identity.target_abi.present".to_string())
    );
    assert!(!validation.schema_matches);
    assert!(validation.identity_digest_matches);
    assert!(validation.bundle_digest_matches);
    assert!(validation.diagnostic_count() >= 7);
}

#[test]
fn native_transport_identity_health_summary_round_trip_fails_closed() {
    let mut bundle = native_bundle();
    bundle.module.target_info = Some(TargetInfo {
        triple: "x86_64-unknown-linux-gnu".to_string(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    bundle.evidence_bundles = native_evidence_bundles(&bundle);
    let identity = bundle.transport_identity();
    let replay_report = identity.identity_replay_report(&identity.identity_rows());
    let mut lines = replay_report.compact_health_summary_key_value_lines();
    lines[0] = "malformed transport identity health summary line".to_string();
    if let Some(line) = lines
        .iter_mut()
        .find(|line| line.starts_with("transport_identity_replay_report.schema_version="))
    {
        *line = "transport_identity_replay_report.schema_version=not_usize".to_string();
    }
    if let Some(line) = lines
        .iter_mut()
        .find(|line| line.starts_with("transport_identity_replay_report.fail_closed="))
    {
        *line = "transport_identity_replay_report.fail_closed=not_bool".to_string();
    }
    lines.push("transport_identity_replay_report.status=replayable".to_string());
    lines.push("transport_identity_replay_report.extra=unexpected".to_string());

    let validation =
        replay_report.compact_health_summary_round_trip_report_for_key_value_lines(&lines);

    assert_eq!(
        validation.status,
        NativeTransportIdentityReplayHealthSummaryRoundTripStatus::Invalid
    );
    assert!(!validation.is_valid());
    assert!(validation.fail_closed);
    assert_eq!(validation.invalid_lines.len(), 1);
    assert!(
        validation
            .missing_keys
            .contains(&"transport_identity_replay_report.schema".to_string())
    );
    assert!(
        validation
            .duplicate_keys
            .contains(&"transport_identity_replay_report.status".to_string())
    );
    assert!(
        validation
            .unexpected_keys
            .contains(&"transport_identity_replay_report.extra".to_string())
    );
    assert!(
        validation
            .invalid_usize_keys
            .contains(&"transport_identity_replay_report.schema_version".to_string())
    );
    assert!(
        validation
            .invalid_bool_keys
            .contains(&"transport_identity_replay_report.fail_closed".to_string())
    );
    assert!(!validation.schema_matches);
    assert!(validation.status_matches);
    assert!(!validation.fail_closed_matches);
    assert!(validation.diagnostic_count() >= 5);
}

#[test]
fn native_bundle_identity_contract_descriptor_names_petri_manifest_fields() {
    let descriptor = native_bundle_identity_contract_descriptor();

    // The former assertions here (descriptor == its own const, each field ==
    // the const it was assembled from, and `contains()` checks against
    // hard-coded copies of the descriptor's own `provided_fields` /
    // `digest_contexts` / `external_fields` string slices) were tautological
    // name mirrors and have been removed. The behavioral coverage below
    // derives a real transport identity from a constructed bundle and pins
    // those live values against the descriptor's declared schema metadata.
    let mut bundle = native_bundle();
    bundle.module.target_info = Some(TargetInfo {
        triple: "x86_64-unknown-linux-gnu".to_string(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    bundle.evidence_bundles = native_evidence_bundles(&bundle);
    let identity = bundle.transport_identity();

    assert_eq!(
        identity.schema.as_str(),
        descriptor.transport_identity_schema
    );
    assert_eq!(
        identity.schema_version,
        descriptor.transport_identity_schema_version
    );
    assert_eq!(
        identity.bundle_schema_version,
        descriptor.bundle_schema_version
    );
    assert_eq!(identity.source_digest, bundle.source_digest());
    assert_eq!(
        identity.trust_ir_module_digest,
        bundle.trust_ir_module_digest
    );
    assert_eq!(
        identity.compiler_facts_digest,
        bundle.compiler_facts.stable_digest()
    );
    assert_eq!(identity.bundle_digest, bundle.stable_digest());

    let target_abi = identity.target_abi.expect("target ABI identity");
    assert_eq!(target_abi.triple, "x86_64-unknown-linux-gnu");
    assert_eq!(target_abi.pointer_size, 8);
    assert_eq!(target_abi.endianness, Endianness::Little);
    assert_eq!(target_abi.digest, target_abi.stable_digest());

    let function = bundle
        .module
        .function_by_id(FuncId::new(0))
        .expect("checked_add function");
    assert_eq!(function.name, "checked_add");
    let func_ty = bundle
        .module
        .func_type(function.ty)
        .expect("checked_add function type");
    assert_eq!(func_ty.params.as_slice(), &[Ty::I32]);
    assert_eq!(func_ty.returns.as_slice(), &[Ty::I32]);
    assert!(!func_ty.is_vararg);

    let monomorphization = &bundle.compiler_facts.monomorphizations[0];
    assert_eq!(monomorphization.source_item, "checked_add");
    assert_eq!(monomorphization.symbol, "_RNvCs_test_checked_add");
    assert_eq!(
        monomorphization.generic_args,
        vec![NativeGenericArg::Ty(Ty::I32)]
    );
    assert_eq!(monomorphization.function, Some(function.id));
    assert!(!monomorphization.stable_digest.is_zero());
    assert_eq!(
        bundle.monomorphization(monomorphization.id),
        Some(monomorphization)
    );
    assert_eq!(
        bundle.monomorphization_by_stable_digest(monomorphization.stable_digest),
        Some(monomorphization)
    );
}

#[test]
fn petri_successor_trust_mc_chc_contract_descriptor_is_self_describing() {
    let descriptor = petri_successor_trust_mc_chc_contract_descriptor();
    let native_descriptor = native_bundle_identity_contract_descriptor();

    // The leading schema/version equality block (descriptor.<field> == the
    // const it was assembled from) was a tautological name mirror and has
    // been removed. The value pins below assert concrete artifact-kind sets,
    // status/reason `.code()` vocabularies, and the literal acceptance-API
    // strings — drift in any of those is real behavior, not a name mirror —
    // and the closing loop cross-checks that the Petri descriptor's
    // `provided_fields` are a subset of the native identity descriptor's.
    assert_eq!(
        descriptor.binding_required_artifact_kinds,
        &[NativeEvidenceArtifactKind::TrustMcHornClauses]
    );
    assert_eq!(
        descriptor.proof_handoff_required_artifact_kinds,
        &[NativeEvidenceArtifactKind::ReplayTranscript]
    );
    assert_eq!(
        descriptor.proof_handoff_optional_artifact_kinds,
        &[NativeEvidenceArtifactKind::TrustMcModel]
    );
    assert_eq!(
        descriptor.model_validation_required_artifact_kinds,
        &[NativeEvidenceArtifactKind::TrustMcModel]
    );
    assert_eq!(
        descriptor.production_acceptance_required_artifact_kinds,
        &[
            NativeEvidenceArtifactKind::TrustMcHornClauses,
            NativeEvidenceArtifactKind::ReplayTranscript,
            NativeEvidenceArtifactKind::TrustMcModel,
        ]
    );
    assert_eq!(
        descriptor.model_validation_requires_solver_acceptance,
        PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_VALIDATION_REQUIRES_SOLVER_ACCEPTANCE
    );
    assert_eq!(
        descriptor.model_acceptance_report_api_name,
        PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_ACCEPTANCE_REPORT_API_NAME
    );
    assert_eq!(
        descriptor.model_acceptance_report_api_name,
        "ay::chc::trust_mc_petri_successor_chc_model_acceptance_report"
    );
    assert_eq!(
        descriptor.consumer_acceptance_api_name,
        PETRI_SUCCESSOR_TRUST_MC_CHC_CONSUMER_ACCEPTANCE_API_NAME
    );
    assert_eq!(
        descriptor.consumer_acceptance_api_name,
        "ay::chc::TrustMcPetriSuccessorChcModelAcceptanceReport::accept_for_consumer"
    );
    assert_eq!(
        descriptor.production_acceptance_owner_suite,
        PETRI_SUCCESSOR_TRUST_MC_CHC_PRODUCTION_ACCEPTANCE_OWNER_SUITE
    );
    assert_eq!(
        descriptor.production_acceptance_owner_suite,
        NativeVerifierSuite::AY
    );
    assert_eq!(
        descriptor.shared_primitive_contract,
        petri_successor_trust_mc_chc_shared_primitive_contract_descriptor()
    );
    assert_eq!(
        descriptor.binding_status_codes,
        &[
            PetriSuccessorTrustMcChcBindingStatus::Bound.code(),
            PetriSuccessorTrustMcChcBindingStatus::Blocked.code(),
        ]
    );
    assert_eq!(
        descriptor.binding_reason_codes,
        &[
            PetriSuccessorTrustMcChcBindingReason::Bound.code(),
            PetriSuccessorTrustMcChcBindingReason::BundleInvalid.code(),
            PetriSuccessorTrustMcChcBindingReason::SemanticBridgeBlocked.code(),
            PetriSuccessorTrustMcChcBindingReason::MissingBridgeProofObligation.code(),
            PetriSuccessorTrustMcChcBindingReason::MissingTrustMcChcRequest.code(),
            PetriSuccessorTrustMcChcBindingReason::MissingTrustMcChcEvidence.code(),
            PetriSuccessorTrustMcChcBindingReason::EvidenceBindingMismatch.code(),
            PetriSuccessorTrustMcChcBindingReason::MissingHornClauseArtifact.code(),
        ]
    );
    assert_eq!(
        descriptor.proof_handoff_status_codes,
        &[
            PetriSuccessorTrustMcChcProofHandoffStatus::Ready.code(),
            PetriSuccessorTrustMcChcProofHandoffStatus::Blocked.code(),
        ]
    );
    assert_eq!(
        descriptor.proof_handoff_reason_codes,
        &[
            PetriSuccessorTrustMcChcProofHandoffReason::Ready.code(),
            PetriSuccessorTrustMcChcProofHandoffReason::BindingBlocked.code(),
            PetriSuccessorTrustMcChcProofHandoffReason::MissingTrustMcChcEvidence.code(),
            PetriSuccessorTrustMcChcProofHandoffReason::MissingReplayTranscriptDigest.code(),
            PetriSuccessorTrustMcChcProofHandoffReason::MissingReplayTranscriptArtifact.code(),
            PetriSuccessorTrustMcChcProofHandoffReason::ReplayTranscriptDigestMismatch.code(),
        ]
    );
    assert_eq!(
        descriptor.model_validation_readiness_status_codes,
        &[
            PetriSuccessorTrustMcChcModelValidationReadinessStatus::ReadyForSolverValidation.code(),
            PetriSuccessorTrustMcChcModelValidationReadinessStatus::Blocked.code(),
        ]
    );
    assert_eq!(
        descriptor.model_validation_readiness_reason_codes,
        &[
            PetriSuccessorTrustMcChcModelValidationReadinessReason::SolverValidationRequired.code(),
            PetriSuccessorTrustMcChcModelValidationReadinessReason::ProofHandoffBlocked.code(),
            PetriSuccessorTrustMcChcModelValidationReadinessReason::MissingModelArtifact.code(),
        ]
    );

    for field in descriptor.provided_fields {
        assert!(
            native_descriptor.provided_fields.contains(field),
            "Petri descriptor field missing from native identity descriptor: {field}"
        );
    }
}

#[test]
fn petri_successor_trust_mc_chc_shared_primitive_contract_is_policy_light() {
    let contract = petri_successor_trust_mc_chc_shared_primitive_contract_descriptor();

    assert_eq!(
        contract,
        PETRI_SUCCESSOR_TRUST_MC_CHC_SHARED_PRIMITIVE_CONTRACT_DESCRIPTOR
    );
    assert_eq!(contract.schema, NATIVE_SHARED_PRIMITIVE_CONTRACT_SCHEMA);
    assert_eq!(
        contract.schema_version,
        NATIVE_SHARED_PRIMITIVE_CONTRACT_SCHEMA_VERSION
    );
    assert_eq!(
        contract.contract_schema,
        PETRI_SUCCESSOR_TRUST_MC_CHC_CONTRACT_SCHEMA
    );
    assert_eq!(
        contract.contract_schema_version,
        PETRI_SUCCESSOR_TRUST_MC_CHC_CONTRACT_SCHEMA_VERSION
    );
    assert_eq!(
        contract.formula_schema,
        PETRI_SUCCESSOR_PLAN_CACHE_EQUIVALENCE_SCHEMA
    );
    assert_eq!(
        contract.readiness_report_schema,
        PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_VALIDATION_READINESS_SCHEMA
    );
    assert_eq!(
        contract.readiness_report_schema_version,
        PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_VALIDATION_READINESS_SCHEMA_VERSION
    );
    assert_eq!(contract.verifier_suite, NativeVerifierSuite::TrustMc);
    assert_eq!(
        contract.verification_mode,
        NativeSharedPrimitiveVerificationMode::TrustMc(TrustMcVerificationMode::Chc)
    );
    assert_eq!(
        contract.verification_mode.verifier_suite(),
        contract.verifier_suite
    );
    assert_eq!(
        contract.required_artifact_kinds,
        PETRI_SUCCESSOR_TRUST_MC_CHC_PRODUCTION_ACCEPTANCE_REQUIRED_ARTIFACT_KINDS
    );
    assert_eq!(
        contract.optional_artifact_kinds,
        PETRI_SUCCESSOR_TRUST_MC_CHC_PRODUCTION_ACCEPTANCE_OPTIONAL_ARTIFACT_KINDS
    );
    assert_eq!(
        contract.required_artifact_requirements,
        PETRI_SUCCESSOR_TRUST_MC_CHC_PRODUCTION_ACCEPTANCE_REQUIRED_ARTIFACT_REQUIREMENTS
    );
    assert!(contract.production_requires_emitted_solver_artifacts);
    assert!(contract.requires_solver_acceptance);
    assert_eq!(
        contract.model_acceptance_report_api_name,
        PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_ACCEPTANCE_REPORT_API_NAME
    );
    assert_eq!(
        contract.consumer_acceptance_api_name,
        PETRI_SUCCESSOR_TRUST_MC_CHC_CONSUMER_ACCEPTANCE_API_NAME
    );
    assert_eq!(
        contract.production_acceptance_owner_suite,
        NativeVerifierSuite::AY
    );
    assert_eq!(
        contract.solver_evidence_descriptor,
        PETRI_SUCCESSOR_TRUST_MC_CHC_SOLVER_EVIDENCE_DESCRIPTOR
    );
    assert_eq!(
        contract.production_acceptance_report_api_name(),
        contract.model_acceptance_report_api_name
    );
    assert_eq!(
        contract.production_consumer_acceptance_api_name(),
        contract.consumer_acceptance_api_name
    );
    assert_eq!(
        contract.production_acceptance_owner_suite(),
        contract.production_acceptance_owner_suite
    );
    assert_eq!(
        contract.production_acceptance_requires_solver(),
        contract.requires_solver_acceptance
    );
    assert_eq!(
        contract.production_required_artifact_requirements(),
        contract.required_artifact_requirements
    );
    assert_eq!(
        contract.production_requires_emitted_solver_artifacts(),
        contract.production_requires_emitted_solver_artifacts
    );
    assert_eq!(
        contract.production_solver_evidence_descriptor(),
        contract.solver_evidence_descriptor
    );
    assert_eq!(
        contract.production_solver_capability_descriptor_schema(),
        AY_SOLVER_CAPABILITY_DESCRIPTOR_SCHEMA
    );
    assert_eq!(
        contract.production_model_blocking_clause_schema(),
        AY_MODEL_BLOCKING_CLAUSE_SCHEMA
    );
    assert_eq!(
        contract.production_model_blocking_clause_evidence_schema(),
        AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA
    );
    assert_eq!(
        contract.production_solve_decision_profile_model_consumer_schema(),
        AY_SOLVE_DECISION_PROFILE_MODEL_CONSUMER_SCHEMA
    );
}

#[test]
fn petri_successor_trust_mc_chc_descriptor_derives_shared_promotion_gates() {
    let descriptor = petri_successor_trust_mc_chc_contract_descriptor();
    let promotion = descriptor.shared_primitive_contract;

    assert_eq!(promotion.contract_schema, descriptor.schema);
    assert_eq!(promotion.contract_schema_version, descriptor.schema_version);
    assert_eq!(promotion.formula_schema, descriptor.formula_schema);
    assert_eq!(
        promotion.readiness_report_schema,
        descriptor.model_validation_readiness_report_schema
    );
    assert_eq!(
        promotion.readiness_report_schema_version,
        descriptor.model_validation_readiness_report_schema_version
    );
    assert_eq!(promotion.verifier_suite, descriptor.verifier_suite);
    assert_eq!(
        promotion.verification_mode,
        NativeSharedPrimitiveVerificationMode::TrustMc(descriptor.verification_mode)
    );
    assert_eq!(
        promotion.verification_mode.verifier_suite(),
        promotion.verifier_suite
    );
    assert_eq!(
        promotion.required_artifact_kinds,
        descriptor.production_acceptance_required_artifact_kinds
    );
    assert_eq!(
        promotion.required_artifact_requirements,
        PETRI_SUCCESSOR_TRUST_MC_CHC_PRODUCTION_ACCEPTANCE_REQUIRED_ARTIFACT_REQUIREMENTS
    );
    assert!(promotion.production_requires_emitted_solver_artifacts);
    assert_eq!(
        promotion.required_artifact_kinds,
        &[
            NativeEvidenceArtifactKind::TrustMcHornClauses,
            NativeEvidenceArtifactKind::ReplayTranscript,
            NativeEvidenceArtifactKind::TrustMcModel,
        ]
    );
    assert_eq!(
        promotion.requires_solver_acceptance,
        descriptor.model_validation_requires_solver_acceptance
    );
    assert!(promotion.requires_solver_acceptance);
    assert_eq!(
        promotion.model_acceptance_report_api_name,
        descriptor.model_acceptance_report_api_name
    );
    assert_eq!(
        promotion.consumer_acceptance_api_name,
        descriptor.consumer_acceptance_api_name
    );
    assert_eq!(
        promotion.production_acceptance_owner_suite,
        descriptor.production_acceptance_owner_suite
    );
    assert_eq!(
        promotion.production_acceptance_owner_suite,
        NativeVerifierSuite::AY
    );
    assert_eq!(
        promotion.solver_evidence_descriptor,
        PETRI_SUCCESSOR_TRUST_MC_CHC_SOLVER_EVIDENCE_DESCRIPTOR
    );
}

#[test]
fn native_shared_primitive_contract_names_ay_owned_solver_evidence() {
    let contract = petri_successor_trust_mc_chc_shared_primitive_contract_descriptor();
    let solver = contract.production_solver_evidence_descriptor();

    assert_eq!(solver.owner_suite, NativeVerifierSuite::AY);
    assert_eq!(
        solver.solver_capability_descriptor_schema,
        AY_SOLVER_CAPABILITY_DESCRIPTOR_SCHEMA
    );
    assert_eq!(
        solver.solver_capability_descriptor_schema_version,
        AY_SOLVER_CAPABILITY_DESCRIPTOR_SCHEMA_VERSION
    );
    assert_eq!(
        solver.capability_descriptor_schema(),
        "ay.solver-capability-descriptor.v1"
    );
    assert_eq!(
        solver.model_blocking_clause_schema(),
        AY_MODEL_BLOCKING_CLAUSE_SCHEMA
    );
    assert_eq!(
        solver.model_blocking_clause_schema_version,
        AY_MODEL_BLOCKING_CLAUSE_SCHEMA_VERSION
    );
    assert_eq!(
        solver.model_blocking_clause_evidence_schema(),
        AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA
    );
    assert_eq!(
        solver.model_blocking_clause_evidence_schema_version,
        AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA_VERSION
    );
    assert_eq!(
        solver.solve_decision_profile_model_consumer_schema(),
        AY_SOLVE_DECISION_PROFILE_MODEL_CONSUMER_SCHEMA
    );
    assert_eq!(
        solver.solve_decision_profile_model_consumer_schema_version,
        AY_SOLVE_DECISION_PROFILE_MODEL_CONSUMER_SCHEMA_VERSION
    );
    assert_eq!(
        solver.acceptance_api_names(),
        (
            PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_ACCEPTANCE_REPORT_API_NAME,
            PETRI_SUCCESSOR_TRUST_MC_CHC_CONSUMER_ACCEPTANCE_API_NAME
        )
    );
}

#[test]
fn petri_native_verification_bundle_handoff_manifest_rows_are_downstream_ready() {
    let descriptor = petri_native_verification_bundle_handoff_descriptor();
    let rows = descriptor.manifest_rows();
    let value = |key: &str| {
        rows.iter()
            .find(|row| row.key == key)
            .map(|row| row.value.as_str())
    };
    let values_for = |prefix: &str| {
        rows.iter()
            .filter(|row| row.key.starts_with(prefix))
            .map(|row| row.value.as_str())
            .collect::<Vec<_>>()
    };

    assert_eq!(
        value("handoff.schema"),
        Some(PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SCHEMA)
    );
    assert_eq!(value("handoff.schema_version"), Some("2"));
    assert_eq!(value("source.package"), Some("trust-ir"));
    assert_eq!(
        value("bundle_identity.schema"),
        Some(NATIVE_BUNDLE_IDENTITY_CONTRACT_SCHEMA)
    );
    let expected_bundle_schema_version = NATIVE_VERIFICATION_BUNDLE_SCHEMA_VERSION.to_string();
    assert_eq!(
        value("bundle_identity.bundle_schema_version"),
        Some(expected_bundle_schema_version.as_str())
    );
    assert_eq!(
        value("bundle_identity.transport_identity.schema"),
        Some(NATIVE_TRANSPORT_IDENTITY_SCHEMA)
    );
    assert_eq!(
        value("artifact_authority.schema"),
        Some(NATIVE_EVIDENCE_ARTIFACT_AUTHORITY_ROW_SCHEMA)
    );
    assert_eq!(
        value("shared_primitive_contract.production.requires_solver_acceptance"),
        Some("true")
    );
    assert_eq!(
        value("shared_primitive_contract.production.acceptance_owner_suite"),
        Some("ay")
    );
    assert_eq!(
        value("shared_primitive_contract.production.solver_evidence.capability_descriptor.schema"),
        Some(AY_SOLVER_CAPABILITY_DESCRIPTOR_SCHEMA)
    );
    assert_eq!(
        value("solver_evidence.capability_descriptor.schema"),
        Some(AY_SOLVER_CAPABILITY_DESCRIPTOR_SCHEMA)
    );
    assert_eq!(
        value("solver_evidence.model_blocking_clause.schema"),
        Some(AY_MODEL_BLOCKING_CLAUSE_SCHEMA)
    );
    assert_eq!(
        value("solver_evidence.model_blocking_clause_evidence.schema"),
        Some(AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA)
    );
    assert_eq!(
        value("solver_evidence.solve_decision_profile_model_consumer.schema"),
        Some(AY_SOLVE_DECISION_PROFILE_MODEL_CONSUMER_SCHEMA)
    );
    assert_eq!(
        value("solver_evidence.acceptance_report_api"),
        Some(PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_ACCEPTANCE_REPORT_API_NAME)
    );
    assert_eq!(
        value("solver_evidence.consumer_acceptance_api"),
        Some(PETRI_SUCCESSOR_TRUST_MC_CHC_CONSUMER_ACCEPTANCE_API_NAME)
    );

    let bundle_fields = values_for("bundle_identity.expected_field.");
    for field in [
        "NativeVerificationBundle::transport_identity()",
        "NativeTransportIdentity::request_digests",
        "NativeTransportIdentity::evidence_digests",
        "NativeVerificationBundle::evidence_bundle_for_request()",
        "NativeVerificationBundle::resolve_evidence_artifact_attachment()",
        "NativeVerificationBundle::resolve_evidence_artifact_attachments_for_kinds()",
    ] {
        assert!(
            bundle_fields.contains(&field),
            "handoff manifest missing expected bundle field {field}"
        );
    }

    let authority_report_keys = values_for("artifact_authority.report_key.");
    for key in [
        "artifact_authority.schema",
        "artifact_resolution.schema",
        "request.id",
        "artifact.kind",
        "authority",
        "status",
        "reason",
        "report.fail_closed",
    ] {
        assert!(
            authority_report_keys.contains(&key),
            "handoff manifest missing authority report key {key}"
        );
    }
    let authority_resolution_keys = values_for("artifact_authority.resolution_key.");
    for key in [
        "resolution.bytes_present",
        "resolution.is_authoritative",
        "resolution.fail_closed",
        "resolution.authoritative_bytes_available",
    ] {
        assert!(
            authority_resolution_keys.contains(&key),
            "handoff manifest missing authority resolution key {key}"
        );
    }

    let responsibilities = values_for("downstream.consumer_responsibility.");
    assert!(responsibilities.contains(&"call_AY_acceptance_API_before_production_selection"));
    assert!(responsibilities.contains(&"do_not_reconstruct_AY_solver_logic_downstream"));
    assert!(
        responsibilities.contains(&"preserve_fail_closed_status_when_required_rows_are_missing")
    );

    let lines = descriptor.manifest_key_value_lines();
    assert_eq!(lines.len(), rows.len());
    assert_eq!(
        lines.first().map(String::as_str),
        Some("handoff.schema=trust_ir.native.petri_successor.bundle_solver_evidence_handoff.v2")
    );
    assert!(lines.iter().any(|line| line
        == "solver_evidence.capability_descriptor.schema=ay.solver-capability-descriptor.v1"));
}

#[test]
fn petri_native_verification_bundle_handoff_normalized_rows_are_direct_sidecar_rows() {
    let descriptor = petri_native_verification_bundle_handoff_descriptor();
    let manifest_rows = descriptor.manifest_rows();
    let normalized_rows = descriptor.normalized_rows();

    assert_eq!(normalized_rows.len(), manifest_rows.len());
    assert_eq!(normalized_rows, descriptor.normalized_rows());
    assert_eq!(
        normalized_rows
            .iter()
            .map(|row| (row.key.as_str(), row.value.as_str()))
            .collect::<Vec<_>>(),
        manifest_rows
            .iter()
            .map(|row| (row.key.as_str(), row.value.as_str()))
            .collect::<Vec<_>>()
    );

    let row = |key: &str| {
        normalized_rows
            .iter()
            .find(|row| row.key == key)
            .unwrap_or_else(|| panic!("missing normalized handoff row {key}"))
    };

    assert_eq!(
        row("handoff.schema").row_kind,
        PetriNativeVerificationBundleHandoffRowKind::Descriptor
    );
    assert_eq!(row("handoff.schema").row_kind_code, "descriptor");
    assert_eq!(
        row("source.package").row_kind,
        PetriNativeVerificationBundleHandoffRowKind::Source
    );
    assert_eq!(
        row("bundle_identity.expected_field.0").row_kind,
        PetriNativeVerificationBundleHandoffRowKind::BundleIdentity
    );
    assert_eq!(
        row("artifact_authority.report_key.0").row_kind,
        PetriNativeVerificationBundleHandoffRowKind::ArtifactAuthority
    );
    assert_eq!(
        row("shared_primitive_contract.production.requires_solver_acceptance").row_kind,
        PetriNativeVerificationBundleHandoffRowKind::SharedPrimitiveContract
    );
    assert_eq!(
        row("solver_evidence.capability_descriptor.schema").row_kind,
        PetriNativeVerificationBundleHandoffRowKind::SolverEvidence
    );
    assert_eq!(
        row("downstream.consumer_responsibility.0").row_kind,
        PetriNativeVerificationBundleHandoffRowKind::DownstreamResponsibility
    );

    let row_kinds: Vec<_> = normalized_rows
        .iter()
        .map(|row| row.row_kind_code)
        .collect();
    for row_kind in [
        "descriptor",
        "source",
        "bundle_identity",
        "artifact_authority",
        "shared_primitive_contract",
        "solver_evidence",
        "downstream_responsibility",
    ] {
        assert!(
            row_kinds.contains(&row_kind),
            "missing normalized row kind {row_kind}"
        );
    }
    assert!(
        !row_kinds.contains(&"other"),
        "current handoff rows should all have explicit row kinds"
    );

    let lines = descriptor.normalized_key_value_lines();
    assert_eq!(lines.len(), normalized_rows.len());
    assert_eq!(lines, descriptor.normalized_key_value_lines());
    assert_eq!(
        lines.first().map(String::as_str),
        Some(
            "row_kind=descriptor\tkey=handoff.schema\tvalue=trust_ir.native.petri_successor.bundle_solver_evidence_handoff.v2"
        )
    );
    assert!(lines.iter().any(|line| line
            == "row_kind=solver_evidence\tkey=solver_evidence.capability_descriptor.schema\tvalue=ay.solver-capability-descriptor.v1"));

    let escaped = PetriNativeVerificationBundleHandoffRow::new(
        PetriNativeVerificationBundleHandoffRowKind::Source,
        "source=a",
        "line\n\ttab\\x=y\r\0",
    );
    assert_eq!(escaped.escaped_key(), "source\\=a");
    assert_eq!(escaped.escaped_value(), "line\\n\\ttab\\\\x\\=y\\r\\u{0}");
    assert_eq!(
        escaped.to_normalized_line(),
        "row_kind=source\tkey=source\\=a\tvalue=line\\n\\ttab\\\\x\\=y\\r\\u{0}"
    );
}

#[test]
fn petri_native_verification_bundle_handoff_completeness_accepts_descriptor_rows() {
    let descriptor = petri_native_verification_bundle_handoff_descriptor();
    let normalized_rows = descriptor.normalized_rows();
    let required_rows = descriptor.required_normalized_rows();
    let report = descriptor.validate_normalized_rows(&normalized_rows);

    assert_eq!(required_rows, descriptor.required_normalized_rows());
    assert_eq!(required_rows.len(), normalized_rows.len());
    assert_eq!(report.required_rows, required_rows);
    assert_eq!(
        report.status,
        PetriNativeVerificationBundleHandoffCompletenessStatus::Complete
    );
    assert_eq!(report.status_code, "complete");
    assert!(report.is_complete());
    assert!(!report.fail_closed());
    assert!(report.missing_rows.is_empty());
    assert!(report.missing_row_kinds.is_empty());
    assert_eq!(report.required_row_count, normalized_rows.len());
    assert_eq!(report.present_required_row_count, normalized_rows.len());

    let required_key = |key: &str| {
        required_rows
            .iter()
            .filter(|row| row.key == key)
            .collect::<Vec<_>>()
    };
    assert_eq!(
        required_key("handoff.schema")[0].row_kind,
        PetriNativeVerificationBundleHandoffRowKind::Descriptor
    );
    assert_eq!(
        required_key("bundle_identity.expected_field.0")[0].row_kind,
        PetriNativeVerificationBundleHandoffRowKind::BundleIdentity
    );
    assert_eq!(
        required_key("artifact_authority.report_key.0")[0].row_kind,
        PetriNativeVerificationBundleHandoffRowKind::ArtifactAuthority
    );
    assert_eq!(
        required_key("solver_evidence.capability_descriptor.schema")[0].row_kind,
        PetriNativeVerificationBundleHandoffRowKind::SolverEvidence
    );
    assert_eq!(
        required_key("downstream.consumer_responsibility.0")[0].row_kind,
        PetriNativeVerificationBundleHandoffRowKind::DownstreamResponsibility
    );

    let artifact_role_ordinals: Vec<_> =
        required_key("shared_primitive_contract.production.artifact_role")
            .into_iter()
            .map(|row| row.ordinal)
            .collect();
    assert_eq!(artifact_role_ordinals, vec![0, 1, 2]);
}

#[test]
fn petri_native_verification_bundle_handoff_completeness_fails_closed_on_missing_rows() {
    let descriptor = petri_native_verification_bundle_handoff_descriptor();
    let incomplete_rows: Vec<_> = descriptor
        .normalized_rows()
        .into_iter()
        .filter(|row| {
            !matches!(
                row.key.as_str(),
                "bundle_identity.schema"
                    | "solver_evidence.capability_descriptor.schema"
                    | "downstream.consumer_responsibility.0"
            )
        })
        .collect();

    let report = descriptor.validate_normalized_rows(&incomplete_rows);

    assert_eq!(
        report.status,
        PetriNativeVerificationBundleHandoffCompletenessStatus::Incomplete
    );
    assert_eq!(report.status_code, "incomplete");
    assert!(!report.is_complete());
    assert!(report.fail_closed());
    assert_eq!(
        report.present_required_row_count + report.missing_rows.len(),
        report.required_row_count
    );

    let missing_keys: Vec<_> = report
        .missing_rows
        .iter()
        .map(|row| (row.row_kind, row.key.as_str(), row.ordinal))
        .collect();
    assert_eq!(
        missing_keys,
        vec![
            (
                PetriNativeVerificationBundleHandoffRowKind::BundleIdentity,
                "bundle_identity.schema",
                0,
            ),
            (
                PetriNativeVerificationBundleHandoffRowKind::SolverEvidence,
                "solver_evidence.capability_descriptor.schema",
                0,
            ),
            (
                PetriNativeVerificationBundleHandoffRowKind::DownstreamResponsibility,
                "downstream.consumer_responsibility.0",
                0,
            ),
        ]
    );
    assert_eq!(
        report.missing_row_kinds,
        vec![
            PetriNativeVerificationBundleHandoffRowKind::BundleIdentity,
            PetriNativeVerificationBundleHandoffRowKind::SolverEvidence,
            PetriNativeVerificationBundleHandoffRowKind::DownstreamResponsibility,
        ]
    );

    let required_keys: Vec<_> = report
        .required_rows
        .iter()
        .map(|row| row.key.as_str())
        .collect();
    assert!(required_keys.contains(&"handoff.schema"));
    assert!(required_keys.contains(&"bundle_identity.schema"));
    assert!(required_keys.contains(&"artifact_authority.report_key.0"));
    assert!(required_keys.contains(&"solver_evidence.capability_descriptor.schema"));
    assert!(required_keys.contains(&"downstream.consumer_responsibility.0"));
}

#[test]
fn petri_native_verification_bundle_handoff_manifest_identity_is_deterministic() {
    let descriptor = petri_native_verification_bundle_handoff_descriptor();
    let normalized_rows = descriptor.normalized_rows();
    let mut reversed_rows = normalized_rows.clone();
    reversed_rows.reverse();

    let identity = descriptor.manifest_identity();
    let repeated_identity = descriptor.manifest_identity();
    let reversed_identity = descriptor.manifest_identity_for_rows(&reversed_rows);

    assert_eq!(identity, repeated_identity);
    assert_eq!(identity, reversed_identity);
    assert_eq!(
        identity.canonical_text,
        descriptor.canonical_manifest_text()
    );
    assert_eq!(
        identity.canonical_text,
        descriptor.canonical_manifest_text_for_rows(&normalized_rows)
    );
    assert_eq!(
        identity.schema,
        PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_SCHEMA
    );
    assert_eq!(
        identity.schema_version,
        PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_SCHEMA_VERSION
    );
    assert_eq!(
        identity.digest_context,
        PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_DIGEST_CONTEXT
    );
    assert_eq!(identity.descriptor_schema, descriptor.schema);
    assert_eq!(
        identity.descriptor_schema_version,
        descriptor.schema_version
    );
    assert_eq!(identity.source_package, descriptor.source_package);
    assert_eq!(
        identity.source_package_version,
        descriptor.source_package_version
    );
    assert_eq!(identity.digest_algorithm, ProofDigestAlgorithm::Sha256);
    assert_eq!(
        identity.digest,
        ProofDigest::sha256_domain(
            PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_DIGEST_CONTEXT,
            identity.canonical_text.as_bytes(),
        )
    );
    assert!(identity.is_complete());
    assert!(!identity.fail_closed());
    assert_eq!(
        identity.completeness_status,
        PetriNativeVerificationBundleHandoffCompletenessStatus::Complete
    );
    assert_eq!(identity.completeness_status_code, "complete");
    assert_eq!(identity.observed_row_count, normalized_rows.len());
    assert_eq!(identity.required_row_count, normalized_rows.len());
    assert_eq!(identity.present_required_row_count, normalized_rows.len());
    assert_eq!(identity.missing_row_count, 0);
    assert_eq!(identity.extra_row_count, 0);

    assert!(identity.canonical_text.ends_with('\n'));
    assert!(identity.canonical_text.contains(
            "identity.schema=trust_ir.native.petri_successor.bundle_solver_evidence_handoff.manifest_identity.v2\n"
        ));
    assert!(identity.canonical_text.contains(
        "descriptor.schema=trust_ir.native.petri_successor.bundle_solver_evidence_handoff.v2\n"
    ));
    assert!(
        identity
            .canonical_text
            .contains("completeness.status=complete\n")
    );
    assert!(identity.canonical_text.contains("rows.extra_count=0\n"));
    assert!(
        identity
            .canonical_text
            .contains("required.0.row_kind=descriptor\n")
    );
    assert!(
        identity
            .canonical_text
            .contains("required.0.key=handoff.schema\n")
    );
    assert!(identity.canonical_text.contains("required.0.ordinal=0\n"));
    assert!(
        identity
            .canonical_text
            .contains("row.0.row_kind=descriptor\n")
    );
    assert!(
        identity
            .canonical_text
            .contains("row.0.key=handoff.schema\n")
    );
    assert!(identity.canonical_text.contains("row.0.ordinal=0\n"));
    assert!(identity.canonical_text.contains(
        "row.0.value=trust_ir.native.petri_successor.bundle_solver_evidence_handoff.v2\n"
    ));
}

#[test]
fn petri_native_verification_bundle_handoff_manifest_identity_changes_when_row_missing() {
    let descriptor = petri_native_verification_bundle_handoff_descriptor();
    let complete_identity = descriptor.manifest_identity();
    let incomplete_rows: Vec<_> = descriptor
        .normalized_rows()
        .into_iter()
        .filter(|row| row.key != "solver_evidence.capability_descriptor.schema")
        .collect();

    let report = descriptor.validate_normalized_rows(&incomplete_rows);
    let incomplete_identity = descriptor.manifest_identity_for_rows(&incomplete_rows);

    assert_eq!(
        report.status,
        PetriNativeVerificationBundleHandoffCompletenessStatus::Incomplete
    );
    assert!(incomplete_identity.fail_closed());
    assert_eq!(
        incomplete_identity.completeness_status,
        PetriNativeVerificationBundleHandoffCompletenessStatus::Incomplete
    );
    assert_eq!(incomplete_identity.completeness_status_code, "incomplete");
    assert_eq!(
        incomplete_identity.observed_row_count,
        complete_identity.observed_row_count - 1
    );
    assert_eq!(
        incomplete_identity.required_row_count,
        complete_identity.required_row_count
    );
    assert_eq!(
        incomplete_identity.present_required_row_count,
        complete_identity.present_required_row_count - 1
    );
    assert_eq!(incomplete_identity.missing_row_count, 1);
    assert_eq!(incomplete_identity.extra_row_count, 0);
    assert_ne!(complete_identity.digest, incomplete_identity.digest);
    assert_ne!(
        complete_identity.canonical_text,
        incomplete_identity.canonical_text
    );
    assert_eq!(
        incomplete_identity.digest,
        ProofDigest::sha256_domain(
            PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_DIGEST_CONTEXT,
            incomplete_identity.canonical_text.as_bytes(),
        )
    );
    assert_eq!(
        incomplete_identity.canonical_text,
        descriptor.canonical_manifest_text_for_rows(&incomplete_rows)
    );
    assert!(
        incomplete_identity
            .canonical_text
            .contains("completeness.status=incomplete\n")
    );
    assert!(
        incomplete_identity
            .canonical_text
            .contains("rows.missing_count=1\n")
    );
    assert!(
        incomplete_identity
            .canonical_text
            .contains("missing.0.row_kind=solver_evidence\n")
    );
    assert!(
        incomplete_identity
            .canonical_text
            .contains("missing.0.key=solver_evidence.capability_descriptor.schema\n")
    );
    assert!(
        incomplete_identity
            .canonical_text
            .contains("missing.0.ordinal=0\n")
    );
}

#[test]
fn petri_native_verification_bundle_handoff_manifest_identity_key_values_are_persistable() {
    let descriptor = petri_native_verification_bundle_handoff_descriptor();
    let identity = descriptor.manifest_identity();
    let rows = identity.key_value_rows();
    let lines = identity.key_value_lines();
    let text = identity.key_value_text();
    let digest_text = identity.digest.to_string();
    let observed_row_count = identity.observed_row_count.to_string();
    let required_row_count = identity.required_row_count.to_string();
    let present_required_row_count = identity.present_required_row_count.to_string();
    let value = |key: &str| {
        rows.iter()
            .find(|row| row.key == key)
            .map(|row| row.value.as_str())
    };

    assert_eq!(rows, identity.key_value_rows());
    assert_eq!(lines, identity.key_value_lines());
    assert_eq!(text, identity.key_value_text());
    assert_eq!(lines.len(), rows.len());
    assert_eq!(text, format!("{}\n", lines.join("\n")));

    assert_eq!(
        value("manifest_identity.schema"),
        Some(PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_SCHEMA)
    );
    assert_eq!(value("manifest_identity.schema_version"), Some("2"));
    assert_eq!(
        value("manifest_identity.descriptor.schema"),
        Some(PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SCHEMA)
    );
    assert_eq!(
        value("manifest_identity.descriptor.schema_version"),
        Some("2")
    );
    assert_eq!(value("manifest_identity.source.package"), Some("trust-ir"));
    assert_eq!(
        value("manifest_identity.digest.context"),
        Some(PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_DIGEST_CONTEXT)
    );
    assert_eq!(value("manifest_identity.digest.algorithm"), Some("sha256"));
    assert_eq!(
        value("manifest_identity.digest"),
        Some(digest_text.as_str())
    );
    assert_eq!(
        value("manifest_identity.completeness.status"),
        Some("complete")
    );
    assert_eq!(value("manifest_identity.fail_closed"), Some("false"));
    assert_eq!(
        value("manifest_identity.rows.observed_count"),
        Some(observed_row_count.as_str())
    );
    assert_eq!(
        value("manifest_identity.rows.required_count"),
        Some(required_row_count.as_str())
    );
    assert_eq!(
        value("manifest_identity.rows.present_required_count"),
        Some(present_required_row_count.as_str())
    );
    assert_eq!(value("manifest_identity.rows.missing_count"), Some("0"));
    assert_eq!(value("manifest_identity.rows.extra_count"), Some("0"));
    assert_eq!(value("manifest_identity.missing_row_kind_count"), Some("0"));
    assert!(identity.missing_rows.is_empty());
    assert!(identity.missing_row_kinds.is_empty());
    assert!(
        !rows
            .iter()
            .any(|row| row.key.starts_with("manifest_identity.missing_row."))
    );
    assert!(
        !rows
            .iter()
            .any(|row| row.key.starts_with("manifest_identity.missing_row_kind."))
    );

    let parsed: BTreeMap<_, _> = lines
        .iter()
        .map(|line| {
            line.split_once('=')
                .unwrap_or_else(|| panic!("malformed identity line {line}"))
        })
        .collect();
    assert_eq!(
        parsed.get("manifest_identity.digest").copied(),
        Some(digest_text.as_str())
    );
    assert_eq!(
        parsed.get("manifest_identity.completeness.status").copied(),
        Some("complete")
    );
    assert_eq!(
        parsed.get("manifest_identity.fail_closed").copied(),
        Some("false")
    );
}

#[test]
fn petri_native_verification_bundle_handoff_manifest_identity_key_values_preserve_missing_rows() {
    let descriptor = petri_native_verification_bundle_handoff_descriptor();
    let incomplete_rows: Vec<_> = descriptor
        .normalized_rows()
        .into_iter()
        .filter(|row| {
            !matches!(
                row.key.as_str(),
                "bundle_identity.schema" | "solver_evidence.capability_descriptor.schema"
            )
        })
        .collect();
    let identity = descriptor.manifest_identity_for_rows(&incomplete_rows);
    let rows = identity.key_value_rows();
    let lines = identity.key_value_lines();
    let text = identity.key_value_text();
    let value = |key: &str| {
        rows.iter()
            .find(|row| row.key == key)
            .map(|row| row.value.as_str())
    };

    assert!(identity.fail_closed());
    assert_eq!(
        identity.completeness_status,
        PetriNativeVerificationBundleHandoffCompletenessStatus::Incomplete
    );
    assert_eq!(identity.completeness_status_code, "incomplete");
    assert_eq!(identity.missing_row_count, 2);
    assert_eq!(
        identity
            .missing_rows
            .iter()
            .map(|row| (row.row_kind, row.key.as_str(), row.ordinal))
            .collect::<Vec<_>>(),
        vec![
            (
                PetriNativeVerificationBundleHandoffRowKind::BundleIdentity,
                "bundle_identity.schema",
                0,
            ),
            (
                PetriNativeVerificationBundleHandoffRowKind::SolverEvidence,
                "solver_evidence.capability_descriptor.schema",
                0,
            ),
        ]
    );
    assert_eq!(
        identity.missing_row_kinds,
        vec![
            PetriNativeVerificationBundleHandoffRowKind::BundleIdentity,
            PetriNativeVerificationBundleHandoffRowKind::SolverEvidence,
        ]
    );

    assert_eq!(
        value("manifest_identity.completeness.status"),
        Some("incomplete")
    );
    assert_eq!(value("manifest_identity.fail_closed"), Some("true"));
    assert_eq!(value("manifest_identity.rows.missing_count"), Some("2"));
    assert_eq!(value("manifest_identity.missing_row_kind_count"), Some("2"));
    assert_eq!(
        value("manifest_identity.missing_row_kind.0"),
        Some("bundle_identity")
    );
    assert_eq!(
        value("manifest_identity.missing_row_kind.1"),
        Some("solver_evidence")
    );
    assert_eq!(
        value("manifest_identity.missing_row.0.row_kind"),
        Some("bundle_identity")
    );
    assert_eq!(
        value("manifest_identity.missing_row.0.key"),
        Some("bundle_identity.schema")
    );
    assert_eq!(value("manifest_identity.missing_row.0.ordinal"), Some("0"));
    assert_eq!(
        value("manifest_identity.missing_row.1.row_kind"),
        Some("solver_evidence")
    );
    assert_eq!(
        value("manifest_identity.missing_row.1.key"),
        Some("solver_evidence.capability_descriptor.schema")
    );
    assert_eq!(value("manifest_identity.missing_row.1.ordinal"), Some("0"));

    assert_eq!(lines, identity.key_value_lines());
    assert_eq!(text, identity.key_value_text());
    assert_eq!(text, format!("{}\n", lines.join("\n")));
    assert!(text.contains("manifest_identity.fail_closed=true\n"));
    assert!(text.contains(
        "manifest_identity.missing_row.1.key=solver_evidence.capability_descriptor.schema\n"
    ));

    let parsed: BTreeMap<_, _> = lines
        .iter()
        .map(|line| {
            line.split_once('=')
                .unwrap_or_else(|| panic!("malformed identity line {line}"))
        })
        .collect();
    assert_eq!(
        parsed.get("manifest_identity.completeness.status").copied(),
        Some("incomplete")
    );
    assert_eq!(
        parsed.get("manifest_identity.missing_row.0.key").copied(),
        Some("bundle_identity.schema")
    );
    assert_eq!(
        parsed.get("manifest_identity.missing_row.1.key").copied(),
        Some("solver_evidence.capability_descriptor.schema")
    );
}

#[test]
fn petri_native_verification_bundle_handoff_manifest_identity_round_trips_healthy_rows() {
    let descriptor = petri_native_verification_bundle_handoff_descriptor();
    let identity = descriptor.manifest_identity();
    let rows = identity.key_value_rows();
    let lines = identity.key_value_lines();
    let report = identity.round_trip_report(&rows);
    let digest_text = identity.digest.to_string();

    assert_eq!(
        report.status,
        PetriNativeVerificationBundleHandoffManifestIdentityRoundTripStatus::Valid
    );
    assert_eq!(report.status_code, "valid");
    assert!(!report.fail_closed);
    assert_eq!(report.expected_row_count, rows.len());
    assert_eq!(report.observed_row_count, rows.len());
    assert_eq!(report.unique_key_count, rows.len());
    assert!(report.duplicate_keys.is_empty());
    assert!(report.missing_keys.is_empty());
    assert!(report.unexpected_keys.is_empty());
    assert!(report.mismatched_value_keys.is_empty());
    assert!(report.invalid_bool_keys.is_empty());
    assert!(report.invalid_usize_keys.is_empty());
    assert_eq!(
        report.reconstructed_schema.as_deref(),
        Some(PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_SCHEMA)
    );
    assert_eq!(
        report.reconstructed_schema_version,
        Some(PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_SCHEMA_VERSION as usize)
    );
    assert_eq!(
        report.reconstructed_digest_context.as_deref(),
        Some(PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_DIGEST_CONTEXT)
    );
    assert_eq!(
        report.reconstructed_digest.as_deref(),
        Some(digest_text.as_str())
    );
    assert_eq!(
        report.reconstructed_completeness_status_code.as_deref(),
        Some("complete")
    );
    assert_eq!(report.reconstructed_fail_closed, Some(false));
    assert_eq!(report.reconstructed_missing_row_count, Some(0));
    assert_eq!(report.reconstructed_missing_row_kind_count, Some(0));
    assert!(report.reconstructed_missing_row_kinds.is_empty());
    assert!(report.reconstructed_missing_rows.is_empty());

    let unique_keys = rows
        .iter()
        .map(|row| row.key.as_str())
        .collect::<BTreeSet<_>>();
    assert_eq!(unique_keys.len(), rows.len());
    assert_eq!(lines.len(), rows.len());
}

#[test]
fn petri_native_verification_bundle_handoff_manifest_identity_round_trips_incomplete_rows() {
    let fixture = petri_native_verification_bundle_handoff_incomplete_diagnostic_fixture();
    let identity = fixture.manifest_identity;
    let rows = identity.key_value_rows();
    let report = identity.round_trip_report(&rows);
    let digest_text = identity.digest.to_string();

    assert_eq!(
        report.status,
        PetriNativeVerificationBundleHandoffManifestIdentityRoundTripStatus::Valid
    );
    assert_eq!(report.status_code, "valid");
    assert!(report.fail_closed);
    assert_eq!(report.expected_row_count, rows.len());
    assert_eq!(report.observed_row_count, rows.len());
    assert_eq!(report.unique_key_count, rows.len());
    assert!(report.duplicate_keys.is_empty());
    assert!(report.missing_keys.is_empty());
    assert!(report.unexpected_keys.is_empty());
    assert!(report.mismatched_value_keys.is_empty());
    assert!(report.invalid_bool_keys.is_empty());
    assert!(report.invalid_usize_keys.is_empty());
    assert_eq!(
        report.reconstructed_schema.as_deref(),
        Some(PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_SCHEMA)
    );
    assert_eq!(
        report.reconstructed_digest_context.as_deref(),
        Some(PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_DIGEST_CONTEXT)
    );
    assert_eq!(
        report.reconstructed_digest.as_deref(),
        Some(digest_text.as_str())
    );
    assert_eq!(
        report.reconstructed_completeness_status_code.as_deref(),
        Some("incomplete")
    );
    assert_eq!(report.reconstructed_fail_closed, Some(true));
    assert_eq!(report.reconstructed_missing_row_count, Some(2));
    assert_eq!(report.reconstructed_missing_row_kind_count, Some(2));
    assert_eq!(
        report.reconstructed_missing_row_kinds,
        vec!["bundle_identity".to_string(), "solver_evidence".to_string()]
    );
    assert_eq!(
        report.reconstructed_missing_rows,
        vec![
            PetriNativeVerificationBundleHandoffManifestIdentityMissingRowDiagnostic {
                row_kind_code: "bundle_identity".to_string(),
                key: "bundle_identity.schema".to_string(),
                ordinal: 0,
            },
            PetriNativeVerificationBundleHandoffManifestIdentityMissingRowDiagnostic {
                row_kind_code: "solver_evidence".to_string(),
                key: "solver_evidence.capability_descriptor.schema".to_string(),
                ordinal: 0,
            },
        ]
    );
}

#[test]
fn petri_native_verification_bundle_handoff_contract_health_report_self_audits_default_surface() {
    let descriptor = petri_native_verification_bundle_handoff_descriptor();
    let manifest_rows = descriptor.manifest_rows();
    let normalized_rows = descriptor.normalized_rows();
    let required_rows = descriptor.required_normalized_rows();
    let completeness_report = descriptor.validate_normalized_rows(&normalized_rows);
    let manifest_identity = descriptor.manifest_identity();
    let identity_key_value_rows = manifest_identity.key_value_rows();
    let identity_key_value_lines = manifest_identity.key_value_lines();
    let identity_key_value_text = manifest_identity.key_value_text();
    let report = petri_native_verification_bundle_handoff_contract_health_report();

    assert_eq!(report, descriptor.contract_health_report());
    assert_eq!(
        report.status,
        PetriNativeVerificationBundleHandoffContractHealthStatus::Healthy
    );
    assert_eq!(report.status_code, "healthy");
    assert!(report.is_healthy());
    assert!(!report.fail_closed());
    assert!(report.schema_version_rows_agree);
    assert!(report.row_counts_agree);
    assert!(report.completeness_agrees);
    assert!(report.manifest_identity_digest_agrees);
    assert!(report.manifest_identity_key_values_agree);

    assert_eq!(report.descriptor_schema, descriptor.schema);
    assert_eq!(report.descriptor_schema_version, descriptor.schema_version);
    assert_eq!(
        report.manifest_identity_schema,
        PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_SCHEMA
    );
    assert_eq!(
        report.manifest_identity_schema_version,
        PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_SCHEMA_VERSION
    );

    assert_eq!(report.manifest_row_count, manifest_rows.len());
    assert_eq!(report.normalized_row_count, normalized_rows.len());
    assert_eq!(report.required_row_count, required_rows.len());
    assert_eq!(
        report.completeness_required_row_count,
        completeness_report.required_row_count
    );
    assert_eq!(
        report.completeness_present_required_row_count,
        completeness_report.present_required_row_count
    );
    assert_eq!(report.completeness_missing_row_count, 0);
    assert_eq!(
        report.manifest_identity_observed_row_count,
        manifest_identity.observed_row_count
    );
    assert_eq!(
        report.manifest_identity_required_row_count,
        manifest_identity.required_row_count
    );
    assert_eq!(
        report.manifest_identity_present_required_row_count,
        manifest_identity.present_required_row_count
    );
    assert_eq!(report.manifest_identity_missing_row_count, 0);
    assert_eq!(report.manifest_identity_extra_row_count, 0);
    assert_eq!(
        report.manifest_identity_key_value_row_count,
        identity_key_value_rows.len()
    );
    assert_eq!(
        report.manifest_identity_key_value_line_count,
        identity_key_value_lines.len()
    );
    assert_eq!(
        report.manifest_identity_key_value_text_line_count,
        identity_key_value_text.lines().count()
    );
    assert_eq!(
        report.manifest_identity_key_value_row_count,
        report.manifest_identity_key_value_line_count
    );
    assert_eq!(
        report.manifest_identity_key_value_line_count,
        report.manifest_identity_key_value_text_line_count
    );
    assert_eq!(report.manifest_identity_digest, manifest_identity.digest);

    assert_eq!(manifest_rows.len(), normalized_rows.len());
    assert_eq!(normalized_rows.len(), required_rows.len());
    assert_eq!(required_rows.len(), completeness_report.required_row_count);
    assert_eq!(
        completeness_report.required_row_count,
        completeness_report.present_required_row_count
    );
    assert_eq!(
        completeness_report.required_row_count,
        manifest_identity.required_row_count
    );
    assert_eq!(
        manifest_identity.required_row_count,
        manifest_identity.present_required_row_count
    );
    assert!(completeness_report.is_complete());
    assert!(manifest_identity.is_complete());
    assert_eq!(manifest_identity.missing_row_count, 0);
    assert_eq!(manifest_identity.extra_row_count, 0);
    assert!(manifest_identity.missing_rows.is_empty());
    assert!(manifest_identity.missing_row_kinds.is_empty());

    let identity_values: BTreeMap<_, _> = identity_key_value_lines
        .iter()
        .map(|line| {
            line.split_once('=')
                .unwrap_or_else(|| panic!("malformed identity line {line}"))
        })
        .collect();
    let digest_text = report.manifest_identity_digest.to_string();
    let required_row_count = report.required_row_count.to_string();
    let observed_row_count = report.manifest_identity_observed_row_count.to_string();
    let present_required_row_count = report
        .manifest_identity_present_required_row_count
        .to_string();

    assert_eq!(
        identity_values
            .get("manifest_identity.descriptor.schema")
            .copied(),
        Some(PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SCHEMA)
    );
    assert_eq!(
        identity_values
            .get("manifest_identity.descriptor.schema_version")
            .copied(),
        Some("2")
    );
    assert_eq!(
        identity_values.get("manifest_identity.schema").copied(),
        Some(PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_SCHEMA)
    );
    assert_eq!(
        identity_values
            .get("manifest_identity.schema_version")
            .copied(),
        Some("2")
    );
    assert_eq!(
        identity_values.get("manifest_identity.digest").copied(),
        Some(digest_text.as_str())
    );
    assert_eq!(
        identity_values
            .get("manifest_identity.completeness.status")
            .copied(),
        Some("complete")
    );
    assert_eq!(
        identity_values
            .get("manifest_identity.fail_closed")
            .copied(),
        Some("false")
    );
    assert_eq!(
        identity_values
            .get("manifest_identity.rows.observed_count")
            .copied(),
        Some(observed_row_count.as_str())
    );
    assert_eq!(
        identity_values
            .get("manifest_identity.rows.required_count")
            .copied(),
        Some(required_row_count.as_str())
    );
    assert_eq!(
        identity_values
            .get("manifest_identity.rows.present_required_count")
            .copied(),
        Some(present_required_row_count.as_str())
    );
    assert_eq!(
        identity_values
            .get("manifest_identity.rows.missing_count")
            .copied(),
        Some("0")
    );
    assert_eq!(
        identity_values
            .get("manifest_identity.rows.extra_count")
            .copied(),
        Some("0")
    );
}

#[test]
fn petri_native_verification_bundle_handoff_contract_health_report_key_values_are_persistable() {
    let report = petri_native_verification_bundle_handoff_contract_health_report();
    let rows = report.key_value_rows();
    let lines = report.key_value_lines();
    let text = report.key_value_text();
    let digest_text = report.manifest_identity_digest.to_string();
    let manifest_row_count = report.manifest_row_count.to_string();
    let normalized_row_count = report.normalized_row_count.to_string();
    let required_row_count = report.required_row_count.to_string();
    let completeness_required_row_count = report.completeness_required_row_count.to_string();
    let completeness_present_required_row_count =
        report.completeness_present_required_row_count.to_string();
    let completeness_missing_row_count = report.completeness_missing_row_count.to_string();
    let manifest_identity_observed_row_count =
        report.manifest_identity_observed_row_count.to_string();
    let manifest_identity_required_row_count =
        report.manifest_identity_required_row_count.to_string();
    let manifest_identity_present_required_row_count = report
        .manifest_identity_present_required_row_count
        .to_string();
    let manifest_identity_missing_row_count =
        report.manifest_identity_missing_row_count.to_string();
    let manifest_identity_extra_row_count = report.manifest_identity_extra_row_count.to_string();
    let identity_key_value_row_count = report.manifest_identity_key_value_row_count.to_string();
    let identity_key_value_line_count = report.manifest_identity_key_value_line_count.to_string();
    let identity_key_value_text_line_count = report
        .manifest_identity_key_value_text_line_count
        .to_string();
    let value = |key: &str| {
        rows.iter()
            .find(|row| row.key == key)
            .map(|row| row.value.as_str())
    };

    assert_eq!(rows, report.key_value_rows());
    assert_eq!(lines, report.key_value_lines());
    assert_eq!(text, report.key_value_text());
    assert_eq!(lines.len(), rows.len());
    assert_eq!(text, format!("{}\n", lines.join("\n")));
    assert!(report.is_healthy());
    assert!(!report.fail_closed());

    assert_eq!(value("contract_health.status"), Some("healthy"));
    assert_eq!(value("contract_health.fail_closed"), Some("false"));
    assert_eq!(
        value("contract_health.descriptor.schema"),
        Some(PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SCHEMA)
    );
    assert_eq!(
        value("contract_health.descriptor.schema_version"),
        Some("2")
    );
    assert_eq!(
        value("contract_health.manifest_identity.schema"),
        Some(PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_SCHEMA)
    );
    assert_eq!(
        value("contract_health.manifest_identity.schema_version"),
        Some("2")
    );

    assert_eq!(
        value("contract_health.count.manifest_rows"),
        Some(manifest_row_count.as_str())
    );
    assert_eq!(
        value("contract_health.count.normalized_rows"),
        Some(normalized_row_count.as_str())
    );
    assert_eq!(
        value("contract_health.count.required_rows"),
        Some(required_row_count.as_str())
    );
    assert_eq!(
        value("contract_health.count.completeness.required_rows"),
        Some(completeness_required_row_count.as_str())
    );
    assert_eq!(
        value("contract_health.count.completeness.present_required_rows"),
        Some(completeness_present_required_row_count.as_str())
    );
    assert_eq!(
        value("contract_health.count.completeness.missing_rows"),
        Some(completeness_missing_row_count.as_str())
    );
    assert_eq!(
        value("contract_health.count.manifest_identity.observed_rows"),
        Some(manifest_identity_observed_row_count.as_str())
    );
    assert_eq!(
        value("contract_health.count.manifest_identity.required_rows"),
        Some(manifest_identity_required_row_count.as_str())
    );
    assert_eq!(
        value("contract_health.count.manifest_identity.present_required_rows"),
        Some(manifest_identity_present_required_row_count.as_str())
    );
    assert_eq!(
        value("contract_health.count.manifest_identity.missing_rows"),
        Some(manifest_identity_missing_row_count.as_str())
    );
    assert_eq!(
        value("contract_health.count.manifest_identity.extra_rows"),
        Some(manifest_identity_extra_row_count.as_str())
    );
    assert_eq!(
        value("contract_health.count.manifest_identity.key_value_rows"),
        Some(identity_key_value_row_count.as_str())
    );
    assert_eq!(
        value("contract_health.count.manifest_identity.key_value_lines"),
        Some(identity_key_value_line_count.as_str())
    );
    assert_eq!(
        value("contract_health.count.manifest_identity.key_value_text_lines"),
        Some(identity_key_value_text_line_count.as_str())
    );

    assert_eq!(
        value("contract_health.manifest_identity.digest"),
        Some(digest_text.as_str())
    );
    assert_eq!(
        value("contract_health.agreement.schema_version_rows"),
        Some("true")
    );
    assert_eq!(value("contract_health.agreement.row_counts"), Some("true"));
    assert_eq!(
        value("contract_health.agreement.completeness"),
        Some("true")
    );
    assert_eq!(
        value("contract_health.agreement.manifest_identity_digest"),
        Some("true")
    );
    assert_eq!(
        value("contract_health.agreement.manifest_identity_key_values"),
        Some("true")
    );

    let parsed: BTreeMap<_, _> = lines
        .iter()
        .map(|line| {
            line.split_once('=')
                .unwrap_or_else(|| panic!("malformed health line {line}"))
        })
        .collect();
    assert_eq!(
        parsed.get("contract_health.status").copied(),
        Some("healthy")
    );
    assert_eq!(
        parsed
            .get("contract_health.agreement.manifest_identity_digest")
            .copied(),
        Some("true")
    );
    assert_eq!(
        parsed
            .get("contract_health.count.manifest_identity.missing_rows")
            .copied(),
        Some("0")
    );
    assert_eq!(
        parsed
            .get("contract_health.count.completeness.missing_rows")
            .copied(),
        Some("0")
    );
}

#[test]
fn petri_native_verification_bundle_handoff_diagnostic_fixture_manifest_lists_both_fixtures() {
    let manifest = petri_native_verification_bundle_handoff_diagnostic_fixture_manifest();
    let repeated_manifest = petri_native_verification_bundle_handoff_diagnostic_fixture_manifest();
    let rows = manifest.key_value_rows();
    let lines = manifest.key_value_lines();
    let text = manifest.key_value_text();
    let values: BTreeMap<_, _> = rows
        .iter()
        .map(|row| (row.key.as_str(), row.value.as_str()))
        .collect();

    assert_eq!(manifest, repeated_manifest);
    assert_eq!(
        manifest.schema,
        PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_DIAGNOSTIC_FIXTURE_MANIFEST_SCHEMA
    );
    assert_eq!(
        manifest.schema_version,
        PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_DIAGNOSTIC_FIXTURE_MANIFEST_SCHEMA_VERSION
    );
    assert_eq!(
        manifest.source_package,
        PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SOURCE_PACKAGE
    );
    assert_eq!(
        manifest.source_package_version,
        PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SOURCE_PACKAGE_VERSION
    );
    assert_eq!(manifest.fixtures.len(), 2);
    assert_eq!(
        manifest
            .fixtures
            .iter()
            .map(|fixture| fixture.fixture_name)
            .collect::<Vec<_>>(),
        vec![
            PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_HEALTHY_DIAGNOSTIC_FIXTURE_NAME,
            PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_INCOMPLETE_DIAGNOSTIC_FIXTURE_NAME,
        ]
    );

    assert_eq!(lines, manifest.key_value_lines());
    assert_eq!(text, format!("{}\n", lines.join("\n")));
    assert_eq!(
        values.get("fixture_manifest.schema").copied(),
        Some(PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_DIAGNOSTIC_FIXTURE_MANIFEST_SCHEMA)
    );
    assert_eq!(
        values.get("fixture_manifest.schema_version").copied(),
        Some("2")
    );
    assert_eq!(
        values.get("fixture_manifest.fixture_count").copied(),
        Some("2")
    );
    assert_eq!(
        values.get("fixture_manifest.fixture.0.name").copied(),
        Some(PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_HEALTHY_DIAGNOSTIC_FIXTURE_NAME)
    );
    assert_eq!(
        values
            .get("fixture_manifest.fixture.0.expected.completeness_status")
            .copied(),
        Some("complete")
    );
    assert_eq!(
        values
            .get("fixture_manifest.fixture.0.expected.manifest_identity_status")
            .copied(),
        Some("complete")
    );
    assert_eq!(
        values
            .get("fixture_manifest.fixture.0.expected.contract_health_status")
            .copied(),
        Some("healthy")
    );
    assert_eq!(
        values
            .get("fixture_manifest.fixture.0.expected.accepted")
            .copied(),
        Some("true")
    );
    assert_eq!(
        values
            .get("fixture_manifest.fixture.0.expected.fail_closed")
            .copied(),
        Some("false")
    );
    assert_eq!(
        values.get("fixture_manifest.fixture.1.name").copied(),
        Some(PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_INCOMPLETE_DIAGNOSTIC_FIXTURE_NAME)
    );
    assert_eq!(
        values
            .get("fixture_manifest.fixture.1.expected.completeness_status")
            .copied(),
        Some("incomplete")
    );
    assert_eq!(
        values
            .get("fixture_manifest.fixture.1.expected.manifest_identity_status")
            .copied(),
        Some("incomplete")
    );
    assert_eq!(
        values
            .get("fixture_manifest.fixture.1.expected.contract_health_status")
            .copied(),
        Some("inconsistent")
    );
    assert_eq!(
        values
            .get("fixture_manifest.fixture.1.expected.accepted")
            .copied(),
        Some("false")
    );
    assert_eq!(
        values
            .get("fixture_manifest.fixture.1.expected.fail_closed")
            .copied(),
        Some("true")
    );
    for index in 0..manifest.fixtures.len() {
        assert_eq!(
            values
                .get(format!("fixture_manifest.fixture.{index}.schema.handoff").as_str())
                .copied(),
            Some(PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SCHEMA)
        );
        assert_eq!(
            values
                .get(format!("fixture_manifest.fixture.{index}.schema.handoff_version").as_str())
                .copied(),
            Some("2")
        );
        assert_eq!(
            values
                .get(format!("fixture_manifest.fixture.{index}.schema.manifest_identity").as_str())
                .copied(),
            Some(PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_SCHEMA)
        );
        assert_eq!(
            values
                .get(
                    format!("fixture_manifest.fixture.{index}.schema.manifest_identity_version")
                        .as_str()
                )
                .copied(),
            Some("2")
        );
    }
}

#[test]
fn petri_native_verification_bundle_handoff_diagnostic_fixture_manifest_matches_fixture_evidence() {
    let manifest = petri_native_verification_bundle_handoff_diagnostic_fixture_manifest();
    let healthy = petri_native_verification_bundle_handoff_healthy_diagnostic_fixture();
    let incomplete = petri_native_verification_bundle_handoff_incomplete_diagnostic_fixture();
    let healthy_entry = manifest
        .fixtures
        .iter()
        .find(|entry| {
            entry.fixture_name
                == PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_HEALTHY_DIAGNOSTIC_FIXTURE_NAME
        })
        .expect("healthy fixture manifest entry");
    let incomplete_entry = manifest
        .fixtures
        .iter()
        .find(|entry| {
            entry.fixture_name
                == PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_INCOMPLETE_DIAGNOSTIC_FIXTURE_NAME
        })
        .expect("incomplete fixture manifest entry");
    fn normalized_value<'a>(
        rows: &'a [PetriNativeVerificationBundleHandoffRow],
        key: &str,
    ) -> Option<&'a str> {
        rows.iter()
            .find(|row| row.key == key)
            .map(|row| row.value.as_str())
    }

    fn manifest_identity_value<'a>(
        rows: &'a [NativeSharedPrimitiveContractManifestRow],
        key: &str,
    ) -> Option<&'a str> {
        rows.iter()
            .find(|row| row.key == key)
            .map(|row| row.value.as_str())
    }

    assert_eq!(
        healthy_entry.expected_completeness_status_code,
        healthy.completeness_report.status_code
    );
    assert_eq!(
        healthy_entry.expected_manifest_identity_status_code,
        healthy.manifest_identity.completeness_status_code
    );
    assert_eq!(
        healthy_entry.expected_contract_health_status_code,
        healthy.contract_health_report.status_code
    );
    assert_eq!(healthy_entry.expected_accepted, healthy.accepted());
    assert_eq!(healthy_entry.expected_fail_closed, healthy.fail_closed());
    assert_eq!(
        healthy_entry.handoff_schema,
        normalized_value(&healthy.normalized_rows, "handoff.schema")
            .expect("healthy handoff schema row")
    );
    assert_eq!(
        healthy_entry.handoff_schema_version.to_string(),
        normalized_value(&healthy.normalized_rows, "handoff.schema_version")
            .expect("healthy handoff schema version row")
    );
    assert_eq!(
        healthy_entry.manifest_identity_schema,
        manifest_identity_value(&healthy.manifest_identity_rows, "manifest_identity.schema")
            .expect("healthy manifest identity schema row")
    );
    assert_eq!(
        healthy_entry.manifest_identity_schema_version.to_string(),
        manifest_identity_value(
            &healthy.manifest_identity_rows,
            "manifest_identity.schema_version"
        )
        .expect("healthy manifest identity schema version row")
    );

    assert_eq!(
        incomplete_entry.expected_completeness_status_code,
        incomplete.completeness_report.status_code
    );
    assert_eq!(
        incomplete_entry.expected_manifest_identity_status_code,
        incomplete.manifest_identity.completeness_status_code
    );
    assert_eq!(
        incomplete_entry.expected_contract_health_status_code,
        incomplete.contract_health_report.status_code
    );
    assert_eq!(
        incomplete_entry.expected_accepted,
        !incomplete.fail_closed()
    );
    assert_eq!(
        incomplete_entry.expected_fail_closed,
        incomplete.fail_closed()
    );
    assert_eq!(
        incomplete_entry.handoff_schema,
        normalized_value(&incomplete.normalized_rows, "handoff.schema")
            .expect("incomplete handoff schema row")
    );
    assert_eq!(
        incomplete_entry.handoff_schema_version.to_string(),
        normalized_value(&incomplete.normalized_rows, "handoff.schema_version")
            .expect("incomplete handoff schema version row")
    );
    assert_eq!(
        incomplete_entry.manifest_identity_schema,
        manifest_identity_value(
            &incomplete.manifest_identity.key_value_rows(),
            "manifest_identity.schema"
        )
        .expect("incomplete manifest identity schema row")
    );
    assert_eq!(
        incomplete_entry
            .manifest_identity_schema_version
            .to_string(),
        manifest_identity_value(
            &incomplete.manifest_identity.key_value_rows(),
            "manifest_identity.schema_version"
        )
        .expect("incomplete manifest identity schema version row")
    );
}

#[test]
fn petri_native_verification_bundle_handoff_diagnostic_fixture_manifest_round_trips_rows() {
    let manifest = petri_native_verification_bundle_handoff_diagnostic_fixture_manifest();
    let rows = manifest.key_value_rows();
    let report = manifest.round_trip_report(&rows);

    assert_eq!(
        report.status,
        PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestRoundTripStatus::Valid
    );
    assert_eq!(report.status_code, "valid");
    assert!(!report.fail_closed);
    assert_eq!(report.expected_row_count, rows.len());
    assert_eq!(report.observed_row_count, rows.len());
    assert_eq!(report.unique_key_count, rows.len());
    assert!(report.duplicate_keys.is_empty());
    assert!(report.missing_keys.is_empty());
    assert!(report.unexpected_keys.is_empty());
    assert!(report.mismatched_value_keys.is_empty());
    assert!(report.invalid_bool_keys.is_empty());
    assert_eq!(
        report.reconstructed_fixture_names,
        vec![
            PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_HEALTHY_DIAGNOSTIC_FIXTURE_NAME.to_string(),
            PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_INCOMPLETE_DIAGNOSTIC_FIXTURE_NAME.to_string(),
        ]
    );
    assert_eq!(
        report.reconstructed_completeness_status_codes,
        vec!["complete".to_string(), "incomplete".to_string()]
    );
    assert_eq!(
        report.reconstructed_manifest_identity_status_codes,
        vec!["complete".to_string(), "incomplete".to_string()]
    );
    assert_eq!(
        report.reconstructed_contract_health_status_codes,
        vec!["healthy".to_string(), "inconsistent".to_string()]
    );
    assert_eq!(report.reconstructed_accepted_values, vec![true, false]);
    assert_eq!(report.reconstructed_fail_closed_values, vec![false, true]);

    let unique_keys = rows
        .iter()
        .map(|row| row.key.as_str())
        .collect::<BTreeSet<_>>();
    assert_eq!(unique_keys.len(), rows.len());
}

#[test]
fn petri_native_verification_bundle_handoff_diagnostic_fixture_manifest_round_trip_fails_closed() {
    let manifest = petri_native_verification_bundle_handoff_diagnostic_fixture_manifest();
    let mut rows = manifest.key_value_rows();
    rows.retain(|row| row.key != "fixture_manifest.fixture.1.expected.fail_closed");
    if let Some(row) = rows
        .iter_mut()
        .find(|row| row.key == "fixture_manifest.fixture.0.expected.accepted")
    {
        row.value = "maybe".to_string();
    }
    rows.push(rows[0].clone());
    rows.push(NativeSharedPrimitiveContractManifestRow::new(
        "fixture_manifest.unexpected",
        "extra",
    ));

    let report = manifest.round_trip_report(&rows);

    assert_eq!(
        report.status,
        PetriNativeVerificationBundleHandoffDiagnosticFixtureManifestRoundTripStatus::Invalid
    );
    assert_eq!(report.status_code, "invalid");
    assert!(report.fail_closed);
    assert_eq!(report.expected_row_count, manifest.key_value_rows().len());
    assert_eq!(report.observed_row_count, rows.len());
    assert_eq!(
        report.duplicate_keys,
        vec!["fixture_manifest.schema".to_string()]
    );
    assert_eq!(
        report.missing_keys,
        vec!["fixture_manifest.fixture.1.expected.fail_closed".to_string()]
    );
    assert_eq!(
        report.unexpected_keys,
        vec!["fixture_manifest.unexpected".to_string()]
    );
    assert_eq!(
        report.mismatched_value_keys,
        vec!["fixture_manifest.fixture.0.expected.accepted".to_string()]
    );
    assert_eq!(
        report.invalid_bool_keys,
        vec!["fixture_manifest.fixture.0.expected.accepted".to_string()]
    );
    assert_eq!(
        report.reconstructed_fixture_names,
        vec![
            PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_HEALTHY_DIAGNOSTIC_FIXTURE_NAME.to_string(),
            PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_INCOMPLETE_DIAGNOSTIC_FIXTURE_NAME.to_string(),
        ]
    );
    assert_eq!(report.reconstructed_accepted_values, vec![false]);
    assert_eq!(report.reconstructed_fail_closed_values, vec![false]);
}

#[test]
fn petri_native_verification_bundle_handoff_healthy_diagnostic_fixture_is_accepted() {
    let descriptor = petri_native_verification_bundle_handoff_descriptor();
    let fixture = petri_native_verification_bundle_handoff_healthy_diagnostic_fixture();
    let repeated_fixture = petri_native_verification_bundle_handoff_healthy_diagnostic_fixture();
    let expected_rows = descriptor.normalized_rows();
    let required_rows = descriptor.required_normalized_rows();

    assert_eq!(fixture, repeated_fixture);
    assert_eq!(
        fixture.fixture_name,
        PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_HEALTHY_DIAGNOSTIC_FIXTURE_NAME
    );
    assert_eq!(fixture.normalized_rows, expected_rows);
    assert_eq!(fixture.normalized_rows.len(), required_rows.len());

    assert_eq!(
        fixture.completeness_report,
        descriptor.validate_normalized_rows(&fixture.normalized_rows)
    );
    assert_eq!(
        fixture.completeness_report.status,
        PetriNativeVerificationBundleHandoffCompletenessStatus::Complete
    );
    assert_eq!(fixture.completeness_report.status_code, "complete");
    assert!(fixture.completeness_report.is_complete());
    assert!(!fixture.completeness_report.fail_closed());
    assert_eq!(
        fixture.completeness_report.required_row_count,
        fixture.normalized_rows.len()
    );
    assert_eq!(
        fixture.completeness_report.present_required_row_count,
        fixture.normalized_rows.len()
    );
    assert!(fixture.completeness_report.missing_rows.is_empty());
    assert!(fixture.completeness_report.missing_row_kinds.is_empty());

    assert_eq!(fixture.manifest_identity, descriptor.manifest_identity());
    assert_eq!(
        fixture.manifest_identity,
        descriptor.manifest_identity_for_rows(&fixture.normalized_rows)
    );
    assert_eq!(
        fixture.manifest_identity_rows,
        fixture.manifest_identity.key_value_rows()
    );
    assert_eq!(
        fixture.manifest_identity.completeness_status,
        PetriNativeVerificationBundleHandoffCompletenessStatus::Complete
    );
    assert_eq!(
        fixture.manifest_identity.completeness_status_code,
        "complete"
    );
    assert!(fixture.manifest_identity.is_complete());
    assert!(!fixture.manifest_identity.fail_closed());
    assert_eq!(
        fixture.manifest_identity.observed_row_count,
        fixture.normalized_rows.len()
    );
    assert_eq!(
        fixture.manifest_identity.required_row_count,
        fixture.normalized_rows.len()
    );
    assert_eq!(
        fixture.manifest_identity.present_required_row_count,
        fixture.normalized_rows.len()
    );
    assert_eq!(fixture.manifest_identity.missing_row_count, 0);
    assert_eq!(fixture.manifest_identity.extra_row_count, 0);
    assert!(fixture.manifest_identity.missing_rows.is_empty());
    assert!(fixture.manifest_identity.missing_row_kinds.is_empty());

    assert_eq!(
        fixture.contract_health_report,
        descriptor.contract_health_report()
    );
    assert_eq!(
        fixture.contract_health_report,
        descriptor.contract_health_report_for_rows(&fixture.normalized_rows)
    );
    assert_eq!(
        fixture.contract_health_rows,
        fixture.contract_health_report.key_value_rows()
    );
    assert_eq!(
        fixture.contract_health_report.status,
        PetriNativeVerificationBundleHandoffContractHealthStatus::Healthy
    );
    assert_eq!(fixture.contract_health_report.status_code, "healthy");
    assert!(fixture.contract_health_report.is_healthy());
    assert!(!fixture.contract_health_report.fail_closed());
    assert!(fixture.contract_health_report.schema_version_rows_agree);
    assert!(fixture.contract_health_report.row_counts_agree);
    assert!(fixture.contract_health_report.completeness_agrees);
    assert!(
        fixture
            .contract_health_report
            .manifest_identity_digest_agrees
    );
    assert!(
        fixture
            .contract_health_report
            .manifest_identity_key_values_agree
    );
    assert_eq!(
        fixture
            .contract_health_report
            .completeness_missing_row_count,
        0
    );
    assert_eq!(
        fixture
            .contract_health_report
            .manifest_identity_missing_row_count,
        0
    );
    assert_eq!(
        fixture
            .contract_health_report
            .manifest_identity_extra_row_count,
        0
    );

    assert!(fixture.is_healthy());
    assert!(fixture.accepted());
    assert!(!fixture.fail_closed());
}

#[test]
fn petri_native_verification_bundle_handoff_healthy_diagnostic_fixture_rows_are_stable() {
    let descriptor = petri_native_verification_bundle_handoff_descriptor();
    let fixture = petri_native_verification_bundle_handoff_healthy_diagnostic_fixture();
    let normalized_lines = fixture
        .normalized_rows
        .iter()
        .map(|row| row.to_normalized_line())
        .collect::<Vec<_>>();
    let identity_lines = fixture
        .manifest_identity_rows
        .iter()
        .map(|row| row.to_key_value_line())
        .collect::<Vec<_>>();
    let health_lines = fixture
        .contract_health_rows
        .iter()
        .map(|row| row.to_key_value_line())
        .collect::<Vec<_>>();
    let identity_values: BTreeMap<_, _> = fixture
        .manifest_identity_rows
        .iter()
        .map(|row| (row.key.as_str(), row.value.as_str()))
        .collect();
    let health_values: BTreeMap<_, _> = fixture
        .contract_health_rows
        .iter()
        .map(|row| (row.key.as_str(), row.value.as_str()))
        .collect();
    let row_count = fixture.normalized_rows.len().to_string();

    assert_eq!(normalized_lines, descriptor.normalized_key_value_lines());
    assert_eq!(identity_lines, fixture.manifest_identity.key_value_lines());
    assert_eq!(
        fixture.manifest_identity.key_value_text(),
        format!("{}\n", identity_lines.join("\n"))
    );
    assert_eq!(
        health_lines,
        fixture.contract_health_report.key_value_lines()
    );
    assert_eq!(
        fixture.contract_health_report.key_value_text(),
        format!("{}\n", health_lines.join("\n"))
    );

    assert_eq!(
        fixture.normalized_rows.first().map(|row| (
            row.row_kind_code,
            row.key.as_str(),
            row.value.as_str()
        )),
        Some((
            "descriptor",
            "handoff.schema",
            PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SCHEMA
        ))
    );
    assert!(
        fixture
            .normalized_rows
            .iter()
            .any(|row| row.key == "bundle_identity.schema")
    );
    assert!(
        fixture
            .normalized_rows
            .iter()
            .any(|row| row.key == "solver_evidence.capability_descriptor.schema")
    );
    assert!(
        fixture
            .normalized_rows
            .iter()
            .any(|row| row.key == "solver_evidence.consumer_acceptance_api")
    );

    assert_eq!(
        identity_values
            .get("manifest_identity.completeness.status")
            .copied(),
        Some("complete")
    );
    assert_eq!(
        identity_values
            .get("manifest_identity.fail_closed")
            .copied(),
        Some("false")
    );
    assert_eq!(
        identity_values
            .get("manifest_identity.rows.observed_count")
            .copied(),
        Some(row_count.as_str())
    );
    assert_eq!(
        identity_values
            .get("manifest_identity.rows.required_count")
            .copied(),
        Some(row_count.as_str())
    );
    assert_eq!(
        identity_values
            .get("manifest_identity.rows.present_required_count")
            .copied(),
        Some(row_count.as_str())
    );
    assert_eq!(
        identity_values
            .get("manifest_identity.rows.missing_count")
            .copied(),
        Some("0")
    );
    assert_eq!(
        identity_values
            .get("manifest_identity.rows.extra_count")
            .copied(),
        Some("0")
    );
    assert_eq!(
        identity_values
            .get("manifest_identity.missing_row_kind_count")
            .copied(),
        Some("0")
    );
    assert!(!identity_values.contains_key("manifest_identity.missing_row.0.key"));

    assert_eq!(
        health_values.get("contract_health.status").copied(),
        Some("healthy")
    );
    assert_eq!(
        health_values.get("contract_health.fail_closed").copied(),
        Some("false")
    );
    assert_eq!(
        health_values
            .get("contract_health.count.completeness.missing_rows")
            .copied(),
        Some("0")
    );
    assert_eq!(
        health_values
            .get("contract_health.count.manifest_identity.missing_rows")
            .copied(),
        Some("0")
    );
    assert_eq!(
        health_values
            .get("contract_health.agreement.schema_version_rows")
            .copied(),
        Some("true")
    );
    assert_eq!(
        health_values
            .get("contract_health.agreement.row_counts")
            .copied(),
        Some("true")
    );
    assert_eq!(
        health_values
            .get("contract_health.agreement.completeness")
            .copied(),
        Some("true")
    );
    assert_eq!(
        health_values
            .get("contract_health.agreement.manifest_identity_digest")
            .copied(),
        Some("true")
    );
    assert_eq!(
        health_values
            .get("contract_health.agreement.manifest_identity_key_values")
            .copied(),
        Some("true")
    );
}

#[test]
fn petri_native_verification_bundle_handoff_incomplete_diagnostic_fixture_fails_closed() {
    let descriptor = petri_native_verification_bundle_handoff_descriptor();
    let fixture = petri_native_verification_bundle_handoff_incomplete_diagnostic_fixture();
    let repeated_fixture = petri_native_verification_bundle_handoff_incomplete_diagnostic_fixture();
    let expected_rows = descriptor.normalized_rows();

    assert_eq!(fixture, repeated_fixture);
    assert_eq!(
        fixture.fixture_name,
        PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_INCOMPLETE_DIAGNOSTIC_FIXTURE_NAME
    );
    assert_eq!(
        fixture.missing_row_keys,
        PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_INCOMPLETE_DIAGNOSTIC_MISSING_ROW_KEYS
    );
    assert_eq!(fixture.normalized_rows.len(), expected_rows.len() - 2);
    for missing_key in fixture.missing_row_keys {
        assert!(
            !fixture
                .normalized_rows
                .iter()
                .any(|row| row.key == *missing_key),
            "diagnostic fixture unexpectedly includes missing row {missing_key}"
        );
    }

    assert!(fixture.fail_closed());
    assert_eq!(
        fixture.completeness_report.status,
        PetriNativeVerificationBundleHandoffCompletenessStatus::Incomplete
    );
    assert_eq!(fixture.completeness_report.status_code, "incomplete");
    assert!(fixture.completeness_report.fail_closed());
    assert_eq!(
        fixture.completeness_report.required_row_count,
        expected_rows.len()
    );
    assert_eq!(
        fixture.completeness_report.present_required_row_count,
        fixture.normalized_rows.len()
    );
    assert_eq!(fixture.completeness_report.missing_rows.len(), 2);
    assert_eq!(
        fixture
            .completeness_report
            .missing_rows
            .iter()
            .map(|row| (row.row_kind, row.key.as_str(), row.ordinal))
            .collect::<Vec<_>>(),
        vec![
            (
                PetriNativeVerificationBundleHandoffRowKind::BundleIdentity,
                "bundle_identity.schema",
                0,
            ),
            (
                PetriNativeVerificationBundleHandoffRowKind::SolverEvidence,
                "solver_evidence.capability_descriptor.schema",
                0,
            ),
        ]
    );
    assert_eq!(
        fixture.completeness_report.missing_row_kinds,
        vec![
            PetriNativeVerificationBundleHandoffRowKind::BundleIdentity,
            PetriNativeVerificationBundleHandoffRowKind::SolverEvidence,
        ]
    );

    assert_eq!(
        fixture.manifest_identity,
        descriptor.manifest_identity_for_rows(&fixture.normalized_rows)
    );
    assert!(fixture.manifest_identity.fail_closed());
    assert_eq!(
        fixture.manifest_identity.completeness_status,
        PetriNativeVerificationBundleHandoffCompletenessStatus::Incomplete
    );
    assert_eq!(
        fixture.manifest_identity.completeness_status_code,
        "incomplete"
    );
    assert_eq!(
        fixture.manifest_identity.observed_row_count,
        fixture.normalized_rows.len()
    );
    assert_eq!(
        fixture.manifest_identity.required_row_count,
        expected_rows.len()
    );
    assert_eq!(
        fixture.manifest_identity.present_required_row_count,
        fixture.normalized_rows.len()
    );
    assert_eq!(fixture.manifest_identity.missing_row_count, 2);
    assert_eq!(fixture.manifest_identity.extra_row_count, 0);
    assert_eq!(
        fixture.manifest_identity.missing_rows,
        fixture.completeness_report.missing_rows
    );
    assert_eq!(
        fixture.manifest_identity.missing_row_kinds,
        fixture.completeness_report.missing_row_kinds
    );
    assert!(
        fixture
            .manifest_identity
            .canonical_text
            .contains("completeness.status=incomplete\n")
    );
    assert!(
        fixture
            .manifest_identity
            .canonical_text
            .contains("missing.0.key=bundle_identity.schema\n")
    );
    assert!(
        fixture
            .manifest_identity
            .canonical_text
            .contains("missing.1.key=solver_evidence.capability_descriptor.schema\n")
    );

    assert_eq!(
        fixture.contract_health_report,
        descriptor.contract_health_report_for_rows(&fixture.normalized_rows)
    );
    assert_eq!(
        fixture.contract_health_report.status,
        PetriNativeVerificationBundleHandoffContractHealthStatus::Inconsistent
    );
    assert_eq!(fixture.contract_health_report.status_code, "inconsistent");
    assert!(fixture.contract_health_report.fail_closed());
    assert!(fixture.contract_health_report.schema_version_rows_agree);
    assert!(!fixture.contract_health_report.row_counts_agree);
    assert!(!fixture.contract_health_report.completeness_agrees);
    assert!(
        fixture
            .contract_health_report
            .manifest_identity_digest_agrees
    );
    assert!(
        fixture
            .contract_health_report
            .manifest_identity_key_values_agree
    );
    assert_eq!(
        fixture.contract_health_report.normalized_row_count,
        fixture.normalized_rows.len()
    );
    assert_eq!(
        fixture.contract_health_report.required_row_count,
        expected_rows.len()
    );
    assert_eq!(
        fixture
            .contract_health_report
            .completeness_missing_row_count,
        2
    );
    assert_eq!(
        fixture
            .contract_health_report
            .manifest_identity_missing_row_count,
        2
    );
    assert_eq!(
        fixture
            .contract_health_report
            .manifest_identity_extra_row_count,
        0
    );
}

#[test]
fn petri_native_verification_bundle_handoff_incomplete_diagnostic_fixture_rows_are_stable() {
    let fixture = petri_native_verification_bundle_handoff_incomplete_diagnostic_fixture();
    let identity_lines = fixture.manifest_identity.key_value_lines();
    let health_lines = fixture.contract_health_report.key_value_lines();
    let identity_values: BTreeMap<_, _> = identity_lines
        .iter()
        .map(|line| {
            line.split_once('=')
                .unwrap_or_else(|| panic!("malformed identity line {line}"))
        })
        .collect();
    let health_values: BTreeMap<_, _> = health_lines
        .iter()
        .map(|line| {
            line.split_once('=')
                .unwrap_or_else(|| panic!("malformed health line {line}"))
        })
        .collect();

    assert_eq!(
        fixture.normalized_rows.first().map(|row| (
            row.row_kind_code,
            row.key.as_str(),
            row.value.as_str()
        )),
        Some((
            "descriptor",
            "handoff.schema",
            PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SCHEMA
        ))
    );
    assert!(
        fixture
            .normalized_rows
            .iter()
            .any(|row| row.key == "solver_evidence.consumer_acceptance_api")
    );
    assert!(
        !fixture
            .normalized_rows
            .iter()
            .any(|row| row.key == "bundle_identity.schema")
    );
    assert!(
        !fixture
            .normalized_rows
            .iter()
            .any(|row| row.key == "solver_evidence.capability_descriptor.schema")
    );

    assert_eq!(
        identity_values
            .get("manifest_identity.completeness.status")
            .copied(),
        Some("incomplete")
    );
    assert_eq!(
        identity_values
            .get("manifest_identity.fail_closed")
            .copied(),
        Some("true")
    );
    assert_eq!(
        identity_values
            .get("manifest_identity.rows.missing_count")
            .copied(),
        Some("2")
    );
    assert_eq!(
        identity_values
            .get("manifest_identity.missing_row_kind_count")
            .copied(),
        Some("2")
    );
    assert_eq!(
        identity_values
            .get("manifest_identity.missing_row_kind.0")
            .copied(),
        Some("bundle_identity")
    );
    assert_eq!(
        identity_values
            .get("manifest_identity.missing_row_kind.1")
            .copied(),
        Some("solver_evidence")
    );
    assert_eq!(
        identity_values
            .get("manifest_identity.missing_row.0.key")
            .copied(),
        Some("bundle_identity.schema")
    );
    assert_eq!(
        identity_values
            .get("manifest_identity.missing_row.1.key")
            .copied(),
        Some("solver_evidence.capability_descriptor.schema")
    );

    assert_eq!(
        health_values.get("contract_health.status").copied(),
        Some("inconsistent")
    );
    assert_eq!(
        health_values.get("contract_health.fail_closed").copied(),
        Some("true")
    );
    assert_eq!(
        health_values
            .get("contract_health.count.completeness.missing_rows")
            .copied(),
        Some("2")
    );
    assert_eq!(
        health_values
            .get("contract_health.count.manifest_identity.missing_rows")
            .copied(),
        Some("2")
    );
    assert_eq!(
        health_values
            .get("contract_health.agreement.row_counts")
            .copied(),
        Some("false")
    );
    assert_eq!(
        health_values
            .get("contract_health.agreement.completeness")
            .copied(),
        Some("false")
    );
    assert_eq!(
        health_values
            .get("contract_health.agreement.manifest_identity_digest")
            .copied(),
        Some("true")
    );
    assert_eq!(
        health_values
            .get("contract_health.agreement.manifest_identity_key_values")
            .copied(),
        Some("true")
    );
}

#[test]
fn petri_native_verification_bundle_handoff_replay_contract_surface_rows_are_internally_consistent()
{
    // Behavioral coverage of the replay-contract-surface serialization:
    // deterministic, deduplicated `key=value` rows whose count/text invariants
    // hold. The former name-mirror assertions (surface == its own const, and
    // `contains()` against hard-coded copies of the const string slices) were
    // tautological and have been removed; round-trip/fail-closed behavior is
    // covered by the sibling `..._round_trips_rows_and_lines` test.
    let surface = petri_native_verification_bundle_handoff_replay_contract_surface();

    assert_eq!(surface.schema_names.len(), surface.schema_values.len());

    let rows = surface.key_value_rows();
    let repeated_rows = surface.key_value_rows();
    let lines = surface.key_value_lines();
    let values: BTreeMap<_, _> = rows
        .iter()
        .map(|row| (row.key.as_str(), row.value.as_str()))
        .collect();
    let unique_keys: BTreeSet<_> = rows.iter().map(|row| row.key.as_str()).collect();
    let helper_count = surface.helper_names.len().to_string();
    let schema_count = surface.schema_names.len().to_string();
    let fixture_count = surface.fixture_names.len().to_string();
    let validator_count = surface.validator_names.len().to_string();

    assert_eq!(rows, repeated_rows);
    assert_eq!(unique_keys.len(), rows.len());
    assert_eq!(lines.len(), rows.len());
    assert_eq!(
        lines,
        rows.iter()
            .map(|row| row.to_key_value_line())
            .collect::<Vec<_>>()
    );
    assert_eq!(surface.key_value_text(), format!("{}\n", lines.join("\n")));
    assert_eq!(
        values.get("replay_contract_surface.schema").copied(),
        Some(PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_SURFACE_SCHEMA)
    );
    assert_eq!(
        values
            .get("replay_contract_surface.source.package")
            .copied(),
        Some(PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_SOURCE_PACKAGE)
    );
    assert_eq!(
        values.get("replay_contract_surface.helper_count").copied(),
        Some(helper_count.as_str())
    );
    assert_eq!(
        values.get("replay_contract_surface.schema_count").copied(),
        Some(schema_count.as_str())
    );
    assert_eq!(
        values.get("replay_contract_surface.fixture_count").copied(),
        Some(fixture_count.as_str())
    );
    assert_eq!(
        values
            .get("replay_contract_surface.validator_count")
            .copied(),
        Some(validator_count.as_str())
    );
    assert!(values.values().any(|value| *value
        == "PetriNativeVerificationBundleHandoffDescriptor::required_normalized_rows()"));
    assert!(values.values().any(|value| *value
        == "PetriNativeVerificationBundleHandoffManifestIdentity::round_trip_report()"));
    assert!(
        values.values().any(
            |value| *value == PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_MANIFEST_IDENTITY_SCHEMA
        )
    );
    assert!(
        values.values().any(|value| *value
            == PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_HEALTHY_DIAGNOSTIC_FIXTURE_NAME)
    );
    assert!(values.values().any(|value| *value
        == PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_INCOMPLETE_DIAGNOSTIC_FIXTURE_NAME));
    assert!(values.values().any(|value| *value
            == "PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport::compact_manifest_json_text()"));
    assert!(values.values().any(|value| *value
            == "PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingFixture::key_value_rows()"));
}

#[test]
fn petri_native_verification_bundle_handoff_replay_contract_surface_round_trips_rows_and_lines() {
    let surface = petri_native_verification_bundle_handoff_replay_contract_surface();
    let rows = surface.key_value_rows();
    let lines = surface.key_value_lines();

    let row_report = surface.round_trip_report(&rows);
    assert_eq!(
        row_report.status,
        PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripStatus::Valid
    );
    assert_eq!(row_report.status_code, "valid");
    assert!(!row_report.fail_closed);
    assert_eq!(row_report.expected_row_count, rows.len());
    assert_eq!(row_report.observed_row_count, rows.len());
    assert_eq!(row_report.unique_key_count, rows.len());
    assert!(row_report.duplicate_keys.is_empty());
    assert!(row_report.missing_keys.is_empty());
    assert!(row_report.unexpected_keys.is_empty());
    assert!(row_report.mismatched_value_keys.is_empty());
    assert!(row_report.invalid_usize_keys.is_empty());
    assert!(row_report.invalid_lines.is_empty());
    assert_eq!(
        row_report.reconstructed_schema.as_deref(),
        Some(PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_SURFACE_SCHEMA)
    );
    assert_eq!(
        row_report.reconstructed_schema_version,
        Some(
            PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_SURFACE_SCHEMA_VERSION
                as usize
        )
    );
    assert_eq!(
        row_report.reconstructed_helper_names,
        surface
            .helper_names
            .iter()
            .map(|name| (*name).to_string())
            .collect::<Vec<_>>()
    );
    assert_eq!(
        row_report.reconstructed_schema_names,
        surface
            .schema_names
            .iter()
            .map(|name| (*name).to_string())
            .collect::<Vec<_>>()
    );
    assert_eq!(
        row_report.reconstructed_schema_values,
        surface
            .schema_values
            .iter()
            .map(|value| (*value).to_string())
            .collect::<Vec<_>>()
    );
    assert_eq!(
        row_report.reconstructed_fixture_count,
        Some(surface.fixture_names.len())
    );
    assert_eq!(
        row_report.reconstructed_fixture_names,
        surface
            .fixture_names
            .iter()
            .map(|name| (*name).to_string())
            .collect::<Vec<_>>()
    );
    assert_eq!(
        row_report.reconstructed_validator_names,
        surface
            .validator_names
            .iter()
            .map(|name| (*name).to_string())
            .collect::<Vec<_>>()
    );
    assert!(row_report.schema_header_matches);
    assert!(row_report.schema_name_value_rows_agree);
    assert!(row_report.helper_names_match);
    assert!(row_report.fixture_count_matches);
    assert!(row_report.fixture_names_match);
    assert!(row_report.validator_names_match);

    let line_report = surface.round_trip_report_for_key_value_lines(&lines);
    assert_eq!(line_report, row_report);
}

#[test]
fn petri_native_verification_bundle_handoff_replay_contract_surface_fails_closed_on_bad_rows() {
    let surface = petri_native_verification_bundle_handoff_replay_contract_surface();
    let mut rows = surface.key_value_rows();
    rows.iter_mut()
        .find(|row| row.key == "replay_contract_surface.schema")
        .expect("surface schema row should be present")
        .value = "stale.replay.contract.surface.v0".to_string();
    let missing_fixture_position = rows
        .iter()
        .position(|row| row.key == "replay_contract_surface.fixture.0.name")
        .expect("fixture.0 row should be present");
    rows.remove(missing_fixture_position);
    let duplicate_helper = rows
        .iter()
        .find(|row| row.key == "replay_contract_surface.helper.0.name")
        .expect("helper.0 row should be present")
        .clone();
    rows.push(duplicate_helper);

    let report = surface.round_trip_report(&rows);
    assert_eq!(
        report.status,
        PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripStatus::Invalid
    );
    assert_eq!(report.status_code, "invalid");
    assert!(report.fail_closed);
    assert_eq!(report.expected_row_count, surface.key_value_rows().len());
    assert_eq!(report.observed_row_count, surface.key_value_rows().len());
    assert_eq!(
        report.duplicate_keys,
        vec!["replay_contract_surface.helper.0.name".to_string()]
    );
    assert_eq!(
        report.missing_keys,
        vec!["replay_contract_surface.fixture.0.name".to_string()]
    );
    assert_eq!(
        report.mismatched_value_keys,
        vec!["replay_contract_surface.schema".to_string()]
    );
    assert!(report.unexpected_keys.is_empty());
    assert!(report.invalid_usize_keys.is_empty());
    assert_eq!(
        report.reconstructed_schema.as_deref(),
        Some("stale.replay.contract.surface.v0")
    );
    assert!(!report.schema_header_matches);
    assert!(report.schema_name_value_rows_agree);
    assert!(report.helper_names_match);
    assert!(report.fixture_count_matches);
    assert!(!report.fixture_names_match);
    assert!(report.validator_names_match);
    assert_eq!(
            report.reconstructed_fixture_names,
            vec![
                PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_INCOMPLETE_DIAGNOSTIC_FIXTURE_NAME
                    .to_string(),
                PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_JSON_MANIFEST_BINDING_HEALTHY_FIXTURE_NAME
                    .to_string(),
                PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_JSON_MANIFEST_BINDING_STALE_FIXTURE_NAME
                    .to_string(),
            ]
        );

    let mut lines = surface.key_value_lines();
    lines[0] = "malformed surface line".to_string();
    let line_report = surface.round_trip_report_for_key_value_lines(&lines);
    assert_eq!(
        line_report.status,
        PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripStatus::Invalid
    );
    assert!(line_report.fail_closed);
    assert_eq!(
        line_report.invalid_lines,
        vec!["0:malformed surface line".to_string()]
    );
    assert!(
        line_report
            .missing_keys
            .contains(&"replay_contract_surface.schema".to_string())
    );
}

#[test]
fn petri_native_verification_bundle_handoff_replay_contract_round_trip_report_rows_are_stable() {
    let surface = petri_native_verification_bundle_handoff_replay_contract_surface();
    let report = surface.round_trip_report(&surface.key_value_rows());
    let repeated_report = surface.round_trip_report_for_key_value_lines(&surface.key_value_lines());
    let rows = report.key_value_rows();
    let repeated_rows = report.key_value_rows();
    let lines = report.key_value_lines();
    let values: BTreeMap<_, _> = rows
        .iter()
        .map(|row| (row.key.as_str(), row.value.as_str()))
        .collect();
    let digest = report.identity_digest();

    assert_eq!(report, repeated_report);
    assert_eq!(report.diagnostic_count(), 0);
    assert_eq!(digest, report.identity_digest());
    assert_eq!(rows, repeated_rows);
    assert_eq!(report.key_value_text(), format!("{}\n", lines.join("\n")));
    assert!(
        report
            .canonical_identity_text()
            .contains("round_trip_report.status=valid\n")
    );
    assert_eq!(
        values.get("round_trip_report.schema").copied(),
        Some(PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_ROUND_TRIP_REPORT_SCHEMA)
    );
    assert_eq!(
        values.get("round_trip_report.status").copied(),
        Some("valid")
    );
    assert_eq!(
        values.get("round_trip_report.fail_closed").copied(),
        Some("false")
    );
    assert_eq!(
        values.get("round_trip_report.surface.schema").copied(),
        Some(PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_SURFACE_SCHEMA)
    );
    assert_eq!(
        values.get("round_trip_report.count.helpers").copied(),
        Some(surface.helper_names.len().to_string().as_str())
    );
    assert_eq!(
        values.get("round_trip_report.count.validators").copied(),
        Some(surface.validator_names.len().to_string().as_str())
    );
    assert_eq!(
        values.get("round_trip_report.count.fixtures").copied(),
        Some(surface.fixture_names.len().to_string().as_str())
    );
    assert_eq!(
        values.get("round_trip_report.count.diagnostics").copied(),
        Some("0")
    );
    assert_eq!(
            values
                .get("round_trip_report.digest.context")
                .copied(),
            Some(
                PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_ROUND_TRIP_REPORT_DIGEST_CONTEXT
            )
        );
    assert_eq!(
        values.get("round_trip_report.digest.algorithm").copied(),
        Some("sha256")
    );
    assert_eq!(
        values.get("round_trip_report.digest").copied(),
        Some(digest.to_string().as_str())
    );

    let row_validation = report.key_value_round_trip_report(&rows);
    assert_eq!(
        row_validation.status,
        PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripStatus::Valid
    );
    assert!(!row_validation.fail_closed);
    assert!(row_validation.duplicate_keys.is_empty());
    assert!(row_validation.missing_keys.is_empty());
    assert!(row_validation.mismatched_value_keys.is_empty());

    let line_validation = report.key_value_line_round_trip_report(&lines);
    assert_eq!(line_validation, row_validation);
}

fn assert_replay_contract_round_trip_report_json_matches_rows(
    report: &PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripReport,
) {
    let rows = report.key_value_rows();
    let values: BTreeMap<_, _> = rows
        .iter()
        .map(|row| (row.key.as_str(), row.value.as_str()))
        .collect();
    let row_value = |key: &str| {
        values
            .get(key)
            .copied()
            .unwrap_or_else(|| panic!("missing report row {key}"))
    };
    let json_text = report.compact_manifest_json_text();
    let parsed: serde_json::Value =
        serde_json::from_str(&json_text).expect("compact report JSON should parse");

    assert_eq!(
        parsed.get("schema").and_then(serde_json::Value::as_str),
        Some(row_value("round_trip_report.schema"))
    );
    assert_eq!(
        parsed
            .get("schema_version")
            .and_then(serde_json::Value::as_u64),
        row_value("round_trip_report.schema_version")
            .parse::<u64>()
            .ok()
    );
    assert_eq!(
        parsed
            .get("identity_text")
            .and_then(serde_json::Value::as_str),
        Some(report.canonical_identity_text().as_str())
    );
    assert_eq!(
        parsed
            .get("identity_digest_context")
            .and_then(serde_json::Value::as_str),
        Some(row_value("round_trip_report.digest.context"))
    );
    assert_eq!(
        parsed
            .get("identity_digest_algorithm")
            .and_then(serde_json::Value::as_str),
        Some(row_value("round_trip_report.digest.algorithm"))
    );
    assert_eq!(
        parsed
            .get("identity_digest")
            .and_then(serde_json::Value::as_str),
        Some(row_value("round_trip_report.digest"))
    );
    assert_eq!(
        parsed.get("status").and_then(serde_json::Value::as_str),
        Some(row_value("round_trip_report.status"))
    );
    assert_eq!(
        parsed
            .get("fail_closed")
            .and_then(serde_json::Value::as_bool),
        Some(row_value("round_trip_report.fail_closed") == "true")
    );
    assert_eq!(
        parsed
            .get("surface_schema")
            .and_then(serde_json::Value::as_str),
        Some(row_value("round_trip_report.surface.schema"))
    );
    assert_eq!(
        parsed
            .get("surface_schema_version")
            .and_then(serde_json::Value::as_u64),
        row_value("round_trip_report.surface.schema_version")
            .parse::<u64>()
            .ok()
    );
    assert_eq!(
        parsed
            .get("expected_row_count")
            .and_then(serde_json::Value::as_u64),
        row_value("round_trip_report.count.expected_rows")
            .parse::<u64>()
            .ok()
    );
    assert_eq!(
        parsed
            .get("observed_row_count")
            .and_then(serde_json::Value::as_u64),
        row_value("round_trip_report.count.observed_rows")
            .parse::<u64>()
            .ok()
    );
    assert_eq!(
        parsed
            .get("unique_key_count")
            .and_then(serde_json::Value::as_u64),
        row_value("round_trip_report.count.unique_keys")
            .parse::<u64>()
            .ok()
    );
    assert_eq!(
        parsed
            .get("helper_count")
            .and_then(serde_json::Value::as_u64),
        row_value("round_trip_report.count.helpers")
            .parse::<u64>()
            .ok()
    );
    assert_eq!(
        parsed
            .get("validator_count")
            .and_then(serde_json::Value::as_u64),
        row_value("round_trip_report.count.validators")
            .parse::<u64>()
            .ok()
    );
    assert_eq!(
        parsed
            .get("fixture_count")
            .and_then(serde_json::Value::as_u64),
        row_value("round_trip_report.count.fixtures")
            .parse::<u64>()
            .ok()
    );
    assert_eq!(
        parsed
            .get("diagnostic_count")
            .and_then(serde_json::Value::as_u64),
        row_value("round_trip_report.count.diagnostics")
            .parse::<u64>()
            .ok()
    );
}

#[test]
fn petri_native_verification_bundle_handoff_replay_contract_round_trip_report_json_matches_rows() {
    let surface = petri_native_verification_bundle_handoff_replay_contract_surface();
    let healthy_report = surface.round_trip_report(&surface.key_value_rows());
    assert_replay_contract_round_trip_report_json_matches_rows(&healthy_report);
    assert_eq!(
        healthy_report.compact_manifest_json_text(),
        healthy_report.compact_manifest_json_text()
    );

    let mut surface_lines = surface.key_value_lines();
    surface_lines[0] = "malformed surface line".to_string();
    let fail_closed_report = surface.round_trip_report_for_key_value_lines(&surface_lines);
    assert_replay_contract_round_trip_report_json_matches_rows(&fail_closed_report);
    assert_eq!(
        fail_closed_report
            .compact_manifest_json_text()
            .matches('\n')
            .count(),
        1
    );
}

#[test]
fn petri_native_verification_bundle_handoff_replay_contract_round_trip_report_json_rejects_stale_text()
 {
    let surface = petri_native_verification_bundle_handoff_replay_contract_surface();
    let mut surface_lines = surface.key_value_lines();
    surface_lines[0] = "malformed surface line".to_string();
    let report = surface.round_trip_report_for_key_value_lines(&surface_lines);
    let json_text = report.compact_manifest_json_text();
    let stale_json_text = json_text.replace("\"status\":\"invalid\"", "\"status\":\"valid\"");
    let stale_json: serde_json::Value =
        serde_json::from_str(&stale_json_text).expect("stale JSON should still parse");
    let values: BTreeMap<_, _> = report
        .key_value_rows()
        .iter()
        .map(|row| (row.key.clone(), row.value.clone()))
        .collect();

    assert_ne!(
        stale_json.get("status").and_then(serde_json::Value::as_str),
        values.get("round_trip_report.status").map(String::as_str)
    );
    assert!(
        serde_json::from_str::<serde_json::Value>(&json_text[1..]).is_err(),
        "manifest without opening object should fail JSON parsing"
    );
}

#[test]
fn petri_native_verification_bundle_handoff_replay_contract_json_manifest_binding_accepts_handoff_identity()
 {
    let descriptor = petri_native_verification_bundle_handoff_descriptor();
    let surface = petri_native_verification_bundle_handoff_replay_contract_surface();
    let report = surface.round_trip_report(&surface.key_value_rows());
    let manifest_identity = descriptor.manifest_identity();
    let binding = report.compact_manifest_handoff_identity_report(&manifest_identity);
    let rows = binding.key_value_rows();
    let values: BTreeMap<_, _> = rows
        .iter()
        .map(|row| (row.key.as_str(), row.value.as_str()))
        .collect();
    let json_text_digest = ProofDigest::sha256_domain(
            PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_JSON_MANIFEST_BINDING_DIGEST_CONTEXT,
            report.compact_manifest_json_text().as_bytes(),
        );
    let json_text_digest_string = json_text_digest.to_string();
    let report_identity_digest_string = report.identity_digest().to_string();
    let manifest_identity_digest_string = manifest_identity.digest.to_string();

    assert_eq!(
        binding.status,
        PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingStatus::Bound
    );
    assert_eq!(binding.status_code, "bound");
    assert!(binding.is_bound());
    assert!(!binding.fail_closed);
    assert!(binding.report_valid);
    assert!(binding.replay_surface_schema_matches);
    assert!(binding.handoff_schema_listed_by_surface);
    assert!(binding.manifest_identity_schema_listed_by_surface);
    assert!(binding.manifest_identity_complete);
    assert!(binding.manifest_identity_descriptor_matches);
    assert!(binding.manifest_identity_source_matches);
    assert!(binding.manifest_identity_digest_matches_canonical_text);
    assert_eq!(binding.json_manifest_text_digest, json_text_digest);
    assert_eq!(
        binding.round_trip_report_identity_digest,
        report.identity_digest()
    );
    assert_eq!(binding.manifest_identity_digest, manifest_identity.digest);
    assert_eq!(
        binding.key_value_text(),
        format!("{}\n", binding.key_value_lines().join("\n"))
    );
    assert_eq!(
        values.get("json_manifest_binding.schema").copied(),
        Some(PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_JSON_MANIFEST_BINDING_SCHEMA)
    );
    assert_eq!(
        values.get("json_manifest_binding.status").copied(),
        Some("bound")
    );
    assert_eq!(
        values.get("json_manifest_binding.fail_closed").copied(),
        Some("false")
    );
    assert_eq!(
        values.get("json_manifest.schema").copied(),
        Some(PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_ROUND_TRIP_REPORT_SCHEMA)
    );
    assert_eq!(
        values.get("json_manifest.text_digest").copied(),
        Some(json_text_digest_string.as_str())
    );
    assert_eq!(
        values.get("round_trip_report.identity_digest").copied(),
        Some(report_identity_digest_string.as_str())
    );
    assert_eq!(
        values.get("manifest_identity.digest").copied(),
        Some(manifest_identity_digest_string.as_str())
    );
    assert_eq!(
        values
            .get("json_manifest_binding.check.manifest_identity_digest_matches_canonical_text")
            .copied(),
        Some("true")
    );
}

#[test]
fn petri_native_verification_bundle_handoff_replay_contract_json_manifest_binding_fails_closed_on_stale_identity()
 {
    let descriptor = petri_native_verification_bundle_handoff_descriptor();
    let surface = petri_native_verification_bundle_handoff_replay_contract_surface();
    let report = surface.round_trip_report(&surface.key_value_rows());
    let manifest_identity = descriptor.manifest_identity();

    let mut stale_digest_identity = manifest_identity.clone();
    stale_digest_identity.digest = report.identity_digest();
    let stale_digest_binding =
        report.compact_manifest_handoff_identity_report(&stale_digest_identity);
    assert_eq!(
        stale_digest_binding.status,
        PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingStatus::Mismatched
    );
    assert_eq!(stale_digest_binding.status_code, "mismatched");
    assert!(stale_digest_binding.fail_closed);
    assert!(!stale_digest_binding.is_bound());
    assert!(stale_digest_binding.manifest_identity_descriptor_matches);
    assert!(!stale_digest_binding.manifest_identity_digest_matches_canonical_text);

    let mut stale_descriptor_identity = manifest_identity;
    stale_descriptor_identity.descriptor_schema =
        "trust_ir.native.petri_successor.bundle_solver_evidence_handoff.v0";
    let stale_descriptor_binding =
        report.compact_manifest_handoff_identity_report(&stale_descriptor_identity);
    let values: BTreeMap<_, _> = stale_descriptor_binding
        .key_value_rows()
        .iter()
        .map(|row| (row.key.clone(), row.value.clone()))
        .collect();

    assert_eq!(
        stale_descriptor_binding.status,
        PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingStatus::Mismatched
    );
    assert!(stale_descriptor_binding.fail_closed);
    assert!(!stale_descriptor_binding.manifest_identity_descriptor_matches);
    assert_eq!(
        values
            .get("json_manifest_binding.status")
            .map(String::as_str),
        Some("mismatched")
    );
    assert_eq!(
        values
            .get("json_manifest_binding.check.manifest_identity_descriptor_matches")
            .map(String::as_str),
        Some("false")
    );
}

#[test]
fn petri_native_verification_bundle_handoff_replay_contract_json_manifest_binding_fixtures_are_canonical()
 {
    let descriptor = petri_native_verification_bundle_handoff_descriptor();
    let healthy =
            petri_native_verification_bundle_handoff_replay_contract_json_manifest_binding_healthy_fixture();
    let repeated_healthy =
            petri_native_verification_bundle_handoff_replay_contract_json_manifest_binding_healthy_fixture();
    let stale =
            petri_native_verification_bundle_handoff_replay_contract_json_manifest_binding_stale_fixture();
    let healthy_rows = healthy.key_value_rows();
    let healthy_lines = healthy.key_value_lines();
    let healthy_values: BTreeMap<_, _> = healthy_rows
        .iter()
        .map(|row| (row.key.as_str(), row.value.as_str()))
        .collect();
    let stale_values: BTreeMap<_, _> = stale
        .key_value_rows()
        .iter()
        .map(|row| (row.key.clone(), row.value.clone()))
        .collect();
    let healthy_json_digest = ProofDigest::sha256_domain(
            PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_JSON_MANIFEST_BINDING_DIGEST_CONTEXT,
            healthy.compact_json_text.as_bytes(),
        );
    let healthy_json_digest_string = healthy_json_digest.to_string();
    let healthy_report_digest_string = healthy.round_trip_report.identity_digest().to_string();
    let healthy_manifest_digest_string = healthy.manifest_identity.digest.to_string();

    assert_eq!(healthy, repeated_healthy);
    assert_eq!(
            healthy.fixture_name,
            PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_JSON_MANIFEST_BINDING_HEALTHY_FIXTURE_NAME
        );
    assert_eq!(
            stale.fixture_name,
            PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_JSON_MANIFEST_BINDING_STALE_FIXTURE_NAME
        );
    assert!(healthy.accepted());
    assert!(!healthy.fail_closed());
    assert_eq!(healthy.expected_status_code, "bound");
    assert!(!healthy.expected_fail_closed);
    assert_eq!(
        healthy.binding_report.status,
        PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingStatus::Bound
    );
    assert_eq!(healthy.manifest_identity, descriptor.manifest_identity());
    assert_eq!(
        healthy.compact_json_text,
        healthy.round_trip_report.compact_manifest_json_text()
    );
    assert_eq!(
        healthy.binding_rows,
        healthy.binding_report.key_value_rows()
    );
    assert_eq!(
        healthy.key_value_text(),
        format!("{}\n", healthy_lines.join("\n"))
    );
    assert_eq!(
        healthy.binding_report.json_manifest_text_digest,
        healthy_json_digest
    );
    assert_eq!(
        healthy.binding_report.round_trip_report_identity_digest,
        healthy.round_trip_report.identity_digest()
    );
    assert_eq!(
        healthy.binding_report.manifest_identity_digest,
        healthy.manifest_identity.digest
    );
    assert_eq!(
            healthy_values
                .get("json_manifest_binding_fixture.name")
                .copied(),
            Some(
                PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_JSON_MANIFEST_BINDING_HEALTHY_FIXTURE_NAME
            )
        );
    assert_eq!(
        healthy_values
            .get("json_manifest_binding_fixture.expected.status")
            .copied(),
        Some("bound")
    );
    assert_eq!(
        healthy_values
            .get("json_manifest_binding_fixture.accepted")
            .copied(),
        Some("true")
    );
    assert_eq!(
        healthy_values
            .get("json_manifest_binding_fixture.compact_json_text_digest")
            .copied(),
        Some(healthy_json_digest_string.as_str())
    );
    assert_eq!(
        healthy_values
            .get("json_manifest_binding_fixture.round_trip_report_identity_digest")
            .copied(),
        Some(healthy_report_digest_string.as_str())
    );
    assert_eq!(
        healthy_values
            .get("json_manifest_binding_fixture.manifest_identity_digest")
            .copied(),
        Some(healthy_manifest_digest_string.as_str())
    );
    assert_eq!(
        healthy_values
            .get("json_manifest_binding_fixture.binding_row_count")
            .and_then(|value| value.parse::<usize>().ok()),
        Some(healthy.binding_rows.len())
    );

    assert!(!stale.accepted());
    assert!(stale.fail_closed());
    assert_eq!(stale.expected_status_code, "mismatched");
    assert!(stale.expected_fail_closed);
    assert_eq!(
        stale.binding_report.status,
        PetriNativeVerificationBundleHandoffReplayContractJsonManifestBindingStatus::Mismatched
    );
    assert_eq!(
        stale.compact_json_text,
        stale.round_trip_report.compact_manifest_json_text()
    );
    assert_eq!(
        stale.binding_report.round_trip_report_identity_digest,
        stale.round_trip_report.identity_digest()
    );
    assert_eq!(
        stale.binding_report.manifest_identity_digest,
        stale.manifest_identity.digest
    );
    assert_ne!(
        stale.manifest_identity.digest,
        descriptor.manifest_identity().digest
    );
    assert!(
        !stale
            .binding_report
            .manifest_identity_digest_matches_canonical_text
    );
    assert_eq!(
            stale_values
                .get("json_manifest_binding_fixture.name")
                .map(String::as_str),
            Some(
                PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_REPLAY_CONTRACT_JSON_MANIFEST_BINDING_STALE_FIXTURE_NAME
            )
        );
    assert_eq!(
        stale_values
            .get("json_manifest_binding_fixture.observed.status")
            .map(String::as_str),
        Some("mismatched")
    );
    assert_eq!(
        stale_values
            .get("json_manifest_binding_fixture.fail_closed")
            .map(String::as_str),
        Some("true")
    );
}

#[test]
fn petri_native_verification_bundle_handoff_replay_contract_round_trip_report_rows_fail_closed() {
    let surface = petri_native_verification_bundle_handoff_replay_contract_surface();
    let mut surface_lines = surface.key_value_lines();
    surface_lines[0] = "malformed surface line".to_string();
    let report = surface.round_trip_report_for_key_value_lines(&surface_lines);
    let rows = report.key_value_rows();
    let values: BTreeMap<_, _> = rows
        .iter()
        .map(|row| (row.key.as_str(), row.value.as_str()))
        .collect();

    assert_eq!(
        report.status,
        PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripStatus::Invalid
    );
    assert!(report.fail_closed);
    assert_eq!(report.diagnostic_count(), 2);
    assert!(
        report
            .canonical_identity_text()
            .contains("round_trip_report.status=invalid\n")
    );
    assert_eq!(
        values.get("round_trip_report.status").copied(),
        Some("invalid")
    );
    assert_eq!(
        values.get("round_trip_report.fail_closed").copied(),
        Some("true")
    );
    assert_eq!(
        values.get("round_trip_report.count.fixtures").copied(),
        Some(surface.fixture_names.len().to_string().as_str())
    );
    assert_eq!(
        values.get("round_trip_report.count.diagnostics").copied(),
        Some("2")
    );
    assert_eq!(
        values
            .get("round_trip_report.diagnostic.missing_keys")
            .copied(),
        Some("1")
    );
    assert_eq!(
        values
            .get("round_trip_report.diagnostic.invalid_lines")
            .copied(),
        Some("1")
    );
    assert_eq!(
        report.key_value_round_trip_report(&rows).status,
        PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripStatus::Valid
    );

    let mut stale_rows = rows.clone();
    stale_rows
        .iter_mut()
        .find(|row| row.key == "round_trip_report.status")
        .expect("report status row should be present")
        .value = "valid".to_string();
    let fixture_count_position = stale_rows
        .iter()
        .position(|row| row.key == "round_trip_report.count.fixtures")
        .expect("fixture count row should be present");
    stale_rows.remove(fixture_count_position);
    let duplicate_digest = stale_rows
        .iter()
        .find(|row| row.key == "round_trip_report.digest")
        .expect("report digest row should be present")
        .clone();
    stale_rows.push(duplicate_digest);
    let stale_report = report.key_value_round_trip_report(&stale_rows);
    assert_eq!(
        stale_report.status,
        PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripStatus::Invalid
    );
    assert!(stale_report.fail_closed);
    assert_eq!(
        stale_report.duplicate_keys,
        vec!["round_trip_report.digest".to_string()]
    );
    assert_eq!(
        stale_report.missing_keys,
        vec!["round_trip_report.count.fixtures".to_string()]
    );
    assert_eq!(
        stale_report.mismatched_value_keys,
        vec!["round_trip_report.status".to_string()]
    );

    let mut malformed_lines = report.key_value_lines();
    malformed_lines[0] = "malformed report line".to_string();
    let malformed_report = report.key_value_line_round_trip_report(&malformed_lines);
    assert_eq!(
        malformed_report.status,
        PetriNativeVerificationBundleHandoffReplayContractSurfaceRoundTripStatus::Invalid
    );
    assert!(malformed_report.fail_closed);
    assert_eq!(
        malformed_report.invalid_lines,
        vec!["0:malformed report line".to_string()]
    );
    assert!(
        malformed_report
            .missing_keys
            .contains(&"round_trip_report.schema".to_string())
    );
}

#[test]
fn native_shared_primitive_contract_carries_solver_artifact_byte_requirements() {
    let contract = petri_successor_trust_mc_chc_shared_primitive_contract_descriptor();
    let requirements = contract.production_required_artifact_requirements();

    assert_eq!(
        requirements,
        PETRI_SUCCESSOR_TRUST_MC_CHC_PRODUCTION_ACCEPTANCE_REQUIRED_ARTIFACT_REQUIREMENTS
    );
    assert_eq!(requirements.len(), contract.required_artifact_kinds.len());
    assert!(contract.production_requires_emitted_solver_artifacts());
    let roles: Vec<_> = contract
        .production_required_artifact_roles()
        .map(|role| role.code())
        .collect();
    assert_eq!(
        roles,
        vec!["solver_input", "replay_transcript", "solver_witness"]
    );
    let owner_suites: Vec<_> = contract.production_artifact_owner_suites().collect();
    assert_eq!(owner_suites, vec![NativeVerifierSuite::AY]);
    assert_eq!(
        contract.production_acceptance_report_api_name(),
        PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_ACCEPTANCE_REPORT_API_NAME
    );
    assert_eq!(
        contract.production_consumer_acceptance_api_name(),
        PETRI_SUCCESSOR_TRUST_MC_CHC_CONSUMER_ACCEPTANCE_API_NAME
    );

    let expected = [
        (
            NativeSharedPrimitiveArtifactRole::SolverInput,
            NativeEvidenceArtifactKind::TrustMcHornClauses,
            "solver_input",
        ),
        (
            NativeSharedPrimitiveArtifactRole::ReplayTranscript,
            NativeEvidenceArtifactKind::ReplayTranscript,
            "replay_transcript",
        ),
        (
            NativeSharedPrimitiveArtifactRole::SolverWitness,
            NativeEvidenceArtifactKind::TrustMcModel,
            "solver_witness",
        ),
    ];

    for (requirement, (role, kind, role_code)) in requirements.iter().zip(expected) {
        assert_eq!(requirement.role, role);
        assert_eq!(requirement.role.code(), role_code);
        assert_eq!(requirement.kind, kind);
        assert_eq!(requirement.digest_algorithm, ProofDigestAlgorithm::Sha256);
        assert_eq!(
            requirement.owner_suite,
            contract.production_acceptance_owner_suite()
        );
        assert!(requirement.requires_emitted_solver_artifact);
    }

    let required_kinds: Vec<_> = requirements
        .iter()
        .map(|requirement| requirement.kind)
        .collect();
    assert_eq!(required_kinds.as_slice(), contract.required_artifact_kinds);
}

#[test]
fn native_shared_primitive_contract_manifest_rows_are_schema_consumer_friendly() {
    let contract = petri_successor_trust_mc_chc_shared_primitive_contract_descriptor();
    let rows = contract.manifest_rows();
    let lines = contract.manifest_key_value_lines();
    let value = |key: &str| {
        rows.iter()
            .find(|row| row.key == key)
            .map(|row| row.value.as_str())
    };

    assert_eq!(
        value("manifest.schema"),
        Some(NATIVE_SHARED_PRIMITIVE_CONTRACT_MANIFEST_SCHEMA)
    );
    assert_eq!(value("manifest.schema_version"), Some("1"));
    assert_eq!(
        value("shared_primitive.schema"),
        Some(NATIVE_SHARED_PRIMITIVE_CONTRACT_SCHEMA)
    );
    assert_eq!(
        value("contract.schema"),
        Some(PETRI_SUCCESSOR_TRUST_MC_CHC_CONTRACT_SCHEMA)
    );
    assert_eq!(
        value("readiness_report.schema"),
        Some(PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_VALIDATION_READINESS_SCHEMA)
    );
    assert_eq!(value("verifier_suite"), Some("trust_mc"));
    assert_eq!(value("verification_mode"), Some("trust_mc.chc"));
    assert_eq!(value("production.requires_solver_acceptance"), Some("true"));
    assert_eq!(
        value("production.requires_emitted_solver_artifacts"),
        Some("true")
    );
    assert_eq!(
        value("production.acceptance_report_api"),
        Some(PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_ACCEPTANCE_REPORT_API_NAME)
    );
    assert_eq!(
        value("production.consumer_acceptance_api"),
        Some(PETRI_SUCCESSOR_TRUST_MC_CHC_CONSUMER_ACCEPTANCE_API_NAME)
    );
    assert_eq!(value("production.acceptance_owner_suite"), Some("ay"));
    assert_eq!(value("production.solver_evidence.owner_suite"), Some("ay"));
    assert_eq!(
        value("production.solver_evidence.capability_descriptor.schema"),
        Some(AY_SOLVER_CAPABILITY_DESCRIPTOR_SCHEMA)
    );
    assert_eq!(
        value("production.solver_evidence.capability_descriptor.schema_version"),
        Some("1")
    );
    assert_eq!(
        value("production.solver_evidence.model_blocking_clause.schema"),
        Some(AY_MODEL_BLOCKING_CLAUSE_SCHEMA)
    );
    assert_eq!(
        value("production.solver_evidence.model_blocking_clause_evidence.schema"),
        Some(AY_MODEL_BLOCKING_CLAUSE_EVIDENCE_SCHEMA)
    );
    assert_eq!(
        value("production.solver_evidence.solve_decision_profile_model_consumer.schema"),
        Some(AY_SOLVE_DECISION_PROFILE_MODEL_CONSUMER_SCHEMA)
    );
    assert_eq!(
        value("production.solver_evidence.acceptance_report_api"),
        Some(PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_ACCEPTANCE_REPORT_API_NAME)
    );
    assert_eq!(
        value("production.solver_evidence.consumer_acceptance_api"),
        Some(PETRI_SUCCESSOR_TRUST_MC_CHC_CONSUMER_ACCEPTANCE_API_NAME)
    );
    assert_eq!(
        value("production.artifact_requirement.0.role"),
        Some("solver_input")
    );
    assert_eq!(
        value("production.artifact_requirement.0.kind"),
        Some("trust_mc_horn_clauses")
    );
    assert_eq!(
        value("production.artifact_requirement.0.digest_algorithm"),
        Some("sha256")
    );
    assert_eq!(
        value("production.artifact_requirement.0.owner_suite"),
        Some("ay")
    );
    assert_eq!(
        value("production.artifact_requirement.0.requires_emitted_solver_artifact"),
        Some("true")
    );

    let artifact_roles: Vec<_> = rows
        .iter()
        .filter(|row| row.key == "production.artifact_role")
        .map(|row| row.value.as_str())
        .collect();
    assert_eq!(
        artifact_roles,
        vec!["solver_input", "replay_transcript", "solver_witness"]
    );
    let owner_suites: Vec<_> = rows
        .iter()
        .filter(|row| row.key == "production.artifact_owner_suite")
        .map(|row| row.value.as_str())
        .collect();
    assert_eq!(owner_suites, vec!["ay"]);
    assert_eq!(contract.manifest_row_count(), rows.len());
    assert_eq!(
        contract.manifest_key_value_text(),
        format!("{}\n", lines.join("\n"))
    );
    assert_eq!(
        contract.manifest_digest(),
        manifest_key_value_lines_digest(&lines)
    );
    assert_eq!(
        contract.manifest_sha256(),
        contract.manifest_digest().to_string()
    );
    assert_eq!(
        petri_successor_trust_mc_chc_shared_primitive_contract_manifest_rows(),
        rows
    );
    assert_eq!(
        petri_successor_trust_mc_chc_shared_primitive_contract_manifest_key_value_lines(),
        lines
    );
    assert_eq!(
        petri_successor_trust_mc_chc_shared_primitive_contract_manifest_key_value_text(),
        contract.manifest_key_value_text()
    );
    assert_eq!(
        petri_successor_trust_mc_chc_shared_primitive_contract_manifest_row_count(),
        rows.len()
    );
    assert_eq!(
        petri_successor_trust_mc_chc_shared_primitive_contract_manifest_digest(),
        contract.manifest_digest()
    );
    assert_eq!(
        petri_successor_trust_mc_chc_shared_primitive_contract_manifest_sha256(),
        contract.manifest_sha256()
    );
    for row in rows {
        assert!(
            !row.key.contains("petri"),
            "Petri-specific manifest key: {}",
            row.key
        );
        assert!(
            !row.key.contains("trust_mc"),
            "TrustMc-specific manifest key: {}",
            row.key
        );
        assert!(
            !row.key.contains("model_acceptance"),
            "legacy model-acceptance manifest key: {}",
            row.key
        );
    }
}

#[test]
fn native_shared_primitive_contract_manifest_rows_have_stable_order_and_escaping() {
    let contract = petri_successor_trust_mc_chc_shared_primitive_contract_descriptor();
    let rows = contract.manifest_rows();
    let keys: Vec<_> = rows.iter().map(|row| row.key.as_str()).collect();
    let expected_keys = [
        "manifest.schema",
        "manifest.schema_version",
        "contract.schema",
        "contract.schema_version",
        "shared_primitive.schema",
        "shared_primitive.schema_version",
        "formula.schema",
        "readiness_report.schema",
        "readiness_report.schema_version",
        "verifier_suite",
        "verification_mode",
        "production.requires_solver_acceptance",
        "production.requires_emitted_solver_artifacts",
        "production.acceptance_report_api",
        "production.consumer_acceptance_api",
        "production.acceptance_owner_suite",
        "production.solver_evidence.owner_suite",
        "production.solver_evidence.capability_descriptor.schema",
        "production.solver_evidence.capability_descriptor.schema_version",
        "production.solver_evidence.model_blocking_clause.schema",
        "production.solver_evidence.model_blocking_clause.schema_version",
        "production.solver_evidence.model_blocking_clause_evidence.schema",
        "production.solver_evidence.model_blocking_clause_evidence.schema_version",
        "production.solver_evidence.solve_decision_profile_model_consumer.schema",
        "production.solver_evidence.solve_decision_profile_model_consumer.schema_version",
        "production.solver_evidence.acceptance_report_api",
        "production.solver_evidence.consumer_acceptance_api",
        "production.artifact_role",
        "production.artifact_role",
        "production.artifact_role",
        "production.artifact_owner_suite",
        "production.artifact_requirement.0.role",
        "production.artifact_requirement.0.kind",
        "production.artifact_requirement.0.digest_algorithm",
        "production.artifact_requirement.0.owner_suite",
        "production.artifact_requirement.0.requires_emitted_solver_artifact",
        "production.artifact_requirement.1.role",
        "production.artifact_requirement.1.kind",
        "production.artifact_requirement.1.digest_algorithm",
        "production.artifact_requirement.1.owner_suite",
        "production.artifact_requirement.1.requires_emitted_solver_artifact",
        "production.artifact_requirement.2.role",
        "production.artifact_requirement.2.kind",
        "production.artifact_requirement.2.digest_algorithm",
        "production.artifact_requirement.2.owner_suite",
        "production.artifact_requirement.2.requires_emitted_solver_artifact",
    ];
    assert_eq!(keys.as_slice(), &expected_keys);

    let lines = contract.manifest_key_value_lines();
    assert_eq!(lines.len(), rows.len());
    assert_eq!(
        lines.first().map(String::as_str),
        Some("manifest.schema=trust_ir.native.shared_primitive_contract.manifest.v1")
    );
    assert_eq!(
        lines.get(1).map(String::as_str),
        Some("manifest.schema_version=1")
    );
    assert_eq!(
        &lines[27..31],
        &[
            "production.artifact_role=solver_input",
            "production.artifact_role=replay_transcript",
            "production.artifact_role=solver_witness",
            "production.artifact_owner_suite=ay",
        ]
    );
    for line in &lines {
        assert!(
            !line.contains('\n') && !line.contains('\r') && !line.contains('\t'),
            "manifest line contains raw control whitespace: {line:?}"
        );
    }

    let escaped = NativeSharedPrimitiveContractManifestRow::new("a=b", "line\n\ttab\\x=y\r\0");
    assert_eq!(escaped.escaped_key(), "a\\=b");
    assert_eq!(escaped.escaped_value(), "line\\n\\ttab\\\\x\\=y\\r\\u{0}");
    assert_eq!(
        escaped.to_key_value_line(),
        "a\\=b=line\\n\\ttab\\\\x\\=y\\r\\u{0}"
    );
}

#[test]
fn hardware_vector_contract_descriptors_emit_sidecar_ready_rows() {
    let descriptors = chc_x86_hardware_vector_contract_descriptors();
    assert_eq!(descriptors.len(), 4);
    assert_eq!(
        descriptors
            .iter()
            .map(|descriptor| descriptor.contract_name)
            .collect::<Vec<_>>(),
        vec![
            "chc_x86.v4_i32",
            "chc_x86.v2_i64",
            "chc_x86.v16_i8",
            "chc_x86.v8_i16"
        ]
    );

    let v4 = CHC_X86_V4_I32_HARDWARE_VECTOR_CONTRACT_DESCRIPTOR;
    assert_eq!(v4.status_code(), "available");
    assert_eq!(v4.reason_code(), "canonical_contract");
    assert!(!v4.fail_closed());
    assert_eq!(v4.value_ty, "<4 x i32>");
    assert_eq!(v4.logical_mask_ty, "<4 x bool>");
    assert_eq!(v4.physical_mask_ty, "<4 x i32>");
    assert_eq!(v4.element_bits, 32);
    assert_eq!(v4.lane_count, 4);
    assert_eq!(v4.total_bits, 128);
    assert_eq!(
        v4.operations,
        CHC_X86_V4_I32_HARDWARE_VECTOR_CONTRACT_OPERATIONS
    );

    let v16 = CHC_X86_V16_I8_HARDWARE_VECTOR_CONTRACT_DESCRIPTOR;
    assert_eq!(v16.status_code(), "available");
    assert!(!v16.fail_closed());
    assert_eq!(v16.value_ty, "<16 x i8>");
    assert_eq!(v16.logical_mask_ty, "<16 x bool>");
    assert_eq!(v16.physical_mask_ty, "<16 x i8>");
    assert_eq!(v16.element_bits, 8);
    assert_eq!(v16.lane_count, 16);
    assert_eq!(v16.total_bits, 128);
    assert_eq!(
        v16.operations,
        CHC_X86_V16_I8_HARDWARE_VECTOR_CONTRACT_OPERATIONS
    );

    let v8 = CHC_X86_V8_I16_HARDWARE_VECTOR_CONTRACT_DESCRIPTOR;
    assert_eq!(v8.status_code(), "available");
    assert!(!v8.fail_closed());
    assert_eq!(v8.value_ty, "<8 x i16>");
    assert_eq!(v8.logical_mask_ty, "<8 x bool>");
    assert_eq!(v8.physical_mask_ty, "<8 x i16>");
    assert_eq!(v8.element_bits, 16);
    assert_eq!(v8.lane_count, 8);
    assert_eq!(v8.total_bits, 128);
    assert_eq!(
        v8.operations,
        CHC_X86_V8_I16_HARDWARE_VECTOR_CONTRACT_OPERATIONS
    );

    let v4_rows = v4.manifest_rows();
    let keys = v4_rows
        .iter()
        .map(|row| row.key.as_str())
        .collect::<Vec<_>>();
    let unique_keys = keys.iter().copied().collect::<BTreeSet<_>>();
    assert_eq!(
        unique_keys.len(),
        keys.len(),
        "hardware vector descriptor manifest keys must be unique"
    );
    let expected_key_prefix = [
        "hardware_vector_contract.manifest.schema",
        "hardware_vector_contract.manifest.schema_version",
        "hardware_vector_contract.schema",
        "hardware_vector_contract.schema_version",
        "hardware_vector_contract.source.package",
        "hardware_vector_contract.target.family",
        "hardware_vector_contract.hardware_model",
        "hardware_vector_contract.contract.name",
        "hardware_vector_contract.status",
        "hardware_vector_contract.reason",
        "hardware_vector_contract.fail_closed",
        "hardware_vector_contract.value_ty",
        "hardware_vector_contract.logical_mask_ty",
        "hardware_vector_contract.physical_mask_ty",
        "hardware_vector_contract.element_ty",
        "hardware_vector_contract.element_bits",
        "hardware_vector_contract.lane_count",
        "hardware_vector_contract.total_bits",
        "hardware_vector_contract.mask_semantics",
        "hardware_vector_contract.operation_count",
        "hardware_vector_contract.operation.0",
        "hardware_vector_contract.operation.1",
        "hardware_vector_contract.operation.2",
        "hardware_vector_contract.operation.3",
        "hardware_vector_contract.operation.4",
        "hardware_vector_contract.operation.5",
        "hardware_vector_contract.operation.6",
        "hardware_vector_contract.operation.7",
        "hardware_vector_contract.operation.8",
        "hardware_vector_contract.operation.9",
        "hardware_vector_contract.operation.10",
        "hardware_vector_contract.operation.11",
        "hardware_vector_contract.operation.12",
        "hardware_vector_contract.operation.13",
        "hardware_vector_contract.operation.14",
        "hardware_vector_contract.operation.15",
        "hardware_vector_contract.operation.16",
        "hardware_vector_contract.operation.17",
        "hardware_vector_contract.operation.18",
        "hardware_vector_contract.operation.19",
        "hardware_vector_contract.operation.20",
        "hardware_vector_contract.operation.21",
        "hardware_vector_contract.operation.22",
        "hardware_vector_contract.operation.binop.mul.status",
        "hardware_vector_contract.operation.binop.mul.reason",
        "hardware_vector_contract.operation.binop.mul.fail_closed",
        "hardware_vector_contract.operation.binop.mul.feature_guard",
        "hardware_vector_contract.operation.binop.mul.native_instruction",
        "hardware_vector_contract.operation.binop.mul.semantics",
        "hardware_vector_contract.operation.pack_lanes.status",
        "hardware_vector_contract.operation.pack_lanes.reason",
        "hardware_vector_contract.operation.pack_lanes.fail_closed",
        "hardware_vector_contract.operation.pack_lanes.trust_cg_lir_opcode",
        "hardware_vector_contract.operation.pack_lanes.feature_guard",
        "hardware_vector_contract.operation.pack_lanes.native_instructions",
        "hardware_vector_contract.operation.pack_lanes.semantics",
        "hardware_vector_contract.trust_cg_x86_vector.generic_feature_guard",
        "hardware_vector_contract.trust_cg_x86_vector.current_feature_guard",
        "hardware_vector_contract.trust_cg_x86_vector.host_jit_feature_guard",
    ];
    assert_eq!(
        &keys[..expected_key_prefix.len()],
        &expected_key_prefix,
        "descriptor identity and legacy pack/mul row order must remain stable"
    );

    let lines = v4.manifest_key_value_lines();
    assert_eq!(v4.manifest_row_count(), v4_rows.len());
    assert_eq!(
        v4.manifest_digest(),
        manifest_key_value_lines_digest(&lines)
    );
    assert_eq!(v4.manifest_sha256(), v4.manifest_digest().to_string());
    assert_eq!(
        lines.first().map(String::as_str),
        Some(
            "hardware_vector_contract.manifest.schema=trust_ir.hardware.vector_contract.manifest.v1"
        )
    );
    assert!(lines.contains(&"hardware_vector_contract.status=available".to_string()));
    assert!(lines.contains(&"hardware_vector_contract.reason=canonical_contract".to_string()));
    assert!(lines.contains(&"hardware_vector_contract.fail_closed=false".to_string()));
    assert!(lines.contains(&"hardware_vector_contract.value_ty=<4 x i32>".to_string()));
    assert!(lines.contains(
            &"hardware_vector_contract.mask_semantics=compare_produced_logical_bool_masks;mask_to_bits_compare_masks_only;integer_masks_via_compare_to_zero;arbitrary_bool_constants_require_explicit_trust_cg_support".to_string()
        ));
    assert!(lines.contains(&"hardware_vector_contract.operation.3=pack_lanes".to_string()));
    assert!(lines.contains(&"hardware_vector_contract.operation.7=binop.mul".to_string()));
    assert!(lines.contains(
        &"hardware_vector_contract.operation.binop.mul.feature_guard=x86.sse4.1".to_string()
    ));
    assert!(lines.contains(
        &"hardware_vector_contract.operation.binop.mul.native_instruction=pmulld".to_string()
    ));
    assert!(lines.contains(
            &"hardware_vector_contract.operation.binop.mul.semantics=lane_wise_i32_wrapping_low_32_bits".to_string()
        ));
    assert!(lines.contains(&"hardware_vector_contract.operation.10=extract_element".to_string()));
    assert!(lines.contains(&"hardware_vector_contract.operation.11=insert_element".to_string()));
    assert!(lines.contains(&"hardware_vector_contract.operation.16=binop.shl".to_string()));
    assert!(lines.contains(&"hardware_vector_contract.operation.17=binop.lshr".to_string()));
    assert!(lines.contains(&"hardware_vector_contract.operation.18=binop.ashr".to_string()));
    assert!(lines.contains(&"hardware_vector_contract.operation.19=icmp.ult".to_string()));
    assert!(lines.contains(&"hardware_vector_contract.operation.20=icmp.ule".to_string()));
    assert!(lines.contains(&"hardware_vector_contract.operation.21=icmp.ugt".to_string()));
    assert!(lines.contains(&"hardware_vector_contract.operation.22=icmp.uge".to_string()));
    assert!(
        lines.contains(&"hardware_vector_contract.operation.icmp.ult.status=deferred".to_string())
    );
    assert!(lines.contains(
            &"hardware_vector_contract.operation.icmp.ult.reason=unsigned_vector_compare_proof_blocked"
                .to_string()
        ));
    assert!(
        lines.contains(&"hardware_vector_contract.operation.icmp.ult.fail_closed=true".to_string())
    );
    assert!(lines.contains(
            &"hardware_vector_contract.operation.icmp.ult.consumer_policy=fail_closed_reject_lowering"
                .to_string()
        ));
    assert!(
        lines
            .contains(&"hardware_vector_contract.operation.binop.add.status=available".to_string())
    );
    assert!(
        lines.contains(
            &"hardware_vector_contract.operation.pack_lanes.trust_cg_lir_opcode=V4I32PackLanes"
                .to_string()
        )
    );
    assert!(lines.contains(
        &"hardware_vector_contract.operation.pack_lanes.feature_guard=x86.sse2".to_string()
    ));
    assert!(lines.contains(
            &"hardware_vector_contract.operation.pack_lanes.native_instructions=movd_to_xmm;punpckldq;punpcklqdq;pshufd_same_lane_broadcast".to_string()
        ));
    assert!(lines.contains(
        &"hardware_vector_contract.operation.binop.add.feature_guard=x86.sse2".to_string()
    ));
    assert!(lines.contains(
        &"hardware_vector_contract.operation.binop.add.native_instructions=paddd".to_string()
    ));
    assert!(lines.contains(
        &"hardware_vector_contract.operation.binop.sub.native_instructions=psubd".to_string()
    ));
    assert!(lines.contains(
            &"hardware_vector_contract.operation.insert_element.trust_cg_lir_opcode=V4I32InsertLane"
                .to_string()
        ));
    assert!(lines.contains(
        &"hardware_vector_contract.operation.insert_element.feature_guard=x86.sse2".to_string()
    ));
    assert!(lines.contains(
            &"hardware_vector_contract.operation.insert_element.native_instructions=movd_to_xmm;movd_from_xmm;pshufd;punpckldq;punpcklqdq;pxor_zero_base".to_string()
        ));
    assert!(lines.contains(
            &"hardware_vector_contract.operation.insert_element.semantics=constant_lane_sse2_rebuild_without_pinsrd_or_stack".to_string()
        ));
    assert!(lines.contains(
            &"hardware_vector_contract.operation.binop.shl.native_instructions=movd_from_xmm;pshufd;mov_to_ecx;shl_rr_or_shr_rr_or_sar_rr;movd_to_xmm;punpckldq;punpcklqdq".to_string()
        ));
    assert!(lines.contains(
        &"hardware_vector_contract.operation.binop.lshr.feature_guard=x86.sse2".to_string()
    ));
    assert!(lines.contains(
            &"hardware_vector_contract.operation.binop.ashr.composition=lane_count_4;each_rhs_lane_in_0_31;x86_shift_count_masking_not_source_semantics".to_string()
        ));
    assert!(lines.contains(
            &"hardware_vector_contract.trust_cg_x86_vector.current_feature_guard=x86.sse4.1+x86.sse4.2"
                .to_string()
        ));
    assert!(lines.contains(
            &"hardware_vector_contract.trust_cg_x86_vector.host_jit_feature_guard=runtime_detected_optional_x86.sse4.1+x86.sse4.2".to_string()
        ));
    for line in &lines {
        assert!(
            !line.contains('\n') && !line.contains('\r') && !line.contains('\t'),
            "hardware vector manifest line contains raw control whitespace: {line:?}"
        );
    }
    assert_eq!(
        v4.manifest_key_value_text(),
        format!("{}\n", lines.join("\n"))
    );
}

fn assert_operation_contract_rows_cover_listed_operations(
    descriptor: HardwareVectorContractDescriptor,
    rows: &[HardwareVectorOperationContractRow],
    status_rows: &[HardwareVectorOperationStatusRow],
) {
    let operations = descriptor.operations;
    let row_operations = rows.iter().map(|row| row.operation).collect::<Vec<_>>();
    assert_eq!(
        row_operations.as_slice(),
        &operations[..row_operations.len()],
        "available contract rows must preserve descriptor operation order"
    );

    let unique_operations = row_operations.iter().copied().collect::<BTreeSet<_>>();
    assert_eq!(
        unique_operations.len(),
        row_operations.len(),
        "per-operation contract rows must not duplicate operation names"
    );

    let status_only_operations = status_rows
        .iter()
        .map(|row| row.operation)
        .collect::<Vec<_>>();
    let unique_status_only_operations = status_only_operations
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    assert_eq!(
        unique_status_only_operations.len(),
        status_only_operations.len(),
        "status-only rows must not duplicate operation names"
    );

    for operation in operations {
        let has_available_row = rows.iter().any(|row| row.operation == *operation)
            || descriptor.emits_legacy_operation_rows(operation);
        let status_only_row = status_rows
            .iter()
            .find(|status_row| status_row.operation == *operation);
        assert!(
            has_available_row || status_only_row.is_some(),
            "{} operation {operation} must have an available row or a fail-closed status row",
            descriptor.contract_name
        );
        assert!(
            !has_available_row || status_only_row.is_none(),
            "{} operation {operation} must not be both available and status-only",
            descriptor.contract_name
        );
    }

    for row in rows {
        assert!(
            operations.contains(&row.operation),
            "{} available row {} must be listed by the descriptor",
            descriptor.contract_name,
            row.operation
        );
        assert!(
            !row.feature_guard.is_empty(),
            "operation {} must publish a feature guard",
            row.operation
        );
        assert!(
            !row.native_instructions.is_empty(),
            "operation {} must publish native instruction coverage",
            row.operation
        );
        assert!(
            !row.semantics.is_empty(),
            "operation {} must publish semantics",
            row.operation
        );
    }

    for row in status_rows {
        assert!(
            operations.contains(&row.operation),
            "{} status-only row {} must be listed by the descriptor",
            descriptor.contract_name,
            row.operation
        );
        assert!(
            row.fail_closed(),
            "{} status-only row {} must fail closed",
            descriptor.contract_name,
            row.operation
        );
        assert_ne!(
            row.status,
            HardwareVectorContractStatus::Available,
            "{} status-only row {} must not claim availability",
            descriptor.contract_name,
            row.operation
        );
    }
}

#[test]
fn chc_x86_operation_contract_rows_cover_all_listed_operations() {
    assert_operation_contract_rows_cover_listed_operations(
        CHC_X86_V4_I32_HARDWARE_VECTOR_CONTRACT_DESCRIPTOR,
        CHC_X86_V4_I32_OPERATION_CONTRACT_ROWS,
        CHC_X86_V4_I32_OPERATION_STATUS_ROWS,
    );
    assert_operation_contract_rows_cover_listed_operations(
        CHC_X86_V2_I64_HARDWARE_VECTOR_CONTRACT_DESCRIPTOR,
        CHC_X86_V2_I64_OPERATION_CONTRACT_ROWS,
        CHC_X86_V2_I64_OPERATION_STATUS_ROWS,
    );
    assert_operation_contract_rows_cover_listed_operations(
        CHC_X86_V16_I8_HARDWARE_VECTOR_CONTRACT_DESCRIPTOR,
        CHC_X86_V16_I8_OPERATION_CONTRACT_ROWS,
        CHC_X86_V16_I8_OPERATION_STATUS_ROWS,
    );
    assert_operation_contract_rows_cover_listed_operations(
        CHC_X86_V8_I16_HARDWARE_VECTOR_CONTRACT_DESCRIPTOR,
        CHC_X86_V8_I16_OPERATION_CONTRACT_ROWS,
        CHC_X86_V8_I16_OPERATION_STATUS_ROWS,
    );
}

#[test]
fn chc_x86_manifest_covers_every_vector_icmp_op_or_fails_closed() {
    let icmp_ops = [
        ICmpOp::Eq,
        ICmpOp::Ne,
        ICmpOp::Ult,
        ICmpOp::Ule,
        ICmpOp::Ugt,
        ICmpOp::Uge,
        ICmpOp::Slt,
        ICmpOp::Sle,
        ICmpOp::Sgt,
        ICmpOp::Sge,
    ];
    let descriptors = chc_x86_hardware_vector_contract_descriptors();

    for descriptor in descriptors {
        let rows = descriptor.manifest_rows();
        let value_for = |key: &str| {
            rows.iter()
                .find(|row| row.key == key)
                .map(|row| row.value.as_str())
        };

        for op in icmp_ops {
            let operation = format!("icmp.{op}");
            assert!(
                descriptor.operations.contains(&operation.as_str()),
                "{} must explicitly list vector ICmp operation {operation}",
                descriptor.contract_name
            );

            let prefix = format!("hardware_vector_contract.operation.{operation}");
            let status = value_for(&format!("{prefix}.status"))
                .expect("each listed ICmp operation must publish a status");
            let fail_closed = value_for(&format!("{prefix}.fail_closed"))
                .expect("each listed ICmp operation must publish fail_closed");
            let is_unsigned = matches!(op, ICmpOp::Ult | ICmpOp::Ule | ICmpOp::Ugt | ICmpOp::Uge);

            if is_unsigned {
                let expected_status = if descriptor.contract_name == "chc_x86.v4_i32" {
                    "deferred"
                } else {
                    "unavailable"
                };
                let expected_reason = if descriptor.contract_name == "chc_x86.v4_i32" {
                    "unsigned_vector_compare_proof_blocked"
                } else {
                    "unsigned_vector_compare_unavailable"
                };
                assert_eq!(
                    status, expected_status,
                    "{} {operation} must not claim proven TrustIr lowering",
                    descriptor.contract_name
                );
                assert_eq!(
                    value_for(&format!("{prefix}.reason")),
                    Some(expected_reason)
                );
                assert_eq!(fail_closed, "true");
                assert_eq!(
                    value_for(&format!("{prefix}.consumer_policy")),
                    Some(CHC_X86_UNSIGNED_VECTOR_COMPARE_FAIL_CLOSED_POLICY)
                );
                assert_eq!(value_for(&format!("{prefix}.feature_guard")), None);
                assert_eq!(value_for(&format!("{prefix}.native_instructions")), None);
                assert_eq!(value_for(&format!("{prefix}.semantics")), None);
            } else {
                assert_eq!(status, "available");
                assert_eq!(
                    value_for(&format!("{prefix}.reason")),
                    Some("canonical_contract")
                );
                assert_eq!(fail_closed, "false");
                assert!(value_for(&format!("{prefix}.feature_guard")).is_some());
                assert!(value_for(&format!("{prefix}.native_instructions")).is_some());
                assert!(value_for(&format!("{prefix}.semantics")).is_some());
            }
        }
    }
}

#[test]
fn chc_x86_narrow_compare_mask_contracts_are_sse2_signed_only() {
    let narrow_contracts = [
        (
            CHC_X86_V16_I8_HARDWARE_VECTOR_CONTRACT_DESCRIPTOR,
            CHC_X86_V16_I8_OPERATION_CONTRACT_ROWS,
            CHC_X86_V16_I8_OPERATION_STATUS_ROWS,
            "pcmpeqb",
            "pcmpgtb",
            CHC_X86_V16_I8_MASK_TO_BITS_SEMANTICS,
        ),
        (
            CHC_X86_V8_I16_HARDWARE_VECTOR_CONTRACT_DESCRIPTOR,
            CHC_X86_V8_I16_OPERATION_CONTRACT_ROWS,
            CHC_X86_V8_I16_OPERATION_STATUS_ROWS,
            "pcmpeqw",
            "pcmpgtw",
            CHC_X86_V8_I16_MASK_TO_BITS_SEMANTICS,
        ),
    ];
    let unsupported_unsigned = ["icmp.ult", "icmp.ule", "icmp.ugt", "icmp.uge"];

    for (descriptor, rows, status_rows, eq_instruction, gt_instruction, mask_semantics) in
        narrow_contracts
    {
        assert_eq!(descriptor.status_code(), "available");
        assert!(!descriptor.fail_closed());
        assert_eq!(descriptor.total_bits, 128);
        let row_operations = rows.iter().map(|row| row.operation).collect::<Vec<_>>();
        assert_eq!(
            row_operations.as_slice(),
            &descriptor.operations[..row_operations.len()]
        );
        for op in unsupported_unsigned {
            assert!(
                descriptor.operations.contains(&op),
                "{} must explicitly list unsigned compare operation {op}",
                descriptor.contract_name
            );
            let status_row = status_rows
                .iter()
                .find(|row| row.operation == op)
                .expect("narrow unsigned compare must have a fail-closed status row");
            assert_eq!(status_row.status, HardwareVectorContractStatus::Unavailable);
            assert_eq!(
                status_row.reason,
                HardwareVectorContractReason::UnsignedVectorCompareUnavailable
            );
            assert!(status_row.fail_closed());
        }

        for row in rows {
            assert_eq!(
                row.feature_guard, CHC_X86_TRUST_CG_GENERIC_VECTOR_FEATURE_GUARD,
                "{} {} must stay SSE2-only",
                descriptor.contract_name, row.operation
            );
            assert_ne!(
                row.feature_guard, CHC_X86_V4_I32_MUL_FEATURE_GUARD,
                "{} {} must not require SSE4.1",
                descriptor.contract_name, row.operation
            );
            assert_ne!(
                row.feature_guard, CHC_X86_V2_I64_ICMP_SIGNED_ORDER_FEATURE_GUARD,
                "{} {} must not require SSE4.2",
                descriptor.contract_name, row.operation
            );
            assert!(
                !unsupported_unsigned.contains(&row.operation),
                "{} must not publish available unsigned row {}",
                descriptor.contract_name,
                row.operation
            );
        }

        let manifest_rows = descriptor.manifest_rows();
        for op in unsupported_unsigned {
            let prefix = format!("hardware_vector_contract.operation.{op}");
            let value_for = |suffix: &str| {
                let key = format!("{prefix}.{suffix}");
                manifest_rows
                    .iter()
                    .find(|row| row.key == key)
                    .map(|row| row.value.as_str())
            };
            assert_eq!(value_for("status"), Some("unavailable"));
            assert_eq!(
                value_for("reason"),
                Some("unsigned_vector_compare_unavailable")
            );
            assert_eq!(value_for("fail_closed"), Some("true"));
            assert_eq!(
                value_for("consumer_policy"),
                Some(CHC_X86_UNSIGNED_VECTOR_COMPARE_FAIL_CLOSED_POLICY)
            );
            assert_eq!(value_for("feature_guard"), None);
            assert_eq!(value_for("native_instructions"), None);
            assert_eq!(value_for("semantics"), None);
        }

        let eq = rows
            .iter()
            .find(|row| row.operation == "icmp.eq")
            .expect("narrow contract must publish eq");
        assert_eq!(eq.native_instructions, eq_instruction);
        assert_eq!(
            eq.composition,
            format!("{eq_instruction}(lhs,rhs)").as_str()
        );

        let slt = rows
            .iter()
            .find(|row| row.operation == "icmp.slt")
            .expect("narrow contract must publish slt");
        assert_eq!(slt.native_instructions, gt_instruction);
        assert_eq!(
            slt.composition,
            format!("{gt_instruction}(rhs,lhs)").as_str()
        );

        let mask_to_bits = rows
            .iter()
            .find(|row| row.operation == "vector.mask_to_bits")
            .expect("narrow contract must publish vector.mask_to_bits");
        assert_eq!(mask_to_bits.native_instructions, "pmovmskb");
        assert_eq!(mask_to_bits.semantics, mask_semantics);
        assert!(
            mask_to_bits.composition.contains("lane0_to_bit0")
                || mask_to_bits
                    .composition
                    .contains("compact_duplicate_byte_bits"),
            "{} mask extraction must document lane-to-bit ordering",
            descriptor.contract_name
        );
    }
}

#[test]
fn chc_x86_hardware_vector_contract_manifest_is_deterministic() {
    let rows = chc_x86_hardware_vector_contract_manifest_rows();
    let lines = chc_x86_hardware_vector_contract_manifest_key_value_lines();
    let keys = rows
        .iter()
        .map(|row| row.key.as_str())
        .collect::<BTreeSet<_>>();

    assert_eq!(lines.len(), rows.len());
    assert_eq!(
        keys.len(),
        rows.len(),
        "hardware vector contract-set manifest keys must be unique"
    );
    assert_eq!(
        chc_x86_hardware_vector_contract_manifest_row_count(),
        rows.len()
    );
    assert_eq!(
        chc_x86_hardware_vector_contract_manifest_digest(),
        manifest_key_value_lines_digest(&lines)
    );
    assert_eq!(
        chc_x86_hardware_vector_contract_manifest_sha256(),
        chc_x86_hardware_vector_contract_manifest_digest().to_string()
    );
    assert!(chc_x86_hardware_vector_contract_manifest_sha256().starts_with("sha256:"));
    assert_eq!(
        lines.first().map(String::as_str),
        Some(
            "hardware_vector_contract_set.manifest.schema=trust_ir.hardware.vector_contract.manifest.v1"
        )
    );
    assert_eq!(
        lines.get(3).map(String::as_str),
        Some("hardware_vector_contract_set.name=chc_x86")
    );
    assert!(lines.contains(&"hardware_vector_contract_set.contract_count=4".to_string()));
    assert!(lines.contains(
        &"hardware_vector_contract_set.contract.0.contract.name=chc_x86.v4_i32".to_string()
    ));
    assert!(lines.contains(
        &"hardware_vector_contract_set.contract.1.contract.name=chc_x86.v2_i64".to_string()
    ));
    assert!(lines.contains(
        &"hardware_vector_contract_set.contract.2.contract.name=chc_x86.v16_i8".to_string()
    ));
    assert!(lines.contains(
        &"hardware_vector_contract_set.contract.3.contract.name=chc_x86.v8_i16".to_string()
    ));
    assert!(
        lines.contains(&"hardware_vector_contract_set.contract.0.status=available".to_string())
    );
    assert!(
        lines.contains(&"hardware_vector_contract_set.contract.1.fail_closed=false".to_string())
    );
    assert!(
        lines.contains(&"hardware_vector_contract_set.contract.2.fail_closed=false".to_string())
    );
    assert!(
        lines.contains(&"hardware_vector_contract_set.contract.3.fail_closed=false".to_string())
    );
    assert!(
        lines.contains(
            &"hardware_vector_contract_set.contract.0.operation.3=pack_lanes".to_string()
        )
    );
    assert!(
        lines
            .contains(&"hardware_vector_contract_set.contract.0.operation.7=binop.mul".to_string())
    );
    assert!(
        lines.contains(
            &"hardware_vector_contract_set.contract.0.operation.binop.mul.feature_guard=x86.sse4.1"
                .to_string()
        )
    );
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.0.operation.binop.mul.native_instruction=pmulld"
                .to_string()
        ));
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.0.operation.binop.mul.semantics=lane_wise_i32_wrapping_low_32_bits"
                .to_string()
        ));
    assert!(lines.contains(
        &"hardware_vector_contract_set.contract.0.operation.10=extract_element".to_string()
    ));
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.0.operation.pack_lanes.native_instructions=movd_to_xmm;punpckldq;punpcklqdq;pshufd_same_lane_broadcast"
                .to_string()
        ));
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.0.operation.binop.add.native_instructions=paddd"
                .to_string()
        ));
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.0.operation.binop.sub.native_instructions=psubd"
                .to_string()
        ));
    assert!(
        lines.contains(
            &"hardware_vector_contract_set.contract.0.operation.16=binop.shl".to_string()
        )
    );
    assert!(
        lines.contains(
            &"hardware_vector_contract_set.contract.0.operation.17=binop.lshr".to_string()
        )
    );
    assert!(
        lines.contains(
            &"hardware_vector_contract_set.contract.0.operation.18=binop.ashr".to_string()
        )
    );
    assert!(
        lines
            .contains(&"hardware_vector_contract_set.contract.0.operation.19=icmp.ult".to_string())
    );
    assert!(
        lines
            .contains(&"hardware_vector_contract_set.contract.0.operation.22=icmp.uge".to_string())
    );
    assert!(lines.contains(
        &"hardware_vector_contract_set.contract.0.operation.icmp.ult.status=deferred".to_string()
    ));
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.0.operation.icmp.ult.reason=unsigned_vector_compare_proof_blocked"
                .to_string()
        ));
    assert!(lines.contains(
        &"hardware_vector_contract_set.contract.0.operation.icmp.ult.fail_closed=true".to_string()
    ));
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.0.operation.icmp.ult.consumer_policy=fail_closed_reject_lowering"
                .to_string()
        ));
    assert!(
        lines.contains(
            &"hardware_vector_contract_set.contract.0.operation.binop.shl.feature_guard=x86.sse2"
                .to_string()
        )
    );
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.0.operation.binop.lshr.native_instructions=movd_from_xmm;pshufd;mov_to_ecx;shl_rr_or_shr_rr_or_sar_rr;movd_to_xmm;punpckldq;punpcklqdq"
                .to_string()
        ));
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.0.operation.binop.ashr.composition=lane_count_4;each_rhs_lane_in_0_31;x86_shift_count_masking_not_source_semantics"
                .to_string()
        ));
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.0.operation.insert_element.feature_guard=x86.sse2"
                .to_string()
        ));
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.0.operation.insert_element.native_instructions=movd_to_xmm;movd_from_xmm;pshufd;punpckldq;punpcklqdq;pxor_zero_base"
                .to_string()
        ));
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.1.operation.pack_lanes.native_instructions=movq_to_xmm;punpcklqdq;pshufd_same_lane_broadcast"
                .to_string()
        ));
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.1.operation.binop.add.trust_cg_lir_opcode=V2I64Add"
                .to_string()
        ));
    assert!(
        lines.contains(
            &"hardware_vector_contract_set.contract.1.operation.binop.add.feature_guard=x86.sse2"
                .to_string()
        )
    );
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.1.operation.binop.add.native_instructions=paddq"
                .to_string()
        ));
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.1.operation.binop.sub.trust_cg_lir_opcode=V2I64Sub"
                .to_string()
        ));
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.1.operation.binop.sub.native_instructions=psubq"
                .to_string()
        ));
    assert!(
        lines.contains(
            &"hardware_vector_contract_set.contract.1.operation.pack_lanes.feature_guard=x86.sse2"
                .to_string()
        )
    );
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.1.trust_cg_x86_vector.generic_feature_guard=x86.sse2"
                .to_string()
        ));
    assert!(!lines.contains(
        &"hardware_vector_contract_set.contract.1.operation.8=extract_element".to_string()
    ));
    assert!(lines.contains(
        &"hardware_vector_contract_set.contract.1.operation.9=insert_element".to_string()
    ));
    assert!(
        lines
            .contains(&"hardware_vector_contract_set.contract.1.operation.10=icmp.slt".to_string())
    );
    assert!(lines.contains(
        &"hardware_vector_contract_set.contract.1.operation.14=extract_element".to_string()
    ));
    assert!(
        lines
            .contains(&"hardware_vector_contract_set.contract.1.operation.15=icmp.ult".to_string())
    );
    assert!(
        lines.contains(
            &"hardware_vector_contract_set.contract.1.operation.icmp.ult.status=unavailable"
                .to_string()
        )
    );
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.1.operation.icmp.ult.reason=unsigned_vector_compare_unavailable"
                .to_string()
        ));
    assert!(
        lines.contains(
            &"hardware_vector_contract_set.contract.1.operation.icmp.eq.feature_guard=x86.sse4.1"
                .to_string()
        )
    );
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.1.operation.icmp.eq.native_instructions=pcmpeqq"
                .to_string()
        ));
    assert!(
        lines.contains(
            &"hardware_vector_contract_set.contract.1.operation.icmp.ne.feature_guard=x86.sse4.1"
                .to_string()
        )
    );
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.1.operation.icmp.ne.composition=not(pcmpeqq(lhs,rhs))"
                .to_string()
        ));
    assert!(
        lines.contains(
            &"hardware_vector_contract_set.contract.1.operation.icmp.slt.feature_guard=x86.sse4.2"
                .to_string()
        )
    );
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.1.operation.icmp.slt.composition=pcmpgtq(rhs,lhs)"
                .to_string()
        ));
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.1.operation.icmp.sle.native_instructions=pcmpgtq;pcmpeqq;por"
                .to_string()
        ));
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.1.operation.icmp.sgt.composition=pcmpgtq(lhs,rhs)"
                .to_string()
        ));
    assert!(
        lines.contains(
            &"hardware_vector_contract_set.contract.1.operation.icmp.sge.feature_guard=x86.sse4.2"
                .to_string()
        )
    );
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.1.operation.insert_element.trust_cg_lir_opcode=V2I64InsertLane"
                .to_string()
        ));
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.1.operation.insert_element.feature_guard=x86.sse2"
                .to_string()
        ));
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.1.operation.insert_element.native_instructions=movq_to_xmm;pshufd;punpcklqdq;pxor_zero_base"
                .to_string()
        ));
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.1.operation.insert_element.semantics=constant_lane_sse2_rebuild_without_pinsrq_or_stack"
                .to_string()
        ));
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.1.operation.extract_element.trust_cg_lir_opcode=V2I64ExtractLane"
                .to_string()
        ));
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.1.operation.extract_element.native_instructions=pshufd;movq_from_xmm"
                .to_string()
        ));
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.1.operation.extract_element.semantics=constant_lane_sse2_extract_without_pextrq_or_stack"
                .to_string()
        ));
    assert!(
        lines.contains(&"hardware_vector_contract_set.contract.2.value_ty=<16 x i8>".to_string())
    );
    assert!(lines.contains(
        &"hardware_vector_contract_set.contract.2.logical_mask_ty=<16 x bool>".to_string()
    ));
    assert!(
        lines.contains(&"hardware_vector_contract_set.contract.2.operation.0=icmp.eq".to_string())
    );
    assert!(lines.contains(
        &"hardware_vector_contract_set.contract.2.operation.6=vector.mask_to_bits".to_string()
    ));
    assert!(
        lines.contains(&"hardware_vector_contract_set.contract.2.operation.7=icmp.ult".to_string())
    );
    assert!(
        lines.contains(
            &"hardware_vector_contract_set.contract.2.operation.icmp.ult.status=unavailable"
                .to_string()
        )
    );
    assert!(
        lines.contains(
            &"hardware_vector_contract_set.contract.2.operation.icmp.eq.feature_guard=x86.sse2"
                .to_string()
        )
    );
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.2.operation.icmp.eq.native_instructions=pcmpeqb"
                .to_string()
        ));
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.2.operation.icmp.ne.composition=not(pcmpeqb(lhs,rhs))"
                .to_string()
        ));
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.2.operation.icmp.slt.composition=pcmpgtb(rhs,lhs)"
                .to_string()
        ));
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.2.operation.icmp.sle.native_instructions=pcmpgtb;pcmpeqb;por"
                .to_string()
        ));
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.2.operation.icmp.sgt.composition=pcmpgtb(lhs,rhs)"
                .to_string()
        ));
    assert!(lines.contains(
            &format!(
                "hardware_vector_contract_set.contract.2.operation.vector.mask_to_bits.semantics={CHC_X86_V16_I8_MASK_TO_BITS_SEMANTICS}"
            )
        ));
    assert!(lines.contains(
            &format!(
                "hardware_vector_contract_set.contract.2.operation.vector.mask_to_bits.composition={CHC_X86_V16_I8_MASK_TO_BITS_COMPOSITION}"
            )
        ));
    assert!(
        lines.contains(&"hardware_vector_contract_set.contract.3.value_ty=<8 x i16>".to_string())
    );
    assert!(lines.contains(
        &"hardware_vector_contract_set.contract.3.logical_mask_ty=<8 x bool>".to_string()
    ));
    assert!(
        lines.contains(&"hardware_vector_contract_set.contract.3.operation.0=icmp.eq".to_string())
    );
    assert!(lines.contains(
        &"hardware_vector_contract_set.contract.3.operation.6=vector.mask_to_bits".to_string()
    ));
    assert!(
        lines.contains(&"hardware_vector_contract_set.contract.3.operation.7=icmp.ult".to_string())
    );
    assert!(
        lines.contains(
            &"hardware_vector_contract_set.contract.3.operation.icmp.ult.status=unavailable"
                .to_string()
        )
    );
    assert!(
        lines.contains(
            &"hardware_vector_contract_set.contract.3.operation.icmp.eq.feature_guard=x86.sse2"
                .to_string()
        )
    );
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.3.operation.icmp.eq.native_instructions=pcmpeqw"
                .to_string()
        ));
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.3.operation.icmp.ne.composition=not(pcmpeqw(lhs,rhs))"
                .to_string()
        ));
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.3.operation.icmp.slt.composition=pcmpgtw(rhs,lhs)"
                .to_string()
        ));
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.3.operation.icmp.sle.native_instructions=pcmpgtw;pcmpeqw;por"
                .to_string()
        ));
    assert!(lines.contains(
            &"hardware_vector_contract_set.contract.3.operation.icmp.sgt.composition=pcmpgtw(lhs,rhs)"
                .to_string()
        ));
    assert!(lines.contains(
            &format!(
                "hardware_vector_contract_set.contract.3.operation.vector.mask_to_bits.semantics={CHC_X86_V8_I16_MASK_TO_BITS_SEMANTICS}"
            )
        ));
    assert!(lines.contains(
            &format!(
                "hardware_vector_contract_set.contract.3.operation.vector.mask_to_bits.composition={CHC_X86_V8_I16_MASK_TO_BITS_COMPOSITION}"
            )
        ));
    assert_eq!(
        chc_x86_hardware_vector_contract_manifest_key_value_text(),
        format!("{}\n", lines.join("\n"))
    );
}

#[test]
fn ty_shared_primitive_manifest_combines_producer_row_surfaces() {
    let manifest = ty_shared_primitive_manifest();
    assert_eq!(manifest.status_code(), "available");
    assert_eq!(manifest.reason_code(), "producer_owned_rows_available");
    assert!(!manifest.fail_closed());

    let rows = manifest.manifest_rows();
    let lines = manifest.manifest_key_value_lines();
    let values: BTreeMap<_, _> = rows
        .iter()
        .map(|row| (row.key.as_str(), row.value.as_str()))
        .collect();
    let keys: BTreeSet<_> = rows.iter().map(|row| row.key.as_str()).collect();

    assert_eq!(
        keys.len(),
        rows.len(),
        "aggregate manifest keys must be unique"
    );
    assert_eq!(manifest.manifest_row_count(), rows.len());
    assert_eq!(
        manifest.manifest_digest(),
        manifest_key_value_lines_digest(&lines)
    );
    assert_eq!(
        manifest.manifest_sha256(),
        manifest.manifest_digest().to_string()
    );
    assert_eq!(
        manifest.manifest_key_value_text(),
        format!("{}\n", lines.join("\n"))
    );
    assert_eq!(
        ty_shared_primitive_manifest_rows(),
        rows,
        "free helper must emit the same rows as the manifest value"
    );
    assert_eq!(
        ty_shared_primitive_manifest_key_value_text(),
        manifest.manifest_key_value_text()
    );
    assert_eq!(ty_shared_primitive_manifest_row_count(), rows.len());
    assert_eq!(
        ty_shared_primitive_manifest_digest(),
        manifest.manifest_digest()
    );
    assert_eq!(
        ty_shared_primitive_manifest_sha256(),
        manifest.manifest_sha256()
    );
    assert_eq!(
        values.get("ty_shared_primitive_manifest.schema").copied(),
        Some(TY_SHARED_PRIMITIVE_MANIFEST_SCHEMA)
    );
    assert_eq!(
        values.get("ty_shared_primitive_manifest.status").copied(),
        Some("available")
    );
    assert_eq!(
        values.get("ty_shared_primitive_manifest.reason").copied(),
        Some("producer_owned_rows_available")
    );
    assert_eq!(
        values
            .get("ty_shared_primitive_manifest.fail_closed")
            .copied(),
        Some("false")
    );
    assert_eq!(
        values
            .get("ty_shared_primitive_manifest.component_count")
            .copied(),
        Some("3")
    );

    assert_eq!(
        values
            .get("ty_shared_primitive_manifest.component.0.name")
            .copied(),
        Some("native_semantic_bridge_proof_identity")
    );
    assert_eq!(
        values
            .get("ty_shared_primitive_manifest.component.0.schema")
            .copied(),
        Some(NATIVE_SEMANTIC_BRIDGE_PROOF_IDENTITY_SCHEMA)
    );
    assert_eq!(
        values
            .get("ty_shared_primitive_manifest.component.0.rows_api")
            .copied(),
        Some("NativeSemanticBridgeReport::proof_identity_rows()")
    );
    assert_eq!(
        values
            .get("ty_shared_primitive_manifest.component.0.compact_health_summary_rows_api")
            .copied(),
        Some("NativeSemanticBridgeProofIdentityReplayReport::compact_health_summary_rows()")
    );
    assert_eq!(
        values
            .get("ty_shared_primitive_manifest.component.0.component_health_summary_rows_api")
            .copied(),
        Some("NativeSemanticBridgeProofIdentityReplayReport::component_health_summary_rows()")
    );

    assert_eq!(
        values
            .get("ty_shared_primitive_manifest.component.1.name")
            .copied(),
        Some("petri_successor_trust_mc_chc_proof_evidence_identity")
    );
    assert_eq!(
        values
            .get("ty_shared_primitive_manifest.component.1.schema")
            .copied(),
        Some(PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_SCHEMA)
    );
    assert_eq!(
        values
            .get("ty_shared_primitive_manifest.component.1.rows_api")
            .copied(),
        Some("PetriSuccessorTrustMcChcProofHandoffReport::proof_evidence_identity_rows()")
    );
    assert_eq!(
        values
            .get("ty_shared_primitive_manifest.component.1.component_health_summary_rows_api")
            .copied(),
        Some(
            "PetriSuccessorTrustMcChcProofEvidenceIdentityReplayReport::component_health_summary_rows()"
        )
    );

    assert_eq!(
        values
            .get("ty_shared_primitive_manifest.component.2.name")
            .copied(),
        Some("chc_x86_hardware_vector_contracts")
    );
    assert_eq!(
        values
            .get("ty_shared_primitive_manifest.component.2.schema")
            .copied(),
        Some(HARDWARE_VECTOR_CONTRACT_SCHEMA)
    );
    assert_eq!(
        values
            .get("ty_shared_primitive_manifest.component.2.row_source")
            .copied(),
        Some("static_descriptor")
    );
    assert_eq!(
        values
            .get("ty_shared_primitive_manifest.component.2.rows_api")
            .copied(),
        Some("chc_x86_hardware_vector_contract_manifest_rows()")
    );
    assert_eq!(
        values
            .get("ty_shared_primitive_manifest.component.2.static_contract_count")
            .copied(),
        Some("4")
    );

    for index in 0..3 {
        assert_eq!(
                values
                    .get(format!("ty_shared_primitive_manifest.component.{index}.downstream_row_synthesis_required").as_str())
                    .copied(),
                Some("false")
            );
        assert_eq!(
            values
                .get(format!("ty_shared_primitive_manifest.component.{index}.fail_closed").as_str())
                .copied(),
            Some("false")
        );
    }
}

#[test]
fn ty_shared_primitive_manifest_embeds_hardware_vector_rows() {
    let rows = ty_shared_primitive_manifest_rows();
    let values: BTreeMap<_, _> = rows
        .iter()
        .map(|row| (row.key.as_str(), row.value.as_str()))
        .collect();
    let expected_hardware_rows = chc_x86_hardware_vector_contract_manifest_rows();
    let hardware_row_count = values
        .get("ty_shared_primitive_manifest.hardware_vector_contract_row_count")
        .and_then(|value| value.parse::<usize>().ok())
        .expect("hardware row count");

    assert_eq!(hardware_row_count, expected_hardware_rows.len());
    let reconstructed = (0..hardware_row_count)
        .map(|index| {
            let key = values
                .get(
                    format!(
                        "ty_shared_primitive_manifest.hardware_vector_contract_row.{index}.key"
                    )
                    .as_str(),
                )
                .expect("embedded hardware row key");
            let value = values
                .get(
                    format!(
                        "ty_shared_primitive_manifest.hardware_vector_contract_row.{index}.value"
                    )
                    .as_str(),
                )
                .expect("embedded hardware row value");
            NativeSharedPrimitiveContractManifestRow::new(*key, *value)
        })
        .collect::<Vec<_>>();

    assert_eq!(reconstructed, expected_hardware_rows);
    assert!(ty_shared_primitive_manifest_key_value_lines().contains(
            &"ty_shared_primitive_manifest.hardware_vector_contract_row.0.key=hardware_vector_contract_set.manifest.schema".to_string()
        ));
    assert!(ty_shared_primitive_manifest_key_value_lines().contains(
            &"ty_shared_primitive_manifest.hardware_vector_contract_row.0.value=trust_ir.hardware.vector_contract.manifest.v1".to_string()
        ));
}

#[test]
fn native_shared_primitive_contract_resolves_artifact_requirements_generically() {
    let contract = petri_successor_trust_mc_chc_shared_primitive_contract_descriptor();

    let solver_input = contract
        .production_required_artifact_requirement_for_role(
            NativeSharedPrimitiveArtifactRole::SolverInput,
        )
        .expect("solver input requirement");
    assert_eq!(solver_input.role_code(), "solver_input");
    assert_eq!(
        solver_input.kind,
        NativeEvidenceArtifactKind::TrustMcHornClauses
    );
    assert_eq!(solver_input.digest_algorithm, ProofDigestAlgorithm::Sha256);
    assert_eq!(solver_input.owner_suite, NativeVerifierSuite::AY);
    assert!(solver_input.requires_emitted_solver_artifact);
    assert_eq!(
        contract
            .production_artifact_digest_algorithm(NativeEvidenceArtifactKind::TrustMcHornClauses),
        Some(ProofDigestAlgorithm::Sha256)
    );
    assert_eq!(
        contract.production_artifact_owner_suite(NativeEvidenceArtifactKind::TrustMcHornClauses),
        Some(NativeVerifierSuite::AY)
    );
    assert_eq!(
        contract
            .production_required_artifact_requirement_for_kind(
                NativeEvidenceArtifactKind::TrustMcHornClauses
            )
            .map(|requirement| requirement.role),
        Some(NativeSharedPrimitiveArtifactRole::SolverInput)
    );
    let ay_owned: Vec<_> = contract
        .production_artifact_requirements_for_owner_suite(NativeVerifierSuite::AY)
        .map(|requirement| requirement.role_code())
        .collect();
    assert_eq!(
        ay_owned,
        vec!["solver_input", "replay_transcript", "solver_witness"]
    );
    assert_eq!(
        contract
            .production_artifact_requirements_for_owner_suite(NativeVerifierSuite::TrustVc)
            .count(),
        0
    );

    let emitted = NativeEvidenceArtifact::new(
        "query.chc",
        NativeEvidenceArtifactKind::TrustMcHornClauses,
        digest(0xC1),
    );
    assert!(solver_input.accepts_artifact_identity(&emitted));

    let zero_digest = NativeEvidenceArtifact::new(
        "query.chc",
        NativeEvidenceArtifactKind::TrustMcHornClauses,
        ProofDigest::sha256([0; 32]),
    );
    assert!(!solver_input.accepts_artifact_identity(&zero_digest));

    let structural_digest = NativeEvidenceArtifact::new(
        "query.chc",
        NativeEvidenceArtifactKind::TrustMcHornClauses,
        ProofDigest::trust_ir_stable("test.artifact", b"query"),
    );
    assert!(!solver_input.accepts_artifact_identity(&structural_digest));

    let wrong_kind = NativeEvidenceArtifact::new(
        "query.chc",
        NativeEvidenceArtifactKind::TrustMcModel,
        digest(0xC2),
    );
    assert!(!solver_input.accepts_artifact_identity(&wrong_kind));
    assert!(
        contract
            .production_required_artifact_requirement_for_role(
                NativeSharedPrimitiveArtifactRole::ProofCertificate
            )
            .is_none()
    );
    assert_eq!(
        contract.production_artifact_digest_algorithm(
            NativeEvidenceArtifactKind::TrustVcCertificateImport
        ),
        None
    );
}

#[test]
fn native_shared_primitive_contract_exposes_solver_neutral_acceptance_boundary() {
    let contract = petri_successor_trust_mc_chc_shared_primitive_contract_descriptor();

    assert_eq!(
        contract.production_acceptance_report_api_name(),
        PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_ACCEPTANCE_REPORT_API_NAME
    );
    assert_eq!(
        contract.production_consumer_acceptance_api_name(),
        PETRI_SUCCESSOR_TRUST_MC_CHC_CONSUMER_ACCEPTANCE_API_NAME
    );
    assert!(contract.production_acceptance_requires_solver());
    assert_eq!(
        contract.production_acceptance_owner_suite(),
        PETRI_SUCCESSOR_TRUST_MC_CHC_PRODUCTION_ACCEPTANCE_OWNER_SUITE
    );
    assert_eq!(
        contract.production_acceptance_owner_suite(),
        NativeVerifierSuite::AY
    );

    // New shared-primitive consumers should be able to identify the
    // acceptance boundary without matching on Petri/TrustMc-specific field
    // names or locally interpreting solver output.
    assert_eq!(
        contract.production_acceptance_report_api_name(),
        "ay::chc::trust_mc_petri_successor_chc_model_acceptance_report"
    );
    assert_eq!(
        contract.production_consumer_acceptance_api_name(),
        "ay::chc::TrustMcPetriSuccessorChcModelAcceptanceReport::accept_for_consumer"
    );
}

#[test]
fn native_semantic_bridge_report_blocks_pending_proof() {
    let mut bundle = native_bundle();
    remove_unreplayed_trust_vc_fixture(&mut bundle);
    let bridge = NativeSemanticBridge::petri_successor_plan_cache_equivalence(FuncId::new(0));

    let report = bundle.native_semantic_bridge_report(bridge.clone());

    assert_eq!(bridge.schema(), NATIVE_SEMANTIC_BRIDGE_SCHEMA);
    assert_eq!(bridge.schema_version, NATIVE_SEMANTIC_BRIDGE_SCHEMA_VERSION);
    assert_eq!(bridge.relation.code(), "petri_successor");
    assert_eq!(bridge.relation.name(), "Petri successor");
    assert_eq!(
        bridge.formula_schema,
        PETRI_SUCCESSOR_PLAN_CACHE_EQUIVALENCE_SCHEMA
    );
    assert!(bridge.is_petri_successor_plan_cache_equivalence());
    assert_eq!(report.schema, NATIVE_SEMANTIC_BRIDGE_SCHEMA);
    assert_eq!(report.schema_version, NATIVE_SEMANTIC_BRIDGE_SCHEMA_VERSION);
    assert_eq!(report.bridge, bridge);
    assert_eq!(report.bridge_digest, report.bridge.stable_digest());
    assert_eq!(report.proof_obligation, Some(ProofId::new(1)));
    assert!(report.proof_digest.is_some());
    assert_eq!(report.proof_status, Some(ProofStatus::Pending));
    assert_eq!(report.evidence_digest, None);
    assert_eq!(
        report.evidence_status,
        NativeSemanticBridgeEvidenceStatus::Missing
    );
    assert_eq!(report.evidence_status.code(), "missing");
    assert_eq!(report.status, NativeSemanticBridgeStatus::Blocked);
    assert_eq!(report.status.code(), "blocked");
    assert_eq!(report.reason, NativeSemanticBridgeReason::ProofPending);
    assert_eq!(report.reason.code(), "proof_pending");
    assert_eq!(report.status_code(), "blocked");
    assert_eq!(report.reason_code(), "proof_pending");
    assert_eq!(report.evidence_status_code(), "missing");
    assert!(report.fail_closed());
    assert_eq!(
        report.proof_identity_schema(),
        NATIVE_SEMANTIC_BRIDGE_PROOF_IDENTITY_SCHEMA
    );
    assert_eq!(
        report.proof_identity_schema_version(),
        NATIVE_SEMANTIC_BRIDGE_PROOF_IDENTITY_SCHEMA_VERSION
    );
    assert!(!report.proof_identity_digest().is_zero());
    assert!(!report.is_represented());
    assert!(!report.represents_petri_successor_plan_cache_equivalence());
}

#[test]
fn native_semantic_bridge_report_requires_replayed_proof_before_evidence() {
    let mut bundle = native_bundle();
    bundle.module.proof_obligations[1].status = ProofStatus::Discharged;
    remove_unreplayed_trust_vc_fixture(&mut bundle);
    let bridge = NativeSemanticBridge::petri_successor_plan_cache_equivalence(FuncId::new(0));

    let report = bundle.native_semantic_bridge_report(bridge);

    assert_eq!(report.proof_obligation, Some(ProofId::new(1)));
    assert!(report.proof_digest.is_some());
    assert_eq!(report.proof_status, Some(ProofStatus::Discharged));
    assert_eq!(report.evidence_digest, None);
    assert_eq!(
        report.evidence_status,
        NativeSemanticBridgeEvidenceStatus::Missing
    );
    assert_eq!(report.status, NativeSemanticBridgeStatus::Blocked);
    assert_eq!(
        report.reason,
        NativeSemanticBridgeReason::TrustedProofNotAdmitted
    );
    assert!(!report.is_represented());
    assert!(!report.represents_petri_successor_plan_cache_equivalence());
}

#[test]
fn native_semantic_bridge_report_rejects_unreplayed_discharged_evidenced_relation() {
    let mut bundle = native_bundle();
    bundle.module.proof_obligations[1].status = ProofStatus::Discharged;
    bundle.evidence_bundles = native_evidence_bundles(&bundle);
    remove_unreplayed_trust_vc_fixture(&mut bundle);
    let bridge = NativeSemanticBridge::petri_successor_plan_cache_equivalence(FuncId::new(0));

    let report = bundle.native_semantic_bridge_report(bridge);

    assert_eq!(report.proof_obligation, Some(ProofId::new(1)));
    assert!(report.proof_digest.is_some());
    assert_eq!(report.proof_status, Some(ProofStatus::Discharged));
    assert_eq!(report.evidence_digest, None);
    assert_eq!(
        report.evidence_status,
        NativeSemanticBridgeEvidenceStatus::Missing
    );
    assert_eq!(report.status, NativeSemanticBridgeStatus::Blocked);
    assert_eq!(
        report.reason,
        NativeSemanticBridgeReason::TrustedProofNotAdmitted
    );
    assert!(report.fail_closed());
    assert_eq!(
        report.proof_identity_schema(),
        NATIVE_SEMANTIC_BRIDGE_PROOF_IDENTITY_SCHEMA
    );
    assert_eq!(
        report.proof_identity_schema_version(),
        NATIVE_SEMANTIC_BRIDGE_PROOF_IDENTITY_SCHEMA_VERSION
    );
    assert!(!report.proof_identity_digest().is_zero());
    assert!(!report.is_represented());
    assert!(!report.represents_petri_successor_plan_cache_equivalence());
}

#[test]
fn petri_successor_semantic_bridge_proof_admission_requires_matching_evidence() {
    let mut bundle = native_bundle();
    bundle.module.proof_obligations[1].status = ProofStatus::Discharged;
    remove_unreplayed_trust_vc_fixture(&mut bundle);

    let report = bundle.petri_successor_semantic_bridge_proof_admission_report(FuncId::new(0), &[]);

    assert_eq!(
        report.schema,
        PETRI_SUCCESSOR_SEMANTIC_BRIDGE_PROOF_ADMISSION_SCHEMA
    );
    assert_eq!(
        report.schema_version,
        PETRI_SUCCESSOR_SEMANTIC_BRIDGE_PROOF_ADMISSION_SCHEMA_VERSION
    );
    assert_eq!(report.function, FuncId::new(0));
    assert_eq!(
        report.status,
        PetriSuccessorSemanticBridgeProofAdmissionStatus::Blocked
    );
    assert_eq!(
        report.reason,
        PetriSuccessorSemanticBridgeProofAdmissionReason::ProofHandoffBlocked
    );
    assert_eq!(report.status_code(), "blocked");
    assert_eq!(report.reason_code(), "proof_handoff_blocked");
    assert!(report.fail_closed());
    assert!(!report.is_admitted());
    assert!(report.artifact_resolutions.is_empty());
    assert_eq!(report.blocked_artifact_kind, None);
    assert_eq!(report.blocked_artifact_reason, None);
    assert_eq!(report.blocked_artifact_reason_code(), None);
    assert_eq!(
        report
            .proof_handoff_report
            .binding_report
            .semantic_bridge_report
            .reason,
        NativeSemanticBridgeReason::TrustedProofNotAdmitted
    );
}

#[test]
fn petri_successor_semantic_bridge_proof_admission_stops_before_metadata_resolution_without_proof_authority()
 {
    let horn_bytes = b"(set-logic HORN)\n(assert true)\n";
    let replay_bytes = br#"{"replay":"accepted"}"#;
    let model_bytes = br#"{"model":"accepted"}"#;
    let (bundle, artifacts) =
        petri_successor_trust_mc_bundle_with_artifacts(horn_bytes, replay_bytes, model_bytes);

    let report = bundle.petri_successor_semantic_bridge_proof_admission_report(FuncId::new(0), &[]);

    assert!(!report.proof_handoff_report.is_ready());
    assert_eq!(report.proof_handoff_report.reason_code(), "binding_blocked");
    assert_eq!(
        report.required_artifact_kinds,
        PETRI_SUCCESSOR_TRUST_MC_CHC_PRODUCTION_ACCEPTANCE_REQUIRED_ARTIFACT_KINDS
    );
    assert!(report.artifact_resolutions.is_empty());
    assert_eq!(
        report.status,
        PetriSuccessorSemanticBridgeProofAdmissionStatus::Blocked
    );
    assert_eq!(
        report.reason,
        PetriSuccessorSemanticBridgeProofAdmissionReason::ProofHandoffBlocked
    );
    assert_eq!(report.blocked_artifact_kind, None);
    assert_eq!(report.blocked_artifact_reason, None);
    assert_eq!(report.blocked_artifact_reason_code(), None);
    assert!(report.fail_closed());
    assert!(!report.is_admitted());
    assert_eq!(
        artifacts.len(),
        3,
        "fixture still carries all metadata descriptors"
    );
    assert_eq!(
        report.authoritative_bytes_for_kind(NativeEvidenceArtifactKind::TrustMcHornClauses),
        None
    );
}

#[test]
fn petri_successor_semantic_bridge_proof_admission_rejects_authoritative_bytes_without_proof_authority()
 {
    let horn_bytes = b"(set-logic HORN)\n(assert true)\n";
    let replay_bytes = br#"{"replay":"accepted"}"#;
    let model_bytes = br#"{"model":"accepted"}"#;
    let (bundle, artifacts) =
        petri_successor_trust_mc_bundle_with_artifacts(horn_bytes, replay_bytes, model_bytes);
    let attachments = petri_successor_trust_mc_artifact_attachments(
        &artifacts,
        horn_bytes,
        replay_bytes,
        model_bytes,
    );

    let report =
        bundle.petri_successor_semantic_bridge_proof_admission_report(FuncId::new(0), &attachments);

    assert_eq!(
        report.status,
        PetriSuccessorSemanticBridgeProofAdmissionStatus::Blocked
    );
    assert_eq!(
        report.reason,
        PetriSuccessorSemanticBridgeProofAdmissionReason::ProofHandoffBlocked
    );
    assert_eq!(report.status_code(), "blocked");
    assert_eq!(report.reason_code(), "proof_handoff_blocked");
    assert!(report.fail_closed());
    assert!(!report.is_admitted());
    assert_eq!(report.blocked_artifact_kind, None);
    assert_eq!(report.blocked_artifact_reason, None);
    assert!(report.artifact_resolutions.is_empty());
    assert_eq!(
        report.authoritative_bytes_for_kind(NativeEvidenceArtifactKind::TrustMcHornClauses),
        None
    );
    assert_eq!(
        report.authoritative_bytes_for_kind(NativeEvidenceArtifactKind::ReplayTranscript),
        None
    );
    assert_eq!(
        report.authoritative_bytes_for_kind(NativeEvidenceArtifactKind::TrustMcModel),
        None
    );
}

#[test]
fn petri_successor_semantic_bridge_proof_admission_key_values_expose_blocked_resolution() {
    let horn_bytes = b"(set-logic HORN)\n(assert true)\n";
    let replay_bytes = br#"{"replay":"accepted"}"#;
    let model_bytes = br#"{"model":"accepted"}"#;
    let (bundle, _) =
        petri_successor_trust_mc_bundle_with_artifacts(horn_bytes, replay_bytes, model_bytes);

    let report = bundle.petri_successor_semantic_bridge_proof_admission_report(FuncId::new(0), &[]);
    let rows = report.key_value_rows();
    let lines = report.key_value_lines();
    let text = report.key_value_text();
    let rows_by_key: BTreeMap<_, _> = rows
        .iter()
        .map(|row| (row.key.as_str(), row.value.as_str()))
        .collect();

    assert_eq!(rows, report.key_value_rows());
    assert_eq!(
        lines,
        rows.iter()
            .map(NativeSharedPrimitiveContractManifestRow::to_key_value_line)
            .collect::<Vec<_>>()
    );
    assert_eq!(text, format!("{}\n", lines.join("\n")));
    assert!(lines.iter().all(|line| !line.contains('\n')));

    assert_eq!(
        rows_by_key["proof_admission.schema"],
        PETRI_SUCCESSOR_SEMANTIC_BRIDGE_PROOF_ADMISSION_SCHEMA
    );
    assert_eq!(
        rows_by_key["proof_admission.schema_version"],
        PETRI_SUCCESSOR_SEMANTIC_BRIDGE_PROOF_ADMISSION_SCHEMA_VERSION.to_string()
    );
    assert_eq!(rows_by_key["proof_admission.function"], "0");
    assert_eq!(rows_by_key["proof_admission.status"], "blocked");
    assert_eq!(
        rows_by_key["proof_admission.reason"],
        "proof_handoff_blocked"
    );
    assert_eq!(rows_by_key["proof_admission.fail_closed"], "true");
    assert_eq!(
        rows_by_key["proof_admission.proof_handoff.status"],
        "blocked"
    );
    assert_eq!(
        rows_by_key["proof_admission.proof_handoff.reason"],
        "binding_blocked"
    );
    assert_eq!(
        rows_by_key["proof_admission.required_artifact_kind.count"],
        "3"
    );
    assert_eq!(
        rows_by_key["proof_admission.required_artifact_kind.0"],
        "trust_mc_horn_clauses"
    );
    assert_eq!(rows_by_key["proof_admission.blocked_artifact.kind"], "none");
    assert_eq!(
        rows_by_key["proof_admission.blocked_artifact.reason"],
        "none"
    );
    assert_eq!(
        rows_by_key["proof_admission.artifact_resolution.count"],
        "0"
    );
    assert_eq!(rows_by_key["proof_admission.authoritative_byte_count"], "0");
}

#[test]
fn petri_successor_semantic_bridge_proof_admission_key_values_withhold_bytes_without_proof_authority()
 {
    let horn_bytes = b"(set-logic HORN)\n(assert true)\n";
    let replay_bytes = br#"{"replay":"accepted"}"#;
    let model_bytes = br#"{"model":"accepted"}"#;
    let (bundle, artifacts) =
        petri_successor_trust_mc_bundle_with_artifacts(horn_bytes, replay_bytes, model_bytes);
    let attachments = petri_successor_trust_mc_artifact_attachments(
        &artifacts,
        horn_bytes,
        replay_bytes,
        model_bytes,
    );

    let report =
        bundle.petri_successor_semantic_bridge_proof_admission_report(FuncId::new(0), &attachments);
    let rows = report.key_value_rows();
    let rows_by_key: BTreeMap<_, _> = rows
        .iter()
        .map(|row| (row.key.as_str(), row.value.as_str()))
        .collect();
    assert_eq!(report.authoritative_byte_count(), 0);
    assert_eq!(rows_by_key["proof_admission.status"], "blocked");
    assert_eq!(
        rows_by_key["proof_admission.reason"],
        "proof_handoff_blocked"
    );
    assert_eq!(rows_by_key["proof_admission.fail_closed"], "true");
    assert_eq!(rows_by_key["proof_admission.blocked_artifact.kind"], "none");
    assert_eq!(
        rows_by_key["proof_admission.blocked_artifact.reason"],
        "none"
    );
    assert_eq!(rows_by_key["proof_admission.authoritative_byte_count"], "0");
}

#[test]
fn native_semantic_bridge_proof_identity_rows_are_sidecar_ready() {
    let mut bundle = native_bundle();
    bundle.module.proof_obligations[1].status = ProofStatus::Discharged;
    bundle.evidence_bundles = native_evidence_bundles(&bundle);
    remove_unreplayed_trust_vc_fixture(&mut bundle);
    let report = bundle.petri_successor_semantic_bridge_report(FuncId::new(0));
    let rows = report.proof_identity_rows();
    let lines = report.proof_identity_key_value_lines();
    let text = report.proof_identity_key_value_text();
    let values: BTreeMap<_, _> = rows
        .iter()
        .map(|row| (row.key.clone(), row.value.clone()))
        .collect();
    let keys: BTreeSet<_> = rows.iter().map(|row| row.key.as_str()).collect();
    let identity_digest = report.proof_identity_digest().to_string();
    let bridge_digest = report.bridge_digest.to_string();
    let row_replay = report.proof_identity_replay_report(&rows);
    let line_replay = report.proof_identity_replay_report_for_key_value_lines(&lines);
    let text_replay = report.proof_identity_replay_report_for_key_value_text(&text);
    let summary_rows = row_replay.compact_health_summary_rows();
    let summary_lines = row_replay.compact_health_summary_key_value_lines();
    let summary_json: serde_json::Value =
        serde_json::from_str(&row_replay.compact_health_summary_json_text())
            .expect("compact semantic bridge health JSON should parse");
    let summary_row_round_trip = row_replay.compact_health_summary_round_trip_report(&summary_rows);
    let summary_line_round_trip =
        row_replay.compact_health_summary_round_trip_report_for_key_value_lines(&summary_lines);
    let summary_text_round_trip = row_replay
        .compact_health_summary_round_trip_report_for_key_value_text(
            &row_replay.compact_health_summary_key_value_text(),
        );
    let summary_values: BTreeMap<_, _> = summary_rows
        .iter()
        .map(|row| (row.key.as_str(), row.value.as_str()))
        .collect();
    let component_rows = row_replay.component_health_summary_rows();
    let component_lines = row_replay.component_health_summary_key_value_lines();
    let component_values: BTreeMap<_, _> = component_rows
        .iter()
        .map(|row| (row.key.as_str(), row.value.as_str()))
        .collect();

    assert_eq!(keys.len(), rows.len(), "identity rows must use unique keys");
    assert_eq!(text, format!("{}\n", lines.join("\n")));
    assert_eq!(row_replay, line_replay);
    assert_eq!(row_replay, text_replay);
    assert_eq!(
        row_replay.status,
        NativeSemanticBridgeProofIdentityReplayStatus::Replayable
    );
    assert!(row_replay.is_replayable());
    assert_eq!(row_replay.diagnostic_count(), 0);
    assert!(row_replay.schema_matches);
    assert!(row_replay.identity_digest_matches);
    assert!(row_replay.bridge_digest_matches);
    assert!(row_replay.bridge_function_matches);
    assert!(row_replay.status_matches);
    assert!(row_replay.reason_matches);
    assert!(row_replay.fail_closed_matches);
    assert!(row_replay.evidence_status_matches);
    assert_eq!(summary_row_round_trip, summary_line_round_trip);
    assert_eq!(summary_row_round_trip, summary_text_round_trip);
    assert_eq!(
        summary_row_round_trip.status,
        NativeSemanticBridgeProofIdentityReplayHealthSummaryRoundTripStatus::Valid
    );
    assert!(summary_row_round_trip.is_valid());
    assert!(!summary_row_round_trip.fail_closed);
    assert_eq!(summary_row_round_trip.diagnostic_count(), 0);
    assert!(summary_row_round_trip.schema_matches);
    assert!(summary_row_round_trip.status_matches);
    assert!(summary_row_round_trip.fail_closed_matches);
    assert!(summary_row_round_trip.diagnostic_count_matches);
    assert_eq!(
        values
            .get("semantic_bridge_proof_identity.schema")
            .map(String::as_str),
        Some(NATIVE_SEMANTIC_BRIDGE_PROOF_IDENTITY_SCHEMA)
    );
    assert_eq!(
        values
            .get("semantic_bridge_proof_identity.digest")
            .map(String::as_str),
        Some(identity_digest.as_str())
    );
    assert_eq!(
        values
            .get("semantic_bridge_proof_identity.bridge.digest")
            .map(String::as_str),
        Some(bridge_digest.as_str())
    );
    assert_eq!(
        values
            .get("semantic_bridge_proof_identity.bridge.relation")
            .map(String::as_str),
        Some("petri_successor")
    );
    assert_eq!(
        values
            .get("semantic_bridge_proof_identity.bridge.function")
            .map(String::as_str),
        Some("0")
    );
    assert_eq!(
        values
            .get("semantic_bridge_proof_identity.report.status")
            .map(String::as_str),
        Some("blocked")
    );
    assert_eq!(
        values
            .get("semantic_bridge_proof_identity.report.reason")
            .map(String::as_str),
        Some("trusted_proof_not_admitted")
    );
    assert_eq!(
        values
            .get("semantic_bridge_proof_identity.report.fail_closed")
            .map(String::as_str),
        Some("true")
    );
    assert_eq!(
        values
            .get("semantic_bridge_proof_identity.report.evidence_status")
            .map(String::as_str),
        Some("missing")
    );
    assert_eq!(
        values
            .get("semantic_bridge_proof_identity.proof.obligation")
            .map(String::as_str),
        Some("1")
    );
    assert_eq!(
        values
            .get("semantic_bridge_proof_identity.proof.status")
            .map(String::as_str),
        Some("discharged")
    );
    assert_eq!(
        row_replay.compact_health_summary_key_value_text(),
        format!("{}\n", summary_lines.join("\n"))
    );
    assert_eq!(
        row_replay.component_health_summary_key_value_text(),
        format!("{}\n", component_lines.join("\n"))
    );
    assert_eq!(
        summary_values
            .get("semantic_bridge_proof_identity_replay_report.schema")
            .copied(),
        Some(NATIVE_SEMANTIC_BRIDGE_PROOF_IDENTITY_SCHEMA)
    );
    assert_eq!(
        summary_values
            .get("semantic_bridge_proof_identity_replay_report.status")
            .copied(),
        Some("replayable")
    );
    assert_eq!(
        summary_values
            .get("semantic_bridge_proof_identity_replay_report.fail_closed")
            .copied(),
        Some("false")
    );
    assert_eq!(
        summary_values
            .get("semantic_bridge_proof_identity_replay_report.count.diagnostics")
            .copied(),
        Some("0")
    );
    assert_eq!(
        summary_values
            .get("semantic_bridge_proof_identity_replay_report.reconstructed.identity_digest")
            .copied(),
        Some(identity_digest.as_str())
    );
    assert_eq!(
        summary_values
            .get("semantic_bridge_proof_identity_replay_report.agreement.identity_digest")
            .copied(),
        Some("true")
    );
    assert_eq!(
        component_values
            .get("semantic_bridge_proof_identity_replay_component_summary.status")
            .copied(),
        Some("replayable")
    );
    assert_eq!(
        component_values
            .get("semantic_bridge_proof_identity_replay_component_summary.component.count")
            .copied(),
        Some("8")
    );
    assert_eq!(
            component_values
                .get("semantic_bridge_proof_identity_replay_component_summary.component.identity_digest.value")
                .copied(),
            Some(identity_digest.as_str())
        );
    assert_eq!(
            component_values
                .get("semantic_bridge_proof_identity_replay_component_summary.component.identity_digest.matches")
                .copied(),
            Some("true")
        );
    assert_eq!(
            component_values
                .get("semantic_bridge_proof_identity_replay_component_summary.component.bridge_function.value")
                .copied(),
            Some("0")
        );
    assert_eq!(
            component_values
                .get("semantic_bridge_proof_identity_replay_component_summary.component.evidence_status.value")
                .copied(),
            Some("missing")
        );
    assert_eq!(
            component_values
                .get("semantic_bridge_proof_identity_replay_component_summary.component.evidence_status.matches")
                .copied(),
            Some("true")
        );
    assert_eq!(
        summary_json
            .get("schema")
            .and_then(serde_json::Value::as_str),
        summary_values
            .get("semantic_bridge_proof_identity_replay_report.schema")
            .copied()
    );
    assert_eq!(
        summary_json
            .get("schema_version")
            .and_then(serde_json::Value::as_u64),
        summary_values
            .get("semantic_bridge_proof_identity_replay_report.schema_version")
            .and_then(|value| value.parse::<u64>().ok())
    );
    assert_eq!(
        summary_json
            .get("status")
            .and_then(serde_json::Value::as_str),
        summary_values
            .get("semantic_bridge_proof_identity_replay_report.status")
            .copied()
    );
    assert_eq!(
        summary_json
            .get("fail_closed")
            .and_then(serde_json::Value::as_bool),
        Some(false)
    );
    assert_eq!(
        summary_json
            .get("diagnostic_count")
            .and_then(serde_json::Value::as_u64),
        Some(0)
    );
    assert_eq!(
        summary_json
            .get("reconstructed_identity_digest")
            .and_then(serde_json::Value::as_str),
        Some(identity_digest.as_str())
    );
}

#[test]
fn native_semantic_bridge_proof_identity_replay_report_fails_closed_on_bad_text() {
    let report = native_bundle().petri_successor_semantic_bridge_report(FuncId::new(0));
    let mut lines = report.proof_identity_key_value_lines();
    lines[0] = "malformed semantic bridge proof identity line".to_string();
    if let Some(line) = lines
        .iter_mut()
        .find(|line| line.starts_with("semantic_bridge_proof_identity.bridge.function="))
    {
        *line = "semantic_bridge_proof_identity.bridge.function=not_usize".to_string();
    }
    if let Some(line) = lines
        .iter_mut()
        .find(|line| line.starts_with("semantic_bridge_proof_identity.report.fail_closed="))
    {
        *line = "semantic_bridge_proof_identity.report.fail_closed=not_bool".to_string();
    }
    lines.push("semantic_bridge_proof_identity.report.status=blocked".to_string());
    lines.push("semantic_bridge_proof_identity.extra=unexpected".to_string());

    let validation = report.proof_identity_replay_report_for_key_value_lines(&lines);
    let component_values: BTreeMap<_, _> = validation
        .component_health_summary_rows()
        .iter()
        .map(|row| (row.key.clone(), row.value.clone()))
        .collect();

    assert_eq!(
        validation.status,
        NativeSemanticBridgeProofIdentityReplayStatus::Invalid
    );
    assert!(!validation.is_replayable());
    assert!(validation.fail_closed);
    assert_eq!(validation.invalid_lines.len(), 1);
    assert!(
        validation
            .missing_keys
            .contains(&"semantic_bridge_proof_identity.schema".to_string())
    );
    assert!(
        validation
            .duplicate_keys
            .contains(&"semantic_bridge_proof_identity.report.status".to_string())
    );
    assert!(
        validation
            .unexpected_keys
            .contains(&"semantic_bridge_proof_identity.extra".to_string())
    );
    assert!(
        validation
            .invalid_usize_keys
            .contains(&"semantic_bridge_proof_identity.bridge.function".to_string())
    );
    assert!(
        validation
            .invalid_bool_keys
            .contains(&"semantic_bridge_proof_identity.report.fail_closed".to_string())
    );
    assert!(!validation.schema_matches);
    assert!(!validation.bridge_function_matches);
    assert!(validation.status_matches);
    assert!(!validation.fail_closed_matches);
    assert!(validation.diagnostic_count() >= 5);
    assert_eq!(
        component_values
            .get("semantic_bridge_proof_identity_replay_component_summary.status")
            .map(String::as_str),
        Some("invalid")
    );
    assert_eq!(
        component_values
            .get("semantic_bridge_proof_identity_replay_component_summary.fail_closed")
            .map(String::as_str),
        Some("true")
    );
    assert_eq!(
        component_values
            .get("semantic_bridge_proof_identity_replay_component_summary.component.schema.matches")
            .map(String::as_str),
        Some("false")
    );
    assert_eq!(
            component_values
                .get("semantic_bridge_proof_identity_replay_component_summary.component.bridge_function.matches")
                .map(String::as_str),
            Some("false")
        );
}

#[test]
fn native_semantic_bridge_proof_identity_health_summary_round_trip_fails_closed() {
    let mut bundle = native_bundle();
    bundle.module.proof_obligations[1].status = ProofStatus::Discharged;
    bundle.evidence_bundles = native_evidence_bundles(&bundle);
    let report = bundle.petri_successor_semantic_bridge_report(FuncId::new(0));
    let replay_report = report.proof_identity_replay_report(&report.proof_identity_rows());
    let mut lines = replay_report.compact_health_summary_key_value_lines();
    lines[0] = "malformed semantic bridge health summary line".to_string();
    if let Some(line) = lines.iter_mut().find(|line| {
        line.starts_with("semantic_bridge_proof_identity_replay_report.schema_version=")
    }) {
        *line = "semantic_bridge_proof_identity_replay_report.schema_version=not_usize".to_string();
    }
    if let Some(line) = lines
        .iter_mut()
        .find(|line| line.starts_with("semantic_bridge_proof_identity_replay_report.fail_closed="))
    {
        *line = "semantic_bridge_proof_identity_replay_report.fail_closed=not_bool".to_string();
    }
    lines.push("semantic_bridge_proof_identity_replay_report.status=replayable".to_string());
    lines.push("semantic_bridge_proof_identity_replay_report.extra=unexpected".to_string());

    let validation =
        replay_report.compact_health_summary_round_trip_report_for_key_value_lines(&lines);

    assert_eq!(
        validation.status,
        NativeSemanticBridgeProofIdentityReplayHealthSummaryRoundTripStatus::Invalid
    );
    assert!(!validation.is_valid());
    assert!(validation.fail_closed);
    assert_eq!(validation.invalid_lines.len(), 1);
    assert!(
        validation
            .missing_keys
            .contains(&"semantic_bridge_proof_identity_replay_report.schema".to_string())
    );
    assert!(
        validation
            .duplicate_keys
            .contains(&"semantic_bridge_proof_identity_replay_report.status".to_string())
    );
    assert!(
        validation
            .unexpected_keys
            .contains(&"semantic_bridge_proof_identity_replay_report.extra".to_string())
    );
    assert!(
        validation
            .invalid_usize_keys
            .contains(&"semantic_bridge_proof_identity_replay_report.schema_version".to_string())
    );
    assert!(
        validation
            .invalid_bool_keys
            .contains(&"semantic_bridge_proof_identity_replay_report.fail_closed".to_string())
    );
    assert!(!validation.schema_matches);
    assert!(validation.status_matches);
    assert!(!validation.fail_closed_matches);
    assert!(validation.diagnostic_count() >= 5);
}

#[test]
fn native_semantic_bridge_proof_identity_binds_fail_closed_reason() {
    let bridge = NativeSemanticBridge::petri_successor_plan_cache_equivalence(FuncId::new(0));
    let mut pending_bundle = native_bundle();
    remove_unreplayed_trust_vc_fixture(&mut pending_bundle);
    let pending = pending_bundle.native_semantic_bridge_report(bridge.clone());

    let mut unreplayed_bundle = native_bundle();
    unreplayed_bundle.module.proof_obligations[1].status = ProofStatus::Discharged;
    unreplayed_bundle.evidence_bundles = native_evidence_bundles(&unreplayed_bundle);
    remove_unreplayed_trust_vc_fixture(&mut unreplayed_bundle);
    let unreplayed = unreplayed_bundle.native_semantic_bridge_report(bridge);

    assert!(pending.fail_closed());
    assert!(unreplayed.fail_closed());
    assert_eq!(pending.status_code(), "blocked");
    assert_eq!(unreplayed.status_code(), "blocked");
    assert_eq!(pending.reason_code(), "proof_pending");
    assert_eq!(unreplayed.reason_code(), "trusted_proof_not_admitted");
    assert_ne!(
        pending.proof_identity_digest(),
        unreplayed.proof_identity_digest(),
        "bridge proof identity must bind the exact fail-closed authority reason"
    );
}

#[test]
fn native_semantic_bridge_report_blocks_missing_or_mismatched_relation() {
    let mut missing_function_bundle = native_bundle();
    remove_unreplayed_trust_vc_fixture(&mut missing_function_bundle);
    let missing_function =
        missing_function_bundle.native_semantic_bridge_report(NativeSemanticBridge::new(
            NativeSemanticRelationKind::NativeSuccessor,
            FuncId::new(99),
            PETRI_SUCCESSOR_PLAN_CACHE_EQUIVALENCE_SCHEMA,
        ));
    assert_eq!(missing_function.proof_obligation, None);
    assert_eq!(
        missing_function.reason,
        NativeSemanticBridgeReason::MissingFunction
    );

    let mut missing_formula_bundle = native_bundle();
    remove_unreplayed_trust_vc_fixture(&mut missing_formula_bundle);
    let missing_formula =
        missing_formula_bundle.native_semantic_bridge_report(NativeSemanticBridge::new(
            NativeSemanticRelationKind::PetriSuccessor,
            FuncId::new(0),
            "ty.petri.native.successor.missing.v1",
        ));
    assert_eq!(missing_formula.proof_obligation, None);
    assert_eq!(
        missing_formula.reason,
        NativeSemanticBridgeReason::MissingProofObligation
    );
    assert!(!missing_formula.is_represented());
}

#[test]
fn petri_successor_bridge_helper_rejects_wrong_relation_or_schema() {
    let mut bundle = native_bundle();
    bundle.module.proof_obligations[1].status = ProofStatus::Discharged;
    bundle.evidence_bundles = native_evidence_bundles(&bundle);
    remove_unreplayed_trust_vc_fixture(&mut bundle);

    let report = bundle.petri_successor_semantic_bridge_report(FuncId::new(0));
    assert!(!report.is_represented());
    assert_eq!(
        report.reason,
        NativeSemanticBridgeReason::TrustedProofNotAdmitted
    );
    assert!(!report.represents_petri_successor_plan_cache_equivalence());
    assert_eq!(
        report.bridge,
        NativeSemanticBridge::petri_successor_plan_cache_equivalence(FuncId::new(0))
    );

    let wrong_relation = bundle.native_semantic_bridge_report(NativeSemanticBridge::new(
        NativeSemanticRelationKind::NativeSuccessor,
        FuncId::new(0),
        PETRI_SUCCESSOR_PLAN_CACHE_EQUIVALENCE_SCHEMA,
    ));
    assert!(!wrong_relation.is_represented());
    assert_eq!(
        wrong_relation.reason,
        NativeSemanticBridgeReason::TrustedProofNotAdmitted
    );
    assert!(
        !wrong_relation
            .bridge
            .is_petri_successor_plan_cache_equivalence()
    );
    assert!(!wrong_relation.represents_petri_successor_plan_cache_equivalence());

    let wrong_schema = NativeSemanticBridge::new(
        NativeSemanticRelationKind::PetriSuccessor,
        FuncId::new(0),
        "ty.petri.native.successor.placeholder.v1",
    );
    assert!(!wrong_schema.is_petri_successor_plan_cache_equivalence());
    let wrong_schema_report = bundle.native_semantic_bridge_report(wrong_schema);
    assert!(!wrong_schema_report.is_represented());
    assert!(!wrong_schema_report.represents_petri_successor_plan_cache_equivalence());
}

#[test]
fn petri_successor_trust_mc_chc_binding_report_requires_replayed_semantic_proof() {
    let mut bundle = native_bundle();
    bundle.module.proof_obligations[1].status = ProofStatus::Discharged;
    bundle.evidence_bundles = native_evidence_bundles(&bundle);
    remove_unreplayed_trust_vc_fixture(&mut bundle);

    let report = bundle.petri_successor_trust_mc_chc_binding_report(FuncId::new(0));

    assert_eq!(report.schema, PETRI_SUCCESSOR_TRUST_MC_CHC_BINDING_SCHEMA);
    assert_eq!(
        report.schema_version,
        PETRI_SUCCESSOR_TRUST_MC_CHC_BINDING_SCHEMA_VERSION
    );
    assert_eq!(report.function, FuncId::new(0));
    assert!(!report.is_bound());
    assert!(report.fail_closed());
    assert_eq!(report.status_code(), "blocked");
    assert_eq!(report.reason_code(), "semantic_bridge_blocked");
    assert_eq!(
        report.semantic_bridge_report.reason,
        NativeSemanticBridgeReason::TrustedProofNotAdmitted
    );
    assert_eq!(report.request, None);
    assert_eq!(report.evidence_digest, None);
    assert_eq!(report.horn_clause_artifact, None);
}

#[test]
fn petri_successor_trust_mc_chc_binding_report_does_not_inspect_horn_artifact_before_proof() {
    let mut bundle = native_bundle();
    bundle.module.proof_obligations[1].status = ProofStatus::Discharged;
    bundle.evidence_bundles = native_evidence_bundles(&bundle);
    if let NativeEvidenceBundle::TrustMc(evidence) = &mut bundle.evidence_bundles[1] {
        evidence.artifacts = vec![NativeEvidenceArtifact::new(
            "trust_mc-model.json",
            NativeEvidenceArtifactKind::TrustMcModel,
            digest(0xC3),
        )];
    } else {
        panic!("TrustMc evidence");
    }
    remove_unreplayed_trust_vc_fixture(&mut bundle);

    let report = bundle.petri_successor_trust_mc_chc_binding_report(FuncId::new(0));

    assert!(!report.semantic_bridge_report.is_represented());
    assert!(report.fail_closed());
    assert_eq!(report.status_code(), "blocked");
    assert_eq!(report.reason_code(), "semantic_bridge_blocked");
    assert_eq!(report.request, None);
    assert_eq!(report.evidence_digest, None);
    assert_eq!(report.horn_clause_artifact, None);
}

#[test]
fn petri_successor_trust_mc_chc_binding_report_blocks_on_proof_before_request_matching() {
    let mut bundle = native_bundle();
    bundle.module.proof_obligations[1].status = ProofStatus::Discharged;
    bundle.evidence_bundles = native_evidence_bundles(&bundle)
        .into_iter()
        .filter(|evidence| evidence.verifier_suite() == NativeVerifierSuite::TrustWp)
        .collect();
    bundle.requests.retain(|request| {
        !matches!(
            request,
            NativeVerificationRequest::TrustMc(TrustMcNativeRequest {
                mode: TrustMcVerificationMode::Chc,
                ..
            })
        )
    });
    remove_unreplayed_trust_vc_fixture(&mut bundle);

    let report = bundle.petri_successor_trust_mc_chc_binding_report(FuncId::new(0));

    assert!(!report.semantic_bridge_report.is_represented());
    assert!(report.fail_closed());
    assert_eq!(report.status_code(), "blocked");
    assert_eq!(report.reason_code(), "semantic_bridge_blocked");
    assert_eq!(report.request, None);
    assert_eq!(report.horn_clause_artifact, None);
}

#[test]
fn petri_successor_trust_mc_chc_proof_handoff_report_withholds_replay_artifacts_without_proof_authority()
 {
    let mut bundle = native_bundle();
    bundle.module.proof_obligations[1].status = ProofStatus::Discharged;
    bundle.evidence_bundles = native_evidence_bundles(&bundle);
    if let NativeEvidenceBundle::TrustMc(evidence) = &mut bundle.evidence_bundles[1] {
        let transcript_digest = evidence
            .replay
            .transcript_digest
            .expect("TrustMc replay transcript digest");
        evidence.artifacts.push(NativeEvidenceArtifact::new(
            "trust_mc-replay.json",
            NativeEvidenceArtifactKind::ReplayTranscript,
            transcript_digest,
        ));
        evidence.artifacts.push(NativeEvidenceArtifact::new(
            "trust_mc-model.json",
            NativeEvidenceArtifactKind::TrustMcModel,
            digest(0xC3),
        ));
    } else {
        panic!("TrustMc evidence");
    }
    remove_unreplayed_trust_vc_fixture(&mut bundle);

    let report = bundle.petri_successor_trust_mc_chc_proof_handoff_report(FuncId::new(0));

    if report.fail_closed() {
        assert!(!report.binding_report.is_bound());
        assert_eq!(report.status_code(), "blocked");
        assert_eq!(report.reason_code(), "binding_blocked");
        assert_eq!(
            report.proof_identity_digest,
            Some(
                report
                    .binding_report
                    .semantic_bridge_report
                    .proof_identity_digest()
            )
        );
        assert_eq!(report.replay_transcript_artifact, None);
        assert_eq!(report.model_artifact, None);
        assert!(report.solver_identities.is_empty());
        return;
    }

    assert_eq!(
        report.schema,
        PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_HANDOFF_SCHEMA
    );
    assert_eq!(
        report.schema_version,
        PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_HANDOFF_SCHEMA_VERSION
    );
    assert_eq!(report.function, FuncId::new(0));
    assert!(report.binding_report.is_bound());
    assert!(report.is_ready());
    assert!(!report.fail_closed());
    assert_eq!(report.status_code(), "ready");
    assert_eq!(report.reason_code(), "ready");
    assert_eq!(
        report.proof_identity_digest,
        Some(
            report
                .binding_report
                .semantic_bridge_report
                .proof_identity_digest()
        )
    );
    assert_eq!(
        report.replay_transcript_digest,
        report.replay.as_ref().expect("replay").transcript_digest
    );
    let replay_artifact = report
        .replay_transcript_artifact
        .expect("replay transcript artifact");
    assert_eq!(replay_artifact.name, "trust_mc-replay.json");
    assert_eq!(
        replay_artifact.kind,
        NativeEvidenceArtifactKind::ReplayTranscript
    );
    assert_eq!(
        Some(replay_artifact.digest),
        report.replay_transcript_digest
    );
    let model_artifact = report.model_artifact.expect("model artifact");
    assert_eq!(model_artifact.name, "trust_mc-model.json");
    assert_eq!(
        model_artifact.kind,
        NativeEvidenceArtifactKind::TrustMcModel
    );
    assert_eq!(model_artifact.digest, digest(0xC3));
    assert_eq!(report.solver_identities.len(), 1);
    assert_eq!(report.solver_identities[0].canonical_name(), "z3");
}

#[test]
fn petri_successor_trust_mc_chc_proof_evidence_identity_rows_are_sidecar_ready() {
    let mut bundle = native_bundle();
    bundle.module.proof_obligations[1].status = ProofStatus::Discharged;
    bundle.evidence_bundles = native_evidence_bundles(&bundle);
    if let NativeEvidenceBundle::TrustMc(evidence) = &mut bundle.evidence_bundles[1] {
        let transcript_digest = evidence
            .replay
            .transcript_digest
            .expect("TrustMc replay transcript digest");
        evidence.artifacts.push(NativeEvidenceArtifact::new(
            "trust_mc-replay.json",
            NativeEvidenceArtifactKind::ReplayTranscript,
            transcript_digest,
        ));
        evidence.artifacts.push(NativeEvidenceArtifact::new(
            "trust_mc-model.json",
            NativeEvidenceArtifactKind::TrustMcModel,
            digest(0xC3),
        ));
    } else {
        panic!("TrustMc evidence");
    }
    remove_unreplayed_trust_vc_fixture(&mut bundle);

    let report = bundle.petri_successor_trust_mc_chc_proof_handoff_report(FuncId::new(0));
    let rows = report.proof_evidence_identity_rows();
    let lines = report.proof_evidence_identity_key_value_lines();
    let values: BTreeMap<_, _> = rows
        .iter()
        .map(|row| (row.key.clone(), row.value.clone()))
        .collect();
    let keys: BTreeSet<_> = rows.iter().map(|row| row.key.as_str()).collect();
    let identity_digest = report.proof_evidence_identity_digest();
    let identity_digest_string = identity_digest.to_string();
    if report.fail_closed() {
        assert_eq!(report.reason_code(), "binding_blocked");
        assert_eq!(keys.len(), rows.len());
        assert_eq!(
            values.get("proof_handoff.status").map(String::as_str),
            Some("blocked")
        );
        assert_eq!(
            values.get("proof_handoff.reason").map(String::as_str),
            Some("binding_blocked")
        );
        assert_eq!(
            report.proof_evidence_identity_key_value_text(),
            format!("{}\n", lines.join("\n"))
        );
        return;
    }
    let semantic_bridge_identity_digest = report
        .binding_report
        .semantic_bridge_report
        .proof_identity_digest()
        .to_string();
    let proof_identity_digest = report
        .proof_identity_digest
        .expect("proof identity digest")
        .to_string();
    let replay_transcript_digest = report
        .replay_transcript_digest
        .expect("replay transcript digest")
        .to_string();
    let replay_artifact_digest = report
        .replay_transcript_artifact
        .as_ref()
        .expect("replay transcript artifact")
        .digest
        .to_string();
    let model_artifact_digest = report
        .model_artifact
        .as_ref()
        .expect("model artifact")
        .digest
        .to_string();

    assert_eq!(keys.len(), rows.len(), "identity rows must use unique keys");
    assert_eq!(
        report.proof_evidence_identity_key_value_text(),
        format!("{}\n", lines.join("\n"))
    );
    assert_eq!(
        values
            .get("proof_evidence_identity.schema")
            .map(String::as_str),
        Some(PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_SCHEMA)
    );
    assert_eq!(
        values
            .get("proof_evidence_identity.schema_version")
            .map(String::as_str),
        Some("1")
    );
    assert_eq!(
        values
            .get("proof_evidence_identity.digest.context")
            .map(String::as_str),
        Some(PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_DIGEST_CONTEXT)
    );
    assert_eq!(
        values
            .get("proof_evidence_identity.digest")
            .map(String::as_str),
        Some(identity_digest_string.as_str())
    );
    assert_eq!(
        values
            .get("proof_evidence_identity.function")
            .map(String::as_str),
        Some("0")
    );
    assert_eq!(
        values.get("semantic_bridge.status").map(String::as_str),
        Some("represented")
    );
    assert_eq!(
        values
            .get("semantic_bridge.proof_identity.digest")
            .map(String::as_str),
        Some(semantic_bridge_identity_digest.as_str())
    );
    assert_eq!(
        values.get("binding.status").map(String::as_str),
        Some("bound")
    );
    assert_eq!(
        values.get("binding.fail_closed").map(String::as_str),
        Some("false")
    );
    assert_eq!(
        values.get("binding.request.id").map(String::as_str),
        Some("1")
    );
    assert_eq!(
        values
            .get("binding.horn_clause_artifact.present")
            .map(String::as_str),
        Some("true")
    );
    assert_eq!(
        values
            .get("binding.horn_clause_artifact.kind")
            .map(String::as_str),
        Some("trust_mc_horn_clauses")
    );
    assert_eq!(
        values.get("proof_handoff.status").map(String::as_str),
        Some("ready")
    );
    assert_eq!(
        values.get("proof_handoff.fail_closed").map(String::as_str),
        Some("false")
    );
    assert_eq!(
        values
            .get("proof_handoff.proof_identity.digest")
            .map(String::as_str),
        Some(proof_identity_digest.as_str())
    );
    assert_eq!(
        values
            .get("proof_handoff.replay.transcript_digest")
            .map(String::as_str),
        Some(replay_transcript_digest.as_str())
    );
    assert_eq!(
        values
            .get("proof_handoff.replay_transcript_artifact.digest")
            .map(String::as_str),
        Some(replay_artifact_digest.as_str())
    );
    assert_eq!(
        values
            .get("proof_handoff.model_artifact.digest")
            .map(String::as_str),
        Some(model_artifact_digest.as_str())
    );
    assert_eq!(
        values
            .get("proof_handoff.solver_identity.count")
            .map(String::as_str),
        Some("1")
    );
    assert_eq!(
        values
            .get("proof_handoff.solver_identity.0.canonical_name")
            .map(String::as_str),
        Some("z3")
    );
}

#[test]
fn petri_successor_trust_mc_chc_proof_evidence_identity_replay_report_accepts_rows_and_text() {
    let mut bundle = native_bundle();
    bundle.module.proof_obligations[1].status = ProofStatus::Discharged;
    bundle.evidence_bundles = native_evidence_bundles(&bundle);
    if let NativeEvidenceBundle::TrustMc(evidence) = &mut bundle.evidence_bundles[1] {
        let transcript_digest = evidence
            .replay
            .transcript_digest
            .expect("TrustMc replay transcript digest");
        evidence.artifacts.push(NativeEvidenceArtifact::new(
            "trust_mc-replay.json",
            NativeEvidenceArtifactKind::ReplayTranscript,
            transcript_digest,
        ));
        evidence.artifacts.push(NativeEvidenceArtifact::new(
            "trust_mc-model.json",
            NativeEvidenceArtifactKind::TrustMcModel,
            digest(0xC3),
        ));
    } else {
        panic!("TrustMc evidence");
    }
    remove_unreplayed_trust_vc_fixture(&mut bundle);

    let handoff = bundle.petri_successor_trust_mc_chc_proof_handoff_report(FuncId::new(0));
    let replay_report =
        handoff.proof_evidence_identity_replay_report(&handoff.proof_evidence_identity_rows());
    let line_report = handoff.proof_evidence_identity_replay_report_for_key_value_lines(
        &handoff.proof_evidence_identity_key_value_lines(),
    );
    let text_report = handoff.proof_evidence_identity_replay_report_for_key_value_text(
        &handoff.proof_evidence_identity_key_value_text(),
    );
    let summary_rows = replay_report.compact_health_summary_rows();
    let summary_lines = replay_report.compact_health_summary_key_value_lines();
    let summary_json: serde_json::Value =
        serde_json::from_str(&replay_report.compact_health_summary_json_text())
            .expect("compact health summary JSON should parse");
    let summary_row_round_trip =
        replay_report.compact_health_summary_round_trip_report(&summary_rows);
    let summary_line_round_trip =
        replay_report.compact_health_summary_round_trip_report_for_key_value_lines(&summary_lines);
    let summary_text_round_trip = replay_report
        .compact_health_summary_round_trip_report_for_key_value_text(
            &replay_report.compact_health_summary_key_value_text(),
        );
    let summary_values: BTreeMap<_, _> = summary_rows
        .iter()
        .map(|row| (row.key.as_str(), row.value.as_str()))
        .collect();
    let component_rows = replay_report.component_health_summary_rows();
    let component_lines = replay_report.component_health_summary_key_value_lines();
    let component_values: BTreeMap<_, _> = component_rows
        .iter()
        .map(|row| (row.key.as_str(), row.value.as_str()))
        .collect();
    let identity_digest = handoff.proof_evidence_identity_digest().to_string();

    if handoff.fail_closed() {
        assert_eq!(handoff.reason_code(), "binding_blocked");
        assert_eq!(replay_report, line_report);
        assert_eq!(replay_report, text_report);
        assert!(replay_report.is_replayable());
        assert_eq!(replay_report.diagnostic_count(), 0);
        assert_eq!(
            replay_report.reconstructed_proof_handoff_status.as_deref(),
            Some("blocked")
        );
        assert_eq!(
            replay_report.reconstructed_proof_handoff_fail_closed,
            Some(true)
        );
        return;
    }

    assert_eq!(replay_report, line_report);
    assert_eq!(replay_report, text_report);
    assert_eq!(
        replay_report.status,
        PetriSuccessorTrustMcChcProofEvidenceIdentityReplayStatus::Replayable
    );
    assert!(replay_report.is_replayable());
    assert!(!replay_report.fail_closed);
    assert_eq!(replay_report.diagnostic_count(), 0);
    assert!(replay_report.schema_matches);
    assert!(replay_report.identity_digest_matches);
    assert!(replay_report.function_matches);
    assert!(replay_report.proof_handoff_status_matches);
    assert!(replay_report.proof_handoff_fail_closed_matches);
    assert!(replay_report.solver_identity_count_matches);
    assert_eq!(
        replay_report.reconstructed_identity_digest.as_deref(),
        Some(identity_digest.as_str())
    );
    assert_eq!(
        replay_report.reconstructed_proof_handoff_status.as_deref(),
        Some("ready")
    );
    assert_eq!(
        replay_report.reconstructed_proof_handoff_fail_closed,
        Some(false)
    );
    assert_eq!(
        replay_report.reconstructed_solver_identity_count,
        Some(handoff.solver_identities.len())
    );
    assert_eq!(
        replay_report.compact_health_summary_key_value_text(),
        format!("{}\n", summary_lines.join("\n"))
    );
    assert_eq!(
        replay_report.component_health_summary_key_value_text(),
        format!("{}\n", component_lines.join("\n"))
    );
    assert_eq!(summary_row_round_trip, summary_line_round_trip);
    assert_eq!(summary_row_round_trip, summary_text_round_trip);
    assert_eq!(
        summary_row_round_trip.status,
        PetriSuccessorTrustMcChcProofEvidenceIdentityReplayHealthSummaryRoundTripStatus::Valid
    );
    assert!(summary_row_round_trip.is_valid());
    assert!(!summary_row_round_trip.fail_closed);
    assert_eq!(summary_row_round_trip.diagnostic_count(), 0);
    assert!(summary_row_round_trip.schema_matches);
    assert!(summary_row_round_trip.status_matches);
    assert!(summary_row_round_trip.fail_closed_matches);
    assert!(summary_row_round_trip.diagnostic_count_matches);
    assert_eq!(
        summary_values
            .get("proof_evidence_identity_replay_report.schema")
            .copied(),
        Some(PETRI_SUCCESSOR_TRUST_MC_CHC_PROOF_EVIDENCE_IDENTITY_REPLAY_REPORT_SCHEMA)
    );
    assert_eq!(
        summary_values
            .get("proof_evidence_identity_replay_report.status")
            .copied(),
        Some("replayable")
    );
    assert_eq!(
        summary_values
            .get("proof_evidence_identity_replay_report.fail_closed")
            .copied(),
        Some("false")
    );
    assert_eq!(
        summary_values
            .get("proof_evidence_identity_replay_report.count.diagnostics")
            .copied(),
        Some("0")
    );
    assert_eq!(
        summary_values
            .get("proof_evidence_identity_replay_report.reconstructed.identity_digest")
            .copied(),
        Some(identity_digest.as_str())
    );
    assert_eq!(
        summary_values
            .get("proof_evidence_identity_replay_report.agreement.identity_digest")
            .copied(),
        Some("true")
    );
    assert_eq!(
        component_values
            .get("proof_evidence_identity_replay_component_summary.status")
            .copied(),
        Some("replayable")
    );
    assert_eq!(
        component_values
            .get("proof_evidence_identity_replay_component_summary.component.count")
            .copied(),
        Some("7")
    );
    assert_eq!(
        component_values
            .get("proof_evidence_identity_replay_component_summary.component.identity_digest.value")
            .copied(),
        Some(identity_digest.as_str())
    );
    assert_eq!(
        component_values
            .get(
                "proof_evidence_identity_replay_component_summary.component.identity_digest.matches"
            )
            .copied(),
        Some("true")
    );
    assert_eq!(
        component_values
            .get("proof_evidence_identity_replay_component_summary.component.function.value")
            .copied(),
        Some("0")
    );
    assert_eq!(
            component_values
                .get("proof_evidence_identity_replay_component_summary.component.proof_handoff_reason.value")
                .copied(),
            Some("ready")
        );
    assert_eq!(
            component_values
                .get("proof_evidence_identity_replay_component_summary.component.proof_handoff_reason.matches")
                .copied(),
            Some("true")
        );
    assert_eq!(
            component_values
                .get("proof_evidence_identity_replay_component_summary.component.solver_identity_count.value")
                .copied(),
            Some("1")
        );
    assert_eq!(
        summary_json
            .get("schema")
            .and_then(serde_json::Value::as_str),
        summary_values
            .get("proof_evidence_identity_replay_report.schema")
            .copied()
    );
    assert_eq!(
        summary_json
            .get("schema_version")
            .and_then(serde_json::Value::as_u64),
        summary_values
            .get("proof_evidence_identity_replay_report.schema_version")
            .and_then(|value| value.parse::<u64>().ok())
    );
    assert_eq!(
        summary_json
            .get("status")
            .and_then(serde_json::Value::as_str),
        summary_values
            .get("proof_evidence_identity_replay_report.status")
            .copied()
    );
    assert_eq!(
        summary_json
            .get("fail_closed")
            .and_then(serde_json::Value::as_bool),
        Some(false)
    );
    assert_eq!(
        summary_json
            .get("diagnostic_count")
            .and_then(serde_json::Value::as_u64),
        Some(0)
    );
    assert_eq!(
        summary_json
            .get("reconstructed_identity_digest")
            .and_then(serde_json::Value::as_str),
        Some(identity_digest.as_str())
    );
}

#[test]
fn petri_successor_trust_mc_chc_proof_evidence_identity_rows_fail_closed_on_blocked_handoff() {
    let mut blocked_bundle = native_bundle();
    blocked_bundle.module.proof_obligations[1].status = ProofStatus::Discharged;
    blocked_bundle.evidence_bundles = native_evidence_bundles(&blocked_bundle);
    remove_unreplayed_trust_vc_fixture(&mut blocked_bundle);
    let blocked_report =
        blocked_bundle.petri_successor_trust_mc_chc_proof_handoff_report(FuncId::new(0));
    let blocked_replay_report = blocked_report
        .proof_evidence_identity_replay_report(&blocked_report.proof_evidence_identity_rows());
    let blocked_values: BTreeMap<_, _> = blocked_report
        .proof_evidence_identity_rows()
        .iter()
        .map(|row| (row.key.clone(), row.value.clone()))
        .collect();

    let mut ready_bundle = native_bundle();
    ready_bundle.module.proof_obligations[1].status = ProofStatus::Discharged;
    ready_bundle.evidence_bundles = native_evidence_bundles(&ready_bundle);
    if let NativeEvidenceBundle::TrustMc(evidence) = &mut ready_bundle.evidence_bundles[1] {
        let transcript_digest = evidence
            .replay
            .transcript_digest
            .expect("TrustMc replay transcript digest");
        evidence.artifacts.push(NativeEvidenceArtifact::new(
            "trust_mc-replay.json",
            NativeEvidenceArtifactKind::ReplayTranscript,
            transcript_digest,
        ));
    } else {
        panic!("TrustMc evidence");
    }
    remove_unreplayed_trust_vc_fixture(&mut ready_bundle);
    let ready_report =
        ready_bundle.petri_successor_trust_mc_chc_proof_handoff_report(FuncId::new(0));

    if blocked_report.reason_code() == "binding_blocked" {
        assert_eq!(ready_report.reason_code(), "binding_blocked");
        assert!(blocked_report.fail_closed());
        assert!(ready_report.fail_closed());
        assert_eq!(
            blocked_report.proof_evidence_identity_digest(),
            ready_report.proof_evidence_identity_digest(),
            "uninspected replay metadata must not affect identity before proof authority"
        );
        assert!(blocked_replay_report.is_replayable());
        assert_eq!(
            blocked_values
                .get("proof_handoff.reason")
                .map(String::as_str),
            Some("binding_blocked")
        );
        return;
    }

    assert!(blocked_report.fail_closed());
    assert_eq!(blocked_report.status_code(), "blocked");
    assert_eq!(
        blocked_report.reason_code(),
        "missing_replay_transcript_artifact"
    );
    assert!(blocked_replay_report.is_replayable());
    assert_eq!(
        blocked_replay_report.reconstructed_proof_handoff_fail_closed,
        Some(true)
    );
    assert_eq!(
        blocked_replay_report
            .reconstructed_proof_handoff_status
            .as_deref(),
        Some("blocked")
    );
    assert_ne!(
        blocked_report.proof_evidence_identity_digest(),
        ready_report.proof_evidence_identity_digest(),
        "proof/evidence identity must bind fail-closed handoff status"
    );
    assert_eq!(
        blocked_values
            .get("proof_handoff.status")
            .map(String::as_str),
        Some("blocked")
    );
    assert_eq!(
        blocked_values
            .get("proof_handoff.reason")
            .map(String::as_str),
        Some("missing_replay_transcript_artifact")
    );
    assert_eq!(
        blocked_values
            .get("proof_handoff.fail_closed")
            .map(String::as_str),
        Some("true")
    );
    assert_eq!(
        blocked_values
            .get("proof_handoff.replay_transcript_artifact.present")
            .map(String::as_str),
        Some("false")
    );
    assert_eq!(
        blocked_values
            .get("proof_handoff.replay_transcript_artifact.digest")
            .map(String::as_str),
        Some("none")
    );
    assert_eq!(
        blocked_values
            .get("proof_handoff.model_artifact.present")
            .map(String::as_str),
        Some("false")
    );
    assert_eq!(
        blocked_values
            .get("proof_handoff.solver_identity.count")
            .map(String::as_str),
        Some("1")
    );
}

#[test]
fn petri_successor_trust_mc_chc_proof_evidence_identity_replay_report_fails_closed_on_bad_text() {
    let mut bundle = native_bundle();
    bundle.module.proof_obligations[1].status = ProofStatus::Discharged;
    bundle.evidence_bundles = native_evidence_bundles(&bundle);
    if let NativeEvidenceBundle::TrustMc(evidence) = &mut bundle.evidence_bundles[1] {
        let transcript_digest = evidence
            .replay
            .transcript_digest
            .expect("TrustMc replay transcript digest");
        evidence.artifacts.push(NativeEvidenceArtifact::new(
            "trust_mc-replay.json",
            NativeEvidenceArtifactKind::ReplayTranscript,
            transcript_digest,
        ));
    } else {
        panic!("TrustMc evidence");
    }

    let handoff = bundle.petri_successor_trust_mc_chc_proof_handoff_report(FuncId::new(0));
    let mut lines = handoff.proof_evidence_identity_key_value_lines();
    lines[0] = "malformed proof evidence identity line".to_string();
    if let Some(line) = lines
        .iter_mut()
        .find(|line| line.starts_with("proof_handoff.fail_closed="))
    {
        *line = "proof_handoff.fail_closed=not_bool".to_string();
    }
    lines.push("proof_evidence_identity.extra=unexpected".to_string());
    let report = handoff.proof_evidence_identity_replay_report_for_key_value_lines(&lines);
    let summary_values: BTreeMap<_, _> = report
        .compact_health_summary_rows()
        .iter()
        .map(|row| (row.key.clone(), row.value.clone()))
        .collect();
    let component_values: BTreeMap<_, _> = report
        .component_health_summary_rows()
        .iter()
        .map(|row| (row.key.clone(), row.value.clone()))
        .collect();

    assert_eq!(
        report.status,
        PetriSuccessorTrustMcChcProofEvidenceIdentityReplayStatus::Invalid
    );
    assert!(!report.is_replayable());
    assert!(report.fail_closed);
    assert!(!report.schema_matches);
    assert!(!report.proof_handoff_fail_closed_matches);
    assert_eq!(report.invalid_lines.len(), 1);
    assert_eq!(
        report.invalid_bool_keys,
        vec!["proof_handoff.fail_closed".to_string()]
    );
    assert!(
        report
            .missing_keys
            .contains(&"proof_evidence_identity.schema".to_string())
    );
    assert!(
        report
            .unexpected_keys
            .contains(&"proof_evidence_identity.extra".to_string())
    );
    assert_eq!(
        summary_values
            .get("proof_evidence_identity_replay_report.status")
            .map(String::as_str),
        Some("invalid")
    );
    assert_eq!(
        summary_values
            .get("proof_evidence_identity_replay_report.fail_closed")
            .map(String::as_str),
        Some("true")
    );
    assert_eq!(
        summary_values
            .get("proof_evidence_identity_replay_report.diagnostic.invalid_lines")
            .map(String::as_str),
        Some("1")
    );
    assert_eq!(
        summary_values
            .get("proof_evidence_identity_replay_report.diagnostic.invalid_bool_keys")
            .map(String::as_str),
        Some("1")
    );
    assert_eq!(
        component_values
            .get("proof_evidence_identity_replay_component_summary.status")
            .map(String::as_str),
        Some("invalid")
    );
    assert_eq!(
        component_values
            .get("proof_evidence_identity_replay_component_summary.fail_closed")
            .map(String::as_str),
        Some("true")
    );
    assert_eq!(
        component_values
            .get("proof_evidence_identity_replay_component_summary.component.schema.matches")
            .map(String::as_str),
        Some("false")
    );
    assert_eq!(
            component_values
                .get("proof_evidence_identity_replay_component_summary.component.proof_handoff_fail_closed.matches")
                .map(String::as_str),
            Some("false")
        );
}

#[test]
fn petri_successor_trust_mc_chc_proof_evidence_identity_health_summary_round_trip_fails_closed() {
    let mut bundle = native_bundle();
    bundle.module.proof_obligations[1].status = ProofStatus::Discharged;
    bundle.evidence_bundles = native_evidence_bundles(&bundle);
    if let NativeEvidenceBundle::TrustMc(evidence) = &mut bundle.evidence_bundles[1] {
        let transcript_digest = evidence
            .replay
            .transcript_digest
            .expect("TrustMc replay transcript digest");
        evidence.artifacts.push(NativeEvidenceArtifact::new(
            "trust_mc-replay.json",
            NativeEvidenceArtifactKind::ReplayTranscript,
            transcript_digest,
        ));
        evidence.artifacts.push(NativeEvidenceArtifact::new(
            "trust_mc-model.json",
            NativeEvidenceArtifactKind::TrustMcModel,
            digest(0xC3),
        ));
    } else {
        panic!("TrustMc evidence");
    }

    let handoff = bundle.petri_successor_trust_mc_chc_proof_handoff_report(FuncId::new(0));
    let replay_report =
        handoff.proof_evidence_identity_replay_report(&handoff.proof_evidence_identity_rows());
    let mut lines = replay_report.compact_health_summary_key_value_lines();
    lines[0] = "malformed health summary line".to_string();
    if let Some(line) = lines
        .iter_mut()
        .find(|line| line.starts_with("proof_evidence_identity_replay_report.schema_version="))
    {
        *line = "proof_evidence_identity_replay_report.schema_version=not_usize".to_string();
    }
    if let Some(line) = lines
        .iter_mut()
        .find(|line| line.starts_with("proof_evidence_identity_replay_report.fail_closed="))
    {
        *line = "proof_evidence_identity_replay_report.fail_closed=not_bool".to_string();
    }
    lines.push("proof_evidence_identity_replay_report.status=replayable".to_string());
    lines.push("proof_evidence_identity_replay_report.extra=unexpected".to_string());

    let validation =
        replay_report.compact_health_summary_round_trip_report_for_key_value_lines(&lines);

    assert_eq!(
        validation.status,
        PetriSuccessorTrustMcChcProofEvidenceIdentityReplayHealthSummaryRoundTripStatus::Invalid
    );
    assert!(!validation.is_valid());
    assert!(validation.fail_closed);
    assert_eq!(validation.invalid_lines.len(), 1);
    assert!(
        validation
            .missing_keys
            .contains(&"proof_evidence_identity_replay_report.schema".to_string())
    );
    assert!(
        validation
            .duplicate_keys
            .contains(&"proof_evidence_identity_replay_report.status".to_string())
    );
    assert!(
        validation
            .unexpected_keys
            .contains(&"proof_evidence_identity_replay_report.extra".to_string())
    );
    assert!(
        validation
            .invalid_usize_keys
            .contains(&"proof_evidence_identity_replay_report.schema_version".to_string())
    );
    assert!(
        validation
            .invalid_bool_keys
            .contains(&"proof_evidence_identity_replay_report.fail_closed".to_string())
    );
    assert!(!validation.schema_matches);
    assert!(validation.status_matches);
    assert!(!validation.fail_closed_matches);
    assert!(validation.diagnostic_count() >= 5);
}

#[test]
fn petri_successor_trust_mc_chc_proof_handoff_report_requires_proof_before_replay_artifact() {
    let mut bundle = native_bundle();
    bundle.module.proof_obligations[1].status = ProofStatus::Discharged;
    bundle.evidence_bundles = native_evidence_bundles(&bundle);
    remove_unreplayed_trust_vc_fixture(&mut bundle);

    let report = bundle.petri_successor_trust_mc_chc_proof_handoff_report(FuncId::new(0));

    assert!(!report.binding_report.is_bound());
    assert!(report.fail_closed());
    assert_eq!(report.status_code(), "blocked");
    assert_eq!(report.reason_code(), "binding_blocked");
    assert!(report.replay.is_none());
    assert!(report.replay_transcript_digest.is_none());
    assert_eq!(report.replay_transcript_artifact, None);
}

#[test]
fn petri_successor_trust_mc_chc_proof_handoff_report_does_not_inspect_stale_replay_before_proof() {
    let mut bundle = native_bundle();
    bundle.module.proof_obligations[1].status = ProofStatus::Discharged;
    bundle.evidence_bundles = native_evidence_bundles(&bundle);
    if let NativeEvidenceBundle::TrustMc(evidence) = &mut bundle.evidence_bundles[1] {
        evidence.artifacts.push(NativeEvidenceArtifact::new(
            "trust_mc-replay.json",
            NativeEvidenceArtifactKind::ReplayTranscript,
            digest(0xDD),
        ));
    } else {
        panic!("TrustMc evidence");
    }
    remove_unreplayed_trust_vc_fixture(&mut bundle);

    let report = bundle.petri_successor_trust_mc_chc_proof_handoff_report(FuncId::new(0));

    assert!(!report.binding_report.is_bound());
    assert!(report.fail_closed());
    assert_eq!(report.status_code(), "blocked");
    assert_eq!(report.reason_code(), "binding_blocked");
    assert_eq!(report.replay_transcript_artifact, None);
    assert_eq!(report.replay_transcript_digest, None);
}

#[test]
fn petri_successor_trust_mc_chc_model_validation_readiness_withholds_model_without_proof_authority()
{
    let mut bundle = native_bundle();
    bundle.module.proof_obligations[1].status = ProofStatus::Discharged;
    bundle.evidence_bundles = native_evidence_bundles(&bundle);
    if let NativeEvidenceBundle::TrustMc(evidence) = &mut bundle.evidence_bundles[1] {
        let transcript_digest = evidence
            .replay
            .transcript_digest
            .expect("TrustMc replay transcript digest");
        evidence.artifacts.push(NativeEvidenceArtifact::new(
            "trust_mc-replay.json",
            NativeEvidenceArtifactKind::ReplayTranscript,
            transcript_digest,
        ));
        evidence.artifacts.push(NativeEvidenceArtifact::new(
            "trust_mc-model.json",
            NativeEvidenceArtifactKind::TrustMcModel,
            digest(0xC3),
        ));
    } else {
        panic!("TrustMc evidence");
    }
    remove_unreplayed_trust_vc_fixture(&mut bundle);

    let report =
        bundle.petri_successor_trust_mc_chc_model_validation_readiness_report(FuncId::new(0));

    assert_eq!(
        report.schema,
        PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_VALIDATION_READINESS_SCHEMA
    );
    assert_eq!(
        report.schema_version,
        PETRI_SUCCESSOR_TRUST_MC_CHC_MODEL_VALIDATION_READINESS_SCHEMA_VERSION
    );
    assert!(!report.proof_handoff_report.is_ready());
    assert!(!report.is_ready_for_solver_validation());
    assert!(
        report.fail_closed(),
        "TrustIr must not mark solver model validation accepted"
    );
    assert!(!report.model_validated);
    assert_eq!(report.status_code(), "blocked");
    assert_eq!(report.reason_code(), "proof_handoff_blocked");
    assert_eq!(report.model_artifact, None);
    assert_eq!(report.model_artifact_digest, None);
    assert!(report.solver_identities.is_empty());
}

#[test]
fn petri_successor_trust_mc_chc_model_validation_readiness_requires_proof_before_model_artifact() {
    let mut bundle = native_bundle();
    bundle.module.proof_obligations[1].status = ProofStatus::Discharged;
    bundle.evidence_bundles = native_evidence_bundles(&bundle);
    if let NativeEvidenceBundle::TrustMc(evidence) = &mut bundle.evidence_bundles[1] {
        let transcript_digest = evidence
            .replay
            .transcript_digest
            .expect("TrustMc replay transcript digest");
        evidence.artifacts.push(NativeEvidenceArtifact::new(
            "trust_mc-replay.json",
            NativeEvidenceArtifactKind::ReplayTranscript,
            transcript_digest,
        ));
    } else {
        panic!("TrustMc evidence");
    }
    remove_unreplayed_trust_vc_fixture(&mut bundle);

    let report =
        bundle.petri_successor_trust_mc_chc_model_validation_readiness_report(FuncId::new(0));

    assert!(!report.proof_handoff_report.is_ready());
    assert!(!report.is_ready_for_solver_validation());
    assert!(report.fail_closed());
    assert!(!report.model_validated);
    assert_eq!(report.status_code(), "blocked");
    assert_eq!(report.reason_code(), "proof_handoff_blocked");
    assert_eq!(report.model_artifact, None);
    assert_eq!(report.model_artifact_digest, None);
    assert!(report.solver_identities.is_empty());
}

#[test]
fn petri_successor_trust_mc_chc_model_validation_readiness_blocks_on_handoff() {
    let mut bundle = native_bundle();
    bundle.module.proof_obligations[1].status = ProofStatus::Discharged;
    bundle.evidence_bundles = native_evidence_bundles(&bundle);
    remove_unreplayed_trust_vc_fixture(&mut bundle);

    let report =
        bundle.petri_successor_trust_mc_chc_model_validation_readiness_report(FuncId::new(0));

    assert!(report.proof_handoff_report.fail_closed());
    assert_eq!(report.proof_handoff_report.reason_code(), "binding_blocked");
    assert!(!report.is_ready_for_solver_validation());
    assert!(report.fail_closed());
    assert!(!report.model_validated);
    assert_eq!(report.status_code(), "blocked");
    assert_eq!(report.reason_code(), "proof_handoff_blocked");
    assert_eq!(report.model_artifact, None);
    assert!(report.solver_identities.is_empty());
}

#[test]
fn native_evidence_consumption_report_rejects_invalid_evidence() {
    let mut bundle = native_bundle();
    bundle.evidence_bundles = native_evidence_bundles(&bundle);
    match &mut bundle.evidence_bundles[0] {
        NativeEvidenceBundle::TrustVc(evidence) => evidence.request_digest = digest(0xAB),
        _ => panic!("TrustVc evidence"),
    }

    let errors = bundle
        .native_evidence_consumption_report()
        .expect_err("invalid evidence is not consumed");

    assert!(errors.iter().any(|error| {
        matches!(
            error,
            NativeVerificationBundleError::EvidenceRequestDigestMismatch { .. }
        )
    }));
}

#[test]
fn native_evidence_consumption_report_rejects_verifier_identity_mismatch() {
    let mut bundle = native_bundle();
    bundle.evidence_bundles = native_evidence_bundles(&bundle);
    let expected_request_digest = bundle.requests[0].stable_digest();
    match &mut bundle.evidence_bundles[0] {
        NativeEvidenceBundle::TrustVc(evidence) => {
            evidence.verifier = NativeToolIdentity::new("trust_vc")
                .with_version("semantics-v2")
                .with_digest(digest(0xDD));
            assert_eq!(evidence.request_digest, expected_request_digest);
        }
        _ => panic!("TrustVc evidence"),
    }

    let errors = bundle
        .native_evidence_consumption_report()
        .expect_err("verifier identity drift is not consumed");

    assert!(errors.iter().any(|error| {
        matches!(
            error,
            NativeVerificationBundleError::EvidenceProvenanceMismatch {
                request: NativeRequestId(0),
                field: "verifier",
            }
        )
    }));
}

#[test]
fn native_evidence_consumption_report_rejects_solver_identity_mismatch() {
    let mut bundle = native_bundle();
    bundle.evidence_bundles = native_evidence_bundles(&bundle);
    let expected_request_digest = bundle.requests[0].stable_digest();
    match &mut bundle.evidence_bundles[0] {
        NativeEvidenceBundle::TrustVc(evidence) => {
            evidence.solvers[0] = NativeToolIdentity::new("lean4").with_version("4.19.0");
            assert_eq!(evidence.request_digest, expected_request_digest);
        }
        _ => panic!("TrustVc evidence"),
    }

    let errors = bundle
        .native_evidence_consumption_report()
        .expect_err("solver identity drift is not consumed");

    assert!(errors.iter().any(|error| {
        matches!(
            error,
            NativeVerificationBundleError::EvidenceProvenanceMismatch {
                request: NativeRequestId(0),
                field: "solvers",
            }
        )
    }));
}

#[test]
fn native_evidence_consumption_report_rejects_replay_transcript_mismatch() {
    let mut bundle = native_bundle();
    bundle.evidence_bundles = native_evidence_bundles(&bundle);
    let expected_request_digest = bundle.requests[0].stable_digest();
    match &mut bundle.evidence_bundles[0] {
        NativeEvidenceBundle::TrustVc(evidence) => {
            evidence.replay.transcript_digest = Some(digest(0xDE));
            assert_eq!(evidence.request_digest, expected_request_digest);
        }
        _ => panic!("TrustVc evidence"),
    }

    let errors = bundle
        .native_evidence_consumption_report()
        .expect_err("replay transcript drift is not consumed");

    assert!(errors.iter().any(|error| {
        matches!(
            error,
            NativeVerificationBundleError::EvidenceProvenanceMismatch {
                request: NativeRequestId(0),
                field: "replay",
            }
        )
    }));
}

#[test]
fn native_request_provenance_helpers_keep_suite_typed() {
    let provenance = NativeRequestProvenance::trust_mc(
        NativeToolIdentity::new("trust_mc").with_version("chc-v1"),
    )
    .with_solver(NativeToolIdentity::new("z3").with_version("4.13.0"));

    assert_eq!(provenance.verifier_suite(), NativeVerifierSuite::TrustMc);
    assert_eq!(provenance.expected_verifier().name.as_str(), "trust_mc");
    assert_eq!(provenance.solver_identities()[0].name.as_str(), "z3");

    let bundle = native_bundle();
    let request = &bundle.requests[1];
    assert_eq!(request.verifier_suite(), NativeVerifierSuite::TrustMc);
    assert_eq!(
        request.expected_verifier_identity().name.as_str(),
        "trust_mc"
    );
    assert_eq!(request.solver_identities()[0].name.as_str(), "z3");
}

#[test]
fn native_tool_identity_canonicalizes_display_spelling() {
    assert_eq!(
        NativeToolIdentity::new("  TrustMc.Native_PDR  ").canonical_name(),
        "trust_mc-native-pdr"
    );
    assert_eq!(NativeToolIdentity::new("tRust").canonical_name(), "trust");
}

#[test]
fn native_bundle_rejects_missing_function_and_unbound_obligation() {
    let mut bundle = native_bundle();
    if let NativeVerificationRequest::TrustMc(request) = &mut bundle.requests[1] {
        request.function = FuncId::new(99);
        request.obligations.push(ProofId::new(99));
    }

    let errors = bundle.validate().expect_err("invalid request rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::MissingFunction {
            request: NativeRequestId(1),
            function: FuncId(99)
        }
    )));
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::UnknownRequestObligation {
            request: NativeRequestId(1),
            obligation: ProofId(99)
        }
    )));
}

#[test]
fn native_bundle_rejects_function_request_for_cross_function_obligation() {
    let mut bundle = native_bundle();
    let ft = bundle.module.functions[0].ty;
    let mut other = Function::new(FuncId::new(1), "other_checked_add", ft, BlockId::new(1));
    other
        .blocks
        .push(Block::new(BlockId::new(1)).with_param(ValueId::new(10), Ty::I32));
    bundle.module.add_function(other);

    if let NativeVerificationRequest::TrustMc(request) = &mut bundle.requests[1] {
        request.function = FuncId::new(1);
    }

    let errors = bundle
        .validate()
        .expect_err("cross-function obligation rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::RequestObligationFunctionMismatch {
            request: NativeRequestId(1),
            obligation: ProofId(1),
            expected: FuncId(1),
            actual: Some(FuncId(0)),
        }
    )));
}

#[test]
fn native_bundle_rejects_source_map_cast_fact_from_another_function() {
    let mut bundle = native_bundle();
    let ft = bundle.module.functions[0].ty;
    let mut other = Function::new(FuncId::new(1), "other_checked_add", ft, BlockId::new(1));
    other
        .blocks
        .push(Block::new(BlockId::new(1)).with_param(ValueId::new(10), Ty::I32));
    bundle.module.add_function(other);
    bundle.compiler_facts.casts.push(NativeCastFact {
        id: NativeCompilerFactId::new(10),
        function: FuncId::new(1),
        result: None,
        op: CastOp::ZExt,
        source_ty: Ty::I32,
        target_ty: Ty::I64,
        evidence: CastLayoutEvidence::NotLayoutSensitive,
        span: Some(SourceSpan {
            file: 0,
            line: 22,
            col: 7,
        }),
        obligations: vec![ProofId::new(1)],
    });
    bundle.compiler_facts.obligation_sources[1]
        .facts
        .push(NativeCompilerFactRef::Cast(NativeCompilerFactId::new(10)));

    let errors = bundle
        .validate()
        .expect_err("cross-function source-map cast fact rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::ObligationSourceFactFunctionMismatch {
            obligation: ProofId(1),
            fact: NativeCompilerFactRef::Cast(NativeCompilerFactId(10)),
            expected: Some(FuncId(0)),
            actual: Some(FuncId(1)),
        }
    )));
}

#[test]
fn native_bundle_rejects_source_map_cast_fact_for_unlisted_obligation() {
    let mut bundle = native_bundle();
    bundle.compiler_facts.casts.push(NativeCastFact {
        id: NativeCompilerFactId::new(11),
        function: FuncId::new(0),
        result: None,
        op: CastOp::ZExt,
        source_ty: Ty::I32,
        target_ty: Ty::I64,
        evidence: CastLayoutEvidence::NotLayoutSensitive,
        span: Some(SourceSpan {
            file: 0,
            line: 23,
            col: 9,
        }),
        obligations: vec![ProofId::new(0)],
    });
    bundle.compiler_facts.obligation_sources[1]
        .facts
        .push(NativeCompilerFactRef::Cast(NativeCompilerFactId::new(11)));

    let errors = bundle
        .validate()
        .expect_err("source-map cast fact for another obligation rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::ObligationSourceFactObligationMismatch {
            obligation: ProofId(1),
            fact: NativeCompilerFactRef::Cast(NativeCompilerFactId(11)),
        }
    )));
}

#[test]
fn native_bundle_rejects_cast_check_source_without_bound_cast_fact() {
    let mut bundle = native_bundle();
    bundle.compiler_facts.obligation_sources[1].cause = NativeObligationCause::CastCheck;

    let errors = bundle
        .validate()
        .expect_err("cast-check source without bound cast fact rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::MissingObligationSourceCastFact {
            obligation: ProofId(1),
        }
    )));
}

fn add_pointer_offset_ir(bundle: &mut NativeVerificationBundle) {
    let func_ty = bundle.module.functions[0].ty;
    bundle.module.func_types[func_ty.as_usize()].params = vec![Ty::Ptr, Ty::I64];
    let function = &mut bundle.module.functions[0];
    function.blocks[0].params = vec![(ValueId::new(0), Ty::Ptr), (ValueId::new(1), Ty::I64)];
    function.blocks[0].body.push(
        InstrNode::new(Inst::GEP {
            pointee_ty: Ty::I32,
            base: ValueId::new(0),
            indices: vec![ValueId::new(1)],
            inbounds: false,
        })
        .with_result(ValueId::new(20)),
    );
}

fn pointer_offset_fact(bundle: &NativeVerificationBundle) -> NativePointerOffsetFact {
    NativePointerOffsetFact {
        id: NativeCompilerFactId::new(40),
        function: FuncId::new(0),
        result: Some(ValueId::new(20)),
        base: ValueId::new(0),
        base_ty: Ty::Ptr,
        pointee_ty: Ty::I32,
        element_layout: bundle.module.ty_layout_shape(&Ty::I32).expect("i32 layout"),
        stride_bits: 32,
        offset: ValueId::new(1),
        offset_ty: Ty::I64,
        signed_offset_const: Some(1),
        provenance: NativePointerOffsetProvenance::SameAsBase,
        span: Some(SourceSpan {
            file: 0,
            line: 25,
            col: 13,
        }),
        obligations: vec![ProofId::new(1)],
    }
}

#[test]
fn native_bundle_accepts_bound_pointer_offset_fact() {
    let mut bundle = native_bundle();
    add_pointer_offset_ir(&mut bundle);
    let fact = pointer_offset_fact(&bundle);
    bundle.compiler_facts.pointer_offsets.push(fact);
    bundle.compiler_facts.obligation_sources[1].cause = NativeObligationCause::PointerOffset;
    bundle.compiler_facts.obligation_sources[1]
        .facts
        .push(NativeCompilerFactRef::PointerOffset(
            NativeCompilerFactId::new(40),
        ));

    remove_unreplayed_trust_vc_fixture(&mut bundle);
    refresh_native_bundle_module_identity(&mut bundle);
    bundle
        .validate()
        .expect("matching pointer-offset fact accepted");
}

#[test]
fn native_bundle_rejects_pointer_offset_source_without_bound_fact() {
    let mut bundle = native_bundle();
    add_pointer_offset_ir(&mut bundle);
    bundle.compiler_facts.obligation_sources[1].cause = NativeObligationCause::PointerOffset;

    let errors = bundle
        .validate()
        .expect_err("pointer-offset source without fact rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::MissingObligationSourcePointerOffsetFact {
            obligation: ProofId(1),
        }
    )));
}

#[test]
fn native_bundle_rejects_pointer_offset_fact_with_unmatched_result() {
    let mut bundle = native_bundle();
    add_pointer_offset_ir(&mut bundle);
    let mut fact = pointer_offset_fact(&bundle);
    fact.pointee_ty = Ty::I64;
    fact.element_layout = bundle.module.ty_layout_shape(&Ty::I64).expect("i64 layout");
    fact.stride_bits = 64;
    bundle.compiler_facts.pointer_offsets.push(fact);
    bundle.compiler_facts.obligation_sources[1].cause = NativeObligationCause::PointerOffset;
    bundle.compiler_facts.obligation_sources[1]
        .facts
        .push(NativeCompilerFactRef::PointerOffset(
            NativeCompilerFactId::new(40),
        ));

    let errors = bundle
        .validate()
        .expect_err("pointer-offset fact result mismatch rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::InvalidCompilerFact {
            fact: NativeCompilerFactRef::PointerOffset(NativeCompilerFactId(40)),
            field: "result",
        }
    )));
}

#[test]
fn native_bundle_rejects_unsupported_bound_pointer_offset_fact() {
    let mut bundle = native_bundle();
    add_pointer_offset_ir(&mut bundle);
    let mut fact = pointer_offset_fact(&bundle);
    fact.provenance = NativePointerOffsetProvenance::Unsupported(NativeUnsupportedMode::new(
        NativeUnsupportedModeReason::UnsupportedCompilerFact,
        "non-linear raw-pointer offset expression",
    ));
    bundle.compiler_facts.pointer_offsets.push(fact);
    bundle.compiler_facts.obligation_sources[1].cause = NativeObligationCause::PointerOffset;
    bundle.compiler_facts.obligation_sources[1]
        .facts
        .push(NativeCompilerFactRef::PointerOffset(
            NativeCompilerFactId::new(40),
        ));

    let errors = bundle
        .validate()
        .expect_err("unsupported pointer-offset fact rejected fail-closed");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::InvalidCompilerFact {
            fact: NativeCompilerFactRef::PointerOffset(NativeCompilerFactId(40)),
            field: "provenance",
        }
    )));
}

fn add_trait_object_fat_pointer_fact(bundle: &mut NativeVerificationBundle) {
    let ty = Ty::FatPtr(crate::FatPtrKind::TraitObject { trait_id: 7 });
    bundle
        .compiler_facts
        .fat_pointers
        .push(NativeFatPointerFact {
            id: NativeCompilerFactId::new(30),
            layout: ty
                .pointer_layout_shape(bundle.module.pointer_bits())
                .expect("trait object fat pointer layout"),
            ty,
        });
}

fn add_trait_object_metadata_fact(bundle: &mut NativeVerificationBundle, ty: Ty) {
    bundle
        .compiler_facts
        .trait_object_metadata
        .push(NativeTraitObjectMetadataFact {
            id: NativeCompilerFactId::new(31),
            ty,
            source_ty: Some(Ty::FatPtr(crate::FatPtrKind::TraitObject { trait_id: 3 })),
            trait_id: 7,
            source_trait_id: Some(3),
            upcast_path: vec![3, 7],
            vtable_symbol: "_RNvNtCs_test_Target_vtable_for_Source".to_string(),
            stable_digest: ProofDigest::sha256_domain(
                "trust.trait_object_metadata.v1",
                b"source-dyn3-to-target-dyn7",
            ),
            function: Some(FuncId::new(0)),
            obligations: vec![ProofId::new(1)],
        });
}

#[test]
fn native_bundle_accepts_trait_object_vtable_upcast_metadata_identity_fact() {
    let mut bundle = native_bundle();
    let ty = Ty::FatPtr(crate::FatPtrKind::TraitObject { trait_id: 7 });
    add_trait_object_fat_pointer_fact(&mut bundle);
    add_trait_object_metadata_fact(&mut bundle, ty);
    bundle.compiler_facts.obligation_sources[1]
        .facts
        .push(NativeCompilerFactRef::FatPointer(
            NativeCompilerFactId::new(30),
        ));
    bundle.compiler_facts.obligation_sources[1].facts.push(
        NativeCompilerFactRef::TraitObjectMetadata(NativeCompilerFactId::new(31)),
    );

    remove_unreplayed_trust_vc_fixture(&mut bundle);
    refresh_native_bundle_module_identity(&mut bundle);
    bundle
        .validate()
        .expect("matching trait-object metadata identity accepted");
}

#[test]
fn native_bundle_rejects_trait_object_fat_pointer_source_without_metadata_identity() {
    let mut bundle = native_bundle();
    add_trait_object_fat_pointer_fact(&mut bundle);
    bundle.compiler_facts.obligation_sources[1]
        .facts
        .push(NativeCompilerFactRef::FatPointer(
            NativeCompilerFactId::new(30),
        ));

    let errors = bundle
        .validate()
        .expect_err("trait-object source without metadata identity rejected");

    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::MissingObligationSourceTraitObjectMetadataFact {
            obligation: ProofId(1),
            fat_pointer: NativeCompilerFactId(30),
        }
    )));
}

#[test]
fn native_bundle_rejects_mismatched_trait_object_metadata_identity_source() {
    let mut bundle = native_bundle();
    add_trait_object_fat_pointer_fact(&mut bundle);
    add_trait_object_metadata_fact(
        &mut bundle,
        Ty::FatPtr(crate::FatPtrKind::TraitObject { trait_id: 8 }),
    );
    bundle.compiler_facts.trait_object_metadata[0].trait_id = 8;
    bundle.compiler_facts.trait_object_metadata[0].upcast_path = vec![3, 8];
    bundle.compiler_facts.obligation_sources[1]
        .facts
        .push(NativeCompilerFactRef::FatPointer(
            NativeCompilerFactId::new(30),
        ));
    bundle.compiler_facts.obligation_sources[1].facts.push(
        NativeCompilerFactRef::TraitObjectMetadata(NativeCompilerFactId::new(31)),
    );

    let errors = bundle
        .validate()
        .expect_err("mismatched trait-object metadata identity rejected");

    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::MissingObligationSourceTraitObjectMetadataFact {
            obligation: ProofId(1),
            fat_pointer: NativeCompilerFactId(30),
        }
    )));
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::ObligationSourceFactObligationMismatch {
            obligation: ProofId(1),
            fact: NativeCompilerFactRef::TraitObjectMetadata(NativeCompilerFactId(31)),
        }
    )));
}

#[test]
fn native_bundle_accepts_source_map_cast_fact_for_matching_result() {
    let mut bundle = native_bundle();
    bundle.module.functions[0].blocks[0].body.push(
        InstrNode::new(Inst::Cast {
            op: CastOp::ZExt,
            src_ty: Ty::I32,
            dst_ty: Ty::I64,
            operand: ValueId::new(0),
        })
        .with_result(ValueId::new(20)),
    );
    bundle.compiler_facts.casts.push(NativeCastFact {
        id: NativeCompilerFactId::new(12),
        function: FuncId::new(0),
        result: Some(ValueId::new(20)),
        op: CastOp::ZExt,
        source_ty: Ty::I32,
        target_ty: Ty::I64,
        evidence: CastLayoutEvidence::NotLayoutSensitive,
        span: Some(SourceSpan {
            file: 0,
            line: 24,
            col: 11,
        }),
        obligations: vec![ProofId::new(1)],
    });
    bundle.compiler_facts.obligation_sources[1]
        .facts
        .push(NativeCompilerFactRef::Cast(NativeCompilerFactId::new(12)));

    remove_unreplayed_trust_vc_fixture(&mut bundle);
    refresh_native_bundle_module_identity(&mut bundle);
    bundle
        .validate()
        .expect("matching source-map cast result accepted");
}

#[test]
fn native_bundle_rejects_source_map_cast_fact_with_unmatched_result() {
    let mut bundle = native_bundle();
    bundle.module.functions[0].blocks[0].body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(0),
        })
        .with_result(ValueId::new(20)),
    );
    bundle.compiler_facts.casts.push(NativeCastFact {
        id: NativeCompilerFactId::new(12),
        function: FuncId::new(0),
        result: Some(ValueId::new(20)),
        op: CastOp::ZExt,
        source_ty: Ty::I32,
        target_ty: Ty::I64,
        evidence: CastLayoutEvidence::NotLayoutSensitive,
        span: Some(SourceSpan {
            file: 0,
            line: 24,
            col: 11,
        }),
        obligations: vec![ProofId::new(1)],
    });
    bundle.compiler_facts.obligation_sources[1]
        .facts
        .push(NativeCompilerFactRef::Cast(NativeCompilerFactId::new(12)));

    let errors = bundle
        .validate()
        .expect_err("source-map cast fact result must bind matching cast");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::InvalidCompilerFact {
            fact: NativeCompilerFactRef::Cast(NativeCompilerFactId(12)),
            field: "result",
        }
    )));
}

#[test]
fn native_bundle_rejects_functionless_source_map_for_function_scoped_fact() {
    let mut bundle = native_bundle();
    bundle.requests.truncate(1);
    bundle.compiler_facts.obligation_sources[0].function = None;

    let errors = bundle
        .validate()
        .expect_err("functionless source map for function-scoped fact rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::ObligationSourceFactFunctionMismatch {
            obligation: ProofId(0),
            fact: NativeCompilerFactRef::Monomorphization(NativeMonomorphizationId(0)),
            expected: None,
            actual: Some(FuncId(0)),
        }
    )));
}

#[test]
fn native_bundle_rejects_source_map_monomorphization_fact_mismatch() {
    let mut bundle = native_bundle();
    bundle
        .compiler_facts
        .monomorphizations
        .push(NativeMonomorphizationFact {
            id: NativeMonomorphizationId::new(1),
            source_item: "checked_add".to_string(),
            symbol: "_RNvCs_test_checked_add_alt".to_string(),
            generic_args: vec![NativeGenericArg::Ty(Ty::I32)],
            function: Some(FuncId::new(0)),
            stable_digest: ProofDigest::sha256_domain(
                "trust.monomorphization.v1",
                b"checked_add::<i32>#alt",
            ),
        });
    bundle.compiler_facts.obligation_sources[1].facts.push(
        NativeCompilerFactRef::Monomorphization(NativeMonomorphizationId::new(1)),
    );

    let errors = bundle
        .validate()
        .expect_err("mismatched source-map monomorphization rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::ObligationSourceFactMonomorphizationMismatch {
            obligation: ProofId(1),
            expected: NativeMonomorphizationId(0),
            actual: NativeMonomorphizationId(1),
        }
    )));
}

#[test]
fn native_bundle_rejects_aliased_monomorphization_identities() {
    let mut bundle = native_bundle();
    let first = bundle.compiler_facts.monomorphizations[0].clone();
    bundle
        .compiler_facts
        .monomorphizations
        .push(NativeMonomorphizationFact {
            id: NativeMonomorphizationId::new(1),
            source_item: "checked_add_alias".to_string(),
            symbol: first.symbol,
            generic_args: vec![NativeGenericArg::Ty(Ty::U32)],
            function: Some(FuncId::new(0)),
            stable_digest: first.stable_digest,
        });

    let errors = bundle
        .validate()
        .expect_err("aliased monomorphization digest and symbol rejected");
    for field in ["stable_digest.duplicate", "symbol.duplicate"] {
        assert!(
            errors.iter().any(|err| matches!(
                err,
                NativeVerificationBundleError::InvalidCompilerFact {
                    fact: NativeCompilerFactRef::Monomorphization(
                        NativeMonomorphizationId(1)
                    ),
                    field: actual,
                } if *actual == field
            )),
            "missing {field} rejection: {errors:?}"
        );
    }
}

#[test]
fn native_bundle_rejects_malformed_monomorphization_identity_fields() {
    let mut bundle = native_bundle();
    let fact = &mut bundle.compiler_facts.monomorphizations[0];
    fact.source_item = " checked_add".to_string();
    fact.symbol = "_RNvCs_test_checked_add\n".to_string();
    fact.generic_args = vec![NativeGenericArg::Ty(Ty::Tuple(vec![Ty::Error]))];

    let errors = bundle
        .validate()
        .expect_err("noncanonical monomorphization text and Ty::Error rejected");
    for field in ["source_item", "symbol", "generic_args[].ty"] {
        assert!(
            errors.iter().any(|err| matches!(
                err,
                NativeVerificationBundleError::InvalidCompilerFact {
                    fact: NativeCompilerFactRef::Monomorphization(
                        NativeMonomorphizationId(0)
                    ),
                    field: actual,
                } if *actual == field
            )),
            "missing {field} rejection: {errors:?}"
        );
    }
}

#[test]
fn native_bundle_requires_exact_monomorphization_source_fact_binding() {
    let mut missing = native_bundle();
    missing.compiler_facts.obligation_sources[1].facts.clear();
    let errors = missing
        .validate()
        .expect_err("declared monomorphization without its fact reference rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::InvalidCompilerFact {
            fact: NativeCompilerFactRef::Monomorphization(NativeMonomorphizationId(0)),
            field: "obligation_sources[].facts.monomorphization",
        }
    )));

    let mut unexpected = native_bundle();
    unexpected.compiler_facts.obligation_sources[1].monomorphization = None;
    let errors = unexpected
        .validate()
        .expect_err("monomorphization fact reference without a declaration rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::InvalidCompilerFact {
            fact: NativeCompilerFactRef::Monomorphization(NativeMonomorphizationId(0)),
            field: "obligation_sources[].monomorphization",
        }
    )));

    let mut duplicate = native_bundle();
    duplicate.compiler_facts.obligation_sources[1].facts.push(
        NativeCompilerFactRef::Monomorphization(NativeMonomorphizationId::new(0)),
    );
    let errors = duplicate
        .validate()
        .expect_err("duplicate monomorphization fact reference rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::InvalidCompilerFact {
            fact: NativeCompilerFactRef::Monomorphization(NativeMonomorphizationId(0)),
            field: "obligation_sources[].facts.duplicate",
        }
    )));
}

#[test]
fn native_bundle_rejects_out_of_range_monomorphization_const_arg() {
    let mut bundle = native_bundle();
    bundle.compiler_facts.monomorphizations[0]
        .generic_args
        .push(NativeGenericArg::Const {
            ty: Ty::U8,
            value: Constant::Int(-1),
        });

    let errors = bundle
        .validate()
        .expect_err("out-of-range const generic arg rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::InvalidCompilerFact {
            fact: NativeCompilerFactRef::Monomorphization(NativeMonomorphizationId(0)),
            field: "generic_args[].const",
        }
    )));
}

#[test]
fn native_bundle_rejects_stale_trust_vc_certificate_digest() {
    let mut bundle = native_bundle();
    if let NativeVerificationRequest::TrustVc(request) = &mut bundle.requests[0] {
        request.certificates[0].evidence_digest = digest(0xFF);
    }

    let errors = bundle
        .validate()
        .expect_err("stale certificate digest rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::CertificateDigestMismatch {
            request: NativeRequestId(0),
            obligation: ProofId(0),
            prover
        } if prover == "trust_vc"
    )));
}

#[test]
fn native_bundle_rejects_trust_vc_certificate_for_pending_obligation() {
    let mut bundle = native_bundle();
    let pending_cert = ProofCertificate {
        obligation: ProofId::new(1),
        prover: "trust_vc".to_string(),
        evidence: ProofEvidence::LeanProof("exact stale_pending_certificate".to_string()),
    };
    let pending_ref = pending_cert.lineage_ref();
    bundle.module.proof_certificates.push(pending_cert);
    bundle.lineage.nodes[0]
        .certificates
        .push(pending_ref.clone());
    if let NativeVerificationRequest::TrustVc(request) = &mut bundle.requests[0] {
        request.obligations.push(ProofId::new(1));
        request.certificates.push(pending_ref);
    }

    let errors = bundle
        .validate()
        .expect_err("pending TrustVc certificate rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::TrustVcCertificateNotDischarged {
            request: NativeRequestId(0),
            obligation: ProofId(1),
            prover,
            status: ProofStatus::Pending,
        } if prover == "trust_vc"
    )));
}

#[test]
fn native_bundle_rejects_forged_discharged_smt_proof() {
    let mut bundle = native_bundle();
    assert_eq!(
        bundle.module.proof_obligations[0].status,
        ProofStatus::Discharged
    );
    let forged = ProofCertificate {
        obligation: ProofId::new(0),
        prover: "trust_vc".to_string(),
        evidence: ProofEvidence::SmtProof(b"(forged opaque solver output)".to_vec()),
    };
    let forged_ref = forged.lineage_ref();
    bundle.module.proof_certificates[0] = forged;
    bundle.lineage.nodes[0].certificates[0] = forged_ref.clone();
    let NativeVerificationRequest::TrustVc(request) = &mut bundle.requests[0] else {
        panic!("fixture request 0 is TrustVc");
    };
    request.certificates[0] = forged_ref;

    let errors = bundle
        .validate()
        .expect_err("opaque SMT bytes plus Discharged label must not authorize TrustVc");
    assert!(errors.iter().any(|error| matches!(
        error,
        NativeVerificationBundleError::TrustVcCertificateNotDischarged {
            request: NativeRequestId(0),
            obligation: ProofId(0),
            status: ProofStatus::Discharged,
            ..
        }
    )));
}

#[test]
fn native_bundle_rejects_faith_stamped_certified_trust_vc_certificate() {
    // SOUNDNESS: a `Certified` obligation with NO lineage-bound CleanCic
    // evidence is faith-stamped. It must be treated as `Trusted`-strength
    // and rejected (not admitted as discharged) — exactly the hole this
    // fix closes.
    let mut bundle = native_bundle();
    bundle.module.proof_obligations[0].status = ProofStatus::Certified;

    let errors = bundle
        .validate()
        .expect_err("faith-stamped Certified TrustVc certificate rejected");
    assert!(
        errors.iter().any(|err| matches!(
            err,
            NativeVerificationBundleError::TrustVcCertificateNotDischarged {
                request: NativeRequestId(0),
                obligation: ProofId(0),
                prover,
                status: ProofStatus::Certified,
            } if prover == "trust_vc"
        )),
        "got: {errors:?}"
    );
}

// A kernel-less consumer must reject even a lineage-matching, non-empty
// CleanCic payload. Both the bytes and digest are producer-controlled; only an
// in-process kernel judgment can promote `Certified` to discharged.
#[cfg(not(feature = "clean-expr"))]
#[test]
fn native_bundle_rejects_lineage_only_certified_trust_vc_certificate() {
    let mut bundle = native_bundle();
    bundle.module.proof_obligations[0].status = ProofStatus::Certified;
    let lineage = crate::proof::clean_cic_lineage_digest(&bundle.module.proof_obligations[0]);
    let clean_cic = ProofCertificate {
        obligation: ProofId::new(0),
        prover: "clean-cic".to_string(),
        evidence: ProofEvidence::CleanCic {
            term: vec![1, 2, 3],
            context: vec![4, 5],
            lineage,
            kernel_recheck: None,
        },
    };
    let clean_ref = clean_cic.lineage_ref();
    bundle.module.proof_certificates.push(clean_cic);
    bundle.lineage.nodes[0].certificates.push(clean_ref);

    let errors = bundle
        .validate()
        .expect_err("kernel-less bundle must reject lineage-only Certified evidence");
    assert!(
        errors.iter().any(|err| matches!(
            err,
            NativeVerificationBundleError::TrustVcCertificateNotDischarged {
                request: NativeRequestId(0),
                obligation: ProofId(0),
                status: ProofStatus::Certified,
                ..
            }
        )),
        "lineage-only Certified evidence must be rejected, got: {errors:?}"
    );
}

#[test]
fn native_bundle_rejects_request_lineage_root_for_different_target_module() {
    let mut bundle = native_bundle();
    let original_root = bundle.lineage.nodes[0].clone();
    bundle.lineage.nodes[0].target_module = digest(0xB0);
    bundle.lineage.nodes.push(ProofLineageNode::new(
        ProofLineageId::new(1),
        ProofTransform::new(
            ProofTransformStage::Frontend,
            "rustc-mir-to-trust_ir",
            "tRust",
            "native-request-schema-v1",
        ),
        original_root.source_module,
        bundle.trust_ir_module_digest,
    ));
    bundle.lineage.nodes[1].obligations.push(ProofId::new(1));
    bundle.lineage.roots.push(ProofLineageId::new(1));

    let errors = bundle
        .validate()
        .expect_err("request lineage root for another target rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::RequestLineageRootTargetMismatch {
            request: NativeRequestId(0),
            root: ProofLineageId(0),
            expected,
            actual,
        } if *expected == bundle.trust_ir_module_digest && *actual == digest(0xB0)
    )));
}

#[test]
fn native_bundle_rejects_duplicate_request_lineage_roots() {
    let mut bundle = native_bundle();
    if let NativeVerificationRequest::TrustVc(request) = &mut bundle.requests[0] {
        request.lineage_roots.push(ProofLineageId::new(0));
    }

    let errors = bundle
        .validate()
        .expect_err("duplicate request lineage root rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::DuplicateRequestLineageRoot {
            request: NativeRequestId(0),
            root: ProofLineageId(0),
        }
    )));
}

#[test]
fn native_bundle_rejects_request_lineage_without_input_source_digest() {
    let mut bundle = native_bundle();
    let original_root = bundle.lineage.nodes[0].clone();
    bundle.lineage.nodes[0].source_module = digest(0xB1);
    bundle.lineage.nodes.push(ProofLineageNode::new(
        ProofLineageId::new(1),
        ProofTransform::new(
            ProofTransformStage::Frontend,
            "rustc-mir-to-trust_ir",
            "tRust",
            "native-request-schema-v1",
        ),
        original_root.source_module,
        bundle.trust_ir_module_digest,
    ));
    bundle.lineage.nodes[1].obligations.push(ProofId::new(1));
    bundle.lineage.roots.push(ProofLineageId::new(1));

    let errors = bundle
        .validate()
        .expect_err("request lineage without input source digest rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::RequestSourceDigestNotInLineage {
            request: NativeRequestId(0),
            source,
        } if *source == original_root.source_module
    )));
}

#[test]
fn native_bundle_rejects_obligation_from_unrelated_lineage_root() {
    let mut bundle = native_bundle();
    let source_digest = bundle.lineage.nodes[0].source_module;
    bundle.lineage.nodes[0]
        .obligations
        .retain(|obligation| *obligation != ProofId::new(1));

    let mut unrelated_root = ProofLineageNode::new(
        ProofLineageId::new(1),
        ProofTransform::new(
            ProofTransformStage::Frontend,
            "stale-mir-to-trust_ir",
            "tRust",
            "native-request-schema-v1",
        ),
        digest(0xB2),
        bundle.trust_ir_module_digest,
    );
    unrelated_root.obligations.push(ProofId::new(1));
    bundle.lineage.nodes.push(unrelated_root);
    bundle.lineage.roots.push(ProofLineageId::new(1));

    let trust_mc_request = bundle.requests[1].clone();
    bundle.requests = vec![trust_mc_request];
    if let NativeVerificationRequest::TrustMc(request) = &mut bundle.requests[0] {
        request.lineage_roots = vec![ProofLineageId::new(0), ProofLineageId::new(1)];
    }

    let errors = bundle
        .validate()
        .expect_err("obligation from unrelated lineage root rejected");
    assert!(!errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::RequestSourceDigestNotInLineage {
            request: NativeRequestId(1),
            source,
        } if *source == source_digest
    )));
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::RequestObligationNotInLineage {
            request: NativeRequestId(1),
            obligation: ProofId(1)
        }
    )));
}

#[test]
fn native_bundle_rejects_duplicate_trust_vc_certificate_attachments() {
    let mut bundle = native_bundle();
    if let NativeVerificationRequest::TrustVc(request) = &mut bundle.requests[0] {
        request.certificates.push(request.certificates[0].clone());
    }

    let errors = bundle
        .validate()
        .expect_err("duplicate certificate attachment rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::DuplicateRequestCertificate {
            request: NativeRequestId(0),
            obligation: ProofId(0),
            prover
        } if prover == "trust_vc"
    )));
}

#[test]
fn native_bundle_rejects_cross_suite_trust_vc_certificate_attachment() {
    let mut bundle = native_bundle();
    bundle.module.proof_certificates[0].prover = "trust_mc".to_string();
    let trust_mc_ref = bundle.module.proof_certificates[0].lineage_ref();
    bundle.lineage.nodes[0].certificates[0] = trust_mc_ref.clone();
    if let NativeVerificationRequest::TrustVc(request) = &mut bundle.requests[0] {
        request.certificates[0] = trust_mc_ref;
    }

    let errors = bundle
        .validate()
        .expect_err("cross-suite certificate attachment rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::CertificateVerifierSuiteMismatch {
            request: NativeRequestId(0),
            expected: NativeVerifierSuite::TrustVc,
            obligation: ProofId(0),
            prover,
            canonical,
        } if prover == "trust_mc" && canonical == "trust_mc"
    )));
}

#[test]
fn native_bundle_rejects_uncanonical_trust_vc_certificate_attachment_identity() {
    let mut bundle = native_bundle();
    bundle.module.proof_certificates[0].prover = " -- ".to_string();
    let blank_ref = bundle.module.proof_certificates[0].lineage_ref();
    bundle.lineage.nodes[0].certificates[0] = blank_ref.clone();
    if let NativeVerificationRequest::TrustVc(request) = &mut bundle.requests[0] {
        request.certificates[0] = blank_ref;
    }

    let errors = bundle
        .validate()
        .expect_err("uncanonical certificate attachment identity rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::CertificateVerifierSuiteMismatch {
            request: NativeRequestId(0),
            expected: NativeVerifierSuite::TrustVc,
            obligation: ProofId(0),
            prover,
            canonical,
        } if prover == " -- " && canonical.is_empty()
    )));
}

#[test]
fn native_bundle_rejects_invalid_verifier_options() {
    let mut bundle = native_bundle();
    if let NativeVerificationRequest::TrustMc(request) = &mut bundle.requests[1] {
        request.mode = TrustMcVerificationMode::Pdr;
        request.options.chc.pdr.enabled = false;
    }
    if let NativeVerificationRequest::TrustWp(request) = &mut bundle.requests[2] {
        request.mode = TrustWpVerificationMode::Abduction;
        request.options.max_abduced_preconditions = 0;
    }

    let errors = bundle
        .validate()
        .expect_err("invalid verifier options rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::InvalidTrustMcChcOptions {
            request: NativeRequestId(1),
            field: "chc.pdr.enabled"
        }
    )));
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::InvalidTrustWpOptions {
            request: NativeRequestId(2),
            field: "max_abduced_preconditions"
        }
    )));
}

#[test]
fn native_bundle_rejects_mismatched_verifier_suite() {
    let mut bundle = native_bundle();
    if let NativeVerificationRequest::TrustMc(request) = &mut bundle.requests[1] {
        request.provenance.verifier_suite = NativeVerifierSuite::TrustVc;
    }

    let errors = bundle
        .validate()
        .expect_err("mismatched verifier suite rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::VerifierSuiteMismatch {
            request: NativeRequestId(1),
            expected: NativeVerifierSuite::TrustMc,
            actual: NativeVerifierSuite::TrustVc,
        }
    )));
}

#[test]
fn native_bundle_rejects_cross_suite_expected_verifier_identity() {
    let mut bundle = native_bundle();
    if let NativeVerificationRequest::TrustMc(request) = &mut bundle.requests[1] {
        request.provenance.expected_verifier.name = "trust_vc".to_string();
    }

    let errors = bundle
        .validate()
        .expect_err("cross-suite verifier identity rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::ExpectedVerifierIdentityMismatch {
            request: NativeRequestId(1),
            suite: NativeVerifierSuite::TrustMc,
            verifier,
            canonical,
        } if verifier == "trust_vc" && canonical == "trust_vc"
    )));
}

#[test]
fn native_bundle_accepts_canonical_expected_verifier_variants() {
    let mut bundle = native_bundle();
    if let NativeVerificationRequest::TrustMc(request) = &mut bundle.requests[1] {
        request.provenance.expected_verifier.name = "  TrustMc.Native_PDR  ".to_string();
    }

    remove_unreplayed_trust_vc_fixture(&mut bundle);
    bundle
        .validate()
        .expect("canonical TrustMc verifier variant accepted");
}

#[test]
fn native_bundle_rejects_missing_solver_identity() {
    let mut bundle = native_bundle();
    if let NativeVerificationRequest::TrustWp(request) = &mut bundle.requests[2] {
        request.provenance.solvers.clear();
    }

    let errors = bundle
        .validate()
        .expect_err("missing solver identity rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::EmptyProvenanceField("request.provenance.solvers")
    )));
}

#[test]
fn native_bundle_rejects_malformed_request_provenance() {
    let mut bundle = native_bundle();
    if let NativeVerificationRequest::TrustMc(request) = &mut bundle.requests[1] {
        request.provenance.expected_verifier.name = "  ".to_string();
        request.provenance.solvers[0].version = Some("".to_string());
        request.provenance.replay = Some(
            ProofReplayIdentity::new("", "   ")
                .with_transcript_digest(ProofDigest::sha256([0; 32])),
        );
    }

    let errors = bundle
        .validate()
        .expect_err("malformed request provenance rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::EmptyProvenanceField("request.provenance.expected_verifier")
    )));
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::InvalidToolIdentityField {
            field: "request.provenance.solvers",
            component: "version"
        }
    )));
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::InvalidReplayIdentity {
            request: NativeRequestId(1),
            field: "engine"
        }
    )));
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::InvalidReplayIdentity {
            request: NativeRequestId(1),
            field: "invocation"
        }
    )));
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::InvalidReplayIdentity {
            request: NativeRequestId(1),
            field: "transcript_digest"
        }
    )));
}

#[test]
fn native_bundle_rejects_cross_suite_replay_engine() {
    let mut bundle = native_bundle();
    if let NativeVerificationRequest::TrustMc(request) = &mut bundle.requests[1] {
        request.provenance.replay.as_mut().expect("replay").engine = "trust_vc-import".to_string();
    }

    let errors = bundle
        .validate()
        .expect_err("cross-suite replay engine rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::ReplayIdentityVerifierSuiteMismatch {
            request: NativeRequestId(1),
            expected: NativeVerifierSuite::TrustMc,
            engine,
            canonical,
        } if engine == "trust_vc-import" && canonical == "trust_vc-import"
    )));
}

#[test]
fn native_bundle_rejects_missing_replay_transcript_digest() {
    let mut bundle = native_bundle();
    if let NativeVerificationRequest::TrustMc(request) = &mut bundle.requests[1] {
        request
            .provenance
            .replay
            .as_mut()
            .expect("replay")
            .transcript_digest = None;
    }

    let errors = bundle
        .validate()
        .expect_err("missing replay transcript digest rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::MissingReplayTranscriptDigest(NativeRequestId(1))
    )));
}

#[test]
fn native_bundle_rejects_stale_evidence_request_digest() {
    let mut bundle = native_bundle();
    bundle.evidence_bundles = native_evidence_bundles(&bundle);
    if let NativeEvidenceBundle::TrustMc(evidence) = &mut bundle.evidence_bundles[1] {
        evidence.request_digest = digest(0xEE);
    }

    let errors = bundle
        .validate()
        .expect_err("stale evidence request digest rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::EvidenceRequestDigestMismatch {
            request: NativeRequestId(1),
            expected: _,
            actual,
        } if *actual == digest(0xEE)
    )));
}

#[test]
fn native_bundle_rejects_cross_request_evidence_obligation() {
    let mut bundle = native_bundle();
    bundle.evidence_bundles = native_evidence_bundles(&bundle);
    if let NativeEvidenceBundle::TrustMc(evidence) = &mut bundle.evidence_bundles[1] {
        evidence.obligations = vec![ProofId::new(0)];
    }

    let errors = bundle
        .validate()
        .expect_err("cross-request evidence obligation rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::EvidenceObligationMismatch {
            request: NativeRequestId(1),
            obligation: ProofId(1),
        }
    )));
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::EvidenceObligationMismatch {
            request: NativeRequestId(1),
            obligation: ProofId(0),
        }
    )));
}

#[test]
fn native_bundle_rejects_cross_suite_evidence_artifact_kind() {
    let mut bundle = native_bundle();
    bundle.evidence_bundles = native_evidence_bundles(&bundle);
    if let NativeEvidenceBundle::TrustMc(evidence) = &mut bundle.evidence_bundles[1] {
        evidence.artifacts[0].kind = NativeEvidenceArtifactKind::TrustWpVerificationCondition;
    }

    let errors = bundle
        .validate()
        .expect_err("cross-suite evidence artifact rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::EvidenceArtifactSuiteMismatch {
            request: NativeRequestId(1),
            suite: NativeVerifierSuite::TrustMc,
            kind: NativeEvidenceArtifactKind::TrustWpVerificationCondition,
        }
    )));
}

#[test]
fn native_bundle_accepts_trust_wp_sp_replay_context() {
    let mut bundle = native_bundle();
    if let NativeVerificationRequest::TrustWp(request) = &mut bundle.requests[2] {
        request.mode = TrustWpVerificationMode::StrongestPostcondition;
        request.provenance.replay_context = NativeReplayContext::default()
            .with_atom(
                NativeReplayAtom::assumption(
                    NativeReplayAtomId::new(0),
                    ProofFormula::smtlib2("(i32 lhs)", "Bool"),
                )
                .with_obligation(ProofId::new(1))
                .with_span(SourceSpan {
                    file: 0,
                    line: 13,
                    col: 9,
                }),
            )
            .with_atom(
                NativeReplayAtom::assertion(
                    NativeReplayAtomId::new(1),
                    ProofFormula::smtlib2("trust_ir_checked_add_equiv", "Bool"),
                )
                .with_obligation(ProofId::new(1))
                .with_assertion_id(NativeAssertionId::new(7))
                .with_span(SourceSpan {
                    file: 0,
                    line: 13,
                    col: 9,
                }),
            );
    }

    remove_unreplayed_trust_vc_fixture(&mut bundle);
    bundle
        .validate()
        .expect("TrustWp SP replay context accepted");
}

#[test]
fn native_bundle_rejects_trust_wp_sp_without_replay_context() {
    let mut bundle = native_bundle();
    if let NativeVerificationRequest::TrustWp(request) = &mut bundle.requests[2] {
        request.mode = TrustWpVerificationMode::StrongestPostcondition;
        request.provenance.replay_context.atoms.clear();
    }

    let errors = bundle
        .validate()
        .expect_err("TrustWp SP without replay atoms rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::MissingTrustWpStrongestPostconditionContext(
            NativeRequestId(2)
        )
    )));
}

#[test]
fn native_bundle_rejects_diagnostic_source_and_lineage_suppression() {
    let mut bundle = native_bundle();
    bundle.diagnostics.include_source_spans = false;
    if let NativeVerificationRequest::TrustMc(request) = &mut bundle.requests[1] {
        request.diagnostics.include_source_spans = false;
        request.diagnostics.include_lineage = false;
    }
    let missing_source = *bundle.requests[1].obligations().first().unwrap();
    bundle
        .compiler_facts
        .obligation_sources
        .retain(|source| source.obligation != missing_source);

    let errors = bundle
        .validate()
        .expect_err("diagnostic suppression rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::InvalidBundleDiagnosticsPolicy {
            field: "include_source_spans"
        }
    )));
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::InvalidDiagnosticsPolicy {
            request: NativeRequestId(1),
            field: "include_source_spans"
        }
    )));
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::InvalidDiagnosticsPolicy {
            request: NativeRequestId(1),
            field: "include_lineage"
        }
    )));
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::MissingObligationSource {
            request: NativeRequestId(1),
            obligation,
        } if *obligation == missing_source
    )));
}

#[test]
fn native_bundle_rejects_requested_obligation_without_source_span() {
    let mut bundle = native_bundle();
    bundle.compiler_facts.obligation_sources[1].span = None;

    let errors = bundle
        .validate()
        .expect_err("requested obligation without source span rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::MissingObligationSourceSpan {
            request: NativeRequestId(1),
            obligation: ProofId(1),
        }
    )));
}

#[test]
fn native_bundle_rejects_requested_obligation_without_assertion_id() {
    let mut bundle = native_bundle();
    bundle.compiler_facts.obligation_sources[1].assertion_id = None;

    let errors = bundle
        .validate()
        .expect_err("requested obligation without assertion id rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::MissingObligationSourceAssertion {
            request: NativeRequestId(1),
            obligation: ProofId(1),
        }
    )));
}

#[test]
fn native_bundle_requires_embedded_source_and_atomic_public_identity() {
    let mut missing_source = native_bundle();
    missing_source.module.proof_obligations[1].source = None;
    refresh_native_bundle_module_identity(&mut missing_source);
    let errors = missing_source
        .validate()
        .expect_err("requested obligation without embedded source rejected");
    assert!(errors.iter().any(|error| matches!(
        error,
        NativeVerificationBundleError::MissingEmbeddedObligationSource {
            request: NativeRequestId(1),
            obligation: ProofId(1),
        }
    )));

    let mut missing_public = native_bundle();
    missing_public.module.proof_obligations[1]
        .source
        .as_mut()
        .unwrap()
        .public = None;
    refresh_native_bundle_module_identity(&mut missing_public);
    let errors = missing_public
        .validate()
        .expect_err("requested obligation without embedded public identity rejected");
    assert!(errors.iter().any(|error| matches!(
        error,
        NativeVerificationBundleError::MissingEmbeddedPublicObligationIdentity {
            request: NativeRequestId(1),
            obligation: ProofId(1),
        }
    )));
}

#[test]
fn native_bundle_reconciles_embedded_public_id_and_exact_range_start() {
    let mut public_mismatch = native_bundle();
    public_mismatch.module.proof_obligations[1]
        .source
        .as_mut()
        .unwrap()
        .public
        .as_mut()
        .unwrap()
        .obligation_id = "vc:checked_add:assert:different".to_string();
    refresh_native_bundle_module_identity(&mut public_mismatch);
    let errors = public_mismatch
        .validate()
        .expect_err("embedded and compiler public ids must agree");
    assert!(errors.iter().any(|error| matches!(
        error,
        NativeVerificationBundleError::EmbeddedPublicObligationIdMismatch {
            request: NativeRequestId(1),
            obligation: ProofId(1),
            ..
        }
    )));

    let mut span_mismatch = native_bundle();
    span_mismatch.module.proof_obligations[1]
        .source
        .as_mut()
        .unwrap()
        .range
        .as_mut()
        .unwrap()
        .start_col += 1;
    refresh_native_bundle_module_identity(&mut span_mismatch);
    let errors = span_mismatch
        .validate()
        .expect_err("embedded and compiler source starts must agree");
    assert!(errors.iter().any(|error| matches!(
        error,
        NativeVerificationBundleError::EmbeddedObligationSourceSpanMismatch {
            request: NativeRequestId(1),
            obligation: ProofId(1),
            ..
        }
    )));
}

#[test]
fn native_bundle_rejects_invalid_embedded_source_identity() {
    let mut bundle = native_bundle();
    let source = bundle.module.proof_obligations[1].source.as_mut().unwrap();
    source.assertion_id = " assertion".to_string();
    source.public.as_mut().unwrap().semantic_digest = ProofDigest::zero();
    refresh_native_bundle_module_identity(&mut bundle);

    let errors = bundle
        .validate()
        .expect_err("invalid embedded source identity rejected");
    for field in ["assertion_id", "public.semantic_digest"] {
        assert!(
            errors.iter().any(|error| matches!(
                error,
                NativeVerificationBundleError::InvalidEmbeddedObligationSource {
                    request: NativeRequestId(1),
                    obligation: ProofId(1),
                    field: actual,
                } if *actual == field
            )),
            "missing {field} rejection: {errors:?}"
        );
    }
}

#[test]
fn native_bundle_rejects_noncanonical_serialization_policy() {
    let mut bundle = native_bundle();
    bundle.serialization.canonical_order = false;
    bundle.provenance.source_digest = Some(digest(0xEE));

    let errors = bundle
        .validate()
        .expect_err("noncanonical serialization rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::NonCanonicalSerialization("serialization.canonical_order")
    )));
    assert!(errors.iter().any(|err| matches!(
        err,
        NativeVerificationBundleError::InputDigestMismatch {
            field: "provenance.source_digest",
            expected: _,
            actual: _
        }
    )));
}

#[test]
fn native_compiler_facts_and_bundle_digests_cover_public_obligation_id() {
    let bundle = native_bundle();
    let mut changed = bundle.clone();
    changed.compiler_facts.obligation_sources[1].public_obligation_id =
        "vc:checked_add:assert:renamed".to_string();

    assert_ne!(
        bundle.compiler_facts.stable_digest(),
        changed.compiler_facts.stable_digest()
    );
    assert_ne!(bundle.stable_digest(), changed.stable_digest());
}

#[test]
fn native_semantic_bridge_digest_binds_every_embedded_source_identity_field() {
    let mut obligation = ProofObligation::new(
        ProofId::new(7),
        ObligationKind::Precondition,
        ProofStatus::Pending,
        "x is nonnegative",
    );
    obligation.source = Some(
        ProofObligationSourceIdentity::new("rust:crate::f", "assertion α")
            .with_range(ProofObligationSourceRange {
                file: 2,
                start_line: 11,
                start_col: 3,
                end_line: 12,
                end_col: 9,
            })
            .with_public(PublicObligationIdentity {
                obligation_id: "vc:crate::f:0".to_string(),
                semantic_digest: ProofDigest::sha256([7; 32]),
            }),
    );
    let digest = native_semantic_bridge_proof_digest(&obligation);
    let mutations: &[fn(&mut ProofObligationSourceIdentity)] = &[
        |source| source.source_id.push('!'),
        |source| source.assertion_id.push('!'),
        |source| source.range.as_mut().unwrap().file += 1,
        |source| source.range.as_mut().unwrap().start_line += 1,
        |source| source.range.as_mut().unwrap().start_col += 1,
        |source| source.range.as_mut().unwrap().end_line += 1,
        |source| source.range.as_mut().unwrap().end_col += 1,
        |source| source.public.as_mut().unwrap().obligation_id.push('!'),
        |source| source.public.as_mut().unwrap().semantic_digest.bytes[0] ^= 1,
    ];
    for mutate in mutations {
        let mut changed = obligation.clone();
        mutate(changed.source.as_mut().unwrap());
        assert_ne!(native_semantic_bridge_proof_digest(&changed), digest);
    }
}

#[test]
fn native_bundle_stable_digest_sorts_unordered_request_fields() {
    let bundle = native_bundle();
    let mut reordered = bundle.clone();
    reordered.requests.reverse();
    if let NativeVerificationRequest::TrustWp(request) = &mut reordered.requests[0] {
        request.obligations.reverse();
        request.lineage_roots.reverse();
    }
    reordered.provenance.toolchain.reverse();

    assert_eq!(bundle.stable_digest(), reordered.stable_digest());

    if let NativeVerificationRequest::TrustMc(request) = &mut reordered.requests[1] {
        request.options.chc.emit_horn_clauses = false;
    }
    assert_ne!(bundle.stable_digest(), reordered.stable_digest());
}

#[test]
fn native_bundle_exposes_assertion_obligation_helpers() {
    let bundle = native_bundle();

    assert_eq!(
        bundle.obligations_for_assertion(NativeAssertionId::new(7)),
        vec![ProofId::new(1)]
    );
    assert_eq!(
        bundle
            .obligation_source(ProofId::new(1))
            .and_then(|source| source.assertion_id),
        Some(NativeAssertionId::new(7))
    );
    assert!(
        bundle
            .obligations_for_assertion(NativeAssertionId::new(99))
            .is_empty()
    );
}

#[test]
fn native_bundle_stable_digest_covers_assertion_ids() {
    let bundle = native_bundle();
    let mut changed = bundle.clone();
    changed.compiler_facts.obligation_sources[1].assertion_id = Some(NativeAssertionId::new(8));

    assert_ne!(bundle.stable_digest(), changed.stable_digest());
}

#[test]
fn native_compiler_facts_digest_covers_vector_lane_count_and_element_type() {
    let facts_for_ty = |ty: Ty| NativeCompilerFacts {
        monomorphizations: vec![NativeMonomorphizationFact {
            id: NativeMonomorphizationId::new(0),
            source_item: "batch_bool_int".to_string(),
            symbol: "_RNvCs_batch_bool_int".to_string(),
            generic_args: vec![NativeGenericArg::Ty(ty)],
            function: Some(FuncId::new(0)),
            stable_digest: digest(0x77),
        }],
        ..NativeCompilerFacts::default()
    };

    let v4i32 = facts_for_ty(Ty::Vector(Box::new(Ty::I32), 4));
    let v8i32 = facts_for_ty(Ty::Vector(Box::new(Ty::I32), 8));
    let v4u32 = facts_for_ty(Ty::Vector(Box::new(Ty::U32), 4));

    assert_ne!(v4i32.stable_digest(), v8i32.stable_digest());
    assert_ne!(v4i32.stable_digest(), v4u32.stable_digest());
}

#[test]
fn native_bundle_stable_digest_covers_verifier_identity() {
    let bundle = native_bundle();
    let mut changed = bundle.clone();
    if let NativeVerificationRequest::TrustMc(request) = &mut changed.requests[1] {
        request.provenance.verifier_suite = NativeVerifierSuite::Other;
        request
            .provenance
            .solvers
            .push(NativeToolIdentity::new("cvc5").with_version("1.1.2"));
    }

    assert_ne!(bundle.stable_digest(), changed.stable_digest());
}

#[test]
fn native_bundle_stable_digest_covers_replay_context_atoms() {
    let bundle = native_bundle();
    let mut changed = bundle.clone();
    if let NativeVerificationRequest::TrustWp(request) = &mut changed.requests[2] {
        request.provenance.replay_context = NativeReplayContext::default().with_atom(
            NativeReplayAtom::assumption(
                NativeReplayAtomId::new(0),
                ProofFormula::smtlib2("(i32 lhs)", "Bool"),
            )
            .with_obligation(ProofId::new(1)),
        );
    }

    assert_ne!(bundle.stable_digest(), changed.stable_digest());
}

#[test]
fn native_bundle_stable_digest_covers_result_evidence_artifacts() {
    let mut bundle = native_bundle();
    bundle.evidence_bundles = native_evidence_bundles(&bundle);
    let mut changed = bundle.clone();
    if let NativeEvidenceBundle::TrustMc(evidence) = &mut changed.evidence_bundles[1] {
        evidence.artifacts[0].digest = digest(0xDD);
    }

    assert_ne!(bundle.stable_digest(), changed.stable_digest());
}

#[test]
fn native_bundle_stable_digest_normalizes_verifier_identity_spelling() {
    let bundle = native_bundle();
    let mut changed = bundle.clone();
    if let NativeVerificationRequest::TrustMc(request) = &mut changed.requests[1] {
        request.provenance.expected_verifier.name = " TRUST_MC ".to_string();
    }

    assert_eq!(bundle.stable_digest(), changed.stable_digest());
}

/// #136: the Trust frontend must serialize to one consistent wire token across
/// both enums that name it. `NativeBundleProducer::TRust` and
/// `NativeVerifierSuite::TRust` previously disagreed (`"Trust"` vs `"tRust"`),
/// which would make a producer and its verifier suite spell the same frontend
/// two different ways in a single JSON/MessagePack handoff. This pins them
/// equal and pins the post-rename canonical spelling `"Trust"`.
#[cfg(feature = "serde")]
#[test]
fn trust_frontend_wire_spelling_is_consistent_across_producer_and_verifier_suite() {
    let producer_json =
        serde_json::to_string(&NativeBundleProducer::TRust).expect("producer should serialize");
    let suite_json =
        serde_json::to_string(&NativeVerifierSuite::TRust).expect("suite should serialize");

    assert_eq!(producer_json, "\"Trust\"");
    assert_eq!(suite_json, "\"Trust\"");
    assert_eq!(
        producer_json, suite_json,
        "the Trust frontend must use one wire spelling across both enums"
    );

    // Round-trip both directions through JSON and MessagePack.
    let producer_back: NativeBundleProducer =
        serde_json::from_str(&producer_json).expect("producer JSON should round-trip");
    assert_eq!(producer_back, NativeBundleProducer::TRust);
    let suite_back: NativeVerifierSuite =
        serde_json::from_str(&suite_json).expect("suite JSON should round-trip");
    assert_eq!(suite_back, NativeVerifierSuite::TRust);

    let suite_mp = rmp_serde::to_vec(&NativeVerifierSuite::TRust)
        .expect("suite should serialize to MessagePack");
    let suite_mp_back: NativeVerifierSuite =
        rmp_serde::from_slice(&suite_mp).expect("suite MessagePack should round-trip");
    assert_eq!(suite_mp_back, NativeVerifierSuite::TRust);

    // The Display spelling matches the wire branding too.
    assert_eq!(NativeVerifierSuite::TRust.to_string(), "Trust");
}

/// #98: the `*_PROVIDED_FIELDS` / `*_EXTERNAL_FIELDS` manifests are PRODUCTION
/// contract data (the production descriptors below embed them, and ty/ay/TrustCg
/// consume those descriptors to learn this crate's identity surface). They are
/// intentionally retained, not deleted. This guard converts the audit's
/// "self-referential, no drift protection" concern into an actual drift gate:
///
/// 1. Each production descriptor embeds *exactly* the manifest constant
///    (same backing slice — a future edit that forks the array fails here).
/// 2. No manifest has duplicate entries (the classic copy-paste drift in a
///    700+-entry hand-maintained list).
/// 3. The owned/external split holds: every `EXTERNAL_FIELDS` entry is
///    `trust_cg.`-namespaced (externally owned) and no `PROVIDED_FIELDS` entry
///    is (this crate owns them) — a field leaking across that boundary is the
///    contract-meaningful drift.
/// 4. Every entry is well-formed (non-empty, no surrounding whitespace).
#[test]
fn manifest_field_sets_have_no_drift() {
    fn assert_no_duplicates(name: &str, fields: &[&str]) {
        let mut seen = std::collections::BTreeSet::new();
        for field in fields {
            assert!(
                seen.insert(*field),
                "{name} has a duplicate entry: {field:?} (copy-paste drift)"
            );
            assert!(!field.is_empty(), "{name} has an empty entry");
            assert_eq!(
                *field,
                field.trim(),
                "{name} entry has surrounding whitespace: {field:?}"
            );
        }
    }

    // (1) Production descriptors embed exactly these canonical field sets.
    // Rust may merge or duplicate immutable allocations, so pointer identity is
    // not a stable semantic contract; compare the complete ordered contents.
    assert_eq!(
        NATIVE_BUNDLE_IDENTITY_CONTRACT_DESCRIPTOR.provided_fields,
        NATIVE_BUNDLE_IDENTITY_CONTRACT_PROVIDED_FIELDS,
    );
    assert_eq!(
        NATIVE_BUNDLE_IDENTITY_CONTRACT_DESCRIPTOR.external_fields,
        NATIVE_BUNDLE_IDENTITY_CONTRACT_EXTERNAL_FIELDS,
    );
    assert_eq!(
        PETRI_NATIVE_VERIFICATION_BUNDLE_HANDOFF_DESCRIPTOR.expected_bundle_identity_fields,
        NATIVE_BUNDLE_IDENTITY_CONTRACT_PROVIDED_FIELDS,
    );
    assert_eq!(
        PETRI_SUCCESSOR_TRUST_MC_CHC_CONTRACT_DESCRIPTOR.provided_fields,
        PETRI_SUCCESSOR_TRUST_MC_CHC_CONTRACT_PROVIDED_FIELDS,
    );

    // (2) No duplicates / malformed entries.
    assert_no_duplicates(
        "NATIVE_BUNDLE_IDENTITY_CONTRACT_PROVIDED_FIELDS",
        NATIVE_BUNDLE_IDENTITY_CONTRACT_PROVIDED_FIELDS,
    );
    assert_no_duplicates(
        "NATIVE_BUNDLE_IDENTITY_CONTRACT_EXTERNAL_FIELDS",
        NATIVE_BUNDLE_IDENTITY_CONTRACT_EXTERNAL_FIELDS,
    );
    assert_no_duplicates(
        "PETRI_SUCCESSOR_TRUST_MC_CHC_CONTRACT_PROVIDED_FIELDS",
        PETRI_SUCCESSOR_TRUST_MC_CHC_CONTRACT_PROVIDED_FIELDS,
    );

    // (3) Owned/external namespace split.
    for field in NATIVE_BUNDLE_IDENTITY_CONTRACT_EXTERNAL_FIELDS {
        assert!(
            field.starts_with("trust_cg."),
            "EXTERNAL_FIELDS entry {field:?} must be externally namespaced (trust_cg.)"
        );
    }
    for field in NATIVE_BUNDLE_IDENTITY_CONTRACT_PROVIDED_FIELDS {
        assert!(
            !field.starts_with("trust_cg."),
            "PROVIDED_FIELDS entry {field:?} is externally owned and belongs in EXTERNAL_FIELDS"
        );
    }
    for field in PETRI_SUCCESSOR_TRUST_MC_CHC_CONTRACT_PROVIDED_FIELDS {
        assert!(
            !field.starts_with("trust_cg."),
            "PETRI PROVIDED_FIELDS entry {field:?} is externally owned"
        );
    }

    // (4) The owned and external sets are disjoint (no field is claimed by both
    // halves of the contract).
    let owned: std::collections::BTreeSet<&str> = NATIVE_BUNDLE_IDENTITY_CONTRACT_PROVIDED_FIELDS
        .iter()
        .copied()
        .collect();
    for field in NATIVE_BUNDLE_IDENTITY_CONTRACT_EXTERNAL_FIELDS {
        assert!(
            !owned.contains(field),
            "field {field:?} appears in both PROVIDED_FIELDS and EXTERNAL_FIELDS"
        );
    }
}

/// Both halves of the `TrustVcNativeRequest::function` stable-writer contract.
///
/// (a) NEUTRALITY. The hex constant was captured from the tree BEFORE the
///     writer arm in `write_native_request_stable` learned about `function`.
///     It is the pin proving a `None` function is wire-invisible, so no
///     pre-existing TrustVc request digest, evidence `request_digest`, or
///     compiler artifact metadata value moved. Pin the REQUEST digest directly:
///     the enclosing bundle also covers the TrustIR module digest, which moves
///     legitimately when the module binary schema gains a semantic field.
///
/// (b) COVERAGE. The stable writers enumerate fields BY HAND with no
///     exhaustive `let Self { .. }` destructuring, so simply forgetting the
///     writer arm compiles clean and silently weakens request identity. Half
///     (b) is what makes that omission fail loudly.
#[test]
fn native_bundle_stable_digest_covers_trust_vc_function() {
    // Captured from the tree BEFORE the writer arm learned about `function`.
    const PRE_CHANGE_TRUST_VC_REQUEST_DIGEST: &str =
        "sha256:76b7df9c9fe2e4a4e8729acb3eacbdad66930c5bfa1ec2d86f5cd9da564c50b7";

    let bundle = native_bundle();
    let baseline_request = bundle.requests[0].stable_digest();
    let baseline_bundle = bundle.stable_digest();

    // (a) captured pre-change — see PRE_CHANGE_TRUST_VC_REQUEST_DIGEST above.
    assert_eq!(
        baseline_request.to_string(),
        PRE_CHANGE_TRUST_VC_REQUEST_DIGEST,
        "a None `function` must be wire-invisible; this digest moving means the \
         field was tagged rather than written as a trailing conditional"
    );

    // (b) the field must actually reach the writer.
    let mut changed = bundle.clone();
    match &mut changed.requests[0] {
        NativeVerificationRequest::TrustVc(request) => {
            assert_eq!(request.function, None, "fixture precondition");
            request.function = Some(FuncId::new(0));
        }
        other => panic!("expected requests[0] to be TrustVc, got {other:?}"),
    }
    assert_ne!(
        baseline_request,
        changed.requests[0].stable_digest(),
        "`function` is not covered by the stable request digest"
    );
    assert_ne!(
        baseline_bundle,
        changed.stable_digest(),
        "the request identity change is not covered by the bundle digest"
    );
}
