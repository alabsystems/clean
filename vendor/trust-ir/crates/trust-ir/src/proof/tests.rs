// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for the `proof` module, kept alongside the code they exercise.

use crate::inst::Ordering;
use crate::proof::*;
use crate::value::{ProofId, ProofTag};
// `FuncId` is referenced only by the serde-gated legacy-bundle test below.
#[cfg(feature = "serde")]
use crate::value::FuncId;

#[test]
fn proof_annotation_memory_safety_variants() {
    let variants = [
        ProofAnnotation::InBounds,
        ProofAnnotation::NotNull,
        ProofAnnotation::ValidBorrow,
        ProofAnnotation::UniqueBorrow,
        ProofAnnotation::SharedBorrow,
        ProofAnnotation::ValidDealloc,
    ];
    for (i, a) in variants.iter().enumerate() {
        for (j, b) in variants.iter().enumerate() {
            if i == j {
                assert_eq!(a, b);
            } else {
                assert_ne!(a, b);
            }
        }
    }
}

#[test]
fn proof_annotation_arithmetic_safety_variants() {
    let variants = [
        ProofAnnotation::NoOverflow,
        ProofAnnotation::NoWrap,
        ProofAnnotation::DivNonZero,
        ProofAnnotation::ShiftInRange,
        ProofAnnotation::Wrapping,
    ];
    assert_eq!(variants.len(), 5);
    assert_ne!(variants[0], variants[1]);
    // Wrapping (modular-arithmetic marker) is distinct from NoOverflow.
    assert_ne!(ProofAnnotation::Wrapping, ProofAnnotation::NoOverflow);
}

#[test]
fn proof_annotation_functional_correctness_variants() {
    let variants = [
        ProofAnnotation::Pure,
        ProofAnnotation::Terminates,
        ProofAnnotation::Deterministic,
        ProofAnnotation::Associative,
        ProofAnnotation::Commutative,
    ];
    assert_eq!(variants.len(), 5);
}

#[test]
fn proof_annotation_concurrency() {
    let drf = ProofAnnotation::DataRaceFree;
    let ao = ProofAnnotation::AtomicOrdering(Ordering::SeqCst);
    assert_ne!(drf, ao);
}

#[test]
fn proof_annotation_bounded_output() {
    let bo = ProofAnnotation::BoundedOutput { lo: -1.0, hi: 1.0 };
    if let ProofAnnotation::BoundedOutput { lo, hi } = &bo {
        assert_eq!(*lo, -1.0);
        assert_eq!(*hi, 1.0);
    } else {
        panic!("expected BoundedOutput");
    }
}

#[test]
fn proof_annotation_monotonic() {
    let m = ProofAnnotation::Monotonic;
    assert_eq!(format!("{:?}", m), "Monotonic");
}

#[test]
fn proof_annotation_custom() {
    let c = ProofAnnotation::Custom(ProofTag::new(42));
    if let ProofAnnotation::Custom(tag) = &c {
        assert_eq!(tag.index(), 42);
    } else {
        panic!("expected Custom");
    }
}

#[test]
fn obligation_kind_all_variants() {
    let kinds = [
        ObligationKind::Precondition,
        ObligationKind::Postcondition,
        ObligationKind::LoopInvariant,
        ObligationKind::TypeInvariant,
        ObligationKind::RefinementType,
        ObligationKind::TranslationValidation,
        ObligationKind::MemorySafety,
        ObligationKind::PanicFreedom,
        ObligationKind::TemporalSafety,
        ObligationKind::Liveness,
        ObligationKind::ArithmeticSafety,
        ObligationKind::BoundsCheck,
        ObligationKind::GiveBackRefinement,
    ];
    assert_eq!(kinds.len(), 13);
}

#[test]
fn proof_status_all_variants() {
    let statuses = [
        ProofStatus::Pending,
        ProofStatus::Discharged,
        ProofStatus::Failed,
        ProofStatus::Trusted,
        ProofStatus::Certified,
    ];
    assert_eq!(statuses.len(), 5);
    assert_ne!(statuses[0], statuses[1]);
    // Certified is distinct from every other status (the de Bruijn tier).
    assert_ne!(ProofStatus::Certified, ProofStatus::Trusted);
}

#[test]
fn proof_obligation_construction() {
    let po = ProofObligation {
        id: ProofId::new(0),
        kind: ObligationKind::MemorySafety,
        status: ProofStatus::Pending,
        description: "array access in bounds".to_string(),
        formula: None,
        function: None,
        source: None,
        site: None,
    };
    assert_eq!(po.id.index(), 0);
    assert_eq!(po.kind, ObligationKind::MemorySafety);
    assert_eq!(po.status, ProofStatus::Pending);
    assert_eq!(po.description, "array access in bounds");
}

#[test]
fn proof_obligation_different_statuses() {
    let pending = ProofObligation {
        id: ProofId::new(0),
        kind: ObligationKind::Precondition,
        status: ProofStatus::Pending,
        description: "pre".to_string(),
        formula: None,
        function: None,
        source: None,
        site: None,
    };
    let discharged = ProofObligation {
        id: ProofId::new(0),
        kind: ObligationKind::Precondition,
        status: ProofStatus::Discharged,
        description: "pre".to_string(),
        formula: None,
        function: None,
        source: None,
        site: None,
    };
    assert_ne!(pending, discharged);
}

#[test]
fn proof_obligation_formula_preserves_machine_payload() {
    let formula =
        ProofFormula::trust_types_json(r#"{"Var":["x",{"BitVec":64}]}"#, "x", "(_ BitVec 64)");
    let po = ProofObligation::new(
        ProofId::new(7),
        ObligationKind::Precondition,
        ProofStatus::Pending,
        "x must be available",
    )
    .with_formula(formula.clone());

    assert!(po.has_formula());
    assert_eq!(po.formula.as_ref(), Some(&formula));
    assert_eq!(formula.schema, "trust-types.Formula@1");
    assert_eq!(formula.smtlib.as_deref(), Some("x"));
    assert_eq!(formula.sort.as_deref(), Some("(_ BitVec 64)"));
}

#[test]
fn proof_evidence_smt() {
    let e = ProofEvidence::SmtProof(vec![0xDE, 0xAD]);
    if let ProofEvidence::SmtProof(data) = &e {
        assert_eq!(data, &[0xDE, 0xAD]);
    } else {
        panic!("expected SmtProof");
    }
}

#[test]
fn proof_evidence_lean() {
    let e = ProofEvidence::LeanProof("theorem foo : True := trivial".to_string());
    if let ProofEvidence::LeanProof(s) = &e {
        assert!(s.contains("theorem"));
    } else {
        panic!("expected LeanProof");
    }
}

#[test]
fn proof_evidence_kani() {
    let e = ProofEvidence::KaniHarness("check_add".to_string());
    assert_eq!(format!("{:?}", e), "KaniHarness(\"check_add\")");
}

#[test]
fn proof_evidence_gamma_crown() {
    let e = ProofEvidence::GammaCrownBound {
        epsilon: 0.01,
        verified_layers: 5,
    };
    if let ProofEvidence::GammaCrownBound {
        epsilon,
        verified_layers,
    } = &e
    {
        assert_eq!(*epsilon, 0.01);
        assert_eq!(*verified_layers, 5);
    } else {
        panic!("expected GammaCrownBound");
    }
}

#[test]
fn proof_evidence_translation_validation() {
    let e = ProofEvidence::TranslationValidation {
        rule_name: "inline".to_string(),
        smt_hash: [0u8; 32],
    };
    if let ProofEvidence::TranslationValidation {
        rule_name,
        smt_hash,
    } = &e
    {
        assert_eq!(rule_name, "inline");
        assert_eq!(smt_hash, &[0u8; 32]);
    } else {
        panic!("expected TranslationValidation");
    }
}

#[test]
fn proof_evidence_trusted() {
    let e = ProofEvidence::Trusted("manual review".to_string());
    assert_eq!(format!("{:?}", e), "Trusted(\"manual review\")");
}

#[test]
fn proof_certificate_construction() {
    let cert = ProofCertificate {
        obligation: ProofId::new(0),
        prover: "ay".to_string(),
        evidence: ProofEvidence::SmtProof(vec![]),
    };
    assert_eq!(cert.obligation.index(), 0);
    assert_eq!(cert.prover, "ay");
}

fn digest(seed: u8) -> ProofDigest {
    ProofDigest::sha256([seed; 32])
}

fn obligation(id: u32, node: &ProofLineageNode) -> ProofObligation {
    ProofObligation::new(
        ProofId::new(id),
        ObligationKind::TranslationValidation,
        ProofStatus::Discharged,
        format!("obligation {id}"),
    )
    .with_formula(node.transform_binding_formula())
}

fn certificate(id: u32, prover: &str, payload: &[u8]) -> ProofCertificate {
    ProofCertificate {
        obligation: ProofId::new(id),
        prover: prover.to_string(),
        evidence: ProofEvidence::SmtProof(payload.to_vec()),
    }
}

fn two_stage_manifest(certs: &[ProofCertificate]) -> ProofLineageManifest {
    let mut lowering = ProofLineageNode::new(
        ProofLineageId::new(0),
        ProofTransform::new(
            ProofTransformStage::TrustIrLowering,
            "rustc-mir-to-trust_ir",
            "tRust",
            "2bb348a",
        ),
        digest(1),
        digest(2),
    );
    lowering.obligations.push(ProofId::new(0));
    lowering.certificates.push(certs[0].lineage_ref());

    let mut solver = ProofLineageNode::new(
        ProofLineageId::new(1),
        ProofTransform::new(
            ProofTransformStage::SolverAdapter,
            "trust-ir-ay",
            "TrustIr",
            "0.1.0",
        ),
        digest(2),
        digest(3),
    );
    solver.obligations.push(ProofId::new(1));
    solver.certificates.push(certs[1].lineage_ref());
    solver.depends_on.push(ProofLineageId::new(0));
    solver.replay = Some(
        ProofReplayIdentity::new("tcargo-stage2", "cargo test -p trust-ir-ay")
            .with_transcript_digest(ProofDigest::sha256_domain("test.transcript.v1", b"ok")),
    );

    ProofLineageManifest {
        schema_version: ProofLineageManifest::SCHEMA_VERSION,
        nodes: vec![lowering, solver],
        roots: vec![ProofLineageId::new(1)],
    }
}

#[test]
fn proof_certificate_digest_is_deterministic_and_structural() {
    let cert = certificate(0, "ay", &[1, 2, 3]);
    let same = certificate(0, "ay", &[1, 2, 3]);
    let changed_payload = certificate(0, "ay", &[1, 2, 4]);
    let changed_prover = certificate(0, "lean", &[1, 2, 3]);

    assert_eq!(cert.evidence_digest(), same.evidence_digest());
    assert_eq!(
        cert.evidence_digest().algorithm,
        ProofDigestAlgorithm::Sha256
    );
    assert_eq!(cert.stable_digest().algorithm, ProofDigestAlgorithm::Sha256);
    assert_ne!(cert.evidence_digest(), changed_payload.evidence_digest());
    assert_ne!(cert.stable_digest(), changed_prover.stable_digest());
    assert_eq!(cert.lineage_ref().obligation, ProofId::new(0));
}

#[test]
fn proof_lineage_manifest_validates_two_stage_dag() {
    let certificates = vec![certificate(0, "ay", &[1]), certificate(1, "ay", &[2])];
    let manifest = two_stage_manifest(&certificates);
    let obligations = vec![
        obligation(0, &manifest.nodes[0]),
        obligation(1, &manifest.nodes[1]),
    ];

    manifest.validate().expect("valid lineage shape");
    manifest
        .validate_against(&obligations, &certificates)
        .expect("valid lineage references");

    let mut reordered = manifest.clone();
    reordered.nodes.reverse();
    assert_eq!(manifest.stable_digest(), reordered.stable_digest());
    assert_eq!(
        manifest.stable_digest().algorithm,
        ProofDigestAlgorithm::Sha256
    );
}

#[test]
fn proof_lineage_rejects_noncryptographic_authority_identities() {
    let certificates = vec![certificate(0, "ay", &[1]), certificate(1, "ay", &[2])];
    let manifest = two_stage_manifest(&certificates);

    let mut bad_source = manifest.clone();
    bad_source.nodes[0].source_module = ProofDigest::trust_ir_stable("legacy.source", b"source");
    assert!(matches!(
        bad_source.validate(),
        Err(errors) if errors.iter().any(|error| matches!(
            error,
            ProofLineageError::NonCryptographicDigest { field: "source_module", .. }
        ))
    ));

    let mut bad_certificate = manifest.clone();
    bad_certificate.nodes[0].certificates[0].evidence_digest =
        ProofDigest::trust_ir_stable("legacy.certificate", b"evidence");
    assert!(matches!(
        bad_certificate.validate(),
        Err(errors) if errors.iter().any(|error| matches!(
            error,
            ProofLineageError::NonCryptographicDigest {
                field: "certificate.evidence_digest",
                ..
            }
        ))
    ));

    let mut bad_replay = manifest;
    bad_replay.nodes[1]
        .replay
        .as_mut()
        .expect("replay identity")
        .transcript_digest = Some(ProofDigest::trust_ir_stable("legacy.replay", b"log"));
    assert!(matches!(
        bad_replay.validate(),
        Err(errors) if errors.iter().any(|error| matches!(
            error,
            ProofLineageError::NonCryptographicDigest {
                field: "replay.transcript_digest",
                ..
            }
        ))
    ));
}

#[test]
fn proof_lineage_validation_rejects_missing_dependency_cycle_and_stale_certificate() {
    let certificates = vec![certificate(0, "ay", &[1]), certificate(1, "ay", &[2])];
    let base_manifest = two_stage_manifest(&certificates);
    let obligations = vec![
        obligation(0, &base_manifest.nodes[0]),
        obligation(1, &base_manifest.nodes[1]),
    ];

    let mut missing_dep = base_manifest.clone();
    missing_dep.nodes[0]
        .depends_on
        .push(ProofLineageId::new(99));
    let errors = missing_dep
        .validate()
        .expect_err("missing dependency rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        ProofLineageError::MissingDependency {
            node: ProofLineageId(0),
            dependency: ProofLineageId(99)
        }
    )));

    let mut no_root = base_manifest.clone();
    no_root.roots.clear();
    let errors = no_root.validate().expect_err("missing root rejected");
    assert!(
        errors
            .iter()
            .any(|err| matches!(err, ProofLineageError::EmptyRoots))
    );

    let mut cycle = base_manifest.clone();
    cycle.nodes[0].depends_on.push(ProofLineageId::new(1));
    let errors = cycle.validate().expect_err("cycle rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        ProofLineageError::Cycle {
            node: ProofLineageId(0) | ProofLineageId(1)
        }
    )));

    let mut mismatched_digest = base_manifest.clone();
    mismatched_digest.nodes[1].source_module = digest(99);
    let errors = mismatched_digest
        .validate()
        .expect_err("dependency target/source mismatch rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        ProofLineageError::DependencyDigestMismatch {
            node: ProofLineageId(1),
            dependency: ProofLineageId(0),
            ..
        }
    )));

    let mut stale = base_manifest;
    stale.nodes[0].certificates[0].evidence_digest = digest(9);
    let errors = stale
        .validate_against(&obligations, &certificates)
        .expect_err("stale certificate digest rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        ProofLineageError::CertificateDigestMismatch {
            node: ProofLineageId(0),
            obligation: ProofId(0),
            prover
        } if prover == "ay"
    )));
}

#[test]
fn proof_lineage_validation_rejects_ambiguous_certificate_identity() {
    let certificates = vec![certificate(0, "ay", &[1]), certificate(1, "ay", &[2])];
    let mut manifest = two_stage_manifest(&certificates);
    let mut stale_ref = certificates[0].lineage_ref();
    stale_ref.evidence_digest = digest(99);
    manifest.nodes[0].certificates.push(stale_ref);

    let errors = manifest
        .validate()
        .expect_err("duplicate certificate identity rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        ProofLineageError::DuplicateCertificateIdentity {
            node: ProofLineageId(0),
            obligation: ProofId(0),
            prover
        } if prover == "ay"
    )));
}

#[test]
fn proof_lineage_validation_rejects_replay_stage_without_identity() {
    let cert = certificate(0, "ay", &[1]);
    let mut replay_node = ProofLineageNode::new(
        ProofLineageId::new(0),
        ProofTransform::new(ProofTransformStage::Replay, "replay-ay", "TrustIr", "0.1.0"),
        digest(1),
        digest(2),
    );
    replay_node.obligations.push(ProofId::new(0));
    replay_node.certificates.push(cert.lineage_ref());

    let manifest = ProofLineageManifest {
        schema_version: ProofLineageManifest::SCHEMA_VERSION,
        nodes: vec![replay_node],
        roots: vec![ProofLineageId::new(0)],
    };

    let errors = manifest
        .validate()
        .expect_err("replay stage without identity rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        ProofLineageError::MissingReplayIdentity(ProofLineageId(0))
    )));
}

#[test]
fn proof_lineage_validation_rejects_malformed_replay_identity() {
    let certificates = vec![certificate(0, "ay", &[1]), certificate(1, "ay", &[2])];
    let mut manifest = two_stage_manifest(&certificates);
    manifest.nodes[1].replay = Some(
        ProofReplayIdentity::new(" ", "").with_transcript_digest(ProofDigest::sha256([0; 32])),
    );

    let errors = manifest
        .validate()
        .expect_err("malformed replay identity rejected");
    assert!(errors.iter().any(|err| matches!(
        err,
        ProofLineageError::InvalidReplayIdentity {
            node: ProofLineageId(1),
            field: "engine"
        }
    )));
    assert!(errors.iter().any(|err| matches!(
        err,
        ProofLineageError::InvalidReplayIdentity {
            node: ProofLineageId(1),
            field: "invocation"
        }
    )));
    assert!(errors.iter().any(|err| matches!(
        err,
        ProofLineageError::InvalidReplayIdentity {
            node: ProofLineageId(1),
            field: "transcript_digest"
        }
    )));
}

#[test]
fn trusted_certificate_evidence_is_explicit_not_summary_magic() {
    let trusted = ProofCertificate {
        obligation: ProofId::new(0),
        prover: "human-review".to_string(),
        evidence: ProofEvidence::Trusted("security signoff ticket TSEC-123".to_string()),
    };
    let solver = certificate(0, "ay", &[1, 2, 3]);

    assert!(trusted.uses_trusted_evidence());
    assert!(!solver.uses_trusted_evidence());
}

// --- Classification method tests ---

#[test]
fn is_memory_safety_positive() {
    let memory_safety = [
        ProofAnnotation::InBounds,
        ProofAnnotation::NotNull,
        ProofAnnotation::ValidBorrow,
        ProofAnnotation::UniqueBorrow,
        ProofAnnotation::SharedBorrow,
        ProofAnnotation::ValidDealloc,
    ];
    for ann in &memory_safety {
        assert!(ann.is_memory_safety(), "{:?} should be memory safety", ann);
    }
}

#[test]
fn is_memory_safety_negative() {
    let not_memory_safety = [
        ProofAnnotation::NoOverflow,
        ProofAnnotation::Pure,
        ProofAnnotation::Commutative,
        ProofAnnotation::DataRaceFree,
    ];
    for ann in &not_memory_safety {
        assert!(
            !ann.is_memory_safety(),
            "{:?} should not be memory safety",
            ann
        );
    }
}

#[test]
fn is_arithmetic_safety_positive() {
    let arith_safety = [
        ProofAnnotation::NoOverflow,
        ProofAnnotation::NoWrap,
        ProofAnnotation::DivNonZero,
        ProofAnnotation::ShiftInRange,
    ];
    for ann in &arith_safety {
        assert!(
            ann.is_arithmetic_safety(),
            "{:?} should be arithmetic safety",
            ann
        );
    }
}

#[test]
fn is_arithmetic_safety_negative() {
    let not_arith = [
        ProofAnnotation::InBounds,
        ProofAnnotation::Pure,
        ProofAnnotation::ValidBorrow,
    ];
    for ann in &not_arith {
        assert!(
            !ann.is_arithmetic_safety(),
            "{:?} should not be arithmetic safety",
            ann
        );
    }
}

#[test]
fn is_functional_positive() {
    let functional = [
        ProofAnnotation::Pure,
        ProofAnnotation::Terminates,
        ProofAnnotation::Deterministic,
        ProofAnnotation::Associative,
        ProofAnnotation::Commutative,
    ];
    for ann in &functional {
        assert!(ann.is_functional(), "{:?} should be functional", ann);
    }
}

#[test]
fn is_functional_negative() {
    let not_functional = [
        ProofAnnotation::InBounds,
        ProofAnnotation::NoOverflow,
        ProofAnnotation::DataRaceFree,
    ];
    for ann in &not_functional {
        assert!(!ann.is_functional(), "{:?} should not be functional", ann);
    }
}

#[test]
fn is_gpu_relevant_positive() {
    let gpu_relevant = [
        ProofAnnotation::Pure,
        ProofAnnotation::InBounds,
        ProofAnnotation::NoOverflow,
        ProofAnnotation::Commutative,
        ProofAnnotation::Associative,
        ProofAnnotation::Deterministic,
        ProofAnnotation::ValidBorrow,
        ProofAnnotation::NoPanic,
        ProofAnnotation::NoAlias,
    ];
    for ann in &gpu_relevant {
        assert!(ann.is_gpu_relevant(), "{:?} should be GPU relevant", ann);
    }
    // Aligned with any value should be GPU relevant
    assert!(ProofAnnotation::Aligned(16).is_gpu_relevant());
}

#[test]
fn is_gpu_relevant_negative() {
    let not_gpu = [
        ProofAnnotation::DataRaceFree,
        ProofAnnotation::Terminates,
        ProofAnnotation::Monotonic,
        ProofAnnotation::NotNull,
        ProofAnnotation::NoWrap,
    ];
    for ann in &not_gpu {
        assert!(
            !ann.is_gpu_relevant(),
            "{:?} should not be GPU relevant",
            ann
        );
    }
}

#[test]
fn classification_overlap_pure_is_functional_and_gpu() {
    let pure = ProofAnnotation::Pure;
    assert!(pure.is_functional());
    assert!(pure.is_gpu_relevant());
    assert!(!pure.is_memory_safety());
    assert!(!pure.is_arithmetic_safety());
}

#[test]
fn classification_overlap_valid_borrow_is_memory_and_gpu() {
    let vb = ProofAnnotation::ValidBorrow;
    assert!(vb.is_memory_safety());
    assert!(vb.is_gpu_relevant());
    assert!(!vb.is_functional());
    assert!(!vb.is_arithmetic_safety());
}

#[test]
fn classification_custom_is_none() {
    let custom = ProofAnnotation::Custom(ProofTag::new(0));
    assert!(!custom.is_memory_safety());
    assert!(!custom.is_arithmetic_safety());
    assert!(!custom.is_functional());
    assert!(!custom.is_gpu_relevant());
    assert!(!custom.is_concurrency());
    assert!(!custom.is_neural_network());
    assert!(!custom.is_aliasing());
}

// --- New variant tests ---

#[test]
fn proof_annotation_no_alias() {
    let na = ProofAnnotation::NoAlias;
    assert_eq!(format!("{}", na), "no_alias");
    assert!(na.is_aliasing());
    assert!(na.is_gpu_relevant());
    assert!(!na.is_memory_safety());
    assert!(!na.is_functional());
}

#[test]
fn proof_annotation_aligned() {
    let a16 = ProofAnnotation::Aligned(16);
    let a64 = ProofAnnotation::Aligned(64);
    assert_ne!(a16, a64);
    assert_eq!(format!("{}", a16), "aligned(16)");
    assert!(a16.is_gpu_relevant());
    assert!(!a16.is_memory_safety());
    assert!(!a16.is_aliasing());
    if let ProofAnnotation::Aligned(n) = &a16 {
        assert_eq!(*n, 16);
    } else {
        panic!("expected Aligned");
    }
}

#[test]
fn proof_annotation_no_panic() {
    let np = ProofAnnotation::NoPanic;
    assert_eq!(format!("{}", np), "no_panic");
    assert!(np.is_gpu_relevant());
    assert!(!np.is_memory_safety());
    assert!(!np.is_arithmetic_safety());
    assert!(!np.is_functional());
}

#[test]
fn proof_annotation_no_undef() {
    let nu = ProofAnnotation::NoUndef;
    assert_eq!(format!("{}", nu), "no_undef");
    assert!(!nu.is_memory_safety());
    assert!(!nu.is_arithmetic_safety());
    assert!(!nu.is_functional());
    assert!(!nu.is_gpu_relevant());
}

// --- Concurrency classification tests ---

#[test]
fn is_concurrency_positive() {
    let concurrency = [
        ProofAnnotation::DataRaceFree,
        ProofAnnotation::AtomicOrdering(Ordering::SeqCst),
    ];
    for ann in &concurrency {
        assert!(ann.is_concurrency(), "{:?} should be concurrency", ann);
    }
}

#[test]
fn is_concurrency_negative() {
    let not_concurrency = [
        ProofAnnotation::Pure,
        ProofAnnotation::InBounds,
        ProofAnnotation::NoOverflow,
        ProofAnnotation::NoAlias,
    ];
    for ann in &not_concurrency {
        assert!(!ann.is_concurrency(), "{:?} should not be concurrency", ann);
    }
}

// --- Neural network classification tests ---

#[test]
fn is_neural_network_positive() {
    let nn = [
        ProofAnnotation::BoundedOutput { lo: -1.0, hi: 1.0 },
        ProofAnnotation::Monotonic,
    ];
    for ann in &nn {
        assert!(
            ann.is_neural_network(),
            "{:?} should be neural_network",
            ann
        );
    }
}

#[test]
fn is_neural_network_negative() {
    let not_nn = [
        ProofAnnotation::Pure,
        ProofAnnotation::NoOverflow,
        ProofAnnotation::InBounds,
    ];
    for ann in &not_nn {
        assert!(
            !ann.is_neural_network(),
            "{:?} should not be neural_network",
            ann
        );
    }
}

// --- Aliasing classification tests ---

#[test]
fn is_aliasing_positive() {
    let aliasing = [
        ProofAnnotation::NoAlias,
        ProofAnnotation::ValidBorrow,
        ProofAnnotation::UniqueBorrow,
        ProofAnnotation::SharedBorrow,
    ];
    for ann in &aliasing {
        assert!(ann.is_aliasing(), "{:?} should be aliasing", ann);
    }
}

#[test]
fn is_aliasing_negative() {
    let not_aliasing = [
        ProofAnnotation::InBounds,
        ProofAnnotation::Pure,
        ProofAnnotation::NoOverflow,
        ProofAnnotation::NotNull,
    ];
    for ann in &not_aliasing {
        assert!(!ann.is_aliasing(), "{:?} should not be aliasing", ann);
    }
}

// --- Cross-category overlap tests ---

#[test]
fn classification_overlap_valid_borrow_is_memory_aliasing_and_gpu() {
    let vb = ProofAnnotation::ValidBorrow;
    assert!(vb.is_memory_safety());
    assert!(vb.is_aliasing());
    assert!(vb.is_gpu_relevant());
    assert!(!vb.is_functional());
    assert!(!vb.is_concurrency());
    assert!(!vb.is_neural_network());
}

#[test]
fn classification_overlap_no_alias_is_aliasing_and_gpu_not_memory() {
    let na = ProofAnnotation::NoAlias;
    assert!(na.is_aliasing());
    assert!(na.is_gpu_relevant());
    assert!(!na.is_memory_safety());
    assert!(!na.is_functional());
}

#[test]
fn classification_no_undef_is_isolated() {
    let nu = ProofAnnotation::NoUndef;
    assert!(!nu.is_memory_safety());
    assert!(!nu.is_arithmetic_safety());
    assert!(!nu.is_functional());
    assert!(!nu.is_gpu_relevant());
    assert!(!nu.is_concurrency());
    assert!(!nu.is_neural_network());
    assert!(!nu.is_aliasing());
}

// --- ProofSummary tests ---

#[test]
fn proof_summary_default_is_zero() {
    let summary = ProofSummary::default();
    assert_eq!(summary.pending, 0);
    assert_eq!(summary.discharged, 0);
    assert_eq!(summary.failed, 0);
    assert_eq!(summary.trusted, 0);
    assert_eq!(summary.certified, 0);
    assert_eq!(summary.total(), 0);
    assert!(summary.is_fully_verified());
}

#[test]
fn proof_summary_total() {
    let summary = ProofSummary {
        pending: 1,
        discharged: 5,
        failed: 2,
        trusted: 3,
        certified: 4,
    };
    // Certified is counted in its own arm and included in total().
    assert_eq!(summary.total(), 15);
}

#[test]
fn proof_summary_fully_verified_when_discharged_and_trusted() {
    let summary = ProofSummary {
        pending: 0,
        discharged: 10,
        failed: 0,
        trusted: 2,
        certified: 1,
    };
    assert!(summary.is_fully_verified());
}

#[test]
fn proof_summary_not_verified_when_pending() {
    let summary = ProofSummary {
        pending: 1,
        discharged: 10,
        failed: 0,
        trusted: 0,
        certified: 0,
    };
    assert!(!summary.is_fully_verified());
}

#[test]
#[allow(deprecated)]
fn proof_summary_strict_excludes_faith_stamped_and_empty() {
    // Empty: status-level "verified" but no strong-completion claim.
    let empty = ProofSummary::default();
    assert!(empty.is_fully_verified());
    assert!(!empty.is_fully_verified_strict());

    // Any Trusted disqualifies strict (faith-stamped, not machine-checked).
    let with_trusted = ProofSummary {
        pending: 0,
        discharged: 5,
        failed: 0,
        trusted: 1,
        certified: 2,
    };
    assert!(with_trusted.is_fully_verified());
    assert!(!with_trusted.is_fully_verified_strict());

    // Forged public labels satisfy only the status predicate; they still have
    // no replayed evidence authority.
    let labelled_strong = ProofSummary {
        pending: 0,
        discharged: 5,
        failed: 0,
        trusted: 0,
        certified: 2,
    };
    assert!(labelled_strong.statuses_claim_strong_completion());
    assert!(labelled_strong.is_fully_verified_strict());

    let obligation = ProofObligation::new(
        ProofId::new(99),
        ObligationKind::Postcondition,
        ProofStatus::Discharged,
        "forged status-only claim",
    );
    assert!(!obligation_has_replayed_authority(
        &obligation,
        &[],
        &RejectingProofAuthorityRechecker,
    ));
}

#[test]
fn proof_summary_not_verified_when_failed() {
    let summary = ProofSummary {
        pending: 0,
        discharged: 10,
        failed: 1,
        trusted: 0,
        certified: 0,
    };
    assert!(!summary.is_fully_verified());
}

// --- Display impl tests: verify exact string output for every variant ---

#[test]
fn proof_annotation_display_all_variants() {
    let cases: &[(ProofAnnotation, &str)] = &[
        (ProofAnnotation::InBounds, "in_bounds"),
        (ProofAnnotation::NotNull, "not_null"),
        (ProofAnnotation::ValidBorrow, "valid_borrow"),
        (ProofAnnotation::UniqueBorrow, "unique_borrow"),
        (ProofAnnotation::SharedBorrow, "shared_borrow"),
        (ProofAnnotation::ValidDealloc, "valid_dealloc"),
        (ProofAnnotation::NoOverflow, "no_overflow"),
        (ProofAnnotation::NoWrap, "no_wrap"),
        (ProofAnnotation::DivNonZero, "div_nonzero"),
        (ProofAnnotation::ShiftInRange, "shift_in_range"),
        (ProofAnnotation::Pure, "pure"),
        (ProofAnnotation::Terminates, "terminates"),
        (ProofAnnotation::Deterministic, "deterministic"),
        (ProofAnnotation::Associative, "associative"),
        (ProofAnnotation::Commutative, "commutative"),
        (ProofAnnotation::DataRaceFree, "data_race_free"),
        (
            ProofAnnotation::AtomicOrdering(Ordering::SeqCst),
            "atomic_ordering(seq_cst)",
        ),
        (
            ProofAnnotation::AtomicOrdering(Ordering::Relaxed),
            "atomic_ordering(relaxed)",
        ),
        (
            ProofAnnotation::BoundedOutput { lo: -1.0, hi: 1.0 },
            "bounded_output(-1, 1)",
        ),
        (ProofAnnotation::Monotonic, "monotonic"),
        (ProofAnnotation::Custom(ProofTag::new(42)), "custom(42)"),
    ];
    assert_eq!(cases.len(), 21);
    for (ann, expected) in cases {
        assert_eq!(
            format!("{}", ann),
            *expected,
            "ProofAnnotation::{:?} display mismatch",
            ann
        );
    }
}

#[test]
fn obligation_kind_display_all_variants() {
    let cases: &[(ObligationKind, &str)] = &[
        (ObligationKind::Precondition, "precondition"),
        (ObligationKind::Postcondition, "postcondition"),
        (ObligationKind::LoopInvariant, "loop_invariant"),
        (ObligationKind::TypeInvariant, "type_invariant"),
        (ObligationKind::RefinementType, "refinement_type"),
        (
            ObligationKind::TranslationValidation,
            "translation_validation",
        ),
        (ObligationKind::MemorySafety, "memory_safety"),
        (ObligationKind::PanicFreedom, "panic_freedom"),
        (ObligationKind::TemporalSafety, "temporal_safety"),
        (ObligationKind::Liveness, "liveness"),
    ];
    assert_eq!(cases.len(), 10);
    for (kind, expected) in cases {
        assert_eq!(
            format!("{}", kind),
            *expected,
            "ObligationKind::{:?} display mismatch",
            kind
        );
    }
}

#[test]
fn proof_status_display_all_variants() {
    let cases: &[(ProofStatus, &str)] = &[
        (ProofStatus::Pending, "pending"),
        (ProofStatus::Discharged, "discharged"),
        (ProofStatus::Failed, "failed"),
        (ProofStatus::Trusted, "trusted"),
    ];
    assert_eq!(cases.len(), 4);
    for (status, expected) in cases {
        assert_eq!(
            format!("{}", status),
            *expected,
            "ProofStatus::{:?} display mismatch",
            status
        );
    }
}

// --- ProofAnnotation Clone tests ---

#[test]
fn proof_annotation_clone_all_variants() {
    let annotations = vec![
        ProofAnnotation::InBounds,
        ProofAnnotation::NotNull,
        ProofAnnotation::ValidBorrow,
        ProofAnnotation::UniqueBorrow,
        ProofAnnotation::SharedBorrow,
        ProofAnnotation::ValidDealloc,
        ProofAnnotation::NoOverflow,
        ProofAnnotation::NoWrap,
        ProofAnnotation::DivNonZero,
        ProofAnnotation::ShiftInRange,
        ProofAnnotation::Pure,
        ProofAnnotation::Terminates,
        ProofAnnotation::Deterministic,
        ProofAnnotation::Associative,
        ProofAnnotation::Commutative,
        ProofAnnotation::DataRaceFree,
        ProofAnnotation::AtomicOrdering(Ordering::AcqRel),
        ProofAnnotation::BoundedOutput { lo: 0.0, hi: 100.0 },
        ProofAnnotation::Monotonic,
        ProofAnnotation::Custom(ProofTag::new(99)),
    ];
    for ann in &annotations {
        let cloned = ann.clone();
        assert_eq!(ann, &cloned, "Clone mismatch for {:?}", ann);
    }
}

// --- ProofEvidence Clone tests ---

#[test]
fn proof_evidence_clone_all_variants() {
    let evidences = vec![
        ProofEvidence::SmtProof(vec![1, 2, 3]),
        ProofEvidence::LeanProof("theorem".to_string()),
        ProofEvidence::KaniHarness("harness".to_string()),
        ProofEvidence::GammaCrownBound {
            epsilon: 0.001,
            verified_layers: 10,
        },
        ProofEvidence::TranslationValidation {
            rule_name: "rule".to_string(),
            smt_hash: [0xFF; 32],
        },
        ProofEvidence::Trusted("trusted".to_string()),
    ];
    for ev in &evidences {
        let cloned = ev.clone();
        assert_eq!(ev, &cloned, "Clone mismatch for {:?}", ev);
    }
}

// --- ProofObligation and ProofCertificate Clone tests ---

#[test]
fn proof_obligation_clone() {
    let po = ProofObligation {
        id: ProofId::new(5),
        kind: ObligationKind::LoopInvariant,
        status: ProofStatus::Discharged,
        description: "loop invariant holds".to_string(),
        formula: None,
        function: None,
        source: None,
        site: None,
    };
    let cloned = po.clone();
    assert_eq!(po, cloned);
}

#[test]
fn proof_certificate_clone() {
    let cert = ProofCertificate {
        obligation: ProofId::new(3),
        prover: "lean".to_string(),
        evidence: ProofEvidence::LeanProof("proof term".to_string()),
    };
    let cloned = cert.clone();
    assert_eq!(cert, cloned);
}

// --- Cross-classification boundary tests ---

#[test]
fn classification_no_overlap_between_memory_and_arithmetic() {
    let memory = [
        ProofAnnotation::InBounds,
        ProofAnnotation::NotNull,
        ProofAnnotation::ValidBorrow,
        ProofAnnotation::UniqueBorrow,
        ProofAnnotation::SharedBorrow,
        ProofAnnotation::ValidDealloc,
    ];
    for ann in &memory {
        assert!(
            !ann.is_arithmetic_safety(),
            "{:?} should not be arithmetic",
            ann
        );
    }
    let arithmetic = [
        ProofAnnotation::NoOverflow,
        ProofAnnotation::NoWrap,
        ProofAnnotation::DivNonZero,
        ProofAnnotation::ShiftInRange,
    ];
    for ann in &arithmetic {
        assert!(
            !ann.is_memory_safety(),
            "{:?} should not be memory safety",
            ann
        );
    }
}

#[test]
fn classification_bounded_output_is_none() {
    let bo = ProofAnnotation::BoundedOutput { lo: -1.0, hi: 1.0 };
    assert!(!bo.is_memory_safety());
    assert!(!bo.is_arithmetic_safety());
    assert!(!bo.is_functional());
    assert!(!bo.is_gpu_relevant());
}

#[test]
fn classification_monotonic_is_none() {
    let m = ProofAnnotation::Monotonic;
    assert!(!m.is_memory_safety());
    assert!(!m.is_arithmetic_safety());
    assert!(!m.is_functional());
    assert!(!m.is_gpu_relevant());
}

#[test]
fn classification_data_race_free_is_none_of_main_categories() {
    let drf = ProofAnnotation::DataRaceFree;
    assert!(!drf.is_memory_safety());
    assert!(!drf.is_arithmetic_safety());
    assert!(!drf.is_functional());
    assert!(!drf.is_gpu_relevant());
}

#[test]
fn classification_atomic_ordering_is_none_of_main_categories() {
    let ao = ProofAnnotation::AtomicOrdering(Ordering::SeqCst);
    assert!(!ao.is_memory_safety());
    assert!(!ao.is_arithmetic_safety());
    assert!(!ao.is_functional());
    assert!(!ao.is_gpu_relevant());
}

// --- ObligationKind equality/inequality ---

#[test]
fn obligation_kind_inequality() {
    let kinds = [
        ObligationKind::Precondition,
        ObligationKind::Postcondition,
        ObligationKind::LoopInvariant,
        ObligationKind::TypeInvariant,
        ObligationKind::RefinementType,
        ObligationKind::TranslationValidation,
        ObligationKind::MemorySafety,
        ObligationKind::PanicFreedom,
        ObligationKind::TemporalSafety,
        ObligationKind::Liveness,
    ];
    for (i, a) in kinds.iter().enumerate() {
        for (j, b) in kinds.iter().enumerate() {
            if i == j {
                assert_eq!(a, b);
            } else {
                assert_ne!(a, b);
            }
        }
    }
}

// --- ProofStatus equality/inequality ---

#[test]
fn proof_status_inequality() {
    let statuses = [
        ProofStatus::Pending,
        ProofStatus::Discharged,
        ProofStatus::Failed,
        ProofStatus::Trusted,
    ];
    for (i, a) in statuses.iter().enumerate() {
        for (j, b) in statuses.iter().enumerate() {
            if i == j {
                assert_eq!(a, b);
            } else {
                assert_ne!(a, b);
            }
        }
    }
}

// --- Hash tests ---

#[test]
fn obligation_kind_hash_consistency() {
    use std::collections::HashSet;
    let mut set = HashSet::new();
    set.insert(ObligationKind::Precondition);
    set.insert(ObligationKind::Postcondition);
    set.insert(ObligationKind::Precondition); // duplicate
    assert_eq!(set.len(), 2);
}

#[test]
fn proof_status_hash_consistency() {
    use std::collections::HashSet;
    let mut set = HashSet::new();
    for s in &[
        ProofStatus::Pending,
        ProofStatus::Discharged,
        ProofStatus::Failed,
        ProofStatus::Trusted,
    ] {
        set.insert(*s);
    }
    assert_eq!(set.len(), 4);
}

// --- Memory-role attribute tests (TrustIr#30 item 2) ---

#[test]
fn divergence_display() {
    assert_eq!(format!("{}", Divergence::Uniform), "uniform");
    assert_eq!(format!("{}", Divergence::Low), "low");
    assert_eq!(format!("{}", Divergence::High), "high");
}

#[test]
fn divergence_inequality_and_hash() {
    use std::collections::HashSet;
    let mut set = HashSet::new();
    set.insert(Divergence::Uniform);
    set.insert(Divergence::Low);
    set.insert(Divergence::High);
    set.insert(Divergence::Uniform); // duplicate
    assert_eq!(set.len(), 3);
    assert_ne!(Divergence::Uniform, Divergence::Low);
    assert_ne!(Divergence::Low, Divergence::High);
}

#[test]
fn memory_role_variants_display() {
    assert_eq!(
        format!("{}", ProofAnnotation::ReadonlyTable),
        "readonly_table"
    );
    assert_eq!(
        format!("{}", ProofAnnotation::AppendOnlyBuffer),
        "append_only_buffer"
    );
    assert_eq!(
        format!("{}", ProofAnnotation::AtomicSetInsert),
        "atomic_set_insert"
    );
}

#[test]
fn memory_role_variants_are_distinct() {
    let variants = [
        ProofAnnotation::ReadonlyTable,
        ProofAnnotation::AppendOnlyBuffer,
        ProofAnnotation::AtomicSetInsert,
    ];
    for (i, a) in variants.iter().enumerate() {
        for (j, b) in variants.iter().enumerate() {
            if i == j {
                assert_eq!(a, b);
            } else {
                assert_ne!(a, b);
            }
        }
    }
}

#[test]
fn is_memory_role_positive() {
    for ann in &[
        ProofAnnotation::ReadonlyTable,
        ProofAnnotation::AppendOnlyBuffer,
        ProofAnnotation::AtomicSetInsert,
    ] {
        assert!(ann.is_memory_role(), "{:?} should be memory_role", ann);
    }
}

#[test]
fn is_memory_role_negative() {
    for ann in &[
        ProofAnnotation::Pure,
        ProofAnnotation::InBounds,
        ProofAnnotation::NoAlias,
        ProofAnnotation::DataRaceFree,
        ProofAnnotation::ParallelMap,
    ] {
        assert!(!ann.is_memory_role(), "{:?} should not be memory_role", ann);
    }
}

#[test]
fn memory_role_is_gpu_relevant() {
    for ann in &[
        ProofAnnotation::ReadonlyTable,
        ProofAnnotation::AppendOnlyBuffer,
        ProofAnnotation::AtomicSetInsert,
    ] {
        assert!(
            ann.is_gpu_relevant(),
            "{:?} should be GPU relevant (address-space hint)",
            ann
        );
    }
}

#[test]
fn atomic_set_insert_is_also_concurrency() {
    let asi = ProofAnnotation::AtomicSetInsert;
    assert!(asi.is_memory_role());
    assert!(asi.is_concurrency());
    assert!(asi.is_gpu_relevant());
}

#[test]
fn memory_role_not_in_other_categories() {
    let rt = ProofAnnotation::ReadonlyTable;
    assert!(!rt.is_memory_safety());
    assert!(!rt.is_arithmetic_safety());
    assert!(!rt.is_functional());
    assert!(!rt.is_concurrency());
    assert!(!rt.is_neural_network());
    assert!(!rt.is_aliasing());
    assert!(!rt.is_parallel());
    let aob = ProofAnnotation::AppendOnlyBuffer;
    assert!(!aob.is_memory_safety());
    assert!(!aob.is_functional());
    assert!(!aob.is_concurrency());
}

// --- Parallel / purity attribute tests (TrustIr#30 item 3) ---

#[test]
fn parallel_variants_display() {
    assert_eq!(format!("{}", ProofAnnotation::ParallelMap), "parallel_map");
    assert_eq!(
        format!("{}", ProofAnnotation::BoundedLoop(128)),
        "bounded_loop(128)"
    );
    assert_eq!(
        format!("{}", ProofAnnotation::DivergenceClass(Divergence::Uniform)),
        "divergence_class(uniform)"
    );
    assert_eq!(
        format!("{}", ProofAnnotation::DivergenceClass(Divergence::Low)),
        "divergence_class(low)"
    );
    assert_eq!(
        format!("{}", ProofAnnotation::DivergenceClass(Divergence::High)),
        "divergence_class(high)"
    );
}

#[test]
fn bounded_loop_parameterized_equality() {
    let a = ProofAnnotation::BoundedLoop(64);
    let b = ProofAnnotation::BoundedLoop(64);
    let c = ProofAnnotation::BoundedLoop(65);
    assert_eq!(a, b);
    assert_ne!(a, c);
}

#[test]
fn divergence_class_parameterized_equality() {
    let u = ProofAnnotation::DivergenceClass(Divergence::Uniform);
    let l = ProofAnnotation::DivergenceClass(Divergence::Low);
    let h = ProofAnnotation::DivergenceClass(Divergence::High);
    assert_ne!(u, l);
    assert_ne!(l, h);
    assert_eq!(u, ProofAnnotation::DivergenceClass(Divergence::Uniform));
}

#[test]
fn is_parallel_positive() {
    for ann in &[
        ProofAnnotation::ParallelMap,
        ProofAnnotation::BoundedLoop(16),
        ProofAnnotation::DivergenceClass(Divergence::Uniform),
        ProofAnnotation::DivergenceClass(Divergence::Low),
        ProofAnnotation::DivergenceClass(Divergence::High),
    ] {
        assert!(ann.is_parallel(), "{:?} should be parallel", ann);
    }
}

#[test]
fn is_parallel_negative() {
    for ann in &[
        ProofAnnotation::Pure, // Pure is functional, not parallel
        ProofAnnotation::ReadonlyTable,
        ProofAnnotation::NoAlias,
        ProofAnnotation::DataRaceFree,
        ProofAnnotation::InBounds,
    ] {
        assert!(!ann.is_parallel(), "{:?} should not be parallel", ann);
    }
}

#[test]
fn pure_stays_functional_only() {
    let p = ProofAnnotation::Pure;
    assert!(p.is_functional());
    assert!(!p.is_parallel());
    assert!(p.is_gpu_relevant());
}

#[test]
fn parallel_map_is_gpu_relevant() {
    assert!(ProofAnnotation::ParallelMap.is_gpu_relevant());
}

#[test]
fn bounded_loop_is_gpu_relevant() {
    assert!(ProofAnnotation::BoundedLoop(1).is_gpu_relevant());
    assert!(ProofAnnotation::BoundedLoop(u64::MAX).is_gpu_relevant());
}

#[test]
fn divergence_uniform_and_low_are_gpu_relevant() {
    assert!(ProofAnnotation::DivergenceClass(Divergence::Uniform).is_gpu_relevant());
    assert!(ProofAnnotation::DivergenceClass(Divergence::Low).is_gpu_relevant());
}

#[test]
fn divergence_high_is_not_gpu_relevant() {
    // DivergenceClass(High) is a hazard marker: its presence means the
    // region is NOT safe for GPU. Therefore it must NOT appear in
    // gpu_relevant annotations.
    assert!(!ProofAnnotation::DivergenceClass(Divergence::High).is_gpu_relevant());
}

// --- Roundtrip serde tests (feature = "serde") ---

#[cfg(feature = "serde")]
#[test]
fn divergence_serde_roundtrip() {
    for d in [Divergence::Uniform, Divergence::Low, Divergence::High] {
        let bytes = rmp_serde::to_vec(&d).expect("serialize Divergence");
        let back: Divergence = rmp_serde::from_slice(&bytes).expect("deserialize Divergence");
        assert_eq!(d, back);
    }
}

#[cfg(feature = "serde")]
#[test]
fn memory_role_serde_roundtrip() {
    let variants = [
        ProofAnnotation::ReadonlyTable,
        ProofAnnotation::AppendOnlyBuffer,
        ProofAnnotation::AtomicSetInsert,
    ];
    for ann in &variants {
        let bytes = rmp_serde::to_vec(ann).expect("serialize memory-role");
        let back: ProofAnnotation = rmp_serde::from_slice(&bytes).expect("deserialize memory-role");
        assert_eq!(ann, &back);
    }
}

#[cfg(feature = "serde")]
#[test]
fn parallel_attrs_serde_roundtrip() {
    let variants = [
        ProofAnnotation::ParallelMap,
        ProofAnnotation::BoundedLoop(1024),
        ProofAnnotation::DivergenceClass(Divergence::Uniform),
        ProofAnnotation::DivergenceClass(Divergence::Low),
        ProofAnnotation::DivergenceClass(Divergence::High),
    ];
    for ann in &variants {
        let bytes = rmp_serde::to_vec(ann).expect("serialize parallel annotation");
        let back: ProofAnnotation =
            rmp_serde::from_slice(&bytes).expect("deserialize parallel annotation");
        assert_eq!(ann, &back);
    }
}

#[test]
fn proof_evidence_clean_cic_construction() {
    let e = ProofEvidence::CleanCic {
        term: vec![0xDE, 0xAD, 0xBE, 0xEF],
        context: vec![0x01, 0x02, 0x03],
        lineage: ProofDigest::sha256([7u8; 32]),
        kernel_recheck: None,
    };
    if let ProofEvidence::CleanCic {
        term,
        context,
        lineage,
        kernel_recheck,
    } = &e
    {
        assert_eq!(term, &[0xDE, 0xAD, 0xBE, 0xEF]);
        assert_eq!(context, &[0x01, 0x02, 0x03]);
        assert_eq!(lineage.algorithm, ProofDigestAlgorithm::Sha256);
        assert_eq!(lineage.bytes, [7u8; 32]);
        assert!(kernel_recheck.is_none());
    } else {
        panic!("expected CleanCic");
    }
}

#[test]
fn proof_evidence_clean_cic_with_kernel_recheck() {
    let recheck = CleanCicKernelRecheck {
        module: "Crownproof.SlackCertZ".to_string(),
        theorems: vec!["NNVerify.farkas_combine_2_le_bound".to_string()],
        anchor: KERNEL_ANCHOR_FARKAS_CONSTRUCTIVE.to_string(),
        allowed_axioms: vec![
            "propext".to_string(),
            "Classical.choice".to_string(),
            "Quot.sound".to_string(),
        ],
    };
    let e = ProofEvidence::CleanCic {
        term: vec![0x01],
        context: vec![0x02],
        lineage: ProofDigest::sha256([9u8; 32]),
        kernel_recheck: Some(recheck.clone()),
    };
    assert_eq!(e.clean_cic_kernel_recheck(), Some(&recheck));
    // A payload with a recheck has a different evidence digest than one
    // without — the directive is bound into the certificate identity.
    let bare = ProofEvidence::CleanCic {
        term: vec![0x01],
        context: vec![0x02],
        lineage: ProofDigest::sha256([9u8; 32]),
        kernel_recheck: None,
    };
    let cert_with = ProofCertificate {
        obligation: ProofId::new(0),
        prover: "p".to_string(),
        evidence: e,
    };
    let cert_without = ProofCertificate {
        obligation: ProofId::new(0),
        prover: "p".to_string(),
        evidence: bare,
    };
    assert_ne!(
        cert_with.evidence_digest(),
        cert_without.evidence_digest(),
        "recheck directive must change the evidence digest"
    );
}

#[cfg(feature = "serde")]
#[test]
fn proof_evidence_clean_cic_serde_roundtrip() {
    let e = ProofEvidence::CleanCic {
        term: vec![0xDE, 0xAD, 0xBE, 0xEF],
        context: vec![0x01, 0x02, 0x03],
        lineage: ProofDigest::sha256([4u8; 32]),
        kernel_recheck: Some(CleanCicKernelRecheck {
            module: "Crownproof.SlackCertZ".to_string(),
            theorems: vec!["NNVerify.farkas_combine_2_le_bound".to_string()],
            anchor: KERNEL_ANCHOR_FARKAS_CONSTRUCTIVE.to_string(),
            allowed_axioms: vec!["propext".to_string()],
        }),
    };
    let bytes = rmp_serde::to_vec(&e).expect("serialize CleanCic");
    let back: ProofEvidence = rmp_serde::from_slice(&bytes).expect("deserialize CleanCic");
    assert_eq!(e, back);

    let json = serde_json::to_string(&e).expect("serialize CleanCic json");
    let back_json: ProofEvidence = serde_json::from_str(&json).expect("deserialize CleanCic json");
    assert_eq!(e, back_json);
}

#[cfg(feature = "serde")]
#[test]
fn proof_status_certified_serde_roundtrip() {
    let s = ProofStatus::Certified;
    let bytes = rmp_serde::to_vec(&s).expect("serialize Certified");
    let back: ProofStatus = rmp_serde::from_slice(&bytes).expect("deserialize Certified");
    assert_eq!(s, back);

    let json = serde_json::to_string(&s).expect("serialize Certified json");
    let back_json: ProofStatus = serde_json::from_str(&json).expect("deserialize Certified json");
    assert_eq!(s, back_json);
}

#[cfg(feature = "serde")]
#[test]
fn legacy_bundle_without_new_variants_still_deserializes() {
    // Forward-compat: a bundle built only from pre-existing variants must
    // round-trip unchanged after the Certified / CleanCic additions.
    let obligation = ProofObligation::new(
        ProofId::new(3),
        ObligationKind::Precondition,
        ProofStatus::Trusted,
        "legacy obligation",
    );
    let certificate = ProofCertificate {
        obligation: ProofId::new(3),
        prover: "legacy".to_string(),
        evidence: ProofEvidence::LeanProof("theorem foo : True := trivial".to_string()),
    };
    let pre_existing_evidence = vec![
        ProofEvidence::SmtProof(vec![0xAB, 0xCD]),
        ProofEvidence::LeanProof("term".to_string()),
        ProofEvidence::KaniHarness("harness".to_string()),
        ProofEvidence::GammaCrownBound {
            epsilon: 0.5,
            verified_layers: 4,
        },
        ProofEvidence::TranslationValidation {
            rule_name: "rule".to_string(),
            smt_hash: [9u8; 32],
        },
        ProofEvidence::Trusted("audited".to_string()),
        ProofEvidence::InheritedFromCallee {
            callee: FuncId::new(2),
            obligation: ProofId::new(5),
        },
    ];
    let pre_existing_statuses = vec![
        ProofStatus::Pending,
        ProofStatus::Discharged,
        ProofStatus::Failed,
        ProofStatus::Trusted,
    ];

    let bundle = (
        obligation,
        certificate,
        pre_existing_evidence,
        pre_existing_statuses,
    );
    let bytes = rmp_serde::to_vec(&bundle).expect("serialize legacy bundle");
    let back: (
        ProofObligation,
        ProofCertificate,
        Vec<ProofEvidence>,
        Vec<ProofStatus>,
    ) = rmp_serde::from_slice(&bytes).expect("deserialize legacy bundle");
    assert_eq!(bundle, back);
}

#[test]
fn clean_cic_match_requires_nonempty_term_and_bound_lineage() {
    // This helper establishes identity only (the kernel-backed helper is the
    // Certified-tier admissibility gate). Identity still requires an exact
    // lineage digest and a non-empty proof carrier.
    let ob = ProofObligation::new(
        ProofId::new(7),
        ObligationKind::Precondition,
        ProofStatus::Certified,
        "certified obligation",
    );
    let good_lineage = clean_cic_lineage_digest(&ob);

    let with = |term: Vec<u8>, lineage: ProofDigest| ProofCertificate {
        obligation: ProofId::new(7),
        prover: "clean".to_string(),
        evidence: ProofEvidence::CleanCic {
            term,
            context: vec![1],
            lineage,
            kernel_recheck: None,
        },
    };

    // Non-empty term + bound lineage: admitted.
    assert!(obligation_has_matching_clean_cic(
        &ob,
        &[with(vec![0xCA, 0xFE], good_lineage)]
    ));
    // Empty term + bound lineage: REJECTED (the new floor).
    assert!(!obligation_has_matching_clean_cic(
        &ob,
        &[with(vec![], good_lineage)]
    ));
    // Non-empty term + wrong lineage: rejected (replay guard).
    assert!(!obligation_has_matching_clean_cic(
        &ob,
        &[with(vec![0xCA, 0xFE], ProofDigest::sha256([0u8; 32]))]
    ));
}

#[test]
fn clean_cic_lineage_binds_full_claim_with_sha256_but_not_status() {
    let obligation = ProofObligation::new(
        ProofId::new(7),
        ObligationKind::Precondition,
        ProofStatus::Pending,
        "x is nonnegative",
    )
    .with_function(crate::value::FuncId::new(3));
    let digest = clean_cic_lineage_digest(&obligation);
    assert_eq!(digest.algorithm, ProofDigestAlgorithm::Sha256);

    let mut changed = obligation.clone();
    changed.description.push('!');
    assert_ne!(clean_cic_lineage_digest(&changed), digest);

    let mut changed = obligation.clone();
    changed.function = Some(crate::value::FuncId::new(4));
    assert_ne!(clean_cic_lineage_digest(&changed), digest);

    let mut changed = obligation;
    changed.status = ProofStatus::Certified;
    assert_eq!(
        clean_cic_lineage_digest(&changed),
        digest,
        "verification progress is not claim identity"
    );
}

#[test]
fn clean_cic_lineage_binds_every_embedded_source_identity_field() {
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
    let digest = clean_cic_lineage_digest(&obligation);
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
        assert_ne!(
            clean_cic_lineage_digest(&changed),
            digest,
            "source mutation must invalidate the CleanCic lineage"
        );
    }

    let mut changed = obligation;
    changed.source = None;
    assert_ne!(clean_cic_lineage_digest(&changed), digest);
}

// ---------------------------------------------------------------------------
// v23: Module::trusted_evidence_census + proof::lineage_closed (Program CK1
// zero-`Trusted` flagship-lane gate).
// ---------------------------------------------------------------------------

/// A module with `n` obligations, each `Discharged` and certified by the
/// evidence `cert_for(i)` returns.
fn census_module(n: u32, cert_for: impl Fn(u32) -> ProofEvidence) -> crate::Module {
    let mut module = crate::Module::new("census");
    for i in 0..n {
        module.proof_obligations.push(ProofObligation::new(
            ProofId::new(i),
            ObligationKind::TranslationValidation,
            ProofStatus::Discharged,
            format!("obligation {i}"),
        ));
        module.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(i),
            prover: "test".to_string(),
            evidence: cert_for(i),
        });
    }
    module
}

#[test]
fn trusted_evidence_census_empty_for_machine_backed_module() {
    // Machine-backed evidence only (and an empty module): census is empty.
    assert!(
        crate::Module::new("empty")
            .trusted_evidence_census()
            .is_empty()
    );
    let module = census_module(3, |_| ProofEvidence::SmtProof(vec![0xAB]));
    assert!(module.trusted_evidence_census().is_empty());
}

#[test]
fn trusted_evidence_census_reports_every_trusted_certificate() {
    // Obligations 1 and 3 are faith-stamped; the census must name exactly
    // those, in table order, with their justifications.
    let module = census_module(4, |i| {
        if i % 2 == 1 {
            ProofEvidence::Trusted(format!("manual audit #{i}"))
        } else {
            ProofEvidence::SmtProof(vec![i as u8])
        }
    });
    let census = module.trusted_evidence_census();
    assert_eq!(
        census,
        vec![
            (ProofId::new(1), "manual audit #1"),
            (ProofId::new(3), "manual audit #3"),
        ]
    );
}

#[test]
fn census_and_lineage_closed_agree_on_a_trusted_rung() {
    struct TestSmtAuthority;
    impl ProofAuthorityRechecker for TestSmtAuthority {
        fn replays_authority(
            &self,
            obligation: &ProofObligation,
            certificate: &ProofCertificate,
        ) -> bool {
            certificate.obligation == obligation.id
                && matches!(certificate.evidence, ProofEvidence::SmtProof(_))
        }
    }
    // One three-rung chain (frontend -> lowering -> backend) whose middle rung
    // cites obligation 1. When obligation 1's certificate is Trusted, the
    // census is non-empty AND `lineage_closed` reports the TrustedRung gap on
    // that exact rung; when it is machine-backed, both report clean — the
    // census and the closure checker must never disagree about faith.
    let build = |middle_evidence: ProofEvidence| {
        let mut module = census_module(3, move |i| {
            if i == 1 {
                middle_evidence.clone()
            } else {
                ProofEvidence::SmtProof(vec![i as u8])
            }
        });
        let mut manifest = ProofLineageManifest::new();
        let d = |tag: &str| ProofDigest::sha256_domain("trust_ir.test.census.v2", tag.as_bytes());
        let stages = [
            (
                ProofTransformStage::Frontend,
                "frontend",
                d("src"),
                d("mid"),
            ),
            (
                ProofTransformStage::TrustIrLowering,
                "lowering",
                d("mid"),
                d("out"),
            ),
            (ProofTransformStage::Backend, "backend", d("out"), d("out")),
        ];
        for (i, (stage, name, source, target)) in stages.into_iter().enumerate() {
            let i = i as u32;
            let mut node = ProofLineageNode::new(
                ProofLineageId::new(i),
                ProofTransform::new(stage, name, "trust-ir-test", "1.0.0"),
                source,
                target,
            );
            node.obligations = vec![ProofId::new(i)];
            node.certificates = vec![module.proof_certificates[i as usize].lineage_ref()];
            if i > 0 {
                node.depends_on = vec![ProofLineageId::new(i - 1)];
            }
            module.proof_obligations[i as usize].formula = Some(node.transform_binding_formula());
            manifest.nodes.push(node);
        }
        manifest.roots = vec![ProofLineageId::new(2)];
        (module, manifest)
    };

    // Faith-stamped middle rung: census non-empty, closure reports THE rung.
    let (module, manifest) = build(ProofEvidence::Trusted("took it on faith".into()));
    let census = module.trusted_evidence_census();
    assert_eq!(census, vec![(ProofId::new(1), "took it on faith")]);
    match lineage_closed_with_authority(&module, &manifest, &TestSmtAuthority) {
        Err(LineageGap::TrustedRung {
            node,
            justification,
        }) => {
            assert_eq!(node, ProofLineageId::new(1));
            assert_eq!(justification, "took it on faith");
        }
        other => panic!("expected TrustedRung gap, got {other:?}"),
    }

    // Machine-backed middle rung: census empty, lineage closed.
    let (module, manifest) = build(ProofEvidence::SmtProof(vec![0x01]));
    assert!(module.trusted_evidence_census().is_empty());
    assert_eq!(
        lineage_closed_with_authority(&module, &manifest, &TestSmtAuthority),
        Ok(())
    );
}

/// POSITIONAL-MESSAGEPACK REGRESSION PIN, for the exact combination that broke:
/// `site: Some` with `source: None`.
///
/// `rmp_serde` serializes structs POSITIONALLY and may only skip a TRAILING
/// field. `source` carried `skip_serializing_if = "Option::is_none"`, which was
/// correct while it WAS trailing — then `site` was appended after it (v34) and
/// the attribute was not removed. A `None` source was still skipped, so the site
/// record shifted into the source slot and the obligation became undecodable.
///
/// The four-way matrix below is the real guard: the failure needs source absent
/// AND site present, so testing either field alone misses it entirely — which is
/// exactly why the existing fixtures did not catch it.
#[cfg(feature = "serde")]
#[test]
fn obligation_msgpack_survives_every_source_site_combination() {
    use crate::proof::{ObligationSite, ProofObligationSourceIdentity};
    use crate::value::{BlockId, FuncId};

    let identity = ProofObligationSourceIdentity::new("rustc.mir.assert", "sym#bb1#bounds_check");
    let site = ObligationSite::new(FuncId::new(2), BlockId::new(3), 4);

    for (want_source, want_site) in [(false, false), (true, false), (false, true), (true, true)] {
        let mut obligation = ProofObligation::new(
            ProofId::new(7),
            ObligationKind::BoundsCheck,
            ProofStatus::Pending,
            "index in bounds",
        )
        .with_function(FuncId::new(2));
        if want_source {
            obligation = obligation.with_source(identity.clone());
        }
        if want_site {
            obligation = obligation.with_site(site);
        }

        let bytes = rmp_serde::to_vec(&obligation)
            .unwrap_or_else(|e| panic!("serialize (source={want_source}, site={want_site}): {e}"));
        let back: ProofObligation = rmp_serde::from_slice(&bytes).unwrap_or_else(|e| {
            panic!(
                "DECODE FAILED (source={want_source}, site={want_site}): {e} — a non-trailing \
                    field is being skipped, shifting every later field by one slot"
            )
        });
        assert_eq!(
            back, obligation,
            "round-trip must be exact (source={want_source}, site={want_site})"
        );
        assert_eq!(back.site.is_some(), want_site, "site presence must survive");
        assert_eq!(
            back.source.is_some(),
            want_source,
            "source presence must survive"
        );
    }
}
