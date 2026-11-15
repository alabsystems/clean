// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
use crate::FuncId;
use crate::interpret::InterpretOptions;
mod against;
mod stops;

#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop_at: Option<usize>,
    work: usize,
    bytes: usize,
    work_limit: Option<usize>,
    byte_limit: Option<usize>,
    stop_retirement: bool,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop_at == Some(self.events.len()) {
            return Err("interior");
        }
        if self.stop_retirement && event.phase == ExecutionPhase::ScratchRetirement {
            return Err("retirement");
        }
        self.work = self.work.checked_add(event.work).ok_or("work overflow")?;
        self.bytes = self
            .bytes
            .checked_add(event.copy_bytes)
            .ok_or("bytes overflow")?;
        if self.work_limit.is_some_and(|cap| self.work > cap) {
            return Err("work");
        }
        if self.byte_limit.is_some_and(|cap| self.bytes > cap) {
            return Err("bytes");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(43))
}
fn digest(tag: u8) -> ProofDigest {
    ProofDigest::sha256([tag; 32])
}
fn node(id: u32, source: u8, target: u8) -> ProofLineageNode {
    let mut node = ProofLineageNode::new(
        ProofLineageId::new(id),
        ProofTransform::new(
            ProofTransformStage::Backend,
            "transform",
            "producer",
            "version",
        ),
        digest(source),
        digest(target),
    );
    node.obligations.push(ProofId::new(id));
    node.certificates.push(ProofCertificateRef {
        obligation: ProofId::new(id),
        prover: "prover".into(),
        evidence_digest: digest(9),
    });
    node
}
fn fixture() -> ProofLineageManifest {
    let mut middle = node(8, 1, 2);
    middle.depends_on.push(ProofLineageId::new(3));
    let mut last = node(99, 2, 3);
    last.depends_on.push(ProofLineageId::new(8));
    ProofLineageManifest {
        schema_version: ProofLineageManifest::SCHEMA_VERSION,
        nodes: vec![last, node(3, 7, 1), middle],
        roots: vec![ProofLineageId::new(99)],
    }
}
fn observed(manifest: &ProofLineageManifest) -> Vec<ProofLineageError> {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let errors = manifest
        .shape_errors_observed(&mut session, site())
        .unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(observer.events.iter().all(|event| event.site == site()));
    errors
}
fn ordinary(manifest: &ProofLineageManifest) -> Vec<ProofLineageError> {
    manifest.validate().err().unwrap_or_default()
}

#[test]
fn full_structural_check_matches_sparse_unordered_chain_without_proof_authority() {
    let manifest = fixture();
    assert!(observed(&manifest).is_empty());
    assert_eq!(observed(&manifest), ordinary(&manifest));
    // Shape validation does not make these absent module certificates replayed.
    assert!(manifest.lineage_is_closed(&[], &[]).is_err());
    assert_eq!(
        observed(&ProofLineageManifest::new()),
        ordinary(&ProofLineageManifest::new())
    );
}

#[test]
fn every_shape_error_is_retained_in_original_order_including_owned_prover_diagnostics() {
    let mut manifest = fixture();
    manifest.schema_version = 0;
    manifest.roots = vec![ProofLineageId::new(999), ProofLineageId::new(999)];
    let first = &mut manifest.nodes[0];
    first.transform.name.clear();
    first.transform.producer.clear();
    first.transform.version.clear();
    first.transform.stage = ProofTransformStage::Replay;
    first.source_module = ProofDigest::zero();
    first.target_module = ProofDigest::trust_ir_stable("legacy", b"legacy");
    first.obligations.push(first.obligations[0]);
    let certificate = first.certificates[0].clone();
    first.certificates.push(certificate.clone());
    first.certificates.push(ProofCertificateRef {
        evidence_digest: digest(10),
        ..certificate
    });
    first.certificates.push(ProofCertificateRef {
        obligation: ProofId::new(500),
        prover: "unknown".into(),
        evidence_digest: ProofDigest::trust_ir_stable("legacy", b"legacy"),
    });
    first.depends_on.extend([
        ProofLineageId::new(99),
        ProofLineageId::new(99),
        ProofLineageId::new(500),
    ]);
    let mut duplicate = manifest.nodes[1].clone();
    duplicate.obligations.clear();
    manifest.nodes.push(duplicate);
    let expected = ordinary(&manifest);
    assert!(expected.len() > 15);
    assert_eq!(observed(&manifest), expected);
}

#[test]
fn duplicate_node_ids_use_same_last_record_for_dependency_digests_and_cycle_graph() {
    let mut manifest = fixture();
    let mut duplicate = node(8, 3, 4);
    duplicate.depends_on = vec![ProofLineageId::new(99)];
    manifest.nodes.push(duplicate);
    assert_eq!(observed(&manifest), ordinary(&manifest));
    assert!(observed(&manifest).contains(&ProofLineageError::Cycle {
        node: ProofLineageId::new(8)
    }));
    manifest.nodes[0].transform.stage = ProofTransformStage::Composition;
    assert_eq!(observed(&manifest), ordinary(&manifest));
}

#[test]
fn iterative_dfs_preserves_complete_cycle_diagnostics_for_every_three_node_graph() {
    for mask in 0u16..512 {
        let mut manifest = ProofLineageManifest {
            schema_version: 2,
            nodes: (0..3).map(|id| node(id, 1, 1)).collect(),
            roots: vec![ProofLineageId::new(0)],
        };
        for (from, node) in manifest.nodes.iter_mut().enumerate() {
            for to in 0..3 {
                if mask & (1 << (from * 3 + to)) != 0 {
                    node.depends_on.push(ProofLineageId::new(to as u32));
                }
            }
        }
        assert_eq!(observed(&manifest), ordinary(&manifest), "mask {mask}");
    }
}

#[test]
fn replay_unicode_whitespace_and_digest_predicates_match_all_existing_cases() {
    for text in ["", " \u{2003}\n\t", " \u{2003}x ", "λ"] {
        for legacy in [false, true] {
            let mut manifest = fixture();
            let n = &mut manifest.nodes[0];
            n.transform.stage = ProofTransformStage::Replay;
            n.replay = Some(ProofReplayIdentity::new(text, text).with_transcript_digest(
                if legacy {
                    ProofDigest::trust_ir_stable("legacy", b"legacy")
                } else {
                    ProofDigest::zero()
                },
            ));
            assert_eq!(observed(&manifest), ordinary(&manifest));
        }
    }
}

#[test]
fn long_duplicate_prover_identity_is_compared_and_copied_inside_the_actual_validator() {
    let mut manifest = fixture();
    manifest.nodes[0].certificates[0].prover = "λ".repeat(4097);
    let cert = manifest.nodes[0].certificates[0].clone();
    manifest.nodes[0].certificates.push(cert);
    let errors = observed(&manifest);
    assert_eq!(errors, ordinary(&manifest));
    assert_eq!(errors.len(), 2);
    let mut observer = Observer {
        stop_at: Some(3),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        text_equal(&"x".repeat(4097), &"x".repeat(4097), &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(observer.events.len(), 3);
    let mut observer = Observer {
        stop_at: Some(4),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        copy_text(&"λ".repeat(4097), &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "interior");
}
