// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
use crate::interpret::InterpretOptions;
use crate::proof::{IslandEnvironment, SourceDefinitionRef};
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
    fn admit(&mut self, event: ExecutionProgress) -> core::result::Result<(), Self::Refusal> {
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
            .ok_or("byte overflow")?;
        if self.work_limit.is_some_and(|n| self.work > n) {
            return Err("work");
        }
        if self.byte_limit.is_some_and(|n| self.bytes > n) {
            return Err("bytes");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(71))
}
fn certificate(evidence: ProofEvidence) -> ProofCertificate {
    ProofCertificate {
        obligation: ProofId::new(9),
        prover: "prover λ".into(),
        evidence,
        assurance: None,
    }
}
fn recheck() -> CleanCicKernelRecheck {
    let mut binding =
        CertificateBinding::new(ProofDigest::sha256([1; 32]), ProofDigest::sha256([2; 32]));
    binding.origin_module = Some(ProofDigest::sha256([3; 32]));
    binding.source = Some(SourceDefinitionRef {
        decl: "source λ".into(),
        closure_digest: ProofDigest::sha256([4; 32]),
    });
    binding.callees = vec!["a".into(), "b".repeat(2049)];
    binding.environment = Some(IslandEnvironment {
        declarations: vec![17; 4097],
        digest: ProofDigest::sha256([5; 32]),
    });
    CleanCicKernelRecheck {
        module: "module".into(),
        theorems: vec!["theorem".into(), "other".into()],
        anchor: "anchor".into(),
        allowed_axioms: vec!["axiom".into()],
        binding: Some(Box::new(binding)),
    }
}
fn cases() -> Vec<ProofEvidence> {
    vec![
        ProofEvidence::SmtProof(vec![0; 4097]),
        ProofEvidence::LeanProof("λ".repeat(2049)),
        ProofEvidence::KaniHarness("harness".into()),
        ProofEvidence::GammaCrownBound {
            epsilon: f64::from_bits(0x7ff8000000000042),
            verified_layers: u32::MAX,
        },
        ProofEvidence::TranslationValidation {
            rule_name: "rule".into(),
            smt_hash: [19; 32],
        },
        ProofEvidence::Trusted("unreplayed identity only".into()),
        ProofEvidence::InheritedFromCallee {
            callee: FuncId::new(7),
            obligation: ProofId::new(9),
            external: None,
        },
        ProofEvidence::InheritedFromCallee {
            callee: FuncId::new(7),
            obligation: ProofId::new(9),
            external: Some(crate::ExternRef {
                module: ImportId::new(3),
                symbol: "external λ".into(),
                obligation: Some(ProofId::new(0)),
            }),
        },
        ProofEvidence::CleanCic {
            term: vec![21; 4097],
            context: vec![22; 1025],
            lineage: ProofDigest::sha256([7; 32]),
            kernel_recheck: None,
        },
        ProofEvidence::CleanCic {
            term: vec![],
            context: vec![],
            lineage: ProofDigest::sha256([7; 32]),
            kernel_recheck: Some(recheck()),
        },
    ]
}
fn measured(c: &ProofCertificate) -> Observer {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        c.evidence_digest_observed(&mut session, site()).unwrap(),
        c.evidence_digest()
    );
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    observer
}
#[test]
fn every_evidence_variant_and_complete_bound_island_preimage_matches_ordinary_identity() {
    for e in cases() {
        let c = certificate(e);
        let observer = measured(&c);
        assert!(observer.events.iter().all(|event| event.site == site()));
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            c.stable_digest_observed(&mut session, site()).unwrap(),
            c.stable_digest()
        );
    }
}
#[test]
fn absent_binding_and_island_tails_keep_exact_legacy_preimages() {
    let mut r = recheck();
    r.binding.as_mut().unwrap().environment = None;
    for binding in [None, r.binding.clone()] {
        r.binding = binding;
        measured(&certificate(ProofEvidence::CleanCic {
            term: vec![1],
            context: vec![2],
            lineage: ProofDigest::sha256([7; 32]),
            kernel_recheck: Some(r.clone()),
        }));
    }
}
#[test]
fn float_bits_and_external_presence_are_identity_bearing_without_replay() {
    let mut seen = Vec::new();
    for bits in [0, 1u64 << 63, 0x7ff8000000000001, 0x7ff8000000000002] {
        let c = certificate(ProofEvidence::GammaCrownBound {
            epsilon: f64::from_bits(bits),
            verified_layers: 1,
        });
        measured(&c);
        let digest = c.evidence_digest();
        assert!(!seen.contains(&digest));
        seen.push(digest);
    }
    let mut seen = Vec::new();
    for obligation in [None, Some(ProofId::new(0)), Some(ProofId::new(9))] {
        let c = certificate(ProofEvidence::InheritedFromCallee {
            callee: FuncId::new(7),
            obligation: ProofId::new(9),
            external: Some(crate::ExternRef {
                module: ImportId::new(3),
                symbol: "external".into(),
                obligation,
            }),
        });
        measured(&c);
        let digest = c.evidence_digest();
        assert!(!seen.contains(&digest));
        seen.push(digest);
    }
}
#[test]
fn every_actual_small_evidence_serialization_digest_and_retirement_stop_is_terminal() {
    let c = certificate(ProofEvidence::SmtProof(vec![1, 2, 3]));
    let measured = measured(&c);
    for stop in 1..=measured.events.len() {
        let mut observer = Observer {
            stop_at: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            c.evidence_digest_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().cause, "interior");
        assert_eq!(
            c.evidence_digest_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(
            observer
                .events
                .iter()
                .skip(stop)
                .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn evidence_work_and_requested_storage_accumulate_without_new_session() {
    let c = certificate(cases().pop().unwrap());
    let measured = measured(&c);
    for memory in [false, true] {
        let mut observer = if memory {
            Observer {
                byte_limit: Some(measured.bytes),
                ..Observer::default()
            }
        } else {
            Observer {
                work_limit: Some(measured.work),
                ..Observer::default()
            }
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            c.evidence_digest_observed(&mut session, site()).unwrap(),
            c.evidence_digest()
        );
        assert_eq!(
            c.evidence_digest_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
    }
}
#[test]
fn evidence_retirement_and_first_variable_storage_refusal_publish_no_digest() {
    for mut observer in [
        Observer {
            stop_retirement: true,
            ..Observer::default()
        },
        Observer {
            byte_limit: Some(0),
            ..Observer::default()
        },
    ] {
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            certificate(ProofEvidence::SmtProof(vec![1]))
                .evidence_digest_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
    }
}
