// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN; complete original stable bytes and selectors are oracles.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::interpret::InterpretOptions;
use crate::proof::{IslandEnvironment, SourceDefinitionRef};
use crate::value::{FuncId, ImportId, ProofId};
use std::{cell::Cell, rc::Rc};
mod custody;
mod parity;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    calls: Rc<Cell<usize>>,
    stop: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
    cleanup: Option<Rc<Cell<bool>>>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("identity stop");
        }
        if self.cleanup.as_ref().is_some_and(|a| a.get())
            && e.phase == ExecutionPhase::ScratchRetirement
        {
            return Err("cleanup");
        }
        self.work = self.work.checked_add(e.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(e.copy_bytes).ok_or("overflow")?;
        if self.work_cap.is_some_and(|n| self.work > n) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|n| self.bytes > n) {
            return Err("copy");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(9401))
}
fn digest(n: u8) -> ProofDigest {
    ProofDigest::sha256([n; 32])
}
fn certificate(evidence: ProofEvidence) -> ProofCertificate {
    ProofCertificate {
        obligation: ProofId::new(7),
        prover: "provider\0é🦀".repeat(4),
        evidence,
        assurance: None,
    }
}
fn rich() -> ProofCertificate {
    let mut binding = CertificateBinding::new(digest(1), digest(2));
    binding.origin_module = Some(digest(3));
    binding.source = Some(SourceDefinitionRef {
        decl: "decl\0é".into(),
        closure_digest: digest(4),
    });
    binding.callees = vec!["z".into(), "a".into(), "z".into()];
    binding.environment = Some(IslandEnvironment {
        declarations: vec![0xff; 2301],
        digest: digest(5),
    });
    certificate(ProofEvidence::CleanCic {
        term: vec![0xff, 0, 7],
        context: vec![0, 1],
        lineage: ProofDigest {
            algorithm: ProofDigestAlgorithm::TrustIrStableV1,
            bytes: [19; 32],
        },
        kernel_recheck: Some(CleanCicKernelRecheck {
            module: "malformed\0module".into(),
            theorems: vec!["z".into(), "a".into(), "z".into()],
            anchor: "unknown".into(),
            allowed_axioms: vec!["fake".into(), "fake".into()],
            binding: Some(Box::new(binding)),
        }),
    })
}
fn ordinary_bytes(c: &ProofCertificate) -> Vec<u8> {
    let mut bytes = Vec::new();
    super::super::write_proof_evidence_stable(&mut bytes, &c.evidence);
    bytes
}
fn run(c: &ProofCertificate) -> (Observer, usize) {
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let reference = c.lineage_ref_observed(&mut s, site()).unwrap();
    let end = calls.get();
    assert_eq!(reference, c.lineage_ref());
    reference.retire_observed(&mut s, site()).unwrap();
    assert_eq!(
        c.evidence_digest_observed(&mut s, site()).unwrap(),
        c.evidence_digest()
    );
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
    (o, end)
}
fn exact(c: &ProofCertificate) {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut state = State::default();
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    state.evidence(&c.evidence, &mut w).unwrap();
    assert_eq!(state.bytes, ordinary_bytes(c));
    state.retire(&mut w);
    assert_eq!(state.bytes.capacity() + state.prover.capacity(), 0);
    drop(w);
    drop(s);
    run(c);
}
