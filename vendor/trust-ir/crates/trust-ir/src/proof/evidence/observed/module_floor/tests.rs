// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Source-authored UNRUN. Ordinary oracle ALWAYS rejects kernel authority.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::interpret::InterpretOptions;
use crate::proof::{
    CleanCicModuleProofAuthority, ModuleCleanCicRechecker, ModuleProofAuthority, ObligationKind,
    ProofStatus,
};
use crate::value::{FuncTyId, ProofId};
use crate::{BlockId, FuncId, Function};
use std::{cell::Cell, rc::Rc};
mod boundaries;
mod parity;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    calls: Rc<Cell<usize>>,
    stop: Option<usize>,
    arm: Option<Rc<Cell<bool>>>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, p: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(p);
        self.calls.set(self.events.len());
        if self.stop == Some(self.events.len()) {
            return Err("interior");
        }
        if self.arm.as_ref().is_some_and(|a| a.get()) {
            return Err("interrupt");
        }
        self.work = self.work.checked_add(p.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(p.copy_bytes).ok_or("overflow")?;
        if self.work_cap.is_some_and(|n| self.work > n) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|n| self.bytes > n) {
            return Err("copy");
        }
        Ok(())
    }
}
struct CountingRejector(Cell<usize>);
impl ModuleCleanCicRechecker for CountingRejector {
    fn kernel_rechecks_clean_cic_in(
        &self,
        _m: &Module,
        _o: &ProofObligation,
        _c: &ProofCertificate,
    ) -> bool {
        self.0.set(self.0.get() + 1);
        false
    }
}
fn oracle(m: &Module, row: &ProofObligation, c: &ProofCertificate) -> bool {
    let kernel = CountingRejector(Cell::new(0));
    let authority = CleanCicModuleProofAuthority { clean_cic: &kernel };
    // We observe the actual ordinary call floor, never an accepting mock:
    // this existing ordinary authority is ALWAYS false in the oracle.
    assert!(!ModuleProofAuthority::replays_authority(
        &authority, m, row, c
    ));
    kernel.0.get() == 1
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(9881))
}
fn fixture() -> (Module, ProofObligation, ProofCertificate) {
    let mut m = Module::new("floor");
    m.functions.push(Function::new(
        FuncId::new(77),
        "owner λ\0",
        FuncTyId::new(0),
        BlockId::new(0),
    ));
    let mut row = ProofObligation::new(
        ProofId::new(9),
        ObligationKind::Precondition,
        ProofStatus::Certified,
        "raw",
    );
    row.function = Some(FuncId::new(77));
    let lineage = crate::proof::clean_cic_lineage_digest_v8(
        &row,
        &crate::proof::module_symbol_resolver(&m),
        None,
    )
    .unwrap();
    let c = ProofCertificate {
        obligation: row.id,
        prover: "raw prover".into(),
        evidence: ProofEvidence::CleanCic {
            term: vec![255],
            context: vec![],
            lineage,
            kernel_recheck: None,
        },
        assurance: None,
    };
    (m, row, c)
}
fn observed(m: &Module, row: &ProofObligation, c: &ProofCertificate) -> (bool, Observer, usize) {
    let expected = oracle(m, row, c);
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let eligible = c
        .clean_cic_module_identity_floor_observed(m, row, &mut s, site())
        .unwrap();
    assert_eq!(eligible, expected);
    let end = calls.get();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|p| p.site == site()));
    (eligible, o, end)
}
