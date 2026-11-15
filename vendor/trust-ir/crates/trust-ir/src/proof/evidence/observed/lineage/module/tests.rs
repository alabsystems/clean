// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Source-authored UNRUN. Actual core module resolver oracle, DATA only.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::interpret::InterpretOptions;
use crate::proof::{
    ClauseBinding, ClausePlace, ClauseSort, CleanCicKernelRecheck, ObligationKind, ProofFormula,
    ProofObligationSourceIdentity, ProofObligationSourceRange, ProofStatus,
    PublicObligationIdentity, SpecObligationRef,
};
use crate::value::{FuncId, FuncTyId, ProofId, ValueId};
use crate::{BlockId, Function};
use std::{cell::Cell, rc::Rc};
mod custody;
mod fixtures;
mod parity;
mod stops;
use fixtures::*;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    calls: Rc<Cell<usize>>,
    stop: Option<usize>,
    arm: Option<Rc<Cell<bool>>>,
    retirement_stop: bool,
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
        if self.retirement_stop && p.phase == ExecutionPhase::ScratchRetirement {
            return Err("retirement");
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
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(9851))
}
fn original(
    m: &Module,
    row: &ProofObligation,
    binding: Option<&CertificateBinding>,
) -> Option<ProofDigest> {
    crate::proof::clean_cic_lineage_digest_v8(
        row,
        &crate::proof::module_symbol_resolver(m),
        binding,
    )
}
fn content(m: &Module, row: &ProofObligation) -> Option<Vec<u8>> {
    crate::proof::clean_cic_lineage_content_v8(row, &crate::proof::module_symbol_resolver(m))
}
fn observed(
    m: &Module,
    row: &ProofObligation,
    binding: Option<&CertificateBinding>,
) -> (Option<ProofDigest>, Observer, usize) {
    let mut o = Observer::default();
    let c = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let digest = row
        .clean_cic_lineage_digest_v8_in_module_observed(m, binding, &mut s, site())
        .unwrap();
    assert_eq!(digest, original(m, row, binding));
    let end = c.get();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    drop(s);
    assert!(o.events.iter().all(|p| p.site == site()));
    (digest, o, end)
}
fn exact_evidence(m: &Module, row: &ProofObligation, e: &ProofEvidence) -> (bool, bool) {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let binds = e
        .clean_cic_lineage_binds_in_module_observed(row, m, &mut s, site())
        .unwrap();
    let v8 = e
        .clean_cic_lineage_is_v8_in_module_observed(row, m, &mut s, site())
        .unwrap();
    assert_eq!(
        binds,
        crate::proof::clean_cic_lineage_binds(row, e, &crate::proof::module_symbol_resolver(m))
    );
    assert_eq!(
        v8,
        crate::proof::clean_cic_lineage_is_v8(row, e, &crate::proof::module_symbol_resolver(m))
    );
    (binds, v8)
}
fn empty(st: &State) {
    assert_eq!(st.bytes.capacity(), 0);
    assert_eq!(st.prover.capacity(), 0);
    assert!(st.reference.is_none());
}
