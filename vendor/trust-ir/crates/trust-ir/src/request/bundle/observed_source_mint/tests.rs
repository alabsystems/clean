// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Source-authored UNRUN. Test fixtures simulate the explicit live-source TCB.
use super::*;
use crate::interpret::InterpretOptions;
use crate::request::{NativeEvidenceBundle, NativeRequestId};
use crate::{FuncId, Ty};
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
    ExecutionSite::Entry(FuncId::new(9839))
}
fn classify(result: &Mint) -> Result<ProofDigest, MintError> {
    result
        .as_ref()
        .map(|a| a.bundle_digest)
        .map_err(Clone::clone)
}
fn oracle(b: &NativeVerificationBundle) -> Result<ProofDigest, MintError> {
    if b.source_generation_live.0.is_some() {
        return Err(MintError::AlreadyMinted);
    }
    let mut copy = b.clone();
    SourceGenerationAuthority::mint_from_live_lowering(&mut copy).map(|a| a.bundle_digest)
}
fn observed(b: &mut NativeVerificationBundle) -> (Mint, Observer, usize) {
    let expected = oracle(b);
    let mut o = Observer::default();
    let c = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let result =
        SourceGenerationAuthority::mint_from_live_lowering_kernel_less_observed(b, &mut s, site())
            .unwrap();
    assert_eq!(classify(&result), expected);
    let end = c.get();
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(o.events.iter().all(|p| p.site == site()));
    (result, o, end)
}
fn dispose(result: Mint, s: &mut ObservedSession<'_, Observer>) {
    match result {
        Ok(a) => {
            a.retire_observed(s, site()).unwrap();
        }
        Err(e) => {
            e.retire_observed(s, site()).unwrap();
        }
    }
}
fn empty(st: &State) {
    assert!(
        st.validation.is_none()
            && st.digest.is_none()
            && st.nonce.is_none()
            && st.marker.is_none()
            && st.output.is_none()
    );
}
