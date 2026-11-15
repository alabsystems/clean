// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Source-authored UNRUN: the actual shared diagnostics finisher.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::FuncId;
use crate::interpret::InterpretOptions;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    retirement_stop: bool,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, p: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(p);
        if self.retirement_stop && p.phase == ExecutionPhase::ScratchRetirement {
            Err("retirement")
        } else {
            Ok(())
        }
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(9873))
}
fn state() -> Checking<'static> {
    let mut st = Checking::default();
    st.roots.insert(ProofLineageId::new(4));
    st.starts = vec![ProofLineageId::new(4)];
    st.stack = vec![Frame::Enter(ProofLineageId::new(4))];
    st.errors = Vec::with_capacity(23);
    st.errors.push(ProofLineageError::EmptyRoots);
    st.pending_error = Some(ProofLineageError::EmptyRoots);
    st
}
fn empty(st: &Checking<'_>) {
    assert!(
        st.nodes.is_empty()
            && st.roots.is_empty()
            && st.dependencies.is_empty()
            && st.obligations.is_empty()
            && st.marks.is_empty()
    );
    assert_eq!(
        st.certificates.capacity()
            + st.starts.capacity()
            + st.stack.capacity()
            + st.errors.capacity(),
        0
    );
    assert!(st.pending_error.is_none());
}
#[test]
fn actual_lineage_finisher_preserves_typed_local_error_after_full_scratch_cleanup_stop() {
    let mut st = state();
    let mut o = Observer {
        retirement_stop: true,
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        finish_diagnostics(
            &mut st,
            Err(ObservedValueError::InvalidRange),
            &mut s,
            site()
        ),
        Err(ObservedValueError::InvalidRange)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "retirement");
    empty(&st);
    drop(s);
    assert!(
        o.events
            .iter()
            .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn actual_capacity_error_is_not_replaced_and_all_pending_error_capacity_is_consumed() {
    let mut st = state();
    let mut o = Observer {
        retirement_stop: true,
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        finish_diagnostics(
            &mut st,
            Err(ObservedValueError::CapacityOverflow),
            &mut s,
            site()
        ),
        Err(ObservedValueError::CapacityOverflow)
    );
    empty(&st);
    assert!(s.first_refusal().is_some());
}
#[test]
fn healthy_lineage_with_cleanup_only_stop_still_returns_operational_refusal() {
    let mut st = state();
    let mut o = Observer {
        retirement_stop: true,
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        finish_diagnostics(&mut st, Ok(()), &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    empty(&st);
}
#[test]
fn public_lineage_shape_and_whole_against_success_semantics_remain_original() {
    let m = ProofLineageManifest::default();
    let expected = m.validate().err().unwrap_or_default();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(m.shape_errors_observed(&mut s, site()).unwrap(), expected);
    assert_eq!(
        m.against_errors_observed(&[], &[], &mut s, site()).unwrap(),
        m.validate_against(&[], &[]).err().unwrap_or_default()
    );
    assert!(s.first_refusal().is_none());
}
