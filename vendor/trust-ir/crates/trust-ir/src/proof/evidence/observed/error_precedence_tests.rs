//! Actual public-selector completion/error controls, authored UNRUN.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::interpret::InterpretOptions;
use crate::value::ProofId;
use std::{cell::Cell, rc::Rc};
#[derive(Default)]
struct Observer {
    arm: Rc<Cell<bool>>,
    calls: Rc<Cell<usize>>,
    events: Vec<ExecutionProgress>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, p: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(p);
        self.calls.set(self.events.len());
        if self.arm.get() && p.phase == ExecutionPhase::ScratchRetirement {
            Err("later core cleanup")
        } else {
            Ok(())
        }
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(crate::FuncId::new(711))
}
fn cert() -> ProofCertificate {
    ProofCertificate {
        obligation: ProofId::new(7),
        prover: "complete λ🙂 prover".repeat(95),
        evidence: ProofEvidence::SmtProof(vec![3; 2300]),
        assurance: None,
    }
}
fn prepared(c: &ProofCertificate, w: &mut Work<'_, '_, Observer>) -> State {
    let mut state = State::default();
    state.reference(c, w).unwrap();
    w.text("partial extra prover", &mut state.prover).unwrap();
    assert!(!state.bytes.is_empty() && state.reference.is_some() && !state.prover.is_empty());
    state
}
#[test]
fn held_allocation_capacity_and_range_errors_survive_actual_reference_finish_cleanup() {
    let c = cert();
    for error in [
        ObservedValueError::CapacityOverflow,
        ObservedValueError::AllocationFailed,
        ObservedValueError::InvalidRange,
    ] {
        let mut o = Observer::default();
        let arm = o.arm.clone();
        let calls = o.calls.clone();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = prepared(&c, &mut w);
        let begin = calls.get();
        arm.set(true);
        assert_eq!(state.finish_reference(Err(error), &mut w), Err(error));
        assert!(state.reference.is_none());
        assert_eq!(state.bytes.capacity() + state.prover.capacity(), 0);
        let first = w.session.first_refusal().unwrap();
        assert_eq!(first.cause, "later core cleanup");
        assert_eq!(first.progress.site, site());
        drop(w);
        drop(s);
        assert!(o.events.iter().all(|p| p.site == site()));
        assert!(!o.events[begin..].is_empty());
        assert!(
            o.events[begin..]
                .iter()
                .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn healthy_whole_reference_is_withheld_after_nonempty_preimage_cleanup_refuses() {
    let c = cert();
    let mut o = Observer::default();
    let arm = o.arm.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = prepared(&c, &mut w);
    arm.set(true);
    assert_eq!(
        state.finish_reference(Ok(()), &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.reference.is_none());
    assert_eq!(state.bytes.capacity() + state.prover.capacity(), 0);
    let first = w.session.first_refusal().unwrap();
    let saved = (first.progress, first.cause);
    assert!(w.publication().is_err());
    let first = w.session.first_refusal().unwrap();
    assert_eq!((first.progress, first.cause), saved);
}
#[test]
fn actual_healthy_completion_keeps_old_whole_identity_and_caller_retirement_receipts() {
    let c = cert();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.reference(&c, &mut w).unwrap();
    let out = state.finish_reference(Ok(()), &mut w).unwrap();
    assert_eq!(out, c.lineage_ref());
    assert!(state.reference.is_none());
    assert_eq!(state.bytes.capacity() + state.prover.capacity(), 0);
    drop(w);
    out.retire_observed(&mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
    drop(s);
    assert_eq!(
        o.events.last(),
        Some(&ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 0,
            copy_bytes: 0
        })
    );
}
#[test]
fn earlier_original_cause_is_immutable_while_local_error_and_full_state_are_preserved() {
    let c = cert();
    let mut o = Observer::default();
    let arm = o.arm.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = prepared(&c, &mut w);
    arm.set(true);
    w.step(37);
    let first = w.session.first_refusal().unwrap();
    let saved = (first.progress, first.cause);
    assert_eq!(
        state.finish_reference(Err(ObservedValueError::CapacityOverflow), &mut w),
        Err(ObservedValueError::CapacityOverflow)
    );
    let first = w.session.first_refusal().unwrap();
    assert_eq!((first.progress, first.cause), saved);
    assert!(state.reference.is_none());
    assert_eq!(state.bytes.capacity() + state.prover.capacity(), 0);
}
