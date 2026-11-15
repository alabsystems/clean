// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! UNRUN original-session cleanup-copy conformance; no execution/proof authority.
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop: Option<usize>,
    work: usize,
    copy: usize,
    work_cap: Option<usize>,
    copy_cap: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = (&'static str, usize);
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        let at = self.events.len();
        if self.stop == Some(at) {
            return Err(("stop", at));
        }
        self.work = self.work.checked_add(e.work).ok_or(("overflow", at))?;
        self.copy = self
            .copy
            .checked_add(e.copy_bytes)
            .ok_or(("overflow", at))?;
        if self.work_cap.is_some_and(|n| self.work > n) {
            return Err(("work", at));
        }
        if self.copy_cap.is_some_and(|n| self.copy > n) {
            return Err(("copy", at));
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Instruction(InstructionSite {
        function: FuncId::new(7),
        block: BlockId::new(9),
        instruction_index: 13,
    })
}
fn event(work: usize, copy_bytes: usize) -> ExecutionProgress {
    ExecutionProgress {
        phase: ExecutionPhase::ScratchRetirement,
        site: site(),
        work,
        copy_bytes,
    }
}
#[test]
fn legacy_step_and_poll_keep_the_complete_original_zero_copy_events() {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    s.retirement_step(site(), 7);
    s.retirement_poll(site());
    assert!(s.first_refusal().is_none());
    drop(s);
    assert_eq!(o.events, vec![event(7, 0), event(0, 0)]);
}
#[test]
fn new_record_preserves_every_supplied_phase_site_work_and_copy_field() {
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    for (work, copy) in [(0, 0), (1, 9), (9, 1), (17, 31)] {
        s.retirement_record(site(), work, copy);
    }
    assert!(s.first_refusal().is_none());
    drop(s);
    assert_eq!(
        o.events,
        vec![event(0, 0), event(1, 9), event(9, 1), event(17, 31)]
    );
}
#[test]
fn nonzero_copy_can_be_the_exact_original_first_refusal_and_never_resume_publication() {
    let mut o = Observer {
        copy_cap: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    s.retirement_record(site(), 0, 1);
    let first = (
        s.first_refusal().unwrap().progress,
        s.first_refusal().unwrap().cause,
    );
    assert_eq!(first, (event(0, 1), ("copy", 1)));
    s.retirement_record(site(), 0, 2);
    assert!(
        s.admit(ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 0,
            copy_bytes: 0
        })
        .is_err()
    );
    assert_eq!(
        (
            s.first_refusal().unwrap().progress,
            s.first_refusal().unwrap().cause
        ),
        first
    );
    drop(s);
    assert_eq!(o.events, vec![event(0, 1), event(0, 2)]);
}
#[test]
fn earlier_normal_typed_cause_survives_all_later_refused_cleanup_records() {
    let mut o = Observer {
        stop: Some(1),
        copy_cap: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let normal = ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site: site(),
        work: 2,
        copy_bytes: 3,
    };
    assert!(s.admit(normal).is_err());
    let first = (
        s.first_refusal().unwrap().progress,
        s.first_refusal().unwrap().cause,
    );
    for n in 1..=4 {
        s.retirement_record(site(), n, n);
    }
    assert_eq!(
        (
            s.first_refusal().unwrap().progress,
            s.first_refusal().unwrap().cause
        ),
        first
    );
    assert_eq!(first, (normal, ("stop", 1)));
    drop(s);
    assert_eq!(o.events.len(), 5);
}
#[test]
fn cumulative_work_and_copy_are_both_debited_across_cleanup_records_without_reset() {
    for copy in [false, true] {
        let mut o = Observer {
            work_cap: (!copy).then_some(7),
            copy_cap: copy.then_some(7),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        s.retirement_record(site(), 3, 3);
        s.retirement_record(site(), 3, 3);
        assert!(s.first_refusal().is_none());
        s.retirement_record(site(), 2, 2);
        assert_eq!(
            s.first_refusal().unwrap().cause,
            (if copy { "copy" } else { "work" }, 3)
        );
        s.retirement_record(site(), 0, 0);
        assert!(
            s.admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: site(),
                work: 0,
                copy_bytes: 0
            })
            .is_err()
        );
        drop(s);
        assert_eq!(o.events.len(), 4);
    }
}
#[test]
fn every_retirement_callback_cut_still_delivers_all_actual_records_and_keeps_first() {
    let expected: Vec<_> = (0..6).map(|n| event(n, n * 2)).collect();
    for cut in 1..=expected.len() {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        for n in 0..6 {
            s.retirement_record(site(), n, n * 2);
        }
        assert_eq!(s.first_refusal().unwrap().cause, ("stop", cut));
        assert_eq!(s.first_refusal().unwrap().progress, expected[cut - 1]);
        drop(s);
        assert_eq!(o.events, expected);
    }
}
#[test]
fn zero_fuel_and_prior_debits_are_preserved_during_copy_record_retirement() {
    let mut o = Observer {
        copy_cap: Some(3),
        ..Observer::default()
    };
    let mut opts = InterpretOptions::default();
    opts.fuel = 0;
    let mut s = ObservedSession::new(opts, &mut o);
    s.admit(ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site: site(),
        work: 1,
        copy_bytes: 2,
    })
    .unwrap();
    s.retirement_record(site(), 1, 2);
    assert_eq!(s.remaining_fuel(), 0);
    assert_eq!(s.first_refusal().unwrap().cause, ("copy", 2));
    s.retirement_poll(site());
    assert_eq!(s.remaining_fuel(), 0);
    drop(s);
    assert_eq!(o.events.len(), 3);
}
#[test]
fn legacy_and_explicit_zero_copy_routes_have_identical_firstcause_and_complete_trace() {
    let mut traces = Vec::new();
    for legacy in [true, false] {
        let mut o = Observer {
            stop: Some(2),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        for n in 0..4 {
            if legacy {
                s.retirement_step(site(), n);
            } else {
                s.retirement_record(site(), n, 0);
            }
        }
        assert_eq!(s.first_refusal().unwrap().cause, ("stop", 2));
        drop(s);
        traces.push(o.events);
    }
    assert_eq!(traces[0], traces[1]);
}
