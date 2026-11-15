// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::interpret::InterpretOptions;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    retirement: bool,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, p: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(p);
        if self.retirement && p.phase == ExecutionPhase::ScratchRetirement {
            Err("cleanup")
        } else {
            Ok(())
        }
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(crate::FuncId::new(318))
}
#[test]
fn held_display_local_errors_keep_priority_through_actual_owned_string_cleanup_refusal() {
    for error in [
        ObservedValueError::CapacityOverflow,
        ObservedValueError::AllocationFailed,
        ObservedValueError::InvalidRange,
    ] {
        let mut o = Observer {
            retirement: true,
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        let mut state = State::default();
        let ty = Ty::handle("full λ", "runtime::🦀");
        state.walk(&ty, &mut work).unwrap();
        assert!(!state.output.is_empty());
        assert_eq!(state.finish(Err(error), &mut work), Err(error));
        assert_eq!(s.first_refusal().unwrap().cause, "cleanup");
        drop(s);
        let first = o
            .events
            .iter()
            .position(|p| p.phase == ExecutionPhase::ScratchRetirement)
            .unwrap();
        assert!(
            o.events[first..]
                .iter()
                .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn a_healthy_complete_display_is_withheld_when_its_actual_scratch_cleanup_refuses() {
    let mut o = Observer {
        retirement: true,
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    let ty = Ty::Tuple(vec![Ty::I64, Ty::handle("H", "r")]);
    state.walk(&ty, &mut work).unwrap();
    assert!(!state.output.is_empty());
    assert_eq!(
        state.finish(Ok(()), &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "cleanup");
}
#[test]
fn a_healthy_actual_display_keeps_whole_ordinary_text_and_existing_publication_fields() {
    let ty = Ty::Tuple(vec![
        Ty::handle("名é🦀", "runtime::H"),
        Ty::Ref(Box::new(Ty::I64)),
    ]);
    let expected = ty.to_string();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let text = ty.display_observed(&mut s, site()).unwrap();
    assert_eq!(text, expected);
    drop(s);
    assert_eq!(
        *o.events.last().unwrap(),
        ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 1,
            copy_bytes: size_of::<String>()
        }
    );
}
#[test]
fn existing_sticky_cause_stays_separate_from_the_held_typed_display_error() {
    let mut o = Observer {
        retirement: true,
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    s.retirement_step(site(), 7);
    let cause = s.first_refusal().unwrap().progress;
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    state.output = "already owned partial text λ".into();
    assert_eq!(
        state.finish(Err(ObservedValueError::InvalidRange), &mut work),
        Err(ObservedValueError::InvalidRange)
    );
    assert_eq!(s.first_refusal().unwrap().progress, cause);
    assert_eq!(s.first_refusal().unwrap().cause, "cleanup");
}
