// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::interpret::InterpretOptions;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    retirement: bool,
    publication: bool,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, p: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(p);
        if self.retirement && p.phase == ExecutionPhase::ScratchRetirement {
            Err("cleanup")
        } else if self.publication && p.phase == ExecutionPhase::Publication {
            Err("fence")
        } else {
            Ok(())
        }
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(crate::FuncId::new(317))
}
#[test]
fn held_equality_local_errors_survive_later_actual_owned_scratch_cleanup_refusal() {
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
        let mut rows = Vec::new();
        let left = Ty::I64;
        let right = Ty::I64;
        push(&mut rows, Task::Pair(&left, &right), &mut work).unwrap();
        let held = Err(error);
        let actual = finish_types(held, rows, &mut work);
        assert_eq!(actual, Err(error));
        assert_eq!(finish_equality(actual, &mut work), Err(error));
        assert_eq!(s.first_refusal().unwrap().cause, "cleanup");
        drop(s);
        assert!(
            o.events
                .iter()
                .skip_while(|p| p.phase != ExecutionPhase::ScratchRetirement)
                .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn held_equality_local_errors_survive_a_later_original_terminal_fence_refusal() {
    for error in [
        ObservedValueError::CapacityOverflow,
        ObservedValueError::AllocationFailed,
        ObservedValueError::InvalidRange,
    ] {
        let mut o = Observer {
            publication: true,
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(finish_equality(Err(error), &mut work), Err(error));
        assert_eq!(s.first_refusal().unwrap().cause, "fence");
        drop(s);
        assert_eq!(
            o.events,
            vec![ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: site(),
                work: 0,
                copy_bytes: 0
            }]
        );
    }
}
#[test]
fn healthy_false_stays_withheld_after_cleanup_refusal_and_first_cause_is_unchanged() {
    let mut o = Observer {
        retirement: true,
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    work.retire(Vec::<usize>::new());
    assert_eq!(
        finish_equality(Ok(false), &mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "cleanup");
    drop(s);
    assert!(
        o.events
            .iter()
            .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn both_healthy_booleans_keep_the_exact_existing_terminal_zero_zero_publication() {
    for equal in [false, true] {
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(finish_equality(Ok(equal), &mut work).unwrap(), equal);
        drop(s);
        assert_eq!(
            o.events,
            vec![ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: site(),
                work: 0,
                copy_bytes: 0
            }]
        );
    }
}
