// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::vec_init_then_push,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::interpret::InterpretOptions;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop_at: Option<usize>,
    cap: Option<usize>,
    work: usize,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop_at == Some(self.events.len()) {
            return Err("interior");
        }
        self.work = self.work.checked_add(event.work).ok_or("overflow")?;
        if self.cap.is_some_and(|cap| self.work > cap) {
            return Err("work");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(crate::FuncId::new(43))
}
fn mixed() -> Ty {
    Ty::Tuple(vec![
        Ty::Bool,
        Ty::Tuple(vec![Ty::Char, Ty::Ref(Box::new(Ty::U32))]),
        Ty::Handle(Box::new(HandleTy::new("name-λ".repeat(500), "runtime"))),
        Ty::Tuple(vec![
            Ty::Tuple(vec![]),
            Ty::Dialect(Box::new(DialectTy::new("space", "name", 1))),
        ]),
    ])
}
fn retire(ty: Ty) -> Observer {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    ty.retire_observed(&mut session, site()).unwrap();
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(session.first_refusal().is_none());
    assert!(observer.events.iter().all(|event| event.site == site()));
    observer
}
#[test]
fn owned_mixed_tree_and_empty_buffers_retire_before_final_publication() {
    let observed = retire(mixed());
    assert_eq!(
        observed.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    assert_eq!(
        observed
            .events
            .iter()
            .filter(|e| e.phase == ExecutionPhase::Publication)
            .count(),
        1
    );
    assert!(observed.events.iter().all(|e| e.copy_bytes == 0));
    for ty in [
        Ty::Tuple(vec![]),
        Ty::Tuple(Vec::with_capacity(17)),
        Ty::Bool,
        Ty::Error,
        Ty::Array(TyId::new(999), u64::MAX),
    ] {
        retire(ty);
    }
}
#[test]
fn spare_slot_continuations_handle_nested_one_capacity_and_wide_branches() {
    for width in 1..20 {
        let mut children = Vec::with_capacity(width);
        for index in 0..width {
            let mut branch = Ty::Bool;
            for _ in 0..index {
                let mut one = Vec::with_capacity(1);
                one.push(branch);
                branch = Ty::Tuple(one);
            }
            children.push(branch);
        }
        retire(Ty::Tuple(children));
    }
    let mut root = Ty::Tuple(vec![]);
    for _ in 0..257 {
        root = Ty::Tuple(vec![Ty::Bool, root, Ty::Tuple(vec![Ty::U8, Ty::U16])]);
    }
    let measured = retire(root);
    assert!(measured.work > 257);
}
#[test]
fn deep_owned_inline_types_do_not_reenter_recursive_type_drop() {
    let mut root = Ty::Bool;
    for i in 0..50_000 {
        root = if i % 2 == 0 {
            Ty::Ref(Box::new(root))
        } else {
            Ty::Vector(Box::new(root), 1)
        };
    }
    let measured = retire(root);
    assert!(measured.work >= 50_000);
    assert!(measured.events.len() < 400_010);
}
#[test]
fn every_actual_small_retirement_event_keeps_first_refusal_and_drains_remaining_payloads() {
    let measured = retire(mixed());
    for stop in 1..=measured.events.len() {
        let mut observer = Observer {
            stop_at: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            mixed().retire_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(session.first_refusal().unwrap().cause, "interior");
        if stop < measured.events.len() {
            assert!(observer.events.len() >= measured.events.len() - 1);
            assert!(
                observer
                    .events
                    .iter()
                    .skip(stop)
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn original_retirement_work_is_charged_even_after_an_earlier_refusal_without_new_grant() {
    let measured = retire(mixed());
    let mut observer = Observer {
        cap: Some(measured.work),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    mixed().retire_observed(&mut session, site()).unwrap();
    assert_eq!(
        mixed().retire_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "work");
    assert!(observer.work > measured.work);
}
#[test]
fn retirement_of_caller_owned_tree_after_existing_stop_preserves_the_original_site_and_cause() {
    let mut observer = Observer {
        stop_at: Some(1),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert!(
        session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Validation,
                site: site(),
                work: 1,
                copy_bytes: 0
            })
            .is_err()
    );
    assert_eq!(
        mixed().retire_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Validation
    );
    assert_eq!(session.first_refusal().unwrap().cause, "interior");
    assert!(observer.events.len() > 10);
    assert!(
        observer
            .events
            .iter()
            .skip(1)
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
