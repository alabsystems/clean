// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::cell::Cell;
use std::rc::Rc;

#[derive(Default)]
struct Cuts {
    events: Vec<ExecutionProgress>,
    cursor: Rc<Cell<usize>>,
    stop: Rc<Cell<Option<usize>>>,
}
impl ExecutionObserver for Cuts {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        self.cursor.set(self.events.len());
        if self.stop.get() == Some(self.events.len()) {
            Err("construction cut")
        } else {
            Ok(())
        }
    }
}
fn full_module() -> Module {
    let mut ids: Vec<u32> = (0..37).map(|n| n * 17).collect();
    ids.extend([0, 17, 0, u32::MAX, u32::MAX]);
    module(&ids)
}

#[test]
fn held_constructor_errors_survive_every_real_nonempty_btree_cleanup_cut() {
    let module = full_module();
    let n = ModuleFunctionCatalog::new(&module).len();
    assert_eq!(n, 38);
    for error in [
        ObservedValueError::CapacityOverflow,
        ObservedValueError::AllocationFailed,
        ObservedValueError::InvalidRange,
        ObservedValueError::UnsupportedValue,
        ObservedValueError::AdmissionRefused,
    ] {
        for cut in 1..=n + 1 {
            let mut observer = Cuts::default();
            observer.stop.set(Some(cut));
            let mut session = ObservedSession::new(
                InterpretOptions {
                    fuel: 0,
                    ..InterpretOptions::default()
                },
                &mut observer,
            );
            let entries = ModuleFunctionCatalog::new(&module).entries;
            // Explicit held typed errors, not simulated allocator failures.
            assert!(
                matches!(finish_catalog(&module, entries, Err(error), &mut session, site()),
                Err(actual) if actual == error)
            );
            let first = session.first_refusal().unwrap().progress;
            assert_eq!(session.first_refusal().unwrap().cause, "construction cut");
            assert_eq!(session.remaining_fuel(), 0);
            drop(session);
            assert_eq!(observer.events.len(), n + 1);
            assert_eq!(first, observer.events[cut - 1]);
            assert!(
                observer
                    .events
                    .iter()
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement
                        && e.site == site()
                        && e.work == 0
                        && e.copy_bytes == 0)
            );
        }
    }
    assert_eq!(module.functions.len(), 42);
}

#[test]
fn constructor_publication_refusal_withholds_and_consumes_the_complete_map() {
    let module = full_module();
    let catalog = ModuleFunctionCatalog::new(&module);
    let n = catalog.len();
    let mut observer = Cuts::default();
    observer.stop.set(Some(1));
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert!(matches!(
        finish_catalog(&module, catalog.entries, Ok(()), &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    drop(session);
    assert_eq!(observer.events.len(), n + 2);
    assert!(
        observer.events[1..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement && e.site == site())
    );
}

#[test]
fn prior_original_cause_stays_immutable_while_held_constructor_error_and_map_drain() {
    let module = full_module();
    let catalog = ModuleFunctionCatalog::new(&module);
    let n = catalog.len();
    let mut observer = Cuts::default();
    observer.stop.set(Some(1));
    let stop = observer.stop.clone();
    let cursor = observer.cursor.clone();
    let mut session = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut observer,
    );
    assert!(
        session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::ModuleLookup,
                site: site(),
                work: 1,
                copy_bytes: 0
            })
            .is_err()
    );
    let first = session.first_refusal().unwrap().progress;
    let before = cursor.get();
    stop.set(Some(before + 1));
    assert!(matches!(
        finish_catalog(
            &module,
            catalog.entries,
            Err(ObservedValueError::InvalidRange),
            &mut session,
            site()
        ),
        Err(ObservedValueError::InvalidRange)
    ));
    assert_eq!(session.first_refusal().unwrap().progress, first);
    assert_eq!(session.first_refusal().unwrap().cause, "construction cut");
    assert_eq!(session.remaining_fuel(), 0);
    drop(session);
    assert_eq!(observer.events.len(), before + n + 1);
    assert_eq!(first, observer.events[before - 1]);
    assert!(
        observer.events[before..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}

#[test]
fn healthy_constructor_completion_preserves_actual_source_and_all_duplicate_lookups() {
    let module = full_module();
    let mut observer = Cuts::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let catalog = ModuleFunctionCatalog::new_observed(&module, &mut session, site()).unwrap();
    let catalog = finish_catalog(&module, catalog.entries, Ok(()), &mut session, site()).unwrap();
    assert!(core::ptr::eq(catalog.source_module(), &module));
    assert_eq!(catalog.len(), 38);
    assert_eq!(
        catalog.ambiguous_ids().collect::<Vec<_>>(),
        vec![0, 17, u32::MAX]
    );
    for function in &module.functions[2..37] {
        assert!(core::ptr::eq(
            catalog.unique(function.id).unwrap(),
            function
        ));
    }
    assert!(session.first_refusal().is_none());
    catalog.retire_observed(&mut session, site()).unwrap();
    assert!(session.first_refusal().is_none());
}
