// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
use crate::interpret::InterpretOptions;
use crate::{BlockId, FuncId, FuncTyId, Function};

#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop_at: Option<usize>,
    work: usize,
    bytes: usize,
    work_limit: Option<usize>,
    byte_limit: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, progress: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(progress);
        if self.stop_at == Some(self.events.len()) {
            return Err("original stop");
        }
        self.work = self
            .work
            .checked_add(progress.work)
            .ok_or("work overflow")?;
        self.bytes = self
            .bytes
            .checked_add(progress.copy_bytes)
            .ok_or("byte overflow")?;
        if self.work_limit.is_some_and(|n| self.work > n) {
            return Err("original work");
        }
        if self.byte_limit.is_some_and(|n| self.bytes > n) {
            return Err("original bytes");
        }
        Ok(())
    }
}
fn module(ids: &[u32]) -> Module {
    let mut module = Module::new("observed_catalog");
    for (position, &id) in ids.iter().enumerate() {
        module.functions.push(Function::new(
            FuncId::new(id),
            format!("function_{position}"),
            FuncTyId::new(0),
            BlockId::new(0),
        ));
    }
    module
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(u32::MAX))
}

#[test]
fn unchanged_unique_sparse_and_duplicate_lookup_results() {
    let module = module(&[3, u32::MAX, 7, 3, u32::MAX]);
    let plain = ModuleFunctionCatalog::new(&module);
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let observed =
        ModuleFunctionCatalog::new_observed(&module, &mut session, site()).expect("catalog");
    assert!(core::ptr::eq(observed.source_module(), &module));
    assert_eq!(observed.len(), plain.len());
    assert_eq!(
        observed.ambiguous_ids().collect::<Vec<_>>(),
        plain.ambiguous_ids().collect::<Vec<_>>()
    );
    assert!(observed.unique(FuncId::new(3)).is_none());
    assert!(observed.unique(FuncId::new(u32::MAX)).is_none());
    assert!(core::ptr::eq(
        observed.unique(FuncId::new(7)).expect("unique"),
        &module.functions[2]
    ));
    assert!(observed.unique(FuncId::new(4)).is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
}

#[test]
fn initial_interior_and_final_stops_never_publish_a_partial_index() {
    let module = module(&[1, 2, 3]);
    for stop in 1..=module.functions.len() + 2 {
        let mut observer = Observer {
            stop_at: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert!(matches!(
            ModuleFunctionCatalog::new_observed(&module, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        let first = session.first_refusal().expect("original typed cause");
        assert_eq!(first.cause, "original stop");
        if stop > 1 && stop <= module.functions.len() + 1 {
            assert_eq!(
                first.progress.site,
                ExecutionSite::Entry(module.functions[stop - 2].id)
            );
            assert!(
                first.progress.copy_bytes > 0,
                "before possible B-tree allocation"
            );
        }
        assert!(ModuleFunctionCatalog::new_observed(&module, &mut session, site()).is_err());
        assert_eq!(
            observer
                .events
                .iter()
                .filter(|event| event.phase != ExecutionPhase::ScratchRetirement)
                .count(),
            stop,
            "refused session only observes already-prepaid retirement"
        );
    }
}

#[test]
fn scratch_refuses_before_index_construction() {
    let module = module(&[1, 2]);
    let mut observer = Observer {
        byte_limit: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert!(matches!(
        ModuleFunctionCatalog::new_observed(&module, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(
        session.first_refusal().expect("cause").cause,
        "original bytes"
    );
    assert_eq!(observer.events.len(), 1);
    assert_eq!(
        observer.events[0].copy_bytes,
        size_of::<ModuleFunctionCatalog<'_>>()
    );
}

#[test]
fn repeated_indexes_share_cumulative_original_work() {
    let module = module(&[1, 2]);
    let mut measured = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
    ModuleFunctionCatalog::new_observed(&module, &mut session, site()).expect("measurement");
    let cost = measured.work;
    let mut observer = Observer {
        work_limit: Some(cost),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    ModuleFunctionCatalog::new_observed(&module, &mut session, site()).expect("first index");
    assert!(ModuleFunctionCatalog::new_observed(&module, &mut session, site()).is_err());
    assert_eq!(
        session.first_refusal().expect("cause").cause,
        "original work"
    );
    assert!(observer.work > cost);
}

#[test]
fn catalog_and_digest_constituents_cannot_renew_the_shared_original_allowance() {
    let module = module(&[1, 2]);
    let mut measured = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
    ModuleFunctionCatalog::new_observed(&module, &mut session, site()).expect("catalog baseline");
    let cost = measured.work;
    let mut observer = Observer {
        work_limit: Some(cost + 50),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    ModuleFunctionCatalog::new_observed(&module, &mut session, site()).expect("catalog");
    assert!(
        crate::ProofDigest::sha256_domain_observed("domain", &[9; 2049], &mut session, site())
            .is_err()
    );
    let first = session.first_refusal().expect("same original stop");
    assert_eq!(first.cause, "original work");
    assert_eq!(first.progress.phase, ExecutionPhase::CanonicalDigest);
    assert!(ModuleFunctionCatalog::new_observed(&module, &mut session, site()).is_err());
}

#[test]
fn affordable_header_cannot_enter_an_unaffordable_first_btree_insertion() {
    let module = module(&[1]);
    let mut observer = Observer {
        byte_limit: Some(size_of::<ModuleFunctionCatalog<'_>>()),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert!(ModuleFunctionCatalog::new_observed(&module, &mut session, site()).is_err());
    let first = session.first_refusal().expect("original insertion refusal");
    assert_eq!(first.cause, "original bytes");
    assert_eq!(
        first.progress.site,
        ExecutionSite::Entry(module.functions[0].id)
    );
    assert!(first.progress.copy_bytes > size_of::<ModuleFunctionCatalog<'_>>());
    assert!(
        observer
            .events
            .iter()
            .any(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
}

#[test]
fn repeated_indexes_share_cumulative_original_copy_allowance() {
    let module = module(&[1, 2]);
    let mut measured = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
    ModuleFunctionCatalog::new_observed(&module, &mut session, site()).expect("baseline");
    let cost = measured.bytes;
    let mut observer = Observer {
        byte_limit: Some(cost),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    ModuleFunctionCatalog::new_observed(&module, &mut session, site()).expect("first");
    assert!(ModuleFunctionCatalog::new_observed(&module, &mut session, site()).is_err());
    assert_eq!(
        session
            .first_refusal()
            .expect("original copy refusal")
            .cause,
        "original bytes"
    );
    assert!(observer.bytes > cost);
}

mod error_precedence;
