// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored source controls, UNRUN.
use super::*;
use crate::interpret::InterpretOptions;
use crate::{BlockId, FuncId, SourceBindingProvenance, SourceLoopProvenance};
use std::{cell::Cell, rc::Rc};
mod parity;
mod stops;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop: Option<usize>,
    work: usize,
    bytes: usize,
    work_cap: Option<usize>,
    byte_cap: Option<usize>,
    cleanup: Option<Rc<Cell<bool>>>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop == Some(self.events.len()) {
            return Err("original source binding stop");
        }
        if event.phase == ExecutionPhase::ScratchRetirement
            && self.cleanup.as_ref().is_some_and(|arm| arm.get())
        {
            return Err("original source binding cleanup");
        }
        self.work = self.work.checked_add(event.work).ok_or("overflow")?;
        self.bytes = self.bytes.checked_add(event.copy_bytes).ok_or("overflow")?;
        if self.work_cap.is_some_and(|cap| self.work > cap) {
            return Err("work");
        }
        if self.byte_cap.is_some_and(|cap| self.bytes > cap) {
            return Err("bytes");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(141))
}
fn digest(algorithm: ProofDigestAlgorithm, byte: u8) -> ProofDigest {
    ProofDigest {
        algorithm,
        bytes: [byte; 32],
    }
}
fn fixture() -> SourceProvenance {
    SourceProvenance::new(
        digest(ProofDigestAlgorithm::Sha256, 3),
        digest(ProofDigestAlgorithm::TrustIrStableV1, 7),
        vec![
            SourceLoopProvenance {
                source_loop_id: 0,
                hir_local_id: 12,
                header: BlockId::new(9),
                bindings: vec![
                    SourceBindingProvenance {
                        name: "λ'\n\0".into(),
                        hir_local_id: 40,
                        place: SourcePlace::FunctionParameter { index: 2 },
                    },
                    SourceBindingProvenance {
                        name: "tail".into(),
                        hir_local_id: 41,
                        place: SourcePlace::LoopParameter { index: 3 },
                    },
                ],
            },
            SourceLoopProvenance {
                source_loop_id: 1,
                hir_local_id: 13,
                header: BlockId::new(10),
                bindings: vec![],
            },
        ],
    )
}
fn run(source: &SourceProvenance) -> (bool, Observer) {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let valid = source
        .binding_digest_is_valid_observed(&mut session, site())
        .unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    (valid, observer)
}
fn parity(source: &SourceProvenance) -> bool {
    let (valid, observer) = run(source);
    assert_eq!(valid, source.binding_digest_is_valid());
    assert!(observer.events.iter().all(|e| e.site == site()));
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    valid
}
