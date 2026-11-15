// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
use crate::interpret::InterpretOptions;
use crate::request::{NativeRequestId, NativeVerifierSuite as Suite};
use crate::{FuncId, ProofId, ProofLineageId, ProofStatus};
mod custody;
mod fixtures;
mod parity;
mod stops;
use fixtures::*;
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
    fn admit(&mut self, p: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(p);
        self.work = self.work.checked_add(p.work).ok_or("work overflow")?;
        self.bytes = self
            .bytes
            .checked_add(p.copy_bytes)
            .ok_or("copy overflow")?;
        if self.stop_at == Some(self.events.len()) {
            return Err("interior");
        }
        if self.work_limit.is_some_and(|n| self.work > n) {
            return Err("work");
        }
        if self.byte_limit.is_some_and(|n| self.bytes > n) {
            return Err("copy");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(9701))
}
fn run(rows: Vec<E>, observer: &mut Observer) -> R {
    let options = InterpretOptions {
        fuel: 0,
        ..InterpretOptions::default()
    };
    let mut session = ObservedSession::new(options, observer);
    let result = retire_native_bundle_errors_observed(rows, &mut session, site());
    assert_eq!(session.remaining_fuel(), 0);
    result
}
fn capture(rows: Vec<E>) -> Observer {
    let mut observer = Observer::default();
    run(rows, &mut observer).unwrap();
    assert_eq!(
        observer.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    assert_eq!(observer.events.last().unwrap().work, 0);
    assert_eq!(observer.events.last().unwrap().copy_bytes, 0);
    assert!(observer.events.iter().all(|p| p.site == site()));
    observer
}
