// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Reconcile useful old boolean-wrapper scenarios with current reference data.
//!
//! These tests neither reintroduce the unpublished wrapper nor claim source,
//! replay, proof or host-callback authority for an interpreter outcome.

use super::*;

mod cfg;
mod fixtures;
mod memory;
mod scalar;
mod stops;

use fixtures::{branch_module, bulk_module, scalar_module};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Cause {
    Cut(usize),
    Budget,
}

#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    cut: Option<usize>,
    work_limit: Option<usize>,
    copy_limit: Option<usize>,
    spent_work: usize,
    spent_copy: usize,
}

impl ExecutionObserver for Observer {
    type Refusal = Cause;

    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Cause> {
        self.events.push(event);
        if self.cut == Some(self.events.len()) {
            // Deliberately not sticky: the actual original session must latch it.
            return Err(Cause::Cut(self.events.len()));
        }
        let work = self
            .spent_work
            .checked_add(event.work)
            .ok_or(Cause::Budget)?;
        let copy = self
            .spent_copy
            .checked_add(event.copy_bytes)
            .ok_or(Cause::Budget)?;
        if self.work_limit.is_some_and(|limit| work > limit)
            || self.copy_limit.is_some_and(|limit| copy > limit)
        {
            return Err(Cause::Budget);
        }
        self.spent_work = work;
        self.spent_copy = copy;
        Ok(())
    }
}

fn assert_data(expected: &InterpretResult<InterpretOutcome>, report: &ObservedReport) {
    assert_eq!(report.host_calls(), 0);
    match (expected, report.exit()) {
        (Ok(expected), ObservedExit::Returned(actual)) => assert_eq!(actual, expected),
        (Err(expected), ObservedExit::ExecutedError { error, .. }) => assert_eq!(error, expected),
        _ => panic!(
            "ordinary/observed data differ: {expected:?}; {:?}",
            report.exit()
        ),
    }
}

fn parity(module: &Module, arguments: Vec<InterpretValue>) -> Observer {
    let interpreter = Interpreter::with_module(module);
    let expected = interpreter.execute_func(FuncId::new(0), arguments.clone());
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let report = interpreter.execute_func_observed(FuncId::new(0), arguments, &mut session);
    assert_data(&expected, &report);
    assert_eq!(
        session.remaining_fuel(),
        InterpretOptions::default().fuel - report.steps()
    );
    report
        .retire_observed(&mut session, ExecutionSite::Entry(FuncId::new(0)))
        .unwrap();
    assert!(session.first_refusal().is_none());
    observer
}
