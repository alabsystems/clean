// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::sync::atomic::{AtomicUsize, Ordering};

#[test]
fn real_store_initializes_and_overwrite_changes_the_assertion() {
    let safe = scalar_module(true, false);
    let outcome = Interpreter::with_module(&safe)
        .execute_func(FuncId::new(0), [])
        .unwrap();
    assert_eq!(outcome.host_calls, 0);
    let healthy = parity(&safe, vec![]);
    assert!(healthy.spent_work > 0 && healthy.spent_copy > 0);
    let bug = scalar_module(true, true);
    let error = Interpreter::with_module(&bug)
        .execute_func(FuncId::new(0), [])
        .unwrap_err();
    assert_eq!(error.code, InterpretErrorCode::Panic);
    assert_eq!(error.panic.as_ref().unwrap().kind, AssertKind::Unspecified);
    parity(&bug, vec![]);
}

#[test]
fn unwritten_memory_is_not_an_assertion_counterexample() {
    let source = scalar_module(false, false);
    let error = Interpreter::with_module(&source)
        .execute_func(FuncId::new(0), [])
        .unwrap_err();
    assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
    assert!(error.panic.is_none());
    parity(&source, vec![]);
}

#[test]
fn legacy_execution_and_limits_are_unchanged_without_observer() {
    let source = scalar_module(true, false);
    assert!(
        Interpreter::with_module(&source)
            .execute_func(FuncId::new(0), [])
            .is_ok()
    );
    let error = Interpreter::with_module(&source)
        .with_options(InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        })
        .execute_func(FuncId::new(0), [])
        .unwrap_err();
    assert_eq!(error.code, InterpretErrorCode::OutOfFuel);
}

#[test]
fn legacy_interpreter_remains_send_sync_and_copy() {
    fn unchanged<T: Send + Sync + Copy>() {}
    unchanged::<Interpreter<'static>>();
}

struct Host(AtomicUsize);
impl HostCalls for Host {
    fn call(
        &self,
        _: &Function,
        _: &FuncTy,
        _: &[InterpretValue],
        _: &mut HostState,
    ) -> Option<InterpretResult<Vec<InterpretValue>>> {
        self.0.fetch_add(1, Ordering::SeqCst);
        Some(Ok(Vec::new()))
    }
}

#[test]
fn bodyless_and_supplied_host_paths_remain_closed_to_observed_execution() {
    let mut source = Module::new("bodyless");
    let ty = source
        .add_func_type(FuncTy::unrecorded(vec![], vec![], false))
        .unwrap();
    source
        .functions
        .push(Function::new(FuncId::new(0), "opaque", ty, BlockId::new(0)));
    let error = Interpreter::with_module(&source)
        .execute_func(FuncId::new(0), [])
        .unwrap_err();
    assert_eq!(error.code, InterpretErrorCode::UnsupportedCall);
    assert!(error.panic.is_none());
    let host = Host(AtomicUsize::new(0));
    for supplied in [false, true] {
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let mut interpreter = Interpreter::with_module(&source);
        if supplied {
            interpreter = interpreter.with_host(&host);
        }
        let report = interpreter.execute_func_observed(FuncId::new(0), vec![], &mut session);
        let expected = if supplied {
            "host-assisted observed execution"
        } else {
            "bodyless observed entry"
        };
        assert!(
            matches!(report.exit(), ObservedExit::UnsupportedObservation { instruction, .. }
            if *instruction == expected)
        );
        assert_eq!(report.steps(), 0);
        assert_eq!(report.host_calls(), 0);
        report
            .retire_observed(&mut session, ExecutionSite::Entry(FuncId::new(0)))
            .unwrap();
        assert!(session.first_refusal().is_none());
    }
    assert_eq!(host.0.load(Ordering::SeqCst), 0);
}
