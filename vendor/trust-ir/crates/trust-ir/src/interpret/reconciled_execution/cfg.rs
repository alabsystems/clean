// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn actual_cfg_paths_keep_initialization_and_values_separate_at_the_join() {
    for flag in [true, false] {
        let safe = branch_module(Some(5));
        let outcome = Interpreter::with_module(&safe)
            .execute_func(FuncId::new(0), [InterpretValue::bool(flag)])
            .unwrap();
        assert_eq!(outcome.host_calls, 0);
        assert!(outcome.returns.is_empty());
    }
    let missing = branch_module(None);
    let error = Interpreter::with_module(&missing)
        .execute_func(FuncId::new(0), [InterpretValue::bool(false)])
        .unwrap_err();
    assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
    assert!(error.panic.is_none());
    let wrong = branch_module(Some(7));
    let error = Interpreter::with_module(&wrong)
        .execute_func(FuncId::new(0), [InterpretValue::bool(false)])
        .unwrap_err();
    assert_eq!(error.code, InterpretErrorCode::Panic);
    assert!(error.panic.is_some());
    for source in [&missing, &wrong] {
        assert!(
            Interpreter::with_module(source)
                .execute_func(FuncId::new(0), [InterpretValue::bool(true)])
                .is_ok()
        );
    }
}

#[test]
fn observed_cfg_refuses_before_executing_either_branch_instead_of_falling_back() {
    for false_write in [None, Some(5), Some(7)] {
        for flag in [true, false] {
            let source = branch_module(false_write);
            let mut observer = Observer::default();
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            let report = Interpreter::with_module(&source).execute_func_observed(
                FuncId::new(0),
                vec![InterpretValue::bool(flag)],
                &mut session,
            );
            assert!(
                matches!(report.exit(), ObservedExit::UnsupportedObservation {
                site: ExecutionSite::Entry(id), instruction: "multi-block observed execution"
            } if *id == FuncId::new(0))
            );
            assert_eq!(report.steps(), 0);
            assert_eq!(report.host_calls(), 0);
            assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
            report
                .retire_observed(&mut session, ExecutionSite::Entry(FuncId::new(0)))
                .unwrap();
            assert!(session.first_refusal().is_none());
            assert!(
                observer
                    .events
                    .iter()
                    .all(|event| event.phase != ExecutionPhase::Instruction)
            );
            assert!(
                observer
                    .events
                    .iter()
                    .any(|event| event.phase == ExecutionPhase::Publication)
            );
        }
    }
}
