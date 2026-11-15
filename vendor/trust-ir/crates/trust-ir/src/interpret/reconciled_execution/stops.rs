// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn every_actual_bulk_callback_cut_keeps_first_cause_and_retires_held_data() {
    let source = bulk_module(true, 2);
    let baseline = parity(&source, vec![]);
    let publication = baseline
        .events
        .iter()
        .position(|event| event.phase == ExecutionPhase::Publication)
        .unwrap();
    let expected = Interpreter::with_module(&source).execute_func(FuncId::new(0), []);
    assert!(
        baseline.events[publication + 1..]
            .iter()
            .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
    for cut in 1..=baseline.events.len() {
        let mut observer = Observer {
            cut: Some(cut),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let interpreter = Interpreter::with_module(&source);
        let report = interpreter.execute_func_observed(FuncId::new(0), vec![], &mut session);
        if cut <= publication + 1 {
            assert!(
                matches!(report.exit(), ObservedExit::AdmissionRefused),
                "cut {cut}"
            );
        } else {
            // The healthy report is DATA; a later caller-retirement stop still
            // cannot authorize publication or clear the same original cause.
            assert_data(&expected, &report);
        }
        assert!(
            report
                .retire_observed(&mut session, ExecutionSite::Entry(FuncId::new(0)))
                .is_err()
        );
        let first = session.first_refusal().unwrap();
        assert_eq!(first.cause, Cause::Cut(cut));
        assert_eq!(first.progress, baseline.events[cut - 1]);
        let report = interpreter.execute_func_observed(FuncId::new(0), vec![], &mut session);
        assert!(matches!(report.exit(), ObservedExit::AdmissionRefused));
        assert!(
            report
                .retire_observed(&mut session, ExecutionSite::Entry(FuncId::new(0)))
                .is_err()
        );
        assert_eq!(session.first_refusal().unwrap().cause, Cause::Cut(cut));
        assert_eq!(&observer.events[..cut], &baseline.events[..cut]);
        assert!(
            observer.events[cut..]
                .iter()
                .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}

#[test]
fn exact_whole_sequence_and_one_short_use_one_original_cumulative_account() {
    let source = bulk_module(true, 2);
    let baseline = parity(&source, vec![]);
    assert!(baseline.spent_work > 0 && baseline.spent_copy > 0);
    let expected = Interpreter::with_module(&source).execute_func(FuncId::new(0), []);
    let mut observer = Observer {
        work_limit: Some(baseline.spent_work),
        copy_limit: Some(baseline.spent_copy),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let interpreter = Interpreter::with_module(&source);
    let report = interpreter.execute_func_observed(FuncId::new(0), vec![], &mut session);
    assert_data(&expected, &report);
    report
        .retire_observed(&mut session, ExecutionSite::Entry(FuncId::new(0)))
        .unwrap();
    assert!(session.first_refusal().is_none());
    let fuel = session.remaining_fuel();
    let report = interpreter.execute_func_observed(FuncId::new(0), vec![], &mut session);
    assert!(matches!(report.exit(), ObservedExit::AdmissionRefused));
    assert_eq!(session.first_refusal().unwrap().cause, Cause::Budget);
    assert_eq!(session.remaining_fuel(), fuel);
    assert!(
        report
            .retire_observed(&mut session, ExecutionSite::Entry(FuncId::new(0)))
            .is_err()
    );
    assert_eq!(observer.spent_work, baseline.spent_work);
    assert_eq!(observer.spent_copy, baseline.spent_copy);
    let mut short = Observer {
        work_limit: Some(baseline.spent_work),
        copy_limit: Some(baseline.spent_copy - 1),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut short);
    let report = interpreter.execute_func_observed(FuncId::new(0), vec![], &mut session);
    assert!(matches!(report.exit(), ObservedExit::AdmissionRefused));
    let first = session.first_refusal().unwrap();
    assert_eq!(first.cause, Cause::Budget);
    assert!(first.progress.copy_bytes > 0);
    assert!(
        report
            .retire_observed(&mut session, ExecutionSite::Entry(FuncId::new(0)))
            .is_err()
    );
    assert!(short.spent_copy < baseline.spent_copy);
}
