// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;

#[test]
fn every_actual_cast_callback_stops_under_original_owner_and_cleans_up() {
    let module = fixture();
    let src = Ty::Struct(StructId::new(91));
    let mut baseline = Observer::default();
    run(&module, CastOp::Transmute, &src, &Ty::U64, &mut baseline)
        .unwrap()
        .unwrap();
    for stop_at in 1..=baseline.events.len() {
        let mut observer = Observer {
            stop_at: Some(stop_at),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let result = LayoutTable::new_observed(&module, &mut session, site()).and_then(|table| {
            table.layout_sensitive_cast_evidence_observed(
                CastOp::Transmute,
                &src,
                &Ty::U64,
                &mut session,
                site(),
            )
        });
        assert_eq!(
            result.unwrap_err(),
            ObservedValueError::AdmissionRefused,
            "event {stop_at}"
        );
        assert_eq!(session.first_refusal().unwrap().cause, "interior");
        assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
        assert!(
            observer
                .events
                .iter()
                .skip(stop_at)
                .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}

#[test]
fn repeated_casts_share_cumulative_original_work_and_requested_bytes() {
    let module = fixture();
    let src = Ty::Struct(StructId::new(91));
    let mut measured = Observer::default();
    run(&module, CastOp::Transmute, &src, &Ty::U64, &mut measured)
        .unwrap()
        .unwrap();
    for copying in [false, true] {
        let mut observer = if copying {
            Observer {
                byte_limit: Some(measured.bytes),
                ..Observer::default()
            }
        } else {
            Observer {
                work_limit: Some(measured.work),
                ..Observer::default()
            }
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let table = LayoutTable::new_observed(&module, &mut session, site()).unwrap();
        table
            .layout_sensitive_cast_evidence_observed(
                CastOp::Transmute,
                &src,
                &Ty::U64,
                &mut session,
                site(),
            )
            .unwrap()
            .unwrap();
        assert_eq!(
            table
                .layout_sensitive_cast_evidence_observed(
                    CastOp::Transmute,
                    &src,
                    &Ty::U64,
                    &mut session,
                    site()
                )
                .unwrap_err(),
            ObservedValueError::AdmissionRefused
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if copying { "bytes" } else { "work" }
        );
    }
}

#[test]
fn final_cast_retirement_refusal_prevents_already_computed_evidence() {
    let module = fixture();
    let src = Ty::Struct(StructId::new(91));
    let mut baseline = Observer::default();
    run(&module, CastOp::Transmute, &src, &Ty::U64, &mut baseline)
        .unwrap()
        .unwrap();
    let stop_at = baseline
        .events
        .iter()
        .rposition(|event| event.phase == ExecutionPhase::ScratchRetirement)
        .unwrap()
        + 1;
    assert_eq!(
        baseline.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    let mut observer = Observer {
        stop_at: Some(stop_at),
        ..Observer::default()
    };
    assert_eq!(
        run(&module, CastOp::Transmute, &src, &Ty::U64, &mut observer).unwrap_err(),
        ObservedValueError::AdmissionRefused
    );
}

#[test]
fn deep_named_cycle_is_observed_without_native_recursion_or_depth_cap() {
    let mut module = Module::new("deep_cast_cycle");
    for index in 0..4096 {
        module
            .types
            .push(Ty::Array(TyId::new((index + 1) % 4096), 1));
    }
    let src = Ty::Ref(Box::new(Ty::Array(TyId::new(0), 1)));
    equal(&module, CastOp::PtrToPtr, &src, &Ty::Ptr);
    assert!(
        run(
            &module,
            CastOp::PtrToPtr,
            &src,
            &Ty::Ptr,
            &mut Observer::default()
        )
        .unwrap()
        .is_ok()
    );
}

#[test]
fn failure_of_second_layout_preserves_first_result_custody_and_semantic_error() {
    let module = fixture();
    let src = Ty::Struct(StructId::new(91));
    let dst = Ty::Struct(StructId::new(404));
    equal(&module, CastOp::Transmute, &src, &dst);
    let mut measured = Observer::default();
    assert!(
        run(&module, CastOp::Transmute, &src, &dst, &mut measured)
            .unwrap()
            .is_err()
    );
    let stop_at = measured
        .events
        .iter()
        .rposition(|event| event.phase == ExecutionPhase::ScratchRetirement)
        .unwrap()
        + 1;
    let mut observer = Observer {
        stop_at: Some(stop_at),
        ..Observer::default()
    };
    assert_eq!(
        run(&module, CastOp::Transmute, &src, &dst, &mut observer).unwrap_err(),
        ObservedValueError::AdmissionRefused
    );
}
