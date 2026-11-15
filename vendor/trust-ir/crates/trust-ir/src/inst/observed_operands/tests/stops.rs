// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn every_real_case_operand_metadata_retirement_and_publication_callback_can_stop() {
    let mut instructions = invocations();
    instructions.push(switch(false, 3));
    instructions.push(Inst::NullPtr);
    for instruction in instructions {
        let (_, baseline) = observed(&instruction);
        for (index, expected) in baseline.events.into_iter().enumerate() {
            let mut observer = Observer {
                stop_at: Some(index + 1),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                instruction.value_operands_observed(&mut session, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(session.first_refusal().unwrap().progress, expected);
            assert_eq!(session.first_refusal().unwrap().cause, "original stop");
            assert_eq!(
                instruction.value_operands_observed(&mut session, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(session.first_refusal().unwrap().cause, "original stop");
            assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
            assert!(
                observer.events[index + 1..]
                    .iter()
                    .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}

#[test]
fn thousands_of_empty_switch_cases_consume_actual_original_work_without_operands() {
    let instruction = switch(true, 5000);
    let (values, baseline) = observed(&instruction);
    assert_eq!(values, ids(&[1]));
    assert!(baseline.work >= 5000);
    let mut observer = Observer {
        work_cap: Some(200),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        instruction.value_operands_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "work");
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Validation
    );
    assert_eq!(session.first_refusal().unwrap().progress.copy_bytes, 0);
    assert!(observer.events.len() < 1000);
}

#[test]
fn original_work_and_requested_bytes_are_cumulative_across_operand_collections() {
    let instruction = switch(false, 5);
    let (_, baseline) = observed(&instruction);
    for bytes in [false, true] {
        let mut observer = Observer {
            work_cap: (!bytes).then_some(baseline.work),
            byte_cap: bytes.then_some(baseline.bytes),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            instruction
                .value_operands_observed(&mut session, site())
                .unwrap(),
            ordinary(&instruction)
        );
        assert_eq!(
            instruction.value_operands_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if bytes { "bytes" } else { "work" }
        );
    }
}

#[test]
fn first_actual_vector_storage_is_refused_before_allocation() {
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut values = Vec::new();
    assert_eq!(
        work.push(&mut values, v(1)),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!((values.len(), values.capacity()), (0, 0));
    work.retire_values(&mut values);
}

#[test]
fn reserved_but_unpublished_slot_is_owned_and_retires_after_copy_admission_refusal() {
    let mut observer = Observer {
        stop_at: Some(3),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut values = Vec::new();
    assert_eq!(
        work.push(&mut values, v(1)),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(values.len(), 0);
    assert!(values.capacity() >= 1);
    work.retire_values(&mut values);
    assert_eq!(values.capacity(), 0);
    assert_eq!(work.session.first_refusal().unwrap().cause, "original stop");
}

#[test]
fn fixed_dispatch_scratch_retirement_refusal_prevents_result_publication() {
    let mut observer = Observer {
        stop_phase: Some(ExecutionPhase::ScratchRetirement),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        switch(false, 3).value_operands_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::ScratchRetirement
    );
    assert!(
        !observer
            .events
            .iter()
            .any(|event| event.phase == ExecutionPhase::Publication)
    );
}

#[test]
fn final_publication_refusal_retires_every_collected_fixed_value() {
    let instruction = switch(false, 3);
    let (_, baseline) = observed(&instruction);
    let mut observer = Observer {
        stop_at: Some(baseline.events.len()),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        instruction.value_operands_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    let retired = &observer.events[baseline.events.len()..];
    assert!(
        retired
            .iter()
            .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
    assert!(retired.len() >= ordinary(&instruction).len() + 2);
}
