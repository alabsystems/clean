// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;

#[test]
fn every_actual_wide_switch_and_invoke_callback_keeps_stop_sticky_and_no_partial_result() {
    let mut instructions = Vec::from(invokes());
    instructions.push(switch(257));
    instructions.push(Inst::NullPtr);
    for instruction in instructions {
        let mut baseline = Observer::default();
        observed(&instruction, &mut baseline).unwrap();
        for stop_at in 1..=baseline.events.len() {
            let mut observer = Observer {
                stop_at: Some(stop_at),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                instruction.successor_edges_observed(&mut session, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(session.first_refusal().unwrap().cause, "original stop");
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
}

#[test]
fn cumulative_work_and_bytes_span_repeated_edge_queries_in_original_session() {
    let invoke = invokes().into_iter().next().unwrap();
    let instructions = [switch(0), invoke, switch(17)];
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    for instruction in &instructions {
        instruction
            .successor_edges_observed(&mut session, site())
            .unwrap();
    }
    for bytes in [false, true] {
        let mut observer = if bytes {
            Observer {
                byte_cap: Some(baseline.bytes - 1),
                ..Observer::default()
            }
        } else {
            Observer {
                work_cap: Some(baseline.work - 1),
                ..Observer::default()
            }
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        for instruction in &instructions[..2] {
            instruction
                .successor_edges_observed(&mut session, site())
                .unwrap();
        }
        assert_eq!(
            instructions[2].successor_edges_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if bytes { "bytes" } else { "work" }
        );
        assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    }
}

#[test]
fn first_edge_storage_is_refused_before_vector_allocation() {
    let values = [ValueId::new(4)];
    let mut edges = Vec::new();
    let mut observer = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        normal(&mut edges, BlockId::new(1), &values, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!((edges.len(), edges.capacity()), (0, 0));
    retire(edges, &mut session, site());
    assert_eq!(session.first_refusal().unwrap().cause, "bytes");
}

#[test]
fn final_publication_refusal_retires_all_completed_borrowed_edges() {
    let instruction = switch(17);
    let mut baseline = Observer::default();
    observed(&instruction, &mut baseline).unwrap();
    let stop_at = baseline.events.len();
    assert_eq!(
        baseline.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    let mut observer = Observer {
        stop_at: Some(stop_at),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        instruction.successor_edges_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert!(observer.events.len() >= stop_at + 18 + 2);
    assert!(
        observer
            .events
            .iter()
            .skip(stop_at)
            .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
}

#[test]
fn final_buffer_drop_is_observed_and_cannot_resume_publication() {
    let instruction = switch(17);
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    retire(instruction.successor_edges(), &mut session, site());
    let stop_at = baseline.events.len();
    let mut observer = Observer {
        stop_at: Some(stop_at),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    retire(instruction.successor_edges(), &mut session, site());
    assert_eq!(session.first_refusal().unwrap().cause, "original stop");
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::ScratchRetirement
    );
    assert!(
        session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: site(),
                work: 0,
                copy_bytes: 0
            })
            .is_err()
    );
    assert_eq!(observer.events.len(), stop_at);
}
