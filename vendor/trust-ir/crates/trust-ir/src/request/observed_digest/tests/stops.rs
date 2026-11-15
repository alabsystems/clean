// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;

fn atom() -> NativeReplayAtom {
    NativeReplayAtom::assertion(
        NativeReplayAtomId::new(5),
        ProofFormula::smtlib2("(= x 3)", "Bool"),
    )
}

#[test]
fn every_actual_atom_serialization_hash_and_retirement_stop_is_terminal() {
    let atom = atom();
    let mut measured = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
    assert_eq!(
        atom.expected_payload_digest_observed(&mut session, site())
            .unwrap(),
        atom.expected_payload_digest()
    );
    let count = measured.events.len();
    for stop_at in 1..=count {
        let mut observer = Observer {
            stop_at: Some(stop_at),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            atom.expected_payload_digest_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused),
            "event {stop_at}"
        );
        assert_eq!(session.first_refusal().unwrap().cause, "interior");
        assert_eq!(
            atom.expected_payload_digest_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
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
fn original_work_and_copy_budgets_accumulate_across_complete_bundle_digests() {
    let value = bundle();
    let mut measured = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
    value.stable_digest_observed(&mut session, site()).unwrap();
    for memory in [false, true] {
        let mut observer = if memory {
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
        assert_eq!(
            value.stable_digest_observed(&mut session, site()).unwrap(),
            value.stable_digest()
        );
        assert_eq!(
            value.stable_digest_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if memory { "bytes" } else { "work" }
        );
    }
}

#[test]
fn refusal_during_scratch_retirement_cannot_publish_completed_identity() {
    let value = bundle();
    let mut observer = Observer {
        stop_retirement: true,
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        value.stable_digest_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "retirement");
    let stopped = observer
        .events
        .iter()
        .position(|event| event.phase == ExecutionPhase::ScratchRetirement)
        .unwrap();
    assert!(
        observer.events[stopped..]
            .iter()
            .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
}

#[test]
fn initial_header_and_interior_sort_growth_are_admitted_before_copying() {
    let value = bundle();
    let mut observer = Observer {
        byte_limit: Some(0),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        value.stable_digest_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(observer.events.len(), 1);
    let mut measured = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
    digest(&mut session, site(), "sort", |out| {
        write_proof_ids(out, &[ProofId::new(3), ProofId::new(1)])
    })
    .unwrap();
    let growth = measured
        .events
        .iter()
        .position(|event| event.copy_bytes == 2 * core::mem::size_of::<&ProofId>())
        .expect("first borrowed sort storage");
    let mut observer = Observer {
        stop_at: Some(growth + 1),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        digest(&mut session, site(), "sort", |out| write_proof_ids(
            out,
            &[ProofId::new(3), ProofId::new(1)]
        )),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "interior");
}

#[test]
fn interior_type_cursor_and_long_sort_comparison_stops_do_not_hash_a_prefix() {
    let ty = Ty::Tuple((0..32).map(|_| Ty::Ref(Box::new(Ty::U8))).collect());
    let tools = [
        NativeToolIdentity {
            name: format!("{}z", "a".repeat(4097)),
            version: None,
            revision: None,
            digest: None,
        },
        NativeToolIdentity {
            name: format!("{}a", "a".repeat(4097)),
            version: None,
            revision: None,
            digest: None,
        },
    ];
    for sorting in [false, true] {
        let mut measured = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
        digest(&mut session, site(), "interior", |out| {
            if sorting {
                write_tool_identities(out, &tools)
            } else {
                write_ty(out, &ty)
            }
        })
        .unwrap();
        let last = measured.events.len();
        for stop_at in [1, last / 4, last / 2, last - 1, last] {
            let mut observer = Observer {
                stop_at: Some(stop_at),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                digest(&mut session, site(), "interior", |out| {
                    if sorting {
                        write_tool_identities(out, &tools)
                    } else {
                        write_ty(out, &ty)
                    }
                }),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(session.first_refusal().unwrap().cause, "interior");
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
