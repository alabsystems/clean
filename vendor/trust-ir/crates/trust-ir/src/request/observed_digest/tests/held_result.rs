// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;

fn cleanup_only(events: &[ExecutionProgress], from: usize) {
    assert!(
        events[from..]
            .iter()
            .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
}

#[test]
fn held_writer_error_survives_cleanup_and_never_requests_publication() {
    for error in [
        ObservedValueError::UnsupportedValue,
        ObservedValueError::CapacityOverflow,
        ObservedValueError::AllocationFailed,
        ObservedValueError::InvalidRange,
    ] {
        for stop_retirement in [false, true] {
            let mut observer = Observer {
                stop_retirement,
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                digest(&mut session, site(), "held", |out| {
                    out.append(b"actual owned prefix")?;
                    Err(error)
                }),
                Err(error)
            );
            assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
            assert_eq!(session.first_refusal().is_some(), stop_retirement);
            if stop_retirement {
                assert_eq!(session.first_refusal().unwrap().cause, "retirement");
            }
            let retired = observer
                .events
                .iter()
                .position(|e| e.phase == ExecutionPhase::ScratchRetirement)
                .unwrap();
            cleanup_only(&observer.events, retired);
            assert!(
                !observer
                    .events
                    .iter()
                    .any(|e| e.phase == ExecutionPhase::Publication)
            );
        }
    }
}

#[test]
fn actual_nested_type_hole_survives_cursor_and_writer_retirement_refusal() {
    let ty = Ty::Tuple(vec![Ty::U8, Ty::Ref(Box::new(Ty::Error)), Ty::Bool]);
    for stop_retirement in [false, true] {
        let mut observer = Observer {
            stop_retirement,
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            digest(&mut session, site(), "hole", |out| write_ty(out, &ty)),
            Err(ObservedValueError::UnsupportedValue)
        );
        assert_eq!(session.first_refusal().is_some(), stop_retirement);
        let retired = observer
            .events
            .iter()
            .position(|e| e.phase == ExecutionPhase::ScratchRetirement)
            .unwrap();
        cleanup_only(&observer.events, retired);
        assert!(observer.events[retired..].len() >= 4);
    }
    assert_eq!(
        ty,
        Ty::Tuple(vec![Ty::U8, Ty::Ref(Box::new(Ty::Error)), Ty::Bool])
    );
}

#[test]
fn failed_actual_comparison_keeps_both_sort_buffers_until_cleanup() {
    for stop_retirement in [false, true] {
        let mut observer = Observer {
            stop_retirement,
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            digest(&mut session, site(), "sort", |out| {
                sorted(&[3u32, 1, 2], out, |_, _, _| {
                    Err(ObservedValueError::InvalidRange)
                })
                .map(drop)
            }),
            Err(ObservedValueError::InvalidRange)
        );
        assert_eq!(session.first_refusal().is_some(), stop_retirement);
        let retired = observer
            .events
            .iter()
            .position(|e| e.phase == ExecutionPhase::ScratchRetirement)
            .unwrap();
        cleanup_only(&observer.events, retired);
        assert!(observer.events[retired..].len() >= 6);
    }
}

fn sorted_types(observer: &mut Observer) -> Result<ProofDigest> {
    let mut session = ObservedSession::new(InterpretOptions::default(), observer);
    digest(&mut session, site(), "typed-sort", |out| {
        write_sorted(
            &[Ty::U8, Ty::Error, Ty::Bool],
            out,
            |_, _, _| Ok(core::cmp::Ordering::Equal),
            |ty, out| write_ty(out, ty),
        )
    })
}

#[test]
fn held_row_error_survives_later_outer_sort_buffer_retirement() {
    let mut measured = Observer::default();
    assert_eq!(
        sorted_types(&mut measured),
        Err(ObservedValueError::UnsupportedValue)
    );
    // The sort and first healthy U8 cursor retire before the actual error.
    let final_suffix = measured
        .events
        .iter()
        .rposition(|e| e.phase != ExecutionPhase::ScratchRetirement)
        .unwrap()
        + 1;
    for stop_at in final_suffix + 1..=measured.events.len() {
        let mut observer = Observer {
            stop_at: Some(stop_at),
            ..Observer::default()
        };
        assert_eq!(
            sorted_types(&mut observer),
            Err(ObservedValueError::UnsupportedValue)
        );
        cleanup_only(&observer.events, final_suffix);
    }
}

#[test]
fn successful_digest_still_requires_original_publication_after_all_cleanup() {
    let value = Constant::Array(vec![Constant::Int(7), Constant::Bool(true)]);
    let mut bytes = Vec::new();
    write_constant_stable(&mut bytes, &value);
    let mut measured = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
    assert_eq!(
        digest(&mut session, site(), "constant", |out| write_constant(
            out, &value
        ))
        .unwrap(),
        ProofDigest::sha256_domain("constant", &bytes)
    );
    assert_eq!(
        measured.events.last().unwrap().phase,
        ExecutionPhase::Publication
    );
    let mut observer = Observer {
        stop_at: Some(measured.events.len()),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        digest(&mut session, site(), "constant", |out| write_constant(
            out, &value
        )),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert_eq!(session.first_refusal().unwrap().cause, "interior");
}
