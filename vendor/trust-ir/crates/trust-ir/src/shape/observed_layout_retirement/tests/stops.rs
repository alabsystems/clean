// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

fn every_stop(sample: Sample, arc: bool) {
    // Identical public owned/unique-Arc entry for baseline and every replay.
    let base = trace(sample.clone(), arc);
    for stop in 1..=base.events.len() {
        let (result, observer) = execute(
            sample.clone(),
            arc,
            Observer {
                stop: Some(stop),
                ..Observer::default()
            },
        );
        assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
        // Retirement callbacks never stop consuming. Only the terminal normal
        // admission is suppressed when a prior retirement latched refusal.
        let end = base.events.len() - usize::from(stop < base.events.len());
        assert_eq!(observer.events, base.events[..end]);
    }
}
#[test]
fn every_callback_owned_ty_all_kinds_consumes_every_remaining_field_after_stop() {
    for shape in ty_shapes() {
        every_stop(Sample::Ty(shape), false);
    }
}
#[test]
fn every_callback_owned_enum_all_encodings_consumes_all_nested_rows_after_stop() {
    every_stop(Sample::Enum(enum_shape(None)), false);
    for encoding in encodings() {
        every_stop(Sample::Enum(enum_shape(Some(encoding))), false);
    }
}
#[test]
fn every_callback_unique_arc_uses_identical_entry_and_cannot_flat_drop_payload() {
    every_stop(Sample::Ty(ty_shapes().remove(3)), true);
    for encoding in encodings() {
        every_stop(Sample::Enum(enum_shape(Some(encoding))), true);
    }
}
#[test]
fn first_callback_refusal_stays_first_through_every_later_owned_enum_child() {
    let sample = Sample::Enum(enum_shape(Some(encodings().remove(1))));
    let base = trace(sample.clone(), false);
    let mut observer = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        sample.retire(false, &mut session),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().cause,
        "original retirement stop"
    );
    assert_eq!(session.first_refusal().unwrap().progress, base.events[0]);
    assert_eq!(observer.events, base.events[..base.events.len() - 1]);
}
#[test]
fn byte_length_is_actual_utf8_bytes_in_retirement_work_and_is_not_copy_fuel() {
    let sample = |name: &str| {
        Sample::Ty(ty_shape(TyLayoutKind::Tuple {
            fields: vec![field(name)],
        }))
    };
    let empty = trace(sample(""), false);
    let ascii = trace(sample("a"), false);
    let unicode = trace(sample("λ"), false);
    assert_eq!(ascii.work - empty.work, 1);
    assert_eq!(unicode.work - empty.work, 2);
    assert_eq!(empty.bytes, 0);
    assert_eq!(ascii.bytes, 0);
    assert_eq!(unicode.bytes, 0);
}
#[test]
fn original_work_cumulates_across_owned_and_arc_cleanup_without_reset() {
    let sample = Sample::Ty(ty_shape(TyLayoutKind::Tuple {
        fields: vec![field(&"λ".repeat(4000))],
    }));
    let first_base = trace(sample.clone(), false);
    let second_base = trace(sample.clone(), true);
    let mut observer = Observer {
        work_cap: Some(first_base.work),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    sample.clone().retire(false, &mut session).unwrap();
    assert_eq!(
        sample.clone().retire(true, &mut session),
        Err(ObservedValueError::AdmissionRefused)
    );
    let first = session.first_refusal().unwrap().progress;
    assert_eq!(session.first_refusal().unwrap().cause, "original work cap");
    assert_eq!(
        sample.retire(false, &mut session),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().progress, first);
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    let mut expected = first_base.events.clone();
    expected.extend_from_slice(&second_base.events[..second_base.events.len() - 1]);
    expected.extend_from_slice(&first_base.events[..first_base.events.len() - 1]);
    assert_eq!(observer.events, expected);
}
#[test]
fn original_copy_budget_refusal_is_preserved_while_all_cleanup_work_still_occurs() {
    let sample = Sample::Enum(enum_shape(Some(encodings().remove(1))));
    let base = trace(sample.clone(), false);
    let mut observer = Observer {
        byte_cap: Some(100),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    session
        .admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site: site(),
            work: 0,
            copy_bytes: 60,
        })
        .unwrap();
    let first = ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site: site(),
        work: 0,
        copy_bytes: 41,
    };
    assert!(session.admit(first).is_err());
    assert_eq!(
        sample.retire(false, &mut session),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "original byte cap");
    assert_eq!(session.first_refusal().unwrap().progress, first);
    assert_eq!(observer.events[2..], base.events[..base.events.len() - 1]);
    assert_eq!(observer.bytes, 101);
}
#[test]
fn interior_name_retirement_refusal_retains_first_cause_and_visits_all_other_names() {
    let names = ["first".repeat(3000), "中".repeat(9001), "last".repeat(5000)];
    let sample = Sample::Ty(ty_shape(TyLayoutKind::Struct {
        id: StructId::new(0),
        fields: names.iter().map(|name| field(name)).collect(),
    }));
    let base = trace(sample.clone(), false);
    let price = names[1].len() + size_of::<String>() + 1;
    let positions = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| e.work == price)
        .map(|(i, _)| i + 1)
        .collect::<Vec<_>>();
    assert_eq!(positions.len(), 1);
    let stop = positions[0];
    let mut observer = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        sample.retire(false, &mut session),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
    assert_eq!(observer.events, base.events[..base.events.len() - 1]);
    for name in names {
        assert_eq!(
            count_work(&observer, name.len() + size_of::<String>() + 1),
            1
        );
    }
}
