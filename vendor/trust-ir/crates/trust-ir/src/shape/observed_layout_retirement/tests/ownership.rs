// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

#[test]
fn shared_then_unique_ty_arc_releases_this_owner_then_consumes_names_once() {
    let name = "λ".repeat(10007);
    let value = Arc::new(ty_shape(TyLayoutKind::Tuple {
        fields: vec![field(&name)],
    }));
    let last = Arc::clone(&value);
    let weak = Arc::downgrade(&value);
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    value.retire_arc_observed(&mut session, site()).unwrap();
    assert_eq!(Arc::strong_count(&last), 1);
    assert!(weak.upgrade().is_some());
    assert!(matches!(&last.kind, TyLayoutKind::Tuple {fields} if fields[0].name == name));
    last.retire_arc_observed(&mut session, site()).unwrap();
    assert!(weak.upgrade().is_none());
    assert!(session.first_refusal().is_none());
    assert_eq!(observer.events[3].phase, ExecutionPhase::Publication);
    assert!(
        observer.events[..3]
            .iter()
            .all(|e| e.work != name.len() + size_of::<String>() + 1)
    );
    assert_eq!(
        count_work(&observer, name.len() + size_of::<String>() + 1),
        1
    );
}
#[test]
fn shared_then_unique_enum_arc_retains_and_later_drains_the_full_descriptor() {
    let shape = enum_shape(Some(encodings().remove(1)));
    let expected = expected_enum_work(&shape);
    let value = Arc::new(shape);
    let last = Arc::clone(&value);
    let weak = Arc::downgrade(&value);
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    value.retire_arc_observed(&mut session, site()).unwrap();
    assert_eq!(Arc::strong_count(&last), 1);
    assert_eq!(last.discriminants, [i128::MIN, 0, i128::MAX]);
    assert_eq!(
        last.descriptor.as_ref().unwrap().variant_field_offsets[0],
        [1, u64::MAX, 0]
    );
    last.retire_arc_observed(&mut session, site()).unwrap();
    assert!(weak.upgrade().is_none());
    assert!(session.first_refusal().is_none());
    // First shared call: Arc release, None, poll, Publication. Second call's
    // Arc precharge precedes exactly the full owned enum receipt.
    assert_eq!(observer.events[3].phase, ExecutionPhase::Publication);
    let owned = &observer.events[5..5 + expected.len()];
    assert_eq!(owned.iter().map(|e| e.work).collect::<Vec<_>>(), expected);
}
#[test]
fn weak_references_do_not_hide_a_unique_ty_payload_from_explicit_consumption() {
    let name = "only-strong".repeat(777);
    let value = Arc::new(ty_shape(TyLayoutKind::Closure {
        id: ClosureTyId::new(1),
        captures: vec![field(&name)],
    }));
    let weak = Arc::downgrade(&value);
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    value.retire_arc_observed(&mut session, site()).unwrap();
    assert!(weak.upgrade().is_none());
    assert_eq!(
        count_work(&observer, name.len() + size_of::<String>() + 1),
        1
    );
}
#[test]
fn weak_references_do_not_hide_a_unique_enum_payload_from_explicit_consumption() {
    let shape = enum_shape(Some(EnumTagEncoding::Direct { tag_offset: 7 }));
    let expected = expected_enum_work(&shape);
    let value = Arc::new(shape);
    let weak = Arc::downgrade(&value);
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    value.retire_arc_observed(&mut session, site()).unwrap();
    assert!(weak.upgrade().is_none());
    assert_eq!(
        observer.events[1..1 + expected.len()]
            .iter()
            .map(|e| e.work)
            .collect::<Vec<_>>(),
        expected
    );
}
#[test]
fn stopped_shared_release_does_not_make_the_later_unique_owner_skip_cleanup() {
    let name = "retained".repeat(3000);
    let value = Arc::new(ty_shape(TyLayoutKind::Struct {
        id: StructId::new(2),
        fields: vec![field(&name)],
    }));
    let last = Arc::clone(&value);
    let weak = Arc::downgrade(&value);
    let mut observer = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        value.retire_arc_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    let first = session.first_refusal().unwrap().progress;
    assert_eq!(Arc::strong_count(&last), 1);
    assert_eq!(
        last.retire_arc_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().progress, first);
    assert_eq!(
        session.first_refusal().unwrap().cause,
        "original retirement stop"
    );
    assert!(weak.upgrade().is_none());
    assert_eq!(
        count_work(&observer, name.len() + size_of::<String>() + 1),
        1
    );
    assert!(
        observer
            .events
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn final_publication_refusal_occurs_after_unique_arc_payload_is_fully_consumed() {
    let shape = enum_shape(Some(encodings().remove(1)));
    let base = trace(Sample::Enum(shape.clone()), true);
    let value = Arc::new(shape);
    let weak = Arc::downgrade(&value);
    let mut observer = Observer {
        stop: Some(base.events.len()),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        value.retire_arc_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert!(weak.upgrade().is_none());
    assert_eq!(observer.events, base.events);
}
