// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored source controls, UNRUN.
use super::*;
use crate::interpret::InterpretOptions;
#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop: Option<usize>,
    cap: Option<usize>,
    work: usize,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop == Some(self.events.len()) {
            return Err("before tree step");
        }
        self.work = self.work.checked_add(event.work).ok_or("overflow")?;
        if self.cap.is_some_and(|cap| self.work > cap) {
            return Err("population");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(976))
}
#[test]
fn iterator_header_is_admitted_before_readonly_or_mutable_cursor_exists() {
    let mut map: BTreeMap<_, _> = (0..257).map(|key| (key, vec![key])).collect();
    let expected = map.clone();
    let mut observer = Observer {
        cap: Some(map.len()),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    assert!(matches!(
        work.entries(&map),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(work.session.first_refusal().unwrap().cause, "population");
    assert_eq!(
        work.session.first_refusal().unwrap().progress.work,
        map.len() + 1
    );
    assert_eq!(map, expected);
    let mut observer = Observer {
        cap: Some(map.len()),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    assert!(matches!(
        work.rows(&mut map),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(work.session.first_refusal().unwrap().cause, "population");
    assert_eq!(map, expected);
}
#[test]
fn readonly_next_refusal_precedes_actual_cursor_advance_and_keeps_original_cause() {
    let map: BTreeMap<_, _> = (0..257u32).map(|key| (key, key + 10)).collect();
    let mut observer = Observer {
        stop: Some(3),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut cursor = work.entries(&map).unwrap();
    assert_eq!(cursor.next(&mut work).unwrap(), Some((&0, &10)));
    assert_eq!(cursor.actual.len(), 256);
    assert_eq!(
        cursor.next(&mut work),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(cursor.actual.len(), 256);
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "before tree step"
    );
    work.retire(cursor);
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "before tree step"
    );
    assert!(
        observer.events[..3]
            .iter()
            .all(|event| event.site == site() && event.work == 258)
    );
    assert!(
        observer.events[3..]
            .iter()
            .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn mutable_cursor_order_and_exhaustion_are_observed_and_interior_refusal_keeps_position() {
    let mut map: BTreeMap<_, _> = (0..257u32).map(|key| (key, vec![key])).collect();
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut cursor = work.rows(&mut map).unwrap();
    for expected in 0..257 {
        assert_eq!(
            cursor.next(&mut work).unwrap().unwrap().as_slice(),
            &[expected]
        );
    }
    assert!(cursor.next(&mut work).unwrap().is_none());
    work.retire(cursor);
    assert!(work.session.first_refusal().is_none());
    assert_eq!(
        observer
            .events
            .iter()
            .filter(|event| event.phase == ExecutionPhase::Validation)
            .count(),
        259
    );
    let mut observer = Observer {
        stop: Some(3),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut cursor = work.rows(&mut map).unwrap();
    assert_eq!(cursor.next(&mut work).unwrap().unwrap().as_slice(), &[0]);
    assert!(matches!(
        cursor.next(&mut work),
        Err(ObservedValueError::AdmissionRefused)
    ));
    assert_eq!(cursor.actual.len(), 256);
    work.retire(cursor);
    assert_eq!(
        work.session.first_refusal().unwrap().cause,
        "before tree step"
    );
}
