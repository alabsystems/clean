// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

#[test]
fn checked_real_wire_identity_matches_ordinary_digest_and_writer_acceptance() {
    let module = module();
    assert!(module.wire_image_refusals().is_empty());
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        module
            .checked_stable_digest_observed(&mut session, site())
            .unwrap(),
        module.stable_digest()
    );
}
#[test]
#[cfg(target_pointer_width = "64")]
fn writer_count_boundary_is_refused_before_oversized_spelling_in_checked_mode_only() {
    for count in [u64::from(u32::MAX), u64::from(u32::MAX) + 1] {
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let mut sink = Output::counter(&mut session, site()).unwrap();
        sink.require_wire_image();
        let result = observed_write_count(&mut sink, "fixture", count as usize);
        if count > u64::from(u32::MAX) {
            assert_eq!(result, Err(ObservedValueError::UnsupportedValue));
            assert_eq!(sink.count().unwrap(), 0);
        } else {
            result.unwrap();
            assert_eq!(sink.count().unwrap(), 5);
        }
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        let mut sink = Output::counter(&mut session, site()).unwrap();
        observed_write_count(&mut sink, "fixture", count as usize).unwrap();
        assert_eq!(sink.count().unwrap(), 5);
    }
}
#[test]
fn checked_wire_has_no_digest_for_the_same_unencodable_producer_internal_type() {
    let mut module = module();
    module.types.push(Ty::Tuple(vec![Ty::Error]));
    assert!(!module.wire_image_refusals().is_empty());
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        module.checked_stable_digest_observed(&mut session, site()),
        Err(ObservedValueError::UnsupportedValue)
    );
}
#[test]
fn checked_writer_remains_cumulatively_refusable_and_retirement_is_not_a_new_grant() {
    let module = module();
    let mut measured = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut measured);
    module
        .checked_stable_digest_observed(&mut session, site())
        .unwrap();
    let mut observer = Observer {
        work_limit: Some(measured.work),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    module
        .checked_stable_digest_observed(&mut session, site())
        .unwrap();
    assert_eq!(
        module.checked_stable_digest_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    let mut observer = Observer {
        retirement_stop: true,
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        module.checked_stable_digest_observed(&mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
}
