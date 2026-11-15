// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::dialect::schema::{DialectSchema, DialectSchemaRegistry, OperationSchema};
use crate::dialect::{AttrValue, DialectInst};
fn registry() -> DialectSchemaRegistry {
    DialectSchemaRegistry::new([DialectSchema {
        namespace: "test".into(),
        version: 1,
        operations: vec![OperationSchema {
            name: "op".into(),
            operands: vec![],
            results: vec![],
            attributes: vec![],
        }],
    }])
    .unwrap()
}
#[test]
fn frozen_lookup_returns_actual_borrowed_declaration_and_never_full_validation_authority() {
    let r = registry();
    let op = DialectInst::new("test", "op");
    let ordinary = r.validate_op(&op, 0, |_| None).unwrap();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let found = r
        .lookup_operation_observed(&op, &mut s, site())
        .unwrap()
        .unwrap();
    assert!(core::ptr::eq(found, ordinary));
    let bad = op.with_operand(crate::ValueId::new(99));
    assert!(
        r.lookup_operation_observed(&bad, &mut s, site())
            .unwrap()
            .is_ok()
    );
    assert!(r.validate_op(&bad, 0, |_| None).is_err());
}
#[test]
fn every_frozen_lexical_version_unknown_prefix_error_matches_actual_schema_display() {
    let r = registry();
    for op in [
        DialectInst::new("bad.name", "op"),
        DialectInst::new("test", ""),
        DialectInst::new("test", "op").with_attr("bad\n", AttrValue::Bool(false)),
        DialectInst::new("absent", "op"),
        DialectInst::new("test", "absent").with_version(2),
        DialectInst::new("test", "absent"),
    ] {
        let expected = r.validate_op(&op, 0, |_| None).unwrap_err().to_string();
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let error = r
            .lookup_operation_observed(&op, &mut s, site())
            .unwrap()
            .unwrap_err();
        assert_eq!(error, expected);
        dispose(error, &mut s);
    }
}
#[test]
fn every_registry_cursor_name_copy_and_full_error_publication_callback_refuses() {
    let r = registry();
    for op in [
        DialectInst::new("test", "op"),
        DialectInst::new("missing中", "op"),
    ] {
        let mut baseline = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
        let out = r.lookup_operation_observed(&op, &mut s, site()).unwrap();
        drop(s);
        drop(out);
        for cut in 1..=baseline.events.len() {
            let mut o = Observer {
                stop: Some(cut),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                r.lookup_operation_observed(&op, &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(s.first_refusal().unwrap().cause, "original raw-debug stop");
            drop(s);
            assert_eq!(&o.events[..cut], &baseline.events[..cut]);
            assert!(
                o.events[cut..]
                    .iter()
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn complete_owned_registry_error_survives_next_caller_fee_and_sticky_retirement() {
    let r = registry();
    let op = DialectInst::new("missing", "op");
    let mut baseline = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let out = r
        .lookup_operation_observed(&op, &mut s, site())
        .unwrap()
        .unwrap_err();
    drop(s);
    drop(out);
    let mut o = Observer {
        stop: Some(baseline.events.len() + 1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut held = Some(
        r.lookup_operation_observed(&op, &mut s, site())
            .unwrap()
            .unwrap_err(),
    );
    assert!(
        s.admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site: site(),
            work: 1,
            copy_bytes: 0
        })
        .is_err()
    );
    assert_eq!(
        held.as_deref(),
        Some("dialect schema mismatch: UnknownDialect(\"missing\")")
    );
    dispose(held.take().unwrap(), &mut s);
    assert!(held.is_none());
    assert_eq!(s.first_refusal().unwrap().cause, "original raw-debug stop");
}
