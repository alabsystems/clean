// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN. Structural cold-memo boundary and ordinary query parity.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::{CastOp, EnumDef, EnumId, EnumVariant};
fn none(table: &LayoutTable<'_>) {
    assert!(table.memo.lock().unwrap().is_none());
}
fn some(table: &LayoutTable<'_>) {
    assert!(table.memo.lock().unwrap().is_some());
}
fn extended() -> Module {
    let mut m = fixture();
    m.enums.push(EnumDef::new(
        EnumId::new(7),
        "E",
        vec![
            EnumVariant {
                name: "empty".into(),
                fields: vec![Ty::Never],
                field_names: vec![],
            },
            EnumVariant {
                name: "unit".into(),
                fields: vec![Ty::Unit],
                field_names: vec![],
            },
        ],
    ));
    m
}
#[test]
fn observed_construction_and_statistics_do_not_initialize_ordinary_hashers() {
    let m = extended();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let t = LayoutTable::new_observed(&m, &mut s, site()).unwrap();
    none(&t);
    assert_eq!(t.stats(), LayoutTableStats::EMPTY);
    none(&t);
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
}
#[test]
fn complete_observed_query_families_leave_ordinary_memo_uninitialized() {
    let m = extended();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let t = LayoutTable::new_observed(&m, &mut s, site()).unwrap();
    let result = t
        .ty_layout_observed(&Ty::Struct(StructId::new(91)), &mut s, site())
        .unwrap()
        .unwrap();
    result.retire_arc_observed(&mut s, site()).unwrap();
    none(&t);
    match t
        .enum_layout_observed(EnumId::new(7), &mut s, site())
        .unwrap()
    {
        Ok(shape) => shape.retire_arc_observed(&mut s, site()).unwrap(),
        Err(error) => error.retire_observed(&mut s, site()).unwrap(),
    }
    none(&t);
    assert!(
        !t.ty_is_uninhabited_observed(&Ty::U32, &mut s, site())
            .unwrap()
    );
    assert!(
        t.variant_is_uninhabited_observed(&m.enums[0].variants[0], &mut s, site())
            .unwrap()
    );
    t.validate_tuple_layouts_observed(&mut s, site())
        .unwrap()
        .unwrap();
    t.validate_closure_layouts_observed(&mut s, site())
        .unwrap()
        .unwrap();
    let value = t
        .layout_sensitive_cast_evidence_observed(
            CastOp::PtrToPtr,
            &Ty::Ptr,
            &Ty::Ptr,
            &mut s,
            site(),
        )
        .unwrap()
        .unwrap();
    assert!(matches!(
        value,
        crate::CastLayoutEvidence::PointerCast { .. }
    ));
    none(&t);
    assert_eq!(t.stats(), LayoutTableStats::EMPTY);
    none(&t);
}
#[test]
fn ordinary_first_query_lazily_builds_exact_memo_and_reuses_same_arc() {
    let m = fixture();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let t = LayoutTable::new_observed(&m, &mut s, site()).unwrap();
    none(&t);
    let a = t.ty_layout(&Ty::Struct(StructId::new(91))).unwrap();
    some(&t);
    let b = t.ty_layout(&Ty::Struct(StructId::new(91))).unwrap();
    assert!(Arc::ptr_eq(&a, &b));
    let ordinary = LayoutTable::new(&m);
    let ordinary_a = ordinary.ty_layout(&Ty::Struct(StructId::new(91))).unwrap();
    let ordinary_b = ordinary.ty_layout(&Ty::Struct(StructId::new(91))).unwrap();
    assert!(Arc::ptr_eq(&ordinary_a, &ordinary_b));
    assert_eq!(*a, *ordinary_a);
    assert_eq!(t.stats(), ordinary.stats());
}
#[test]
fn ordinary_definition_layout_inhabitance_and_reach_queries_match_original_table() {
    let m = extended();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let t = LayoutTable::new_observed(&m, &mut s, site()).unwrap();
    let ordinary = LayoutTable::new(&m);
    assert_eq!(
        t.struct_def(StructId::new(91)),
        ordinary.struct_def(StructId::new(91))
    );
    assert_eq!(
        t.enum_def(EnumId::new(7)),
        ordinary.enum_def(EnumId::new(7))
    );
    for ty in [
        Ty::U32,
        Ty::Bool,
        Ty::Struct(StructId::new(91)),
        Ty::Enum(EnumId::new(7)),
        Ty::Never,
        Ty::handle("H", "rt::H"),
    ] {
        assert_eq!(t.ty_layout(&ty), ordinary.ty_layout(&ty));
        assert_eq!(t.ty_is_uninhabited(&ty), ordinary.ty_is_uninhabited(&ty));
        assert_eq!(
            t.type_reaches_handle(&ty),
            ordinary.type_reaches_handle(&ty)
        );
        assert_eq!(
            t.type_holds_closure_by_value(&ty),
            ordinary.type_holds_closure_by_value(&ty)
        );
        assert_eq!(
            t.type_stores_bool_lane(&ty),
            ordinary.type_stores_bool_lane(&ty)
        );
    }
    assert_eq!(
        t.enum_layout(EnumId::new(7)),
        ordinary.enum_layout(EnumId::new(7))
    );
    assert_eq!(
        t.variant_is_uninhabited(&m.enums[0].variants[0]),
        ordinary.variant_is_uninhabited(&m.enums[0].variants[0])
    );
    assert_eq!(
        t.niche_unencoded_inhabited_variant(&m.enums[0], 1, 0, 0),
        ordinary.niche_unencoded_inhabited_variant(&m.enums[0], 1, 0, 0)
    );
    assert_eq!(t.stats(), ordinary.stats());
}
#[test]
fn initialized_observed_table_memo_roundtrip_preserves_actual_ordinary_answers() {
    let m = fixture();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let t = LayoutTable::new_observed(&m, &mut s, site()).unwrap();
    let shape = t.ty_layout(&Ty::Struct(StructId::new(91))).unwrap();
    let ordinary = LayoutTable::new(&m);
    let ordinary_shape = ordinary.ty_layout(&Ty::Struct(StructId::new(91))).unwrap();
    assert_eq!(*shape, *ordinary_shape);
    let stats = t.stats();
    assert_eq!(stats, ordinary.stats());
    let memo = t.into_memo();
    let ordinary_memo = ordinary.into_memo();
    assert_eq!(memo.stats(), stats);
    assert_eq!(memo.stats(), ordinary_memo.stats());
    let next = LayoutTable::with_memo(&m, memo);
    let ordinary_next = LayoutTable::with_memo(&m, ordinary_memo);
    assert_eq!(next.stats(), stats);
    let next_shape = next.ty_layout(&Ty::Struct(StructId::new(91))).unwrap();
    let ordinary_next_shape = ordinary_next
        .ty_layout(&Ty::Struct(StructId::new(91)))
        .unwrap();
    assert!(Arc::ptr_eq(&shape, &next_shape));
    assert!(Arc::ptr_eq(&ordinary_shape, &ordinary_next_shape));
    assert_eq!(*next_shape, *shape);
    assert_eq!(*next_shape, *ordinary_next_shape);
    assert_eq!(next.stats(), ordinary_next.stats());
}
#[test]
fn unused_observed_table_into_ordinary_memo_remains_empty_without_fake_work() {
    let m = fixture();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let t = LayoutTable::new_observed(&m, &mut s, site()).unwrap();
    none(&t);
    let memo = t.into_memo();
    assert_eq!(memo.stats(), LayoutTableStats::EMPTY);
    let next = LayoutTable::with_memo(&m, memo);
    assert_eq!(next.stats(), LayoutTableStats::EMPTY);
    assert_eq!(
        next.ty_layout(&Ty::U32),
        LayoutTable::new(&m).ty_layout(&Ty::U32)
    );
}
#[test]
fn every_observed_constructor_callback_refuses_without_partial_table_publication() {
    let m = fixture();
    let mut baseline = Observer::default();
    {
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
        let t = LayoutTable::new_observed(&m, &mut s, site()).unwrap();
        none(&t);
    }
    let end = baseline.events.len();
    for cut in 1..=end {
        let mut o = Observer {
            stop_at: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert!(matches!(
            LayoutTable::new_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(s.first_refusal().unwrap().cause, "interior");
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn memo_free_construction_uses_original_cumulative_work_and_copy_limits() {
    let m = fixture();
    let mut baseline = Observer::default();
    {
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
        let t = LayoutTable::new_observed(&m, &mut s, site()).unwrap();
        none(&t);
    }
    for copy in [false, true] {
        let cap = baseline
            .events
            .iter()
            .map(|e| if copy { e.copy_bytes } else { e.work })
            .sum();
        let mut o = Observer {
            work_limit: (!copy).then_some(cap),
            byte_limit: copy.then_some(cap),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let t = LayoutTable::new_observed(&m, &mut s, site()).unwrap();
        none(&t);
        assert!(matches!(
            LayoutTable::new_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "bytes" } else { "work" }
        );
        assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
#[test]
fn poisoned_ordinary_memo_is_discarded_and_recomputed_with_same_answers() {
    let m = fixture();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let t = LayoutTable::new_observed(&m, &mut s, site()).unwrap();
    let before = t.ty_layout(&Ty::U32).unwrap();
    let stopped = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _guard = t.memo.lock().unwrap();
        panic!("private ordinary memo poison fixture");
    }));
    assert!(stopped.is_err());
    assert_eq!(t.stats(), LayoutTableStats::EMPTY);
    none(&t);
    assert_eq!(*t.ty_layout(&Ty::U32).unwrap(), *before);
    some(&t);
}
