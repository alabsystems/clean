// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN integration of exhaustive owning-result retirement.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use std::{cell::Cell, rc::Rc};
#[derive(Default)]
struct OwnObserver {
    events: Vec<ExecutionProgress>,
    arm: Option<Rc<Cell<bool>>>,
    work: usize,
    cap: Option<usize>,
    next: Option<Rc<Cell<bool>>>,
}
impl ExecutionObserver for OwnObserver {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        if self.next.as_ref().is_some_and(|a| a.replace(false)) {
            return Err("allocation");
        }
        if self.arm.as_ref().is_some_and(|a| a.get())
            && e.phase == ExecutionPhase::ScratchRetirement
        {
            return Err("retirement");
        }
        self.work = self.work.checked_add(e.work).ok_or("overflow")?;
        if self.cap.is_some_and(|n| self.work > n) {
            return Err("work");
        }
        Ok(())
    }
}
fn own_site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(141))
}
fn shape() -> TyLayoutShape {
    TyLayoutShape {
        size_bits: 64,
        align_bits: Some(64),
        kind: TyLayoutKind::Struct {
            id: StructId::new(91),
            fields: vec![
                FieldOffsetShape {
                    field: 0,
                    name: "payload-λ".repeat(1000),
                    ty_shape: TyShape::Unit,
                    offset_bits: Some(0),
                },
                FieldOffsetShape {
                    field: 1,
                    name: "tail".repeat(1000),
                    ty_shape: TyShape::Unit,
                    offset_bits: None,
                },
            ],
        },
    }
}
fn enum_shape() -> EnumLayoutShape {
    EnumLayoutShape {
        id: EnumId::new(4),
        tag: EnumTagRepr::U128,
        tag_size_bits: 128,
        payload_offset_bits: 128,
        payload_size_bits: 128,
        size_bits: 256,
        align_bits: 128,
        discriminants: vec![i128::MIN, 0, i128::MAX],
        descriptor: Some(crate::EnumLayoutDescriptor {
            encoding: crate::EnumTagEncoding::Niche {
                untagged_variant: 0,
                niche_variants_start: 1,
                niche_variants_end: 2,
                niche_start: u128::MAX,
                niche_offset: 8,
                niche_ty: EnumTagRepr::U128,
            },
            size: 32,
            align: 16,
            variant_field_offsets: vec![vec![0; 1000], vec![], vec![16; 1000]],
        }),
    }
}
fn total_retirement(o: &OwnObserver) -> usize {
    o.events
        .iter()
        .filter(|e| e.phase == ExecutionPhase::ScratchRetirement)
        .map(|e| e.work)
        .sum()
}
#[test]
fn work_unique_ty_arc_consumes_full_field_names_with_nonzero_original_retirement_work() {
    let a = Arc::new(shape());
    let weak = Arc::downgrade(&a);
    let mut o = OwnObserver::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work::new(&mut s, own_site()).unwrap();
    work.retire_layout(a);
    assert!(weak.upgrade().is_none());
    assert!(work.poll().is_ok());
    work.retire_scratch();
    drop(work);
    assert!(s.first_refusal().is_none());
    drop(s);
    assert!(total_retirement(&o) >= 13000);
    assert!(o.events.iter().all(|e| e.site == own_site()));
}
#[test]
fn work_shared_ty_handle_leaves_other_owner_and_last_handle_consumes_payload_in_same_session() {
    let a = Arc::new(shape());
    let weak = Arc::downgrade(&a);
    let b = Arc::clone(&a);
    let mut o = OwnObserver::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work::new(&mut s, own_site()).unwrap();
    work.retire_layout(a);
    assert!(weak.upgrade().is_some());
    assert!(
        matches!(&b.kind,TyLayoutKind::Struct {fields,..} if fields[1].name=="tail".repeat(1000))
    );
    work.retire_layout(b);
    assert!(weak.upgrade().is_none());
    assert!(work.poll().is_ok());
    work.retire_scratch();
    drop(work);
    assert!(s.first_refusal().is_none());
    drop(s);
    assert!(total_retirement(&o) >= 13000);
}
#[test]
fn work_enum_arc_consumes_full_discriminants_descriptor_rows_and_every_encoding() {
    for encoding in [
        crate::EnumTagEncoding::Untagged,
        crate::EnumTagEncoding::Direct {
            tag_offset: u64::MAX,
        },
        enum_shape().descriptor.unwrap().encoding,
    ] {
        let mut value = enum_shape();
        value.descriptor.as_mut().unwrap().encoding = encoding;
        let a = Arc::new(value);
        let weak = Arc::downgrade(&a);
        let mut o = OwnObserver::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work::new(&mut s, own_site()).unwrap();
        work.retire_enum(a);
        assert!(weak.upgrade().is_none());
        assert!(work.poll().is_ok());
        work.retire_scratch();
        drop(work);
        assert!(s.first_refusal().is_none());
        drop(s);
        assert!(total_retirement(&o) > 16000);
    }
}
#[test]
fn work_shared_enum_retirement_keeps_borrowed_owner_then_consumes_the_unique_descriptor() {
    let a = Arc::new(enum_shape());
    let b = Arc::clone(&a);
    let weak = Arc::downgrade(&a);
    let mut o = OwnObserver::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work::new(&mut s, own_site()).unwrap();
    work.retire_enum(a);
    assert!(weak.upgrade().is_some());
    assert_eq!(
        b.descriptor.as_ref().unwrap().variant_field_offsets[2].len(),
        1000
    );
    work.retire_enum(b);
    assert!(weak.upgrade().is_none());
    assert!(work.poll().is_ok());
    work.retire_scratch();
    drop(work);
    assert!(s.first_refusal().is_none());
    drop(s);
    assert!(total_retirement(&o) > 16000);
}
#[test]
fn work_layout_errors_consume_owned_target_and_fixed_errors_without_generic_drop_fallback() {
    let mut o = OwnObserver::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work::new(&mut s, own_site()).unwrap();
    work.retire_error(Error::Layout(LayoutError::TargetScalarLayoutUnavailable {
        triple: "owned-λ".repeat(2000),
    }));
    work.retire_error(Error::Layout(LayoutError::MissingType(TyId::new(u32::MAX))));
    work.retire_error(Error::Resource(ObservedValueError::InvalidRange));
    assert!(work.poll().is_ok());
    work.retire_scratch();
    drop(work);
    assert!(s.first_refusal().is_none());
    drop(s);
    assert!(total_retirement(&o) >= 16000);
}
#[test]
fn sticky_private_cache_retirement_consumes_every_owned_ty_and_enum_arc() {
    let arm = Rc::new(Cell::new(false));
    let mut o = OwnObserver {
        arm: Some(arm.clone()),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work::new(&mut s, own_site()).unwrap();
    let a = Arc::new(shape());
    let b = Arc::new(enum_shape());
    let aw = Arc::downgrade(&a);
    let bw = Arc::downgrade(&b);
    work.value = Some(Arc::clone(&a));
    work.cache.insert((0, 0), a);
    work.enums.insert(0, b);
    arm.set(true);
    work.retire_scratch();
    assert!(aw.upgrade().is_none());
    assert!(bw.upgrade().is_none());
    assert!(work.value.is_none() && work.cache.is_empty() && work.enums.is_empty());
    assert!(matches!(
        work.poll(),
        Err(Error::Resource(ObservedValueError::AdmissionRefused))
    ));
    drop(work);
    assert_eq!(s.first_refusal().unwrap().cause, "retirement");
    drop(s);
    assert!(
        o.events
            .iter()
            .filter(|e| e.phase == ExecutionPhase::ScratchRetirement)
            .count()
            > 2000
    );
}
#[test]
fn refused_arc_allocation_consumes_the_original_owning_enum_shape_before_returning() {
    let next = Rc::new(Cell::new(false));
    let mut o = OwnObserver {
        next: Some(next.clone()),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work::new(&mut s, own_site()).unwrap();
    next.set(true);
    assert!(matches!(
        work.arc_enum(enum_shape()),
        Err(Error::Resource(ObservedValueError::AdmissionRefused))
    ));
    work.retire_scratch();
    drop(work);
    assert_eq!(s.first_refusal().unwrap().cause, "allocation");
    drop(s);
    assert!(total_retirement(&o) > 16000);
}
#[test]
fn real_public_query_success_and_semantic_error_match_ordinary_after_inner_retirement_change() {
    let m = fixture();
    let mut o = OwnObserver::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let table = LayoutTable::new_observed(&m, &mut s, own_site()).unwrap();
    for ty in [
        Ty::Struct(StructId::new(91)),
        Ty::U128,
        Ty::Struct(StructId::new(999)),
    ] {
        let actual = table.ty_layout_observed(&ty, &mut s, own_site()).unwrap();
        let expected = m.layout_table().ty_layout(&ty);
        match (actual, expected) {
            (Ok(shape), Ok(expected)) => {
                assert_eq!(*shape, *expected);
                shape.retire_arc_observed(&mut s, own_site()).unwrap();
            }
            (Err(error), Err(expected)) => {
                assert_eq!(error, expected);
                error.retire_observed(&mut s, own_site()).unwrap();
            }
            _ => panic!("parity"),
        }
    }
    assert!(s.first_refusal().is_none());
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
}
#[test]
fn cumulative_retirement_work_refuses_without_reset_and_still_consumes_the_second_owner() {
    let baseline = {
        let mut o = OwnObserver::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut work = Work::new(&mut s, own_site()).unwrap();
        work.retire_layout(Arc::new(shape()));
        assert!(work.poll().is_ok());
        work.retire_scratch();
        drop(work);
        drop(s);
        o.work
    };
    let mut o = OwnObserver {
        cap: Some(baseline),
        ..Default::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut work = Work::new(&mut s, own_site()).unwrap();
    work.retire_layout(Arc::new(shape()));
    assert!(work.poll().is_ok());
    let second = Arc::new(shape());
    let weak = Arc::downgrade(&second);
    work.retire_layout(second);
    assert!(weak.upgrade().is_none());
    assert!(matches!(
        work.poll(),
        Err(Error::Resource(ObservedValueError::AdmissionRefused))
    ));
    work.retire_scratch();
    drop(work);
    assert_eq!(s.first_refusal().unwrap().cause, "work");
    assert_eq!(s.remaining_fuel(), InterpretOptions::default().fuel);
}
