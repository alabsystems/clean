// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Authored UNRUN controls for actual pending walk-frame consumption.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
use crate::interpret::InterpretOptions;
use std::{cell::Cell, rc::Rc};

struct FrameObserver {
    events: Vec<ExecutionProgress>,
    arm: Rc<Cell<bool>>,
}
impl ExecutionObserver for FrameObserver {
    type Refusal = &'static str;
    fn admit(&mut self, e: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(e);
        if self.arm.get() && e.phase == ExecutionPhase::ScratchRetirement {
            Err("frame cleanup")
        } else {
            Ok(())
        }
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(crate::FuncId::new(153))
}

#[test]
fn fixed_pending_frames_are_copy_guarded_and_consumed_after_the_first_refusal() {
    let arm = Rc::new(Cell::new(false));
    let mut o = FrameObserver {
        events: Vec::new(),
        arm: arm.clone(),
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work::new(&mut s, site()).unwrap();
    let ty = Ty::U8;
    let frames = vec![
        Frame::Vector {
            elem: &ty,
            lanes: u32::MAX,
        },
        Frame::Array {
            elem: TyId::new(99),
            len: u64::MAX,
        },
        Frame::Entry((2, usize::MAX)),
    ];
    arm.set(true);
    w.retire_frames(frames);
    assert!(w.poll().is_err());
    drop(w);
    assert_eq!(s.first_refusal().unwrap().cause, "frame cleanup");
    drop(s);
    assert!(
        o.events
            .iter()
            .filter(|e| e.phase == ExecutionPhase::ScratchRetirement && e.work > 0)
            .count()
            >= 8
    );
    assert!(o.events.iter().all(|e| e.site == site()));
}

#[test]
fn aggregate_frame_drains_actual_copied_long_field_names_after_stop() {
    let mut m = Module::new("frame name");
    m.structs.push(StructDef {
        id: StructId::new(1),
        name: "s".into(),
        fields: vec![FieldDef {
            name: "λ".repeat(3000),
            ty: Ty::U8,
            offset: Some(0),
        }],
        size: Some(1),
        align: Some(1),
        repr: StructRepr::Rust,
        origin: None,
    });
    let arm = Rc::new(Cell::new(false));
    let mut o = FrameObserver {
        events: Vec::new(),
        arm: arm.clone(),
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work::new(&mut s, site()).unwrap();
    let mut a = Aggregate::begin(&m, (0, 0)).ok().unwrap();
    let layout = TyLayoutShape {
        size_bits: 8,
        align_bits: Some(8),
        kind: TyLayoutKind::Scalar(TyShape::Int {
            signed: false,
            bits: 8,
        }),
    };
    assert!(a.take(&layout, &mut w).is_ok());
    arm.set(true);
    w.retire_frames(vec![Frame::Aggregate(a)]);
    assert!(w.poll().is_err());
    drop(w);
    assert_eq!(s.first_refusal().unwrap().cause, "frame cleanup");
    drop(s);
    assert!(
        o.events
            .iter()
            .any(|e| e.phase == ExecutionPhase::ScratchRetirement
                && e.work == 6000 + size_of::<String>() + 1)
    );
}

#[test]
fn real_pending_enum_frame_retires_all_discriminants_even_when_cleanup_is_refused() {
    let mut m = Module::new("enum frame");
    m.enums.push(EnumDef::new(
        EnumId::new(3),
        "e",
        vec![
            EnumVariant {
                name: "a".into(),
                fields: vec![Ty::U8],
                field_names: Vec::new(),
            },
            EnumVariant {
                name: "b".into(),
                fields: Vec::new(),
                field_names: Vec::new(),
            },
        ],
    ));
    let arm = Rc::new(Cell::new(false));
    let mut o = FrameObserver {
        events: Vec::new(),
        arm: arm.clone(),
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let table = LayoutTable::new_observed(&m, &mut s, site()).unwrap();
    let mut w = Work::new(&mut s, site()).unwrap();
    let frame = enums::Frame::begin(&table, 0, &mut w).ok().unwrap();
    arm.set(true);
    w.retire_frames(vec![Frame::Enum(frame)]);
    assert!(w.poll().is_err());
    drop(w);
    assert_eq!(s.first_refusal().unwrap().cause, "frame cleanup");
    drop(s);
    assert!(
        o.events
            .iter()
            .filter(
                |e| e.phase == ExecutionPhase::ScratchRetirement && e.work == size_of::<i128>() + 1
            )
            .count()
            >= 2
    );
}
