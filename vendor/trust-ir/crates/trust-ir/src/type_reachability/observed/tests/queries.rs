// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn direct_seeds_missing_references_and_untyped_pointer_remain_three_distinct_axes() {
    parity(
        &Module::new(""),
        &[
            dialect(),
            handle(),
            Ty::Ptr,
            Ty::Error,
            Ty::Func(FuncTyId::new(u32::MAX)),
            Ty::Closure(ClosureTyId::new(u32::MAX)),
            Ty::Struct(StructId::new(u32::MAX)),
            Ty::FatPtr(crate::FatPtrKind::TraitObject { trait_id: 7 }),
            Ty::FatPtr(crate::FatPtrKind::ContainerVtable),
            Ty::FatPtr(crate::FatPtrKind::ContainerLen),
        ],
    );
}
#[test]
fn instruction_results_frame_slots_and_type_attributes_match_actual_original_visitor() {
    let m = fixture();
    let mut op = crate::dialect::DialectInst::new("opaque", "typed");
    op.result_tys = vec![array(0), Ty::Bool];
    op.attrs = vec![
        crate::dialect::AttrEntry {
            name: "ignored name".into(),
            value: crate::dialect::AttrValue::Bytes(vec![0; 4096]),
        },
        crate::dialect::AttrEntry {
            name: "typed".into(),
            value: crate::dialect::AttrValue::Ty(array(2)),
        },
    ];
    let frame = Inst::OpenFrame {
        def: crate::inst::BindingFrameDef::new(
            crate::value::BindingFrameId::new(7),
            "frame",
            vec![
                crate::inst::BindingSlot::new("a", array(0)),
                crate::inst::BindingSlot::new("b", array(2)),
            ],
        ),
    };
    let original = m.nominal_type_reachability();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = m
        .nominal_type_reachability_observed(&mut s, site())
        .unwrap();
    for inst in [
        Inst::DialectOp(Box::new(op)),
        frame,
        Inst::Undef { ty: array(0) },
        Inst::NullPtr,
    ] {
        assert_eq!(
            out.contains_dialect_instruction_types_observed(&inst, &mut s, site())
                .unwrap(),
            original.contains_dialect_instruction_types(&inst)
        );
        assert_eq!(
            out.contains_handle_instruction_types_observed(&inst, &mut s, site())
                .unwrap(),
            original.contains_handle_instruction_types(&inst)
        );
    }
    out.retire_observed(&mut s, site()).unwrap();
}
#[test]
fn known_true_query_still_walks_and_can_refuse_in_the_actual_inline_tail() {
    let m = Module::new("");
    let root = Ty::Tuple(
        core::iter::once(dialect())
            .chain((0..64).map(|_| Ty::Bool))
            .collect(),
    );
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = m
        .nominal_type_reachability_observed(&mut s, site())
        .unwrap();
    let start = calls.get();
    assert!(
        out.contains_dialect_observed(&root, &mut s, site())
            .unwrap()
    );
    let end = calls.get();
    out.retire_observed(&mut s, site()).unwrap();
    drop(s);
    let candidates: Vec<_> = o.events[start..end]
        .iter()
        .enumerate()
        .filter(|(_, e)| e.phase == ExecutionPhase::Validation)
        .map(|(i, _)| start + i + 1)
        .collect();
    let cut = candidates[candidates.len() / 2];
    assert!(cut > start + 64);
    let mut stopped = Observer {
        stop: Some(cut),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut stopped);
    let out = m
        .nominal_type_reachability_observed(&mut s, site())
        .unwrap();
    assert_eq!(
        out.contains_dialect_observed(&root, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        out.retire_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    drop(s);
    assert_eq!(&stopped.events[..cut], &o.events[..cut]);
    assert!(
        stopped.events[cut..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn deep_inline_query_is_iterative_and_external_fixture_disposal_is_explicit() {
    let m = Module::new("");
    let mut root = handle();
    for _ in 0..2048 {
        root = Ty::Ref(Box::new(root));
    }
    parity(&m, core::slice::from_ref(&root));
    // Input ownership is outside the observed query. Do not hide recursive
    // fixture destruction or claim it is a production disposal proof.
    loop {
        match root {
            Ty::Ref(inner) => root = *inner,
            other => {
                drop(other);
                break;
            }
        }
    }
}
