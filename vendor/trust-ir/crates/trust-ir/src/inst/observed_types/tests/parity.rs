// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;

#[test]
fn every_current_instruction_has_a_constructor_witness_and_original_pointer_parity() {
    let mut shapes = std::collections::BTreeSet::new();
    for instruction in witnesses::all() {
        assert!(shapes.insert(instruction.shape()));
        parity(&instruction);
    }
    assert_eq!(shapes, InstShape::ALL.iter().copied().collect());
}
#[test]
fn cast_and_pointer_pairs_keep_exact_borrowed_field_order_even_for_equal_types() {
    for instruction in [
        Inst::Cast {
            op: CastOp::Bitcast,
            src_ty: Ty::U32,
            dst_ty: Ty::F32,
            operand: v(),
        },
        Inst::PtrMetadata {
            ptr_ty: Ty::Ptr,
            metadata_ty: Ty::Usize,
            ptr: v(),
        },
        Inst::PtrFromParts {
            ptr_ty: Ty::U32,
            metadata_ty: Ty::U32,
            data: v(),
            metadata: v(),
        },
    ] {
        let types = parity(&instruction);
        assert_eq!(types.len(), 2);
        assert!(!core::ptr::eq(types[0], types[1]));
    }
}
#[test]
fn slot_and_dialect_type_references_keep_order_and_equal_payloads_distinct() {
    for instruction in [frame(7), dialect(7)] {
        let types = parity(&instruction);
        assert_eq!(types.len(), 7);
        for pair in types.windows(2) {
            assert!(!core::ptr::eq(pair[0], pair[1]));
        }
    }
}
#[test]
fn nested_inline_types_and_constant_payloads_add_no_hidden_walk_or_clone() {
    let shallow = Inst::Const {
        ty: Ty::U32,
        value: Constant::Int(0),
    };
    let mut deep = Ty::Tuple(vec![Ty::U32; 20_000]);
    for _ in 0..20 {
        deep = Ty::Tuple(vec![deep]);
    }
    let deep = Inst::Const {
        ty: deep,
        value: Constant::Aggregate(vec![Constant::Int(0); 20_000]),
    };
    let (a, shallow_observer) = observed(&shallow);
    let (b, deep_observer) = observed(&deep);
    assert_eq!((a.len(), b.len()), (1, 1));
    assert_eq!(shallow_observer.events, deep_observer.events);
    parity(&deep);
}
#[test]
fn frame_names_and_dialect_names_operands_attributes_are_outside_the_type_scan() {
    let a = frame(3);
    let mut b = frame(3);
    if let Inst::OpenFrame { def } = &mut b {
        def.name = "λ".repeat(20_000);
        for slot in &mut def.slots {
            slot.name = "slot".repeat(20_000);
        }
    }
    assert_eq!(observed(&a).1.events, observed(&b).1.events);
    let a = dialect(3);
    let mut b = dialect(3);
    if let Inst::DialectOp(op) = &mut b {
        op.dialect = "namespace".repeat(20_000);
        op.op = "operation".repeat(20_000);
        op.operands = vec![v(); 20_000];
        op.version = u32::MAX;
        // Attribute types are not declared result types in the original rule.
        op.attrs.push(crate::dialect::AttrEntry {
            name: "opaque".repeat(20_000),
            value: crate::dialect::AttrValue::Ty(Ty::Tuple(vec![Ty::U32; 20_000])),
        });
    }
    assert_eq!(observed(&a).1.events, observed(&b).1.events);
    parity(&b);
}
#[test]
fn empty_variable_surfaces_still_observe_the_actual_exhausted_probe() {
    let empty_instruction = Inst::NullPtr;
    let slot_instruction = frame(0);
    let type_instruction = dialect(0);
    let (_, empty) = observed(&empty_instruction);
    let (a, slots) = observed(&slot_instruction);
    let (b, types) = observed(&type_instruction);
    assert!(a.is_empty() && b.is_empty());
    assert_eq!(slots.events, types.events);
    assert_eq!(slots.events.len(), empty.events.len() + 2);
}
#[test]
fn wide_actual_slot_and_dialect_type_sequences_match_retained_original_rule() {
    for instruction in [frame(1024), dialect(1024)] {
        assert_eq!(parity(&instruction).len(), 1024);
    }
}
#[test]
fn returned_borrows_outlive_observer_and_session_but_still_name_the_original_input() {
    let instruction = Inst::Undef {
        ty: Ty::Tuple(vec![Ty::U32; 100]),
    };
    let types;
    {
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        types = instruction
            .inline_types_observed(&mut session, site())
            .unwrap();
    }
    let Inst::Undef { ty } = &instruction else {
        unreachable!()
    };
    assert!(core::ptr::eq(types[0], ty));
}
