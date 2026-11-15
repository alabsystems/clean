// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

#[test]
fn every_current_kind_is_consumed_without_a_variable_payload_fallback() {
    let shapes = ty_shapes();
    assert_eq!(shapes.len(), 11);
    for shape in shapes {
        let observer = trace(Sample::Ty(shape), false);
        assert!(observer.work > size_of::<TyLayoutShape>() + size_of::<TyLayoutKind>());
    }
}
#[test]
fn struct_tuple_and_closure_retire_all_actual_unicode_name_bytes() {
    for which in 0..3 {
        let names = ["λ".repeat(4097), "中".repeat(8001), "tail".repeat(15000)];
        let fields = names.iter().map(|name| field(name)).collect();
        let kind = match which {
            0 => TyLayoutKind::Struct {
                id: StructId::new(0),
                fields,
            },
            1 => TyLayoutKind::Tuple { fields },
            2 => TyLayoutKind::Closure {
                id: ClosureTyId::new(0),
                captures: fields,
            },
            _ => unreachable!(),
        };
        let observer = trace(Sample::Ty(ty_shape(kind)), false);
        let mut positions = Vec::new();
        for name in names {
            assert_eq!(
                count_work(&observer, name.len() + size_of::<String>() + 1),
                1
            );
            let at = observer
                .events
                .iter()
                .position(|e| e.work == name.len() + size_of::<String>() + 1)
                .unwrap();
            positions.push(at);
            assert_eq!(
                observer.events[at - 3].work,
                size_of::<Option<FieldOffsetShape>>() + 1
            );
            assert_eq!(
                observer.events[at - 2].work,
                size_of::<FieldOffsetShape>() + 1
            );
            assert_eq!(observer.events[at - 1].work, size_of::<u32>() + 1);
            assert_eq!(observer.events[at + 1].work, 0);
            assert_eq!(observer.events[at + 2].work, size_of::<TyShape>() + 1);
            assert_eq!(observer.events[at + 3].work, size_of::<Option<u64>>() + 1);
        }
        assert!(positions.windows(2).all(|pair| pair[0] > pair[1]));
    }
}
#[test]
fn enum_discriminants_and_every_nested_descriptor_offset_are_individually_consumed() {
    for encoding in encodings() {
        let shape = enum_shape(Some(encoding));
        let expected = expected_enum_work(&shape);
        let observer = trace(Sample::Enum(shape), false);
        assert_eq!(
            observer.events[..observer.events.len() - 1]
                .iter()
                .map(|e| e.work)
                .collect::<Vec<_>>(),
            expected
        );
    }
}
#[test]
fn absent_descriptor_and_empty_allocated_children_retain_distinct_cleanup_paths() {
    let none = enum_shape(None);
    let expected = expected_enum_work(&none);
    let observer = trace(Sample::Enum(none), false);
    assert_eq!(
        observer.events[..observer.events.len() - 1]
            .iter()
            .map(|e| e.work)
            .collect::<Vec<_>>(),
        expected
    );
    let mut shape = enum_shape(Some(EnumTagEncoding::Untagged));
    shape.discriminants = Vec::with_capacity(97);
    let descriptor = shape.descriptor.as_mut().unwrap();
    descriptor.variant_field_offsets = vec![Vec::with_capacity(99), Vec::with_capacity(101)];
    let expected = expected_enum_work(&shape);
    let some = trace(Sample::Enum(shape), false);
    assert_eq!(
        some.events[..some.events.len() - 1]
            .iter()
            .map(|e| e.work)
            .collect::<Vec<_>>(),
        expected
    );
}
#[test]
fn retirement_consumes_malformed_fixed_layout_values_without_semantic_admission() {
    let zero = ty_shape(TyLayoutKind::Array {
        elem: TyId::new(0),
        len: 0,
        stride_bits: 0,
    });
    let max = ty_shape(TyLayoutKind::Array {
        elem: TyId::new(u32::MAX),
        len: u64::MAX,
        stride_bits: u64::MAX,
    });
    let a = trace(Sample::Ty(zero), false);
    let b = trace(Sample::Ty(max), false);
    assert_eq!(a.events, b.events);
    for encoding in encodings() {
        trace(Sample::Enum(enum_shape(Some(encoding))), false);
    }
}
#[test]
fn only_terminal_zero_cost_publication_follows_all_positive_cleanup_and_polls() {
    for sample in [
        Sample::Ty(ty_shapes().remove(3)),
        Sample::Enum(enum_shape(Some(encodings().remove(1)))),
    ] {
        for arc in [false, true] {
            let observer = trace(sample.clone(), arc);
            assert_eq!(
                observer
                    .events
                    .iter()
                    .filter(|e| e.phase == ExecutionPhase::Publication)
                    .count(),
                1
            );
            assert!(
                observer
                    .events
                    .iter()
                    .any(|e| e.phase == ExecutionPhase::ScratchRetirement && e.work > 0)
            );
            assert_eq!(observer.bytes, 0);
        }
    }
}
