// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

#[test]
fn all_twenty_three_variants_match_ordinary_messages_at_id_extremes() {
    for n in [0, 1, u32::MAX] {
        for error in fixtures::errors(n) {
            parity(&error);
        }
    }
    assert_eq!(
        parity(&LayoutError::MissingType(TyId::new(0))),
        "type table entry ty.0 is missing"
    );
    assert_eq!(
        parity(&LayoutError::ClosureLayoutIncoherent(ClosureTyId::new(
            u32::MAX
        ))),
        "closure layout closure.4294967295 has incoherent or ambiguous declared metadata"
    );
}

#[test]
fn every_tyshape_spelling_in_all_shape_positions_matches_the_original() {
    let shapes = fixtures::shapes();
    for shape in shapes {
        parity(&LayoutError::UnsupportedTyShape(shape));
        parity(&LayoutError::NotPointer(shape));
        parity(&LayoutError::NotFunctionPointerSource(shape));
        for (src, dst) in [(shape, TyShape::ThinPointer), (TyShape::Bool, shape)] {
            parity(&LayoutError::OpaqueHandleCast { src, dst });
            parity(&LayoutError::BoolLaneReinterpret { src, dst });
            parity(&LayoutError::ClosureCast { src, dst });
        }
    }
}

#[test]
fn signed_unsigned_pointer_and_float_shape_parameters_keep_zero_and_maximum() {
    for bits in [0, 1, u32::MAX] {
        for signed in [false, true] {
            parity(&LayoutError::NotPointer(TyShape::Int { signed, bits }));
            parity(&LayoutError::NotPointer(TyShape::PointerInt { signed }));
        }
        parity(&LayoutError::NotPointer(TyShape::Float { bits }));
    }
}

#[test]
fn metadata_uses_option_and_struct_debug_including_typed_id_not_display() {
    for src in fixtures::metadata() {
        for dst in fixtures::metadata() {
            parity(&LayoutError::PointerMetadataMismatch { src, dst });
        }
    }
    assert_eq!(
        parity(&LayoutError::PointerMetadataMismatch {
            src: None,
            dst: Some(PointerMetadataShape::SliceLen {
                elem: TyId::new(u32::MAX)
            })
        }),
        "pointer cast changes metadata from None to Some(SliceLen { elem: TyId(4294967295) })"
    );
    assert_eq!(
        parity(&LayoutError::PointerMetadataMismatch {
            src: Some(PointerMetadataShape::VTable { trait_id: 0 }),
            dst: Some(PointerMetadataShape::ContainerVtable)
        }),
        "pointer cast changes metadata from Some(VTable { trait_id: 0 }) to Some(ContainerVtable)"
    );
}

#[test]
fn decimal_lane_and_bit_width_extremes_are_never_truncated_or_signed() {
    for src_lanes in [0, 1, u8::MAX] {
        for dst_lanes in [0, 1, u8::MAX] {
            parity(&LayoutError::PointerLaneMismatch {
                src_lanes,
                dst_lanes,
            });
        }
    }
    for src_bits in [0, 1, u64::from(u32::MAX), u64::MAX] {
        for dst_bits in [0, 1, u64::from(u32::MAX), u64::MAX] {
            parity(&LayoutError::CastSizeMismatch { src_bits, dst_bits });
        }
    }
    assert_eq!(
        parity(&LayoutError::CastSizeMismatch {
            src_bits: u64::MAX,
            dst_bits: 0
        }),
        "cast layout sizes differ: 18446744073709551615b -> 0b"
    );
}

#[test]
fn quoted_triples_preserve_apostrophes_controls_combining_and_unicode_debug() {
    for text in [
        "",
        "x86_64-unknown-linux-gnu",
        "'\"\\\n\r\t\0\u{7f}",
        "λé中😀",
        "a\u{301}\u{200d}\u{2028}\u{e000}\u{10ffff}",
    ] {
        parity(&triple(text));
    }
    assert_eq!(
        parity(&triple("'\"\n")),
        "target \"'\\\"\\n\" is outside TrustIR's canonical scalar-layout set"
    );
}

#[test]
fn long_owned_triple_reads_and_copies_each_real_scalar_without_changing_input() {
    let text = "λ'\n😀".repeat(1300);
    let error = triple(&text);
    let actual = parity(&error);
    let LayoutError::TargetScalarLayoutUnavailable { triple } = error else {
        unreachable!()
    };
    assert_eq!(triple, text);
    assert!(actual.len() > triple.len());
    let (_, observer) = run(&LayoutError::TargetScalarLayoutUnavailable { triple });
    assert_eq!(
        observer
            .events
            .iter()
            .filter(|e| e.work == 4 && e.copy_bytes == 2 * size_of::<char>())
            .count(),
        4 * 1300 + 1
    );
}

#[test]
fn every_variant_has_consuming_retirement_then_only_terminal_zero_cost_publication() {
    for error in fixtures::errors(u32::MAX) {
        let observer = retirement(error);
        assert!(observer.events.iter().all(|e| e.site == site()));
        let (last, before) = observer.events.split_last().unwrap();
        assert_eq!(
            (last.phase, last.work, last.copy_bytes),
            (ExecutionPhase::Publication, 0, 0)
        );
        assert!(
            before
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement && e.copy_bytes == 0)
        );
        assert_eq!(before.first().unwrap().work, size_of::<LayoutError>() + 1);
    }
}

#[test]
fn consuming_field_costs_cover_both_fixed_fields_and_actual_owned_text_length() {
    let observer = retirement(LayoutError::MissingFieldOffset {
        struct_id: StructId::new(7),
        field: 9,
    });
    assert_eq!(
        observer.events.iter().map(|e| e.work).collect::<Vec<_>>(),
        vec![
            size_of::<LayoutError>() + 1,
            size_of::<StructId>() + 1,
            size_of::<u32>() + 1,
            0,
            0
        ]
    );
    let observer = retirement(triple(&"λ".repeat(6000)));
    assert_eq!(
        observer.events.iter().map(|e| e.work).collect::<Vec<_>>(),
        vec![
            size_of::<LayoutError>() + 1,
            12000 + size_of::<String>() + 1,
            0,
            0,
            0
        ]
    );
    let observer = retirement(LayoutError::PointerMetadataMismatch {
        src: None,
        dst: Some(PointerMetadataShape::StrLen),
    });
    assert_eq!(
        observer.events.iter().map(|e| e.work).collect::<Vec<_>>(),
        vec![
            size_of::<LayoutError>() + 1,
            size_of::<Option<PointerMetadataShape>>() + 1,
            size_of::<Option<PointerMetadataShape>>() + 1,
            0,
            0
        ]
    );
}
