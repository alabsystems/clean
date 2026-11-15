// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) fn field(name: &str) -> FieldOffsetShape {
    FieldOffsetShape {
        field: u32::MAX,
        name: name.into(),
        ty_shape: TyShape::Int {
            signed: true,
            bits: u32::MAX,
        },
        offset_bits: Some(u64::MAX),
    }
}
pub(super) fn ty_shape(kind: TyLayoutKind) -> TyLayoutShape {
    TyLayoutShape {
        size_bits: u64::MAX,
        align_bits: Some(0),
        kind,
    }
}
pub(super) fn ty_shapes() -> Vec<TyLayoutShape> {
    // One constructor per actual ordinary TyLayoutKind variant, no wildcard.
    vec![
        TyLayoutKind::Scalar(TyShape::Float { bits: u32::MAX }),
        TyLayoutKind::ThinPointer,
        TyLayoutKind::FatPointer(PointerMetadataShape::SliceLen {
            elem: TyId::new(u32::MAX),
        }),
        TyLayoutKind::Struct {
            id: StructId::new(9),
            fields: vec![field("λ"), field("named-tail")],
        },
        TyLayoutKind::Enum {
            id: EnumId::new(10),
            variants: usize::MAX,
        },
        TyLayoutKind::Array {
            elem: TyId::new(11),
            len: u64::MAX,
            stride_bits: u64::MAX,
        },
        TyLayoutKind::Vector {
            elem_shape: TyShape::Bool,
            lanes: u32::MAX,
            lane_bits: u64::MAX,
        },
        TyLayoutKind::Unit,
        TyLayoutKind::Never,
        TyLayoutKind::Tuple {
            fields: vec![field("tuple-λ")],
        },
        TyLayoutKind::Closure {
            id: ClosureTyId::new(12),
            captures: vec![field("capture-λ")],
        },
    ]
    .into_iter()
    .map(ty_shape)
    .collect()
}
pub(super) fn encodings() -> Vec<EnumTagEncoding> {
    vec![
        EnumTagEncoding::Direct {
            tag_offset: u64::MAX,
        },
        EnumTagEncoding::Niche {
            untagged_variant: u32::MAX,
            niche_variants_start: 9,
            niche_variants_end: 0,
            niche_start: u128::MAX,
            niche_offset: u64::MAX,
            niche_ty: EnumTagRepr::I128,
        },
        EnumTagEncoding::Untagged,
        EnumTagEncoding::SingleInhabited { variant: u32::MAX },
    ]
}
pub(super) fn enum_shape(encoding: Option<EnumTagEncoding>) -> EnumLayoutShape {
    EnumLayoutShape {
        id: EnumId::new(u32::MAX),
        tag: EnumTagRepr::U128,
        tag_size_bits: 128,
        payload_offset_bits: u64::MAX,
        payload_size_bits: u64::MAX,
        size_bits: u64::MAX,
        align_bits: 0,
        discriminants: vec![i128::MIN, 0, i128::MAX],
        descriptor: encoding.map(|encoding| EnumLayoutDescriptor {
            encoding,
            size: u64::MAX,
            align: 0,
            variant_field_offsets: vec![vec![1, u64::MAX, 0], vec![], vec![9]],
        }),
    }
}

pub(super) fn expected_enum_work(shape: &EnumLayoutShape) -> Vec<usize> {
    // Independent field inventory fixes the new logical cleanup receipt. No
    // production helper supplies this expected trace; values are not validated.
    let mut out = vec![
        size_of::<EnumLayoutShape>() + 1,
        size_of::<EnumId>() + 1,
        size_of::<EnumTagRepr>() + 1,
    ];
    out.extend([size_of::<u64>() + 1; 5]);
    scalar_work::<i128>(shape.discriminants.len(), &mut out);
    out.push(size_of::<Option<EnumLayoutDescriptor>>() + 1);
    if let Some(descriptor) = &shape.descriptor {
        out.push(size_of::<EnumLayoutDescriptor>() + 1);
        out.push(size_of::<EnumTagEncoding>() + 1);
        match &descriptor.encoding {
            EnumTagEncoding::Direct { tag_offset: _ } => out.push(size_of::<u64>() + 1),
            EnumTagEncoding::Niche {
                untagged_variant: _,
                niche_variants_start: _,
                niche_variants_end: _,
                niche_start: _,
                niche_offset: _,
                niche_ty: _,
            } => {
                out.extend([size_of::<u32>() + 1; 3]);
                out.extend([
                    size_of::<u128>() + 1,
                    size_of::<u64>() + 1,
                    size_of::<EnumTagRepr>() + 1,
                ]);
            }
            EnumTagEncoding::Untagged => out.push(1),
            EnumTagEncoding::SingleInhabited { variant: _ } => out.push(size_of::<u32>() + 1),
        }
        out.extend([size_of::<u64>() + 1; 2]);
        for row in descriptor.variant_field_offsets.iter().rev() {
            out.push(size_of::<Option<Vec<u64>>>() + 1);
            scalar_work::<u64>(row.len(), &mut out);
        }
        out.extend([
            size_of::<Option<Vec<u64>>>() + 1,
            size_of::<Vec<Vec<u64>>>() + 1,
            0,
        ]);
    } else {
        out.push(1);
    }
    out.push(0);
    out
}
fn scalar_work<T: Copy>(count: usize, out: &mut Vec<usize>) {
    for _ in 0..count {
        out.extend([size_of::<Option<T>>() + 1, size_of::<T>() + 1]);
    }
    out.extend([size_of::<Option<T>>() + 1, size_of::<Vec<T>>() + 1, 0]);
}
