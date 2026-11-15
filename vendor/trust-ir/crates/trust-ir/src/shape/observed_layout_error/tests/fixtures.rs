// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

pub(super) fn errors(n: u32) -> [LayoutError; 23] {
    [
        LayoutError::MissingType(TyId::new(n)),
        LayoutError::MissingStruct(StructId::new(n)),
        LayoutError::MissingStructSize(StructId::new(n)),
        LayoutError::MissingStructAlign(StructId::new(n)),
        LayoutError::StructLayoutIncoherent(StructId::new(n)),
        LayoutError::TupleLayoutIncoherent(TyId::new(n)),
        LayoutError::TupleLayoutTargetMissing,
        LayoutError::ClosureLayoutIncoherent(ClosureTyId::new(n)),
        LayoutError::ClosureLayoutTargetMissing,
        triple("λ\n'\"\\\0"),
        LayoutError::MissingFieldOffset {
            struct_id: StructId::new(n),
            field: n,
        },
        LayoutError::EnumLayoutUnavailable(EnumId::new(n)),
        LayoutError::TyLayoutCycle(TyId::new(n)),
        LayoutError::UnsupportedTyShape(TyShape::Int {
            signed: false,
            bits: n,
        }),
        LayoutError::SizeOverflow,
        LayoutError::NotPointer(TyShape::PointerInt { signed: true }),
        LayoutError::OpaqueHandleCast {
            src: TyShape::Handle,
            dst: TyShape::ThinPointer,
        },
        LayoutError::BoolLaneReinterpret {
            src: TyShape::Vector,
            dst: TyShape::Bool,
        },
        LayoutError::ClosureCast {
            src: TyShape::Closure,
            dst: TyShape::Function,
        },
        LayoutError::PointerLaneMismatch {
            src_lanes: 0,
            dst_lanes: u8::MAX,
        },
        LayoutError::PointerMetadataMismatch {
            src: Some(PointerMetadataShape::SliceLen { elem: TyId::new(n) }),
            dst: Some(PointerMetadataShape::VTable { trait_id: n }),
        },
        LayoutError::NotFunctionPointerSource(TyShape::Dialect),
        LayoutError::CastSizeMismatch {
            src_bits: 0,
            dst_bits: u64::MAX,
        },
    ]
}
pub(super) fn shapes() -> [TyShape; 28] {
    [
        TyShape::Int {
            signed: true,
            bits: 0,
        },
        TyShape::PointerInt { signed: false },
        TyShape::Error,
        TyShape::Float { bits: u32::MAX },
        TyShape::Bool,
        TyShape::ThinPointer,
        TyShape::FatPointer,
        TyShape::Unit,
        TyShape::Never,
        TyShape::Struct,
        TyShape::Array,
        TyShape::Vector,
        TyShape::Tuple,
        TyShape::Enum,
        TyShape::Function,
        TyShape::Ref,
        TyShape::RefMut,
        TyShape::PtrConst,
        TyShape::PtrMut,
        TyShape::Rc,
        TyShape::Set,
        TyShape::Sequence,
        TyShape::Record,
        TyShape::Closure,
        TyShape::Refine,
        TyShape::Dialect,
        TyShape::Handle,
        TyShape::Tensor,
    ]
}
pub(super) fn metadata() -> [Option<PointerMetadataShape>; 8] {
    [
        None,
        Some(PointerMetadataShape::SliceLen { elem: TyId::new(0) }),
        Some(PointerMetadataShape::SliceLen {
            elem: TyId::new(u32::MAX),
        }),
        Some(PointerMetadataShape::StrLen),
        Some(PointerMetadataShape::VTable { trait_id: 0 }),
        Some(PointerMetadataShape::VTable { trait_id: u32::MAX }),
        Some(PointerMetadataShape::ContainerLen),
        Some(PointerMetadataShape::ContainerVtable),
    ]
}
