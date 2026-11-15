// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Exact existing canonical field/tag spelling, with fallible inner writes.

use super::*;

pub(super) fn write_u8<O: ExecutionObserver>(out: &mut Writer<'_, '_, O>, value: u8) -> Result {
    out.poll()?;
    out.push(value)?;

    Ok(())
}

pub(super) fn write_bool<O: ExecutionObserver>(out: &mut Writer<'_, '_, O>, value: bool) -> Result {
    out.poll()?;
    write_u8(out, u8::from(value))?;

    Ok(())
}

pub(super) fn write_u32<O: ExecutionObserver>(out: &mut Writer<'_, '_, O>, value: u32) -> Result {
    out.poll()?;
    out.append(&value.to_le_bytes())?;

    Ok(())
}

pub(super) fn write_u64<O: ExecutionObserver>(out: &mut Writer<'_, '_, O>, value: u64) -> Result {
    out.poll()?;
    out.append(&value.to_le_bytes())?;

    Ok(())
}

pub(super) fn write_len<O: ExecutionObserver>(out: &mut Writer<'_, '_, O>, value: usize) -> Result {
    out.poll()?;
    write_u64(
        out,
        u64::try_from(value).map_err(|_| ObservedValueError::CapacityOverflow)?,
    )?;

    Ok(())
}

pub(super) fn write_u128<O: ExecutionObserver>(out: &mut Writer<'_, '_, O>, value: u128) -> Result {
    out.poll()?;
    out.append(&value.to_le_bytes())?;

    Ok(())
}

pub(super) fn write_i128<O: ExecutionObserver>(out: &mut Writer<'_, '_, O>, value: i128) -> Result {
    out.poll()?;
    out.append(&value.to_le_bytes())?;

    Ok(())
}

pub(super) fn write_str<O: ExecutionObserver>(out: &mut Writer<'_, '_, O>, value: &str) -> Result {
    out.poll()?;
    write_len(out, value.len())?;
    out.append(value.as_bytes())?;

    Ok(())
}

pub(super) fn write_option_str<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    value: Option<&str>,
) -> Result {
    out.poll()?;
    match value {
        None => write_u8(out, 0)?,
        Some(value) => {
            write_u8(out, 1)?;
            write_str(out, value)?;
        }
    }

    Ok(())
}

pub(super) fn write_option_u32<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    value: Option<u32>,
) -> Result {
    out.poll()?;
    match value {
        None => write_u8(out, 0)?,
        Some(value) => {
            write_u8(out, 1)?;
            write_u32(out, value)?;
        }
    }

    Ok(())
}

pub(super) fn write_option_u64<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    value: Option<u64>,
) -> Result {
    out.poll()?;
    match value {
        None => write_u8(out, 0)?,
        Some(value) => {
            write_u8(out, 1)?;
            write_u64(out, value)?;
        }
    }

    Ok(())
}

pub(super) fn write_option_i128<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    value: Option<i128>,
) -> Result {
    out.poll()?;
    match value {
        None => write_u8(out, 0)?,
        Some(value) => {
            write_u8(out, 1)?;
            write_i128(out, value)?;
        }
    }

    Ok(())
}

pub(super) fn write_option_digest<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    value: Option<ProofDigest>,
) -> Result {
    out.poll()?;
    match value {
        None => write_u8(out, 0)?,
        Some(value) => {
            write_u8(out, 1)?;
            write_digest(out, &value)?;
        }
    }

    Ok(())
}

pub(super) fn write_digest<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    digest: &ProofDigest,
) -> Result {
    out.poll()?;
    let algorithm = match digest.algorithm {
        ProofDigestAlgorithm::Sha256 => 0,
        ProofDigestAlgorithm::TrustIrStableV1 => 1,
    };
    write_u8(out, algorithm)?;
    out.append(&digest.bytes)?;

    Ok(())
}

pub(super) fn write_source_span<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    span: &SourceSpan,
) -> Result {
    out.poll()?;
    write_u32(out, span.file)?;
    write_u32(out, span.line)?;
    write_u32(out, span.col)?;

    Ok(())
}

pub(super) fn write_option_source_span<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    span: Option<SourceSpan>,
) -> Result {
    out.poll()?;
    match span {
        None => write_u8(out, 0)?,
        Some(span) => {
            write_u8(out, 1)?;
            write_source_span(out, &span)?;
        }
    }

    Ok(())
}

pub(super) fn write_option_assertion_id<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    assertion_id: Option<NativeAssertionId>,
) -> Result {
    out.poll()?;
    match assertion_id {
        None => write_u8(out, 0)?,
        Some(assertion_id) => {
            write_u8(out, 1)?;
            write_u32(out, assertion_id.index())?;
        }
    }

    Ok(())
}

pub(super) fn write_set_repr<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    repr: SetRepr,
) -> Result {
    out.poll()?;
    write_u8(
        out,
        match repr {
            SetRepr::Bitset => 0,
            SetRepr::Boxed => 1,
        },
    )?;

    Ok(())
}

pub(super) fn write_fat_ptr_kind<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    kind: &crate::FatPtrKind,
) -> Result {
    out.poll()?;
    match *kind {
        crate::FatPtrKind::Slice(elem) => {
            write_u8(out, 0)?;
            write_u32(out, elem.index())?;
        }
        crate::FatPtrKind::Str => write_u8(out, 1)?,
        crate::FatPtrKind::TraitObject { trait_id } => {
            write_u8(out, 2)?;
            write_u32(out, trait_id)?;
        }
        // Tag 3, DISTINCT from Str's 1 on purpose: this digest is a
        // content-derived identity, and a container-tail pointer is not a
        // string pointer. Sharing a tag would make two different meanings hash
        // equal, which is the one thing a stable digest may never do.
        crate::FatPtrKind::ContainerLen => write_u8(out, 3)?,
        // Tag 4, DISTINCT from TraitObject's 2 for the same reason: a
        // container-tail pointer is not a trait-object pointer, and it has no
        // trait id to write -- nothing dispatches through it.
        crate::FatPtrKind::ContainerVtable => write_u8(out, 4)?,
    }

    Ok(())
}

pub(super) fn write_ty_id<O: ExecutionObserver>(out: &mut Writer<'_, '_, O>, id: TyId) -> Result {
    out.poll()?;
    write_u32(out, id.index())?;

    Ok(())
}

pub(super) fn write_struct_id<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    id: StructId,
) -> Result {
    out.poll()?;
    write_u32(out, id.index())?;

    Ok(())
}

pub(super) fn write_enum_id<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    id: EnumId,
) -> Result {
    out.poll()?;
    write_u32(out, id.index())?;

    Ok(())
}

pub(super) fn write_func_ty_id<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    id: FuncTyId,
) -> Result {
    out.poll()?;
    write_u32(out, id.index())?;

    Ok(())
}

pub(super) fn write_record_id<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    id: RecordId,
) -> Result {
    out.poll()?;
    write_u32(out, id.index())?;

    Ok(())
}

pub(super) fn write_closure_ty_id<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    id: ClosureTyId,
) -> Result {
    out.poll()?;
    write_u32(out, id.index())?;

    Ok(())
}

pub(super) fn write_ty_shape<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    shape: TyShape,
) -> Result {
    out.poll()?;
    match shape {
        TyShape::Storage => write_u8(out, 27)?,
        // PKG-U13a: the next free shape tag (the native digest's 28).
        TyShape::Tensor => write_u8(out, 28)?,
        TyShape::Int { signed, bits } => {
            write_u8(out, 0)?;
            write_bool(out, signed)?;
            write_u32(out, bits)?;
        }
        TyShape::Float { bits } => {
            write_u8(out, 1)?;
            write_u32(out, bits)?;
        }
        TyShape::Bool => write_u8(out, 2)?,
        TyShape::ThinPointer => write_u8(out, 3)?,
        TyShape::FatPointer => write_u8(out, 4)?,
        TyShape::Unit => write_u8(out, 5)?,
        TyShape::Never => write_u8(out, 6)?,
        TyShape::Struct => write_u8(out, 7)?,
        TyShape::Array => write_u8(out, 8)?,
        TyShape::Tuple => write_u8(out, 9)?,
        TyShape::Enum => write_u8(out, 10)?,
        TyShape::Function => write_u8(out, 11)?,
        TyShape::Ref => write_u8(out, 12)?,
        TyShape::RefMut => write_u8(out, 13)?,
        TyShape::PtrConst => write_u8(out, 14)?,
        TyShape::PtrMut => write_u8(out, 15)?,
        TyShape::Rc => write_u8(out, 16)?,
        TyShape::Set => write_u8(out, 17)?,
        TyShape::Sequence => write_u8(out, 18)?,
        TyShape::Record => write_u8(out, 19)?,
        TyShape::Closure => write_u8(out, 20)?,
        TyShape::Vector => write_u8(out, 21)?,
        // v25: pointer-width integer + error shapes.
        TyShape::PointerInt { signed } => {
            write_u8(out, 22)?;
            write_bool(out, signed)?;
        }
        TyShape::Error => write_u8(out, 23)?,
        // v30: refinement shape (representation-preserving; the base type's
        // own shape is digested wherever the base is reachable).
        TyShape::Refine => write_u8(out, 24)?,
        TyShape::Dialect => write_u8(out, 25)?,
        // v43: one pointer word, but a distinct shape from `ThinPointer` (3).
        TyShape::Handle => write_u8(out, 26)?,
    }

    Ok(())
}

pub(super) fn write_pointer_metadata_shape<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    metadata: PointerMetadataShape,
) -> Result {
    out.poll()?;
    match metadata {
        PointerMetadataShape::SliceLen { elem } => {
            write_u8(out, 0)?;
            write_ty_id(out, elem)?;
        }
        PointerMetadataShape::StrLen => write_u8(out, 1)?,
        PointerMetadataShape::VTable { trait_id } => {
            write_u8(out, 2)?;
            write_u32(out, trait_id)?;
        }
        PointerMetadataShape::ContainerLen => write_u8(out, 3)?,
        PointerMetadataShape::ContainerVtable => write_u8(out, 4)?,
    }

    Ok(())
}

pub(super) fn write_option_pointer_metadata_shape<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    metadata: Option<PointerMetadataShape>,
) -> Result {
    out.poll()?;
    match metadata {
        None => write_u8(out, 0)?,
        Some(metadata) => {
            write_u8(out, 1)?;
            write_pointer_metadata_shape(out, metadata)?;
        }
    }

    Ok(())
}

pub(super) fn write_pointer_layout_shape<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    layout: PointerLayoutShape,
) -> Result {
    out.poll()?;
    write_u32(out, layout.data_bits)?;
    write_option_u32(out, layout.metadata_bits)?;
    write_option_pointer_metadata_shape(out, layout.metadata)?;

    Ok(())
}

pub(super) fn write_field_offset_shape<O: ExecutionObserver>(
    out: &mut Writer<'_, '_, O>,
    field: &FieldOffsetShape,
) -> Result {
    out.poll()?;
    write_u32(out, field.field)?;
    write_str(out, &field.name)?;
    write_ty_shape(out, field.ty_shape)?;
    write_option_u64(out, field.offset_bits)?;

    Ok(())
}
