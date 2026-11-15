// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

pub(super) fn write<O: ExecutionObserver>(
    error: &LayoutError,
    work: &mut Work<'_, '_, O>,
    output: &mut String,
) -> R {
    work.admit(1, size_of::<LayoutError>())?;
    match error {
        LayoutError::MissingType(id) => number(
            work,
            output,
            "type table entry ty.",
            u64::from(id.0),
            " is missing",
        ),
        LayoutError::MissingStruct(id) => number(
            work,
            output,
            "struct layout entry struct.",
            u64::from(id.0),
            " is missing",
        ),
        LayoutError::MissingStructSize(id) => number(
            work,
            output,
            "struct.",
            u64::from(id.0),
            " has no size layout metadata",
        ),
        LayoutError::MissingStructAlign(id) => number(
            work,
            output,
            "struct.",
            u64::from(id.0),
            " has no alignment layout metadata",
        ),
        LayoutError::StructLayoutIncoherent(id) => number(
            work,
            output,
            "struct.",
            u64::from(id.0),
            " has incoherent declared layout metadata",
        ),
        LayoutError::TupleLayoutIncoherent(id) => number(
            work,
            output,
            "tuple layout ty.",
            u64::from(id.0),
            " has incoherent or ambiguous declared metadata",
        ),
        LayoutError::TupleLayoutTargetMissing => {
            work.text("declared tuple layout requires target information", output)
        }
        LayoutError::ClosureLayoutIncoherent(id) => number(
            work,
            output,
            "closure layout closure.",
            u64::from(id.index()),
            " has incoherent or ambiguous declared metadata",
        ),
        LayoutError::ClosureLayoutTargetMissing => work.text(
            "declared closure layout requires target information",
            output,
        ),
        LayoutError::TargetScalarLayoutUnavailable { triple } => {
            work.text("target ", output)?;
            work.quoted(triple, output)?;
            work.text(" is outside TrustIR's canonical scalar-layout set", output)
        }
        LayoutError::MissingFieldOffset { struct_id, field } => {
            number(work, output, "struct.", u64::from(struct_id.0), " field ")?;
            number(
                work,
                output,
                "",
                u64::from(*field),
                " has no offset layout metadata",
            )
        }
        LayoutError::EnumLayoutUnavailable(id) => number(
            work,
            output,
            "enum.",
            u64::from(id.0),
            " has no concrete enum layout metadata",
        ),
        LayoutError::TyLayoutCycle(id) => number(
            work,
            output,
            "type table entry ty.",
            u64::from(id.0),
            " is cyclic; a self-referential type has no finite layout",
        ),
        LayoutError::UnsupportedTyShape(shape) => shape_suffix(
            work,
            output,
            *shape,
            " has no concrete memory layout evidence",
        ),
        LayoutError::SizeOverflow => work.text("layout size overflow", output),
        LayoutError::NotPointer(shape) => {
            shape_suffix(work, output, *shape, " is not pointer-like")
        }
        LayoutError::OpaqueHandleCast { src, dst } => cast(
            work,
            output,
            *src,
            *dst,
            ": an opaque runtime handle has no cast in or out; its only origins are its runtime's pinned entry points",
        ),
        LayoutError::BoolLaneReinterpret { src, dst } => cast(
            work,
            output,
            *src,
            *dst,
            ": a bool lane is one bit of value in one byte of storage, so no bit-image reinterpretation is defined for it (the reference interpreter and the Lean model both refuse it); spell int<->bool as trunc/zext and obtain a logical <N x bool> mask by comparing",
        ),
        LayoutError::ClosureCast { src, dst } => cast(
            work,
            output,
            *src,
            *dst,
            ": a first-class closure's bits are its captured environment, never a code address, and no cast reinterprets them, declared frame or not; apply it through CallIndirect at its closure type",
        ),
        LayoutError::PointerLaneMismatch {
            src_lanes,
            dst_lanes,
        } => {
            number(
                work,
                output,
                "pointer cast changes lane count from ",
                u64::from(*src_lanes),
                " to ",
            )?;
            work.number(u64::from(*dst_lanes), output)
        }
        LayoutError::PointerMetadataMismatch { src, dst } => {
            work.text("pointer cast changes metadata from ", output)?;
            shapes::metadata(*src, work, output)?;
            work.text(" to ", output)?;
            shapes::metadata(*dst, work, output)
        }
        LayoutError::NotFunctionPointerSource(shape) => {
            work.text(
                "reify_fn_pointer source must be a function item, got ",
                output,
            )?;
            shapes::shape(*shape, work, output)
        }
        LayoutError::CastSizeMismatch { src_bits, dst_bits } => {
            number(
                work,
                output,
                "cast layout sizes differ: ",
                *src_bits,
                "b -> ",
            )?;
            number(work, output, "", *dst_bits, "b")
        }
    }
}

fn number<O: ExecutionObserver>(
    work: &mut Work<'_, '_, O>,
    output: &mut String,
    prefix: &str,
    value: u64,
    suffix: &str,
) -> R {
    work.text(prefix, output)?;
    work.number(value, output)?;
    work.text(suffix, output)
}
fn shape_suffix<O: ExecutionObserver>(
    work: &mut Work<'_, '_, O>,
    output: &mut String,
    shape: TyShape,
    suffix: &str,
) -> R {
    shapes::shape(shape, work, output)?;
    work.text(suffix, output)
}
fn cast<O: ExecutionObserver>(
    work: &mut Work<'_, '_, O>,
    output: &mut String,
    src: TyShape,
    dst: TyShape,
    suffix: &str,
) -> R {
    shapes::shape(src, work, output)?;
    work.text(" -> ", output)?;
    shape_suffix(work, output, dst, suffix)
}
