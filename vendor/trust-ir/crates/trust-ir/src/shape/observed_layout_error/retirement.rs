// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

pub(super) fn consume<O: ExecutionObserver>(error: LayoutError, work: &mut Work<'_, '_, O>) {
    // Retain and consume the owned error even if this step is itself refused.
    work.step(size_of::<LayoutError>().saturating_add(1));
    match error {
        LayoutError::MissingType(id) => work.fixed(id),
        LayoutError::MissingStruct(id) => work.fixed(id),
        LayoutError::MissingStructSize(id) => work.fixed(id),
        LayoutError::MissingStructAlign(id) => work.fixed(id),
        LayoutError::StructLayoutIncoherent(id) => work.fixed(id),
        LayoutError::TupleLayoutIncoherent(id) => work.fixed(id),
        LayoutError::TupleLayoutTargetMissing => work.fixed(()),
        LayoutError::ClosureLayoutIncoherent(id) => work.fixed(id),
        LayoutError::ClosureLayoutTargetMissing => work.fixed(()),
        LayoutError::TargetScalarLayoutUnavailable { triple } => work.retire_text(triple),
        LayoutError::MissingFieldOffset { struct_id, field } => {
            work.fixed(struct_id);
            work.fixed(field);
        }
        LayoutError::EnumLayoutUnavailable(id) => work.fixed(id),
        LayoutError::TyLayoutCycle(id) => work.fixed(id),
        LayoutError::UnsupportedTyShape(shape) => work.fixed(shape),
        LayoutError::SizeOverflow => work.fixed(()),
        LayoutError::NotPointer(shape) => work.fixed(shape),
        LayoutError::OpaqueHandleCast { src, dst } => {
            work.fixed(src);
            work.fixed(dst);
        }
        LayoutError::BoolLaneReinterpret { src, dst } => {
            work.fixed(src);
            work.fixed(dst);
        }
        LayoutError::ClosureCast { src, dst } => {
            work.fixed(src);
            work.fixed(dst);
        }
        LayoutError::PointerLaneMismatch {
            src_lanes,
            dst_lanes,
        } => {
            work.fixed(src_lanes);
            work.fixed(dst_lanes);
        }
        LayoutError::PointerMetadataMismatch { src, dst } => {
            work.fixed(src);
            work.fixed(dst);
        }
        LayoutError::NotFunctionPointerSource(shape) => work.fixed(shape),
        LayoutError::CastSizeMismatch { src_bits, dst_bits } => {
            work.fixed(src_bits);
            work.fixed(dst_bits);
        }
    }
    work.poll();
}
