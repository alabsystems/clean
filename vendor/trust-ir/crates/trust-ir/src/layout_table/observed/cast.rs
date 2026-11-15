// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The original cast rule, with actual observed predicates and layout work.
//! Reachability uses a fresh per-query visited set, not the ordinary memo.

use super::*;
use crate::{CastLayoutEvidence, CastOp};

mod reach;
#[cfg(test)]
mod retirement;

impl LayoutTable<'_> {
    /// The original cast evidence or semantic layout error. The outer error
    /// is a stop under the caller's original session, never cast evidence.
    /// All three reachability guards follow this table's exact borrowed module;
    /// no ordinary predicate, layout memo or source authority is credited.
    pub fn layout_sensitive_cast_evidence_observed<O: ExecutionObserver>(
        &self,
        op: CastOp,
        src: &Ty,
        dst: &Ty,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Result<Result<CastLayoutEvidence, LayoutError>, ObservedValueError> {
        let mut work = Work::new(session, site)?;
        let result = evidence(self, op, src, dst, &mut work);
        work.retire_scratch();
        if storage::publication(work.session, work.site).is_err() {
            match result {
                Ok(value) => retire_evidence(value, &mut work),
                Err(error) => work.retire_error(error),
            }
            return Err(ObservedValueError::AdmissionRefused);
        }
        match result {
            Ok(value) => Ok(Ok(value)),
            Err(Error::Layout(error)) => Ok(Err(error)),
            Err(Error::Resource(error)) => Err(error),
        }
    }
}

fn evidence<O: ExecutionObserver>(
    table: &LayoutTable<'_>,
    op: CastOp,
    src: &Ty,
    dst: &Ty,
    work: &mut Work<'_, '_, O>,
) -> R<CastLayoutEvidence> {
    work.admit(1, size_of::<CastLayoutEvidence>())?;
    if !op.is_layout_sensitive() {
        return Ok(CastLayoutEvidence::NotLayoutSensitive);
    }
    if reach::reaches(table.module, reach::Mode::Handle, src, work)?
        || reach::reaches(table.module, reach::Mode::Handle, dst, work)?
    {
        return Err(LayoutError::OpaqueHandleCast {
            src: src.shape(),
            dst: dst.shape(),
        }
        .into());
    }
    if reach::reaches(table.module, reach::Mode::Storage, src, work)?
        || reach::reaches(table.module, reach::Mode::Storage, dst, work)?
    {
        return Err(LayoutError::UnsupportedTyShape(TyShape::Storage).into());
    }
    if reach::reaches(table.module, reach::Mode::Closure, src, work)?
        || reach::reaches(table.module, reach::Mode::Closure, dst, work)?
    {
        return Err(LayoutError::ClosureCast {
            src: src.shape(),
            dst: dst.shape(),
        }
        .into());
    }
    work.poll()?;
    match op {
        CastOp::PtrToPtr => {
            let bits = table.module.pointer_bits();
            // These helpers inspect only the outer constructor and fixed-size
            // pointer metadata. They traverse neither child nor table types.
            let src = src
                .pointer_layout_shape(bits)
                .ok_or_else(|| LayoutError::NotPointer(src.shape()))?;
            let dst = dst
                .pointer_layout_shape(bits)
                .ok_or_else(|| LayoutError::NotPointer(dst.shape()))?;
            if src.lane_count() != dst.lane_count() {
                return Err(LayoutError::PointerLaneMismatch {
                    src_lanes: src.lane_count(),
                    dst_lanes: dst.lane_count(),
                }
                .into());
            }
            if src.metadata != dst.metadata {
                return Err(LayoutError::PointerMetadataMismatch {
                    src: src.metadata,
                    dst: dst.metadata,
                }
                .into());
            }
            Ok(CastLayoutEvidence::PointerCast { src, dst })
        }
        CastOp::Bitcast | CastOp::Transmute => {
            if !equality::types(src, dst, work)?
                && (reach::reaches(table.module, reach::Mode::Bool, src, work)?
                    || reach::reaches(table.module, reach::Mode::Bool, dst, work)?)
            {
                return Err(LayoutError::BoolLaneReinterpret {
                    src: src.shape(),
                    dst: dst.shape(),
                }
                .into());
            }
            same_size(table, src, dst, work)
        }
        CastOp::ReifyFnPointer => {
            if !matches!(src, Ty::Func(_)) {
                return Err(LayoutError::NotFunctionPointerSource(src.shape()).into());
            }
            let pointer_bits = table.module.pointer_bits();
            let layout = dst
                .pointer_layout_shape(pointer_bits)
                .ok_or_else(|| LayoutError::NotPointer(dst.shape()))?;
            if layout.is_fat() {
                return Err(LayoutError::PointerLaneMismatch {
                    src_lanes: 1,
                    dst_lanes: layout.lane_count(),
                }
                .into());
            }
            Ok(CastLayoutEvidence::ReifyFnPointer { pointer_bits })
        }
        _ => Ok(CastLayoutEvidence::NotLayoutSensitive),
    }
}

fn same_size<O: ExecutionObserver>(
    table: &LayoutTable<'_>,
    src: &Ty,
    dst: &Ty,
    work: &mut Work<'_, '_, O>,
) -> R<CastLayoutEvidence> {
    let source = work.walk(table, src)?;
    // Retain the first owned result through a failure of the second query;
    // dispose it explicitly before final publication even on that error path.
    let result = match work.walk(table, dst) {
        Ok(target) => {
            let result = if source.size_bits != target.size_bits {
                Err(LayoutError::CastSizeMismatch {
                    src_bits: source.size_bits,
                    dst_bits: target.size_bits,
                }
                .into())
            } else {
                Ok(CastLayoutEvidence::SameSize {
                    size_bits: source.size_bits,
                    src_align_bits: source.align_bits,
                    dst_align_bits: target.align_bits,
                })
            };
            work.retire_layout(target);
            result
        }
        Err(error) => Err(error),
    };
    work.retire_layout(source);
    result
}

// This enum is not Copy. Match every variant and require Copy for its actual
// fields so a future owned payload cannot enter a generic Drop fallback.
fn retire_evidence<O: ExecutionObserver>(value: CastLayoutEvidence, work: &mut Work<'_, '_, O>) {
    match value {
        CastLayoutEvidence::NotLayoutSensitive => work.retire_fixed(()),
        CastLayoutEvidence::PointerCast { src, dst } => work.retire_fixed((src, dst)),
        CastLayoutEvidence::SameSize {
            size_bits,
            src_align_bits,
            dst_align_bits,
        } => work.retire_fixed((size_bits, src_align_bits, dst_align_bits)),
        CastLayoutEvidence::ReifyFnPointer { pointer_bits } => work.retire_fixed(pointer_bits),
    }
}
