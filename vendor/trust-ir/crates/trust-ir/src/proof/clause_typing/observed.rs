// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Observed borrowed resolution; this is type data, never proof authority.
use super::*;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use core::mem::size_of;
mod resolve;
#[cfg(test)]
mod tests;
type R<T> = Result<T, ObservedValueError>;
/// Exact ordinary resolution refusal data, retaining borrowed nested types
/// instead of cloning them before a later diagnostic allocation. It cannot
/// authenticate a clause, a function, an import or any proof status.
#[derive(Debug, Clone, Copy)]
pub enum ObservedClauseTypingError<'a> {
    FunctionUnresolved { function: FuncId, matches: usize },
    SignatureUnresolved { function: FuncId },
    ParamOutOfRange { index: u32, arity: usize },
    ResultOutOfRange { index: u32, arity: usize },
    MutParamExitNotMutable { index: u32, ty: &'a Ty },
    ParamPointeeNotReference { index: u32, ty: &'a Ty },
    PlaceHasNoIrType(ClausePlace),
    ValuePlaceUnsupported(ClausePlace),
}
struct Work<'s, 'o, O: ExecutionObserver> {
    session: &'s mut ObservedSession<'o, O>,
    site: ExecutionSite,
}
impl<O: ExecutionObserver> Work<'_, '_, O> {
    fn admit(&mut self, work: usize, copy_bytes: usize) -> R<()> {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Validation,
                site: self.site,
                work,
                copy_bytes,
            })
            .map_err(Into::into)
    }
    fn at<'a, T>(&mut self, rows: &'a [T], index: usize) -> R<Option<&'a T>> {
        self.admit(1, size_of::<Option<&T>>())?;
        Ok(rows.get(index))
    }
    fn next(&mut self, index: &mut usize) -> R<()> {
        self.admit(1, size_of::<usize>())?;
        *index = index
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        Ok(())
    }
    fn publish(&mut self, bytes: usize) -> R<()> {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: self.site,
                work: 1,
                copy_bytes: bytes,
            })
            .map_err(Into::into)
    }
}
/// Exact ordinary unique-function/signature/place resolution without owned
/// type clones or an opaque candidate Vec. Every physical candidate and slot
/// is read under the caller's original session/site, including for ambient
/// places. Both resolved and refused semantic outcomes require publication.
pub fn resolve_clause_place_borrowed_observed<'a, O: ExecutionObserver>(
    module: &'a Module,
    function: FuncId,
    place: &ClausePlace,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Result<&'a Ty, ObservedClauseTypingError<'a>>> {
    session.admit(ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site,
        work: 1,
        copy_bytes: size_of::<Work<'_, '_, O>>()
            + size_of::<Result<&Ty, ObservedClauseTypingError<'_>>>(),
    })?;
    let mut work = Work { session, site };
    let result = resolve::resolve(module, function, place, &mut work)?;
    work.publish(size_of::<Result<&Ty, ObservedClauseTypingError<'_>>>())?;
    Ok(result)
}
/// The same finite scalar sort/type table as clause_sort_admits. Only inline
/// tags/scalars are inspected; nested arrays/datatypes/types are deliberately
/// not traversed or made admissible. No default target width is invented.
pub fn clause_sort_admits_observed<O: ExecutionObserver>(
    sort: &ClauseSort,
    ty: &Ty,
    pointer_bits: Option<u32>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<bool> {
    session.admit(ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site,
        work: 1,
        copy_bytes: size_of::<Work<'_, '_, O>>() + 2 * size_of::<&Ty>(),
    })?;
    let mut work = Work { session, site };
    // Full current sort/type census and fixed scalar operations precede the
    // actual table; no recursive bit_width or integer predicate is invoked.
    work.admit(7 + 41 + 12, 2 * size_of::<u32>() + size_of::<bool>())?;
    let integer_width = match ty {
        Ty::I8 | Ty::U8 => Some(8),
        Ty::I16 | Ty::U16 => Some(16),
        Ty::I32 | Ty::U32 => Some(32),
        Ty::I64 | Ty::U64 => Some(64),
        Ty::I128 | Ty::U128 => Some(128),
        Ty::Isize | Ty::Usize => pointer_bits,
        _ => None,
    };
    let result = match sort {
        ClauseSort::Bool => matches!(ty, Ty::Bool),
        ClauseSort::Int => matches!(
            ty,
            Ty::I8
                | Ty::U8
                | Ty::I16
                | Ty::U16
                | Ty::I32
                | Ty::U32
                | Ty::I64
                | Ty::U64
                | Ty::I128
                | Ty::U128
                | Ty::Isize
                | Ty::Usize
                | Ty::Char
        ),
        ClauseSort::BitVec(width) => match ty {
            Ty::Char => *width == 32,
            _ => integer_width == Some(*width),
        },
        ClauseSort::Float { eb, sb } => matches!(
            (ty, eb, sb),
            (Ty::F16, 5, 11) | (Ty::F32, 8, 24) | (Ty::F64, 11, 53)
        ),
        ClauseSort::RoundingMode | ClauseSort::Array(..) | ClauseSort::Datatype { .. } => false,
    };
    work.publish(size_of::<bool>())?;
    Ok(result)
}
