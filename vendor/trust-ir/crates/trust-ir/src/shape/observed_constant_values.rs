// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Exact table-free constant value check and shape-label work under one owner.
use super::*;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use core::mem::{size_of, take};
mod label;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State<'a> {
    pending: Vec<(core::slice::Iter<'a, Constant>, &'a Ty)>,
    label: String,
}
impl Constant {
    /// Exact ordinary table-free predicate: scalar integer/char width checks,
    /// branching nested vectors with short circuit and all other fixed outer
    /// shapes. No module pointer provenance/type/reference/proof authority.
    /// Pointer width stays the original explicit parameter. No new owner,
    /// grant, deadline, TLS or instruction fuel; physical std/allocator bounds
    /// and successful borrowed input disposal remain caller obligations.
    pub fn value_matches_ty_observed<O: ExecutionObserver>(
        &self,
        ty: &Ty,
        pointer_bits: u32,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        let mut work = Work { session, site };
        work.admit(1, size_of::<State<'_>>() + size_of::<Work<'_, '_, O>>())?;
        let mut state = State::default();
        let result = state.matches(self, ty, pointer_bits, &mut work);
        state.retire(&mut work);
        result
            .and_then(|answer| {
                work.publication(size_of::<bool>())?;
                Ok(answer)
            })
            .map_err(|e| work.terminal(e))
    }
    /// Exact ordinary shape_label text, including unescaped symbol identity
    /// and signed addend. Variable Unicode copied in bounded chunks, decimal
    /// digits produced by observed scalar arithmetic; no opaque formatter.
    /// Successful owned String must be explicitly retired by its caller.
    pub fn shape_label_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<String> {
        let mut work = Work { session, site };
        work.admit(1, size_of::<State<'_>>() + size_of::<Work<'_, '_, O>>())?;
        let mut state = State::default();
        let result = state.label(self, &mut work);
        match result.and_then(|()| work.publication(size_of::<String>())) {
            Ok(()) => Ok(take(&mut state.label)),
            Err(error) => {
                state.retire(&mut work);
                Err(work.terminal(error))
            }
        }
    }
}
impl<'a> State<'a> {
    fn matches<O: ExecutionObserver>(
        &mut self,
        mut value: &'a Constant,
        mut ty: &'a Ty,
        pointer_bits: u32,
        work: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        loop {
            // Source-bound closed scalar dispatch. shape_matches_ty contains no
            // loop/allocation/deep compare: outer tags, lengths and <=2 Int
            // leaves only. int_value_fits_ty is called only after scalar
            // is_integer/Char guards, so its bit_width path cannot recurse
            // through a vector. These finite primitives are not prewalk credit.
            work.admit(256, size_of::<[u128; 8]>() + size_of::<[usize; 8]>())?;
            let matches = match (value, ty) {
                (Constant::Int(integer), ty) if ty.is_integer() => {
                    int_value_fits_ty(*integer, ty, pointer_bits)
                }
                (Constant::Int(integer), Ty::Char) => {
                    int_value_fits_ty(*integer, &Ty::Char, pointer_bits)
                }
                (Constant::U128(_), Ty::U128) => true,
                (Constant::Bytes { data, .. }, Ty::Array(_, n)) => *n == data.len() as u64,
                (Constant::Vector(elements), Ty::Vector(element_ty, lanes)) => {
                    if elements.len() != *lanes as usize {
                        return Ok(false);
                    }
                    work.admit(
                        4,
                        size_of::<core::slice::Iter<'_, Constant>>()
                            + size_of::<Option<&Constant>>(),
                    )?;
                    let mut children = elements.iter();
                    if let Some(first) = children.next() {
                        if children.len() != 0 {
                            work.reserve(&mut self.pending)?;
                            work.admit(1, size_of::<(core::slice::Iter<'_, Constant>, &Ty)>())?;
                            self.pending.push((children, element_ty));
                        }
                        value = first;
                        ty = element_ty;
                        continue;
                    }
                    true
                }
                _ => value.shape_matches_ty(ty),
            };
            if !matches {
                return Ok(false);
            }
            work.admit(
                2,
                size_of::<Option<&mut (core::slice::Iter<'_, Constant>, &Ty)>>(),
            )?;
            let Some((siblings, element_ty)) = self.pending.last_mut() else {
                return Ok(true);
            };
            work.admit(2, size_of::<Option<&Constant>>() + size_of::<&Ty>())?;
            value = siblings.next().ok_or(ObservedValueError::InvalidRange)?;
            ty = *element_ty;
            work.admit(1, size_of::<bool>())?;
            if siblings.len() == 0 {
                work.admit(
                    1,
                    size_of::<Option<(core::slice::Iter<'_, Constant>, &Ty)>>(),
                )?;
                work.retire(self.pending.pop());
                work.admit(1, 0)?;
            }
        }
    }
    fn retire<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        loop {
            work.step(
                size_of::<Option<(core::slice::Iter<'_, Constant>, &Ty)>>().saturating_add(1),
            );
            let Some(row) = self.pending.pop() else {
                break;
            };
            work.retire(row);
        }
        work.retire(take(&mut self.pending));
        work.flat(take(&mut self.label));
    }
}
