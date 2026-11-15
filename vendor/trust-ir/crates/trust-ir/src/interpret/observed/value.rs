// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Observed value construction and retirement. Logical array length is never
//! a loop bound: the rope operations visit retained structure only.

use super::super::{ArrayValue, InterpretValue, InterpretValueKind as K};
use super::*;
use crate::ty::Ty;
use core::mem::size_of;

pub(super) fn scalar_type(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::I128
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::U128
            | Ty::Isize
            | Ty::Usize
            | Ty::Char
            | Ty::Bool
            | Ty::F16
            | Ty::F32
            | Ty::F64
            | Ty::Ptr
            | Ty::Unit
    )
}

pub(super) fn flat_type(ty: &Ty) -> bool {
    scalar_type(ty) || matches!(ty, Ty::Array(_, _))
}

pub(super) fn clone_value(
    value: &InterpretValue,
    progress: &mut impl StructuralProgress,
) -> Result<InterpretValue, ObservedValueError> {
    progress.admit(
        ExecutionPhase::LiteralElement,
        1,
        size_of::<InterpretValue>(),
    )?;
    if !flat_type(&value.ty) {
        return Err(ObservedValueError::UnsupportedValue);
    }
    let kind = match &value.kind {
        K::Int(v) => K::Int(*v),
        K::FloatBits(v) => K::FloatBits(*v),
        K::Bool(v) => K::Bool(*v),
        K::Ptr(v) => K::Ptr(*v),
        K::DanglingPtr(v) => K::DanglingPtr(*v),
        K::NullPtr => K::NullPtr,
        K::Unit => K::Unit,
        K::PartialBytes(bytes) if scalar_type(&value.ty) && bytes.len() <= 16 => {
            let mut cloned = Vec::new();
            progress.admit(ExecutionPhase::HostAllocation, 1, bytes.len())?;
            cloned
                .try_reserve(bytes.len())
                .map_err(|_| ObservedValueError::AllocationFailed)?;
            for byte in bytes {
                progress.admit(ExecutionPhase::LiteralElement, 1, 1)?;
                cloned.push(*byte);
            }
            K::PartialBytes(cloned)
        }
        K::Array(array) => {
            progress.admit(ExecutionPhase::RopeNode, 1, size_of::<ArrayValue>())?;
            K::Array(array.clone())
        }
        _ => return Err(ObservedValueError::UnsupportedValue),
    };
    Ok(InterpretValue {
        ty: value.ty.clone(),
        kind,
    })
}

impl ObservedRopeElem for InterpretValue {
    fn clone_observed(
        &self,
        progress: &mut impl StructuralProgress,
    ) -> Result<Self, ObservedValueError> {
        clone_value(self, progress)
    }

    fn same_observed(
        &self,
        other: &Self,
        progress: &mut impl StructuralProgress,
    ) -> Result<bool, ObservedValueError> {
        progress.admit(ExecutionPhase::LiteralElement, 1, 0)?;
        if !flat_type(&self.ty) || !flat_type(&other.ty) {
            return Err(ObservedValueError::UnsupportedValue);
        }
        if self.ty != other.ty {
            return Ok(false);
        }
        Ok(match (&self.kind, &other.kind) {
            (K::Int(a), K::Int(b)) => a == b,
            (K::FloatBits(a), K::FloatBits(b)) => a == b,
            (K::Bool(a), K::Bool(b)) => a == b,
            (K::Ptr(a), K::Ptr(b)) => a == b,
            (K::DanglingPtr(a), K::DanglingPtr(b)) => a == b,
            (K::NullPtr, K::NullPtr) | (K::Unit, K::Unit) => true,
            (K::Array(a), K::Array(b)) => a.ptr_eq(b),
            _ => false,
        })
    }

    fn retire_observed(self, progress: &mut impl StructuralProgress) {
        retire_value(self, progress);
    }
}

impl ArrayValue {
    pub fn splat_observed<O: ExecutionObserver>(
        value: InterpretValue,
        len: u64,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Result<Self, ObservedValueError> {
        Ok(Self::from_rope(super::super::rope::Rope::uniform_observed(
            value,
            len,
            &mut session.structural(site),
        )?))
    }

    pub fn set_observed<O: ExecutionObserver>(
        &self,
        index: u64,
        value: InterpretValue,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Result<Self, ObservedValueError> {
        Ok(Self::from_rope(self.rope().set_observed(
            index,
            value,
            &mut session.structural(site),
        )?))
    }

    pub fn get_observed<O: ExecutionObserver>(
        &self,
        index: u64,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Result<Option<&InterpretValue>, ObservedValueError> {
        self.rope()
            .get_observed(index, &mut session.structural(site))
    }
}

impl InterpretValue {
    /// Consume an input/output under the SAME original cleanup observer.
    /// Refusal remains sticky; cleanup does not replenish work or fuel.
    pub fn retire_observed<O: ExecutionObserver>(
        self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Result<(), ObservationStopped> {
        retire_value(self, &mut session.structural(site));
        if session.first_refusal.is_some() {
            Err(ObservationStopped)
        } else {
            Ok(())
        }
    }
}

pub(super) fn retire_values(values: Vec<InterpretValue>, progress: &mut impl StructuralProgress) {
    for value in values {
        progress.retirement_poll();
        retire_value(value, progress);
    }
}

fn empty_value() -> InterpretValue {
    InterpretValue {
        ty: Ty::Unit,
        kind: K::Unit,
    }
}

fn retire_tick(progress: &mut impl StructuralProgress) {
    // A caller-owned unsupported tree may predate this session. Debit its
    // actual cleanup while admission remains available; after refusal only
    // mandatory zero-debit original-owner cleanup polls continue.
    let _ = progress.admit(ExecutionPhase::ScratchRetirement, 1, 0);
    progress.retirement_poll();
}

fn retire_value(value: InterpretValue, progress: &mut impl StructuralProgress) {
    // Allocation-free owned zipper. A removed child slot stores the parent
    // link, reusing the original Vec/Box capacity; no recursive Rust drop or
    // new scratch allocation is needed for aggregate/record/fat-pointer trees.
    let mut pending = empty_value();
    let mut current = Some(value);
    loop {
        if let Some(InterpretValue { ty, kind }) = current.take() {
            retire_tick(progress);
            retire_type(ty, progress);
            match kind {
                K::Array(a)
                | K::Vector(a)
                | K::Sequence(a)
                | K::Set(a)
                | K::Tensor { elems: a, .. } => a.into_rope_observed().retire_observed(progress),
                K::Aggregate(mut values)
                | K::Closure {
                    captures: mut values,
                    ..
                } => {
                    if let Some(child) = values.pop() {
                        values.push(pending); // reuses the just-vacated slot
                        pending = InterpretValue {
                            ty: Ty::Unit,
                            kind: K::Aggregate(values),
                        };
                        current = Some(child);
                    }
                }
                K::Record(mut fields) => {
                    if let Some((name, child)) = fields.pop() {
                        drop(name);
                        fields.push((String::new(), pending)); // no allocation
                        pending = InterpretValue {
                            ty: Ty::Unit,
                            kind: K::Record(fields),
                        };
                        current = Some(child);
                    }
                }
                K::FatPtr { mut data, metadata } => {
                    let child = core::mem::replace(&mut *data, pending);
                    pending = InterpretValue {
                        ty: Ty::Unit,
                        kind: K::FatPtr { data, metadata },
                    };
                    current = Some(child);
                }
                K::Frame { mut slots, .. } => {
                    // Frames are outside the admitted observed input closure.
                    // A unique frame can still be drained without recursion.
                    // Shared unsized Arc slices cannot be atomically detached
                    // by Arc::into_inner; no general Frame cleanup claim is made.
                    let mut child = None;
                    if let Some(values) = std::sync::Arc::get_mut(&mut slots) {
                        for (index, slot) in values.iter_mut().enumerate().rev() {
                            retire_tick(progress);
                            if let Some(value) = slot.take() {
                                *slot = Some(core::mem::replace(&mut pending, empty_value()));
                                child = Some((index as u64, value));
                                break;
                            }
                        }
                    }
                    if let Some((index, value)) = child {
                        pending = InterpretValue {
                            ty: Ty::Unit,
                            kind: K::Frame {
                                lineage: index,
                                slots,
                            },
                        };
                        current = Some(value);
                    } else {
                        drop(slots);
                    }
                }
                K::PartialBytes(bytes) => {
                    for _ in &bytes {
                        retire_tick(progress);
                    }
                    drop(bytes);
                }
                _ => {}
            }
            if current.is_some() {
                continue;
            }
        }
        // The pending values below are private zipper frames, not arbitrary
        // program values. Their final slot is always the previous parent.
        match core::mem::replace(&mut pending, empty_value()).kind {
            K::Unit => break,
            K::Aggregate(mut values) => {
                let parent = values.pop().unwrap_or_else(empty_value);
                if let Some(child) = values.pop() {
                    values.push(parent);
                    pending = InterpretValue {
                        ty: Ty::Unit,
                        kind: K::Aggregate(values),
                    };
                    current = Some(child);
                } else {
                    pending = parent;
                }
            }
            K::Record(mut fields) => {
                let parent = fields
                    .pop()
                    .map(|(_, value)| value)
                    .unwrap_or_else(empty_value);
                if let Some((name, child)) = fields.pop() {
                    drop(name);
                    fields.push((String::new(), parent));
                    pending = InterpretValue {
                        ty: Ty::Unit,
                        kind: K::Record(fields),
                    };
                    current = Some(child);
                } else {
                    pending = parent;
                }
            }
            K::FatPtr { data, metadata } => {
                pending = *data;
                current = Some(*metadata);
            }
            K::Frame { lineage, mut slots } => {
                let mut parent = empty_value();
                let mut child = None;
                if let Some(values) = std::sync::Arc::get_mut(&mut slots) {
                    if let Some(slot) = values.get_mut(lineage as usize) {
                        parent = slot.take().unwrap_or_else(empty_value);
                    }
                    for (index, slot) in values[..lineage as usize].iter_mut().enumerate().rev() {
                        retire_tick(progress);
                        if let Some(value) = slot.take() {
                            *slot = Some(core::mem::replace(&mut parent, empty_value()));
                            child = Some((index as u64, value));
                            break;
                        }
                    }
                }
                if let Some((index, value)) = child {
                    pending = InterpretValue {
                        ty: Ty::Unit,
                        kind: K::Frame {
                            lineage: index,
                            slots,
                        },
                    };
                    current = Some(value);
                } else {
                    drop(slots);
                    pending = parent;
                }
            }
            _ => break, // unreachable private-frame shape, no public constructor
        }
    }
    progress.retirement_poll();
}

fn retire_type(ty: Ty, progress: &mut impl StructuralProgress) {
    // Flat positive types take this allocation-free fast path. Deep malformed
    // inline input types use the same vacated-Tuple-slot zipper, not vec![ty].
    let mut pending = Ty::Unit;
    let mut current = Some(ty);
    loop {
        if let Some(ty) = current.take() {
            retire_tick(progress);
            match ty {
                Ty::Vector(inner, _)
                | Ty::Tensor(inner, _)
                | Ty::Ref(inner)
                | Ty::RefMut(inner)
                | Ty::PtrConst(inner)
                | Ty::PtrMut(inner)
                | Ty::Rc(inner) => current = Some(*inner),
                Ty::Tuple(mut fields) => {
                    if let Some(child) = fields.pop() {
                        fields.push(pending);
                        pending = Ty::Tuple(fields);
                        current = Some(child);
                    }
                }
                _ => {}
            }
            if current.is_some() {
                continue;
            }
        }
        match core::mem::replace(&mut pending, Ty::Unit) {
            Ty::Unit => break,
            Ty::Tuple(mut fields) => {
                let parent = fields.pop().unwrap_or(Ty::Unit);
                if let Some(child) = fields.pop() {
                    fields.push(parent);
                    pending = Ty::Tuple(fields);
                    current = Some(child);
                } else {
                    pending = parent;
                }
            }
            _ => break,
        }
    }
}

impl ObservedReport {
    /// Classify through `exit()` first, then retire every owned payload before
    /// the consumer's final source/token/owner publication check.
    pub fn retire_observed<O: ExecutionObserver>(
        self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Result<(), ObservationStopped> {
        match self.exit {
            ObservedExit::Returned(outcome) => {
                retire_values(outcome.returns, &mut session.structural(site))
            }
            ObservedExit::EntryRejected(error)
            | ObservedExit::ExecutedError { error, .. }
            | ObservedExit::InterpreterLimit { error, .. } => {
                session.retirement_poll(site);
                drop(error);
            }
            _ => {}
        }
        session.retirement_poll(site);
        if session.first_refusal.is_some() {
            Err(ObservationStopped)
        } else {
            Ok(())
        }
    }
}
