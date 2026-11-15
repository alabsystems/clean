// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;

pub(super) fn collect<'a, O: ExecutionObserver>(
    plan: plan::Plan<'a>,
    types: &mut Vec<&'a Ty>,
    work: &mut Work<'_, '_, O>,
) -> R {
    match plan {
        plan::Plan::One(ty) => work.push(types, ty),
        plan::Plan::Pair(first, second) => {
            work.push(types, first)?;
            work.push(types, second)
        }
        plan::Plan::Slots(slots) => {
            work.admit(1, size_of::<usize>())?;
            let mut index = 0usize;
            loop {
                // Charge before the actual outer slot read and type-header
                // projection, including an empty/exhausted slice probe.
                work.admit(1, 2 * size_of::<&Ty>())?;
                let Some(slot) = slots.get(index) else {
                    return Ok(());
                };
                work.push(types, &slot.ty)?;
                work.admit(1, size_of::<usize>())?;
                index = index
                    .checked_add(1)
                    .ok_or(ObservedValueError::CapacityOverflow)?;
            }
        }
        plan::Plan::Types(source) => {
            work.admit(1, size_of::<usize>())?;
            let mut index = 0usize;
            loop {
                work.admit(1, 2 * size_of::<&Ty>())?;
                let Some(ty) = source.get(index) else {
                    return Ok(());
                };
                work.push(types, ty)?;
                work.admit(1, size_of::<usize>())?;
                index = index
                    .checked_add(1)
                    .ok_or(ObservedValueError::CapacityOverflow)?;
            }
        }
        plan::Plan::Map(ty, body) => {
            work.push(types, ty)?;
            work.admit(1, size_of::<usize>())?;
            let mut index = 0usize;
            loop {
                work.admit(1, 2 * size_of::<&Ty>())?;
                let Some(node) = body.get(index) else {
                    return Ok(());
                };
                for node_ty in node.types() {
                    work.push(types, node_ty)?;
                }
                work.admit(1, size_of::<usize>())?;
                index = index
                    .checked_add(1)
                    .ok_or(ObservedValueError::CapacityOverflow)?;
            }
        }
        plan::Plan::Empty => Ok(()),
    }
}
