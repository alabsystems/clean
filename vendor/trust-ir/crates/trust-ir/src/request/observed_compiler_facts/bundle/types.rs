// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The two inline generic-argument walks; nominal tables are not expanded by
//! either original rule. Scratch contains only borrowed references.

use super::*;

fn push<T: Copy, O: ExecutionObserver>(
    pending: &mut Vec<T>,
    value: T,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R {
    reserve(pending, session, site)?;
    admit(session, site, 1, size_of::<T>())?;
    pending.push(value);
    Ok(())
}

pub(super) fn contains_error<O: ExecutionObserver>(
    root: &Ty,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<bool> {
    admit(session, site, 1, size_of::<Vec<&Ty>>())?;
    let mut pending = Vec::new();
    let result: R<bool> = (|| {
        push(&mut pending, root, session, site)?;
        while !pending.is_empty() {
            admit(session, site, 1, 0)?;
            let Some(ty) = pending.pop() else {
                break;
            };
            match ty {
                Ty::Error => return Ok(true),
                Ty::Vector(child, _)
                | Ty::Tensor(child, _)
                | Ty::Ref(child)
                | Ty::RefMut(child)
                | Ty::PtrConst(child)
                | Ty::PtrMut(child)
                | Ty::Rc(child) => push(&mut pending, child.as_ref(), session, site)?,
                Ty::Tuple(children) => {
                    for child in children.iter().rev() {
                        admit(session, site, 1, 0)?;
                        push(&mut pending, child, session, site)?;
                    }
                }
                _ => {}
            }
        }
        Ok(false)
    })();
    retire_vec(&mut pending, session, site);
    if session.first_refusal().is_some() {
        return Err(ObservedValueError::AdmissionRefused);
    }
    let result = result?;
    admit(session, site, 1, 0)?;
    Ok(result)
}

#[derive(Clone, Copy)]
enum Task<'a> {
    Pair(&'a Constant, &'a Ty),
    Lanes(&'a [Constant], &'a Ty),
}

pub(super) fn constant_matches<O: ExecutionObserver>(
    root: &Constant,
    ty: &Ty,
    bits: u32,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<bool> {
    admit(session, site, 1, size_of::<Vec<Task<'_>>>())?;
    let mut pending = Vec::new();
    let result: R<bool> = (|| {
        push(&mut pending, Task::Pair(root, ty), session, site)?;
        while !pending.is_empty() {
            admit(session, site, 1, 0)?;
            let Some(task) = pending.pop() else {
                break;
            };
            match task {
                Task::Lanes(children, ty) => {
                    if let Some((first, rest)) = children.split_first() {
                        if !rest.is_empty() {
                            push(&mut pending, Task::Lanes(rest, ty), session, site)?;
                        }
                        push(&mut pending, Task::Pair(first, ty), session, site)?;
                    }
                }
                Task::Pair(value, ty) => {
                    if let (Constant::Vector(children), Ty::Vector(element, lanes)) = (value, ty) {
                        admit(session, site, 2, 0)?;
                        if children.len() != *lanes as usize {
                            return Ok(false);
                        }
                        push(&mut pending, Task::Lanes(children, element), session, site)?;
                    } else {
                        admit(session, site, 64, 0)?;
                        if !leaf_matches(value, ty, bits) {
                            return Ok(false);
                        }
                    }
                }
            }
        }
        Ok(true)
    })();
    retire_vec(&mut pending, session, site);
    if session.first_refusal().is_some() {
        return Err(ObservedValueError::AdmissionRefused);
    }
    let result = result?;
    admit(session, site, 1, 0)?;
    Ok(result)
}

// Only fixed discriminants, scalar payloads and O(1) slice headers/heads.
fn leaf_matches(value: &Constant, ty: &Ty, bits: u32) -> bool {
    match (value, ty) {
        (Constant::Int(value), Ty::Char) => {
            (0..=0x10ffff).contains(value) && !(0xd800..=0xdfff).contains(value)
        }
        (Constant::Int(value), ty) if ty.is_integer() => {
            ty.bit_width_with(bits)
                .is_some_and(|bits| match (bits, ty.is_signed()) {
                    (1..=127, true) => {
                        let half = 1i128 << (bits - 1);
                        (-half..half).contains(value)
                    }
                    (1..=127, false) => *value >= 0 && *value >> bits == 0,
                    (128, true) => true,
                    (128, false) => *value >= 0,
                    _ => false,
                })
        }
        (Constant::U128(_), Ty::U128) | (Constant::Int(_), Ty::Ptr) => true,
        (Constant::Bytes { data, .. }, Ty::Array(_, count)) => *count == data.len() as u64,
        (Constant::Aggregate(elements), Ty::FatPtr(_)) => {
            matches!(elements.as_slice(), [Constant::Int(0), Constant::Int(0)])
        }
        (Constant::Float(_), ty) if ty.is_float() => true,
        (Constant::Bool(_), Ty::Bool) => true,
        (
            Constant::Aggregate(_),
            Ty::Tuple(_) | Ty::Array(_, _) | Ty::Struct(_) | Ty::Record(_),
        ) => true,
        (Constant::Aggregate(elements), Ty::Enum(_)) => {
            matches!(elements.first(), Some(Constant::Int(_)))
        }
        (Constant::Array(_), Ty::Array(_, _)) => true,
        (Constant::Splat { len, .. }, Ty::Array(_, count)) => len == count,
        (Constant::Sequence(_), Ty::Sequence(_))
        | (Constant::Set(_), Ty::Set(_, _))
        | (Constant::Record(_), Ty::Record(_))
        | (Constant::Closure { .. }, Ty::Closure(_))
        | (Constant::FnDef(_), Ty::Func(_))
        | (Constant::SymbolAddr { .. }, Ty::Ptr | Ty::Func(_))
        | (Constant::PhantomData, Ty::Unit) => true,
        _ => false,
    }
}
