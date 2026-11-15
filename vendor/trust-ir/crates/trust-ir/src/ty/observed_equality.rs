// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Structural type identity with actual observed iterative comparisons.

use super::*;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use core::mem::size_of;
type R<T = ()> = Result<T, ObservedValueError>;

struct Work<'s, 'o, O: ExecutionObserver> {
    session: &'s mut ObservedSession<'o, O>,
    site: ExecutionSite,
}
impl<O: ExecutionObserver> Work<'_, '_, O> {
    fn admit(&mut self, work: usize, bytes: usize) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Validation,
                site: self.site,
                work,
                copy_bytes: bytes,
            })
            .map_err(Into::into)
    }
    fn poll(&mut self) -> R {
        self.admit(1, 0)
    }
    fn reserve<T>(&mut self, rows: &mut Vec<T>) -> R {
        self.poll()?;
        if rows.len() == rows.capacity() {
            let requested = rows
                .len()
                .checked_mul(2)
                .and_then(|n| n.checked_add(1))
                .ok_or(ObservedValueError::CapacityOverflow)?;
            let images = requested
                .checked_add(rows.len())
                .ok_or(ObservedValueError::CapacityOverflow)?;
            self.admit(
                images,
                images
                    .checked_mul(size_of::<T>())
                    .ok_or(ObservedValueError::CapacityOverflow)?,
            )?;
            rows.try_reserve_exact(requested - rows.len())
                .map_err(|_| ObservedValueError::AllocationFailed)?;
        }
        Ok(())
    }
    fn retire<T>(&mut self, value: T) {
        self.session.retirement_poll(self.site);
        drop(value);
        self.session.retirement_poll(self.site);
    }
}
impl Ty {
    /// Exact level-R structural equality under the caller's original observer.
    /// Inline types and variable nominal strings are traversed in actual bounded
    /// steps, with requested scratch admitted before growth. Referenced type IDs
    /// remain identities and are not expanded. No layout or proof is established.
    pub fn structural_eq_observed<O: ExecutionObserver>(
        &self,
        other: &Self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        session.admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site,
            work: 1,
            copy_bytes: size_of::<Work<'_, '_, O>>()
                .checked_add(size_of::<Vec<Task<'_>>>())
                .ok_or(ObservedValueError::CapacityOverflow)?,
        })?;
        let mut work = Work { session, site };
        let result = types(self, other, &mut work);
        finish_equality(result, &mut work)
    }
}
fn finish_equality<O: ExecutionObserver>(result: R<bool>, work: &mut Work<'_, '_, O>) -> R<bool> {
    // Keep the actual old terminal event attempt/fields, but never let it
    // replace a typed local result already held before this later callback.
    let publication: R = work
        .session
        .admit(ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: work.site,
            work: 0,
            copy_bytes: 0,
        })
        .map_err(Into::into);
    result.and_then(|equal| publication.map(|()| equal))
}
#[cfg(test)]
mod precedence_tests;
#[cfg(test)]
mod tests;

enum Task<'a> {
    Pair(&'a Ty, &'a Ty),
    Tail(&'a [Ty], &'a [Ty]),
}

fn types<O: ExecutionObserver>(left: &Ty, right: &Ty, work: &mut Work<'_, '_, O>) -> R<bool> {
    let mut tasks = Vec::new();
    let result = (|| {
        push(&mut tasks, Task::Pair(left, right), work)?;
        while !tasks.is_empty() {
            work.poll()?;
            let Some(task) = tasks.pop() else { break };
            match task {
                Task::Pair(left, right) => {
                    // Char and U32 intentionally share a layout shape, but
                    // are distinct tuple keys under Ty's derived equality.
                    if core::mem::discriminant(left) != core::mem::discriminant(right) {
                        return Ok(false);
                    }
                    let equal = match (left, right) {
                        (Ty::Storage(a), Ty::Storage(b)) => a == b,
                        (Ty::Struct(a), Ty::Struct(b)) => a == b,
                        (Ty::Enum(a), Ty::Enum(b)) => a == b,
                        (Ty::Func(a), Ty::Func(b)) => a == b,
                        (Ty::Record(a), Ty::Record(b)) => a == b,
                        (Ty::Closure(a), Ty::Closure(b)) => a == b,
                        (Ty::Sequence(a), Ty::Sequence(b)) => a == b,
                        (Ty::Array(a, n), Ty::Array(b, m)) => a == b && n == m,
                        (Ty::Set(a, n), Ty::Set(b, m)) => a == b && n == m,
                        (Ty::Refine(a, n), Ty::Refine(b, m)) => a == b && n == m,
                        (Ty::FatPtr(a), Ty::FatPtr(b)) => a == b,
                        (Ty::Vector(a, n), Ty::Vector(b, m))
                        | (Ty::Tensor(a, n), Ty::Tensor(b, m)) => {
                            if n != m {
                                return Ok(false);
                            }
                            push(&mut tasks, Task::Pair(a, b), work)?;
                            true
                        }
                        (Ty::Ref(a), Ty::Ref(b))
                        | (Ty::RefMut(a), Ty::RefMut(b))
                        | (Ty::PtrConst(a), Ty::PtrConst(b))
                        | (Ty::PtrMut(a), Ty::PtrMut(b))
                        | (Ty::Rc(a), Ty::Rc(b)) => {
                            push(&mut tasks, Task::Pair(a, b), work)?;
                            true
                        }
                        (Ty::Tuple(a), Ty::Tuple(b)) => {
                            if a.len() != b.len() {
                                return Ok(false);
                            }
                            push(&mut tasks, Task::Tail(a, b), work)?;
                            true
                        }
                        (Ty::Dialect(a), Ty::Dialect(b)) => {
                            a.version == b.version
                                && text(&a.namespace, &b.namespace, work)?
                                && text(&a.name, &b.name, work)?
                        }
                        (Ty::Handle(a), Ty::Handle(b)) => {
                            text(&a.name, &b.name, work)? && text(&a.runtime, &b.runtime, work)?
                        }
                        _ => payload_free(left),
                    };
                    if !equal {
                        return Ok(false);
                    }
                }
                Task::Tail(left, right) => {
                    if let (Some((a, rest_a)), Some((b, rest_b))) =
                        (left.split_first(), right.split_first())
                    {
                        if !rest_a.is_empty() {
                            push(&mut tasks, Task::Tail(rest_a, rest_b), work)?;
                        }
                        push(&mut tasks, Task::Pair(a, b), work)?;
                    }
                }
            }
        }
        Ok(true)
    })();
    finish_types(result, tasks, work)
}

fn finish_types<O: ExecutionObserver>(
    result: R<bool>,
    tasks: Vec<Task<'_>>,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
    work.retire(tasks);
    // Attempt the same original post-cleanup poll before publishing anything.
    // Preserve a local error held before that later observer callback.
    let retirement = work.poll();
    result.and_then(|equal| retirement.map(|()| equal))
}

// Exhaustive, so a new inhabited Ty variant requires an identity decision.
fn payload_free(ty: &Ty) -> bool {
    match ty {
        Ty::Storage(_) => false,
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
        | Ty::Error
        | Ty::F16
        | Ty::F32
        | Ty::F64
        | Ty::Bool
        | Ty::Ptr
        | Ty::Unit
        | Ty::Never => true,
        Ty::Ext(extension) => extension.unreachable(),
        Ty::Struct(_)
        | Ty::Enum(_)
        | Ty::Func(_)
        | Ty::Record(_)
        | Ty::Closure(_)
        | Ty::Sequence(_)
        | Ty::Array(_, _)
        | Ty::Set(_, _)
        | Ty::Refine(_, _)
        | Ty::FatPtr(_)
        | Ty::Vector(_, _)
        | Ty::Tensor(_, _)
        | Ty::Ref(_)
        | Ty::RefMut(_)
        | Ty::PtrConst(_)
        | Ty::PtrMut(_)
        | Ty::Rc(_)
        | Ty::Tuple(_)
        | Ty::Dialect(_)
        | Ty::Handle(_) => false,
    }
}

fn push<'a, O: ExecutionObserver>(
    tasks: &mut Vec<Task<'a>>,
    task: Task<'a>,
    work: &mut Work<'_, '_, O>,
) -> R {
    work.reserve(tasks)?;
    work.admit(1, size_of::<Task<'_>>())?;
    tasks.push(task);
    Ok(())
}

fn text<O: ExecutionObserver>(left: &str, right: &str, work: &mut Work<'_, '_, O>) -> R<bool> {
    work.poll()?;
    if left.len() != right.len() {
        return Ok(false);
    }
    for (left, right) in left
        .as_bytes()
        .chunks(1024)
        .zip(right.as_bytes().chunks(1024))
    {
        work.admit(
            left.len()
                .checked_add(right.len())
                .ok_or(ObservedValueError::CapacityOverflow)?,
            0,
        )?;
        if left != right {
            return Ok(false);
        }
    }
    Ok(true)
}
