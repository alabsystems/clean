// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Structural tuple identity without recursive Ty clone/hash/equality helpers.

use super::*;

#[derive(Clone, Copy)]
enum Task<'a> {
    Pair(&'a Ty, &'a Ty),
    Tail(&'a [Ty], &'a [Ty]),
}

pub(super) fn types<O: ExecutionObserver>(
    left: &Ty,
    right: &Ty,
    work: &mut Work<'_, '_, O>,
) -> R<bool> {
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
    work.retire_copy_vec(tasks);
    work.poll()?;
    result
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
