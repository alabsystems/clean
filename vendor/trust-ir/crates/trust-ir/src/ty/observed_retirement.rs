// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Allocation-free retirement of an owned inline type tree.
use super::*;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
#[cfg(test)]
mod tests;

impl Ty {
    /// Consume this type with an original-observer callback inside each actual
    /// payload step, even after an earlier refusal. No scratch allocation or
    /// recursive type Drop is used. Refusal remains latched, and no new grant,
    /// deadline, TLS capture or owner is created. Allocator deallocation latency
    /// and the enclosing caller's other inputs remain separate limitations.
    pub fn retire_observed<O: ExecutionObserver>(
        self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> Result<(), ObservedValueError> {
        retire_type(self, session, site);
        session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site,
                work: 0,
                copy_bytes: 0,
            })
            .map_err(Into::into)
    }
}

pub(crate) fn retire_type<O: ExecutionObserver>(
    root: Ty,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    let mut current = Some(root);
    let mut pending = Vec::new();
    loop {
        session.retirement_step(site, 1);
        let value = if let Some(value) = current.take() {
            value
        } else if let Some(value) = pending.pop() {
            value
        } else {
            break;
        };
        match value {
            Ty::Storage(_) => {}
            Ty::Tuple(mut children) => {
                if let Some(next) = children.pop() {
                    if !pending.is_empty() {
                        // pop() freed ONE existing slot: push below cannot grow
                        // this Vec. Store the previous continuation in that slot
                        // instead of allocating a separate traversal stack.
                        session.retirement_step(site, 1);
                        children.push(Ty::Tuple(core::mem::take(&mut pending)));
                    }
                    let empty = core::mem::replace(&mut pending, children);
                    // The prior continuation was moved above, or was empty.
                    // No recursive Ty is owned by this buffer's Drop.
                    drop_flat(empty, session, site);
                    current = Some(next);
                } else {
                    drop_flat(children, session, site);
                }
            }
            Ty::Vector(child, _)
            | Ty::Tensor(child, _)
            | Ty::Ref(child)
            | Ty::RefMut(child)
            | Ty::PtrConst(child)
            | Ty::PtrMut(child)
            | Ty::Rc(child) => {
                session.retirement_step(site, 1);
                let inner = unbox(child);
                session.retirement_poll(site);
                current = Some(inner);
            }
            Ty::Dialect(value) => {
                session.retirement_step(site, 1);
                let DialectTy {
                    namespace,
                    name,
                    version: _,
                } = unbox(value);
                session.retirement_poll(site);
                drop_flat(namespace, session, site);
                drop_flat(name, session, site);
            }
            Ty::Handle(value) => {
                session.retirement_step(site, 1);
                let HandleTy { name, runtime } = unbox(value);
                session.retirement_poll(site);
                drop_flat(name, session, site);
                drop_flat(runtime, session, site);
            }
            // These payloads own no heap children; referenced IDs are not an
            // owned graph and must never be chased during destruction.
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
            | Ty::Never
            | Ty::FatPtr(_)
            | Ty::Struct(_)
            | Ty::Array(_, _)
            | Ty::Enum(_)
            | Ty::Func(_)
            | Ty::Set(_, _)
            | Ty::Sequence(_)
            | Ty::Record(_)
            | Ty::Closure(_)
            | Ty::Refine(_, _) => {}
            Ty::Ext(extension) => extension.unreachable(),
        }
    }
    // The loop has consumed every original payload and every continuation;
    // pending is empty. Retiring the final buffer needs no spare workspace.
    drop_flat(pending, session, site);
}

#[allow(
    clippy::boxed_local,
    reason = "moving the value out of its box is the point: the box's storage is retired here"
)]
fn unbox<T>(value: Box<T>) -> T {
    *value
}
fn drop_flat<T, O: ExecutionObserver>(
    value: T,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) {
    session.retirement_step(site, 1);
    drop(value);
    session.retirement_poll(site);
}
