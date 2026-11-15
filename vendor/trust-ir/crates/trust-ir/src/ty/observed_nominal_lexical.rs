// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual nominal lexical validation without opaque chars/split iterators.
use super::*;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use core::mem::size_of;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
impl DialectTy {
    /// Exact ordinary namespace/name/version errors, in their original order,
    /// with actual bounded ASCII byte work under this same original owner.
    /// Non-ASCII fails the same alphabet without decoding an opaque scalar
    /// iterator. No namespace schema admission, type/source/proof authority or
    /// ownership grant follows. Original input disposal and physical std/
    /// Unicode/allocator/OOM/panic/unwind/RSS/hardtime remain OPEN.
    pub fn validate_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Result<(), DialectTyError>> {
        let mut work = Work { session, site };
        work.admit(
            8,
            size_of::<Work<'_, '_, O>>() + 4 * size_of::<Result<(), DialectTyError>>(),
        )?;
        if !work.segment(&self.namespace)? {
            return work.publish(Err(DialectTyError::InvalidNamespace));
        }
        if !work.segment(&self.name)? {
            return work.publish(Err(DialectTyError::InvalidName));
        }
        work.admit(1, size_of::<u32>() + size_of::<bool>())?;
        work.publish(if self.version == 0 {
            Err(DialectTyError::ZeroVersion)
        } else {
            Ok(())
        })
    }
}
impl HandleTy {
    /// Exact ordinary name then nonempty `::`-separated runtime grammar. Every
    /// actual byte/segment delimiter and original stop is observed. This does
    /// not pin a runtime or establish any type/module/proof/source authority.
    /// No owner, grant, deadline, TLS or interpreter fuel is created/reset;
    /// original input disposal and physical primitive/time limits remain OPEN.
    pub fn validate_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Result<(), HandleTyError>> {
        let mut work = Work { session, site };
        work.admit(
            8,
            size_of::<Work<'_, '_, O>>() + 3 * size_of::<Result<(), HandleTyError>>(),
        )?;
        if !work.segment(&self.name)? {
            return work.publish(Err(HandleTyError::InvalidName));
        }
        if !work.runtime(&self.runtime)? {
            return work.publish(Err(HandleTyError::InvalidRuntime));
        }
        work.publish(Ok(()))
    }
}
