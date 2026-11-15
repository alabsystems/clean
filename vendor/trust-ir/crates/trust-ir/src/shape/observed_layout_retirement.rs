// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Consuming layout-result cleanup under the caller's original observation.
//!
//! These methods consume owned fields even after a sticky refusal. An Arc
//! release consumes only this reference; another owner retains its own cleanup
//! obligation. No successful result, layout/source/proof authority, allocation
//! or deallocation bound, OOM/panic/unwind containment or hard-time claim follows.
use super::{EnumLayoutShape, FieldOffsetShape, TyLayoutKind, TyLayoutShape};
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use crate::ty::{EnumLayoutDescriptor, EnumTagEncoding};
use core::mem::size_of;
use std::sync::Arc;

mod enum_layout;
mod storage;
#[cfg(test)]
mod tests;
mod ty_layout;
use storage::Work;
type R = Result<(), ObservedValueError>;

impl TyLayoutShape {
    /// Consume this shape, all actual field names and buffers in the same
    /// supplied session. A stop is returned only after complete local cleanup.
    pub fn retire_observed<O: ExecutionObserver>(
        self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let mut work = Work { session, site };
        ty_layout::consume(self, &mut work);
        work.finish()
    }

    /// Atomically release this Arc, explicitly consuming the extracted shape
    /// if it was the last strong reference. No failed-try_unwrap/drop fallback.
    pub fn retire_arc_observed<O: ExecutionObserver>(
        self: Arc<Self>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let mut work = Work { session, site };
        work.arc::<Self>();
        // Primary alloc/sync.rs into_inner uses ManuallyDrop and one atomic
        // decrement: None releases this reference without ordinary payload
        // Drop; Some retains the complete unique payload for explicit cleanup.
        match Arc::into_inner(self) {
            Some(shape) => ty_layout::consume(shape, &mut work),
            None => work.fixed(()),
        }
        work.poll();
        work.finish()
    }
}

impl EnumLayoutShape {
    /// Consume discriminants, the optional full descriptor and every nested
    /// offset buffer, even if the original session has already stopped.
    pub fn retire_observed<O: ExecutionObserver>(
        self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let mut work = Work { session, site };
        enum_layout::consume(self, &mut work);
        work.finish()
    }

    /// Release exactly this Arc using into_inner. A shared payload remains
    /// another owner's responsibility; a unique payload is fully drained here.
    pub fn retire_arc_observed<O: ExecutionObserver>(
        self: Arc<Self>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let mut work = Work { session, site };
        work.arc::<Self>();
        match Arc::into_inner(self) {
            Some(shape) => enum_layout::consume(shape, &mut work),
            None => work.fixed(()),
        }
        work.poll();
        work.finish()
    }
}
