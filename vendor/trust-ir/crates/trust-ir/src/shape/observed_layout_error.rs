// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Same-owner LayoutError text and consuming cleanup; never layout authority.
//!
//! Returned text is caller owned. Input/output disposal on successful display
//! remains the caller's responsibility. Scalar std escape classification is a
//! fixed primitive boundary, not a measured allocator or hard-time bound.
use super::{LayoutError, PointerMetadataShape, TyShape};
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use core::mem::size_of;

mod display;
mod retirement;
mod shapes;
mod storage;
#[cfg(test)]
mod tests;

type R<T = ()> = Result<T, ObservedValueError>;
use storage::Work;

impl LayoutError {
    /// Render the existing diagnostic under the caller's original observation.
    /// Resource refusal is operational and never substitutes a layout message.
    pub fn display_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<String> {
        let mut work = Work { session, site };
        work.admit(1, size_of::<String>())?;
        let mut output = String::new();
        let result = display::write(self, &mut work, &mut output)
            .and_then(|()| work.publication(1, size_of::<String>()));
        match result {
            Ok(()) => Ok(output),
            Err(error) => {
                work.retire_text(output);
                Err(work.terminal(error))
            }
        }
    }

    /// Consume every field, even after refusal, in that same original session.
    /// A sticky stop survives cleanup and rejects the final publication event.
    pub fn retire_observed<O: ExecutionObserver>(
        self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let mut work = Work { session, site };
        retirement::consume(self, &mut work);
        work.publication(0, 0)
    }
}
