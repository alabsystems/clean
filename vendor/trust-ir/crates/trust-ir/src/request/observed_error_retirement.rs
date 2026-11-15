// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Consuming disposal of the complete native bundle diagnostic enum.
//! No validation, authority, source identity or permission is constructed.
use super::{NativeSourceLanguage, NativeVerificationBundleError as E};
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use crate::proof::FormulaSite;
use crate::{Producer, ProofLineageError};
use core::mem::{align_of, size_of};
use std::collections::BTreeSet;
mod lineage;
mod payloads;
mod storage;
#[cfg(test)]
mod tests;
mod variants;
use storage::Work;
type R = Result<(), ObservedValueError>;
impl E {
    /// Consume every owned field under the caller's original session/site.
    /// The caller prepays its owning argument transport. Cleanup always runs
    /// after a sticky stop; final healthy publication is (0 work, 0 copy).
    /// Logical drop accounting is not a physical allocator/deallocator bound.
    pub fn retire_observed<O: ExecutionObserver>(
        self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let mut work = Work { session, site };
        work.bundle(self);
        work.finish()
    }
}
/// Consume a complete returned bundle diagnostic batch, including its spare
/// capacity. No input is validated and no accepting subset is published.
/// The caller prepays the whole argument transport before handing it over.
pub fn retire_native_bundle_errors_observed<O: ExecutionObserver>(
    errors: Vec<E>,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R {
    let mut work = Work { session, site };
    work.bundle_rows(errors);
    work.finish()
}
