// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual original spec identity, ownership, binding and reference structure.
use super::*;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use crate::proof::{ClausePlace, ClauseSort, ProofFormula};
use core::{
    cmp::Ordering,
    mem::{size_of, take},
};
type R<T = ()> = Result<T, ObservedValueError>;
// The fixed borrowed descriptor is admitted BEFORE its actual construction.
macro_rules! emit {
    ($state:ident,$work:ident,$view:expr) => {{
        $work.admit(1, size_of::<V<'_>>())?;
        output::issue(&mut $state.errors, &mut $state.fields, $view, $work)
    }};
}
mod anchors;
mod bindings;
mod declarations;
mod effective;
mod format;
mod normalize;
mod output;
mod references;
mod retirement;
mod sorts;
mod storage;
#[cfg(test)]
mod tests;
use output::View as V;
use storage::Work;
#[derive(Default)]
struct State<'a> {
    fields: [String; 5],
    detail: String,
    format: Vec<format::Task<'a>>,
    equality: Vec<sorts::Pair<'a>>,
    pending: Option<SpecLinkViolation>,
    errors: Vec<SpecLinkViolation>,
}
/// Exact original structural diagnostics, including their canonical order and
/// deduplication. This excludes linked text parsing, executable linkage,
/// coverage/harness/kernel authority as the ordinary structural pass does.
/// Actual scans/comparisons/formatting/storage use the supplied original owner.
/// No partial accepting diagnostic vector escapes a resource refusal.
pub fn validate_spec_structure_observed<O: ExecutionObserver>(
    specs: &[SpecModule],
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<SpecLinkViolation>> {
    session.admit(ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site,
        work: 1,
        copy_bytes: size_of::<State<'_>>() + size_of::<Work<'_, '_, O>>(),
    })?;
    let mut state = State::default();
    let mut work = Work { session, site };
    let result = (|| {
        state.declarations(specs, &mut work)?;
        state.references(specs, &mut work)?;
        state.normalize(&mut work)
    })();
    state.finish(result, &mut work)
}
impl State<'_> {
    fn begin_detail<O: ExecutionObserver>(&self, work: &mut Work<'_, '_, O>) -> R {
        work.admit(1, 0)?;
        if self.detail.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        Ok(())
    }
    fn clear_detail<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        work.retire_text(&mut self.detail);
        work.admit(1, 0)
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        for field in &mut self.fields {
            work.step(size_of::<String>().saturating_add(1));
            work.retire_text(field);
        }
        work.retire_text(&mut self.detail);
        work.retire_fixed_vec(&mut self.format);
        work.retire_fixed_vec(&mut self.equality);
        work.step(size_of::<Option<SpecLinkViolation>>().saturating_add(1));
        if let Some(error) = self.pending.take() {
            retirement::consume(error, work);
        }
    }
    fn finish<O: ExecutionObserver>(
        &mut self,
        result: R,
        work: &mut Work<'_, '_, O>,
    ) -> R<Vec<SpecLinkViolation>> {
        self.retire_scratch(work);
        match result.and_then(|()| work.publication(1, size_of::<Vec<SpecLinkViolation>>())) {
            Ok(()) => Ok(take(&mut self.errors)),
            Err(error) => {
                retirement::consume_vec(take(&mut self.errors), work);
                Err(work.terminal(error))
            }
        }
    }
}
// Borrowed concrete scans replace discarded indexes with actual repeated work;
// normalization uses an observed stable insertion sort, not old complexity.
// Successful caller/input disposal, linked surface/full module/native/source/
// proof authority and physical std/Unicode/allocator/deallocator/OOM/panic/
// unwind/RSS/machine-work/hardtime remain OPEN. No owner/grant/deadline/TLS/fuel.
