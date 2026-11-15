// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual module-local spec executable targets; no certifying authority.
use super::*;
use crate::Function;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use crate::ty::{DialectTy, FatPtrKind, HandleTy, SetRepr};
use core::{
    cmp::Ordering,
    mem::{size_of, take},
};
mod debug;
mod normalize;
mod scan;
mod storage;
#[cfg(test)]
mod tests;
use scan::Role;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State<'a> {
    fields: [String; 2],
    detail: String,
    tasks: Vec<debug::Task<'a>>,
    pending: Option<SpecLinkViolation>,
    errors: Vec<SpecLinkViolation>,
}
/// Exact ordinary executable action/projection diagnostics, canonically sorted
/// and deduplicated. This checks body PRESENCE, names and projection signature
/// shape only; it authenticates neither executable bodies nor spec/proof claims.
/// Every actual visit, text operation and owned output uses the supplied owner.
/// No partial accepting vector escapes an operational refusal.
pub fn validate_spec_executable_links_observed<O: ExecutionObserver>(
    module: &Module,
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
        state.run(module, &mut work)?;
        state.normalize(&mut work)
    })();
    state.finish(result, &mut work)
}
impl State<'_> {
    fn begin<O: ExecutionObserver>(&self, work: &mut Work<'_, '_, O>) -> R {
        work.admit(1, 0)?;
        if self.detail.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
        Ok(())
    }
    fn issue<O: ExecutionObserver>(
        &mut self,
        spec: &SpecModule,
        anchor: &SpecAnchor,
        role: Role,
        function: FuncId,
        work: &mut Work<'_, '_, O>,
    ) -> R {
        work.admit(2, 0)?;
        for field in &self.fields {
            if field.capacity() != 0 {
                return Err(ObservedValueError::InvalidRange);
            }
        }
        work.text(&spec.name, &mut self.fields[0])?;
        work.text(&anchor.action, &mut self.fields[1])?;
        work.reserve(&mut self.errors)?;
        work.admit(1, size_of::<SpecLinkViolation>())?;
        self.errors
            .push(SpecLinkViolation::ExecutableTargetInvalid {
                machine: take(&mut self.fields[0]),
                action: take(&mut self.fields[1]),
                target: role.label(),
                function: function.index(),
                detail: take(&mut self.detail),
            });
        Ok(())
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        for field in &mut self.fields {
            work.step(size_of::<String>().saturating_add(1));
            work.retire_text(field);
        }
        work.retire_text(&mut self.detail);
        work.retire_fixed_vec(&mut self.tasks);
        work.step(size_of::<Option<SpecLinkViolation>>().saturating_add(1));
        if let Some(error) = self.pending.take() {
            let _ = error.retire_observed(work.session, work.site);
        }
    }
    fn consume_errors<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) {
        loop {
            work.step(size_of::<Option<SpecLinkViolation>>().saturating_add(1));
            let Some(error) = self.errors.pop() else {
                break;
            };
            let _ = error.retire_observed(work.session, work.site);
        }
        work.step(size_of::<Vec<SpecLinkViolation>>().saturating_add(1));
        drop(take(&mut self.errors));
        work.poll();
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
                self.consume_errors(work);
                Err(work.terminal(error))
            }
        }
    }
}
// Successful caller/input cleanup, executable body validity, full structural/
// linked-text/coverage/harness/module/native/source/proof authority and physical
// std/allocator/deallocator/OOM/panic/unwind/RSS/hard-time guarantees remain OPEN.
