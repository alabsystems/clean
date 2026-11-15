// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Exact original sorted set-difference DATA errors, never request authority.
use super::{
    NativeEvidenceBundle, NativeRequestId, NativeVerificationBundleError as E,
    NativeVerificationRequest, retire_native_bundle_errors_observed,
};
use crate::ProofId;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use core::mem::{size_of, take};
mod sets;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    requested: Vec<ProofId>,
    supplied: Vec<ProofId>,
    pending: Option<E>,
    errors: Vec<E>,
}
#[derive(Clone, Copy)]
enum Side {
    Requested,
    Supplied,
}
impl Side {
    fn other(self) -> Self {
        match self {
            Self::Requested => Self::Supplied,
            Self::Supplied => Self::Requested,
        }
    }
}
impl NativeEvidenceBundle {
    /// Entire ordinary symmetric membership diagnostic helper. It reports
    /// unique ascending requested-minus-supplied then supplied-minus-requested.
    /// Request ID/digest/suite/provenance/replay binding remains the caller's
    /// separate work; arbitrary matching sets confer no authority here.
    pub fn obligation_errors_observed<O: ExecutionObserver>(
        &self,
        request: &NativeVerificationRequest,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<E>> {
        let mut w = Work { session, site };
        w.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
        let mut state = State::default();
        let result = state.run(request, self, &mut w);
        state.finish(result, &mut w)
    }
}
impl State {
    fn emit<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) -> R {
        w.reserve(&mut self.errors)?;
        w.admit(1, size_of::<E>() + size_of::<Option<E>>())?;
        self.errors.push(
            self.pending
                .take()
                .ok_or(ObservedValueError::InvalidRange)?,
        );
        Ok(())
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        w.record(1, size_of::<Vec<ProofId>>());
        w.copy_rows(take(&mut self.requested));
        w.record(1, size_of::<Vec<ProofId>>());
        w.copy_rows(take(&mut self.supplied));
        w.record(1, size_of::<Option<E>>());
        if let Some(e) = self.pending.take() {
            let _ = e.retire_observed(w.session, w.site);
        }
        w.poll();
    }
    fn finish<O: ExecutionObserver>(&mut self, result: R, w: &mut Work<'_, '_, O>) -> R<Vec<E>> {
        self.retire_scratch(w);
        match result.and_then(|()| w.publication(size_of::<Vec<E>>())) {
            Ok(()) => Ok(take(&mut self.errors)),
            Err(error) => {
                w.record(1, size_of::<Vec<E>>());
                let _ =
                    retire_native_bundle_errors_observed(take(&mut self.errors), w.session, w.site);
                Err(error)
            }
        }
    }
}
