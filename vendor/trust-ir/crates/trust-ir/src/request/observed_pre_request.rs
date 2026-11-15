// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Complete original ordered bundle groups BEFORE mandatory request replay.
use super::{
    NativeAdapterInput, NativeVerificationBundle, NativeVerificationBundleError as E,
    retire_native_bundle_errors_observed,
};
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use crate::{ProofDigest, ProofDigestAlgorithm, ProofLineageError};
use core::mem::{size_of, take};
use std::vec::IntoIter;
mod batch;
mod children;
mod scan;
mod storage;
#[cfg(test)]
mod tests;
use children::Group;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    batch: Option<IntoIter<E>>,
    batch_capacity: usize,
    lineage: Vec<ProofLineageError>,
    pending: Option<E>,
    errors: Vec<E>,
}
impl NativeVerificationBundle {
    /// Whole original validate prefix through compiler facts, including exact
    /// module identity, source/provenance/policies/lineage/formula checks.
    /// Actual full requests (including REAL kernel replay) and evidence groups
    /// MUST still follow. An empty list is NOT full validation or authority.
    pub fn pre_request_errors_observed<O: ExecutionObserver>(
        &self,
        s: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<E>> {
        let mut w = Work { session: s, site };
        w.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
        let mut st = State::default();
        let result = st.run(self, &mut w);
        st.finish(result, &mut w)
    }
}
impl State {
    fn fixed<O: ExecutionObserver>(
        &mut self,
        make: impl FnOnce() -> E + Copy,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(1, size_of::<E>() + size_of::<Option<E>>())?;
        self.pending = Some(make());
        self.emit(w)
    }
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
        self.retire_batch(w);
        w.record(1, size_of::<Vec<ProofLineageError>>() + size_of::<E>());
        let _ = E::Lineage(take(&mut self.lineage)).retire_observed(w.session, w.site);
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
