// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Exact ordered schema/digest/wire prefix, never full bundle admission.
use super::{
    NativeVerificationBundle, NativeVerificationBundleError as E,
    retire_native_bundle_errors_observed,
};
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use crate::{ProofDigest, ProofDigestAlgorithm};
use core::mem::{size_of, take};
mod scan;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    batch: Vec<E>,
    actual: Option<ProofDigest>,
    pending: Option<E>,
    errors: Vec<E>,
}
impl NativeVerificationBundle {
    /// Exact original initial validate group: schema, claimed module digest,
    /// COMPLETE actual wire diagnostics, and only-if-encodable actual module
    /// digest comparison. All later original groups remain mandatory; this
    /// DATA prefix is not full validation or source/kernel/proof authority.
    pub fn identity_prefix_errors_observed<O: ExecutionObserver>(
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
        w.reserve(&mut self.errors)?;
        w.admit(1, size_of::<E>() + size_of::<Option<E>>())?;
        self.errors.push(
            self.pending
                .take()
                .ok_or(ObservedValueError::InvalidRange)?,
        );
        Ok(())
    }
    fn flush<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) -> R {
        let mut at = 0;
        while w.at(&self.batch, at)?.is_some() {
            w.reserve(&mut self.errors)?;
            w.admit(1, 2 * size_of::<E>())?;
            let row = core::mem::replace(&mut self.batch[at], E::EmptyRequests);
            self.errors.push(row);
            w.next(&mut at)?;
        }
        Ok(())
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        w.record(1, size_of::<Vec<E>>());
        let _ = retire_native_bundle_errors_observed(take(&mut self.batch), w.session, w.site);
        w.record(1, size_of::<Option<ProofDigest>>());
        let _ = self.actual.take();
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
