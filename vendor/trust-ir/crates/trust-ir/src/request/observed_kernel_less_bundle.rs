// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Complete original core bundle validation ONLY without the Clean kernel.
//! This DATA diagnostic result mints no source marker or proof currency.
use super::{
    NativeVerificationBundle, NativeVerificationBundleError as E,
    retire_native_bundle_errors_observed,
};
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use core::mem::{size_of, take};
use std::vec::IntoIter;
mod batch;
mod children;
mod retirement;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
type Validation = Result<(), Vec<E>>;
#[derive(Default)]
struct State {
    batch: Option<IntoIter<E>>,
    batch_capacity: usize,
    pending: Option<E>,
    errors: Vec<E>,
    output: Option<Validation>,
}
impl NativeVerificationBundle {
    /// Exact whole ordinary validate result in a genuinely kernel-less build,
    /// wrapped in the same original owner's operational Result. All original
    /// pre-request, full request and full evidence groups run in order.
    /// This method is absent with clean-expr and never mints live source or
    /// proof authority, including on Ok(Ok(())). Whole physical bounds remain
    /// subject to the actual inherited primitive profiles.
    pub fn validate_kernel_less_observed<O: ExecutionObserver>(
        &self,
        s: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Validation> {
        let mut w = Work { session: s, site };
        w.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
        let mut st = State::default();
        let result = st.run(self, &mut w);
        st.finish(result, &mut w)
    }
    /// Consume the complete owning inner result under the SAME original
    /// session/site. Healthy retirement ends with Publication(0,0); a sticky
    /// stop still drains all fields/backing and suppresses healthy publication.
    pub fn retire_kernel_less_validation_observed<O: ExecutionObserver>(
        result: Validation,
        s: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let mut w = Work { session: s, site };
        w.record(1, size_of::<Validation>() + size_of::<Work<'_, '_, O>>());
        match result {
            Err(rows) => retire_native_bundle_errors_observed(rows, w.session, w.site),
            Ok(()) => w.terminal(),
        }
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
    fn ready<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) -> R {
        w.admit(
            2,
            size_of::<Validation>()
                + size_of::<Option<Validation>>()
                + size_of::<Vec<E>>()
                + 2 * size_of::<bool>(),
        )?;
        if self.output.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        self.output = Some(if self.errors.is_empty() {
            Ok(())
        } else {
            Err(take(&mut self.errors))
        });
        // In the healthy empty case this owns any spare errors backing until
        // complete consuming retirement. The whole output remains in State.
        self.retire_errors(w);
        w.publication(size_of::<Validation>() + size_of::<Option<Validation>>())
    }
    fn finish<O: ExecutionObserver>(
        &mut self,
        result: R,
        w: &mut Work<'_, '_, O>,
    ) -> R<Validation> {
        self.retire_scratch(w);
        // Do not evaluate ready/publication after an already-held local Err.
        let result = result.and_then(|()| self.ready(w));
        match result {
            Ok(()) => self.output.take().ok_or(ObservedValueError::InvalidRange),
            Err(error) => {
                self.retire_errors(w);
                self.retire_output(w);
                Err(error)
            }
        }
    }
}
