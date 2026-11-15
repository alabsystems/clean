// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Complete original native replay-context DATA diagnostics, not replay authority.
use super::{
    NativeCompilerFacts, NativeObligationSource, NativeReplayAtom, NativeReplayAtomKind,
    NativeReplayContext, NativeRequestId, NativeUnsupportedModeReason,
    NativeVerificationBundleError as E, retire_native_bundle_errors_observed,
};
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use crate::pred::PredTable;
use crate::{ProofDigest, ProofDigestAlgorithm, ProofId};
use core::mem::{size_of, take};
mod binding;
mod scan;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    text: String,
    pending: Option<E>,
    errors: Vec<E>,
}
impl NativeReplayContext {
    /// Complete unchanged replay-context diagnostics over the actual request
    /// obligation slice, compiler sidecar and module predicate table. This
    /// validates no request/module/proof or replay verdict and mints no authority.
    /// Duplicate requested IDs have set-membership semantics here; the complete
    /// original request pass remains responsible for its separate duplicate error.
    pub fn validation_errors_observed<O: ExecutionObserver>(
        &self,
        request: NativeRequestId,
        obligations: &[ProofId],
        facts: &NativeCompilerFacts,
        predicates: &PredTable<'_>,
        s: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<E>> {
        let mut w = Work { session: s, site };
        w.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
        let mut st = State::default();
        let result = st.run(self, request, obligations, facts, predicates, &mut w);
        st.finish(result, &mut w)
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
    fn fixed<O: ExecutionObserver>(
        &mut self,
        make: impl FnOnce() -> E,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(1, size_of::<E>() + size_of::<Option<E>>())?;
        self.pending = Some(make());
        self.emit(w)
    }
    fn invalid<O: ExecutionObserver>(
        &mut self,
        request: NativeRequestId,
        a: &NativeReplayAtom,
        field: &'static str,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        self.fixed(
            || E::InvalidReplayAtom {
                request,
                atom: a.id,
                field,
            },
            w,
        )
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        w.record(1, size_of::<String>());
        w.text_drop(take(&mut self.text));
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
