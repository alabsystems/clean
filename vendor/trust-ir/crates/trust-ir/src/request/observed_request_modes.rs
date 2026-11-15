// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Complete existing MC/WP mode and request-diagnostics DATA guards.
use super::{
    NativeDiagnosticsPolicy, NativeReplayAtom, NativeReplayAtomKind, NativeRequestId,
    NativeVerificationBundleError as E, TrustMcNativeRequest, TrustMcVerificationMode as McMode,
    TrustWpNativeRequest, TrustWpVerificationMode as WpMode, retire_native_bundle_errors_observed,
};
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use core::mem::{size_of, take};
mod guards;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    pending: Option<E>,
    errors: Vec<E>,
}
enum Check<'a> {
    Mc(&'a TrustMcNativeRequest),
    Wp(&'a TrustWpNativeRequest),
    Diagnostics(NativeRequestId, &'a NativeDiagnosticsPolicy),
}
impl TrustMcNativeRequest {
    /// Complete original MC option checks only, not model checking or request
    /// admission. No option value, default or mode is rewritten.
    pub fn mode_errors_observed<O: ExecutionObserver>(
        &self,
        s: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<E>> {
        run(Check::Mc(self), s, site)
    }
}
impl TrustWpNativeRequest {
    /// Complete original WP mode checks, including both independent actual
    /// strongest-postcondition atom searches, before remaining option guards.
    pub fn mode_errors_observed<O: ExecutionObserver>(
        &self,
        s: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<E>> {
        run(Check::Wp(self), s, site)
    }
}
impl NativeDiagnosticsPolicy {
    /// Complete original per-request diagnostic-policy errors with its exact
    /// original request ID. Bundle-level diagnostic checks remain separate.
    pub fn request_errors_observed<O: ExecutionObserver>(
        &self,
        request: NativeRequestId,
        s: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<E>> {
        run(Check::Diagnostics(request, self), s, site)
    }
}
fn run<O: ExecutionObserver>(
    check: Check<'_>,
    s: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<E>> {
    let mut w = Work { session: s, site };
    w.admit(
        1,
        size_of::<State>() + size_of::<Check<'_>>() + size_of::<Work<'_, '_, O>>(),
    )?;
    let mut st = State::default();
    let result = match check {
        Check::Mc(r) => st.mc(r, &mut w),
        Check::Wp(r) => st.wp(r, &mut w),
        Check::Diagnostics(id, p) => st.diagnostics(id, p, &mut w),
    };
    st.finish(result, &mut w)
}
impl State {
    fn fixed<O: ExecutionObserver>(
        &mut self,
        make: impl FnOnce() -> E,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        // All private constructors capture only fixed Copy fields.
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
    fn retire_scratch<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
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
