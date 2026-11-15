// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Complete original identity metadata checks. No replay/source authority.
use super::{
    NativeRequestId, NativeToolIdentity, NativeVerificationBundleError as E,
    NativeVerifierSuite as Suite, canonical_name_matches_family, canonical_tool_name_observed,
    retire_native_bundle_errors_observed,
};
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use crate::{ProofCertificateRef, ProofDigestAlgorithm, ProofReplayIdentity};
use core::mem::{size_of, take};
mod names;
mod replay;
mod storage;
#[cfg(test)]
mod tests;
mod tool;
use names::Kind;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    canonical: String,
    text: String,
    pending: Option<E>,
    errors: Vec<E>,
}
enum Check<'a> {
    Tool(&'static str, &'a NativeToolIdentity),
    Verifier(NativeRequestId, Suite, &'a NativeToolIdentity),
    Replay(NativeRequestId, Suite, &'a ProofReplayIdentity),
    Certificate(NativeRequestId, Suite, &'a ProofCertificateRef),
}
impl NativeToolIdentity {
    /// Same complete ordinary tool metadata checks and diagnostic field label.
    /// A clean metadata list does not identify a running verifier or its bytes.
    pub fn validation_errors_observed<O: ExecutionObserver>(
        &self,
        field: &'static str,
        s: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<E>> {
        run(Check::Tool(field, self), s, site)
    }
    /// Entire ordinary expected-verifier suite metadata check, with its exact
    /// existing empty-canonical-name exception. No verifier is executed here.
    pub fn verifier_suite_errors_observed<O: ExecutionObserver>(
        &self,
        request: NativeRequestId,
        suite: Suite,
        s: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<E>> {
        run(Check::Verifier(request, suite, self), s, site)
    }
}
impl ProofReplayIdentity {
    /// Entire ordinary replay identity metadata check, not transcript replay.
    pub fn validation_errors_observed<O: ExecutionObserver>(
        &self,
        request: NativeRequestId,
        suite: Suite,
        s: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<E>> {
        run(Check::Replay(request, suite, self), s, site)
    }
}
impl ProofCertificateRef {
    /// Entire ordinary certificate-prover suite metadata check. This does not
    /// discharge, resolve, authenticate or replay any cited certificate.
    pub fn verifier_suite_errors_observed<O: ExecutionObserver>(
        &self,
        request: NativeRequestId,
        suite: Suite,
        s: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<E>> {
        run(Check::Certificate(request, suite, self), s, site)
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
        Check::Tool(field, t) => st.tool(field, t, &mut w),
        Check::Verifier(r, q, t) => st.verifier(r, q, t, &mut w),
        Check::Replay(r, q, p) => st.replay(r, q, p, &mut w),
        Check::Certificate(r, q, c) => st.certificate(r, q, c, &mut w),
    };
    st.finish(result, &mut w)
}
impl State {
    fn fixed<O: ExecutionObserver>(
        &mut self,
        make: impl FnOnce() -> E,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        // Every private caller captures only fixed Copy fields. Price whole E
        // before construction, then retain it before either output fee.
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
        w.record(1, size_of::<String>());
        w.text_drop(take(&mut self.canonical));
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
