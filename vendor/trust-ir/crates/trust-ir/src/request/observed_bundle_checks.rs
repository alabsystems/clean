// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Two complete existing native bundle DATA checks, never replay/authority.
use super::{
    NativeVerificationBundle, NativeVerificationBundleError as E,
    retire_native_bundle_errors_observed,
};
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use crate::{Block, Function, Producer, ProofDigest};
use core::mem::{size_of, take};
mod scan;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Clone, Copy)]
enum Rule {
    Reference,
    Lineage,
}
#[derive(Default)]
struct State {
    text: String,
    pending: Option<E>,
    errors: Vec<E>,
}
impl NativeVerificationBundle {
    /// Entire original TRust-only permission-spelling check. The caller still
    /// performs every other bundle/module/replay check; this mints no authority.
    pub fn reference_spelling_errors_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<E>> {
        run(self, Rule::Reference, session, site)
    }
    /// Entire original source/target membership check, including physical
    /// duplicate nodes and short-circuiting. A matching digest is DATA only.
    pub fn lineage_digest_errors_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<E>> {
        run(self, Rule::Lineage, session, site)
    }
}
fn run<O: ExecutionObserver>(
    bundle: &NativeVerificationBundle,
    rule: Rule,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<Vec<E>> {
    let mut w = Work { session, site };
    w.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = match rule {
        Rule::Reference => state.references(bundle, &mut w),
        Rule::Lineage => state.lineage(bundle, &mut w),
    };
    state.finish(result, &mut w)
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
        w.record(1, size_of::<String>());
        w.text_drop(take(&mut self.text));
        w.record(1, size_of::<Option<E>>());
        if let Some(error) = self.pending.take() {
            let _ = error.retire_observed(w.session, w.site);
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
                // Preserve the already-held operational error; cleanup cannot
                // replace it with a later refusal. Session keeps first cause.
                Err(error)
            }
        }
    }
}
