// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Exact existing canonical_tool_name DATA transform under original custody.
use super::NativeToolIdentity;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use core::mem::{size_of, take};
mod names;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    normalized: String,
    canonical: String,
}
impl NativeToolIdentity {
    /// Same bytes as canonical_name(), observed throughout actual construction.
    /// This normalizes display DATA; it is not verifier/source/replay authority.
    pub fn canonical_name_observed<O: ExecutionObserver>(
        &self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<String> {
        canonical_tool_name_observed(&self.name, session, site)
    }
}
pub(crate) fn canonical_tool_name_observed<O: ExecutionObserver>(
    name: &str,
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> R<String> {
    let mut w = Work { session, site };
    w.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
    let mut state = State::default();
    let result = state.run(name, &mut w);
    state.finish(result, &mut w)
}
impl State {
    fn retire_scratch<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        w.record(1, size_of::<String>());
        w.text_drop(take(&mut self.normalized));
    }
    fn finish<O: ExecutionObserver>(&mut self, result: R, w: &mut Work<'_, '_, O>) -> R<String> {
        self.retire_scratch(w);
        match result.and_then(|()| w.publication(size_of::<String>())) {
            Ok(()) => Ok(take(&mut self.canonical)),
            Err(error) => {
                w.record(1, size_of::<String>());
                w.text_drop(take(&mut self.canonical));
                Err(error)
            }
        }
    }
}
