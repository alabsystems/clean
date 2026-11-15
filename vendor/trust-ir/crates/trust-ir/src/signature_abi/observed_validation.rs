// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual semantic ABI carrier/target/legacy reconciliation, original owner.
use super::*;
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use crate::{Function, TargetInfo, Ty};
use core::{
    cmp::Ordering,
    mem::{size_of, take},
};
mod argument;
mod carriers;
mod reconcile;
mod storage;
#[cfg(test)]
mod tests;
mod validate;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Clone, Copy)]
enum Kind {
    Parameter,
    Result,
    HiddenResultParameter,
}
impl Kind {
    fn label(self) -> &'static str {
        match self {
            Self::Parameter => "parameter",
            Self::Result => "result",
            Self::HiddenResultParameter => "hidden result parameter",
        }
    }
}
enum Request<'a> {
    Validate(&'a FuncTy),
    Target(Option<&'a TargetInfo>),
    Function(&'a Function),
}
#[derive(Default)]
struct State {
    wire: String,
    reason: String,
    context: String,
    ranges: Vec<(u64, u64)>,
    parameters: Vec<Vec<(u64, u64)>>,
    results: Vec<Vec<(u64, u64)>>,
}
impl SignatureAbi {
    /// Full original semantic validation after the actual observed canonical
    /// encoding/reader round trip, then every real argument/binding/census and
    /// carrier check in original error order. A wire-unrepresentable value is
    /// typed outer UnsupportedValue (the existing observed wire contract),
    /// never accepted or substituted by an ordinary opaque encoder/prewalk.
    /// Bounded encodable malformed records retain exact original semantic text.
    /// This validates producer DATA only, never emitted ABI/target/source/proof
    /// truth, FnAbiView, a new authority, owner/grant/deadline/TLS/fuel or flag.
    pub fn validate_observed<O: ExecutionObserver>(
        &self,
        signature: &FuncTy,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Result<(), String>> {
        self.check_observed(Request::Validate(signature), session, site)
    }
    /// Exact optional-target/triple/width/endian/ABI agreement under the same
    /// original owner. All variable equality compares actual bounded chunks.
    pub fn validate_target_observed<O: ExecutionObserver>(
        &self,
        target: Option<&TargetInfo>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Result<(), String>> {
        self.check_observed(Request::Target(target), session, site)
    }
    /// Exact legacy whole-carrier reconciliation with every source owner, not
    /// only the first match. Does not validate the descriptor or its target;
    /// both remain mandatory original preceding checks in the full caller.
    pub fn reconcile_function_observed<O: ExecutionObserver>(
        &self,
        function: &Function,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Result<(), String>> {
        self.check_observed(Request::Function(function), session, site)
    }
    fn check_observed<O: ExecutionObserver>(
        &self,
        request: Request<'_>,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Result<(), String>> {
        let mut w = Work { session, site };
        w.admit(
            1,
            size_of::<State>() + size_of::<Work<'_, '_, O>>() + size_of::<Request<'_>>(),
        )?;
        let mut state = State::default();
        let result = match request {
            Request::Validate(signature) => state.validate(self, signature, &mut w),
            Request::Target(target) => state.target(self, target, &mut w),
            Request::Function(function) => state.reconcile(self, function, &mut w),
        };
        state.retire_scratch(&mut w);
        match result.and_then(|valid| {
            if valid {
                w.flat(take(&mut state.reason));
                w.admit(1, 0)?;
            }
            w.publication()?;
            Ok(valid)
        }) {
            Ok(true) => Ok(Ok(())),
            Ok(false) => Ok(Err(take(&mut state.reason))),
            Err(error) => {
                w.flat(take(&mut state.reason));
                Err(w.terminal(error))
            }
        }
    }
}
impl State {
    fn fail<O: ExecutionObserver>(&mut self, message: &str, w: &mut Work<'_, '_, O>) -> R<bool> {
        w.text(message, &mut self.reason)?;
        Ok(false)
    }
    fn retire_ranges<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        w.rows(take(&mut self.ranges));
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        w.flat(take(&mut self.wire));
        w.flat(take(&mut self.context));
        self.retire_ranges(w);
        for rows in [&mut self.parameters, &mut self.results] {
            loop {
                w.step(size_of::<Option<Vec<(u64, u64)>>>().saturating_add(1));
                let Some(row) = rows.pop() else { break };
                w.rows(row);
            }
            w.step(size_of::<Vec<Vec<(u64, u64)>>>().saturating_add(1));
            drop(take(rows));
            w.poll();
        }
    }
    fn prefix<O: ExecutionObserver>(&mut self, index: Option<usize>, w: &mut Work<'_, '_, O>) -> R {
        w.text("source ", &mut self.context)?;
        if let Some(index) = index {
            w.text("argument ", &mut self.context)?;
            w.unsigned(index as u128, &mut self.context)?;
            w.text(": ", &mut self.context)?;
        } else {
            w.text("result: ", &mut self.context)?;
        }
        w.text(&self.reason, &mut self.context)?;
        w.admit(1, 3 * size_of::<String>())?;
        core::mem::swap(&mut self.reason, &mut self.context);
        w.flat(take(&mut self.context));
        w.admit(1, 0)
    }
}
