// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Complete ordinary VC discharge-site and mode-shape DATA prefixes.
use super::{
    NativeVerificationBundle, NativeVerificationBundleError as E, NativeVerificationRequest,
    TrustVcNativeRequest, TrustVcVerificationMode as Mode, retire_native_bundle_errors_observed,
};
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use crate::{FuncId, ProofCertificateRef, ProofId};
use core::mem::{size_of, size_of_val, take};
mod shape;
mod sites;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State {
    ids: Vec<ProofId>,
    text: String,
    pending: Option<E>,
    errors: Vec<E>,
}
impl NativeVerificationBundle {
    /// Exact ordinary VC discharge-site checks followed by its mode-shape
    /// prefix, selected from the ACTUAL physical request. MC/WP skip this
    /// leaf exactly, but retain their separate mandatory mode validators.
    /// Certificate strong-status/trusted/real replay checks are NOT replaced.
    pub fn request_vc_shape_errors_observed<O: ExecutionObserver>(
        &self,
        index: usize,
        s: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<E>> {
        let mut w = Work { session: s, site };
        w.admit(1, size_of::<State>() + size_of::<Work<'_, '_, O>>())?;
        let mut st = State::default();
        let result = st.run(self, index, &mut w);
        st.finish(result, &mut w)
    }
}
impl State {
    fn run<O: ExecutionObserver>(
        &mut self,
        b: &NativeVerificationBundle,
        index: usize,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        let r = w
            .at(&b.requests, index)?
            .ok_or(ObservedValueError::InvalidRange)?;
        w.admit(1, size_of::<Option<&TrustVcNativeRequest>>())?;
        let NativeVerificationRequest::TrustVc(r) = r else {
            return Ok(());
        };
        self.sites(b, r, w)?;
        self.shape(r, w)
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
        let mut ids = take(&mut self.ids);
        loop {
            w.record(1, size_of::<Option<ProofId>>());
            if ids.pop().is_none() {
                break;
            }
        }
        w.record(1, ids.capacity().saturating_mul(size_of::<ProofId>()));
        drop(ids);
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
    fn insert<O: ExecutionObserver>(&mut self, id: &ProofId, w: &mut Work<'_, '_, O>) -> R {
        let mut at = 0;
        while let Some(prior) = w.at(&self.ids, at)? {
            w.admit(2, 2 * size_of::<ProofId>() + size_of::<bool>())?;
            if prior == id {
                return Ok(());
            }
            if prior > id {
                break;
            }
            w.next(&mut at)?;
        }
        w.reserve(&mut self.ids)?;
        w.admit(1, size_of::<ProofId>() + size_of::<usize>())?;
        let mut to = self.ids.len();
        self.ids.push(*id);
        loop {
            w.admit(1, size_of::<bool>())?;
            if to == at {
                break;
            }
            w.admit(2, size_of::<ProofId>() + size_of::<usize>())?;
            self.ids[to] = self.ids[to - 1];
            to -= 1;
        }
        w.admit(1, size_of::<ProofId>())?;
        self.ids[at] = *id;
        Ok(())
    }
}
