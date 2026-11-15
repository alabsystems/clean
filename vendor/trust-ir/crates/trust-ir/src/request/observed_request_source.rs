// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Complete original contiguous request lineage/source/function diagnostic group.
use super::{
    NativeObligationSource, NativeRequestId, NativeRequestLineage, NativeVerificationBundle,
    NativeVerificationBundleError as E, NativeVerificationRequest,
    retire_native_bundle_errors_observed,
};
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use crate::{FuncId, ProofDigest, ProofId, ProofLineageId, ProofLineageNode};
use core::mem::{size_of, take};
mod obligations;
mod roots;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct State<'m> {
    lineage: Option<NativeRequestLineage<'m>>,
    ids: Vec<ProofId>,
    pending: Option<E>,
    errors: Vec<E>,
}
impl NativeVerificationBundle {
    /// Exact original contiguous request group from physical lineage roots
    /// through source-bound obligations, sidecar rows and function ownership.
    /// This DATA query alone binds neither an actual bundle request row nor
    /// certificate/kernel/source authority; whole validation remains required.
    pub fn request_source_errors_observed<'m, O: ExecutionObserver>(
        &'m self,
        request: &NativeVerificationRequest,
        s: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Vec<E>> {
        let mut w = Work { session: s, site };
        w.admit(1, size_of::<State<'m>>() + size_of::<Work<'_, '_, O>>())?;
        let mut st = State::default();
        let result = st.run(self, request, &mut w);
        st.finish(result, &mut w)
    }
}
impl<'m> State<'m> {
    fn run<O: ExecutionObserver>(
        &mut self,
        b: &'m NativeVerificationBundle,
        r: &NativeVerificationRequest,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(
            1,
            size_of::<NativeRequestId>() + size_of::<&[ProofLineageId]>(),
        )?;
        let id = r.id();
        let roots = r.lineage_roots();
        self.roots(b, id, roots, w)?;
        w.admit(1, size_of::<Option<ProofDigest>>())?;
        let source = b.source_digest();
        w.admit(1, size_of::<bool>())?;
        if self.lineage.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        w.admit(
            1,
            size_of::<R<NativeRequestLineage<'m>>>()
                + size_of::<Option<NativeRequestLineage<'m>>>(),
        )?;
        // Capture the WHOLE successful child before any further fee.
        self.lineage = Some(
            b.lineage
                .request_lineage_observed(roots, source, w.session, w.site)?,
        );
        w.admit(1, size_of::<Option<ProofDigest>>())?;
        if let Some(source) = source {
            w.admit(1, size_of::<R<bool>>())?;
            let found = self
                .lineage
                .as_ref()
                .ok_or(ObservedValueError::InvalidRange)?
                .reachable_source_contains_observed(&source, w.session, w.site)?;
            if !found {
                self.fixed(
                    || E::RequestSourceDigestNotInLineage {
                        request: id,
                        source,
                    },
                    w,
                )?;
            }
        }
        w.admit(1, size_of::<&[ProofId]>())?;
        let obligations = r.obligations();
        let mut at = 0;
        while let Some(obligation) = w.at(obligations, at)? {
            self.insert(obligation, w)?;
            w.next(&mut at)?;
        }
        self.obligations(b, r, id, w)
    }
    fn fixed<O: ExecutionObserver>(
        &mut self,
        make: impl FnOnce() -> E,
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
    fn retire_scratch<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        w.record(
            1,
            size_of::<Option<NativeRequestLineage<'m>>>() + size_of::<NativeRequestLineage<'m>>(),
        );
        if let Some(lineage) = self.lineage.take() {
            let _ = lineage.retire_observed(w.session, w.site);
        }
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
