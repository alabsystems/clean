// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Exact raw diagnostic locations from the complete actual wire-refusal child.
use super::{
    NativeVerificationBundle, NativeVerificationBundleError as E,
    retire_native_bundle_errors_observed,
};
use crate::binary::{WireNodeSite, retire_wire_image_refusals_observed};
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use crate::{BinaryProjectionError, FuncId, Function, Module};
use core::mem::{size_of, take};
mod lookup;
mod render;
mod storage;
#[cfg(test)]
mod tests;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct Render {
    text: String,
    pending: Option<E>,
    errors: Vec<E>,
}
#[derive(Default)]
struct State {
    rows: Vec<BinaryProjectionError>,
    render: Render,
}
impl NativeVerificationBundle {
    /// Complete original raw wire refusal diagnostics for this actual module.
    /// This neither hashes an unencodable image nor issues identity authority.
    pub fn wire_identity_errors_observed<O: ExecutionObserver>(
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
    fn run<O: ExecutionObserver>(
        &mut self,
        b: &NativeVerificationBundle,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(1, size_of::<Vec<BinaryProjectionError>>())?;
        self.rows = b.module.wire_image_refusals_observed(w.session, w.site)?;
        let mut at = 0;
        while let Some(row) = w.at(&self.rows, at)? {
            self.render.map(&b.module, row, w)?;
            w.next(&mut at)?;
        }
        Ok(())
    }
    fn retire_scratch<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        w.record(1, size_of::<Vec<BinaryProjectionError>>());
        let _ = retire_wire_image_refusals_observed(take(&mut self.rows), w.session, w.site);
        self.render.retire_scratch(w);
    }
    fn finish<O: ExecutionObserver>(&mut self, result: R, w: &mut Work<'_, '_, O>) -> R<Vec<E>> {
        self.retire_scratch(w);
        match result.and_then(|()| w.publication(size_of::<Vec<E>>())) {
            Ok(()) => Ok(take(&mut self.render.errors)),
            Err(error) => {
                w.record(1, size_of::<Vec<E>>());
                let _ = retire_native_bundle_errors_observed(
                    take(&mut self.render.errors),
                    w.session,
                    w.site,
                );
                Err(error)
            }
        }
    }
}
impl Render {
    fn emit<O: ExecutionObserver>(
        &mut self,
        construct: &'static str,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(
            1,
            size_of::<E>() + size_of::<Option<E>>() + size_of::<String>(),
        )?;
        self.pending = Some(E::TrustIrModuleHasNoWireIdentity {
            location: take(&mut self.text),
            construct,
        });
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
        if let Some(e) = self.pending.take() {
            let _ = e.retire_observed(w.session, w.site);
        }
        w.poll();
    }
}
