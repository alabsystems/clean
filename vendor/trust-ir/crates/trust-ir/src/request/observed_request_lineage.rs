// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Exact original request lineage set computations; no proof authority.
use crate::interpret::{
    ExecutionObserver, ExecutionPhase, ExecutionProgress, ExecutionSite, ObservedSession,
    ObservedValueError,
};
use crate::{
    ProofCertificateRef, ProofDigest, ProofId, ProofLineageId, ProofLineageManifest,
    ProofLineageNode,
};
use core::mem::{size_of, take};
mod sets;
mod storage;
#[cfg(test)]
mod tests;
mod walk;
use storage::Work;
type R<T = ()> = Result<T, ObservedValueError>;
#[derive(Default)]
struct Members<'m> {
    obligations: Vec<ProofId>,
    certificates: Vec<&'m ProofCertificateRef>,
    sources: Vec<ProofDigest>,
}
/// Private owning set storage with references borrowed from the actual source
/// manifest. This DATA value proves no validation, replay or source authority.
/// Its fields are inaccessible; all membership reads and disposal stay observed.
#[derive(Default)]
pub struct NativeRequestLineage<'m> {
    reachable: Members<'m>,
    bound: Members<'m>,
}
#[derive(Default)]
struct State<'m> {
    out: NativeRequestLineage<'m>,
    current: Members<'m>,
    stack: Vec<ProofLineageId>,
    seen: Vec<ProofLineageId>,
}
#[derive(Clone, Copy)]
enum Target {
    Reachable,
    Current,
}
impl ProofLineageManifest {
    /// Compute both whole reachable sets and the exact original per-root
    /// source-bound membership sets. LAST physical duplicate node wins;
    /// unknown IDs and cycles retain the ordinary closure semantics.
    pub fn request_lineage_observed<'m, O: ExecutionObserver>(
        &'m self,
        roots: &[ProofLineageId],
        source: Option<ProofDigest>,
        s: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<NativeRequestLineage<'m>> {
        let mut w = Work { session: s, site };
        w.admit(1, size_of::<State<'m>>() + size_of::<Work<'_, '_, O>>())?;
        let mut st = State::default();
        let result = st.run(self, roots, source, &mut w);
        st.finish(result, &mut w)
    }
}
impl NativeRequestLineage<'_> {
    pub fn reachable_source_contains_observed<O: ExecutionObserver>(
        &self,
        source: &ProofDigest,
        s: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        let mut w = Work { session: s, site };
        let yes = w.contains(&self.reachable.sources, source)?;
        w.publish_bool(yes)
    }
    pub fn source_bound_obligation_contains_observed<O: ExecutionObserver>(
        &self,
        id: ProofId,
        s: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        let mut w = Work { session: s, site };
        let yes = w.contains(&self.bound.obligations, &id)?;
        w.publish_bool(yes)
    }
    pub fn source_bound_certificate_contains_observed<O: ExecutionObserver>(
        &self,
        reference: &ProofCertificateRef,
        s: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<bool> {
        let mut w = Work { session: s, site };
        let yes = w.has_certificate(&self.bound.certificates, reference)?;
        w.publish_bool(yes)
    }
    /// Consume all actual set arrays/backing capacity. Borrowed certificate
    /// payloads stay owned by the original manifest, not this DATA container.
    pub fn retire_observed<O: ExecutionObserver>(
        mut self,
        s: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let mut w = Work { session: s, site };
        w.record(1, size_of::<Self>());
        self.retire(&mut w);
        w.terminal()
    }
    fn retire<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        self.reachable.retire(w);
        self.bound.retire(w);
    }
}
impl<'m> State<'m> {
    fn scratch<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        self.current.retire(w);
        w.rows(&mut self.stack);
        w.rows(&mut self.seen);
    }
    fn finish<O: ExecutionObserver>(
        &mut self,
        result: R,
        w: &mut Work<'_, '_, O>,
    ) -> R<NativeRequestLineage<'m>> {
        self.scratch(w);
        match result.and_then(|()| w.publish(size_of::<NativeRequestLineage<'_>>())) {
            Ok(()) => Ok(take(&mut self.out)),
            Err(error) => {
                self.out.retire(w);
                Err(error)
            }
        }
    }
}
