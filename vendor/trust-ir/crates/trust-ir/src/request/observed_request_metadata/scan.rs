// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
impl State {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        b: &NativeVerificationBundle,
        index: usize,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        let r = w
            .at(&b.requests, index)?
            .ok_or(ObservedValueError::InvalidRange)?;
        w.admit(
            3,
            size_of::<NativeRequestId>()
                + size_of::<&[crate::ProofId]>()
                + size_of::<&[crate::ProofLineageId]>(),
        )?;
        let id = r.id();
        let obligations = r.obligations();
        let roots = r.lineage_roots();
        if Self::duplicate_request(&b.requests, index, id, w)? {
            self.fixed(|| E::DuplicateRequestId(id), w)?;
        }
        w.admit(1, size_of::<bool>())?;
        if obligations.is_empty() {
            self.fixed(|| E::EmptyRequestObligations(id), w)?;
        }
        w.admit(1, size_of::<bool>())?;
        if roots.is_empty() {
            self.fixed(|| E::EmptyLineageRoots(id), w)?;
        }
        self.children(r, id, w)?;
        let mut at = 0;
        while let Some(obligation) = w.at(obligations, at)? {
            if Self::duplicate_obligation(obligations, at, obligation, w)? {
                self.fixed(
                    || E::DuplicateRequestObligation {
                        request: id,
                        obligation: *obligation,
                    },
                    w,
                )?;
            }
            if !Self::known(b, obligation, w)? {
                self.fixed(
                    || E::UnknownRequestObligation {
                        request: id,
                        obligation: *obligation,
                    },
                    w,
                )?;
            }
            w.next(&mut at)?;
        }
        self.prepare(w)?;
        // Actual PredTable is only two borrowed slices; no memo/hash/entropy.
        w.admit(
            1,
            size_of::<crate::pred::PredTable<'_>>()
                + size_of::<&super::super::NativeReplayContext>(),
        )?;
        let predicates = b.module.pred_table();
        self.capture(r.provenance().replay_context().validation_errors_observed(
            id,
            obligations,
            &b.compiler_facts,
            &predicates,
            w.session,
            w.site,
        )?);
        self.flush(w)
    }
    fn duplicate_request<O: ExecutionObserver>(
        rows: &[NativeVerificationRequest],
        end: usize,
        id: NativeRequestId,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let mut at = 0;
        loop {
            w.admit(1, size_of::<bool>())?;
            if at == end {
                return Ok(false);
            }
            let prior = w.at(rows, at)?.ok_or(ObservedValueError::InvalidRange)?;
            w.admit(2, 2 * size_of::<NativeRequestId>() + size_of::<bool>())?;
            if prior.id() == id {
                return Ok(true);
            }
            w.next(&mut at)?;
        }
    }
    fn duplicate_obligation<O: ExecutionObserver>(
        rows: &[crate::ProofId],
        end: usize,
        id: &crate::ProofId,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let mut at = 0;
        loop {
            w.admit(1, size_of::<bool>())?;
            if at == end {
                return Ok(false);
            }
            let prior = w.at(rows, at)?.ok_or(ObservedValueError::InvalidRange)?;
            w.admit(1, 2 * size_of::<crate::ProofId>() + size_of::<bool>())?;
            if prior == id {
                return Ok(true);
            }
            w.next(&mut at)?;
        }
    }
    fn known<O: ExecutionObserver>(
        b: &NativeVerificationBundle,
        id: &crate::ProofId,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let mut at = 0;
        while let Some(row) = w.at(&b.module.proof_obligations, at)? {
            w.admit(1, 2 * size_of::<crate::ProofId>() + size_of::<bool>())?;
            if row.id == *id {
                return Ok(true);
            }
            w.next(&mut at)?;
        }
        Ok(false)
    }
}
