// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[derive(Clone, Copy)]
pub(super) enum Group {
    Identity,
    References,
    Provenance,
    Serialization,
    Diagnostics,
    Formula,
    LineageDigests,
    CompilerFacts,
}
impl State {
    pub(super) fn child<O: ExecutionObserver>(
        &mut self,
        b: &NativeVerificationBundle,
        group: Group,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        self.prepare(w)?;
        w.admit(8, size_of::<Group>())?;
        let rows = match group {
            Group::Identity => b.identity_prefix_errors_observed(w.session, w.site)?,
            Group::References => b.reference_spelling_errors_observed(w.session, w.site)?,
            Group::Provenance => b.provenance_errors_observed(w.session, w.site)?,
            Group::Serialization => b.serialization_errors_observed(w.session, w.site)?,
            Group::Diagnostics => b.diagnostics_policy_errors_observed(w.session, w.site)?,
            Group::Formula => b.formula_text_errors_observed(w.session, w.site)?,
            Group::LineageDigests => b.lineage_digest_errors_observed(w.session, w.site)?,
            Group::CompilerFacts => b.compiler_fact_errors_observed(w.session, w.site)?,
        };
        self.capture(rows);
        self.flush(w)
    }
    pub(super) fn lineage<O: ExecutionObserver>(
        &mut self,
        b: &NativeVerificationBundle,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(
            1,
            size_of::<Vec<ProofLineageError>>() + size_of::<R<Vec<ProofLineageError>>>(),
        )?;
        w.admit(1, size_of::<usize>() + 3 * size_of::<bool>())?;
        // This private stage is entered once from fresh State. Refuse stale
        // owning slots rather than implicitly replacing any old allocation.
        if self.lineage.capacity() != 0 || self.pending.is_some() || self.batch.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        self.lineage = b.lineage.against_errors_observed(
            &b.module.proof_obligations,
            &b.module.proof_certificates,
            w.session,
            w.site,
        )?;
        w.admit(1, size_of::<bool>())?;
        if !self.lineage.is_empty() {
            w.admit(
                1,
                size_of::<E>() + size_of::<Option<E>>() + size_of::<Vec<ProofLineageError>>(),
            )?;
            self.pending = Some(E::Lineage(take(&mut self.lineage)));
            self.emit(w)?;
        }
        Ok(())
    }
}
