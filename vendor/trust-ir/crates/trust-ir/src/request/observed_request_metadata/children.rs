// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
impl State {
    pub(super) fn children<O: ExecutionObserver>(
        &mut self,
        r: &NativeVerificationRequest,
        id: NativeRequestId,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        self.prepare(w)?;
        w.admit(1, size_of::<&super::super::NativeDiagnosticsPolicy>())?;
        self.capture(
            r.diagnostics()
                .request_errors_observed(id, w.session, w.site)?,
        );
        self.flush(w)?;
        w.admit(
            3,
            2 * size_of::<Suite>() + size_of::<&super::super::NativeRequestProvenance>(),
        )?;
        let suite = r.verifier_suite();
        let provenance = r.provenance();
        if provenance.verifier_suite != suite {
            self.fixed(
                || E::VerifierSuiteMismatch {
                    request: id,
                    expected: suite,
                    actual: provenance.verifier_suite,
                },
                w,
            )?;
        }
        self.prepare(w)?;
        self.capture(provenance.expected_verifier().validation_errors_observed(
            "request.provenance.expected_verifier",
            w.session,
            w.site,
        )?);
        self.flush(w)?;
        self.prepare(w)?;
        self.capture(
            provenance
                .expected_verifier()
                .verifier_suite_errors_observed(id, suite, w.session, w.site)?,
        );
        self.flush(w)?;
        w.admit(
            1,
            size_of::<&[super::super::NativeToolIdentity]>() + size_of::<bool>(),
        )?;
        let solvers = r.solver_identities();
        if solvers.is_empty() {
            self.fixed(|| E::EmptyProvenanceField("request.provenance.solvers"), w)?;
        }
        let mut at = 0;
        while let Some(solver) = w.at(solvers, at)? {
            self.prepare(w)?;
            self.capture(solver.validation_errors_observed(
                "request.provenance.solvers",
                w.session,
                w.site,
            )?);
            self.flush(w)?;
            w.next(&mut at)?;
        }
        w.admit(1, size_of::<Option<&crate::ProofReplayIdentity>>())?;
        match provenance.replay_identity() {
            Some(replay) => {
                self.prepare(w)?;
                self.capture(replay.validation_errors_observed(id, suite, w.session, w.site)?);
                self.flush(w)?;
            }
            None => self.fixed(|| E::MissingReplayIdentity(id), w)?,
        }
        Ok(())
    }
}
