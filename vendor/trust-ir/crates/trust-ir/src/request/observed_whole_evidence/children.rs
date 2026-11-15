// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
impl State {
    pub(super) fn children<O: ExecutionObserver>(
        &mut self,
        request: &NativeVerificationRequest,
        e: &NativeEvidenceBundle,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(8, size_of::<NativeRequestId>() + size_of::<Suite>())?;
        let id = e.request();
        let suite = e.verifier_suite();
        self.prepare(w)?;
        self.capture(e.provenance_binding_errors_observed(request, w.session, w.site)?);
        self.flush(w)?;
        self.prepare(w)?;
        self.capture(e.verifier().validation_errors_observed(
            "evidence.verifier",
            w.session,
            w.site,
        )?);
        self.flush(w)?;
        self.prepare(w)?;
        self.capture(
            e.verifier()
                .verifier_suite_errors_observed(id, suite, w.session, w.site)?,
        );
        self.flush(w)?;
        w.admit(
            1,
            size_of::<&[super::super::NativeToolIdentity]>() + size_of::<bool>(),
        )?;
        if e.solvers().is_empty() {
            self.fixed(|| E::EmptyProvenanceField("evidence.solvers"), w)?;
        }
        let mut at = 0;
        while let Some(solver) = w.at(e.solvers(), at)? {
            self.prepare(w)?;
            self.capture(solver.validation_errors_observed(
                "evidence.solvers",
                w.session,
                w.site,
            )?);
            self.flush(w)?;
            w.next(&mut at)?;
        }
        self.prepare(w)?;
        self.capture(
            e.replay()
                .validation_errors_observed(id, suite, w.session, w.site)?,
        );
        self.flush(w)?;
        self.prepare(w)?;
        self.capture(e.obligation_errors_observed(request, w.session, w.site)?);
        self.flush(w)?;
        self.prepare(w)?;
        self.capture(e.artifact_errors_observed(w.session, w.site)?);
        self.flush(w)
    }
}
