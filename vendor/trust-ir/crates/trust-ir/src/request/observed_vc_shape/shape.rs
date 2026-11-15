// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
impl State {
    pub(super) fn shape<O: ExecutionObserver>(
        &mut self,
        r: &TrustVcNativeRequest,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(1, size_of::<Mode>())?;
        match r.mode {
            Mode::ImportProofCertificates | Mode::MergeProofCertificates => {
                let mut at = 0;
                while let Some(id) = w.at(&r.obligations, at)? {
                    if !Self::has(&r.certificates, id, w)? {
                        self.fixed(
                            || E::MissingTrustVcEvidenceForObligation {
                                request: r.id,
                                obligation: *id,
                            },
                            w,
                        )?;
                    }
                    w.next(&mut at)?;
                }
            }
            Mode::DischargeProofObligations => {
                w.admit(1, size_of::<Option<FuncId>>() + size_of::<bool>())?;
                if r.function.is_none() {
                    self.fixed(|| E::MissingTrustVcDischargeFunction(r.id), w)?;
                }
                let mut at = 0;
                while let Some(c) = w.at(&r.certificates, at)? {
                    w.text(&c.prover, &mut self.text)?;
                    w.admit(
                        1,
                        size_of::<String>() + size_of::<E>() + size_of::<Option<E>>(),
                    )?;
                    self.pending = Some(E::TrustVcDischargeRequestCarriesCertificate {
                        request: r.id,
                        obligation: c.obligation,
                        prover: take(&mut self.text),
                    });
                    self.emit(w)?;
                    w.next(&mut at)?;
                }
            }
        }
        Ok(())
    }
    fn has<O: ExecutionObserver>(
        rows: &[ProofCertificateRef],
        id: &ProofId,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let mut at = 0;
        while let Some(c) = w.at(rows, at)? {
            w.admit(1, 2 * size_of::<ProofId>() + size_of::<bool>())?;
            if c.obligation == *id {
                return Ok(true);
            }
            w.next(&mut at)?;
        }
        Ok(false)
    }
}
