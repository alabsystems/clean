// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
impl State {
    pub(super) fn sites<O: ExecutionObserver>(
        &mut self,
        b: &NativeVerificationBundle,
        r: &TrustVcNativeRequest,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(2, size_of::<Mode>() + size_of::<Option<FuncId>>())?;
        if r.mode != Mode::DischargeProofObligations {
            return Ok(());
        }
        let Some(function) = r.function else {
            return Ok(());
        };
        let mut at = 0;
        while let Some(id) = w.at(&r.obligations, at)? {
            self.insert(id, w)?;
            w.next(&mut at)?;
        }
        at = 0;
        while let Some(id) = w.at(&self.ids, at)? {
            w.admit(1, size_of::<ProofId>())?;
            let id = *id;
            if let Some(declared) = Self::first(b, id, w)? {
                w.admit(
                    2,
                    size_of_val(&declared.site) + size_of::<Option<FuncId>>() + size_of::<bool>(),
                )?;
                let actual = declared.site.map(|site| site.function);
                if actual != Some(function) {
                    self.fixed(
                        || E::TrustVcDischargeObligationNotSitedInFunction {
                            request: r.id,
                            obligation: id,
                            expected: function,
                            actual,
                        },
                        w,
                    )?;
                }
            }
            w.next(&mut at)?;
        }
        Ok(())
    }
    fn first<'a, O: ExecutionObserver>(
        b: &'a NativeVerificationBundle,
        id: ProofId,
        w: &mut Work<'_, '_, O>,
    ) -> R<Option<&'a crate::ProofObligation>> {
        let mut at = 0;
        while let Some(row) = w.at(&b.module.proof_obligations, at)? {
            w.admit(1, 2 * size_of::<ProofId>() + size_of::<bool>())?;
            if row.id == id {
                return Ok(Some(row));
            }
            w.next(&mut at)?;
        }
        Ok(None)
    }
}
