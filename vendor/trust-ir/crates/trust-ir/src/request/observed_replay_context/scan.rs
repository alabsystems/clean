// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
impl State {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        c: &NativeReplayContext,
        id: NativeRequestId,
        obligations: &[ProofId],
        facts: &NativeCompilerFacts,
        predicates: &PredTable<'_>,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0;
        while let Some(u) = w.at(&c.unsupported_modes, at)? {
            w.text(&u.detail, &mut self.text)?;
            w.admit(
                2,
                size_of::<NativeUnsupportedModeReason>()
                    + size_of::<E>()
                    + size_of::<Option<E>>()
                    + size_of::<String>(),
            )?;
            self.pending = Some(E::UnsupportedNativeRequestMode {
                request: id,
                reason: u.reason,
                detail: take(&mut self.text),
            });
            self.emit(w)?;
            w.next(&mut at)?;
        }
        at = 0;
        while let Some(a) = w.at(&c.atoms, at)? {
            if self.duplicate(&c.atoms, at, a, w)? {
                self.fixed(
                    || E::DuplicateReplayAtomId {
                        request: id,
                        atom: a.id,
                    },
                    w,
                )?;
            }
            if w.blank(&a.formula.schema)? {
                self.invalid(id, a, "formula.schema", w)?;
            }
            if w.blank(&a.formula.payload)? {
                self.invalid(id, a, "formula.payload", w)?;
            }
            w.admit(1, size_of::<R<bool>>())?;
            if a.formula
                .states_two_texts_observed(predicates, w.session, w.site)?
            {
                self.invalid(id, a, "formula.smtlib", w)?;
            }
            self.digest(id, a, w)?;
            self.bind(id, a, obligations, facts, w)?;
            w.next(&mut at)?;
        }
        Ok(())
    }
    fn duplicate<O: ExecutionObserver>(
        &self,
        atoms: &[NativeReplayAtom],
        end: usize,
        a: &NativeReplayAtom,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let mut at = 0;
        loop {
            w.admit(1, size_of::<bool>())?;
            if at == end {
                return Ok(false);
            }
            let prior = w.at(atoms, at)?.ok_or(ObservedValueError::InvalidRange)?;
            w.admit(
                1,
                2 * size_of::<super::super::NativeReplayAtomId>() + size_of::<bool>(),
            )?;
            if prior.id == a.id {
                return Ok(true);
            }
            w.next(&mut at)?;
        }
    }
    fn digest<O: ExecutionObserver>(
        &mut self,
        id: NativeRequestId,
        a: &NativeReplayAtom,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(32, size_of::<ProofDigest>() + size_of::<bool>())?;
        if a.payload_digest.is_zero() {
            return self.invalid(id, a, "payload_digest", w);
        }
        w.admit(1, size_of::<ProofDigestAlgorithm>() + size_of::<bool>())?;
        if a.payload_digest.algorithm != ProofDigestAlgorithm::Sha256 {
            return self.invalid(id, a, "payload_digest.algorithm", w);
        }
        w.admit(1, size_of::<R<ProofDigest>>() + size_of::<ProofDigest>())?;
        let expected = a.expected_payload_digest_observed(w.session, w.site)?;
        w.admit(34, 2 * size_of::<ProofDigest>() + size_of::<bool>())?;
        if a.payload_digest != expected {
            self.fixed(
                || E::ReplayAtomDigestMismatch {
                    request: id,
                    atom: a.id,
                    expected,
                    actual: a.payload_digest,
                },
                w,
            )?;
        }
        Ok(())
    }
}
