// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
impl State {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        requests: &[NativeVerificationRequest],
        w: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0;
        while let Some(r) = w.at(requests, at)? {
            w.admit(1, size_of::<Option<&super::super::TrustVcNativeRequest>>())?;
            if let NativeVerificationRequest::TrustVc(r) = r {
                let mut row = 0;
                while let Some(id) = w.at(&r.obligations, row)? {
                    self.insert(id, w)?;
                    w.next(&mut row)?;
                }
            }
            w.next(&mut at)?;
        }
        at = 0;
        while let Some(id) = w.at(&self.ids, at)? {
            w.admit(1, size_of::<ProofId>())?;
            let id = *id;
            let (importing, discharging) = Self::first_pair(requests, &id, w)?;
            w.admit(1, 2 * size_of::<Option<NativeRequestId>>())?;
            if let (Some(importing), Some(discharging)) = (importing, discharging) {
                w.admit(1, size_of::<E>() + size_of::<Option<E>>())?;
                self.pending = Some(E::TrustVcObligationBothImportedAndDischarged {
                    obligation: id,
                    importing,
                    discharging,
                });
                w.reserve(&mut self.errors)?;
                w.admit(1, size_of::<E>() + size_of::<Option<E>>())?;
                self.errors.push(
                    self.pending
                        .take()
                        .ok_or(ObservedValueError::InvalidRange)?,
                );
            }
            w.next(&mut at)?;
        }
        Ok(())
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
    fn first_pair<O: ExecutionObserver>(
        rows: &[NativeVerificationRequest],
        id: &ProofId,
        w: &mut Work<'_, '_, O>,
    ) -> R<(Option<NativeRequestId>, Option<NativeRequestId>)> {
        w.admit(1, 2 * size_of::<Option<NativeRequestId>>())?;
        let (mut importing, mut discharging) = (None, None);
        let mut at = 0;
        while let Some(r) = w.at(rows, at)? {
            w.admit(1, size_of::<Option<&super::super::TrustVcNativeRequest>>())?;
            if let NativeVerificationRequest::TrustVc(r) = r {
                w.admit(2, size_of::<Mode>() + size_of::<Option<NativeRequestId>>())?;
                let slot = match r.mode {
                    Mode::ImportProofCertificates | Mode::MergeProofCertificates => &mut importing,
                    Mode::DischargeProofObligations => &mut discharging,
                };
                w.admit(1, size_of::<bool>())?;
                if slot.is_none() {
                    let mut row = 0;
                    while let Some(candidate) = w.at(&r.obligations, row)? {
                        w.admit(1, 2 * size_of::<ProofId>() + size_of::<bool>())?;
                        if candidate == id {
                            w.admit(
                                1,
                                size_of::<Option<NativeRequestId>>() + size_of::<NativeRequestId>(),
                            )?;
                            *slot = Some(r.id);
                            break;
                        }
                        w.next(&mut row)?;
                    }
                }
            }
            w.admit(2, 2 * size_of::<bool>())?;
            if importing.is_some() && discharging.is_some() {
                break;
            }
            w.next(&mut at)?;
        }
        w.admit(1, 2 * size_of::<Option<NativeRequestId>>())?;
        Ok((importing, discharging))
    }
}
