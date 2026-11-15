// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
impl State {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        request: &NativeVerificationRequest,
        evidence: &NativeEvidenceBundle,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(
            3,
            2 * size_of::<&[ProofId]>() + size_of::<NativeRequestId>(),
        )?;
        let request_id = request.id();
        let requested = request.obligations();
        let supplied = evidence.obligations();
        self.load(requested, Side::Requested, w)?;
        self.load(supplied, Side::Supplied, w)?;
        self.difference(request_id, Side::Requested, w)?;
        self.difference(request_id, Side::Supplied, w)
    }
    pub(super) fn load<O: ExecutionObserver>(
        &mut self,
        source: &[ProofId],
        side: Side,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0;
        while let Some(id) = w.at(source, at)? {
            w.admit(1, size_of::<ProofId>())?;
            let id = *id;
            let rows = match side {
                Side::Requested => &mut self.requested,
                Side::Supplied => &mut self.supplied,
            };
            w.insert_id(rows, id)?;
            w.next(&mut at)?;
        }
        Ok(())
    }
    fn rows(&self, side: Side) -> &[ProofId] {
        match side {
            Side::Requested => &self.requested,
            Side::Supplied => &self.supplied,
        }
    }
    fn difference<O: ExecutionObserver>(
        &mut self,
        request: NativeRequestId,
        side: Side,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0;
        loop {
            let id = {
                let Some(id) = w.at(self.rows(side), at)? else {
                    break;
                };
                w.admit(1, size_of::<ProofId>())?;
                *id
            };
            if !self.contains(id, side.other(), w)? {
                w.admit(1, size_of::<E>() + size_of::<Option<E>>())?;
                self.pending = Some(E::EvidenceObligationMismatch {
                    request,
                    obligation: id,
                });
                self.emit(w)?;
            }
            w.next(&mut at)?;
        }
        Ok(())
    }
    fn contains<O: ExecutionObserver>(
        &self,
        id: ProofId,
        side: Side,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let mut at = 0;
        while let Some(other) = w.at(self.rows(side), at)? {
            w.admit(2, size_of::<bool>())?;
            if *other == id {
                return Ok(true);
            }
            if *other > id {
                return Ok(false);
            }
            w.next(&mut at)?;
        }
        Ok(false)
    }
}
impl<O: ExecutionObserver> Work<'_, '_, O> {
    // Observed sorted unique insertion avoids opaque sort/hash/BTree setup.
    // Each actual comparison and each individual shift is admitted. A stopped
    // shift may leave duplicate Copy IDs, but all owning buffers remain in
    // State and no partial set/diagnostic result can be published.
    pub(super) fn insert_id(&mut self, rows: &mut Vec<ProofId>, id: ProofId) -> R {
        let mut at = 0;
        while let Some(other) = self.at(rows, at)? {
            self.admit(2, size_of::<bool>())?;
            if *other == id {
                return Ok(());
            }
            if *other > id {
                break;
            }
            self.next(&mut at)?;
        }
        self.reserve(rows)?;
        self.admit(1, size_of::<ProofId>())?;
        rows.push(id);
        let mut end = rows.len() - 1;
        while end > at {
            self.admit(2, 2 * size_of::<ProofId>())?;
            let value = rows
                .get(end - 1)
                .copied()
                .ok_or(ObservedValueError::InvalidRange)?;
            *rows.get_mut(end).ok_or(ObservedValueError::InvalidRange)? = value;
            self.admit(1, size_of::<usize>())?;
            end -= 1;
        }
        self.admit(1, size_of::<ProofId>())?;
        *rows.get_mut(at).ok_or(ObservedValueError::InvalidRange)? = id;
        Ok(())
    }
}
