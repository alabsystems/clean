// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
impl Refusals {
    /// The actual writer always propagates a prior error before another arm:
    /// pending is empty on entry; capture a returned owned ABI detail BEFORE
    /// the next fallible callback. No candidate authority is carried here.
    pub(in crate::binary::observed) fn capture(&mut self, refusal: WireRefusal) {
        self.pending = Some(refusal);
    }
    pub(in crate::binary::observed) fn accept<O: ExecutionObserver>(
        &mut self,
        out: &mut Output<'_, '_, O>,
    ) -> R {
        out.admit(
            6,
            size_of::<WireRefusal>()
                + size_of::<(usize, BinaryProjectionError)>()
                + size_of::<Option<WireRefusal>>()
                + size_of::<Option<(usize, BinaryProjectionError)>>(),
        )?;
        let refusal = self
            .pending
            .take()
            .ok_or(ObservedValueError::InvalidRange)?;
        self.converted = Some(refusal.ranked());
        self.record(out)
    }
    pub(in crate::binary::observed) fn count<O: ExecutionObserver>(
        &mut self,
        what: &'static str,
        count: u64,
        out: &mut Output<'_, '_, O>,
    ) -> R {
        out.admit(
            1,
            size_of::<(usize, BinaryProjectionError)>()
                + size_of::<Option<(usize, BinaryProjectionError)>>(),
        )?;
        self.converted = Some((
            COUNT_REFUSAL_RANK,
            BinaryProjectionError::CountExceedsFormat { what, count },
        ));
        self.record(out)
    }
    fn record<O: ExecutionObserver>(&mut self, out: &mut Output<'_, '_, O>) -> R {
        out.admit(1, size_of::<usize>() + size_of::<bool>())?;
        let rank = self
            .converted
            .as_ref()
            .ok_or(ObservedValueError::InvalidRange)?
            .0;
        let slot = self
            .first
            .get_mut(rank)
            .ok_or(ObservedValueError::InvalidRange)?;
        if slot.is_none() {
            out.admit(
                1,
                size_of::<Option<BinaryProjectionError>>()
                    + size_of::<Option<(usize, BinaryProjectionError)>>(),
            )?;
            *slot = Some(
                self.converted
                    .take()
                    .ok_or(ObservedValueError::InvalidRange)?
                    .1,
            );
        } else {
            out.record_retirement(1, size_of::<Option<(usize, BinaryProjectionError)>>());
            if let Some((_, e)) = self.converted.take() {
                let site = out.request_site();
                retirement::projection(e, out.session_mut(), site);
            }
        }
        Ok(())
    }
    pub(in crate::binary::observed) fn transfer<O: ExecutionObserver>(
        &mut self,
        out: &mut Output<'_, '_, O>,
    ) -> R<Vec<BinaryProjectionError>> {
        let mut at = 0usize;
        loop {
            out.admit(1, size_of::<Option<&Option<BinaryProjectionError>>>())?;
            let Some(row) = self.first.get(at) else {
                break;
            };
            out.admit(1, size_of::<bool>())?;
            if row.is_some() {
                out.reserve(&mut self.result, 1)?;
                out.admit(
                    1,
                    size_of::<Option<BinaryProjectionError>>() + size_of::<BinaryProjectionError>(),
                )?;
                let e = self.first[at]
                    .take()
                    .ok_or(ObservedValueError::InvalidRange)?;
                self.result.push(e);
            }
            out.admit(1, size_of::<usize>())?;
            at = at
                .checked_add(1)
                .ok_or(ObservedValueError::CapacityOverflow)?;
        }
        out.admit(1, size_of::<Vec<BinaryProjectionError>>())?;
        out.publication()?;
        Ok(take(&mut self.result))
    }
}
