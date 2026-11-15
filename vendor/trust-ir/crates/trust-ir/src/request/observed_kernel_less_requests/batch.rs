// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
impl State {
    pub(super) fn prepare<O: ExecutionObserver>(&self, w: &mut Work<'_, '_, O>) -> R {
        w.admit(
            1,
            size_of::<R<Vec<E>>>()
                + size_of::<Vec<E>>()
                + size_of::<IntoIter<E>>()
                + size_of::<Option<IntoIter<E>>>()
                + size_of::<usize>(),
        )?;
        if self.batch.is_some() || self.pending.is_some() {
            return Err(ObservedValueError::InvalidRange);
        }
        Ok(())
    }
    pub(super) fn capture(&mut self, rows: Vec<E>) {
        // prepare has checked empty owning slots and prepaid this full
        // transform BEFORE the actual child. No callback separates child
        // return from complete batch/header/capacity capture.
        self.batch_capacity = rows.capacity();
        self.batch = Some(rows.into_iter());
    }
    pub(super) fn flush<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) -> R {
        loop {
            w.admit(
                1,
                size_of::<E>() + size_of::<Option<E>>() + size_of::<IntoIter<E>>(),
            )?;
            self.pending = self
                .batch
                .as_mut()
                .ok_or(ObservedValueError::InvalidRange)?
                .next();
            if self.pending.is_none() {
                break;
            }
            self.emit(w)?;
        }
        self.retire_batch(w);
        w.admit(0, 0)
    }
    pub(super) fn retire_batch<O: ExecutionObserver>(&mut self, w: &mut Work<'_, '_, O>) {
        if let Some(rows) = self.batch.as_mut() {
            loop {
                w.record(
                    1,
                    size_of::<E>() + size_of::<Option<E>>() + size_of::<IntoIter<E>>(),
                );
                let Some(error) = rows.next() else {
                    break;
                };
                let _ = error.retire_observed(w.session, w.site);
            }
        }
        w.record(
            1,
            size_of::<Option<IntoIter<E>>>() + size_of::<IntoIter<E>>() + size_of::<usize>(),
        );
        w.record(1, self.batch_capacity.saturating_mul(size_of::<E>()));
        drop(self.batch.take());
        self.batch_capacity = 0;
        w.poll();
    }
}
