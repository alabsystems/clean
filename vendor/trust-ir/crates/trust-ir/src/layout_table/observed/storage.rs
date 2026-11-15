// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;

mod enums;
mod scratch;

pub(super) fn admit<O: ExecutionObserver>(
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
    work: usize,
    bytes: usize,
) -> Result<(), ObservedValueError> {
    session
        .admit(ExecutionProgress {
            phase: ExecutionPhase::Layout,
            site,
            work,
            copy_bytes: bytes,
        })
        .map_err(Into::into)
}
pub(super) fn publication<O: ExecutionObserver>(
    session: &mut ObservedSession<'_, O>,
    site: ExecutionSite,
) -> Result<(), ObservedValueError> {
    session
        .admit(ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site,
            work: 0,
            copy_bytes: 0,
        })
        .map_err(Into::into)
}

impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn admit(&mut self, work: usize, bytes: usize) -> R {
        admit(self.session, self.site, work, bytes).map_err(Into::into)
    }
    pub(super) fn poll(&mut self) -> R {
        self.admit(1, 0)
    }
    pub(super) fn lookup(&mut self, count: usize) -> R {
        self.admit(observed_btree::population_work(count)?, 0)
    }
    pub(super) fn tree<K, V>(&mut self, count: usize) -> R {
        let cost = observed_btree::insertion_cost::<K, V>(count)?;
        self.admit(cost.work, cost.copy_bytes)
    }
    pub(super) fn reserve<T>(&mut self, rows: &mut Vec<T>) -> R {
        self.poll()?;
        if rows.len() == rows.capacity() {
            let requested = rows
                .len()
                .checked_mul(2)
                .and_then(|n| n.checked_add(1))
                .ok_or(ObservedValueError::CapacityOverflow)?;
            let images = requested
                .checked_add(rows.len())
                .ok_or(ObservedValueError::CapacityOverflow)?;
            self.admit(
                images,
                images
                    .checked_mul(size_of::<T>())
                    .ok_or(ObservedValueError::CapacityOverflow)?,
            )?;
            rows.try_reserve_exact(requested - rows.len())
                .map_err(|_| ObservedValueError::AllocationFailed)?;
        }
        Ok(())
    }
    pub(super) fn push<T: Copy>(&mut self, rows: &mut Vec<T>, value: T) -> R {
        self.reserve(rows)?;
        self.admit(1, size_of::<T>())?;
        rows.push(value);
        Ok(())
    }
    pub(super) fn empty_row<T>(&mut self, rows: &mut Vec<Vec<T>>) -> R {
        self.reserve(rows)?;
        self.admit(1, size_of::<Vec<T>>())?;
        rows.push(Vec::new());
        Ok(())
    }
    pub(super) fn copy_text(&mut self, source: &str) -> R<String> {
        let mut text = String::new();
        let result = (|| {
            let mut rest = source;
            while !rest.is_empty() {
                self.admit(4, 0)?;
                let mut end = rest.len().min(1024);
                while !rest.is_char_boundary(end) {
                    end -= 1;
                }
                let chunk = &rest[..end];
                if text
                    .len()
                    .checked_add(chunk.len())
                    .ok_or(ObservedValueError::CapacityOverflow)?
                    > text.capacity()
                {
                    let requested = text
                        .len()
                        .checked_mul(2)
                        .and_then(|n| n.checked_add(chunk.len()))
                        .ok_or(ObservedValueError::CapacityOverflow)?;
                    let images = requested
                        .checked_add(text.len())
                        .ok_or(ObservedValueError::CapacityOverflow)?;
                    self.admit(images, images)?;
                    text.try_reserve_exact(requested - text.len())
                        .map_err(|_| ObservedValueError::AllocationFailed)?;
                }
                self.admit(chunk.len(), chunk.len())?;
                text.push_str(chunk);
                rest = &rest[end..];
            }
            Ok(())
        })();
        if let Err(error) = result {
            self.retire_text(text);
            self.poll()?;
            return Err(error);
        }
        Ok(text)
    }
    pub(super) fn index_name(&mut self, mut index: usize) -> R<String> {
        let mut digits = [0u8; 40];
        let mut first = digits.len();
        loop {
            self.poll()?;
            first -= 1;
            digits[first] = b'0' + (index % 10) as u8;
            index /= 10;
            if index == 0 {
                break;
            }
        }
        self.admit(digits.len(), 0)?;
        let text =
            core::str::from_utf8(&digits[first..]).map_err(|_| ObservedValueError::InvalidRange)?;
        self.copy_text(text)
    }
    pub(super) fn arc(&mut self, shape: TyLayoutShape) -> R<Arc<TyLayoutShape>> {
        let bytes = size_of::<TyLayoutShape>()
            .checked_add(2 * size_of::<usize>())
            .and_then(|n| n.checked_add(2 * align_of::<TyLayoutShape>()))
            .ok_or(ObservedValueError::CapacityOverflow);
        let result = bytes
            .map_err(Error::from)
            .and_then(|bytes| self.admit(1, bytes));
        if let Err(error) = result {
            self.retire_shape(shape);
            self.poll()?;
            return Err(error);
        }
        Ok(Arc::new(shape))
    }
    pub(super) fn give(&mut self, shape: Arc<TyLayoutShape>) -> R {
        if let Some(previous) = self.value.replace(shape) {
            self.retire_layout(previous);
        }
        self.poll()
    }
    pub(super) fn retire_shape(&mut self, shape: TyLayoutShape) {
        let _ = shape.retire_observed(self.session, self.site);
    }
    pub(super) fn retire_layout(&mut self, layout: Arc<TyLayoutShape>) {
        let _ = layout.retire_arc_observed(self.session, self.site);
    }
    pub(super) fn retire_error(&mut self, error: Error) {
        match error {
            Error::Layout(error) => {
                let _ = error.retire_observed(self.session, self.site);
            }
            Error::Resource(error) => self.retire_fixed(error),
        }
    }
    pub(super) fn retire_fixed<T: Copy>(&mut self, value: T) {
        // Copy bound prevents a future owned payload from falling
        // through an unobserved generic Drop path.
        self.session
            .retirement_step(self.site, size_of::<T>().saturating_add(1));
        let _ = value;
        self.session.retirement_poll(self.site);
    }
    pub(super) fn retire_scratch(&mut self) {
        if let Some(value) = self.value.take() {
            self.retire_layout(value);
        }
        loop {
            self.retire_tree_pop::<Key, Arc<TyLayoutShape>>(self.cache.len());
            let Some((key, value)) = self.cache.pop_first() else {
                break;
            };
            self.retire_fixed(key);
            self.retire_layout(value);
        }
        self.session.retirement_step(
            self.site,
            size_of::<BTreeMap<Key, Arc<TyLayoutShape>>>().saturating_add(1),
        );
        // Every entry was consumed above; only the empty root can remain.
        drop(core::mem::take(&mut self.cache));
        self.session.retirement_poll(self.site);
        loop {
            self.retire_tree_pop::<usize, Arc<EnumLayoutShape>>(self.enums.len());
            let Some((key, shape)) = self.enums.pop_first() else {
                break;
            };
            self.retire_fixed(key);
            self.retire_enum(shape);
        }
        self.session.retirement_step(
            self.site,
            size_of::<BTreeMap<usize, Arc<EnumLayoutShape>>>().saturating_add(1),
        );
        drop(core::mem::take(&mut self.enums));
        self.session.retirement_poll(self.site);
        let inhabitedness = core::mem::take(&mut self.inhabitedness);
        self.retire_copy_map(inhabitedness);
        let open = core::mem::take(&mut self.open);
        self.retire_set(open);
        let definitions = core::mem::take(&mut self.definitions);
        self.retire_copy_map(definitions);
        self.clear_spans();
        self.session.retirement_poll(self.site);
    }
    pub(super) fn clear_spans(&mut self) {
        let spans = core::mem::take(&mut self.spans);
        self.retire_set(spans);
    }
}
