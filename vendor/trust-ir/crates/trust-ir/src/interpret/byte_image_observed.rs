// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Observed sparse byte-store operations. The ordinary entry points remain
//! unchanged; these use only the fallible rope cores and the original control.

use super::*;
use crate::interpret::observed::{
    ExecutionPhase, ObservedRopeElem, ObservedValueError, StructuralProgress,
};
use core::mem::size_of;

type Result<T> = core::result::Result<T, ObservedValueError>;

impl ObservedRopeElem for Option<u8> {
    fn clone_observed(&self, p: &mut impl StructuralProgress) -> Result<Self> {
        p.admit(ExecutionPhase::LiteralElement, 1, 0)?;
        Ok(*self)
    }

    fn same_observed(&self, other: &Self, p: &mut impl StructuralProgress) -> Result<bool> {
        p.admit(ExecutionPhase::LiteralElement, 1, 0)?;
        Ok(self == other)
    }

    fn retire_observed(self, p: &mut impl StructuralProgress) {
        p.retirement_poll();
    }
}

fn run_event(count: usize, p: &mut impl StructuralProgress) -> Result<()> {
    // Conservatively prepay std's lookup (including its comparisons). There
    // is also a fresh event for every actual range iterator step below.
    p.admit(
        ExecutionPhase::SparseRun,
        count
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?,
        0,
    )?;
    Ok(())
}

fn reserve<T>(values: &mut Vec<T>, extra: usize, p: &mut impl StructuralProgress) -> Result<()> {
    let need = values
        .len()
        .checked_add(extra)
        .ok_or(ObservedValueError::CapacityOverflow)?;
    if need <= values.capacity() {
        return Ok(());
    }
    let capacity = need
        .max(
            values
                .capacity()
                .checked_mul(2)
                .ok_or(ObservedValueError::CapacityOverflow)?,
        )
        .max(4);
    let bytes = capacity
        .checked_mul(size_of::<T>())
        .ok_or(ObservedValueError::CapacityOverflow)?;
    p.admit(
        ExecutionPhase::HostAllocation,
        capacity
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?,
        bytes,
    )?;
    values
        .try_reserve_exact(capacity - values.len())
        .map_err(|_| ObservedValueError::AllocationFailed)
}

fn retire_parts(mut parts: Vec<Image>, p: &mut impl StructuralProgress) {
    while let Some(part) = parts.pop() {
        p.retirement_poll();
        part.retire_observed(p);
    }
    p.retirement_poll();
}

impl ByteStore {
    pub(crate) fn new_observed(
        len: u64,
        byte: Option<u8>,
        p: &mut impl StructuralProgress,
    ) -> Result<Self> {
        run_event(0, p)?;
        let mut result = Self {
            len,
            runs: BTreeMap::new(),
        };
        if len != 0 {
            let image = Image::uniform_observed(byte, len, p)?;
            if let Err(error) = result.insert_observed(0, image, p) {
                result.retire_observed(p);
                return Err(error);
            }
        }
        if let Err(error) = p.admit(ExecutionPhase::SparseRun, 0, 0) {
            result.retire_observed(p);
            return Err(error.into());
        }
        Ok(result)
    }

    pub(crate) fn read_observed(
        &self,
        start: u64,
        len: u64,
        p: &mut impl StructuralProgress,
    ) -> Result<Image> {
        run_event(self.runs.len(), p)?;
        let end = start
            .checked_add(len)
            .filter(|end| *end <= self.len)
            .ok_or(ObservedValueError::InvalidRange)?;
        if len == 0 {
            return Image::uniform_observed(None, 0, p);
        }
        let first = self
            .runs
            .range(..=start)
            .next_back()
            .map(|(key, _)| *key)
            .ok_or(ObservedValueError::InvalidRange)?;
        let mut parts = Vec::new();
        let result = (|| {
            let mut runs = self.runs.range(first..end);
            loop {
                run_event(0, p)?;
                let Some((&run_start, image)) = runs.next() else {
                    break;
                };
                let run_end = run_start
                    .checked_add(image.len())
                    .ok_or(ObservedValueError::CapacityOverflow)?;
                if run_end <= start {
                    continue;
                }
                let lo = start.max(run_start);
                let hi = end.min(run_end);
                reserve(&mut parts, 1, p)?;
                parts.push(image.slice_observed(lo - run_start, hi - lo, p)?);
            }
            Ok(())
        })();
        if let Err(error) = result {
            retire_parts(parts, p);
            return Err(error);
        }
        let image = Image::concat_observed(parts, p)?;
        if image.len() != len {
            image.retire_observed(p);
            return Err(ObservedValueError::InvalidRange);
        }
        Ok(image)
    }

    /// On error the interrupted execution must abort. Retire any partially
    /// mutated store immediately and leave a valid empty store, rather than
    /// allowing a partial tiling or a rollback allocation after refusal.
    pub(crate) fn write_observed(
        &mut self,
        start: u64,
        image: &Image,
        p: &mut impl StructuralProgress,
    ) -> Result<()> {
        let result = self.write_inner_observed(start, image, p);
        let result = result.and_then(|()| {
            p.admit(ExecutionPhase::SparseRun, 0, 0)
                .map_err(ObservedValueError::from)
        });
        if let Err(error) = result {
            let old = core::mem::replace(
                self,
                Self {
                    len: 0,
                    runs: BTreeMap::new(),
                },
            );
            old.retire_observed(p);
            return Err(error);
        }
        Ok(())
    }

    fn write_inner_observed(
        &mut self,
        start: u64,
        image: &Image,
        p: &mut impl StructuralProgress,
    ) -> Result<()> {
        run_event(self.runs.len(), p)?;
        let len = image.len();
        let end = start
            .checked_add(len)
            .filter(|end| *end <= self.len)
            .ok_or(ObservedValueError::InvalidRange)?;
        if len == 0 {
            return Ok(());
        }
        if image.is_leaf() && self.write_in_place_observed(start, end, image, p)? {
            return Ok(());
        }
        self.split_at_observed(start, p)?;
        self.split_at_observed(end, p)?;
        let mut covered = Vec::new();
        run_event(self.runs.len(), p)?;
        let mut runs = self.runs.range(start..end);
        loop {
            run_event(0, p)?;
            let Some((&key, _)) = runs.next() else { break };
            reserve(&mut covered, 1, p)?;
            covered.push(key);
        }
        for key in covered {
            run_event(self.runs.len(), p)?;
            if let Some(old) = self.runs.remove(&key) {
                old.retire_observed(p);
            }
        }
        if let Some(bytes) = image.as_dense() {
            run_event(self.runs.len(), p)?;
            if let Some((&left_start, left)) = self.runs.range_mut(..start).next_back()
                && left_start.checked_add(left.len()) == Some(start)
                && left.try_append_in_place_observed(bytes, p)?
            {
                return Ok(());
            }
        }
        self.insert_observed(start, image.clone_observed(p)?, p)
    }

    fn insert_observed(
        &mut self,
        start: u64,
        image: Image,
        p: &mut impl StructuralProgress,
    ) -> Result<()> {
        // A B-tree insertion may split all ancestors. Charge a conservative
        // whole-current-container bound before entering std's allocator; this
        // depends on stored runs, never on their logical extents.
        let admission = (|| {
            let cost =
                crate::interpret::observed::btree::insertion_cost::<u64, Image>(self.runs.len())?;
            p.admit(ExecutionPhase::HostAllocation, cost.work, cost.copy_bytes)?;
            run_event(self.runs.len(), p)
        })();
        if let Err(error) = admission {
            image.retire_observed(p);
            return Err(error);
        }
        if let Some(old) = self.runs.insert(start, image) {
            old.retire_observed(p);
        }
        Ok(())
    }

    fn write_in_place_observed(
        &mut self,
        start: u64,
        end: u64,
        leaf: &Image,
        p: &mut impl StructuralProgress,
    ) -> Result<bool> {
        run_event(self.runs.len(), p)?;
        let Some((&run_start, run)) = self.runs.range_mut(..=start).next_back() else {
            return Ok(false);
        };
        if run_start
            .checked_add(run.len())
            .is_none_or(|run_end| run_end < end)
            || run.as_dense().is_none()
        {
            return Ok(false);
        }
        let at =
            usize::try_from(start - run_start).map_err(|_| ObservedValueError::CapacityOverflow)?;
        let len = usize::try_from(end - start).map_err(|_| ObservedValueError::CapacityOverflow)?;
        let window = run
            .dense_mut_observed(p)?
            .ok_or(ObservedValueError::UnsupportedValue)?;
        let finish = at
            .checked_add(len)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        let target = window
            .get_mut(at..finish)
            .ok_or(ObservedValueError::InvalidRange)?;
        if let Some(bytes) = leaf.as_dense() {
            if bytes.len() != target.len() {
                return Err(ObservedValueError::InvalidRange);
            }
            for (destination, source) in target.iter_mut().zip(bytes) {
                p.admit(ExecutionPhase::LiteralElement, 1, size_of::<Option<u8>>())?;
                *destination = *source;
            }
        } else if let Some(byte) = leaf.as_uniform() {
            // Only an already materialized literal window is touched here.
            // A fill of an unmaterialized huge extent takes the one-run path.
            for destination in target {
                p.admit(ExecutionPhase::LiteralElement, 1, size_of::<Option<u8>>())?;
                *destination = *byte;
            }
        } else {
            return Err(ObservedValueError::UnsupportedValue);
        }
        Ok(true)
    }

    fn split_at_observed(&mut self, offset: u64, p: &mut impl StructuralProgress) -> Result<()> {
        run_event(self.runs.len(), p)?;
        if offset == 0 || offset >= self.len || self.runs.contains_key(&offset) {
            return Ok(());
        }
        run_event(self.runs.len(), p)?;
        let Some((&start, run)) = self.runs.range(..offset).next_back() else {
            return Err(ObservedValueError::InvalidRange);
        };
        let end = start
            .checked_add(run.len())
            .ok_or(ObservedValueError::CapacityOverflow)?;
        if end <= offset {
            return Ok(());
        }
        let left = run.slice_observed(0, offset - start, p)?;
        let right = match run.slice_observed(offset - start, end - offset, p) {
            Ok(right) => right,
            Err(error) => {
                left.retire_observed(p);
                return Err(error);
            }
        };
        if let Err(error) = self.insert_observed(start, left, p) {
            right.retire_observed(p);
            return Err(error);
        }
        self.insert_observed(offset, right, p)
    }

    pub(crate) fn retire_observed(mut self, p: &mut impl StructuralProgress) {
        while !self.runs.is_empty() {
            p.retirement_poll();
            if let Some((_, image)) = self.runs.pop_first() {
                image.retire_observed(p);
            }
        }
        p.retirement_poll();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interpret::observed::ObservationStopped;

    #[derive(Default)]
    struct Progress {
        work: usize,
        copies: usize,
        work_limit: Option<usize>,
        copy_limit: Option<usize>,
        stopped: bool,
        retired: usize,
    }
    impl StructuralProgress for Progress {
        fn admit(
            &mut self,
            _: ExecutionPhase,
            work: usize,
            copies: usize,
        ) -> core::result::Result<(), ObservationStopped> {
            if self.stopped {
                return Err(ObservationStopped);
            }
            if self
                .work_limit
                .is_some_and(|limit| self.work.saturating_add(work) > limit)
                || self
                    .copy_limit
                    .is_some_and(|limit| self.copies.saturating_add(copies) > limit)
            {
                self.stopped = true;
                return Err(ObservationStopped);
            }
            self.work += work;
            self.copies += copies;
            Ok(())
        }
        fn retirement_poll(&mut self) {
            self.retired += 1;
        }
    }

    #[test]
    fn observed_maximum_allocation_and_uniform_write_use_one_run() {
        let mut p = Progress::default();
        let mut store = ByteStore::new_observed(u64::MAX, None, &mut p).unwrap();
        let fill = Image::uniform_observed(Some(7), u64::MAX, &mut p).unwrap();
        store.write_observed(0, &fill, &mut p).unwrap();
        let tail = store.read_observed(u64::MAX - 3, 3, &mut p).unwrap();
        assert_eq!(tail.get_observed(2, &mut p).unwrap(), Some(&Some(7)));
        assert_eq!(store.run_count(), 1);
        assert!(p.work < 10_000);
        tail.retire_observed(&mut p);
        fill.retire_observed(&mut p);
        store.retire_observed(&mut p);
    }

    #[test]
    fn observed_overlapping_copy_keeps_prewrite_image_and_initialization() {
        let mut p = Progress::default();
        let mut store = ByteStore::new_observed(4, None, &mut p).unwrap();
        let initial = Image::dense_observed(vec![Some(1), None, Some(3), Some(4)], &mut p).unwrap();
        store.write_observed(0, &initial, &mut p).unwrap();
        let before = store.read_observed(0, 3, &mut p).unwrap();
        store.write_observed(1, &before, &mut p).unwrap();
        let after = store.read_observed(0, 4, &mut p).unwrap();
        for (index, expected) in [Some(1), Some(1), None, Some(3)].iter().enumerate() {
            assert_eq!(
                after.get_observed(index as u64, &mut p).unwrap(),
                Some(expected)
            );
        }
        assert_eq!(before.get_observed(1, &mut p).unwrap(), Some(&None));
        after.retire_observed(&mut p);
        before.retire_observed(&mut p);
        initial.retire_observed(&mut p);
        store.retire_observed(&mut p);
    }

    #[test]
    fn observed_many_run_read_can_refuse_inside_one_instruction() {
        let mut p = Progress::default();
        let mut store = ByteStore::new_observed(128, None, &mut p).unwrap();
        let byte = Image::uniform_observed(Some(9), 1, &mut p).unwrap();
        for offset in (0..128).step_by(2) {
            store.write_observed(offset, &byte, &mut p).unwrap();
        }
        assert!(store.run_count() > 32);
        let retired_before = p.retired;
        p.work_limit = Some(p.work + store.run_count() + 40);
        assert!(matches!(
            store.read_observed(0, 128, &mut p),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert!(p.stopped);
        assert!(
            p.retired > retired_before,
            "partial read scratch was retired after refusal"
        );
        byte.retire_observed(&mut p);
        store.retire_observed(&mut p);
    }

    #[test]
    fn observed_cow_copy_quota_refuses_and_preserves_shared_snapshot() {
        let mut p = Progress::default();
        let mut store = ByteStore::new_observed(16, None, &mut p).unwrap();
        let literal = Image::dense_observed((0..16).map(Some).collect(), &mut p).unwrap();
        store.write_observed(0, &literal, &mut p).unwrap();
        let snapshot = store.read_observed(0, 16, &mut p).unwrap();
        let replacement = Image::dense_observed(vec![Some(99)], &mut p).unwrap();
        p.copy_limit = Some(p.copies);
        assert!(matches!(
            store.write_observed(4, &replacement, &mut p),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(
            store.len, 0,
            "a failed execution keeps no partial allocation"
        );
        let mut healthy = Progress::default();
        assert_eq!(
            snapshot.get_observed(4, &mut healthy).unwrap(),
            Some(&Some(4))
        );
        snapshot.retire_observed(&mut p);
        replacement.retire_observed(&mut p);
        literal.retire_observed(&mut p);
        store.retire_observed(&mut p);
    }
}
