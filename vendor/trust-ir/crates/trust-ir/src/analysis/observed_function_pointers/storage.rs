// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
pub(super) struct Work<'s, 'o, O: ExecutionObserver> {
    pub(super) session: &'s mut ObservedSession<'o, O>,
    pub(super) site: ExecutionSite,
}
impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn admit(&mut self, work: usize, copy_bytes: usize) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Validation,
                site: self.site,
                work,
                copy_bytes,
            })
            .map_err(Into::into)
    }
    pub(super) fn publication(&mut self, copy_bytes: usize) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: self.site,
                work: usize::from(copy_bytes != 0),
                copy_bytes,
            })
            .map_err(Into::into)
    }
    pub(super) fn lookup(&mut self, len: usize) -> R {
        self.admit(1, size_of::<usize>())?;
        self.admit(observed_btree::population_work(len)?, 0)
    }
    pub(super) fn tree<V>(&mut self, len: usize) -> R {
        self.admit(
            6 * 16,
            size_of::<[core::alloc::Layout; 6]>() + 4 * size_of::<usize>(),
        )?;
        let cost = observed_btree::insertion_cost::<u32, V>(len)?;
        self.admit(cost.work, cost.copy_bytes)
    }
    // Private call sites have u32 keys and fixed-header Copy values only.
    pub(super) fn read<V: Copy>(&mut self, map: &BTreeMap<u32, V>, key: u32) -> R<Option<V>> {
        self.lookup(map.len())?;
        self.admit(1, size_of::<Option<V>>())?;
        Ok(map.get(&key).copied())
    }
    pub(super) fn insert<V: Copy>(&mut self, map: &mut BTreeMap<u32, V>, key: u32, value: V) -> R {
        self.tree::<V>(map.len())?;
        self.admit(1, size_of::<Option<V>>())?;
        let _ = map.insert(key, value);
        Ok(())
    }
    pub(super) fn contains(&mut self, set: &BTreeSet<u32>, key: u32) -> R<bool> {
        self.lookup(set.len())?;
        self.admit(1, size_of::<bool>())?;
        Ok(set.contains(&key))
    }
    pub(super) fn mark(&mut self, set: &mut BTreeSet<u32>, key: u32) -> R {
        self.tree::<()>(set.len())?;
        self.admit(1, size_of::<bool>())?;
        set.insert(key);
        Ok(())
    }
    pub(super) fn unmark(&mut self, set: &mut BTreeSet<u32>, key: u32) -> R {
        self.lookup(set.len())?;
        self.admit(1, size_of::<bool>())?;
        set.remove(&key);
        Ok(())
    }
    pub(super) fn at<'a, T>(&mut self, rows: &'a [T], at: usize) -> R<Option<&'a T>> {
        self.admit(1, size_of::<Option<&T>>())?;
        Ok(rows.get(at))
    }
    pub(super) fn next(&mut self, at: &mut usize) -> R {
        self.admit(1, size_of::<usize>())?;
        *at = at
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        Ok(())
    }
    pub(super) fn push<T: Copy>(&mut self, rows: &mut Vec<T>, value: T) -> R {
        self.admit(1, size_of::<usize>())?;
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
        self.admit(1, size_of::<T>())?;
        rows.push(value);
        Ok(())
    }
    pub(super) fn cursor<V>(&mut self, len: usize) -> R {
        self.lookup(len)?;
        self.admit(1, size_of::<Iter<'_, u32, V>>())
    }
    pub(super) fn cursor_next<V>(&mut self, len: usize) -> R {
        self.lookup(len)?;
        self.admit(1, size_of::<Option<(&u32, &V)>>())
    }
    pub(super) fn step(&mut self, work: usize) {
        self.session.retirement_step(self.site, work);
    }
    pub(super) fn poll(&mut self) {
        self.session.retirement_poll(self.site);
    }
    pub(super) fn terminal(&self, error: ObservedValueError) -> ObservedValueError {
        if self.session.first_refusal().is_some() {
            ObservedValueError::AdmissionRefused
        } else {
            error
        }
    }
}
