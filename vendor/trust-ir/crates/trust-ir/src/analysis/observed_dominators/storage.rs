// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;

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
    pub(super) fn poll(&mut self) -> R {
        self.admit(1, 0)
    }
    pub(super) fn publication(&mut self, copy_bytes: usize) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: self.site,
                work: 1,
                copy_bytes,
            })
            .map_err(Into::into)
    }
    fn lookup(&mut self, len: usize) -> R {
        self.admit(observed_btree::population_work(len)?, 0)
    }
    fn tree<K, V>(&mut self, len: usize) -> R {
        let cost = observed_btree::insertion_cost::<K, V>(len)?;
        self.admit(cost.work, cost.copy_bytes)
    }
    // All private call sites use fixed-size integer/tuple keys and Copy values.
    pub(super) fn read<K: Ord, V: Copy>(&mut self, map: &BTreeMap<K, V>, key: &K) -> R<Option<V>> {
        self.lookup(map.len())?;
        Ok(map.get(key).copied())
    }
    pub(super) fn insert<K: Ord, V: Copy>(
        &mut self,
        map: &mut BTreeMap<K, V>,
        key: K,
        value: V,
    ) -> R {
        self.tree::<K, V>(map.len())?;
        map.insert(key, value);
        Ok(())
    }
    pub(super) fn contains(&mut self, set: &BTreeSet<u32>, key: u32) -> R<bool> {
        self.lookup(set.len())?;
        Ok(set.contains(&key))
    }
    pub(super) fn mark(&mut self, set: &mut BTreeSet<u32>, key: u32) -> R<bool> {
        if self.contains(set, key)? {
            return Ok(false);
        }
        self.tree::<u32, ()>(set.len())?;
        Ok(set.insert(key))
    }
    pub(super) fn reserve<T>(&mut self, values: &mut Vec<T>) -> R {
        self.poll()?;
        if values.len() == values.capacity() {
            let requested = values
                .len()
                .checked_mul(2)
                .and_then(|n| n.checked_add(1))
                .ok_or(ObservedValueError::CapacityOverflow)?;
            let images = requested
                .checked_add(values.len())
                .ok_or(ObservedValueError::CapacityOverflow)?;
            self.admit(
                images,
                images
                    .checked_mul(size_of::<T>())
                    .ok_or(ObservedValueError::CapacityOverflow)?,
            )?;
            values
                .try_reserve_exact(requested - values.len())
                .map_err(|_| ObservedValueError::AllocationFailed)?;
        }
        Ok(())
    }
    pub(super) fn push<T: Copy>(&mut self, values: &mut Vec<T>, value: T) -> R {
        self.reserve(values)?;
        self.admit(1, size_of::<T>())?;
        values.push(value);
        Ok(())
    }
    pub(super) fn row<'a>(
        &mut self,
        map: &'a BTreeMap<u32, Vec<u32>>,
        key: u32,
    ) -> R<Option<&'a [u32]>> {
        self.lookup(map.len())?;
        Ok(map.get(&key).map(Vec::as_slice))
    }
    pub(super) fn ensure_row(&mut self, map: &mut BTreeMap<u32, Vec<u32>>, key: u32) -> R {
        self.lookup(map.len())?;
        if !map.contains_key(&key) {
            self.tree::<u32, Vec<u32>>(map.len())?;
            if let Some(old) = map.insert(key, Vec::new()) {
                self.retire_vec(old);
            }
        }
        Ok(())
    }
    pub(super) fn append(&mut self, map: &mut BTreeMap<u32, Vec<u32>>, key: u32, value: u32) -> R {
        self.ensure_row(map, key)?;
        self.lookup(map.len())?;
        let row = map.get_mut(&key).ok_or(ObservedValueError::InvalidRange)?;
        self.push(row, value)
    }
    pub(super) fn store_row(
        &mut self,
        map: &mut BTreeMap<u32, Vec<u32>>,
        key: u32,
        row: &mut Vec<u32>,
    ) -> R {
        self.tree::<u32, Vec<u32>>(map.len())?;
        if let Some(old) = map.insert(key, take(row)) {
            self.retire_vec(old);
        }
        self.poll()
    }
    pub(super) fn remove<K: Ord, V: Copy>(&mut self, map: &mut BTreeMap<K, V>, key: &K) -> R {
        self.lookup(map.len())?;
        map.remove(key);
        Ok(())
    }
    pub(super) fn retire<T>(&mut self, value: T) {
        self.session.retirement_step(self.site, 1);
        drop(value);
        self.session.retirement_poll(self.site);
    }
    pub(super) fn retire_vec<T: Copy>(&mut self, mut values: Vec<T>) {
        while !values.is_empty() {
            self.session.retirement_step(self.site, 1);
            values.pop();
        }
        self.retire(values);
    }
    pub(super) fn retire_map<K: Ord + Copy, V: Copy>(&mut self, map: &mut BTreeMap<K, V>) {
        while !map.is_empty() {
            self.session
                .retirement_step(self.site, map.len().saturating_add(1));
            map.pop_first();
        }
        self.retire(take(map));
    }
    pub(super) fn retire_set(&mut self, set: &mut BTreeSet<u32>) {
        while !set.is_empty() {
            self.session
                .retirement_step(self.site, set.len().saturating_add(1));
            set.pop_first();
        }
        self.retire(take(set));
    }
    pub(super) fn retire_rows(&mut self, map: &mut BTreeMap<u32, Vec<u32>>) {
        while !map.is_empty() {
            self.session
                .retirement_step(self.site, map.len().saturating_add(1));
            if let Some((_, row)) = map.pop_first() {
                self.retire_vec(row);
            }
        }
        self.retire(take(map));
    }
    pub(super) fn terminal(&self, error: ObservedValueError) -> ObservedValueError {
        if self.session.first_refusal().is_some() {
            ObservedValueError::AdmissionRefused
        } else {
            error
        }
    }
}
