// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Admit before actual B-tree iterator construction AND every advancement.
use super::*;
use std::collections::btree_map::{Iter, ValuesMut};
#[cfg(test)]
mod tests;
pub(super) struct Entries<'a, K, V> {
    population: usize,
    actual: Iter<'a, K, V>,
}
pub(super) struct Rows<'a> {
    population: usize,
    actual: ValuesMut<'a, u32, Vec<u32>>,
}
impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn entries<'a, K, V>(&mut self, map: &'a BTreeMap<K, V>) -> R<Entries<'a, K, V>> {
        let bytes = size_of::<Entries<'a, K, V>>()
            .checked_mul(2)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        // Price both borrowed descriptor images before construction. Tree
        // descent may be lazy until first next(), which is charged separately.
        self.admit(observed_btree::population_work(map.len())?, bytes)?;
        Ok(Entries {
            population: map.len(),
            actual: map.iter(),
        })
    }
    pub(super) fn rows<'a>(&mut self, map: &'a mut BTreeMap<u32, Vec<u32>>) -> R<Rows<'a>> {
        let population = map.len();
        let bytes = size_of::<Rows<'a>>()
            .checked_mul(2)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        self.admit(observed_btree::population_work(population)?, bytes)?;
        Ok(Rows {
            population,
            actual: map.values_mut(),
        })
    }
}
impl<'a, K, V> Entries<'a, K, V> {
    pub(super) fn next<O: ExecutionObserver>(
        &mut self,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<(&'a K, &'a V)>> {
        // A for-loop body poll runs after .next(). Keep this admission before
        // every actual advance, including the final exhausted-tree advance.
        work.admit(
            observed_btree::population_work(self.population)?,
            size_of::<(&K, &V)>(),
        )?;
        Ok(self.actual.next())
    }
}
impl<'a> Rows<'a> {
    pub(super) fn next<O: ExecutionObserver>(
        &mut self,
        work: &mut Work<'_, '_, O>,
    ) -> R<Option<&'a mut Vec<u32>>> {
        work.admit(
            observed_btree::population_work(self.population)?,
            size_of::<&mut Vec<u32>>(),
        )?;
        Ok(self.actual.next())
    }
}
