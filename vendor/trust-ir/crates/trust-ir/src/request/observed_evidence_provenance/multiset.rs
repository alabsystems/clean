// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
impl<O: ExecutionObserver> Work<'_, '_, O> {
    pub(super) fn multiset(
        &mut self,
        expected: &[NativeToolIdentity],
        actual: &[NativeToolIdentity],
    ) -> R<bool> {
        self.admit(2, 2 * size_of::<usize>() + size_of::<bool>())?;
        if expected.len() != actual.len() {
            return Ok(false);
        }
        let mut at = 0;
        while let Some(value) = self.at(actual, at)? {
            let expected_count = self.count(expected, value)?;
            let actual_count = self.count(actual, value)?;
            self.admit(1, 2 * size_of::<usize>() + size_of::<bool>())?;
            if expected_count != actual_count {
                return Ok(false);
            }
            self.next(&mut at)?;
        }
        // Equal total length and equal multiplicities for every actual value
        // iff sorted raw records are equal, including duplicate counts. No
        // canonical-name/set shortcut, clone/sort or BTree/hash setup occurs.
        self.admit(1, size_of::<bool>())?;
        Ok(true)
    }
    fn count(&mut self, rows: &[NativeToolIdentity], needle: &NativeToolIdentity) -> R<usize> {
        self.admit(2, 2 * size_of::<usize>())?;
        let mut count = 0usize;
        let mut at = 0;
        while let Some(value) = self.at(rows, at)? {
            self.admit(
                1,
                size_of::<R<bool>>() + 2 * size_of::<&NativeToolIdentity>(),
            )?;
            if value.structural_eq_observed(needle, self.session, self.site)? {
                self.admit(1, size_of::<usize>())?;
                count = count
                    .checked_add(1)
                    .ok_or(ObservedValueError::CapacityOverflow)?;
            }
            self.next(&mut at)?;
        }
        self.admit(1, size_of::<usize>())?;
        Ok(count)
    }
}
