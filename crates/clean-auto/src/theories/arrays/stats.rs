// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::theory::ArrayTheory;

impl ArrayTheory {
    /// Get statistics about the array theory state.
    pub fn stats(&self) -> ArrayStats {
        ArrayStats {
            num_selects: self.selects.len(),
            num_stores: self.stores.len(),
            num_equalities: self.equalities.len(),
            num_disequalities: self.disequalities.len(),
        }
    }
}

/// Statistics for array theory.
#[derive(Clone, Debug, Default)]
pub struct ArrayStats {
    pub num_selects: usize,
    pub num_stores: usize,
    pub num_equalities: usize,
    pub num_disequalities: usize,
}
