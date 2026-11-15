// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Recursor-application argument layout shared by congruence comparisons.
//!
//! Split out of `branch_sharing.rs`: this is the pure *layout* half — given a
//! recursor's arity data and its argument spine, it names the sub-ranges
//! (params, motives, indices, major premise, minors, extras) for both
//! `RecursorArgOrder` conventions. It holds no cache and does no reduction;
//! `branch_sharing.rs` owns those.

use crate::inductive::{RecursorArgOrder, RecursorVal};
use crate::name::Name;
use std::ops::Range;

pub(super) struct RecursorApp<'a> {
    pub(super) name: &'a Name,
    pub(super) levels: &'a [crate::level::Level],
    pub(super) layout: RecursorLayout,
    pub(super) args: crate::expr::AppArgs<'a>,
}

/// The layout needs only registered arities, not another application-spine walk.
pub(super) struct RecursorLayout {
    arg_order: RecursorArgOrder,
    num_params: usize,
    num_indices: usize,
    num_motives: usize,
    num_minors: usize,
}

impl RecursorLayout {
    pub(super) fn new(recursor: &RecursorVal) -> Self {
        Self {
            arg_order: recursor.arg_order,
            num_params: recursor.num_params as usize,
            num_indices: recursor.num_indices as usize,
            num_motives: recursor.num_motives as usize,
            num_minors: recursor.num_minors as usize,
        }
    }

    fn args_before_major(&self) -> usize {
        match self.arg_order {
            RecursorArgOrder::MajorAfterMinors => {
                self.num_params + self.num_motives + self.num_minors + self.num_indices
            }
            RecursorArgOrder::MajorAfterMotive => {
                self.num_params + self.num_motives + self.num_indices
            }
        }
    }

    pub(super) fn required_args(&self) -> usize {
        match self.arg_order {
            RecursorArgOrder::MajorAfterMinors => self.args_before_major() + 1,
            RecursorArgOrder::MajorAfterMotive => self.args_before_major() + 1 + self.num_minors,
        }
    }

    pub(super) fn params_range(&self) -> Range<usize> {
        0..self.num_params
    }

    pub(super) fn motives_range(&self) -> Range<usize> {
        let start = self.params_range().end;
        start..start + self.num_motives
    }

    pub(super) fn indices_range(&self) -> Range<usize> {
        match self.arg_order {
            RecursorArgOrder::MajorAfterMinors => {
                let start = self.minors_range().end;
                start..start + self.num_indices
            }
            RecursorArgOrder::MajorAfterMotive => {
                let start = self.motives_range().end;
                start..start + self.num_indices
            }
        }
    }

    pub(super) fn major_idx(&self) -> usize {
        self.args_before_major()
    }

    pub(super) fn minors_range(&self) -> Range<usize> {
        match self.arg_order {
            RecursorArgOrder::MajorAfterMinors => {
                let start = self.motives_range().end;
                start..start + self.num_minors
            }
            RecursorArgOrder::MajorAfterMotive => {
                let start = self.major_idx() + 1;
                start..start + self.num_minors
            }
        }
    }

    pub(super) fn extras_range(&self, arg_count: usize) -> Range<usize> {
        let start = match self.arg_order {
            RecursorArgOrder::MajorAfterMinors => self.major_idx() + 1,
            RecursorArgOrder::MajorAfterMotive => self.minors_range().end,
        };
        start..arg_count
    }

    /// Visit every supplied argument once, with the major before the minors.
    /// Partial recursor applications retain ordinary application congruence.
    pub(super) fn comparison_indices(
        &self,
        arg_count: usize,
    ) -> Option<impl Iterator<Item = usize>> {
        if arg_count < self.required_args() {
            return None;
        }
        Some(
            (0..self.motives_range().end)
                .chain(self.indices_range())
                .chain(std::iter::once(self.major_idx()))
                .chain(self.minors_range())
                .chain(self.extras_range(arg_count)),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::{RecursorArgOrder, RecursorLayout};

    #[test]
    fn recursor_comparison_layout_covers_each_slot_once_in_both_orders() {
        for (arg_order, expected) in [
            (
                RecursorArgOrder::MajorAfterMinors,
                vec![0, 1, 2, 3, 7, 8, 9, 4, 5, 6, 10, 11],
            ),
            (RecursorArgOrder::MajorAfterMotive, (0..12).collect()),
        ] {
            let layout = RecursorLayout {
                arg_order,
                num_params: 2,
                num_motives: 2,
                num_indices: 2,
                num_minors: 3,
            };
            assert_eq!(layout.required_args(), 10);
            for partial_arity in 0..10 {
                assert!(layout.comparison_indices(partial_arity).is_none());
            }
            for arg_count in [10, 11, 12] {
                let actual: Vec<_> = layout
                    .comparison_indices(arg_count)
                    .expect("saturated recursor has a comparison order")
                    .collect();
                assert_eq!(actual, expected[..arg_count]);
                let mut slots = actual;
                slots.sort_unstable();
                assert_eq!(slots, (0..arg_count).collect::<Vec<_>>());
            }
        }
    }
}
