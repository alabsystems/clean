// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Recursor-application argument layout used by the branch-sharing comparison.
//!
//! Split out of `branch_sharing.rs`: this is the pure *layout* half — given a
//! recursor's arity data and its argument spine, it names the sub-ranges
//! (params, motives, indices, major premise, minors, extras) for both
//! `RecursorArgOrder` conventions. It holds no cache and does no reduction;
//! `branch_sharing.rs` owns those.

use crate::inductive::RecursorArgOrder;
use crate::name::Name;
use std::ops::Range;

pub(super) struct RecursorApp<'a> {
    pub(super) name: &'a Name,
    pub(super) levels: &'a [crate::level::Level],
    pub(super) arg_order: RecursorArgOrder,
    pub(super) num_params: usize,
    pub(super) num_indices: usize,
    pub(super) num_motives: usize,
    pub(super) num_minors: usize,
    pub(super) args: crate::expr::AppArgs<'a>,
}

impl<'a> RecursorApp<'a> {
    pub(super) fn args_before_major(&self) -> usize {
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

    pub(super) fn extras_range(&self) -> Range<usize> {
        let start = match self.arg_order {
            RecursorArgOrder::MajorAfterMinors => self.major_idx() + 1,
            RecursorArgOrder::MajorAfterMotive => self.minors_range().end,
        };
        start..self.args.len()
    }
}
