// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{CdclSolver, Lit};

/// Whether a SAT trail entry came from a branching decision or propagation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CdclTrailKind {
    Decision,
    Propagation,
}

/// One SAT assignment on the CDCL trail with its decision-level metadata.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct CdclTrailEntry {
    pub(crate) lit: Lit,
    pub(crate) level: u32,
    pub(crate) kind: CdclTrailKind,
}

impl CdclSolver {
    /// Snapshot the current SAT assignment trail in trail order.
    pub(crate) fn trail_entries(&self) -> Vec<CdclTrailEntry> {
        self.trail
            .iter()
            .copied()
            .map(|lit| {
                let var_data = &self.var_data[lit.var().index()];
                let kind = if var_data.reason.is_valid() {
                    CdclTrailKind::Propagation
                } else {
                    CdclTrailKind::Decision
                };
                CdclTrailEntry {
                    lit,
                    level: var_data.level,
                    kind,
                }
            })
            .collect()
    }
}
