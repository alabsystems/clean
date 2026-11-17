// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Termination guard shared by the raw elaborator-metadata spine readers.
//!
//! An expression decoder's memo cannot protect these earlier walks. A spine
//! has one successor, so seeing the same raw pointer twice is a cycle, never
//! ordinary DAG sharing. The byte length bounds the number of distinct valid
//! offsets without imposing a smaller limit on any acyclic captured region.

use super::{deadline, ImportError};
use crate::region::CompactedRegion;
use std::collections::HashSet;

pub(super) struct BinderSpine<'a> {
    name: &'a str,
    seen: HashSet<u64>,
    remaining: usize,
}

impl<'a> BinderSpine<'a> {
    pub(super) fn new(region: &CompactedRegion<'_>, name: &'a str) -> Result<Self, ImportError> {
        deadline::check()?;
        Ok(Self {
            name,
            seen: HashSet::new(),
            remaining: region.len(),
        })
    }

    pub(super) fn visit(&mut self, pointer: u64) -> Result<(), ImportError> {
        deadline::poll()?;
        if !self.seen.insert(pointer) {
            return Err(ImportError::ResourceLimit {
                operation: format!("reading raw binder names of `{}`", self.name),
                reason: format!("cyclic expression spine at {pointer:#x}"),
            });
        }
        self.remaining =
            self.remaining
                .checked_sub(1)
                .ok_or_else(|| ImportError::ResourceLimit {
                    operation: format!("reading raw binder names of `{}`", self.name),
                    reason: "expression spine exceeds its captured region's byte length".into(),
                })?;
        Ok(())
    }
}
