// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cache for environment-level delta reduction results.
//!
//! This cache stores constant unfolding results keyed by declaration name.
//! Unlike the type checker's WHNF cache, these entries persist across
//! type-checker instances and memoize only the first delta-reduction step.

use crate::expr::Expr;
use crate::name::Name;
use std::collections::HashMap;

/// Default maximum number of cached unfoldings.
const DEFAULT_MAX_CAPACITY: usize = 10_000;

/// Cache of unfolded constant definitions shared at the environment level.
///
/// The cache maps a constant name to the expression obtained by unfolding that
/// constant's definition. When the cache reaches capacity, it is cleared
/// entirely before inserting a new entry.
#[derive(Clone, Debug)]
pub(crate) struct ReductionCache {
    entries: HashMap<Name, Expr>,
    max_capacity: usize,
}

impl ReductionCache {
    /// Creates an empty reduction cache with the default capacity.
    pub(crate) fn new() -> Self {
        Self::with_capacity(DEFAULT_MAX_CAPACITY)
    }

    /// Creates an empty reduction cache with the given maximum capacity.
    ///
    /// A capacity of `0` disables storage: inserts become no-ops.
    pub(crate) fn with_capacity(max: usize) -> Self {
        Self {
            entries: HashMap::with_capacity(max),
            max_capacity: max,
        }
    }

    /// Returns the cached unfolding for `name`, if present.
    pub(crate) fn get(&self, name: &Name) -> Option<&Expr> {
        self.entries.get(name)
    }

    /// Inserts a cached unfolding result.
    ///
    /// If inserting a new key would exceed the configured capacity, the cache
    /// is cleared before the new entry is stored.
    pub(crate) fn insert(&mut self, name: Name, value: Expr) {
        if self.max_capacity == 0 {
            return;
        }

        if self.entries.len() >= self.max_capacity && !self.entries.contains_key(&name) {
            self.clear();
        }

        self.entries.insert(name, value);
    }

    /// Returns the number of cached unfoldings.
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    /// Returns `true` when the cache contains no entries.
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Removes all cached unfoldings.
    pub(crate) fn clear(&mut self) {
        self.entries.clear();
    }
}

impl Default for ReductionCache {
    fn default() -> Self {
        Self::new()
    }
}
