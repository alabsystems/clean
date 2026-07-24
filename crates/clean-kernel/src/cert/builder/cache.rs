// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared WHNF cache for certificate building.

use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::RwLock;

use crate::expr::Expr;

/// Shared cache for builder-side WHNF reductions.
///
/// This cache is intended to be wrapped in an `Arc` and reused across multiple
/// `CertBuilder` instances in batch mode.
#[derive(Debug, Default)]
pub struct WhnfCache {
    entries: RwLock<HashMap<Expr, Expr>>,
    hits: AtomicUsize,
    misses: AtomicUsize,
}

impl WhnfCache {
    /// Create an empty WHNF cache.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    pub(crate) fn get(&self, expr: &Expr) -> Option<Expr> {
        let result = self
            .entries
            .read()
            .expect("invariant: WHNF cache lock not poisoned")
            .get(expr)
            .cloned();

        if result.is_some() {
            self.hits.fetch_add(1, Ordering::Relaxed);
        } else {
            self.misses.fetch_add(1, Ordering::Relaxed);
        }

        result
    }

    pub(crate) fn insert(&self, expr: Expr, whnf: Expr) {
        self.entries
            .write()
            .expect("invariant: WHNF cache lock not poisoned")
            .insert(expr, whnf);
    }

    /// Number of cached WHNF entries.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries
            .read()
            .expect("invariant: WHNF cache lock not poisoned")
            .len()
    }

    /// Whether the cache is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[cfg(test)]
    pub(crate) fn hits(&self) -> usize {
        self.hits.load(Ordering::Relaxed)
    }

    #[cfg(test)]
    pub(crate) fn misses(&self) -> usize {
        self.misses.load(Ordering::Relaxed)
    }
}
