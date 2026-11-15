// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Inference-local structural support, not cached typing or proof authority.

use super::support::Support;
use crate::cert::ProofCert;
use std::collections::HashMap;
use std::sync::{Arc, Weak};

/// Reuse only exhaustive, target-independent FVar-free support summaries.
///
/// SOUNDNESS: the key denotes an immutable actual certificate Arc, never a
/// temporary root value. A live Weak allocation prevents address reuse; lookup
/// additionally upgrades and checks pointer identity before using its summary.
/// Arc::make_mut either cannot mutate a shared allocation or dissociates its
/// Weak owners. No node value or previous certificate version is kept alive.
/// Binder depth is NOT erased: callers must still apply unchanged_at(depth),
/// including its loose-BVar and checked-depth conditions. This cache contains
/// no target-specific FVar absence result and makes no validity assertion.
#[derive(Default)]
pub(in crate::tc) struct RebindClosedMemo {
    entries: HashMap<usize, (Weak<ProofCert>, Support)>,
    #[cfg(test)]
    pub(super) visits: usize,
    #[cfg(test)]
    pub(super) hits: usize,
}

impl RebindClosedMemo {
    pub(super) fn get(&mut self, cert: &Arc<ProofCert>) -> Option<Support> {
        let key = Arc::as_ptr(cert) as usize;
        let (owner, support) = self.entries.get(&key)?;
        if owner.upgrade().is_some_and(|live| Arc::ptr_eq(&live, cert)) {
            #[cfg(test)]
            {
                self.hits += 1;
            }
            Some(*support)
        } else {
            self.entries.remove(&key);
            None
        }
    }

    pub(super) fn insert(&mut self, cert: &Arc<ProofCert>, support: Support, cap: usize) {
        if support.fvar_free() && self.entries.len() < cap {
            self.entries
                .insert(Arc::as_ptr(cert) as usize, (Arc::downgrade(cert), support));
        }
    }

    pub(in crate::tc) fn clear(&mut self) {
        self.entries.clear();
    }

    #[cfg(test)]
    pub(in crate::tc) fn len(&self) -> usize {
        self.entries.len()
    }
}

#[cfg(test)]
#[path = "rebind_closed_memo_tests.rs"]
mod tests;

#[cfg(all(test, not(debug_assertions)))]
#[path = "rebind_closed_memo_release_tests.rs"]
mod release_tests;
