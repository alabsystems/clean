// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::expr::{BinderData, BinderInfo, Expr, FVarId};
use crate::name::Name;
// HashMap in production, BTreeMap under Kani verification.
// HashMap's RandomState calls CCRandomGenerateBytes (Apple random) which Kani
// cannot model (kani#2423). BTreeMap avoids this by using Ord instead of Hash.
#[cfg(kani)]
use std::collections::{BTreeMap, BTreeSet};
#[cfg(not(kani))]
use std::collections::{HashMap, HashSet};

/// Saturating addition for De Bruijn indices.
///
/// Returns `a + b`, saturating at `u32::MAX` on overflow instead of panicking.
/// Saturation is safe because De Bruijn depths in the TypeChecker are bounded
/// by expression nesting depth, which is far below u32::MAX.
///
/// # Contract
///
/// ENSURES: Returns `a + b` when no overflow
/// ENSURES: Returns `u32::MAX` when `a + b` would overflow
/// ENSURES: Never panics
pub(super) fn checked_add_u32(a: u32, b: u32, _context: &'static str) -> u32 {
    a.saturating_add(b)
}

/// Local context entry
#[derive(Clone, Debug)]
pub struct LocalDecl {
    /// Unique identifier
    pub id: FVarId,
    /// User-facing name
    pub name: Name,
    /// Type of the variable
    pub type_: Expr,
    /// Value (for let bindings)
    pub value: Option<Expr>,
    /// Binder data (info + multiplicity)
    pub bi: BinderData,
}

/// Local context (stack of local declarations)
#[derive(Clone, Debug, Default)]
pub struct LocalContext {
    decls: Vec<LocalDecl>,
    #[cfg(not(kani))]
    index_by_id: HashMap<FVarId, usize>,
    #[cfg(kani)]
    index_by_id: BTreeMap<FVarId, usize>,
    #[cfg(not(kani))]
    used_ids: HashSet<FVarId>,
    #[cfg(kani)]
    used_ids: BTreeSet<FVarId>,
    next_id: u64,
    /// Monotone lower bound for `push_low_local`'s free-id scan. `used_ids`
    /// is permanent, so every id below the cursor is known-used and the scan
    /// may start here instead of re-probing the dense range from
    /// `decls.len()` on every push — that re-probe made long unifier
    /// sessions QUADRATIC in cumulative allocations (measured: a 2.55M-push
    /// corec-spine elaboration spent ~6.6e10 hash probes; with the cursor,
    /// 340). Uniqueness is still enforced by the unchanged `used_ids` scan
    /// loop and insert below — the cursor only moves the scan's start.
    low_cursor: u64,
}

impl LocalContext {
    /// Create a new empty context
    ///
    /// # Contract
    ///
    /// ENSURES: `result.is_empty() == true`
    /// ENSURES: `result.len() == 0`
    pub fn new() -> Self {
        Self::default()
    }

    /// Push a new variable binding
    ///
    /// # Contract
    ///
    /// ENSURES: `self.len() == old(self.len()) + 1` after call
    /// ENSURES: `self.get(result).is_some()` (returned FVarId is valid)
    /// ENSURES: `self.get(result).map(|d| &d.type_) == Some(&type_)`
    /// ENSURES: `self.get(result).and_then(|d| d.value.as_ref()).is_none()`
    pub fn push(&mut self, name: Name, type_: Expr, bi: impl Into<BinderData>) -> FVarId {
        let id = FVarId(self.next_id);
        self.next_id += 1;
        assert!(
            !self.index_by_id.contains_key(&id),
            "LocalContext::push generated active duplicate FVarId {id:?}"
        );
        assert!(
            self.used_ids.insert(id),
            "LocalContext::push generated previously-used FVarId {id:?}"
        );
        self.index_by_id.insert(id, self.decls.len());
        self.decls.push(LocalDecl {
            id,
            name,
            type_,
            value: None,
            bi: bi.into(),
        });
        id
    }

    /// Push a let binding
    ///
    /// # Contract
    ///
    /// ENSURES: `self.len() == old(self.len()) + 1` after call
    /// ENSURES: `self.get(result).is_some()` (returned FVarId is valid)
    /// ENSURES: `self.get(result).map(|d| &d.type_) == Some(&type_)`
    /// ENSURES: `self.get(result).and_then(|d| d.value.as_ref()) == Some(&value)`
    pub fn push_let(&mut self, name: Name, type_: Expr, value: Expr) -> FVarId {
        let id = FVarId(self.next_id);
        self.next_id += 1;
        assert!(
            !self.index_by_id.contains_key(&id),
            "LocalContext::push_let generated active duplicate FVarId {id:?}"
        );
        assert!(
            self.used_ids.insert(id),
            "LocalContext::push_let generated previously-used FVarId {id:?}"
        );
        self.index_by_id.insert(id, self.decls.len());
        self.decls.push(LocalDecl {
            id,
            name,
            type_,
            value: Some(value),
            bi: BinderInfo::Default.into(),
        });
        id
    }

    /// Push a new variable binding using a fresh FVarId guaranteed to lie in
    /// the *low* (non-tagged) FVarId range `[0, 1<<63)`.
    ///
    /// The elaborator's metavariable layer encodes metavars as FVarIds with the
    /// top bit (`1<<63`) set (`MetaState::META_FVAR_TAG`). When meta-FVars are
    /// registered into this context, `next_id` can be advanced past `1<<63`, so
    /// a plain [`LocalContext::push`] would hand out an id whose top bit is set
    /// — which the elaborator would then misclassify as a metavariable. This
    /// method scans for the smallest unused id below the tag boundary so the
    /// returned FVar is unambiguously a genuine local (e.g. a binder local the
    /// higher-order unifier opens under a `Pi`/`Lam`).
    ///
    /// # Contract
    ///
    /// ENSURES: `result.as_u64() < (1u64 << 63)`
    /// ENSURES: `self.get(result).is_some()`
    pub fn push_low_local(&mut self, name: Name, type_: Expr, bi: impl Into<BinderData>) -> FVarId {
        const META_TAG: u64 = 1u64 << 63;
        // Smallest free id below the tag region. `used_ids` is permanent (never
        // cleared except in tests), so this never reuses a popped id.
        let mut candidate = (self.decls.len() as u64).max(self.low_cursor);
        if candidate >= META_TAG {
            candidate = 0;
        }
        while self.used_ids.contains(&FVarId(candidate)) {
            candidate += 1;
            debug_assert!(candidate < META_TAG, "exhausted low FVarId range");
        }
        self.low_cursor = candidate + 1;
        let id = FVarId(candidate);
        self.used_ids.insert(id);
        self.index_by_id.insert(id, self.decls.len());
        self.decls.push(LocalDecl {
            id,
            name,
            type_,
            value: None,
            bi: bi.into(),
        });
        // Keep `next_id` strictly above every low-range id handed out (same
        // rule as `push_with_id`). Without this, a subsequent plain `push`
        // while this local is still active would mint the same id and trip
        // the duplicate-FVarId assertion. Never decreases the counter, so a
        // `next_id` already advanced into the meta-tagged range (>= 1<<63)
        // stays untouched — the low-range guarantee applies to the id this
        // method *returns*, not to the counter.
        if id.0 >= self.next_id {
            self.next_id = id.0 + 1;
        }
        id
    }

    /// Pop the most recent binding
    ///
    /// # Contract
    ///
    /// ENSURES: If `old(self.is_empty())` then returns `None` and `self` unchanged
    /// ENSURES: If `!old(self.is_empty())` then `self.len() == old(self.len()) - 1`
    /// ENSURES: Returned decl is no longer accessible via `get(decl.id)`
    pub fn pop(&mut self) -> Option<LocalDecl> {
        let decl = self.decls.pop()?;
        self.index_by_id.remove(&decl.id);
        Some(decl)
    }

    /// Look up a free variable
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `Some(decl)` iff `id` was pushed and not popped
    /// ENSURES: Returns `None` iff `id` was never pushed or has been popped
    pub fn get(&self, id: FVarId) -> Option<&LocalDecl> {
        let idx = *self.index_by_id.get(&id)?;
        self.decls.get(idx)
    }

    /// Number of bindings
    ///
    /// # Contract
    ///
    /// ENSURES: Returns count of currently valid FVarIds
    /// ENSURES: `result == 0` iff `is_empty() == true`
    pub fn len(&self) -> usize {
        self.decls.len()
    }

    /// Check if empty
    ///
    /// # Contract
    ///
    /// ENSURES: `result == true` iff `len() == 0`
    pub fn is_empty(&self) -> bool {
        self.decls.is_empty()
    }

    /// Truncate context back to `target_len` entries, popping from the end.
    ///
    /// Used by iterative binder comparison (`is_def_eq_binding`) to batch-restore
    /// context state after processing N consecutive binders. Equivalent to calling
    /// `pop()` `self.len() - target_len` times but avoids per-entry Option checks.
    ///
    /// # Contract
    ///
    /// REQUIRES: `target_len <= self.len()`
    /// ENSURES: `self.len() == target_len`
    /// ENSURES: All FVarIds beyond `target_len` are removed from the index
    pub(crate) fn truncate_to(&mut self, target_len: usize) {
        while self.decls.len() > target_len {
            if let Some(decl) = self.decls.pop() {
                self.index_by_id.remove(&decl.id);
            }
        }
    }

    /// Iterate over all local declarations
    ///
    /// # Contract
    ///
    /// ENSURES: Yields exactly `len()` declarations
    /// ENSURES: All yielded declarations are valid (not popped)
    pub fn iter(&self) -> impl DoubleEndedIterator<Item = &LocalDecl> + ExactSizeIterator {
        self.decls.iter()
    }

    /// Get the current next FVarId counter value.
    ///
    /// Used by TcCaches save/restore to preserve FVarId monotonicity
    /// across TypeChecker instances that share caches.
    /// Part of #2382.
    pub(super) fn next_id(&self) -> u64 {
        self.next_id
    }

    /// Advance the next FVarId counter to at least `min_id`.
    ///
    /// Ensures that future FVarId allocations will not reuse IDs
    /// from a previous TypeChecker whose caches we're inheriting.
    /// Never decreases the counter.
    /// Part of #2382.
    pub(super) fn advance_next_id(&mut self, min_id: u64) {
        if min_id > self.next_id {
            self.next_id = min_id;
        }
    }

    /// Clear the FVarId reuse guard after external cache invalidation.
    ///
    /// `TypeChecker::local_context_mut()` clears all context-sensitive caches
    /// before returning `&mut LocalContext`, so explicit FVarIds that were
    /// previously popped become safe to reuse again at that boundary.
    #[cfg(test)]
    pub(crate) fn clear_reuse_history(&mut self) {
        self.used_ids.clear();
        self.low_cursor = 0;
    }

    /// Push a binding with a specific FVarId (used by elaborator)
    ///
    /// # Contract
    ///
    /// REQUIRES: `id` is not already in this context (`get(id).is_none()`)
    /// REQUIRES: `id` was never previously used and then popped in this
    ///   TypeChecker session, OR caches have been cleared (via
    ///   `local_context_mut()`). Reusing a popped FVarId without clearing
    ///   caches would cause stale cache hits (#1411 F2).
    ///
    /// ENSURES: `self.len() == old(self.len()) + 1` after call
    /// ENSURES: `self.get(id).is_some()` (id is now valid)
    /// ENSURES: `self.get(id).map(|d| &d.type_) == Some(&type_)`
    /// ENSURES: `self.get(id).and_then(|d| d.value.as_ref()).is_none()`
    pub fn push_with_id(&mut self, id: FVarId, name: Name, type_: Expr, bi: impl Into<BinderData>) {
        assert!(
            !self.index_by_id.contains_key(&id),
            "LocalContext::push_with_id saw active duplicate FVarId {id:?}"
        );
        assert!(
            self.used_ids.insert(id),
            "LocalContext::push_with_id reused popped FVarId {id:?} without clearing caches via TypeChecker::local_context_mut()"
        );
        self.index_by_id.insert(id, self.decls.len());
        self.decls.push(LocalDecl {
            id,
            name,
            type_,
            value: None,
            bi: bi.into(),
        });
        // Update next_id if needed to avoid collisions
        if id.0 >= self.next_id {
            self.next_id = id.0 + 1;
        }
    }

    /// Push a let binding with a specific FVarId.
    ///
    /// # Contract
    ///
    /// REQUIRES: `id` is not already in this context (`get(id).is_none()`)
    /// REQUIRES: `id` was never previously used and then popped in this
    ///   TypeChecker session, OR caches have been cleared (via
    ///   `local_context_mut()`). Reusing a popped FVarId without clearing
    ///   caches would cause stale cache hits (#1411 F2).
    /// ENSURES: `self.len() == old(self.len()) + 1` after call
    /// ENSURES: `self.get(id).is_some()` (id is now valid)
    /// ENSURES: `self.get(id).map(|d| &d.type_) == Some(&type_)`
    /// ENSURES: `self.get(id).and_then(|d| d.value.as_ref()) == Some(&value)`
    pub fn push_let_with_id(&mut self, id: FVarId, name: Name, type_: Expr, value: Expr) {
        assert!(
            !self.index_by_id.contains_key(&id),
            "LocalContext::push_let_with_id saw active duplicate FVarId {id:?}"
        );
        assert!(
            self.used_ids.insert(id),
            "LocalContext::push_let_with_id reused popped FVarId {id:?} without clearing caches via TypeChecker::local_context_mut()"
        );
        self.index_by_id.insert(id, self.decls.len());
        self.decls.push(LocalDecl {
            id,
            name,
            type_,
            value: Some(value),
            bi: BinderInfo::Default.into(),
        });
        if id.0 >= self.next_id {
            self.next_id = id.0 + 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_checked_add_u32_normal() {
        assert_eq!(checked_add_u32(10, 20, "test"), 30);
        assert_eq!(checked_add_u32(0, 0, "test"), 0);
        assert_eq!(checked_add_u32(u32::MAX - 1, 1, "test"), u32::MAX);
    }

    #[test]
    fn test_checked_add_u32_overflow_saturates() {
        assert_eq!(checked_add_u32(u32::MAX, 1, "test_overflow"), u32::MAX);
    }

    #[test]
    fn test_checked_add_u32_large_overflow_saturates() {
        assert_eq!(
            checked_add_u32(u32::MAX / 2 + 1, u32::MAX / 2 + 1, "test_large"),
            u32::MAX
        );
    }

    /// Regression: `push_low_local` must advance `next_id` past the id it
    /// hands out, otherwise a subsequent plain `push` while the low local is
    /// still active mints the same id and panics ("active duplicate FVarId").
    /// Observed via the elaborator unifier opening a Pi/Lam binder
    /// (`push_binder_local`) and then recursing into kernel `is_def_eq` →
    /// `infer_type_fast` → `push`.
    #[test]
    fn test_push_low_local_then_push_mints_distinct_id() {
        let mut ctx = LocalContext::new();
        let low = ctx.push_low_local(Name::anon(), Expr::type_(), BinderInfo::Default);
        assert_eq!(low, FVarId(0), "fresh context should hand out the low id 0");
        // Must not panic and must not collide with the active low local.
        let fresh = ctx.push(Name::anon(), Expr::type_(), BinderInfo::Default);
        assert_ne!(
            low, fresh,
            "plain push after push_low_local must mint a distinct FVarId"
        );
    }

    /// `push_low_local` must never *decrease* `next_id`: a counter already in
    /// the meta-tagged range (>= 1<<63, from registered meta-FVars) stays put
    /// while the returned id remains in the low range.
    #[test]
    fn test_push_low_local_does_not_decrease_next_id() {
        const META_TAG: u64 = 1u64 << 63;
        let mut ctx = LocalContext::new();
        ctx.push_with_id(
            FVarId(META_TAG),
            Name::anon(),
            Expr::type_(),
            BinderInfo::Default,
        );
        assert_eq!(ctx.next_id(), META_TAG + 1);
        let low = ctx.push_low_local(Name::anon(), Expr::type_(), BinderInfo::Default);
        assert!(low.0 < META_TAG, "returned id must stay in the low range");
        assert_eq!(
            ctx.next_id(),
            META_TAG + 1,
            "tagged-range next_id must not be decreased"
        );
    }
}
