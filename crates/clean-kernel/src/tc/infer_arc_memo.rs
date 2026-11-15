// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constant-size identity for an Arc inference node in an active local scope.

use super::TypeChecker;
use crate::cert::ProofCert;
use crate::expr::{Expr, FVarId};
// `hashbrown`'s default (foldhash) hasher rather than `std`'s SipHash: the
// memo is only probed, filled, and cleared or retired by key — never iterated
// — so the hash function decides nothing it returns. Its keys are node
// addresses and binder ids no input chooses. Measured 2026-09-30 (macOS
// `sample`, the concurrent `.olean.private` checks of Mathlib `Order/Basic`'s
// import header), SipHash on these tables was several percent of the checks.
use hashbrown::HashMap;
use std::sync::Arc;

/// A stable node, inference mode, and exact active binder prefix.
///
/// Within one checker's memo lifetime declarations are immutable, appended to
/// a stack, and never reissued after pop. Consequently the last active FVarId
/// identifies the entire active prefix, including after nested scopes restore
/// it. Depth alone aliases sibling scopes; next_id needlessly loses reuse when
/// returning to a prefix. Neither a context hash nor a new allocation is needed.
///
/// Keep emptiness separate from the ID: FVar0 is valid, not an empty sentinel.
/// Storing that discriminant beside infer_only avoids a per-entry Option<FVarId>
/// layout expansion on 64-bit targets. The Arc itself is still pinned by the
/// memo value; this key does not own the expression or extend a variable's scope.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) struct InferArcMemoKey {
    node: usize,
    last: FVarId,
    infer_only: bool,
    scope_tag: InferArcMemoScopeTag,
}

impl InferArcMemoKey {
    pub(super) fn new(arc: &Arc<Expr>, infer_only: bool, last: Option<FVarId>) -> Self {
        Self {
            node: Arc::as_ptr(arc) as usize,
            last: last.unwrap_or(FVarId::new(0)),
            infer_only,
            scope_tag: if last.is_some() {
                InferArcMemoScopeTag::Prefix
            } else {
                InferArcMemoScopeTag::Empty
            },
        }
    }

    #[cfg(not(debug_assertions))]
    pub(super) fn independent(arc: &Arc<Expr>, infer_only: bool) -> Self {
        Self {
            node: Arc::as_ptr(arc) as usize,
            last: FVarId::new(0),
            infer_only,
            scope_tag: InferArcMemoScopeTag::Independent,
        }
    }

    fn scope(self) -> InferArcMemoScope {
        match self.scope_tag {
            InferArcMemoScopeTag::Empty => InferArcMemoScope::Empty,
            InferArcMemoScopeTag::Prefix => InferArcMemoScope::Prefix(self.last),
            #[cfg(not(debug_assertions))]
            InferArcMemoScopeTag::Independent => InferArcMemoScope::Independent,
        }
    }

    fn node(self) -> InferArcMemoNode {
        InferArcMemoNode {
            address: self.node,
            infer_only: self.infer_only,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum InferArcMemoScopeTag {
    Empty,
    Prefix,
    #[cfg(not(debug_assertions))]
    Independent,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum InferArcMemoScope {
    Empty,
    Prefix(FVarId),
    #[cfg(not(debug_assertions))]
    Independent,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct InferArcMemoNode {
    address: usize,
    infer_only: bool,
}

// Retain the certificate allocation, not just its shallow value: App children
// must receive the same certified node on a hit, including its boxed type fields.
type InferArcMemoValue = (Arc<Expr>, Expr, Option<Arc<ProofCert>>);
type InferArcMemoBucket = HashMap<InferArcMemoNode, InferArcMemoValue>;

#[derive(Default)]
struct InferArcMemoWindow {
    buckets: HashMap<InferArcMemoScope, InferArcMemoBucket>,
    len: usize,
}

impl InferArcMemoWindow {
    fn get(&self, key: &InferArcMemoKey) -> Option<&InferArcMemoValue> {
        self.buckets.get(&key.scope())?.get(&key.node())
    }

    fn get_mut(&mut self, key: &InferArcMemoKey) -> Option<&mut InferArcMemoValue> {
        self.buckets.get_mut(&key.scope())?.get_mut(&key.node())
    }

    fn retire_scope(&mut self, id: FVarId) {
        if let Some(bucket) = self.buckets.remove(&InferArcMemoScope::Prefix(id)) {
            self.len -= bucket.len();
        }
    }

    fn clear(&mut self) {
        self.buckets.clear();
        self.len = 0;
    }
}

/// The same exact memo keys, grouped by active prefix in two admission windows.
///
/// A popped last FVarId can never be issued again within this memo's lifetime.
/// Its bucket therefore has no future valid hit. Dropping that bucket releases
/// raw certificate versions before the enclosing binder's rebinding traversal;
/// buckets for still-active prefixes remain available after nested scopes pop.
/// No expression analysis, cross-prefix reuse, or other cache invalidation is
/// involved. Retirement visits only the two removed buckets, never the whole memo.
///
/// A completed NEW admission rotates once the current window reaches ceil(cap/2)
/// or the aggregate reaches cap: drop the previous window and demote the current
/// one. Unlike two independently capped caches, the aggregate never exceeds cap.
/// Hits and certificate upgrades do not rotate or promote entries. This policy
/// admits a sliding working set rather than freezing the first cap nodes, but can
/// evict an older hot node; it is not an LRU policy or a performance guarantee.
#[derive(Default)]
pub(super) struct InferArcMemo {
    current: InferArcMemoWindow,
    previous: InferArcMemoWindow,
}

impl InferArcMemo {
    pub(super) fn len(&self) -> usize {
        self.current.len + self.previous.len
    }

    pub(super) fn get(&self, key: &InferArcMemoKey) -> Option<&InferArcMemoValue> {
        // One probe of kernel work (`crate::work_meter`).
        crate::work_meter::charge(crate::work_meter::Walk::Probe, 1);
        self.current.get(key).or_else(|| self.previous.get(key))
    }

    pub(super) fn get_mut(&mut self, key: &InferArcMemoKey) -> Option<&mut InferArcMemoValue> {
        crate::work_meter::charge(crate::work_meter::Walk::Probe, 1);
        if let Some(entry) = self.current.get_mut(key) {
            return Some(entry);
        }
        self.previous.get_mut(key)
    }

    /// Admission occurs only after inference succeeds. At a fixed capacity, a
    /// recursively supplied entry in either window wins before value creation
    /// or eviction; fast inference must never downgrade its genuine certificate.
    pub(super) fn insert_if_absent_with(
        &mut self,
        key: InferArcMemoKey,
        capacity: usize,
        value: impl FnOnce() -> InferArcMemoValue,
    ) {
        // The checker setter normally clears on capacity reduction. Keep this
        // private explicit-cap API bounded even if a caller supplies a smaller
        // cap directly; policy reset is distinct from normal window rotation.
        let window_capacity = capacity / 2 + capacity % 2;
        if self.len() > capacity
            || self.current.len > window_capacity
            || self.previous.len > window_capacity
        {
            self.clear();
        }
        if self.get(&key).is_some() || capacity == 0 {
            return;
        }
        let value = value();
        if capacity == 1 {
            // Demoting a single entry then inserting would exceed this cap.
            #[cfg(feature = "inference-stats")]
            if !self.is_empty() {
                super::reduction_stats::inference::record_memo_rotation(self.len());
            }
            self.clear();
        } else if self.current.len >= window_capacity || self.len() >= capacity {
            #[cfg(feature = "inference-stats")]
            super::reduction_stats::inference::record_memo_rotation(self.previous.len);
            self.previous = std::mem::take(&mut self.current);
        }
        self.current
            .buckets
            .entry(key.scope())
            .or_default()
            .insert(key.node(), value);
        self.current.len += 1;
        #[cfg(feature = "inference-stats")]
        super::reduction_stats::inference::record_memo_entries(self.len());
    }

    pub(super) fn retire_scope(&mut self, id: FVarId) {
        self.current.retire_scope(id);
        self.previous.retire_scope(id);
    }

    pub(super) fn clear(&mut self) {
        self.current.clear();
        self.previous.clear();
    }

    #[cfg(any(test, feature = "inference-stats"))]
    pub(super) fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[cfg(test)]
    pub(super) fn contains_key(&self, key: &InferArcMemoKey) -> bool {
        self.get(key).is_some()
    }
}

#[cfg(test)]
impl std::ops::Index<&InferArcMemoKey> for InferArcMemo {
    type Output = InferArcMemoValue;

    fn index(&self, key: &InferArcMemoKey) -> &Self::Output {
        self.get(key).expect("existing inference memo entry")
    }
}

impl TypeChecker<'_> {
    /// Shared by fast and certificate inference; read only the last stack slot.
    pub(super) fn infer_arc_memo_key(&self, arc: &Arc<Expr>) -> InferArcMemoKey {
        let last = self.ctx.borrow().iter().next_back().map(|decl| decl.id);
        InferArcMemoKey::new(arc, self.infer_only.get(), last)
    }
}

#[cfg(test)]
#[path = "infer_arc_memo_retirement_tests.rs"]
mod retirement_tests;

#[cfg(test)]
#[path = "infer_arc_certificate_tests.rs"]
mod certificate_tests;

#[cfg(test)]
#[path = "infer_arc_memo_window_tests.rs"]
mod window_tests;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BinderInfo, Environment, Name, TypeError};

    #[test]
    fn key_distinguishes_empty_zero_id_modes_and_node_identity() {
        let first = Arc::new(Expr::prop());
        let second = Arc::new(Expr::prop());
        let empty = InferArcMemoKey::new(&first, true, None);
        assert_ne!(
            empty,
            InferArcMemoKey::new(&first, true, Some(FVarId::new(0)))
        );
        assert_ne!(empty, InferArcMemoKey::new(&first, false, None));
        assert_ne!(empty, InferArcMemoKey::new(&second, true, None));
        #[cfg(target_pointer_width = "64")]
        assert!(size_of::<InferArcMemoKey>() <= size_of::<(usize, bool, usize)>());
    }

    #[test]
    fn active_prefix_restores_after_pop_and_truncate_but_not_sibling_push() {
        let env = Environment::new();
        let checker = TypeChecker::new(&env);
        let node = Arc::new(Expr::prop());
        let empty = checker.infer_arc_memo_key(&node);
        let outer = checker.ctx_push(Name::anon(), Expr::prop(), BinderInfo::Default);
        let prefix = checker.infer_arc_memo_key(&node);
        assert_ne!(empty, prefix);
        checker.ctx_push_let(Name::anon(), Expr::type_(), Expr::prop());
        let nested = checker.infer_arc_memo_key(&node);
        checker.pop_binder_local();
        assert_eq!(prefix, checker.infer_arc_memo_key(&node));
        checker.push_binder_local(Name::anon(), Expr::prop(), BinderInfo::Default);
        assert_ne!(nested, checker.infer_arc_memo_key(&node));
        checker.ctx_push(Name::anon(), Expr::type_(), BinderInfo::Default);
        checker.ctx_truncate_to(1);
        assert_eq!(prefix, checker.infer_arc_memo_key(&node));
        checker.ctx_pop();
        assert_eq!(empty, checker.infer_arc_memo_key(&node));
        let sibling = checker.ctx_push(Name::anon(), Expr::prop(), BinderInfo::Default);
        assert_ne!(outer, sibling);
        assert_ne!(prefix, checker.infer_arc_memo_key(&node));
    }

    #[test]
    fn certificate_memo_preserves_restored_prefix_entries_and_rejects_retired_fvar() {
        let env = Environment::new();
        let checker = TypeChecker::new(&env);
        let outer = checker.ctx_push(Name::anon(), Expr::prop(), BinderInfo::Default);
        let shared = Arc::new(Expr::fvar(outer));
        // Observe actual child-cache entries inside an enclosing test frame.
        // Public-entry regressions independently exercise natural recursion.
        checker.infer_memo_depth.set(1);
        checker.cert_retained.set(true);
        let prefix = checker.infer_arc_memo_key(&shared);
        assert_eq!(
            checker
                .infer_type_with_cert_arc(&shared)
                .expect("outer scope")
                .0,
            Expr::prop()
        );
        checker.ctx_push(Name::anon(), Expr::type_(), BinderInfo::Default);
        assert_eq!(
            checker
                .infer_type_with_cert_arc(&shared)
                .expect("nested scope")
                .0,
            Expr::prop()
        );
        assert_eq!(checker.infer_arc_memo.borrow().len(), 2);
        assert!(checker.infer_arc_memo.borrow()[&prefix].2.is_some());
        checker.ctx_pop();
        assert_eq!(prefix, checker.infer_arc_memo_key(&shared));
        assert!(checker.infer_arc_memo.borrow().contains_key(&prefix));
        assert_eq!(
            checker
                .infer_type_with_cert_arc(&shared)
                .expect("restored scope")
                .0,
            Expr::prop()
        );
        assert_eq!(checker.infer_arc_memo.borrow().len(), 1);
        checker.ctx_pop();
        checker.ctx_push(Name::anon(), Expr::prop(), BinderInfo::Default);
        assert!(
            matches!(checker.infer_type_with_cert_arc(&shared), Err(TypeError::UnknownFVar(id)) if id == outer)
        );
        assert_eq!(
            checker.infer_arc_memo.borrow().len(),
            0,
            "only the two actually retired prefix buckets are removed"
        );
        checker.infer_memo_depth.set(0);
        checker.cert_retained.set(false);
        checker.infer_arc_memo.borrow_mut().clear();
    }
}
