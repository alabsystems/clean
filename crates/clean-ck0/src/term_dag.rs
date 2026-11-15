//! Identity keys and scoped hash-consing. A key owns its node: an allocation
//! address cannot be reused while a cache entry names it. Structural equality
//! remains an exact check on hash collisions; no hash grants equality.
use crate::term::{Term, TermKind};
use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::sync::{Arc, Weak};

#[derive(Clone, Debug)]
pub(crate) struct NodeKey(pub(crate) Term);
impl PartialEq for NodeKey {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0.kind, &other.0.kind)
    }
}
impl Eq for NodeKey {}
impl Hash for NodeKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        std::ptr::hash(Arc::as_ptr(&self.0.kind), state);
    }
}

type Pool = HashMap<u64, Vec<Weak<TermKind>>>;
thread_local! {
    static POOL: RefCell<Pool> = RefCell::new(HashMap::new());
    static DEPTH: Cell<u32> = const { Cell::new(0) };
    static SINCE_SWEEP: Cell<usize> = const { Cell::new(0) };
    static SWEEP_EVERY: Cell<usize> = const { Cell::new(4096) };
}

/// Both validation and a decision keep their producer's shared nodes shared.
/// Nested scopes reuse the pool; no weak entry survives the outer scope.
pub(crate) struct DagScope(std::marker::PhantomData<std::rc::Rc<()>>);
impl DagScope {
    pub(crate) fn enter() -> Self {
        DEPTH.with(|depth| {
            if depth.get() == 0 {
                POOL.with(|pool| pool.borrow_mut().clear());
                SINCE_SWEEP.with(|count| count.set(0));
                SWEEP_EVERY.with(|count| count.set(4096));
            }
            depth.set(depth.get().saturating_add(1));
        });
        Self(std::marker::PhantomData)
    }
}
impl Drop for DagScope {
    fn drop(&mut self) {
        DEPTH.with(|depth| {
            depth.set(depth.get().saturating_sub(1));
            if depth.get() == 0 {
                POOL.with(|pool| pool.borrow_mut().clear());
                SINCE_SWEEP.with(|count| count.set(0));
                SWEEP_EVERY.with(|count| count.set(4096));
            }
        });
    }
}

pub(crate) fn intern(kind: TermKind, hash: u64) -> Arc<TermKind> {
    if DEPTH.with(Cell::get) == 0 {
        return Arc::new(kind);
    }
    POOL.with(|pool| {
        let mut pool = pool.borrow_mut();
        // Keep a replay-wide pool without retaining the dead control blocks
        // of every temporary reduct. A sweep is amortized over at least as
        // many constructions as the previous sweep's live hash buckets.
        let calls = SINCE_SWEEP.with(|count| {
            let calls = count.get().saturating_add(1);
            count.set(calls);
            calls
        });
        if calls >= SWEEP_EVERY.with(Cell::get) {
            pool.retain(|_, bucket| {
                bucket.retain(|node| node.strong_count() != 0);
                !bucket.is_empty()
            });
            SINCE_SWEEP.with(|count| count.set(0));
            SWEEP_EVERY.with(|count| count.set(pool.len().max(4096)));
        }
        let bucket = pool.entry(hash).or_default();
        let mut found = None;
        bucket.retain(|weak| {
            let Some(node) = weak.upgrade() else {
                return false;
            };
            if found.is_none() && crate::term_ops::kind_eq(&kind, &node) {
                found = Some(node);
            }
            true
        });
        if let Some(node) = found {
            return node;
        }
        let node = Arc::new(kind);
        bucket.push(Arc::downgrade(&node));
        node
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn replay_pool_collects_dead_temporaries_before_the_scope_ends() {
        let _scope = DagScope::enter();
        for index in 0..50_000 {
            drop(Term::bvar(index));
        }
        assert!(POOL.with(|pool| pool.borrow().len()) <= 8192);
    }
}
