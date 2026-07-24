// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pre-allocated builder pool for batch certificate verification.
//!
//! In batch mode, `CertBuilder` instances are created and destroyed for every
//! input. Each creation allocates fresh `Vec` and `HashMap` buffers. This
//! module provides [`BuilderPool`], which keeps a pool of pre-allocated
//! [`BuilderResources`] that are cleared (but not deallocated) between uses,
//! amortizing allocation cost across the batch.
//!
//! ## Usage
//!
//! ```text
//! let pool = BuilderPool::new(8);
//! let resources = pool.acquire(); // takes from pool or creates new
//! // ... use resources.nodes, resources.context, resources.fvar_types ...
//! drop(resources); // RAII: auto-returns to pool
//! ```

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use crate::expr::{Expr, FVarId};

use super::builder::BuildNode;

/// Pre-allocated buffers that a `CertBuilder` uses internally.
///
/// These are the heap-allocated containers that benefit from reuse:
/// clearing them retains capacity while resetting logical state.
#[derive(Debug)]
pub struct BuilderResources {
    /// Verified certificate nodes accumulated during building.
    pub(crate) nodes: Vec<BuildNode>,
    /// Typing context stack (binder types pushed/popped during building).
    pub(crate) context: Vec<Expr>,
    /// Free variable type registry.
    pub(crate) fvar_types: HashMap<FVarId, Expr>,
}

impl BuilderResources {
    /// Create a new `BuilderResources` with empty (but allocated) buffers.
    #[must_use]
    pub fn new() -> Self {
        Self {
            nodes: Vec::new(),
            context: Vec::new(),
            fvar_types: HashMap::new(),
        }
    }

    /// Clear all logical state but retain allocated memory.
    ///
    /// After reset, `nodes`, `context`, and `fvar_types` are empty but their
    /// backing storage is preserved for the next use.
    pub fn reset(&mut self) {
        self.nodes.clear();
        self.context.clear();
        self.fvar_types.clear();
    }
}

impl Default for BuilderResources {
    fn default() -> Self {
        Self::new()
    }
}

/// Usage statistics for the builder pool.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct PoolStats {
    /// Total number of `acquire()` calls.
    pub total_acquired: u64,
    /// Total number of releases (via `Drop` or explicit return).
    pub total_released: u64,
    /// Peak number of resources checked out simultaneously.
    pub peak_concurrent: usize,
    /// Number of acquires satisfied from the pool (reuse).
    pub pool_hits: u64,
    /// Number of acquires that had to create a fresh resource.
    pub pool_misses: u64,
}

/// Internal shared state behind `Arc<Mutex<_>>`.
#[derive(Debug)]
struct PoolInner {
    /// Available (idle) resources ready for checkout.
    available: Vec<BuilderResources>,
    /// Fixed pool capacity (max idle resources to keep).
    capacity: usize,
    /// Running statistics.
    stats: PoolStats,
    /// Current number of resources checked out.
    outstanding: usize,
}

/// A pool of pre-allocated [`BuilderResources`] for batch certificate building.
///
/// Thread-safe via `Arc<Mutex<_>>`. The pool keeps up to `pool_size` idle
/// resources. When a resource is acquired, it is removed from the pool (or a
/// new one is created if the pool is empty). When released (via [`PooledBuilder`]
/// drop), the resource is reset and returned to the pool if capacity allows.
#[derive(Debug, Clone)]
pub struct BuilderPool {
    inner: Arc<Mutex<PoolInner>>,
}

impl BuilderPool {
    /// Create a new pool that will keep up to `pool_size` idle resources.
    ///
    /// Resources are created lazily on first `acquire()`, not upfront.
    #[must_use]
    pub fn new(pool_size: usize) -> Self {
        Self {
            inner: Arc::new(Mutex::new(PoolInner {
                available: Vec::with_capacity(pool_size),
                capacity: pool_size,
                stats: PoolStats::default(),
                outstanding: 0,
            })),
        }
    }

    /// Acquire a builder resource from the pool.
    ///
    /// If idle resources are available, one is returned (pool hit).
    /// Otherwise a fresh `BuilderResources` is created (pool miss).
    ///
    /// The returned [`PooledBuilder`] auto-releases back to this pool on drop.
    #[must_use]
    pub fn acquire(&self) -> PooledBuilder {
        let resources = {
            let mut inner = self
                .inner
                .lock()
                .expect("invariant: builder pool mutex not poisoned");

            inner.stats.total_acquired += 1;
            inner.outstanding += 1;
            if inner.outstanding > inner.stats.peak_concurrent {
                inner.stats.peak_concurrent = inner.outstanding;
            }

            if let Some(res) = inner.available.pop() {
                inner.stats.pool_hits += 1;
                res
            } else {
                inner.stats.pool_misses += 1;
                BuilderResources::new()
            }
        };

        PooledBuilder {
            resources: Some(resources),
            pool: Arc::clone(&self.inner),
        }
    }

    /// Return a resource to the pool manually, bypassing RAII.
    ///
    /// Prefer letting [`PooledBuilder`] drop naturally. This is available for
    /// callers who need explicit lifetime control.
    pub fn release(&self, mut resources: BuilderResources) {
        resources.reset();
        let mut inner = self
            .inner
            .lock()
            .expect("invariant: builder pool mutex not poisoned");

        inner.stats.total_released += 1;
        if inner.outstanding > 0 {
            inner.outstanding -= 1;
        }
        if inner.available.len() < inner.capacity {
            inner.available.push(resources);
        }
        // If at capacity, resource is dropped (deallocated).
    }

    /// Maximum number of idle resources the pool will keep.
    #[must_use]
    pub fn pool_size(&self) -> usize {
        let inner = self
            .inner
            .lock()
            .expect("invariant: builder pool mutex not poisoned");
        inner.capacity
    }

    /// Number of resources currently idle in the pool.
    #[must_use]
    pub fn available(&self) -> usize {
        let inner = self
            .inner
            .lock()
            .expect("invariant: builder pool mutex not poisoned");
        inner.available.len()
    }

    /// Snapshot of pool usage statistics.
    #[must_use]
    pub fn stats(&self) -> PoolStats {
        let inner = self
            .inner
            .lock()
            .expect("invariant: builder pool mutex not poisoned");
        inner.stats.clone()
    }
}

/// RAII wrapper that auto-returns [`BuilderResources`] to the pool on drop.
///
/// Access the underlying resources via `Deref`/`DerefMut` or the explicit
/// `resources()` / `resources_mut()` accessors.
#[derive(Debug)]
pub struct PooledBuilder {
    /// `Some` while checked out, `None` after release/drop.
    resources: Option<BuilderResources>,
    /// Shared reference to the owning pool for auto-return.
    pool: Arc<Mutex<PoolInner>>,
}

impl PooledBuilder {
    /// Borrow the underlying resources.
    #[must_use]
    pub fn resources(&self) -> &BuilderResources {
        self.resources
            .as_ref()
            .expect("invariant: PooledBuilder accessed after release")
    }

    /// Mutably borrow the underlying resources.
    pub fn resources_mut(&mut self) -> &mut BuilderResources {
        self.resources
            .as_mut()
            .expect("invariant: PooledBuilder accessed after release")
    }

    /// Consume this wrapper and return the raw resources without
    /// returning them to the pool. The caller takes ownership.
    #[must_use]
    pub fn take(mut self) -> BuilderResources {
        let resources = self
            .resources
            .take()
            .expect("invariant: PooledBuilder::take called after release");
        // Decrement outstanding without returning to pool.
        if let Ok(mut inner) = self.pool.lock() {
            if inner.outstanding > 0 {
                inner.outstanding -= 1;
            }
        }
        resources
    }
}

impl std::ops::Deref for PooledBuilder {
    type Target = BuilderResources;

    fn deref(&self) -> &Self::Target {
        self.resources()
    }
}

impl std::ops::DerefMut for PooledBuilder {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.resources_mut()
    }
}

impl Drop for PooledBuilder {
    fn drop(&mut self) {
        if let Some(mut resources) = self.resources.take() {
            resources.reset();
            if let Ok(mut inner) = self.pool.lock() {
                inner.stats.total_released += 1;
                if inner.outstanding > 0 {
                    inner.outstanding -= 1;
                }
                if inner.available.len() < inner.capacity {
                    inner.available.push(resources);
                }
            }
            // If lock is poisoned during drop, silently discard resources.
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_builder_resources_new_is_empty() {
        let res = BuilderResources::new();
        assert!(res.nodes.is_empty());
        assert!(res.context.is_empty());
        assert!(res.fvar_types.is_empty());
    }

    #[test]
    fn test_builder_resources_reset_clears_but_retains_capacity() {
        let mut res = BuilderResources::new();
        // Populate to force allocation.
        for _ in 0..100 {
            res.nodes.push(BuildNode {
                cert: crate::cert::ProofCert::Sort {
                    level: crate::level::Level::zero(),
                },
                computed_type: crate::expr::Expr::from_kind(crate::expr::ExprKind::Sort(
                    crate::level::Level::zero(),
                )),
            });
        }
        let cap_before = res.nodes.capacity();
        assert!(cap_before >= 100);

        res.reset();
        assert!(res.nodes.is_empty());
        assert_eq!(res.nodes.capacity(), cap_before);
    }

    #[test]
    fn test_pool_new_starts_empty() {
        let pool = BuilderPool::new(4);
        assert_eq!(pool.pool_size(), 4);
        assert_eq!(pool.available(), 0);
        let stats = pool.stats();
        assert_eq!(stats.total_acquired, 0);
        assert_eq!(stats.total_released, 0);
        assert_eq!(stats.peak_concurrent, 0);
    }

    #[test]
    fn test_pool_acquire_release_cycle() {
        let pool = BuilderPool::new(4);

        // First acquire: pool miss (lazy creation).
        let builder = pool.acquire();
        assert_eq!(pool.available(), 0);
        let stats = pool.stats();
        assert_eq!(stats.total_acquired, 1);
        assert_eq!(stats.pool_misses, 1);
        assert_eq!(stats.pool_hits, 0);

        // Drop returns to pool.
        drop(builder);
        assert_eq!(pool.available(), 1);
        let stats = pool.stats();
        assert_eq!(stats.total_released, 1);

        // Second acquire: pool hit (reuse).
        let builder2 = pool.acquire();
        assert_eq!(pool.available(), 0);
        let stats = pool.stats();
        assert_eq!(stats.total_acquired, 2);
        assert_eq!(stats.pool_hits, 1);
        assert_eq!(stats.pool_misses, 1);
        drop(builder2);
    }

    #[test]
    fn test_pool_exhaustion_creates_new() {
        let pool = BuilderPool::new(2);

        // Acquire more than pool capacity.
        let b1 = pool.acquire();
        let b2 = pool.acquire();
        let b3 = pool.acquire();

        let stats = pool.stats();
        assert_eq!(stats.total_acquired, 3);
        assert_eq!(stats.pool_misses, 3);
        assert_eq!(stats.peak_concurrent, 3);

        // Release all three, but pool only keeps 2.
        drop(b1);
        drop(b2);
        drop(b3);
        assert_eq!(pool.available(), 2);
        let stats = pool.stats();
        assert_eq!(stats.total_released, 3);
    }

    #[test]
    fn test_pool_stats_peak_concurrent() {
        let pool = BuilderPool::new(8);

        let b1 = pool.acquire();
        let b2 = pool.acquire();
        let b3 = pool.acquire();
        assert_eq!(pool.stats().peak_concurrent, 3);

        drop(b1);
        // Peak stays at 3 even after releasing one.
        assert_eq!(pool.stats().peak_concurrent, 3);

        let _b4 = pool.acquire();
        let _b5 = pool.acquire();
        let _b6 = pool.acquire();
        // Now 5 outstanding (b2, b3, b4, b5, b6).
        assert_eq!(pool.stats().peak_concurrent, 5);
    }

    #[test]
    fn test_pooled_builder_raii_drop() {
        let pool = BuilderPool::new(4);

        {
            let _b = pool.acquire();
            assert_eq!(pool.available(), 0);
        }
        // After scope exit, resource returned.
        assert_eq!(pool.available(), 1);
        assert_eq!(pool.stats().total_released, 1);
    }

    #[test]
    fn test_pooled_builder_deref() {
        let pool = BuilderPool::new(4);
        let mut builder = pool.acquire();

        // Deref gives access to nodes.
        assert!(builder.nodes.is_empty());
        builder.nodes.push(BuildNode {
            cert: crate::cert::ProofCert::Sort {
                level: crate::level::Level::zero(),
            },
            computed_type: crate::expr::Expr::from_kind(crate::expr::ExprKind::Sort(
                crate::level::Level::zero(),
            )),
        });
        assert_eq!(builder.nodes.len(), 1);
    }

    #[test]
    fn test_pooled_builder_take_does_not_return_to_pool() {
        let pool = BuilderPool::new(4);

        let builder = pool.acquire();
        let _resources = builder.take();

        // take() consumed the wrapper without returning to pool.
        assert_eq!(pool.available(), 0);
        assert_eq!(pool.stats().total_released, 0);
    }

    #[test]
    fn test_pool_explicit_release() {
        let pool = BuilderPool::new(4);

        let builder = pool.acquire();
        let resources = builder.take();
        assert_eq!(pool.available(), 0);

        pool.release(resources);
        assert_eq!(pool.available(), 1);
        assert_eq!(pool.stats().total_released, 1);
    }

    #[test]
    fn test_pool_concurrent_stats_accuracy() {
        let pool = BuilderPool::new(16);
        let mut builders = Vec::new();

        // Acquire 10 concurrently.
        for _ in 0..10 {
            builders.push(pool.acquire());
        }
        let stats = pool.stats();
        assert_eq!(stats.total_acquired, 10);
        assert_eq!(stats.pool_misses, 10);
        assert_eq!(stats.peak_concurrent, 10);

        // Release 5, then acquire 3 more.
        for _ in 0..5 {
            builders.pop();
        }
        assert_eq!(pool.available(), 5);

        for _ in 0..3 {
            builders.push(pool.acquire());
        }
        let stats = pool.stats();
        assert_eq!(stats.total_acquired, 13);
        assert_eq!(stats.pool_hits, 3);
        assert_eq!(stats.peak_concurrent, 10); // Still 10 from earlier.
    }

    #[test]
    fn test_builder_resources_default() {
        let res = BuilderResources::default();
        assert!(res.nodes.is_empty());
        assert!(res.context.is_empty());
        assert!(res.fvar_types.is_empty());
    }

    #[test]
    fn test_pool_zero_capacity() {
        let pool = BuilderPool::new(0);
        assert_eq!(pool.pool_size(), 0);

        let b = pool.acquire();
        drop(b);
        // With zero capacity, nothing is kept.
        assert_eq!(pool.available(), 0);
        assert_eq!(pool.stats().total_released, 1);
    }
}
