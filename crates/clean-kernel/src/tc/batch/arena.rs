// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! VerificationArena: zero-copy arena for batch verification.

use super::verifier::BatchVerifier;
use super::{compute_stats_from_slice, BatchCheckResult, BatchCheckStats};
use crate::expr::Expr;

/// Zero-copy arena for batch verification
///
/// Pre-allocates storage for expressions and results, enabling efficient
/// batch verification without per-expression allocation.
pub struct VerificationArena {
    /// Input expressions
    exprs: Vec<Expr>,
    /// Results (None = not yet verified)
    results: Vec<Option<BatchCheckResult>>,
    /// Wall-clock time for last verify_all call (None = not verified)
    last_wall_time_ns: Option<u64>,
}

impl VerificationArena {
    /// Create arena with pre-allocated capacity
    ///
    /// # Contract
    ///
    /// ENSURES: `result.is_empty() == true`
    /// ENSURES: `result.len() == 0`
    /// ENSURES: Arena has pre-allocated capacity for `capacity` expressions
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            exprs: Vec::with_capacity(capacity),
            results: Vec::with_capacity(capacity),
            last_wall_time_ns: None,
        }
    }

    /// Create empty arena
    ///
    /// # Contract
    ///
    /// ENSURES: `result.is_empty() == true`
    /// ENSURES: `result.len() == 0`
    pub fn new() -> Self {
        Self {
            exprs: Vec::new(),
            results: Vec::new(),
            last_wall_time_ns: None,
        }
    }

    /// Add an expression, return its slot index
    ///
    /// Note: Invalidates any previously computed wall-clock time since the
    /// arena now contains unverified expressions.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.len() < u32::MAX as usize` (index must fit in u32)
    /// ENSURES: `self.len() == old(self.len()) + 1`
    /// ENSURES: `result == old(self.len()) as u32`
    /// ENSURES: `self.get_expr(result) == Some(&expr)`
    /// ENSURES: `self.get_result(result).is_none()` (not yet verified)
    pub fn push(&mut self, expr: Expr) -> u32 {
        debug_assert!(
            self.exprs.len() < u32::MAX as usize,
            "BatchArena overflow: len exceeds u32::MAX"
        );
        let idx = self.exprs.len() as u32;
        self.exprs.push(expr);
        self.results.push(None);
        self.last_wall_time_ns = None; // Invalidate stale timing
        idx
    }

    /// Add multiple expressions, return first slot index
    ///
    /// Note: Invalidates any previously computed wall-clock time since the
    /// arena now contains unverified expressions.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self.len() + exprs.count() <= u32::MAX as usize` (indices must fit in u32)
    /// ENSURES: `result == old(self.len()) as u32`
    /// ENSURES: Expressions added at consecutive indices starting from `result`
    pub fn push_many(&mut self, exprs: impl IntoIterator<Item = Expr>) -> u32 {
        debug_assert!(
            self.exprs.len() < u32::MAX as usize,
            "BatchArena overflow: len exceeds u32::MAX"
        );
        let first = self.exprs.len() as u32;
        for expr in exprs {
            self.exprs.push(expr);
            self.results.push(None);
        }
        self.last_wall_time_ns = None; // Invalidate stale timing
        first
    }

    /// Number of expressions in the arena
    ///
    /// # Contract
    ///
    /// ENSURES: `result == 0` iff `is_empty() == true`
    pub fn len(&self) -> usize {
        self.exprs.len()
    }

    /// Check if arena is empty
    ///
    /// # Contract
    ///
    /// ENSURES: `result == true` iff `len() == 0`
    pub fn is_empty(&self) -> bool {
        self.exprs.is_empty()
    }

    /// Verify all expressions in the arena
    ///
    /// # Contract
    ///
    /// ENSURES: After call, `get_result(i).is_some()` for all `i < len()`
    /// ENSURES: `stats().wall_time_ns > 0`
    pub fn verify_all(&mut self, verifier: &BatchVerifier) {
        let wall_start = std::time::Instant::now();
        let results = verifier.batch_check(&self.exprs);
        self.last_wall_time_ns = Some(wall_start.elapsed().as_nanos() as u64);
        self.results = results.into_iter().map(Some).collect();
    }

    /// Get result for a slot (returns None if not verified)
    ///
    /// # Contract
    ///
    /// ENSURES: `None` if `idx >= len()` or slot not verified
    /// ENSURES: `Some(result)` if slot exists and was verified
    pub fn get_result(&self, idx: u32) -> Option<&BatchCheckResult> {
        self.results.get(idx as usize).and_then(|r| r.as_ref())
    }

    /// Get expression at a slot
    ///
    /// # Contract
    ///
    /// ENSURES: `None` if `idx >= len()`
    /// ENSURES: `Some(&expr)` if slot exists
    pub fn get_expr(&self, idx: u32) -> Option<&Expr> {
        self.exprs.get(idx as usize)
    }

    /// Get inferred type for a slot (returns None if invalid or not verified)
    ///
    /// # Contract
    ///
    /// ENSURES: `None` if slot not verified or expression is invalid
    /// ENSURES: `Some(&ty)` if slot was verified and expression is well-typed
    pub fn get_type(&self, idx: u32) -> Option<&Expr> {
        self.get_result(idx).and_then(|r| r.inferred_type.as_ref())
    }

    /// Check if slot is valid (well-typed)
    ///
    /// # Contract
    ///
    /// ENSURES: `false` if slot not verified or expression is invalid
    /// ENSURES: `true` iff slot was verified and expression is well-typed
    pub fn is_valid(&self, idx: u32) -> bool {
        self.get_result(idx).map(|r| r.valid).unwrap_or(false)
    }

    /// Iterate over valid (expr, type) pairs
    ///
    /// # Contract
    ///
    /// ENSURES: Yields only expressions that are well-typed
    /// ENSURES: Each pair `(expr, ty)` satisfies: expr has inferred type ty
    pub fn valid_pairs(&self) -> impl Iterator<Item = (&Expr, &Expr)> {
        self.exprs
            .iter()
            .zip(self.results.iter())
            .filter_map(|(e, r)| {
                r.as_ref()
                    .and_then(|r| r.inferred_type.as_ref().map(|ty| (e, ty)))
            })
    }

    /// Get indices of valid expressions
    ///
    /// # Contract
    ///
    /// ENSURES: All indices in result are in range `[0, len())`
    /// ENSURES: `is_valid(i) == true` for all `i` in result
    /// ENSURES: Indices are in ascending order
    pub fn valid_indices(&self) -> Vec<u32> {
        self.results
            .iter()
            .enumerate()
            .filter_map(|(i, r)| r.as_ref().and_then(|r| r.valid.then_some(i as u32)))
            .collect()
    }

    /// Clear the arena for reuse
    ///
    /// # Contract
    ///
    /// ENSURES: `self.is_empty() == true`
    /// ENSURES: `self.len() == 0`
    pub fn clear(&mut self) {
        self.exprs.clear();
        self.results.clear();
        self.last_wall_time_ns = None;
    }

    /// Get statistics for verified expressions
    ///
    /// Uses actual wall-clock time measured during `verify_all()`.
    /// Returns 0 if `verify_all()` was not called since the last mutation.
    ///
    /// # Contract
    ///
    /// ENSURES: `result.total` equals number of verified results
    /// ENSURES: `result.valid + result.invalid == result.total`
    pub fn stats(&self) -> BatchCheckStats {
        let verified: Vec<_> = self.results.iter().filter_map(|r| r.as_ref()).collect();
        let wall_time_ns = self.last_wall_time_ns.unwrap_or(0);
        compute_stats_from_slice(&verified, wall_time_ns)
    }
}

impl Default for VerificationArena {
    /// Create a default (empty) verification arena
    ///
    /// # Contract
    ///
    /// ENSURES: `result.is_empty() == true`
    fn default() -> Self {
        Self::new()
    }
}
