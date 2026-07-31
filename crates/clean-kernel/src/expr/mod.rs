// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Expression representation
//!
//! The core expression type used throughout clean.
//! Uses de Bruijn indices for bound variables.

mod bignat_ops;
mod constructors;
mod display;
mod drop;
mod kind;
mod meta;
mod sorry;
mod subst;
mod trust;
mod types;
pub mod visitor;

pub use drop::iterative_drop;
pub(crate) use kind::ek;
pub use kind::{ExprKind, ZFCSetExpr};
#[cfg(kani)]
pub(crate) use meta::KaniHasher;
pub(crate) use meta::{hash_to_u64, level_has_mvar, mix_hash, ExprMeta};
pub use types::*;
pub use visitor::{ExprFolder, ExprFolderOpt, ExprVisitor};

use serde::{Deserialize, Serialize};

// These imports are used by tests.rs (included via include! below) through `use super::*`.
#[cfg(test)]
use crate::level::Level;
#[cfg(test)]
use crate::name::Name;
#[cfg(test)]
use std::sync::Arc;

/// Minimum stack space to reserve before recursive calls (256 KB).
///
/// Type-checker recursion can perform a level substitution, WHNF reduction, and
/// certificate construction before reaching the next `stack_safe` boundary.
/// Those operations collectively need substantially more than 32 KB in debug
/// builds.  A 32 KB red zone therefore allowed an otherwise protected recursive
/// descent to exhaust a standard 2 MB Rust test-thread stack while checking
/// generated `noConfusion` declarations.  Grow early enough to cover the whole
/// interval between guards, not merely the next call frame.
const MIN_STACK_RED_ZONE: usize = 256 * 1024;

/// Stack size to grow to when running low (1 MB).
const STACK_GROWTH_SIZE: usize = 1024 * 1024;

/// Stack-safe recursive call wrapper.
///
/// Under normal execution, uses stacker::maybe_grow for stack safety.
/// Under Kani verification, stacker uses FFI (psm crate) which Kani doesn't support,
/// so we bypass the stack check and call the closure directly.
///
/// # Contract
///
/// ENSURES: Returns `f()` (closure result is preserved)
/// ENSURES: Closure is called exactly once
/// ENSURES: Provides stack overflow protection for deep recursion
#[inline(always)]
pub(crate) fn stack_safe<R>(f: impl FnOnce() -> R) -> R {
    #[cfg(kani)]
    {
        f()
    }
    #[cfg(not(kani))]
    {
        stacker::maybe_grow(MIN_STACK_RED_ZONE, STACK_GROWTH_SIZE, f)
    }
}

/// Saturating addition for De Bruijn indices.
///
/// Returns `a + b`, saturating at `u32::MAX` on overflow instead of panicking.
/// Saturation is safe because:
/// - BVar(u32::MAX) cannot match any real binder depth (ExprMeta caps at 1M)
/// - A saturated depth causes `should_descend` to return false, stopping traversal
/// - The type checker rejects any expression with unreachable De Bruijn indices
///
/// # Contract
///
/// ENSURES: Returns `a + b` when no overflow
/// ENSURES: Returns `u32::MAX` when `a + b` would overflow
/// ENSURES: Never panics
pub(crate) fn checked_add_u32(a: u32, b: u32, _context: &'static str) -> u32 {
    a.saturating_add(b)
}

/// Check if a bound variable index is in the range [start, end).
///
/// # Contract
///
/// ENSURES: If `end == u32::MAX`, returns `idx >= start` (unbounded above)
/// ENSURES: Otherwise, returns `idx >= start && idx < end` (half-open interval)
/// ENSURES: Pure - no side effects
pub(crate) fn bvar_in_range(idx: u32, start: u32, end: u32) -> bool {
    if end == u32::MAX {
        idx >= start
    } else {
        idx >= start && idx < end
    }
}

/// Shift a BVar range up by 1 when entering a binder.
///
/// When traversing into a binder body, the range of BVars to check must be
/// shifted up by 1 to account for the new binding level.
///
/// # Contract
///
/// ENSURES: Returns `None` if range is invalid (`start >= end` for bounded, or `start == u32::MAX`)
/// ENSURES: Returns `Some((start + 1, end + 1))` for valid bounded range
/// ENSURES: Returns `Some((start + 1, u32::MAX))` for unbounded range
/// ENSURES: On overflow, saturates at `u32::MAX` (never panics)
/// ENSURES: Pure - no side effects
pub(crate) fn shift_bvar_range(start: u32, end: u32) -> Option<(u32, u32)> {
    if end != u32::MAX && start >= end {
        return None;
    }
    if start == u32::MAX {
        return None;
    }
    let next_start = checked_add_u32(start, 1, "has_loose_bvar_in_range start");
    let next_end = if end == u32::MAX {
        u32::MAX
    } else {
        checked_add_u32(end, 1, "has_loose_bvar_in_range end")
    };
    Some((next_start, next_end))
}

/// Check if BVar `vidx` appears in the domain of a subsequent Pi binder.
///
/// In strict mode, only checks Pi domains (not the final result body).
/// In non-strict mode, also checks the result body.
///
/// The "transitivity" rule: if `vidx` appears in an implicit argument's domain,
/// and that implicit argument appears in a later domain, then `vidx` transitively
/// appears in the later domain.
///
/// Reference: lean4-ref/src/kernel/expr.cpp:370-387
pub(crate) fn has_loose_bvars_in_domain(b: &Expr, vidx: u32, strict: bool) -> bool {
    match &b.kind {
        ExprKind::Pi(bd, domain, body) => {
            if domain.has_loose_bvar(vidx) {
                if bd.info == BinderInfo::Default {
                    // vidx appears in an explicit argument's domain
                    return true;
                } else if has_loose_bvars_in_domain(body, 0, strict) {
                    // Transitivity: vidx appears in an implicit argument,
                    // and that implicit argument appears in a later domain
                    return true;
                }
            }
            // Search for vidx in the rest of the body (shifted by 1 for the binder)
            has_loose_bvars_in_domain(body, vidx + 1, strict)
        }
        _ => {
            if !strict {
                b.has_loose_bvar(vidx)
            } else {
                false
            }
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Expr struct — wraps ExprKind with cached ExprMeta (#1326 Phase 1b)
// ════════════════════════════════════════════════════════════════════════════

/// Core expression type for clean kernel.
///
/// Wraps `ExprKind` (the structural variants) with cached `ExprMeta` for O(1)
/// hash, flags, and loose bvar range access. Metadata is computed once at
/// construction time and never recomputed.
///
/// # Pattern Matching
///
/// To pattern-match on an expression, use the `kind()` accessor:
/// ```text
/// match expr.kind() {
///     ExprKind::App(f, a) => { /* ... */ }
///     ExprKind::Lam(bi, ty, body) => { /* ... */ }
///     _ => { /* ... */ }
/// }
/// ```
///
/// # Construction
///
/// Always use constructor methods (`Expr::app()`, `Expr::lam()`, etc.) which
/// compute metadata automatically. Direct construction via `Expr::new()` is
/// available but requires passing correct metadata.
///
/// # Must Use
///
/// Expressions are typically created as inputs to elaboration, type checking,
/// or rewriting. Dropping a freshly-built expression is usually a bug.
/// ```compile_fail
/// #![deny(unused_must_use)]
/// use clean_kernel::Expr;
///
/// Expr::bvar(0);
/// ```
#[must_use = "expressions should be inspected or passed onward"]
pub struct Expr {
    /// The structural kind of this expression.
    ///
    /// Use `kind()` for read-only access. Field is `pub(crate)` to prevent
    /// external mutation that would desynchronize cached metadata.
    /// See issue #1397.
    pub(crate) kind: ExprKind,
    /// Cached metadata (hash, depth, flags, loose bvar range).
    meta: ExprMeta,
}

impl From<ExprKind> for Expr {
    #[inline]
    fn from(kind: ExprKind) -> Self {
        Expr::from_kind(kind)
    }
}

impl std::ops::Deref for Expr {
    type Target = ExprKind;

    #[inline]
    fn deref(&self) -> &ExprKind {
        &self.kind
    }
}

impl Expr {
    /// Maximum valid BVar de Bruijn index.
    ///
    /// BVar indices must satisfy `idx < MAX_BVAR_RANGE` so that
    /// `loose_bvar_range = idx + 1` fits in the 20-bit metadata field.
    /// This matches Lean 4's `ExprMeta::MAX_BVAR_RANGE` (2^20 - 1 = 1,048,575).
    pub const MAX_BVAR_INDEX: u32 = ExprMeta::MAX_BVAR_RANGE - 1;

    /// Create an Expr from a kind, computing metadata automatically.
    #[inline]
    pub fn from_kind(kind: ExprKind) -> Self {
        let meta = kind.compute_meta();
        Expr { kind, meta }
    }

    /// Create an Expr with pre-computed metadata.
    /// Caller must ensure metadata is correct for the given kind.
    #[inline]
    #[allow(dead_code)]
    pub(crate) fn with_meta(kind: ExprKind, meta: ExprMeta) -> Self {
        Expr { kind, meta }
    }

    /// Read-only access to the structural kind of this expression.
    ///
    /// Prefer this over the `Deref<Target=ExprKind>` impl when pattern matching:
    /// ```text
    /// match expr.kind() {
    ///     ExprKind::App(f, a) => { /* ... */ }
    ///     _ => { /* ... */ }
    /// }
    /// ```
    #[inline]
    pub fn kind(&self) -> &ExprKind {
        &self.kind
    }

    /// Get the cached metadata for this expression (O(1)).
    #[inline]
    pub(crate) fn meta(&self) -> ExprMeta {
        self.meta
    }

    /// Return cached metadata (compatibility name for existing tests/callers).
    #[inline]
    #[allow(dead_code)]
    pub(crate) fn compute_meta(&self) -> ExprMeta {
        self.meta
    }

    /// Cached hash (O(1), lower 32 bits of metadata word).
    #[inline]
    pub fn hash_cached(&self) -> u32 {
        self.meta.hash()
    }

    /// Does this expression contain free variables? (O(1) metadata check)
    #[inline]
    pub fn has_fvar_quick(&self) -> bool {
        self.meta.has_fvar()
    }

    /// Does this expression contain expression metavariables? (O(1) metadata check)
    #[inline]
    pub fn has_expr_mvar_quick(&self) -> bool {
        self.meta.has_expr_mvar()
    }

    /// Does this expression contain level metavariables? (O(1) metadata check)
    #[inline]
    pub fn has_level_mvar_quick(&self) -> bool {
        self.meta.has_level_mvar()
    }

    /// Does this expression contain universe level parameters? (O(1) metadata check)
    #[inline]
    pub fn has_level_param_quick(&self) -> bool {
        self.meta.has_level_param()
    }

    /// Upper bound on loose bound variable indices (O(1) metadata check).
    /// If 0, expression has no loose bound variables.
    #[inline]
    pub fn loose_bvar_range(&self) -> u32 {
        self.meta.loose_bvar_range()
    }

    /// Does this expression have any loose bound variables? (O(1) metadata check)
    #[inline]
    pub fn has_loose_bvars_quick(&self) -> bool {
        self.meta.has_loose_bvars()
    }

    /// Apply a sharing-preserving folder. Returns None when unchanged.
    #[cfg(test)]
    pub(crate) fn fold_opt<F: ExprFolderOpt>(&self, folder: &mut F) -> Option<Expr> {
        folder.fold_expr_opt(self)
    }

    /// Apply a sharing-preserving folder. Returns self when unchanged.
    pub fn fold_opt_or_clone<F: ExprFolderOpt>(&self, folder: &mut F) -> Expr {
        folder.fold_expr_opt(self).unwrap_or_else(|| self.clone())
    }
}

impl Clone for Expr {
    #[inline]
    fn clone(&self) -> Self {
        Expr {
            kind: self.kind.clone(),
            meta: self.meta,
        }
    }
}

impl std::fmt::Debug for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Stack-safe: ExprKind's derived Debug recursively traverses all
        // Arc<Expr> children. Without this guard, deeply nested expressions
        // (common in Mathlib) overflow during error formatting.
        stack_safe(|| self.kind.fmt(f))
    }
}

impl std::hash::Hash for Expr {
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // O(1) hash using cached metadata — no tree traversal
        state.write_u32(self.meta.hash());
    }
}

impl PartialEq for Expr {
    fn eq(&self, other: &Self) -> bool {
        // Metadata pre-filter: reject mismatches in O(1) using the full cached
        // metadata word (hash/depth/flags/loose_bvar_range).
        if self.meta != other.meta {
            return false;
        }
        // Fall back to structural equality (required for correctness since
        // hash collisions are possible with 32-bit hash). Every child
        // comparison re-enters `Expr::eq`, so put the recursive descent behind
        // the same segmented-stack guard used by the other kernel walks.
        // Without this boundary, two independently allocated but structurally
        // equal deep terms can exhaust a normal test-thread stack in
        // `ExprKind::arc_eq`.
        stack_safe(|| self.kind == other.kind)
    }
}

impl Eq for Expr {}

impl Serialize for Expr {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        // Serialize only the kind; meta is recomputed on deserialization
        //
        // ExprKind recursively serializes Arc<Expr> children.  Keep the serde
        // boundary stack-safe just like the other recursive kernel walks: a
        // proof carrier can legitimately be much deeper than the native
        // thread stack, and encoding it must not turn into a process abort.
        stack_safe(|| self.kind.serialize(serializer))
    }
}

impl<'de> Deserialize<'de> for Expr {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let _decode_node = crate::serde_budget::enter_decode_node::<D::Error>("expression")?;
        stack_safe(|| {
            let kind = ExprKind::deserialize(deserializer)?;
            // Validate BVar indices at deserialization boundary.
            // ExprMeta::pack panics on loose_bvar_range > MAX_BVAR_RANGE (matching Lean 4),
            // which is correct for trusted code but must not crash on malformed .olean input.
            if let ExprKind::BVar(idx) = &kind {
                if *idx >= ExprMeta::MAX_BVAR_RANGE {
                    return Err(serde::de::Error::custom(
                        "BVar index exceeds ExprMeta::MAX_BVAR_RANGE",
                    ));
                }
            }
            Ok(Expr::from_kind(kind))
        })
    }
}

// Include test module from separate file
include!("tests.rs");

// Include kani module from separate file
include!("kani.rs");
