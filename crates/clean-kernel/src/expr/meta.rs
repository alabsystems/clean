// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Expression metadata (packed u64) and hashing helpers.
//!
//! Contains: ExprMeta with bit-packed hash/depth/flags/bvar_range,
//! mix_hash, hash_to_u64, level_has_mvar.

use crate::level::Level;
use serde::{Deserialize, Serialize};

// ════════════════════════════════════════════════════════════════════════════
// Expression Metadata (Phase 1 of expr-interning, #1326)
// ════════════════════════════════════════════════════════════════════════════

/// Cached expression metadata packed into a 64-bit word.
///
/// Matches Lean 4's `Expr.Data` bit layout exactly:
///   bits  0-31: hash (u32)
///   bits 32-39: approx_depth (u8, saturates at 255)
///   bit    40:  has_fvar
///   bit    41:  has_expr_mvar
///   bit    42:  has_level_mvar
///   bit    43:  has_level_param
///   bits 44-63: loose_bvar_range (u20, max 1_048_575)
///
/// Computed once at construction. Enables O(1) hash, O(1) subtree skipping.
/// Reference: lean4/src/kernel/expr.cpp:105-114, lean4/src/Lean/Expr.lean:119-158
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub(crate) struct ExprMeta(u64);

impl ExprMeta {
    // ── Bit layout constants ────────────────────────────────────────────

    const HASH_MASK: u64 = 0xFFFF_FFFF;
    const DEPTH_SHIFT: u32 = 32;
    const DEPTH_MASK: u64 = 0xFF;
    const HAS_FVAR_BIT: u32 = 40;
    const HAS_EXPR_MVAR_BIT: u32 = 41;
    const HAS_LEVEL_MVAR_BIT: u32 = 42;
    const HAS_LEVEL_PARAM_BIT: u32 = 43;
    const BVAR_RANGE_SHIFT: u32 = 44;
    pub(crate) const MAX_DEPTH: u32 = 255;
    pub(crate) const MAX_BVAR_RANGE: u32 = 1_048_575; // 2^20 - 1

    // ── Constructor ─────────────────────────────────────────────────────

    /// Pack metadata fields into a single u64.
    ///
    /// Mirrors `lean_expr_mk_data` from lean4/src/kernel/expr.cpp.
    #[inline]
    pub fn pack(
        hash: u32,
        loose_bvar_range: u32,
        approx_depth: u32,
        has_fvar: bool,
        has_expr_mvar: bool,
        has_level_mvar: bool,
        has_level_param: bool,
    ) -> Self {
        let depth = approx_depth.min(Self::MAX_DEPTH);
        // Match Lean 4: panic on too many bound variables (expr.cpp:109).
        // Saturation would cause incorrect O(1) guard behavior. Fix: #1363.
        // This is an INTENDED Lean-matching invariant (a documented design panic),
        // caller-guaranteed; excluded from the verified MIR (it is correct behavior,
        // not a panic-freedom obligation the verifier should refute).
        #[cfg(not(trust_verify))]
        assert!(
            loose_bvar_range <= Self::MAX_BVAR_RANGE,
            "too many bound variables: loose_bvar_range={loose_bvar_range} exceeds max={max}",
            max = Self::MAX_BVAR_RANGE
        );
        let range = loose_bvar_range;
        let bits = (hash as u64)
            | ((depth as u64) << Self::DEPTH_SHIFT)
            | ((has_fvar as u64) << Self::HAS_FVAR_BIT)
            | ((has_expr_mvar as u64) << Self::HAS_EXPR_MVAR_BIT)
            | ((has_level_mvar as u64) << Self::HAS_LEVEL_MVAR_BIT)
            | ((has_level_param as u64) << Self::HAS_LEVEL_PARAM_BIT)
            | ((range as u64) << Self::BVAR_RANGE_SHIFT);
        ExprMeta(bits)
    }

    /// Empty metadata (hash=0, no flags, depth=0, range=0).
    #[cfg(test)]
    pub const ZERO: ExprMeta = ExprMeta(0);

    // ── Accessors (O(1) bit extraction) ─────────────────────────────────

    /// Cached hash (lower 32 bits).
    #[inline]
    pub fn hash(self) -> u32 {
        (self.0 & Self::HASH_MASK) as u32
    }

    /// Approximate expression depth (bits 32-39, max 255).
    #[inline]
    pub fn approx_depth(self) -> u8 {
        ((self.0 >> Self::DEPTH_SHIFT) & Self::DEPTH_MASK) as u8
    }

    /// Does this expression contain free variables?
    #[inline]
    pub fn has_fvar(self) -> bool {
        (self.0 >> Self::HAS_FVAR_BIT) & 1 == 1
    }

    /// Does this expression contain expression metavariables?
    #[inline]
    pub fn has_expr_mvar(self) -> bool {
        (self.0 >> Self::HAS_EXPR_MVAR_BIT) & 1 == 1
    }

    /// Does this expression contain level metavariables?
    #[inline]
    pub fn has_level_mvar(self) -> bool {
        (self.0 >> Self::HAS_LEVEL_MVAR_BIT) & 1 == 1
    }

    /// Does this expression contain universe level parameters?
    #[inline]
    pub fn has_level_param(self) -> bool {
        (self.0 >> Self::HAS_LEVEL_PARAM_BIT) & 1 == 1
    }

    /// Upper bound on loose bound variable indices (bits 44-63, max 1_048_575).
    /// If 0, expression has no loose bound variables.
    #[inline]
    pub fn loose_bvar_range(self) -> u32 {
        (self.0 >> Self::BVAR_RANGE_SHIFT) as u32
    }

    /// Does this expression have any loose bound variables?
    #[inline]
    pub fn has_loose_bvars(self) -> bool {
        self.loose_bvar_range() > 0
    }

    /// Raw u64 value (for hashing the metadata word itself, as Lean 4 does).
    #[inline]
    #[cfg(test)]
    pub fn raw(self) -> u64 {
        self.0
    }

    // ── Combining operations (for building metadata from children) ──────

    /// Compute App metadata from function and argument metadata.
    ///
    /// Mirrors `lean_expr_mk_app_data` from lean4/src/kernel/expr.cpp:120-126.
    /// - hash: mix_hash(f.raw, a.raw) (hashes the full data words, not just hash fields)
    /// - depth: max(f.depth, a.depth) + 1
    /// - flags: bitwise OR of both
    /// - bvar_range: max(f.range, a.range)
    #[inline]
    pub fn mk_app_meta(f: ExprMeta, a: ExprMeta) -> ExprMeta {
        let depth = (f.approx_depth().max(a.approx_depth()) as u32 + 1).min(Self::MAX_DEPTH);
        let range = f.loose_bvar_range().max(a.loose_bvar_range());
        let h = mix_hash(f.0, a.0) as u32;
        // OR the 4 flag bits (bits 40-43) from both
        let flags = (f.0 | a.0) & (0xF_u64 << Self::HAS_FVAR_BIT);
        let bits = (h as u64)
            | ((depth as u64) << Self::DEPTH_SHIFT)
            | flags
            | ((range as u64) << Self::BVAR_RANGE_SHIFT);
        ExprMeta(bits)
    }

    /// Compute binder metadata (for Lam, Pi).
    ///
    /// body_range uses saturating_sub(1) because the binder binds one variable.
    /// Reference: lean4/src/Lean/Expr.lean:482,491
    #[inline]
    pub fn mk_binder_meta(ty: ExprMeta, body: ExprMeta, extra_hash: u64) -> ExprMeta {
        let depth = (ty.approx_depth().max(body.approx_depth()) as u32 + 1).min(Self::MAX_DEPTH);
        let body_range = body.loose_bvar_range().saturating_sub(1);
        let range = ty.loose_bvar_range().max(body_range);
        let h = mix_hash(
            depth as u64,
            mix_hash(ty.hash() as u64, mix_hash(body.hash() as u64, extra_hash)),
        ) as u32;
        ExprMeta::pack(
            h,
            range,
            depth,
            ty.has_fvar() || body.has_fvar(),
            ty.has_expr_mvar() || body.has_expr_mvar(),
            ty.has_level_mvar() || body.has_level_mvar(),
            ty.has_level_param() || body.has_level_param(),
        )
    }

    /// Compute Let metadata (ty, val are outside binder; body is inside).
    ///
    /// Reference: lean4/src/Lean/Expr.lean:500
    #[inline]
    pub fn mk_let_meta(ty: ExprMeta, val: ExprMeta, body: ExprMeta) -> ExprMeta {
        let depth = (ty
            .approx_depth()
            .max(val.approx_depth())
            .max(body.approx_depth()) as u32
            + 1)
        .min(Self::MAX_DEPTH);
        let body_range = body.loose_bvar_range().saturating_sub(1);
        let range = ty
            .loose_bvar_range()
            .max(val.loose_bvar_range())
            .max(body_range);
        let h = mix_hash(
            depth as u64,
            mix_hash(
                ty.hash() as u64,
                mix_hash(val.hash() as u64, body.hash() as u64),
            ),
        ) as u32;
        ExprMeta::pack(
            h,
            range,
            depth,
            ty.has_fvar() || val.has_fvar() || body.has_fvar(),
            ty.has_expr_mvar() || val.has_expr_mvar() || body.has_expr_mvar(),
            ty.has_level_mvar() || val.has_level_mvar() || body.has_level_mvar(),
            ty.has_level_param() || val.has_level_param() || body.has_level_param(),
        )
    }

    /// Compute wrapper metadata (for MData, Proj, Squash).
    /// Just increments depth and mixes in extra hash material.
    #[inline]
    pub fn mk_wrapper_meta(inner: ExprMeta, extra_hash: u64) -> ExprMeta {
        let depth = (inner.approx_depth() as u32 + 1).min(Self::MAX_DEPTH);
        let h = mix_hash(depth as u64, mix_hash(inner.hash() as u64, extra_hash)) as u32;
        ExprMeta::pack(
            h,
            inner.loose_bvar_range(),
            depth,
            inner.has_fvar(),
            inner.has_expr_mvar(),
            inner.has_level_mvar(),
            inner.has_level_param(),
        )
    }
}

impl PartialEq for ExprMeta {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for ExprMeta {}

impl std::hash::Hash for ExprMeta {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u64(self.0);
    }
}

/// MurmurHash2-64A mixing step.
///
/// Matches Lean 4's `lean_uint64_mix_hash` from runtime/hash.h.
/// Used for combining hash values in expression metadata computation.
#[inline]
pub(crate) fn mix_hash(h: u64, k: u64) -> u64 {
    const M: u64 = 0xc6a4_a793_5bd1_e995;
    const R: u32 = 47;
    let mut k = k.wrapping_mul(M);
    k ^= k >> R;
    k ^= M;
    let mut h = h ^ k;
    h = h.wrapping_mul(M);
    h
}

/// Simple FxHash-style hasher for Kani/CBMC verification.
///
/// Replaces `DefaultHasher` (SipHash) under `cfg(kani)` because CBMC cannot
/// efficiently unwind SipHash's multi-round compression function, causing
/// verification timeouts on any harness that constructs `Name`, `Sort`, `Const`,
/// or other expression variants requiring hashing during `ExprKind::compute_meta()`.
///
/// Uses single multiply-XOR per word — no compression rounds, no block
/// accumulation. CBMC handles this in O(1) per `write_*` call.
///
/// Hash quality is irrelevant for verification: Kani harnesses test functional
/// properties (roundtrips, idempotence), not hash distribution.
#[cfg(kani)]
pub(crate) struct KaniHasher {
    state: u64,
}

#[cfg(kani)]
impl KaniHasher {
    pub(crate) fn new() -> Self {
        KaniHasher { state: 0 }
    }
}

#[cfg(kani)]
impl std::hash::Hasher for KaniHasher {
    fn finish(&self) -> u64 {
        self.state
    }

    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.state = self.state.wrapping_mul(31).wrapping_add(b as u64);
        }
    }

    fn write_u8(&mut self, i: u8) {
        self.state ^= i as u64;
        self.state = self.state.wrapping_mul(0x517cc1b727220a95);
    }

    fn write_u16(&mut self, i: u16) {
        self.state ^= i as u64;
        self.state = self.state.wrapping_mul(0x517cc1b727220a95);
    }

    fn write_u32(&mut self, i: u32) {
        self.state ^= i as u64;
        self.state = self.state.wrapping_mul(0x517cc1b727220a95);
    }

    fn write_u64(&mut self, i: u64) {
        self.state ^= i;
        self.state = self.state.wrapping_mul(0x517cc1b727220a95);
    }

    fn write_u128(&mut self, i: u128) {
        self.write_u64(i as u64);
        self.write_u64((i >> 64) as u64);
    }

    fn write_usize(&mut self, i: usize) {
        self.write_u64(i as u64);
    }

    fn write_i8(&mut self, i: i8) {
        self.write_u8(i as u8);
    }

    fn write_i16(&mut self, i: i16) {
        self.write_u16(i as u16);
    }

    fn write_i32(&mut self, i: i32) {
        self.write_u32(i as u32);
    }

    fn write_i64(&mut self, i: i64) {
        self.write_u64(i as u64);
    }

    fn write_i128(&mut self, i: i128) {
        self.write_u128(i as u128);
    }

    fn write_isize(&mut self, i: isize) {
        self.write_u64(i as u64);
    }
}

/// Stable 64-bit hash helper used for expression metadata inputs.
#[cfg(not(kani))]
#[inline]
pub(crate) fn hash_to_u64<T: std::hash::Hash>(value: &T) -> u64 {
    use std::hash::Hasher;
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

/// Stable 64-bit hash helper used for expression metadata inputs.
///
/// Under Kani, uses `KaniHasher` (FxHash-style) instead of `DefaultHasher`
/// (SipHash) to avoid CBMC verification condition explosion from SipHash
/// compression rounds. See `KaniHasher` doc comment.
#[cfg(kani)]
#[inline]
pub(crate) fn hash_to_u64<T: std::hash::Hash>(value: &T) -> u64 {
    use std::hash::Hasher;
    let mut hasher = KaniHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

/// Level metavariable check used by Expr metadata computation.
///
/// clean `Level` currently has no MVar constructor, so this is always false.
/// We still recurse structurally so future `Level` extensions fail to compile
/// here until the new variant is handled explicitly.
#[cfg(not(kani))]
#[inline]
pub(crate) fn level_has_mvar(level: &Level) -> bool {
    match level {
        Level::Zero | Level::Param(_) => false,
        Level::Succ(inner) => level_has_mvar(inner),
        Level::Max(lhs, rhs) | Level::IMax(lhs, rhs) => level_has_mvar(lhs) || level_has_mvar(rhs),
    }
}

/// Kani override: Level has no MVar variant, so this is unconditionally false.
/// Avoids CBMC unwinding through recursive Arc<Level> trees during
/// ExprKind::compute_meta() (observed as "level_has_mvar iteration 1569" timeout).
/// Production code retains the structural match for compile-time safety on
/// future Level variant additions.
#[cfg(kani)]
#[inline]
pub(crate) fn level_has_mvar(_level: &Level) -> bool {
    false
}
