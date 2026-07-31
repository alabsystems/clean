// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Reference Counting Pipeline for L5CNF → L5IR
//!
//! Implements the "Counting Immutable Beans" paper (Ullrich & de Moura, IFL 2020)
//! to transform high-level functional code into code with explicit reference counting.
//!
//! # Pipeline Overview
//!
//! ```text
//! ┌──────────────────────────────────────────────────────────────────────────────┐
//! │                        L5CNF → L5IR Pipeline                                  │
//! │                                                                              │
//! │  L5CNF                                                                       │
//! │    │                                                                         │
//! │    ▼                                                                         │
//! │  ╔═══════════════════╗                                                       │
//! │  ║  Borrow Inference ║  Determine which params can be borrowed vs owned      │
//! │  ╚═══════════════════╝                                                       │
//! │    │                                                                         │
//! │    ▼                                                                         │
//! │  ╔═══════════════════╗                                                       │
//! │  ║  Reset/Reuse      ║  Insert memory reuse opportunities                    │
//! │  ╚═══════════════════╝                                                       │
//! │    │                                                                         │
//! │    ▼                                                                         │
//! │  ╔═══════════════════╗                                                       │
//! │  ║  RC Insertion     ║  Insert inc/dec based on ownership                    │
//! │  ╚═══════════════════╝                                                       │
//! │    │                                                                         │
//! │    ▼                                                                         │
//! │  ╔═══════════════════╗                                                       │
//! │  ║  Expand Reset     ║  Lower reset/reuse to runtime checks                  │
//! │  ╚═══════════════════╝                                                       │
//! │    │                                                                         │
//! │    ▼                                                                         │
//! │  L5IR (with explicit inc/dec)                                                │
//! └──────────────────────────────────────────────────────────────────────────────┘
//! ```
//!
//! # Usage
//!
//! The example builds a minimal identity declaration and runs the pipeline.
//!
//! ```rust,no_run
//! use clean_compiler::lcnf::{Code, Decl, Param};
//! use clean_compiler::rc::{transform_decl, RCConfig};
//! use clean_kernel::{Expr, FVarId, Name};
//!
//! fn fvar(n: u64) -> FVarId {
//!     FVarId::new(n)
//! }
//!
//! fn name(s: &str) -> Name {
//!     Name::from_string(s)
//! }
//!
//! fn nat_type() -> Expr {
//!     Expr::const_str("Nat")
//! }
//!
//! let decl = Decl::new(
//!     name("id"),
//!     vec![],
//!     nat_type(),
//!     vec![Param::new(fvar(0), name("x"), nat_type())],
//!     Code::ret(fvar(0)),
//!     false,
//! );
//!
//! let config = RCConfig::default();
//! let _ir_decl = transform_decl(&decl, &config);
//! ```
//!
//! # References
//!
//! - Paper: Ullrich, S. and de Moura, L. "Counting Immutable Beans"
//!   IFL 2020. <https://arxiv.org/abs/1908.05647>
//! - Lean 4: src/Lean/Compiler/IR/{Borrow,RC,ResetReuse,ExpandResetReuse}.lean
//!
//! Part of #963 - Compiler IR infrastructure.

pub mod borrow;
pub mod expand;
pub mod insert;
pub(crate) mod pseudo_op;
pub mod reset_reuse;

use crate::lcnf::{Code, Decl};
use borrow::BorrowMap;
use clean_kernel::FVarId;

// Re-export key types
pub use borrow::{FnBorrow, Ownership};

// ═══════════════════════════════════════════════════════════════════════════
// FVarId Allocator
// ═══════════════════════════════════════════════════════════════════════════

/// Reserved FVarId ranges for different compiler phases.
///
/// Each range has 10M IDs, preventing collisions between passes.
///
/// All three passes use `FVarIdAllocator` with pass-specific constructors:
/// - `expand`: `FVarIdAllocator::for_expand_reset()` (start: 20M)
/// - `reset_reuse`: `FVarIdAllocator::for_reset_reuse()` (start: 30M)
/// - `insert`: `FVarIdAllocator::for_insert_rc()` (start: 40M)
pub mod fvar_ranges {
    /// Start of expand_reset_reuse IDs.
    pub const EXPAND_RESET_START: u64 = 20_000_000;
    /// Start of reset_reuse pass IDs.
    pub const RESET_REUSE_START: u64 = 30_000_000;
    /// Start of RC insert pass IDs.
    pub const INSERT_RC_START: u64 = 40_000_000;
    /// Maximum ID before overflow (leaves headroom).
    pub const MAX_FVAR_ID: u64 = u64::MAX - 1_000_000;
}

/// Pass-local FVarId allocator with overflow checking.
///
/// Each pass creates its own allocator with a reserved starting range,
/// preventing ID collisions between concurrent or sequential passes.
///
/// # Overflow Safety
///
/// Unlike raw atomic counters, this allocator:
/// - Uses `checked_add` to detect overflow
/// - Returns `Option<FVarId>` so callers can handle failure
/// - Reserves headroom before `u64::MAX` for safety
///
/// # Usage
///
/// ```rust,no_run
/// use clean_compiler::rc::FVarIdAllocator;
///
/// let mut alloc = FVarIdAllocator::for_expand_reset();
/// let id1 = alloc.fresh().expect("allocation failed");
/// let id2 = alloc.fresh().expect("allocation failed");
/// assert!(id2.as_u64() > id1.as_u64()); // Monotonically increasing
/// ```
#[derive(Clone, Debug)]
pub struct FVarIdAllocator {
    next_id: u64,
}

impl FVarIdAllocator {
    /// Create an allocator starting at a specific ID.
    ///
    /// Use the `for_*` constructors for standard pass-specific ranges.
    pub fn new(start: u64) -> Self {
        Self { next_id: start }
    }

    /// Create an allocator for the expand_reset_reuse pass.
    pub fn for_expand_reset() -> Self {
        Self::new(fvar_ranges::EXPAND_RESET_START)
    }

    /// Create an allocator for the reset_reuse pass.
    pub fn for_reset_reuse() -> Self {
        Self::new(fvar_ranges::RESET_REUSE_START)
    }

    /// Create an allocator for the RC insert pass.
    pub fn for_insert_rc() -> Self {
        Self::new(fvar_ranges::INSERT_RC_START)
    }

    /// Allocate a fresh FVarId.
    ///
    /// Returns `None` if allocation would overflow.
    pub fn fresh(&mut self) -> Option<FVarId> {
        if self.next_id >= fvar_ranges::MAX_FVAR_ID {
            return None;
        }
        let id = self.next_id;
        self.next_id = id.checked_add(1)?;
        Some(FVarId::new(id))
    }

    /// Current counter value (for testing/debugging).
    pub fn current(&self) -> u64 {
        self.next_id
    }
}

impl Default for FVarIdAllocator {
    /// Default allocator starts at 0.
    ///
    /// For pass-specific ranges, use `for_expand_reset()`, `for_reset_reuse()`,
    /// or `for_insert_rc()` instead.
    fn default() -> Self {
        Self::new(0)
    }
}

pub use expand::expand_reset_reuse;
pub use insert::insert_rc;
pub use reset_reuse::{reset_reuse, ResetReuseConfig};

/// Configuration for the RC transformation pipeline.
#[derive(Clone, Debug)]
pub struct RCConfig {
    /// Enable reset/reuse optimization.
    pub enable_reset_reuse: bool,
    /// Allow cross-family reuse (e.g., PSigma.mk → Prod.mk).
    pub cross_family_reuse: bool,
    /// Expand reset/reuse to runtime checks.
    pub expand_reset_reuse: bool,
}

impl Default for RCConfig {
    fn default() -> Self {
        Self {
            enable_reset_reuse: true,
            cross_family_reuse: false,
            expand_reset_reuse: true,
        }
    }
}

impl RCConfig {
    /// Minimal configuration (no optimizations).
    pub fn minimal() -> Self {
        Self {
            enable_reset_reuse: false,
            cross_family_reuse: false,
            expand_reset_reuse: false,
        }
    }

    /// Aggressive configuration (all optimizations).
    pub fn aggressive() -> Self {
        Self {
            enable_reset_reuse: true,
            cross_family_reuse: true,
            expand_reset_reuse: true,
        }
    }
}

/// The all-OWNED calling-convention map for a set of declarations (R3).
///
/// Every parameter of every declaration is `Owned`: the callee consumes
/// exactly one reference per parameter (releasing it either by `dec` on its
/// return paths or by transferring it into the result).
///
/// This is deliberately NOT [`infer_borrow`]. RC insertion runs PER
/// DECLARATION (the pass manager maps `transform_decl` over each decl), so a
/// self-inferred `Borrowed` parameter is a private convention no call site
/// can see: callers find nothing in their own borrow map for the callee and
/// default every position to `Owned` (transferring ownership in), while the
/// borrowed-convention callee never releases what it received. Each such
/// call leaked one reference per argument — `OfNat.ofNat`'s `inc; return`
/// stranded every `instOfNatNat` cell in the UIntN/Char `ofNat` carriers,
/// and `List.append`'s synthesized `go` (nil arm `inc m; return m` for a
/// param its wrapper passed as owned) stranded the entire appended suffix
/// per call. The external ABI is pinned the same way: runtime shims and
/// drivers invoke emitted functions consume-style, and `clean_apply_n`
/// forwards closure captures to a callee that consumes them.
///
/// Borrowed parameters remain sound only under a JOINT analysis whose
/// signatures every caller (in-slice and cross-slice) can consult; until a
/// persistent signature store exists, the ABI is all-owned, fail-closed.
fn abi_owned_map(decls: &[Decl]) -> BorrowMap {
    let mut map = BorrowMap::new();
    for decl in decls {
        map.insert(
            decl.name.clone(),
            FnBorrow {
                params: vec![Ownership::Owned; decl.params.len()],
            },
        );
    }
    map
}

/// Transform a list of declarations through the RC pipeline.
///
/// This is the main entry point for the RC transformation.
pub fn transform(decls: &[Decl], config: &RCConfig) -> Vec<Decl> {
    // Phase 1: the all-owned ABI map (see `abi_owned_map` for why this is
    // not `infer_borrow`).
    let borrow_map = abi_owned_map(decls);

    // Transform each declaration
    decls
        .iter()
        .map(|decl| transform_decl_with_borrow(decl, &borrow_map, config))
        .collect()
}

/// Transform a single declaration through the RC pipeline.
pub fn transform_decl(decl: &Decl, config: &RCConfig) -> Decl {
    let borrow_map = abi_owned_map(std::slice::from_ref(decl));
    transform_decl_with_borrow(decl, &borrow_map, config)
}

/// Transform a declaration with pre-computed borrow info.
fn transform_decl_with_borrow(decl: &Decl, borrow_map: &BorrowMap, config: &RCConfig) -> Decl {
    // Phase 2: Reset/Reuse optimization
    let decl = if config.enable_reset_reuse {
        let rr_config = ResetReuseConfig {
            cross_family: config.cross_family_reuse,
        };
        reset_reuse::reset_reuse_with_config(decl, &rr_config, borrow_map, None)
    } else {
        decl.clone()
    };

    // Phase 3: RC insertion
    let decl = insert_rc(&decl, borrow_map);

    // Phase 4: Expand reset/reuse
    if config.expand_reset_reuse {
        expand_reset_reuse(&decl)
    } else {
        decl
    }
}

/// Transform code through the RC pipeline (standalone).
///
/// Useful for testing or when you have code outside of a Decl context.
pub fn transform_code(code: &Code, config: &RCConfig) -> Code {
    // Phase 2: Reset/Reuse
    let code = if config.enable_reset_reuse {
        reset_reuse::reset_reuse_in_code(code)
    } else {
        code.clone()
    };

    // Phase 3: RC insertion (with empty borrow map for standalone)
    let borrow_map = BorrowMap::new();
    let code = insert::insert_rc_in_code_standalone(&code, &borrow_map);

    // Phase 4: Expand reset/reuse
    if config.expand_reset_reuse {
        expand::expand_reset_reuse_in_code(&code)
    } else {
        code
    }
}

#[cfg(test)]
mod tests;
