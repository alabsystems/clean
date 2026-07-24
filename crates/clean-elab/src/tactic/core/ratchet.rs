// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Ratchet constants for tracking trusted / unchecked call sites.
//!
//! Each constant is a ceiling on the number of known call sites for a
//! particular bypass pattern. The corresponding ratchet test prevents
//! new sites from being added without deliberate review.

/// Maximum `close_goal_unchecked` production call sites (#2159).
///
/// Each site bypasses type-checking and requires a `// SAFETY:` comment.
/// Decrease when a site is migrated to the checked `close_goal`.
/// History: 22 → 0 across Waves 1-15 plus #2355 (#2154, #2184, #302).
pub(crate) const CLOSE_GOAL_UNCHECKED_RATCHET: usize = 0;

/// Maximum `metas.assign` direct bypass sites in tactic/ (#2202).
///
/// Direct `state.metas.assign(goal_meta_id, proof)` bypasses both
/// `close_goal` (checked) and `close_goal_unchecked` (ratcheted).
/// Wave 14 (#2154): migrated the last site (mono Nat-addition).
pub(crate) const METAS_ASSIGN_BYPASS_RATCHET: usize = 0;

/// Maximum `create_trusted_ay_term(` call sites in tactic/ (#2442 Phase 3).
///
/// Produces trustedAy axiom instead of kernel-verifiable proof.
pub(crate) const TRUSTED_AY_CALL_SITE_RATCHET: usize = 0;

/// Maximum trustedArith production source sites in tactic/ (#2422).
///
/// Counts:
/// - `close_with_trusted_arith(` goal-closing fallbacks
/// - direct `create_trusted_arith_term(` calls outside `trusted_arith.rs`
/// - raw `make_trusted_arith_term_untracked(` calls outside `trusted_arith.rs`
/// - `replace_target_with_trusted_fallback(` callers outside `tactic/core/`
///
/// Live baseline on 2026-03-14:
/// - close=0
/// - direct=0
/// - raw=0
/// - rewrite=0
pub(crate) const TRUSTED_ARITH_SOURCE_SITE_RATCHET: usize = 0;

/// Maximum inherited-goal local-declaration rewrite sites outside `local_ops.rs`
/// (#2554, #2569).
///
/// All known local-declaration rewrite bypasses now go through `local_ops.rs`:
/// the 6 indexed-access sites from `#2554` and the 5 iterator-based
/// definitional rewrites from `#2569` (`clean`, `dsimp at *`, `dsimp at h`,
/// and their pattern-module mirrors).
pub(crate) const LOCAL_DECL_REWRITE_SOURCE_SITE_RATCHET: usize = 0;

/// Maximum elaborator sorry-producing source sites in infer/ (#2613, #2154).
///
/// Counts:
/// - `elab_sorry_with_kind(...)` entrypoints in `infer/`
/// - direct `create_sorry_term_with_kind_at_level(..., SorryKind::..., ...)`
///   sites in `infer/`
/// - direct `create_sorry_term_with_kind(..., SorryKind::..., ...)` sites
/// - direct `create_sorry_term(` sites
///
/// Live baseline on 2026-07-09:
/// - helper entrypoints=2 (`elab_explicit_sorry`, `elab_synthetic_sorry`)
/// - direct constructor sites=0 (`elab_let_rec`'s synthetic-`sorry` fallback
///   was eliminated for audit d04 — unsupported `let rec`/`where` shapes now
///   fail loud with `ElabError::WhereLetRecUnsupported`)
pub(crate) const ELAB_SORRY_SOURCE_SITE_RATCHET: usize = 2;
