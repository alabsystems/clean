// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Hard-theorem dependency-graph analyzer.
//!
//! Given a "headline" theorem (e.g. `T60` = `NNVerify.Block.blockwise_crown_sound`,
//! `C004` = `NNVerify.C004.crown_equals_ibp`, `C006` =
//! `NNVerify.C006.blockwise_equals_monolithic`), this module walks the
//! kernel `Environment` to enumerate:
//!
//! 1. The **transitive dependency closure** — every constant reachable from
//!    the headline's type/value via `Expr::Const` edges.
//! 2. The **axiom closure** — the subset of the transitive closure that is a
//!    non-foundational `Declaration::Axiom` (the "trust gap" blocking
//!    constructive promotion).
//! 3. Per-node **impact** — how many other nodes in the headline's closure
//!    transitively depend on this node. Promoting a high-impact axiom into a
//!    constructive theorem unblocks a larger sub-closure than promoting a
//!    leaf. Agents use this ranking to pick the highest-leverage next-lemma
//!    target instead of picking blindly.
//!
//! Consumed by the `clean-depgraph` CLI (`crates/clean-mathverse/src/bin/clean_depgraph.rs`)
//! and by future proof-search / planner code that wants "what unblocks T60
//! the most right now?" programmatically.
//!
//! Reuses `Environment::axiom_deps` (see `clean-kernel/src/env/axiom_audit.rs`)
//! and `is_foundational_axiom` / `is_trust_marker` for classification.
//!
//! Design: issue #3595. Related: #3551 (axiom-reject triage), #3494 (Tier D
//! rat algebra), #3456 (Tier A/B prioritization).

pub mod analyze;
pub mod output;
pub mod seed;

pub use analyze::{
    build_closure, rank_unblock_candidates, rank_unblock_for_headline, ClosureGraph, NodeClass,
    NodeInfo, UnblockCandidate,
};
pub use output::{emit_dot, emit_headline_json, emit_impact_text, emit_unblock_text};
pub use seed::{headline_name, seed_environment, KNOWN_HEADLINES};
