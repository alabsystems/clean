// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Graduation — the front door from project-side proofs into the Mathverse
//! corpus.
//!
//! `graduate::intake` is the **only** producer of `SourceSystem::Cake`
//! shards; `shard_verify::cake_gate` is the verify-side enforcement that
//! makes the pairing unbypassable (a Cake-tagged shard without a digest-bound
//! `mathverse-graduation-v3.1` — or legacy v3/v2/v1 — record fails
//! verification, regardless of how it was produced).
//!
//! Trust contract (proof-soundness rules are law here):
//! * A theorem is stamped `KernelVerified` only when the kernel re-checked
//!   it **with its proof value** in a fresh environment.
//! * v2: definition-valued dependencies are **carried** under the exact same
//!   discipline — kernel `add_decl` with the defining value, dependency
//!   order, recorded in the record's `carried_definitions` section. A
//!   theorem's closure includes its carried definitions' closures, so a
//!   definition can never launder an axiom; a definition that fails its
//!   kernel re-check kills its dependents.
//! * v3: value-less inductive-family carriers are **carried** through the
//!   kernel's full checked `add_inductive` replay (positivity, universes,
//!   recursor generation) and recorded in the record's `carried_inductives`
//!   section. v3.0 fence: single-type non-nested families only; mutual and
//!   nested families fail closed (`carried-inductive-unsupported`). The
//!   family's closure contribution is the union over ALL member types and
//!   must be foundational-only.
//! * v3.1: theorem-valued dependencies are **carried** under the exact
//!   candidate discipline — kernel `add_decl` WITH the proof value,
//!   dependency-ordered within the full carry graph (families → definitions
//!   → theorems interleaved by topological order) — and recorded in the
//!   record's `carried_theorems` section. A carried theorem is supporting
//!   material, never a graduating candidate: the `on_duplicate` policy does
//!   not apply to it; its baseline novelty is an honest informational field
//!   (carried mathlib lemmas are expected duplicates). Closure composition
//!   is transitive, so a carried proof can never launder an axiom.
//! * The transitive axiom closure must be `⊆ FOUNDATIONAL_AXIOMS`; anything
//!   else is recorded `AxiomDependent` and rejected — never laundered.
//! * Novelty is honest `name + statement-hash` dedup against a pinned
//!   baseline plus earlier accepted candidates from the same run;
//!   defeq-grade dedup is explicitly out of scope for v3.

pub mod baseline_index;
pub mod compact_record;
pub mod intake;
mod intake_family;
pub mod lineage_build;
pub(crate) mod recheck;
pub mod record;
mod record_carried;
mod shadow;
pub mod tree_score;

pub use baseline_index::{build_baseline_index, BaselineIndex, BaselineIndexStats};
pub use compact_record::{
    extract_compact_record, CompactCarried, CompactGate, CompactProvenance, CompactRecord,
    CompactRecordError, CompactShard, CompactTheorem, COMPACT_RECORD_SCHEMA,
};
pub use intake::{
    graduate, graduate_with_base, CertificateCrossCheck, GraduationBaseline, GraduationRequest,
    RecheckBase,
};
pub use lineage_build::{build_corpus_lineage, LineageStats};
pub use record::{
    blake3_digest, blake3_file_digest, expr_canonical_digest, graduation_record_path,
    EvidenceClass, GraduatedTheorem, GraduationRecord, KernelVerdict, NoveltyMatchKind,
    NoveltyVerdict, OnDuplicate, GRADUATION_GATE_VERSION, GRADUATION_MIN_TRUST,
    GRADUATION_NOTE_PREFIX, GRADUATION_SCHEMA_VERSION, GRADUATION_SCHEMA_VERSION_V1,
    GRADUATION_SCHEMA_VERSION_V2, GRADUATION_SCHEMA_VERSION_V3, GRADUATION_SCHEMA_VERSION_V31,
    RECHECK_BASE_CLEAN_PRELUDE, RECHECK_BASE_LEAN_CORE,
};
pub use tree_score::{
    fast_tree_signature, tree_score_verified_corpus, CollisionForm, SameTreeSignatureHit,
    TreeScoreOptions, TreeScoreStats, TREE_SCORE_FUEL,
};

#[cfg(test)]
mod tests;
