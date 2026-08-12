// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The Mathverse Library — cross-system mathematics storage, import, trust, and retrieval.
//!
//! Imports theorems from Lean 4, Coq, HOL Light, HOL4, Isabelle, Mizar,
//! Metamath, Agda, Idris, F*, program verification tools, decision procedures,
//! and NN verification certificates into a unified format with trust tracking.
//!
//! Stores theorem and certificate shards from multiple source systems in a trust-labeled format.
//! Tracks source-system variants (see [`types::SourceSystem`]) via dedicated
//! translators, with a keyword-scan census across 238 repositories.
//! Enforces trust boundaries so axiomatized proofs can't contaminate kernel-verified ones.
//! Indexes the corpus for sub-millisecond retrieval across 5 search modes.
//!
//! Current downloadable release: `mathverse-v1.2.0` (2026-05-24) — 65 shards,
//! 945 MB uncompressed, published as a `mathverse-library-v1.2.0.tar.zst` archive
//! (195 MB) with an `mathverse-manifest.json` of BLAKE3 checksums (verified end to
//! end against the release). Shards are not checked in: fetch the release with
//! `clean mathverse download` (or `scripts/download_mathverse_library.sh`), or rebuild
//! from the public upstream libraries with `clean mathverse build-library`.
//!
//! Design reference: `designs/2026-03-27-unified-math-library-v2.md`

pub mod types;

// --- Unified `clean mathverse <verb>` CLI surface (Epic #3436, #3440) ---
pub mod cli;

// --- Library-hosted command implementations for the standalone `mathverse`
//     binary AND the unified `clean mathverse <verb>` dispatch (Epic #3436,
//     issue #3512). Moved here so both the old `mathverse` bin and the new
//     clap-based dispatch share a single source of truth. ---
pub mod mathverse_bin_cmds;

// --- Alpha machine modules (WS1, WS2a, WS5, WS10) ---
// The former top-level `coq_*` modules now live as flat submodules under
// `coq::*` (e.g. `coq::alpha`, `coq::shard`). Callers use those paths directly.
pub(crate) mod closure_source;
pub mod coq;
pub mod format;
pub(crate) mod frozen_map;
pub mod graph;
pub mod knowledge_graph;
pub mod lean4;
pub mod retrieval;

// --- Beta machine modules (WS3, WS4, WS7, WS11) ---
pub mod hol;
pub mod metamath;
pub mod mizar;
pub mod program_verify;
pub mod progverif;
/// Lane-agnostic replay infrastructure (targeter, verdict-source ledger, Coq
/// adapter) extracted from the Isabelle campaign — see `replay_infra`.
pub mod replay_infra;
pub mod smtlib;
pub mod tlaplus;
pub mod tptp;
pub mod trust;
/// Phase-2 trust layer: sign the kernel-re-verified verdict, re-audit, revoke.
/// See `designs/2026-06-24-mathverse-phase2-trust-the-archive.md`.
pub mod trust_sign;

// --- Gamma machine modules (WS2b, WS6, WS8, WS9) ---
pub mod decision;
pub mod decision_certs;
pub mod export;
pub mod nn;
pub mod nn_cert;
pub mod typetheory;

// --- Mathverse Engine: arXiv autoformalization pipeline ---
pub mod arxiv;
pub mod attempt_log;
pub mod authority_scope;
pub mod batch_typecheck;
pub mod env_fingerprint;
// The blessed choke point for all `std::env::set_var`/`remove_var` in this
// crate (production + tests + `tests/` integration binaries). Doc-hidden: it is
// process-environment plumbing, not part of the crate's mathematical API.
pub mod drift;
pub mod evidence_query;
pub mod evidence_refresh;
pub mod external_patch_attempt;
pub mod false_control_suite;
// --- Untrusted patch-bundle ingest (Aristotle/MathMap interop) ---
pub mod math_map;
#[doc(hidden)]
pub mod process_env;
// `metrics` declaration removed to match Wave 39 ("re-delete metrics.rs stub"):
// the source file was deleted but the declaration remained, breaking the build.
// Restore both together when the metrics contract is defined.

// --- Source refresh pipeline ---
pub mod source_refresh;

// --- Shared: pipeline, stats, verification ---
mod acl2_import;
mod acl2_term_translator;
pub mod agda_source;
pub mod bulk_import;
mod dafny_import;
mod dafny_type_parser;
pub mod dtt_import;
pub mod fstar_source;
pub mod idris_source;
pub mod importers;
mod isabelle_term_parser;
mod isabelle_thy_import;
mod lean3_import;
mod lean3_type_parser;
pub mod matita_source;
pub mod mizar_source;
pub mod pvs_source;
pub mod stats;
pub mod structured_import;
pub mod twelf_source;
pub mod type_preservation;

// --- Convert output: persistent shard metadata and output directory ---
// (now `export::convert_output`)
pub mod artifacts;
// Incremental/cached reconstruct: content-addressed per-system fingerprint +
// `mathverse.lock.json` build ledger. See designs/2026-06-30-mathverse-reconstruct-cli.md.
pub mod build_plan;
pub mod release;
// Corpus distribution verbs (UPLOAD / DOWNLOAD / SERVE) built on the release +
// serve_api substrate: server-pull download client, publish targets, and the
// turnkey serve launcher.
pub mod corpus_download;
pub mod corpus_upload;
pub mod replay_corpus;
pub mod replay_report;
pub mod serve_launch;
pub mod shard_metadata;

// --- Olean binary pipeline ---
pub mod olean_pipeline;

// --- Coq kernel-declaration shard writer (now coq::shard) ---
// --- Kernel Declaration → .mathverse export pipeline (now export::kernel_export) ---
// --- Native theorem → .mathverse export with tags/conjecture metadata
//     (now export::native_export) ---
// --- Coq extended importer (now coq::extended) ---
// --- Coq .vo binary parser + scale pipeline (now coq::vo) ---

// --- Alpha zone modules (real toolchain import, search, sharding) ---
pub mod build_library;
pub mod build_library_native;
pub mod build_mathlib;
pub mod cross_system_index;
pub mod discrim;
pub mod embedding;
pub mod equiv_graph;
pub mod equivalence;
pub mod error;
pub mod gamma_crown_shard;
pub mod graduate;
pub mod graph_alpha;
pub(crate) mod inductive_replay;
// `export::alpha` (export config/exporter), `trust::gamma_crown`, and the former
// top-level `lean4_*` modules (now `lean4::olean::*`) are reached via their
// canonical namespaced paths; the transitional re-export aliases were removed.
pub mod library;
pub mod manifest;
pub mod mathlib_verify;
pub mod nn_alpha;
pub mod nnverify_ieee754_shard;
pub mod premise_select;
pub mod provenance;
pub mod search;
pub mod self_verify;
pub mod serve_api;
pub mod shard;
pub mod shard_integrity;
pub mod shard_reconstruct;
pub mod shard_verify;
pub mod similar;
pub mod skeleton;
pub mod swarm_worker;
pub mod tag_index;
pub mod verify;

// --- Hard-theorem dependency graph analyzer (#3595) ---
pub mod depgraph;

#[cfg(test)]
mod integration_tests;

#[cfg(test)]
mod integration;

#[cfg(test)]
mod release_tests;

#[cfg(test)]
mod mathverse_integration_tests;

#[cfg(test)]
mod mathverse_integration_tests_extra;

pub mod fstar_reproof;

pub mod fstar_ay;

#[cfg(test)]
mod fstar_coverage_tests;

#[cfg(all(test, feature = "slow_tests"))]
mod verify_measurement;

#[cfg(all(test, feature = "slow_tests"))]
mod verify_measurement_incremental;

#[cfg(test)]
mod verify_incremental_synthetic;

#[cfg(test)]
mod tests_e2e_nontrivial;
#[cfg(test)]
mod tests_e2e_nontrivial_levels;
#[cfg(test)]
mod tests_e2e_pipeline;

/// Regression tests for interval-arithmetic T01/T11 reachability to
/// `mathverse_shard build-native` — see #3484.
#[cfg(test)]
mod build_library_native_interval_arith_tests;

/// Regression tests for the `mathverse_shard build-native` axiom classifier's
/// FOUNDATIONAL_AXIOMS whitelist delegation — see #3536.
#[cfg(test)]
mod build_library_native_classifier_tests;
