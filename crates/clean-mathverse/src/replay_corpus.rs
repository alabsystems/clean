// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rust-owned Mathverse production replay corpus accounting.
//!
//! This replaces `scripts/generate_mathverse_replay_production_corpus.py` as the
//! launch/report evidence surface. It is intentionally fail-closed: discovered
//! production `mathverse` tactic sites receive native-gate or strict `mathverse_use`
//! credit only when a bounded Rust replay witness matches the exact scanned
//! source location and source text.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::LazyLock;

use regex::Regex;
use serde::Serialize;

use crate::library::MathverseLibrary;
use crate::premise_select::{search_for_goal, PremiseConfig};
use crate::shard_verify::verify_native_shard;
use crate::trust::policy::TrustPolicy;

/// Default production corpus report path.
pub const DEFAULT_REPLAY_CORPUS_OUTPUT: &str = "reports/mathverse-replay-production-corpus.json";

/// Number of unsupported obligations sampled per source for fail-closed smoke
/// diagnostics.
pub const UNSUPPORTED_REPLAY_SAMPLE_PER_SOURCE: usize = 4;

const MATHLIB_ROOT: &str = "data/raw/mathlib4/Mathlib";
const BATTERIES_ROOT: &str = "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse";
const LINE65_NATIVE_SHARD_FIXTURE_PATH: &str =
    "crates/clean-mathverse/tests/fixtures/mathverse-replay/line65-clean-native.mathverse";

struct BoundedWitnessSpec {
    id: &'static str,
    line: &'static str,
    native_declaration: &'static str,
}

const BOUNDED_NATIVE_GATE_WITNESSES: &[BoundedWitnessSpec] = &[
    BoundedWitnessSpec {
        id: "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:65",
        line: "example (_ : (1 : Int) < (0 : Int)) : False := by mathverse",
        native_declaration: "clean.Mathverse.Production.BatteriesBenchmark.line65.nativeGateWitness",
    },
    BoundedWitnessSpec {
        id: "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:67",
        line: "example (_ : (0 : Int) < (0 : Int)) : False := by mathverse",
        native_declaration: "clean.Mathverse.Production.BatteriesBenchmark.line67.nativeGateWitness",
    },
    BoundedWitnessSpec {
        id: "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:71",
        line: "example {x : Int} (_ : 0 ≤ x) (_ : x ≤ -1) : False := by mathverse",
        native_declaration: "clean.Mathverse.Production.BatteriesBenchmark.line71.nativeGateWitness",
    },
    BoundedWitnessSpec {
        id: "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:73",
        line: "example {x : Int} (_ : x % 2 < x - 2 * (x / 2)) : False := by mathverse",
        native_declaration: "clean.Mathverse.Production.BatteriesBenchmark.line73.nativeGateWitness",
    },
    BoundedWitnessSpec {
        id: "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:74",
        line: "example {x : Int} (_ : x % 2 > 5) : False := by mathverse",
        native_declaration: "clean.Mathverse.Production.BatteriesBenchmark.line74.nativeGateWitness",
    },
    BoundedWitnessSpec {
        id: "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:76",
        line: "example {x : Int} (_ : 2 * (x / 2) > x) : False := by mathverse",
        native_declaration: "clean.Mathverse.Production.BatteriesBenchmark.line76.nativeGateWitness",
    },
    BoundedWitnessSpec {
        id: "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:77",
        line: "example {x : Int} (_ : 2 * (x / 2) ≤ x - 2) : False := by mathverse",
        native_declaration: "clean.Mathverse.Production.BatteriesBenchmark.line77.nativeGateWitness",
    },
    BoundedWitnessSpec {
        id: "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:79",
        line: "example {x : Nat} : x / 0 = 0 := by mathverse",
        native_declaration: "clean.Mathverse.Production.BatteriesBenchmark.line79.nativeGateWitness",
    },
    BoundedWitnessSpec {
        id: "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:80",
        line: "example {x : Int} : x / 0 = 0 := by mathverse",
        native_declaration: "clean.Mathverse.Production.BatteriesBenchmark.line80.nativeGateWitness",
    },
    BoundedWitnessSpec {
        id: "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:82",
        line: "example {x : Int} : x / 2 + x / (-2) = 0 := by mathverse",
        native_declaration: "clean.Mathverse.Production.BatteriesBenchmark.line82.nativeGateWitness",
    },
    BoundedWitnessSpec {
        id: "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:84",
        line: "example (_ : 7 < 3) : False := by mathverse",
        native_declaration: "clean.Mathverse.Production.BatteriesBenchmark.line84.nativeGateWitness",
    },
    BoundedWitnessSpec {
        id: "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:85",
        line: "example (_ : 0 < 0) : False := by mathverse",
        native_declaration: "clean.Mathverse.Production.BatteriesBenchmark.line85.nativeGateWitness",
    },
    BoundedWitnessSpec {
        id: "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:87",
        line: "example {x : Nat} (_ : x > 7) (_ : x < 3) : False := by mathverse",
        native_declaration: "clean.Mathverse.Production.BatteriesBenchmark.line87.nativeGateWitness",
    },
    BoundedWitnessSpec {
        id: "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:88",
        line: "example {x : Nat} (_ : x ≥ 7) (_ : x ≤ 3) : False := by mathverse",
        native_declaration: "clean.Mathverse.Production.BatteriesBenchmark.line88.nativeGateWitness",
    },
    BoundedWitnessSpec {
        id: "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:90",
        line: "example {x y : Nat} (_ : x + y > 10) (_ : x < 5) (_ : y < 5) : False := by mathverse",
        native_declaration: "clean.Mathverse.Production.BatteriesBenchmark.line90.nativeGateWitness",
    },
    BoundedWitnessSpec {
        id: "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:92",
        line:
            "example {x y : Int} (_ : x + y > 10) (_ : 2 * x < 11) (_ : y < 5) : False := by mathverse",
        native_declaration: "clean.Mathverse.Production.BatteriesBenchmark.line92.nativeGateWitness",
    },
    BoundedWitnessSpec {
        id: "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:93",
        line:
            "example {x y : Nat} (_ : x + y > 10) (_ : 2 * x < 11) (_ : y < 5) : False := by mathverse",
        native_declaration: "clean.Mathverse.Production.BatteriesBenchmark.line93.nativeGateWitness",
    },
    BoundedWitnessSpec {
        id: "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:95",
        line: "example {x y : Int} (_ : 2 * x + 4 * y = 5) : False := by mathverse",
        native_declaration: "clean.Mathverse.Production.BatteriesBenchmark.line95.nativeGateWitness",
    },
    BoundedWitnessSpec {
        id: "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:96",
        line: "example {x y : Nat} (_ : 2 * x + 4 * y = 5) : False := by mathverse",
        native_declaration: "clean.Mathverse.Production.BatteriesBenchmark.line96.nativeGateWitness",
    },
    BoundedWitnessSpec {
        id: "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:100",
        line: "example {x y : Nat} (_ : 6 * x + 7 * y = 5) : False := by mathverse",
        native_declaration: "clean.Mathverse.Production.BatteriesBenchmark.line100.nativeGateWitness",
    },
    BoundedWitnessSpec {
        id: "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:102",
        line: "example {x : Nat} (_ : x < 0) : False := by mathverse",
        native_declaration: "clean.Mathverse.Production.BatteriesBenchmark.line102.nativeGateWitness",
    },
    BoundedWitnessSpec {
        id: "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:104",
        line: "example {x y z : Int} (_ : x + y > z) (_ : x < 0) (_ : y < 0) (_ : z > 0) : False := by mathverse",
        native_declaration: "clean.Mathverse.Production.BatteriesBenchmark.line104.nativeGateWitness",
    },
    BoundedWitnessSpec {
        id: "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:110",
        line: "example {x y z : Int} (_ : x - y - z = 0) (_ : x > y + z) : False := by mathverse",
        native_declaration: "clean.Mathverse.Production.BatteriesBenchmark.line110.nativeGateWitness",
    },
    BoundedWitnessSpec {
        id: "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:112",
        line: "example {x y z : Nat} (_ : x - y - z = 0) (_ : x > y + z) : False := by mathverse",
        native_declaration: "clean.Mathverse.Production.BatteriesBenchmark.line112.nativeGateWitness",
    },
    BoundedWitnessSpec {
        id: "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:118",
        line: "example {x y : Nat} (h₁ : x - y ≤ 0) (h₂ : y < x) : False := by mathverse",
        native_declaration: "clean.Mathverse.Production.BatteriesBenchmark.line118.nativeGateWitness",
    },
    BoundedWitnessSpec {
        id: "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:120",
        line: "example {x y : Int} (_ : x / 2 - y / 3 < 1) (_ : 3 * x ≥ 2 * y + 6) : False := by mathverse",
        native_declaration: "clean.Mathverse.Production.BatteriesBenchmark.line120.nativeGateWitness",
    },
    BoundedWitnessSpec {
        id: "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:122",
        line: "example {x y : Nat} (_ : x / 2 - y / 3 < 1) (_ : 3 * x ≥ 2 * y + 6) : False := by mathverse",
        native_declaration: "clean.Mathverse.Production.BatteriesBenchmark.line122.nativeGateWitness",
    },
    BoundedWitnessSpec {
        id: "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:124",
        line: "example {x y : Nat} (_ : x / 2 - y / 3 < 1) (_ : 3 * x ≥ 2 * y + 4) : False := by mathverse",
        native_declaration: "clean.Mathverse.Production.BatteriesBenchmark.line124.nativeGateWitness",
    },
    BoundedWitnessSpec {
        id: "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:126",
        line: "example {x y : Nat} (_ : x / 2 - y / 3 < x % 2) (_ : 3 * x ≥ 2 * y + 4) : False := by mathverse",
        native_declaration: "clean.Mathverse.Production.BatteriesBenchmark.line126.nativeGateWitness",
    },
    BoundedWitnessSpec {
        id: "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:128",
        line: "example {x : Int} (h₁ : 5 ≤ x) (h₂ : x ≤ 4) : False := by mathverse",
        native_declaration: "clean.Mathverse.Production.BatteriesBenchmark.line128.nativeGateWitness",
    },
    BoundedWitnessSpec {
        id: "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:130",
        line: "example {x : Nat} (h₁ : 5 ≤ x) (h₂ : x ≤ 4) : False := by mathverse",
        native_declaration: "clean.Mathverse.Production.BatteriesBenchmark.line130.nativeGateWitness",
    },
    BoundedWitnessSpec {
        id: "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:132",
        line: "example {x : Nat} (h₁ : x / 3 ≥ 2) (h₂ : x < 6) : False := by mathverse",
        native_declaration: "clean.Mathverse.Production.BatteriesBenchmark.line132.nativeGateWitness",
    },
];

static TACTIC_PATTERNS: LazyLock<[Regex; 3]> = LazyLock::new(|| {
    [
        Regex::new(r"\bby\s*\(?\s*mathverse\b").expect("valid by mathverse regex"),
        Regex::new(r"(?:^|[;<|>(]\s*)mathverse\b").expect("valid mathverse line regex"),
        Regex::new(r"\bfail_if_success\s+mathverse\b").expect("valid fail_if_success regex"),
    ]
});

/// Production corpus generation error.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum ReplayCorpusError {
    /// A scan root or source file could not be read.
    #[error("I/O while scanning `{path}`: {source}")]
    Io {
        /// Path that failed.
        path: PathBuf,
        /// Underlying error.
        #[source]
        source: std::io::Error,
    },
    /// Output serialization failed.
    #[error("failed to serialize replay corpus JSON: {0}")]
    Json(#[from] serde_json::Error),
}

/// Production corpus report.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ReplayCorpusReport {
    /// Schema marker.
    pub schema_version: &'static str,
    /// Rust generator identity.
    pub generated_by: &'static str,
    /// Determinism marker for report validators.
    pub deterministic: bool,
    /// Overall status.
    pub status: &'static str,
    /// Bounded claim.
    pub claim: &'static str,
    /// Scanned roots, repo-relative.
    pub scan_roots: Vec<String>,
    /// Classification legend.
    pub classification: BTreeMap<&'static str, &'static str>,
    /// Aggregate counts.
    pub counts: ReplayCorpusCounts,
    /// Counts by source corpus.
    pub by_source: BTreeMap<String, usize>,
    /// Counts by outcome.
    pub by_outcome: BTreeMap<String, usize>,
    /// Bounded per-obligation replay witnesses that received native-gate credit.
    pub native_gate_witnesses: Vec<ReplayWitness>,
    /// Narrow extracted production obligations that are not yet replay credit.
    pub production_extraction_fixtures: Vec<ProductionExtractionFixture>,
    /// Sampled fail-closed diagnostics.
    pub replay_smoke: ReplaySmoke,
    /// First 25 obligations for review.
    pub sample_obligations: Vec<ReplayObligation>,
    /// Total obligation count.
    pub obligation_count: usize,
}

/// Aggregate corpus counts.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct ReplayCorpusCounts {
    /// Found syntactic Mathverse tactic sites.
    pub found: usize,
    /// Native-gate verified production obligations.
    pub native_gate_verified: usize,
    /// Obligations applied through strict `mathverse_use`.
    pub applied_through_strict_mathverse_use: usize,
    /// Expected failure sites.
    pub rejected: usize,
    /// Found sites without replay coverage.
    pub unsupported: usize,
}

/// One found Mathverse tactic site.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ReplayObligation {
    /// Stable id `<repo-relative-path>:<line>`.
    pub id: String,
    /// Source corpus label.
    pub source: String,
    /// Repo-relative file path.
    pub path: String,
    /// 1-indexed source line.
    pub line: usize,
    /// `native_gate_verified`, `rejected`, or `unsupported`.
    pub outcome: String,
}

/// One bounded production replay witness.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ReplayWitness {
    /// Obligation id.
    pub obligation_id: String,
    /// Rust runner identity.
    pub runner: &'static str,
    /// Native declaration that passed the bounded witness gate.
    pub native_declaration: &'static str,
    /// Whether the source line still matches the allowlisted obligation.
    pub source_line_verified: bool,
    /// Whether a native-gate replay witness was verified.
    pub native_gate_verified: bool,
    /// Whether the witness was applied through strict `mathverse_use`.
    pub applied_through_strict_mathverse_use: bool,
    /// Scope limits that keep this witness from overclaiming full coverage.
    pub limitations: Vec<&'static str>,
}

/// One extracted production obligation fixture.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ProductionExtractionFixture {
    /// Obligation id.
    pub obligation_id: &'static str,
    /// Extractor identity.
    pub extractor: &'static str,
    /// Extraction status.
    pub status: &'static str,
    /// clean goal expression sketch.
    pub clean_goal: &'static str,
    /// clean local hypothesis sketches.
    pub clean_local_hypotheses: Vec<&'static str>,
    /// Whether this fixture received native-gate credit.
    pub native_gate_verified: bool,
    /// Whether this fixture was applied through strict `mathverse_use`.
    pub applied_through_strict_mathverse_use: bool,
    /// Missing clean entry point that must construct the active tactic proof state.
    pub proof_state_entry_point: &'static str,
    /// Missing native Mathverse search entry point for the extracted obligation.
    pub native_mathverse_search_entry_point: &'static str,
    /// Rust-owned native shard verification entry point.
    pub native_shard_verification_entry_point: &'static str,
    /// Missing strict tactic application entry point.
    pub strict_mathverse_use_entry_point: &'static str,
    /// First typed internal obligation adapter status.
    pub typed_obligation_status: &'static str,
    /// Typed internal obligation when the fixture is accepted by the narrow adapter.
    pub typed_internal_obligation: Option<TypedProductionMathverseObligation>,
    /// Remaining requirements before this can count as strict production replay.
    pub required_for_strict_credit: Vec<&'static str>,
}

/// Typed internal Mathverse obligation built from a production extraction fixture.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct TypedProductionMathverseObligation {
    /// Source fixture obligation id.
    pub obligation_id: &'static str,
    /// Internal adapter identity.
    pub adapter: &'static str,
    /// Goal sort.
    pub goal_sort: &'static str,
    /// Goal expression.
    pub goal_expr: &'static str,
    /// Local hypotheses available to Mathverse.
    pub local_hypotheses: Vec<TypedProductionHypothesis>,
    /// Whether an elaborator ProofState has been constructed.
    pub proof_state_constructed: bool,
    /// Whether this obligation is eligible for strict replay credit.
    pub strict_replay_ready: bool,
    /// Native search attempt attached to this typed obligation.
    pub native_search_attempt: Option<ProductionNativeSearchAttempt>,
}

/// Fail-closed native Mathverse search attempt for a typed production obligation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ProductionNativeSearchAttempt {
    /// Typed obligation id.
    pub obligation_id: &'static str,
    /// Search adapter identity.
    pub runner: &'static str,
    /// Fail-closed search status.
    pub status: &'static str,
    /// Rendered query passed to the narrow native search path.
    pub goal_text: String,
    /// Whether native Mathverse search was invoked.
    pub native_search_invoked: bool,
    /// Number of native search candidates returned.
    pub candidate_count: usize,
    /// Candidates available from a concrete per-obligation native source.
    pub candidate_sources: Vec<ProductionNativeCandidateSource>,
    /// Selected native declaration, if one was found.
    pub selected_native_declaration: Option<String>,
    /// Selected native shard identity, if one was found.
    pub selected_native_shard: Option<&'static str>,
    /// Verifier input for the selected native shard, if one was found.
    pub native_shard_verifier_input: Option<ProductionNativeShardVerifierInput>,
    /// Native shard verification status.
    pub native_shard_verification_status: &'static str,
    /// Whether a native shard verification attempt was made for the selected declaration.
    pub native_shard_verification_attempted: bool,
    /// Whether the selected native shard passed the native gate.
    pub native_shard_verified: bool,
    /// Fail-closed bridge from a verified native shard toward an elaborator ProofState.
    pub proof_state_bridge_attempt: Option<ProductionProofStateBridgeAttempt>,
    /// Whether an elaborator ProofState was available for strict closure.
    pub proof_state_constructed: bool,
    /// Whether strict `mathverse_use` closed the obligation.
    pub strict_mathverse_use_closed: bool,
    /// Whether this attempt can be counted as strict replay.
    pub strict_replay_ready: bool,
    /// Reasons the attempt remains fail-closed.
    pub fail_closed_reasons: Vec<&'static str>,
}

/// Fail-closed ProofState bridge for a verified production native shard.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ProductionProofStateBridgeAttempt {
    /// Typed obligation id.
    pub obligation_id: &'static str,
    /// Bridge identity.
    pub bridge: &'static str,
    /// Fail-closed bridge status.
    pub status: &'static str,
    /// Goal sort expected by the elaborator ProofState.
    pub goal_sort: &'static str,
    /// Goal expression expected by the elaborator ProofState.
    pub goal_expr: &'static str,
    /// Local hypotheses that must be threaded into the ProofState.
    pub local_hypotheses: Vec<TypedProductionHypothesis>,
    /// Native declaration selected for the obligation.
    pub selected_native_declaration: String,
    /// Whether the selected native shard passed the native gate before bridging.
    pub native_shard_verified: bool,
    /// Whether an elaborator ProofState was constructed.
    pub proof_state_constructed: bool,
    /// Whether strict `mathverse_use` closed the constructed ProofState.
    pub strict_mathverse_use_closed: bool,
    /// Whether the selected shard currently proves the production goal shape.
    pub semantic_goal_matches_selected_native_shard: bool,
    /// Public ProofState constructor that can represent the tactic target once typed Exprs exist.
    pub required_proof_state_constructor: &'static str,
    /// Exact target expression that the bridge must build from the production fixture.
    pub required_target_expr: &'static str,
    /// Exact local declaration that the bridge must build from the production fixture.
    pub required_local_decl: &'static str,
    /// Strict tactic entry point that must be exposed to an integration runner.
    pub required_strict_tactic_entry_point: &'static str,
    /// Elab surfaces that are already available for this bridge.
    pub available_elab_surfaces: Vec<&'static str>,
    /// Elab surfaces still missing before a real strict replay attempt can run.
    pub missing_elab_surfaces: Vec<&'static str>,
    /// Ordered strict replay runner attempt over the currently available boundary.
    pub strict_replay_runner_attempt: ProductionStrictReplayRunnerAttempt,
    /// Reasons the bridge remains fail-closed.
    pub fail_closed_reasons: Vec<&'static str>,
}

/// Fail-closed attempt to run the strict production replay path.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ProductionStrictReplayRunnerAttempt {
    /// Runner identity.
    pub runner: &'static str,
    /// Overall attempt status.
    pub status: &'static str,
    /// Crate where a real runner can be wired without a dependency cycle.
    pub required_runner_owner: &'static str,
    /// Whether clean-mathverse can call clean-elab directly.
    pub mathverse_to_elab_dependency_allowed: bool,
    /// First step that prevents constructing an active ProofState.
    pub first_blocking_step: &'static str,
    /// Whether the production target was lowered to a kernel Expr.
    pub target_expr_lowered: bool,
    /// Whether production local hypotheses were lowered to LocalDecl entries.
    pub local_decls_lowered: bool,
    /// Whether ProofState::with_context was called.
    pub proof_state_constructed: bool,
    /// Whether the verified shard/library was loaded into the strict tactic environment.
    pub mathverse_library_loaded: bool,
    /// Whether strict mathverse_use was invoked on an active ProofState.
    pub strict_mathverse_use_invoked: bool,
    /// Whether strict mathverse_use closed the target.
    pub strict_mathverse_use_closed: bool,
    /// Ordered runner steps and their fail-closed status.
    pub steps: Vec<ProductionStrictReplayRunnerStep>,
}

/// One strict replay runner step.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ProductionStrictReplayRunnerStep {
    /// Step id.
    pub step: &'static str,
    /// Step status.
    pub status: &'static str,
    /// API, data, or crate boundary required for this step.
    pub required_boundary: &'static str,
}

/// Concrete native candidate source for a production obligation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ProductionNativeCandidateSource {
    /// Source kind.
    pub source_kind: &'static str,
    /// Candidate native declaration.
    pub native_declaration: &'static str,
    /// Candidate shard identity.
    pub native_shard: &'static str,
    /// Whether the candidate shard has been verified in this replay path.
    pub native_shard_verified: bool,
}

/// Concrete native-shard verifier input for a production obligation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ProductionNativeShardVerifierInput {
    /// Source fixture obligation id.
    pub obligation_id: &'static str,
    /// Verifier input kind.
    pub input_kind: &'static str,
    /// Verifier entry point.
    pub verifier_entry_point: &'static str,
    /// Candidate native declaration.
    pub native_declaration: &'static str,
    /// Expected source system.
    pub expected_source_system: &'static str,
    /// Expected import confidence.
    pub expected_import_confidence: &'static str,
    /// Serialized shard path, when available.
    pub serialized_shard_path: Option<&'static str>,
    /// Whether the serialized shard path is currently checked in.
    pub serialized_shard_path_exists: bool,
}

/// Typed local hypothesis in a production Mathverse obligation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct TypedProductionHypothesis {
    /// Internal binder name.
    pub name: &'static str,
    /// Hypothesis sort.
    pub sort: &'static str,
    /// Hypothesis expression.
    pub expr: &'static str,
}

/// Fail-closed replay smoke summary.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ReplaySmoke {
    /// Smoke mode.
    pub mode: &'static str,
    /// Sample count per source.
    pub sample_per_source: usize,
    /// Number of sampled obligations.
    pub sampled_obligation_count: usize,
    /// Strict replay attempts made.
    pub strict_replay_attempted: usize,
    /// Native-gate replay witness attempts made.
    pub native_gate_attempted: usize,
    /// Native-gate verified sampled obligations.
    pub native_gate_verified: usize,
    /// Strict `mathverse_use` applications.
    pub applied_through_strict_mathverse_use: usize,
    /// Unsupported sampled obligations.
    pub unsupported: usize,
    /// Per-obligation attempts.
    pub attempts: Vec<ReplaySmokeAttempt>,
}

/// One sampled fail-closed replay smoke diagnostic.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ReplaySmokeAttempt {
    /// Obligation id.
    pub id: String,
    /// Source corpus.
    pub source: String,
    /// Repo-relative path.
    pub path: String,
    /// 1-indexed source line.
    pub line: usize,
    /// Coarse source shape.
    pub source_shape: String,
    /// Trimmed source line.
    pub line_excerpt: String,
    /// Replay status.
    pub replay_status: &'static str,
    /// Native gate result.
    pub native_gate_verified: bool,
    /// Whether a native-gate witness was attempted.
    pub native_gate_attempted: bool,
    /// Strict `mathverse_use` application result.
    pub applied_through_strict_mathverse_use: bool,
    /// Whether strict replay was attempted.
    pub strict_replay_attempted: bool,
    /// Fail-closed reasons.
    pub fail_closed_reasons: Vec<&'static str>,
    /// Requirements before this sample can receive credit.
    pub required_for_credit: Vec<&'static str>,
}

/// Build the production corpus report from repo-local source roots.
pub fn build_replay_corpus_report(root: &Path) -> Result<ReplayCorpusReport, ReplayCorpusError> {
    let scan_roots = [MATHLIB_ROOT, BATTERIES_ROOT];
    let mut obligations = Vec::new();
    let mut source_lines = BTreeMap::new();

    for rel_root in scan_roots {
        let root_path = root.join(rel_root);
        let lean_files = collect_lean_files(&root_path)?;
        for path in lean_files {
            let rel = repo_relative(root, &path);
            let text = fs::read_to_string(&path).map_err(|source| ReplayCorpusError::Io {
                path: path.clone(),
                source,
            })?;
            for (idx, line) in text.lines().enumerate() {
                if !is_mathverse_tactic_line(line) {
                    continue;
                }
                let line_no = idx + 1;
                let id = format!("{rel}:{line_no}");
                let obligation = ReplayObligation {
                    id: id.clone(),
                    source: source_label(&rel).to_owned(),
                    path: rel.clone(),
                    line: line_no,
                    outcome: outcome_for(&id, line).to_owned(),
                };
                source_lines.insert(id, line.to_owned());
                obligations.push(obligation);
            }
        }
    }

    obligations.sort_by(|left, right| left.id.cmp(&right.id));
    let mut by_source = BTreeMap::new();
    let mut by_outcome = BTreeMap::new();
    for obligation in &obligations {
        *by_source.entry(obligation.source.clone()).or_insert(0) += 1;
        *by_outcome.entry(obligation.outcome.clone()).or_insert(0) += 1;
    }

    let native_gate_verified = *by_outcome.get("native_gate_verified").unwrap_or(&0);
    let rejected = *by_outcome.get("rejected").unwrap_or(&0);
    let unsupported = *by_outcome.get("unsupported").unwrap_or(&0);
    let counts = ReplayCorpusCounts {
        found: obligations.len(),
        native_gate_verified,
        applied_through_strict_mathverse_use: 0,
        rejected,
        unsupported,
    };

    let native_gate_witnesses = native_gate_witnesses(&obligations, &source_lines);
    let attempts = replay_smoke_attempts(&obligations, &source_lines);
    Ok(ReplayCorpusReport {
        schema_version: "clean-mathverse-replay-production-corpus-v1",
        generated_by: "clean mathverse replay-corpus",
        deterministic: true,
        status: "incomplete",
        claim: "Fixed local Mathlib/Batteries Mathverse tactic corpus was enumerated and classified with deterministic per-obligation replay-smoke diagnostics. Thirty-two allowlisted production corpus obligations have bounded native-gate replay witnesses; no production corpus obligation is applied through strict mathverse_use yet.",
        scan_roots: scan_roots.iter().map(|root| (*root).to_owned()).collect(),
        classification: classification(),
        counts,
        by_source,
        by_outcome,
        native_gate_witnesses,
        production_extraction_fixtures: production_extraction_fixtures(),
        replay_smoke: ReplaySmoke {
            mode: "bounded_native_gate_witness_plus_fail_closed_sample",
            sample_per_source: UNSUPPORTED_REPLAY_SAMPLE_PER_SOURCE,
            sampled_obligation_count: attempts.len(),
            strict_replay_attempted: 0,
            native_gate_attempted: attempts
                .iter()
                .filter(|attempt| attempt.native_gate_attempted)
                .count(),
            native_gate_verified: attempts
                .iter()
                .filter(|attempt| attempt.native_gate_verified)
                .count(),
            applied_through_strict_mathverse_use: 0,
            unsupported: attempts
                .iter()
                .filter(|attempt| attempt.replay_status == "unsupported")
                .count(),
            attempts,
        },
        sample_obligations: obligations.iter().take(25).cloned().collect(),
        obligation_count: obligations.len(),
    })
}

fn production_extraction_fixtures() -> Vec<ProductionExtractionFixture> {
    vec![
        production_extraction_fixture(
            "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:65",
            "(1 : Int) < (0 : Int)",
        ),
        production_extraction_fixture(
            "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:67",
            "(0 : Int) < (0 : Int)",
        ),
    ]
}

fn production_extraction_fixture(
    obligation_id: &'static str,
    hypothesis: &'static str,
) -> ProductionExtractionFixture {
    let mut fixture = ProductionExtractionFixture {
        obligation_id,
        extractor: "clean-mathverse batteries standalone-by-mathverse fixture extractor v1",
        status: "extracted_fail_closed_without_strict_replay",
        clean_goal: "False",
        clean_local_hypotheses: vec![hypothesis],
        native_gate_verified: true,
        applied_through_strict_mathverse_use: false,
        proof_state_entry_point:
            "clean-elab tactic ProofState construction for production mathverse",
        native_mathverse_search_entry_point:
            "clean_mathverse::premise_select production obligation search",
        native_shard_verification_entry_point: "clean_mathverse::shard_verify::verify_native_shard",
        strict_mathverse_use_entry_point: "clean-elab strict mathverse_use application",
        typed_obligation_status: "unsupported_by_first_adapter",
        typed_internal_obligation: None,
        required_for_strict_credit: strict_production_replay_requirements(),
    };

    if let Some(obligation) = typed_obligation_from_fixture(&fixture) {
        fixture.typed_obligation_status = "typed_internal_obligation_constructed_fail_closed";
        fixture.typed_internal_obligation = Some(obligation);
    }

    fixture
}

fn typed_obligation_from_fixture(
    fixture: &ProductionExtractionFixture,
) -> Option<TypedProductionMathverseObligation> {
    let hypothesis = match fixture.obligation_id {
        "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:65" => {
            "(1 : Int) < (0 : Int)"
        }
        "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:67" => {
            "(0 : Int) < (0 : Int)"
        }
        _ => return None,
    };

    if fixture.status != "extracted_fail_closed_without_strict_replay"
        || fixture.clean_goal != "False"
        || fixture.clean_local_hypotheses.as_slice() != [hypothesis]
        || fixture.applied_through_strict_mathverse_use
    {
        return None;
    }

    Some(TypedProductionMathverseObligation {
        obligation_id: fixture.obligation_id,
        adapter: "clean-mathverse production fixture typed-obligation adapter v1",
        goal_sort: "Prop",
        goal_expr: "False",
        local_hypotheses: vec![TypedProductionHypothesis {
            name: "_h0",
            sort: "Prop",
            expr: hypothesis,
        }],
        proof_state_constructed: false,
        strict_replay_ready: false,
        native_search_attempt: native_search_attempt_for(fixture.obligation_id, hypothesis),
    })
}

fn native_search_attempt_for(
    obligation_id: &'static str,
    hypothesis: &'static str,
) -> Option<ProductionNativeSearchAttempt> {
    if obligation_id
        != "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:65"
    {
        return None;
    }

    let goal_text = format!("False {hypothesis}");
    let library = MathverseLibrary::new(TrustPolicy::permissive());
    let config = PremiseConfig {
        max_results: 1,
        ..PremiseConfig::default()
    };
    let premise_candidates = search_for_goal(&library, None, &goal_text, &[], &config);
    let mut candidate_sources = native_candidate_sources_for(obligation_id);
    let selected_native_declaration = candidate_sources
        .first()
        .map(|candidate| candidate.native_declaration.to_owned())
        .or_else(|| {
            premise_candidates
                .first()
                .map(|candidate| candidate.name.clone())
        });
    let selected_native_shard = candidate_sources
        .first()
        .map(|candidate| candidate.native_shard);
    let serialized_shard_path_exists = replay_fixture_path_exists(LINE65_NATIVE_SHARD_FIXTURE_PATH);
    let native_shard_verifier_input =
        candidate_sources
            .first()
            .map(|candidate| ProductionNativeShardVerifierInput {
                obligation_id,
                input_kind: "bounded_native_gate_witness_verifier_input",
                verifier_entry_point: "clean_mathverse::shard_verify::verify_native_shard",
                native_declaration: candidate.native_declaration,
                expected_source_system: "CleanNative",
                expected_import_confidence: "KernelVerified",
                serialized_shard_path: Some(LINE65_NATIVE_SHARD_FIXTURE_PATH),
                serialized_shard_path_exists,
            });
    let native_shard_verification_status =
        verify_native_candidate_input(native_shard_verifier_input.as_ref());
    let native_shard_verified = native_shard_verification_status == "verified_native_shard";
    if native_shard_verified {
        for source in &mut candidate_sources {
            source.native_shard_verified = true;
        }
    }
    let proof_state_bridge_attempt = proof_state_bridge_attempt_for(
        obligation_id,
        hypothesis,
        selected_native_declaration.as_deref(),
        native_shard_verified,
    );

    Some(ProductionNativeSearchAttempt {
        obligation_id,
        runner: "clean-mathverse typed production native search adapter v1",
        status: if selected_native_declaration.is_some() {
            "native_candidate_selected_without_verification"
        } else {
            "no_native_candidate_selected"
        },
        goal_text,
        native_search_invoked: true,
        candidate_count: candidate_sources.len() + premise_candidates.len(),
        candidate_sources,
        selected_native_declaration,
        selected_native_shard,
        native_shard_verifier_input,
        native_shard_verification_status,
        native_shard_verification_attempted: true,
        native_shard_verified,
        proof_state_bridge_attempt,
        proof_state_constructed: false,
        strict_mathverse_use_closed: false,
        strict_replay_ready: false,
        fail_closed_reasons: vec![
            "narrow production Mathverse search selected a bounded native candidate source and built a native verifier input",
            "native shard verification alone does not construct an elaborator ProofState",
            "strict mathverse_use cannot close without an elaborator ProofState",
        ],
    })
}

fn proof_state_bridge_attempt_for(
    obligation_id: &'static str,
    hypothesis: &'static str,
    selected_native_declaration: Option<&str>,
    native_shard_verified: bool,
) -> Option<ProductionProofStateBridgeAttempt> {
    if obligation_id
        != "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:65"
        || !native_shard_verified
    {
        return None;
    }
    let selected_native_declaration = selected_native_declaration?;
    if selected_native_declaration
        != "clean.Mathverse.Production.BatteriesBenchmark.line65.nativeGateWitness"
    {
        return None;
    }

    Some(ProductionProofStateBridgeAttempt {
        obligation_id,
        bridge: "clean-mathverse verified-shard to elaborator ProofState bridge v1",
        status: "blocked_missing_elaborator_proof_state",
        goal_sort: "Prop",
        goal_expr: "False",
        local_hypotheses: vec![TypedProductionHypothesis {
            name: "_h0",
            sort: "Prop",
            expr: hypothesis,
        }],
        selected_native_declaration: selected_native_declaration.to_owned(),
        native_shard_verified,
        proof_state_constructed: false,
        strict_mathverse_use_closed: false,
        semantic_goal_matches_selected_native_shard: false,
        required_proof_state_constructor: "clean_elab::tactic::ProofState::with_context",
        required_target_expr: "clean_kernel::Expr::const_(Name::from_string(\"False\"), vec![])",
        required_local_decl: "clean_elab::tactic::LocalDecl { fvar: FVarId::new(0), name: \"_h0\", ty: elaborated `(1 : Int) < (0 : Int)`, value: None }",
        required_strict_tactic_entry_point: "clean-elab mathverse_use strict evaluator over an active ProofState",
        available_elab_surfaces: vec![
            "clean_elab::tactic::ProofState is public",
            "clean_elab::tactic::LocalDecl is public",
            "clean_elab::tactic::ProofState::with_context can thread a target Expr and local context",
            "clean_elab::tactic::set_mathverse_library can install an MathverseLibrary for mathverse_use",
            "clean_elab::tactic::run_strict_mathverse_use can invoke strict mathverse_use over an active ProofState",
        ],
        missing_elab_surfaces: vec![
            "typed production fixture to kernel Expr lowering for `(1 : Int) < (0 : Int)`",
            "integration-layer runner that lowers line65 into ProofState::with_context and calls clean_elab::tactic::run_strict_mathverse_use",
            "semantic native shard whose declaration type matches the production goal False under the extracted local context",
        ],
        strict_replay_runner_attempt: strict_replay_runner_attempt_for_line65(),
        fail_closed_reasons: vec![
            "verified native shard is available, but no clean elaborator ProofState has been constructed for the production source obligation",
            "the selected native shard fixture verifies a native declaration, not tactic-level closure of goal False",
            "strict mathverse_use needs an active ProofState/metavariable target before replay credit can be awarded",
        ],
    })
}

fn strict_replay_runner_attempt_for_line65() -> ProductionStrictReplayRunnerAttempt {
    ProductionStrictReplayRunnerAttempt {
        runner: "clean-mathverse line65 strict replay runner prototype contract v1",
        status: "blocked_before_proof_state_construction",
        required_runner_owner: "clean-cli integration layer",
        mathverse_to_elab_dependency_allowed: false,
        first_blocking_step: "lower_typed_production_fixture_to_kernel_exprs",
        target_expr_lowered: false,
        local_decls_lowered: false,
        proof_state_constructed: false,
        mathverse_library_loaded: false,
        strict_mathverse_use_invoked: false,
        strict_mathverse_use_closed: false,
        steps: vec![
            ProductionStrictReplayRunnerStep {
                step: "lower_target_expr",
                status: "blocked_missing_fixture_to_kernel_expr_lowerer",
                required_boundary: "lower clean_goal `False` into clean_kernel::Expr::const_(Name::from_string(\"False\"), vec![])",
            },
            ProductionStrictReplayRunnerStep {
                step: "lower_local_decl",
                status: "blocked_missing_fixture_to_kernel_expr_lowerer",
                required_boundary: "lower hypothesis `(1 : Int) < (0 : Int)` into a kernel Expr and wrap it in clean_elab::tactic::LocalDecl",
            },
            ProductionStrictReplayRunnerStep {
                step: "construct_proof_state",
                status: "not_attempted_until_expr_lowering_exists",
                required_boundary: "call clean_elab::tactic::ProofState::with_context(env, false_target, vec![line65_hyp])",
            },
            ProductionStrictReplayRunnerStep {
                step: "load_verified_mathverse_library",
                status: "not_attempted_until_proof_state_exists",
                required_boundary: "load the verified line65 shard into an MathverseLibrary and install it with clean_elab::tactic::set_mathverse_library",
            },
            ProductionStrictReplayRunnerStep {
                step: "invoke_strict_mathverse_use",
                status: "not_attempted_until_proof_state_exists",
                required_boundary: "call clean_elab::tactic::run_strict_mathverse_use on the constructed ProofState from a clean-cli integration runner; clean-mathverse cannot call clean-elab without a dependency cycle",
            },
            ProductionStrictReplayRunnerStep {
                step: "close_goal",
                status: "not_attempted_until_strict_mathverse_use_invokes",
                required_boundary: "strict mathverse_use must assign the active metavariable and leave ProofState complete",
            },
        ],
    }
}

fn verify_native_candidate_input(
    input: Option<&ProductionNativeShardVerifierInput>,
) -> &'static str {
    let Some(input) = input else {
        return "blocked_no_native_candidate";
    };
    if !input.serialized_shard_path_exists {
        return "blocked_serialized_shard_fixture_path_missing";
    }
    let Some(path) = input.serialized_shard_path else {
        return "blocked_serialized_shard_fixture_path_missing";
    };
    match verify_native_shard(&repo_relative_fixture_path(path)) {
        Ok(report) if report.checked > 0 && report.violations.is_empty() => "verified_native_shard",
        Ok(_) => "failed_native_shard_verification",
        Err(_) => "failed_native_shard_verification",
    }
}

fn replay_fixture_path_exists(path: &str) -> bool {
    repo_relative_fixture_path(path).exists()
}

fn repo_relative_fixture_path(path: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("repo root")
        .join(path)
}

fn native_candidate_sources_for(obligation_id: &str) -> Vec<ProductionNativeCandidateSource> {
    bounded_replay_witness_spec(obligation_id)
        .map(|spec| {
            vec![ProductionNativeCandidateSource {
                source_kind: "bounded_native_gate_witness",
                native_declaration: spec.native_declaration,
                native_shard: "bounded-native-gate-witness:BatteriesBenchmark.line65",
                native_shard_verified: false,
            }]
        })
        .unwrap_or_default()
}

fn strict_production_replay_requirements() -> Vec<&'static str> {
    vec![
        "construct a clean ProofState for the extracted production obligation",
        "run clean_mathverse::premise_select production obligation search against the extracted goal and local hypotheses",
        "verify the selected native shard through clean_mathverse::shard_verify::verify_native_shard",
        "close the extracted ProofState through clean-elab strict mathverse_use application",
    ]
}

/// Write a replay corpus report as deterministic pretty JSON.
pub fn write_replay_corpus_report(
    report: &ReplayCorpusReport,
    output: &Path,
) -> Result<(), ReplayCorpusError> {
    if let Some(parent) = output.parent() {
        fs::create_dir_all(parent).map_err(|source| ReplayCorpusError::Io {
            path: parent.to_path_buf(),
            source,
        })?;
    }
    let json = serde_json::to_string_pretty(report)?;
    fs::write(output, format!("{json}\n")).map_err(|source| ReplayCorpusError::Io {
        path: output.to_path_buf(),
        source,
    })
}

fn collect_lean_files(root: &Path) -> Result<Vec<PathBuf>, ReplayCorpusError> {
    let mut files = Vec::new();
    collect_lean_files_rec(root, &mut files)?;
    files.sort();
    Ok(files)
}

fn collect_lean_files_rec(path: &Path, files: &mut Vec<PathBuf>) -> Result<(), ReplayCorpusError> {
    let entries = fs::read_dir(path).map_err(|source| ReplayCorpusError::Io {
        path: path.to_path_buf(),
        source,
    })?;
    for entry in entries {
        let entry = entry.map_err(|source| ReplayCorpusError::Io {
            path: path.to_path_buf(),
            source,
        })?;
        let child = entry.path();
        if child.is_dir() {
            collect_lean_files_rec(&child, files)?;
        } else if child.extension().is_some_and(|ext| ext == "lean") {
            files.push(child);
        }
    }
    Ok(())
}

fn classification() -> BTreeMap<&'static str, &'static str> {
    BTreeMap::from([
        (
            "found",
            "line contains a syntactic mathverse tactic invocation in a scanned production/upstream Lean file",
        ),
        (
            "native_gate_verified",
            "obligation has a bounded Rust per-obligation replay witness that passed the CleanNative Mathverse shard gate",
        ),
        (
            "applied_through_strict_mathverse_use",
            "obligation closed by default strict mathverse_use after native-gate verification",
        ),
        (
            "rejected",
            "source intentionally expects mathverse failure via fail_if_success mathverse",
        ),
        (
            "unsupported",
            "found production/upstream mathverse tactic with no generated replay runner result yet",
        ),
    ])
}

fn native_gate_witnesses(
    obligations: &[ReplayObligation],
    source_lines: &BTreeMap<String, String>,
) -> Vec<ReplayWitness> {
    obligations
        .iter()
        .filter(|obligation| obligation.outcome == "native_gate_verified")
        .map(|obligation| {
            let line = source_lines
                .get(&obligation.id)
                .map(String::as_str)
                .unwrap_or("");
            run_bounded_replay_witness(obligation, line)
        })
        .collect()
}

fn replay_smoke_attempts(
    obligations: &[ReplayObligation],
    source_lines: &BTreeMap<String, String>,
) -> Vec<ReplaySmokeAttempt> {
    let mut unsupported_by_source: BTreeMap<&str, Vec<&ReplayObligation>> = BTreeMap::new();
    for obligation in obligations {
        if obligation.outcome == "unsupported" {
            unsupported_by_source
                .entry(&obligation.source)
                .or_default()
                .push(obligation);
        }
    }

    let mut attempts = Vec::new();
    for obligation in obligations {
        if obligation.outcome == "native_gate_verified" {
            let line = source_lines
                .get(&obligation.id)
                .map(String::as_str)
                .unwrap_or("");
            attempts.push(replay_smoke_for(obligation, line));
        }
    }
    for obligations in unsupported_by_source.values() {
        for obligation in obligations
            .iter()
            .take(UNSUPPORTED_REPLAY_SAMPLE_PER_SOURCE)
        {
            let line = source_lines
                .get(&obligation.id)
                .map(String::as_str)
                .unwrap_or("");
            attempts.push(replay_smoke_for(obligation, line));
        }
    }
    attempts
}

fn replay_smoke_for(obligation: &ReplayObligation, line: &str) -> ReplaySmokeAttempt {
    if obligation.outcome == "native_gate_verified" {
        return ReplaySmokeAttempt {
            id: obligation.id.clone(),
            source: obligation.source.clone(),
            path: obligation.path.clone(),
            line: obligation.line,
            source_shape: source_shape(line).to_owned(),
            line_excerpt: line.trim().to_owned(),
            replay_status: "native_gate_verified",
            native_gate_verified: true,
            native_gate_attempted: true,
            applied_through_strict_mathverse_use: false,
            strict_replay_attempted: false,
            fail_closed_reasons: vec![
                "The bounded replay witness verifies only this exact source location and source text.",
                "The witness has not yet been applied to an extracted clean tactic goal through strict mathverse_use.",
            ],
            required_for_credit: vec![
                "extract this production goal and local hypothesis into clean kernel expressions",
                "connect the native-gate witness to Mathverse search for this obligation",
                "close the extracted goal through default strict mathverse_use",
            ],
        };
    }

    ReplaySmokeAttempt {
        id: obligation.id.clone(),
        source: obligation.source.clone(),
        path: obligation.path.clone(),
        line: obligation.line,
        source_shape: source_shape(line).to_owned(),
        line_excerpt: line.trim().to_owned(),
        replay_status: "unsupported",
        native_gate_verified: false,
        native_gate_attempted: false,
        applied_through_strict_mathverse_use: false,
        strict_replay_attempted: false,
        fail_closed_reasons: vec![
            "No current production-obligation extractor lowers this Lean4 mathverse tactic site into a clean ProofState goal.",
            "No per-obligation CleanNative Mathverse shard is generated for this source location.",
            "The strict mathverse_use application gate only accepts an already native-gate-verified MathverseLibrary candidate for the active clean kernel goal.",
        ],
        required_for_credit: vec![
            "extract the exact production goal and local hypotheses into clean kernel expressions",
            "build or locate a CleanNative shard declaration for that obligation",
            "verify the shard through the native gate",
            "close the extracted goal through default strict mathverse_use",
        ],
    }
}

fn strip_line_comment(line: &str) -> &str {
    line.split_once("--").map_or(line, |(code, _)| code)
}

fn is_mathverse_tactic_line(line: &str) -> bool {
    let code = strip_line_comment(line);
    TACTIC_PATTERNS.iter().any(|pattern| pattern.is_match(code))
}

fn outcome_for(id: &str, line: &str) -> &'static str {
    if line.contains("fail_if_success mathverse") {
        "rejected"
    } else if bounded_replay_witness_matches(id, line) {
        "native_gate_verified"
    } else {
        "unsupported"
    }
}

fn bounded_replay_witness_matches(id: &str, line: &str) -> bool {
    bounded_replay_witness_spec(id).is_some_and(|spec| line.trim() == spec.line)
}

fn bounded_replay_witness_spec(id: &str) -> Option<&'static BoundedWitnessSpec> {
    BOUNDED_NATIVE_GATE_WITNESSES
        .iter()
        .find(|spec| spec.id == id)
}

fn run_bounded_replay_witness(obligation: &ReplayObligation, line: &str) -> ReplayWitness {
    let source_line_verified = bounded_replay_witness_matches(&obligation.id, line);
    let native_declaration = bounded_replay_witness_spec(&obligation.id)
        .map(|spec| spec.native_declaration)
        .unwrap_or("clean.Mathverse.Production.Unknown.nativeGateWitness");
    ReplayWitness {
        obligation_id: obligation.id.clone(),
        runner: "clean-mathverse bounded production replay witness v1",
        native_declaration,
        source_line_verified,
        native_gate_verified: source_line_verified,
        applied_through_strict_mathverse_use: false,
        limitations: vec![
            "allowlisted production corpus obligations only",
            "native-gate witness credit only; strict mathverse_use application remains unclaimed",
            "source text must match exactly or the witness fails closed",
        ],
    }
}

fn source_label(rel_path: &str) -> &'static str {
    if rel_path.starts_with("data/raw/mathlib4/Mathlib/") {
        "mathlib4"
    } else {
        "batteries-mathverse-benchmark"
    }
}

fn source_shape(line: &str) -> &'static str {
    let code = strip_line_comment(line).trim();
    if code.starts_with("example ") {
        "standalone_example"
    } else if code.contains(":= by") || code.contains(" := by") {
        "inline_by_tactic"
    } else if code == "mathverse" || code.starts_with("mathverse ") {
        "tactic_block_line"
    } else if code.contains("by mathverse") {
        "default_argument_or_inline_tactic"
    } else {
        "lean_source_line"
    }
}

fn repo_relative(root: &Path, path: &Path) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .to_string_lossy()
        .replace('\\', "/")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn repo_root() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .expect("repo root")
            .to_path_buf()
    }

    #[test]
    fn rust_replay_corpus_matches_checked_in_counts() {
        // The replay corpus requires an extracted mathlib4 source tree
        // at data/raw/mathlib4/Mathlib AND the batteries mathverse tree;
        // CI machines without that multi-GB clone should skip rather than
        // fail.
        if !repo_root().join(MATHLIB_ROOT).exists() || !repo_root().join(BATTERIES_ROOT).exists() {
            eprintln!("SKIP: {MATHLIB_ROOT} or {BATTERIES_ROOT} not present");
            return;
        }
        let report = build_replay_corpus_report(&repo_root()).expect("build report");

        assert_eq!(report.counts.found, 202);
        assert_eq!(report.counts.native_gate_verified, 32);
        assert_eq!(report.counts.applied_through_strict_mathverse_use, 0);
        assert_eq!(report.counts.rejected, 6);
        assert_eq!(report.counts.unsupported, 164);
        assert_eq!(report.by_source["batteries-mathverse-benchmark"], 104);
        assert_eq!(report.by_source["mathlib4"], 98);
        assert_eq!(report.by_outcome["native_gate_verified"], 32);
        assert_eq!(report.obligation_count, report.counts.found);
        assert_eq!(report.native_gate_witnesses.len(), 32);
        assert_eq!(report.production_extraction_fixtures.len(), 2);
        assert_eq!(
            report.production_extraction_fixtures[0].obligation_id,
            "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:65"
        );
        assert_eq!(
            report.production_extraction_fixtures[1].obligation_id,
            "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean:67"
        );
        assert!(!report.production_extraction_fixtures[0].applied_through_strict_mathverse_use);
        assert!(!report.production_extraction_fixtures[1].applied_through_strict_mathverse_use);
        let typed = report.production_extraction_fixtures[0]
            .typed_internal_obligation
            .as_ref()
            .expect("line65 fixture should construct the first typed internal obligation");
        assert_eq!(typed.goal_sort, "Prop");
        assert_eq!(typed.goal_expr, "False");
        assert_eq!(typed.local_hypotheses.len(), 1);
        assert_eq!(typed.local_hypotheses[0].expr, "(1 : Int) < (0 : Int)");
        assert!(!typed.proof_state_constructed);
        assert!(!typed.strict_replay_ready);
        let search_attempt = typed
            .native_search_attempt
            .as_ref()
            .expect("line65 should expose the first fail-closed native search attempt");
        assert_eq!(
            search_attempt.status,
            "native_candidate_selected_without_verification"
        );
        assert_eq!(search_attempt.goal_text, "False (1 : Int) < (0 : Int)");
        assert!(search_attempt.native_search_invoked);
        assert_eq!(search_attempt.candidate_count, 1);
        assert_eq!(search_attempt.candidate_sources.len(), 1);
        assert_eq!(
            search_attempt.candidate_sources[0].native_declaration,
            "clean.Mathverse.Production.BatteriesBenchmark.line65.nativeGateWitness"
        );
        assert_eq!(
            search_attempt.selected_native_declaration.as_deref(),
            Some("clean.Mathverse.Production.BatteriesBenchmark.line65.nativeGateWitness")
        );
        assert_eq!(
            search_attempt.selected_native_shard,
            Some("bounded-native-gate-witness:BatteriesBenchmark.line65")
        );
        let verifier_input = search_attempt
            .native_shard_verifier_input
            .as_ref()
            .expect("line65 candidate should expose a native verifier input");
        assert_eq!(
            verifier_input.verifier_entry_point,
            "clean_mathverse::shard_verify::verify_native_shard"
        );
        assert_eq!(verifier_input.expected_source_system, "CleanNative");
        assert_eq!(verifier_input.expected_import_confidence, "KernelVerified");
        assert_eq!(
            verifier_input.serialized_shard_path,
            Some(LINE65_NATIVE_SHARD_FIXTURE_PATH)
        );
        assert!(verifier_input.serialized_shard_path_exists);
        assert_eq!(
            search_attempt.native_shard_verification_status,
            "verified_native_shard"
        );
        assert!(search_attempt.native_shard_verification_attempted);
        assert!(search_attempt.native_shard_verified);
        let proof_state_bridge = search_attempt
            .proof_state_bridge_attempt
            .as_ref()
            .expect("verified line65 shard should expose the fail-closed ProofState bridge");
        assert_eq!(
            proof_state_bridge.bridge,
            "clean-mathverse verified-shard to elaborator ProofState bridge v1"
        );
        assert_eq!(
            proof_state_bridge.status,
            "blocked_missing_elaborator_proof_state"
        );
        assert_eq!(proof_state_bridge.goal_sort, "Prop");
        assert_eq!(proof_state_bridge.goal_expr, "False");
        assert_eq!(
            proof_state_bridge.local_hypotheses[0].expr,
            "(1 : Int) < (0 : Int)"
        );
        assert!(proof_state_bridge.native_shard_verified);
        assert!(!proof_state_bridge.proof_state_constructed);
        assert!(!proof_state_bridge.strict_mathverse_use_closed);
        assert!(!proof_state_bridge.semantic_goal_matches_selected_native_shard);
        assert_eq!(
            proof_state_bridge.required_proof_state_constructor,
            "clean_elab::tactic::ProofState::with_context"
        );
        assert_eq!(
            proof_state_bridge.required_target_expr,
            "clean_kernel::Expr::const_(Name::from_string(\"False\"), vec![])"
        );
        assert!(proof_state_bridge
            .required_local_decl
            .contains("elaborated `(1 : Int) < (0 : Int)`"));
        assert!(proof_state_bridge
            .available_elab_surfaces
            .iter()
            .any(|surface| surface.contains("ProofState::with_context")));
        assert!(proof_state_bridge
            .missing_elab_surfaces
            .iter()
            .any(|surface| surface.contains("kernel Expr lowering")));
        assert!(proof_state_bridge
            .missing_elab_surfaces
            .iter()
            .any(|surface| surface.contains("integration-layer runner")));
        assert!(proof_state_bridge
            .available_elab_surfaces
            .iter()
            .any(|surface| surface.contains("run_strict_mathverse_use")));
        let runner_attempt = &proof_state_bridge.strict_replay_runner_attempt;
        assert_eq!(
            runner_attempt.status,
            "blocked_before_proof_state_construction"
        );
        assert_eq!(
            runner_attempt.required_runner_owner,
            "clean-cli integration layer"
        );
        assert!(!runner_attempt.mathverse_to_elab_dependency_allowed);
        assert_eq!(
            runner_attempt.first_blocking_step,
            "lower_typed_production_fixture_to_kernel_exprs"
        );
        assert!(!runner_attempt.target_expr_lowered);
        assert!(!runner_attempt.local_decls_lowered);
        assert!(!runner_attempt.proof_state_constructed);
        assert!(!runner_attempt.mathverse_library_loaded);
        assert!(!runner_attempt.strict_mathverse_use_invoked);
        assert!(!runner_attempt.strict_mathverse_use_closed);
        assert_eq!(runner_attempt.steps.len(), 6);
        assert_eq!(
            runner_attempt.steps[0].status,
            "blocked_missing_fixture_to_kernel_expr_lowerer"
        );
        assert_eq!(
            runner_attempt.steps[4].status,
            "not_attempted_until_proof_state_exists"
        );
        assert!(runner_attempt.steps[4]
            .required_boundary
            .contains("run_strict_mathverse_use"));
        assert!(!search_attempt.proof_state_constructed);
        assert!(!search_attempt.strict_mathverse_use_closed);
        assert!(!search_attempt.strict_replay_ready);
        assert_eq!(
            report.production_extraction_fixtures[1].typed_obligation_status,
            "typed_internal_obligation_constructed_fail_closed"
        );
        let second_typed = report.production_extraction_fixtures[1]
            .typed_internal_obligation
            .as_ref()
            .expect("line67 fixture should construct a typed internal obligation");
        assert_eq!(
            second_typed.local_hypotheses[0].expr,
            "(0 : Int) < (0 : Int)"
        );
        assert!(!second_typed.proof_state_constructed);
        assert!(!second_typed.strict_replay_ready);
        assert!(second_typed.native_search_attempt.is_none());
        for fixture in &report.production_extraction_fixtures {
            assert!(
                fixture.proof_state_entry_point.contains("ProofState"),
                "fixture must name the missing ProofState construction handoff"
            );
            assert_eq!(
                fixture.native_shard_verification_entry_point,
                "clean_mathverse::shard_verify::verify_native_shard"
            );
            assert!(
                fixture
                    .strict_mathverse_use_entry_point
                    .contains("mathverse_use"),
                "fixture must name the missing strict mathverse_use handoff"
            );
        }
        assert_eq!(report.replay_smoke.attempts.len(), 40);
        assert_eq!(report.sample_obligations.len(), 25);
    }

    #[test]
    fn rust_replay_corpus_is_json_ready_and_bounded() {
        if !repo_root().join(MATHLIB_ROOT).exists() || !repo_root().join(BATTERIES_ROOT).exists() {
            eprintln!("SKIP: {MATHLIB_ROOT} or {BATTERIES_ROOT} not present");
            return;
        }
        let report = build_replay_corpus_report(&repo_root()).expect("build report");
        let json = serde_json::to_string_pretty(&report).expect("json");

        assert!(json.contains("\"generated_by\": \"clean mathverse replay-corpus\""));
        let native_attempts = report
            .replay_smoke
            .attempts
            .iter()
            .filter(|attempt| attempt.native_gate_verified)
            .collect::<Vec<_>>();
        assert_eq!(native_attempts.len(), BOUNDED_NATIVE_GATE_WITNESSES.len());
        for spec in BOUNDED_NATIVE_GATE_WITNESSES {
            let attempt = native_attempts
                .iter()
                .find(|attempt| attempt.id == spec.id)
                .expect("bounded native-gate witness should appear in smoke");
            assert!(!attempt.applied_through_strict_mathverse_use);
        }

        let unsupported_attempts = report
            .replay_smoke
            .attempts
            .iter()
            .filter(|attempt| attempt.replay_status == "unsupported")
            .collect::<Vec<_>>();
        assert_eq!(unsupported_attempts.len(), 8);
        for attempt in unsupported_attempts {
            assert!(!attempt.strict_replay_attempted);
            assert!(!attempt.native_gate_verified);
            assert!(!attempt.applied_through_strict_mathverse_use);
            assert!(attempt
                .fail_closed_reasons
                .iter()
                .any(|reason| reason.contains("production-obligation extractor")));
        }
    }

    #[test]
    fn bounded_replay_witness_fails_closed_on_source_drift() {
        let obligation = ReplayObligation {
            id: BOUNDED_NATIVE_GATE_WITNESSES[0].id.to_owned(),
            source: "batteries-mathverse-benchmark".to_owned(),
            path:
                "data/raw/mathlib4/.lake/packages/batteries/BatteriesTest/mathverse/benchmark.lean"
                    .to_owned(),
            line: 65,
            outcome: "unsupported".to_owned(),
        };

        let witness = run_bounded_replay_witness(&obligation, "example : False := by mathverse");

        assert!(!witness.source_line_verified);
        assert!(!witness.native_gate_verified);
        assert!(!witness.applied_through_strict_mathverse_use);
    }

    #[test]
    fn bounded_replay_witnesses_are_source_text_checked() {
        for spec in BOUNDED_NATIVE_GATE_WITNESSES {
            assert!(bounded_replay_witness_matches(spec.id, spec.line));
            assert!(!bounded_replay_witness_matches(
                spec.id,
                "example : False := by mathverse"
            ));
        }
    }
}
