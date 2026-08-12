// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! AI-driven proof discovery loop for clean.
//!
//! Uses the kernel's sub-microsecond type checking to evaluate millions of
//! candidate theorem-proof pairs per second, searching for novel mathematical
//! results about neural network verification.
//!
//! # Architecture
//!
//! 1. **Candidate Generator** produces parameterized theorem statements, each
//!    with a genuine proof term when (and only when) the loop can construct one.
//! 2. **Kernel Verifier** GENUINELY checks each candidate: it infers the proof
//!    term's type and requires it to be definitionally equal to the claimed
//!    statement (`TypeChecker::check_type` = `infer_type()` + `is_def_eq()`). A
//!    proof that is merely well-typed but does not have the statement as its type
//!    is REJECTED, and a candidate with no proof is honestly Unverified.
//! 3. **Search Runner** orchestrates exhaustive or guided search over parameter spaces
//!
//! Part of #3258.

pub mod abstract_domain;
pub mod candidate;
pub mod cli;
pub mod complexity;
pub mod dependency_tracker;
pub mod discovery_loop;
pub mod discovery_stats;
pub mod error;
pub mod exploration;
pub mod exploration_patterns;
pub mod family;
pub mod feedback;
pub mod feedback_loop;
pub mod goal_features;
pub mod lemma_library;
pub mod novelty;
#[cfg(feature = "oracle")]
pub mod oracle;
pub mod proof_repair;
pub mod relaxation;
pub mod relaxation_params;
pub mod reporting;
pub mod result_store;
pub mod runner;
pub(crate) mod scoring;
pub mod search;
pub mod tactic_learning;
pub mod tactic_recommender;
pub mod tightness;

pub use candidate::CandidateTheorem;
pub use dependency_tracker::{extract_dependencies, DependencyGraph};
pub use discovery_loop::{DiscoveryLoop, DiscoveryLoopConfig, DiscoveryLoopResult};
pub use discovery_stats::{DiscoveryStats, StatsReport};
pub use error::DiscoveryError;
pub use exploration::{
    CounterexampleFilter, ExplorationConfig, ExplorationResult, ExplorationRunner, ExplorationState,
};
pub use exploration_patterns::{FuncSig, TermPattern};
pub use family::TheoremFamily;
pub use feedback::{FeedbackAnalyzer, FeedbackCategory, FeedbackEntry, FeedbackSummary};
pub use feedback_loop::{AdjustDirection, AdjustmentSummary, CandidateAdjustment, FeedbackLoop};
pub use goal_features::{extract_goal_features, ArgTypeTag, FeatureVector, GoalFeatures};
pub use lemma_library::{compute_content_hash, LemmaEntry, LemmaLibrary};
pub use novelty::{NoveltyFilter, NoveltyScore};
pub use proof_repair::{
    ChangeKind, ChangedDefinition, ProofRepairer, RepairOutcome, RepairResult, RepairStrategy,
};
pub use runner::DiscoveryRunner;
pub use search::{ExhaustiveSearch, SearchResult, SearchStats};
pub use tactic_learning::{TacticCorpus, TacticRecommendation, TacticRecord, TacticSequence};
pub use tactic_recommender::{CorpusBuilder, KnnRecommender};
