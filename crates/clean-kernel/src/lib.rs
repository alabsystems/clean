// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

#![cfg_attr(not(kani), forbid(unsafe_code))]
// Trust verification: register the `trust` tool namespace so `#[trust::skip]`
// (and other `#[trust::…]` attributes) are accepted under the trust-verify build
// (`--cfg trust_verify`, set by `targo trust survey --contracts`). Gated on
// `trust_verify` so ordinary stable builds — which don't enable the nightly
// `register_tool` feature — are completely unaffected.
#![cfg_attr(trust_verify, feature(register_tool))]
#![cfg_attr(trust_verify, register_tool(trust))]
// The kernel intentionally compiles staged proof/checker APIs before every
// downstream call path is wired; keep consumer builds quiet while narrower
// hygiene lints remain active.
//! clean Kernel - Trusted Type Checker
//!
//! This crate implements the core type checking algorithm for clean.
//! It is the trusted computing base - all proofs ultimately reduce to
//! kernel type checking.
//!
//! # Architecture
//!
//! The kernel consists of:
//! - Expression representation (`expr/`)
//! - Universe levels (`level.rs`)
//! - Environment with declarations (`env/`)
//! - Type checker (`tc/`)
//! - Definitional equality / conversion (`tc/def_eq/`)
//! - Inductive types (`inductive.rs`)
//! - Certificate verification (`cert` module)
//! - Micro-checker (`micro` module)
//!
//! Certificate and micro-checker APIs are namespaced under `clean_kernel::cert`
//! and `clean_kernel::micro` (they are not re-exported at the crate root).
//!
//! # Performance
//!
//! The kernel is designed for maximum performance:
//! - Expression nodes (136 bytes; boxed variants limit stack pressure)
//! - Arena allocation
//! - Hash consing for structural sharing
//! - Aggressive caching of type inference results

/// clean-kernel crate version (`CARGO_PKG_VERSION`). Exposed so downstream tools
/// can record the exact kernel revision a verdict was produced under (e.g. the
/// reproducibility fingerprint in `clean-mathverse`'s KernelVerifiedManifest).
/// Pure metadata — never read by the type checker.
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

#[cfg(test)]
pub(crate) mod beta_congruence;
pub mod bitvec_coercion;
pub mod bitvec_compute;
pub mod bitvec_inductive;
pub mod bitvec_slice;
pub mod bool_model;
pub mod cache;
#[cfg(test)]
mod cache_tests;
pub mod cert;
pub mod cfg;
#[cfg(feature = "cli")]
pub mod cli;
#[cfg(any(test, feature = "proof-import"))]
pub mod coq_import;
#[cfg(feature = "test-utils")]
pub mod differential_baseline;
pub mod env;
pub mod expr;
pub mod flat;
#[cfg(any(test, feature = "proof-import"))]
pub mod hol_light_import;
pub mod inductive;
pub mod level;
#[cfg(test)]
mod level_scaling_tests;
pub mod lrat_check;
pub mod lrat_soundness;
pub mod memory_model;
pub mod metamath_reflect;
pub mod micro;
#[cfg(any(test, kani))]
pub(crate) mod micro_contracts;
pub mod mode;
pub mod name;
#[cfg(any(test, feature = "proof-import"))]
pub mod open_theory;
pub mod resolution_check;
pub mod resolution_soundness;
mod serde_budget;
#[cfg(any(test, feature = "proof-import"))]
pub use open_theory as opentheory;
pub mod quot;
pub mod sem_memory_model;
pub mod sem_memory_trait;
pub mod separation_logic;
pub mod sorry;
pub mod tc; // Type checker (definitional equality, WHNF, type inference)
#[cfg(any(test, feature = "test-utils"))]
pub mod test_utils;
pub mod vc_protocol;
pub mod verify_api;

pub use env::proof_search::{search_proof, ProofSearchResult};
pub use env::{
    canonical_ambient_axiom_kind,
    is_foundational_axiom,
    is_trust_marker,
    // Metamath two-pass PASS-1 axiom-only flag (verification-skip, see decl_add)
    mm_axiom_only,
    mm_two_pass_active,
    set_mm_axiom_only,
    AesopIndexMode,
    AesopRule,
    AesopRuleBuilder,
    AesopRulePhase,
    AesopRuleSet,
    // Attribute storage persistent extension
    AttrExtEntry,
    AttrExtState,
    AttrRegistration,
    CanonicalAmbientAxiomKind,
    CertificationAudit,
    CertificationIssue,
    ConstantInfo,
    ConstantKind,
    ConstantOrigin,
    ConstantOriginInfo,
    Declaration,
    DeclarationVerification,
    EnvError,
    EnvExtensionEntry,
    EnvExtensionEntryData,
    Environment,
    ExtensionIdx,
    // Instance database persistent extension
    InductiveInfo,
    InstanceExtEntry,
    InstanceExtState,
    InstanceInfo,
    KernelClassInfo,
    KernelInstanceInfo,
    // Pillar-1 G1: RAII guard establishing the sanctioned two-pass sentinel
    MmAxiomOnlyGuard,
    NoConfusionRegenerationDiagnostic,
    NoConfusionRegenerationIssue,
    NoConfusionRegenerationReport,
    OriginTrust,
    PersistentEnvExtensionState,
    PersistentExtEntry,
    PersistentExtState,
    ProofQuality,
    Reducibility,
    SimpExtEntry,
    SimpExtState,
    SorrySummary,
    SorryTracer,
    SoundnessReport,
    TransparencyMode,
    DEFAULT_INSTANCE_PRIORITY,
};
pub use expr::{
    iterative_drop, AppArgs, AppArgsIter, BigNat, BinderData, BinderInfo, Expr, ExprFolder,
    ExprFolderOpt, ExprKind, ExprVisitor, FVarId, LevelVec, Literal, MDataMap, MDataValue,
    Multiplicity,
};
pub use inductive::{
    allows_large_elim, Constructor, ConstructorVal, InductiveDecl, InductiveError, InductiveType,
    InductiveVal, RecursorArgOrder, RecursorRule, RecursorVal,
};
pub use level::Level;
pub use name::Name;
pub use quot::{QuotKind, QuotVal};
pub use separation_logic::{
    check_frame_rule, check_frame_rule_with, satisfies, satisfies_with, satisfies_with_extensions,
    SepExpr, SepHeap, SepLogicProof,
};
pub use serde_budget::{with_decode_resource_limits, DecodeResourceLimits};
pub use tc::batch::{
    BatchCheckResult, BatchCheckStats, BatchConfig, BatchVerifier, VerificationArena,
};
pub use tc::heartbeat_profiler::{
    HeartbeatProfile, HeartbeatProfileCategory, OverrunEstimate, ProfileEntry, ProfileNameEntry,
    ProfilePositionEntry, ProfileTacticEntry, SourcePos,
};
pub use tc::reduction_stats::{reduction_stats_report, reduction_stats_reset};
pub use tc::whnf_proof::{EqProofBuilder, WhnfWithProof};
pub use tc::{
    set_global_max_cache_entries, ExprLocation, ExprPathStep, LocalContext, LocalDecl, TcCaches,
    TypeChecker, TypeError,
};

pub use cache::{TypeCheckCache, TypeCheckCacheStats, TypeCheckId};
pub use mode::{AxiomId, CleanMode, ModeError, SourceSystem};

/// Domain-prefixed alias for collision-free imports.
///
/// Use `KernelEnvError` when importing from multiple crates with `EnvError` types.
pub use env::EnvError as KernelEnvError;

/// Domain-prefixed alias for collision-free imports.
///
/// Use `KernelInductiveError` when importing from multiple crates with `InductiveError` types.
pub use inductive::InductiveError as KernelInductiveError;

/// Domain-prefixed alias for collision-free imports.
///
/// Use `KernelTypeError` when importing from multiple crates with `TypeError` types.
pub use tc::TypeError as KernelTypeError;

/// Domain-prefixed alias for collision-free imports.
///
/// Use `KernelLocalDecl` when importing from multiple crates with `LocalDecl` types.
pub use tc::LocalDecl as KernelLocalDecl;
