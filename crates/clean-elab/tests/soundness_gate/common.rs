// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Common clean-side helpers for the kernel soundness gate.
//!
//! Provides:
//! - `GateVerdict`: accept/reject enum for parity comparison
//! - `GateVerdictTag`: accept/reject tag without diagnostic payload
//! - `run_clean_file`: parse + elaborate a Lean source file through clean
//! - `corpus_root` / `manifest_path`: shared corpus path helpers
//!
//! Issues: #2134, #2543

use clean_elab::register::{kernel_check_failure_count, reset_kernel_check_counter};
use clean_elab::tactic::{arith_proof_count, reset_arith_counter};
use clean_kernel::sorry::{
    ay_proof_count, explicit_sorry_count, reset_ay_counter, reset_sorry_counter, sorry_count,
    synthetic_sorry_count,
};
use clean_kernel::{Environment, Expr};
use clean_parser::parse_file;
use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};
use std::sync::{Mutex, OnceLock};

/// Gate verdict: does the system accept or reject a file?
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum GateVerdict {
    /// All declarations parsed and elaborated successfully.
    Accept,
    /// At least one declaration failed. Contains first error message.
    Reject(String),
}

impl GateVerdict {
    pub(crate) fn is_accept(&self) -> bool {
        matches!(self, GateVerdict::Accept)
    }

    pub(crate) fn tag(&self) -> GateVerdictTag {
        match self {
            GateVerdict::Accept => GateVerdictTag::Accept,
            GateVerdict::Reject(_) => GateVerdictTag::Reject,
        }
    }
}

/// Accept/reject tag without diagnostic payload.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum GateVerdictTag {
    Accept,
    Reject,
}

impl GateVerdictTag {
    pub(crate) fn lane_name(self) -> &'static str {
        match self {
            GateVerdictTag::Accept => "accept",
            GateVerdictTag::Reject => "reject",
        }
    }
}

impl std::fmt::Display for GateVerdictTag {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.lane_name())
    }
}

/// Trust metadata captured for a single gate run.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct GateTrustSummary {
    pub(crate) sorry_count: u64,
    pub(crate) explicit_sorry_count: u64,
    pub(crate) synthetic_sorry_count: u64,
    pub(crate) ay_count: u64,
    pub(crate) arith_count: u64,
    pub(crate) kernel_check_failures: u64,
    pub(crate) fully_verified: bool,
}

/// Full result for one soundness-gate execution.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct GateRunResult {
    pub(crate) verdict: GateVerdict,
    pub(crate) trust: GateTrustSummary,
}

static GATE_TRUST_LOCK: OnceLock<Mutex<()>> = OnceLock::new();

fn gate_trust_lock() -> &'static Mutex<()> {
    GATE_TRUST_LOCK.get_or_init(|| Mutex::new(()))
}

#[cfg(any(test, feature = "test-utils"))]
const GATE_THREAD_STACK_SIZE: usize = clean_kernel::test_utils::SMALL_STACK;

#[cfg(not(any(test, feature = "test-utils")))]
const GATE_THREAD_STACK_SIZE: usize = 8 * 1024 * 1024;

pub(crate) fn reset_gate_trust_counters() {
    reset_sorry_counter();
    reset_ay_counter();
    reset_arith_counter();
    reset_kernel_check_counter();
}

pub(crate) fn read_gate_trust_summary(accepted: bool) -> GateTrustSummary {
    let sorry = sorry_count();
    let explicit = explicit_sorry_count();
    let synthetic = synthetic_sorry_count();
    let ay = ay_proof_count();
    let arith = arith_proof_count();
    let kernel_failures = kernel_check_failure_count();
    GateTrustSummary {
        sorry_count: sorry,
        explicit_sorry_count: explicit,
        synthetic_sorry_count: synthetic,
        ay_count: ay,
        arith_count: arith,
        kernel_check_failures: kernel_failures,
        fully_verified: accepted && sorry == 0 && ay == 0 && arith == 0 && kernel_failures == 0,
    }
}

pub(crate) fn sample_gate_trust<T>(accepted: bool, f: impl FnOnce() -> T) -> (T, GateTrustSummary) {
    let _guard = gate_trust_lock()
        .lock()
        .expect("soundness gate trust lock poisoned");
    reset_gate_trust_counters();
    let value = f();
    let trust = read_gate_trust_summary(accepted);
    (value, trust)
}

fn evaluate_clean_file(source: &str) -> GateVerdict {
    let decls = match parse_file(source) {
        Ok(decls) => decls,
        Err(e) => return GateVerdict::Reject(format!("parse error: {e}")),
    };

    let mut env = Environment::new();
    // Initialize core prelude types (same set as lean4_phase1_compat.rs)
    env.init_nat().ok();
    env.init_and().ok();
    env.init_true_false().ok();
    env.init_classical().ok();
    env.init_eq().ok();
    env.init_bool().ok();
    env.init_unit().ok();

    for decl in &decls {
        if let Err(e) = clean_elab::elaborate_decl_and_register(&mut env, decl) {
            return GateVerdict::Reject(format!("elab error: {e}"));
        }
    }

    GateVerdict::Accept
}

/// Run a Lean source file through the clean parse + elaborate + type-check
/// pipeline. Enables strict kernel checking so that `elaborate_decl_and_register`
/// uses `add_decl` (full type check) instead of `add_decl_structural`.
///
/// Returns the accept/reject verdict plus trust metadata for the run.
pub(crate) fn run_clean_file(source: &str) -> GateRunResult {
    let _guard = gate_trust_lock()
        .lock()
        .expect("soundness gate trust lock poisoned");
    reset_gate_trust_counters();
    let verdict = evaluate_clean_file(source);
    let trust = read_gate_trust_summary(verdict.is_accept());
    GateRunResult { verdict, trust }
}

/// Run a Lean source file through the clean pipeline on a dedicated thread
/// with a larger stack to avoid overflows on deeply nested expressions.
pub(crate) fn run_clean_file_threaded(source: &str) -> GateRunResult {
    let _guard = gate_trust_lock()
        .lock()
        .expect("soundness gate trust lock poisoned");
    reset_gate_trust_counters();
    let source = source.to_string();
    let handle = std::thread::Builder::new()
        .stack_size(GATE_THREAD_STACK_SIZE)
        .spawn(move || evaluate_clean_file(&source))
        .expect("Failed to spawn thread for soundness gate");

    let verdict = match handle.join() {
        Ok(verdict) => verdict,
        Err(_) => GateVerdict::Reject("thread panic (possible stack overflow)".to_string()),
    };
    let trust = read_gate_trust_summary(verdict.is_accept());
    GateRunResult { verdict, trust }
}

pub(crate) fn synthetic_sorry_probe() -> (Expr, GateTrustSummary) {
    sample_gate_trust(true, || {
        let mut env = Environment::default();
        env.init_bool()
            .expect("Bool init should make synthetic sorryAx available");
        clean_kernel::sorry::create_sorry_term(&env, &Expr::prop())
    })
}

pub(crate) fn explicit_sorry_probe() -> (Expr, GateTrustSummary) {
    sample_gate_trust(true, || {
        let mut env = Environment::default();
        env.init_bool()
            .expect("Bool init should make explicit sorryAx available");
        clean_kernel::sorry::create_sorry_term_with_kind(
            &env,
            &Expr::prop(),
            clean_kernel::sorry::SorryKind::Explicit,
        )
    })
}

/// Path to the corpus root directory from the crate manifest directory.
pub(crate) fn corpus_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/soundness_gate")
}

/// Path to the manifest file.
pub(crate) fn manifest_path() -> PathBuf {
    corpus_root().join("manifest.txt")
}
