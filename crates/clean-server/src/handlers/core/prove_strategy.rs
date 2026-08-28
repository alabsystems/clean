// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof-search strategy dispatch for the "prove" handler.
//!
//! `handle_prove` decides *what* to prove; this module decides *how*. The
//! three legs ("smt", "superposition", and the default "auto" cascade) each
//! own their engine wiring here so the handler body stays a thin
//! parse-elaborate-dispatch shell.

use std::time::Duration;

use clean_auto::bridge::SmtBridge;
use clean_auto::{AutomationEngine, AutomationQuery};

use super::super::types::ProveResult;
use super::super::{prove_result_from_automation_outcome, prove_result_from_smt_verification};
use crate::rpc::RpcError;

/// Dispatch proof search to the selected strategy.
///
/// "smt" uses the SmtBridge directly. "superposition" uses the superposition
/// prover. "auto" (default) chains SMT -> superposition -> oracle via
/// [`AutomationEngine::auto_prove_with_query`].
pub(super) fn prove_with_strategy(
    env: &clean_kernel::Environment,
    goal: &clean_kernel::Expr,
    hypotheses: &[(
        clean_kernel::Expr,
        Option<clean_auto::bridge::QuantifierOrigin>,
    )],
    timeout: Duration,
    strategy: &str,
) -> Result<ProveResult, RpcError> {
    match strategy {
        "smt" => prove_smt_only(env, goal, hypotheses),
        "superposition" => Ok(prove_superposition_only(env, goal, hypotheses)),
        _ => Ok(prove_auto_cascade(env, goal, hypotheses, timeout)),
    }
}

/// SMT-only strategy: use SmtBridge directly (original behavior).
fn prove_smt_only(
    env: &clean_kernel::Environment,
    goal: &clean_kernel::Expr,
    hypotheses: &[(
        clean_kernel::Expr,
        Option<clean_auto::bridge::QuantifierOrigin>,
    )],
) -> Result<ProveResult, RpcError> {
    let mut bridge = SmtBridge::new(env);
    let mut dropped = 0u32;
    for (hyp_expr, _origin) in hypotheses {
        if bridge.add_hypothesis(hyp_expr).is_err() {
            dropped += 1;
        }
    }
    if dropped > 0 {
        tracing::warn!(
            dropped,
            total = hypotheses.len(),
            "hypothesis(es) dropped in RPC prove handler (unsupported by SMT bridge)"
        );
    }
    match bridge.prove(goal) {
        Ok(result) => Ok(prove_result_from_smt_verification(env, goal, result)),
        Err(e) => Err(RpcError::internal_error(format!("SMT bridge error: {e}"))),
    }
}

/// Superposition-only strategy.
fn prove_superposition_only(
    env: &clean_kernel::Environment,
    goal: &clean_kernel::Expr,
    hypotheses: &[(
        clean_kernel::Expr,
        Option<clean_auto::bridge::QuantifierOrigin>,
    )],
) -> ProveResult {
    let engine = AutomationEngine::new();
    let outcome = match engine.try_superposition_prove_with_hypotheses(env, goal, hypotheses) {
        Some(result) => clean_auto::AutomationOutcome::Verified(Box::new(result)),
        None => clean_auto::AutomationOutcome::Unknown {
            reason: "superposition: no refutation found".to_string(),
            source: clean_auto::AutomationSource::Superposition,
            time_ms: 0,
        },
    };
    prove_result_from_automation_outcome(env, goal, outcome)
}

/// Full cascade: SMT -> superposition -> oracle via AutomationEngine.
fn prove_auto_cascade(
    env: &clean_kernel::Environment,
    goal: &clean_kernel::Expr,
    hypotheses: &[(
        clean_kernel::Expr,
        Option<clean_auto::bridge::QuantifierOrigin>,
    )],
    timeout: Duration,
) -> ProveResult {
    let engine = AutomationEngine::new();
    let query = AutomationQuery::new(goal, timeout).with_hypotheses(hypotheses);
    let outcome = engine.auto_prove_with_query(env, query);
    prove_result_from_automation_outcome(env, goal, outcome)
}
