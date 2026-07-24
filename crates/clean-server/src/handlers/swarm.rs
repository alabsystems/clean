// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Swarm-worker declaration submission (`addDecl`).
//!
//! A swarm of proof workers submits proved declarations to the server and gets
//! a kernel verdict + transitive axiom closure back in real time. `addDecl` is
//! the front door: it routes a candidate declaration through the SAME
//! kernel-recheck trust verdict the graduation intake gate uses (kernel
//! `add_decl` WITH the proof value, then the transitive `axiom_deps` closure),
//! and on accept lands the declaration in the worker's SESSION OVERLAY so it is
//! immediately available as a premise for the worker's sibling obligations.
//!
//! Trust shape (mirrors [`crate::handlers::admin::handle_load_environment`]'s
//! `env.add_decl` fail-closed pattern):
//!
//! - The verdict is FACTS: did the proof value type-check, and what is the
//!   transitive NON-foundational ("domain") axiom set. `require_foundational`
//!   (default `true`) is the only policy knob — when set, a verdict with a
//!   non-empty domain-axiom closure is REJECTED even though it kernel-checked.
//! - Fail-closed: any kernel rejection (type error, missing dependency,
//!   duplicate, free variable, **heartbeat budget exhaustion**) leaves the
//!   session overlay — and therefore the shared base corpus — pristine, and is
//!   reported as `accepted: false` with a `reject_reason`.
//! - The declaration lands in the overlay ONLY on a fully-accepted verdict. A
//!   policy rejection of an otherwise-kernel-valid decl does NOT leave it in
//!   the overlay: the session is rolled back to its pre-call state.
//!
//! This handler touches NO kernel trust logic. It reuses the kernel's
//! `add_decl` / `proof_quality` / `axiom_deps` primitives (the same ones Task A
//! built `recheck_and_classify` on) through the session overlay, plus the
//! kernel's existing deterministic `maxHeartbeats` fuel mechanism to bound a
//! single pathological check.

use super::state::ServerState;
use crate::rpc::{RequestId, Response, RpcError};
use crate::session_env::{SessionEnv, SessionEnvError, SessionId};
use clean_kernel::{Declaration, Name, ProofQuality};
use serde::{Deserialize, Serialize};
use std::str::FromStr;
use tracing::instrument;

/// Default per-call kernel heartbeat (fuel) budget for an `addDecl` check.
///
/// Bounds the number of major kernel operations (whnf / def_eq / inference
/// ticks) a single submission may consume, so a pathological proof term cannot
/// wedge a worker. This is deliberately well below the kernel's own default
/// (`2_000_000`) — a swarm worker's interactive submission should be cheap;
/// a genuinely large proof can opt into a higher budget per call.
pub(crate) const DEFAULT_ADD_DECL_HEARTBEAT: u32 = 200_000;

/// Request parameters for the `addDecl` method.
#[derive(Debug, Clone, Deserialize)]
pub struct AddDeclParams {
    /// The worker session to add the declaration into. When absent, the call
    /// fails closed (`addDecl` is session-scoped: it has no shared-environment
    /// fallback, so a missing or unknown session never mutates the corpus).
    #[serde(default)]
    pub session_id: Option<String>,
    /// The declaration to submit (definition / axiom / theorem / opaque),
    /// carrying its type and — for theorems / definitions / opaques — its
    /// proof value. The value is what the kernel type-checks: this is the only
    /// honest road to a `KernelVerified` verdict.
    pub decl: Declaration,
    /// Whether the transitive axiom closure must be `⊆ FOUNDATIONAL_AXIOMS`
    /// for the decl to be accepted (the strict `kernel_verified` finish line).
    /// Defaults to `true`: a decl that kernel-checks but cites a domain axiom
    /// is rejected rather than landed in the overlay.
    #[serde(default = "default_require_foundational")]
    pub require_foundational: bool,
    /// Per-call kernel heartbeat (fuel) budget. `None` uses
    /// [`DEFAULT_ADD_DECL_HEARTBEAT`]; `Some(0)` opts out (kernel default,
    /// unbounded heartbeat) for a caller that knowingly submits a large proof.
    #[serde(default)]
    pub heartbeat_limit: Option<u32>,
}

const fn default_require_foundational() -> bool {
    true
}

/// The verdict a kernel re-check produced for a submitted declaration.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum AddDeclVerdict {
    /// The proof value type-checked AND the transitive axiom closure is
    /// foundational-only (`⊆ FOUNDATIONAL_AXIOMS`).
    KernelVerified,
    /// The proof value type-checked but the transitive closure cites at least
    /// one domain-specific axiom.
    AxiomDependent,
    /// The kernel rejected the declaration (type error, missing dependency,
    /// duplicate, free variable, heartbeat budget exhausted, …).
    KernelRejected,
}

/// Response for the `addDecl` method.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AddDeclResult {
    /// Whether the declaration was accepted into the session overlay.
    ///
    /// `true` only when the kernel verified the value AND policy
    /// (`require_foundational`) is satisfied. On `false` the overlay — and the
    /// shared base corpus — is unchanged.
    pub accepted: bool,
    /// The kernel verdict (facts, independent of policy).
    pub verdict: AddDeclVerdict,
    /// The transitive non-foundational axiom names reachable from the
    /// declaration, sorted. Empty ⇔ foundational-only.
    pub axiom_closure: Vec<String>,
    /// Why the declaration was rejected, when `accepted` is `false`. `None`
    /// on accept.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reject_reason: Option<String>,
}

/// The kernel-recheck verdict for one session-scoped declaration: the same
/// shape Task A's `recheck_and_classify` produces, expressed against a
/// [`SessionEnv`] overlay. On success the declaration is registered in the
/// overlay; the returned closure is the transitive non-foundational axiom set.
struct SessionRecheck {
    verdict: AddDeclVerdict,
    axiom_closure: Vec<String>,
}

/// Why a session re-check did not yield a clean kernel verdict.
#[derive(Debug, Clone, thiserror::Error)]
enum SessionRecheckError {
    /// `add_decl` rejected the declaration (type error, missing dependency,
    /// duplicate, free variable, or a deterministic heartbeat-limit-exceeded).
    /// The kernel's own message is preserved.
    #[error("kernel-rejected: {0}")]
    KernelRejected(String),
    /// `add_decl` succeeded but the constant could not be classified
    /// afterwards (no stored proof value / not-a-theorem / vanished). Treated
    /// as a kernel rejection rather than a silent pass.
    #[error("kernel-rejected: unexpected proof quality after add_decl: {0}")]
    Unclassifiable(String),
}

/// Replay `decl` into the session overlay via the real kernel `add_decl` path
/// (under `heartbeat_limit` fuel), then classify its transitive axiom closure.
///
/// Mirrors Task A's `recheck_and_classify` exactly — kernel `add_decl` WITH the
/// value (the only honest path to `KernelVerified`), then `proof_quality` for
/// theorems / `axiom_deps` for non-theorems — but operates on a [`SessionEnv`]
/// so the decl lands in the worker's overlay and is immediately a premise for
/// the worker's siblings. Any kernel rejection fails closed: the overlay is
/// left unchanged (the kernel never registers a decl it rejected).
fn recheck_and_classify_session(
    session: &mut SessionEnv,
    decl: Declaration,
    heartbeat_limit: u32,
) -> Result<SessionRecheck, SessionRecheckError> {
    let name = decl_name(&decl);
    let is_theorem = matches!(decl, Declaration::Theorem { .. });

    // Step 1: kernel re-check WITH the value under the fuel budget. Any error
    // (including heartbeat exhaustion) fails closed.
    session
        .add_decl_with_heartbeat(decl, heartbeat_limit)
        .map_err(|e: SessionEnvError| SessionRecheckError::KernelRejected(e.to_string()))?;

    // Step 2: transitive non-foundational axiom closure. Theorems route
    // through `proof_quality` so the not-a-theorem / unchecked / vanished
    // cases stay kernel rejections; non-theorems read the closure directly.
    let axiom_closure = if is_theorem {
        match session.proof_quality(&name) {
            Some(ProofQuality::Constructive) => Vec::new(),
            Some(ProofQuality::AxiomDependent { axioms, .. }) => sorted_names(axioms.iter()),
            other => {
                return Err(SessionRecheckError::Unclassifiable(format!("{other:?}")));
            }
        }
    } else {
        match session.axiom_deps(&name) {
            Some(deps) => sorted_names(deps.iter()),
            None => {
                return Err(SessionRecheckError::Unclassifiable(
                    "axiom_deps: constant absent after add_decl".to_string(),
                ));
            }
        }
    };

    let verdict = if axiom_closure.is_empty() {
        AddDeclVerdict::KernelVerified
    } else {
        AddDeclVerdict::AxiomDependent
    };

    Ok(SessionRecheck {
        verdict,
        axiom_closure,
    })
}

/// The declaration's name, for the post-add closure query.
fn decl_name(decl: &Declaration) -> Name {
    match decl {
        Declaration::Axiom { name, .. }
        | Declaration::Definition { name, .. }
        | Declaration::Theorem { name, .. }
        | Declaration::Opaque { name, .. } => name.clone(),
    }
}

/// Sort a set of axiom names into a stable `Vec<String>`.
fn sorted_names<'a>(names: impl Iterator<Item = &'a Name>) -> Vec<String> {
    let mut out: Vec<String> = names.map(Name::to_string).collect();
    out.sort();
    out
}

/// Handle the `addDecl` method.
///
/// Submits a worker's proved declaration into its session overlay, returning a
/// kernel verdict + axiom closure. Fail-closed on every error path: a missing /
/// unknown session, a kernel rejection, or a policy rejection all leave the
/// shared corpus pristine.
#[instrument(skip(state, params), fields(session_id = ?params.session_id))]
pub async fn handle_add_decl(
    state: &ServerState,
    id: RequestId,
    params: AddDeclParams,
) -> Response {
    // Session is mandatory: `addDecl` only ever writes into a session overlay,
    // never the shared environment. A missing or malformed id fails closed.
    let session_id = match params.session_id.as_deref() {
        Some(raw) => match SessionId::from_str(raw) {
            Ok(sid) => sid,
            Err(e) => {
                return Response::error(
                    id,
                    RpcError::invalid_params(format!("Invalid session_id '{raw}': {e}")),
                );
            }
        },
        None => {
            return Response::error(
                id,
                RpcError::invalid_params(
                    "addDecl requires a session_id (it writes only into a session overlay)"
                        .to_string(),
                ),
            );
        }
    };

    let heartbeat_limit = params.heartbeat_limit.unwrap_or(DEFAULT_ADD_DECL_HEARTBEAT);
    let require_foundational = params.require_foundational;
    let decl = params.decl;

    // Write-lock the session map (mirrors admin's `state.env.write().await`
    // pattern) — a session is mutated by exactly one in-flight addDecl at a
    // time, and the overlay add is the only mutation.
    let mut sessions = state.sessions.write().await;
    let Some(session) = sessions.get_mut(&session_id) else {
        return Response::error(
            id,
            RpcError::invalid_params(format!("Unknown session: {session_id}")),
        );
    };

    // Checkpoint the overlay BEFORE the speculative add, but only on the path
    // that can roll a kernel-valid decl back (`require_foundational`). The
    // checkpoint captures the session's earlier accepted work so a policy
    // rejection undoes ONLY this call's decl, never the siblings. On the
    // relaxed path no checkpoint is taken (any kernel-valid decl is kept) and
    // a kernel rejection never registers anything, so neither needs a restore.
    let checkpoint = if require_foundational {
        Some(session.checkpoint())
    } else {
        None
    };

    let result = match recheck_and_classify_session(session, decl, heartbeat_limit) {
        Ok(recheck) => {
            // Kernel accepted the value. Apply policy.
            if require_foundational && recheck.verdict != AddDeclVerdict::KernelVerified {
                // Policy rejection of an otherwise-valid decl: restore the
                // pre-add checkpoint so the rejected decl is NOT left as a
                // premise, while every earlier accepted decl survives.
                if let Some(cp) = checkpoint {
                    session.restore(cp);
                }
                AddDeclResult {
                    accepted: false,
                    verdict: recheck.verdict,
                    axiom_closure: recheck.axiom_closure.clone(),
                    reject_reason: Some(format!(
                        "require_foundational: declaration cites domain axioms: {}",
                        recheck.axiom_closure.join(", ")
                    )),
                }
            } else {
                AddDeclResult {
                    accepted: true,
                    verdict: recheck.verdict,
                    axiom_closure: recheck.axiom_closure,
                    reject_reason: None,
                }
            }
        }
        Err(err) => AddDeclResult {
            accepted: false,
            verdict: AddDeclVerdict::KernelRejected,
            axiom_closure: Vec::new(),
            reject_reason: Some(err.to_string()),
        },
    };
    drop(sessions);

    Response::success_typed(id.clone(), &result)
        .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string())))
}

// Tests live in `handlers/tests/swarm.rs`, matching the crate convention for
// handler tests (alongside `environment.rs`, `external_cert.rs`, …). This keeps
// the handler module focused and under the 500-line file budget.
