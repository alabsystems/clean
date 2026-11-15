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
//!   the overlay: the check runs on a copy of the session, which replaces the
//!   session only when the verdict is accepted.
//! - Deadline: the kernel's check runs on the server's work pool under the
//!   request's `timeout_ms` (the server's default when absent), the way every
//!   other kernel check does (`work.rs`). A check the deadline interrupted is
//!   no verdict: the request answers the timeout error and the session keeps
//!   nothing. Until 2026-10-15 the check ran on the runtime worker with no
//!   deadline, bounded only by `heartbeat_limit` (none at `0`).
//! - Order: each session has a lock of its own, so `addDecl`s to different
//!   sessions never wait for each other, and those to one session are checked
//!   one at a time, first come first served, each against every declaration
//!   accepted before it. One waiting for its session holds no work slot. Until
//!   2026-10-16 every `addDecl` held the whole session map's write lock across
//!   its check, and one queued for it held a slot (R34 in `docs/DECISIONS.md`).
//! - The copy of the session the check runs on is made on the work pool, from
//!   a share of the session, and every session the handler lets go (the one an
//!   accepted declaration replaces, a refused copy, and one closed while this
//!   `addDecl` held it) is freed off the runtime (R36, R87).
//!
//! This handler touches NO kernel trust logic. It reuses the kernel's
//! `add_decl` / `proof_quality` / `axiom_deps` primitives (the same ones Task A
//! built `recheck_and_classify` on) through the session overlay, plus the
//! kernel's existing deterministic `maxHeartbeats` fuel mechanism to bound a
//! single pathological check.

use super::off_runtime::{free_off_runtime, Shared};
use super::state::ServerState;
use super::work::{within, WorkPool};
use crate::rpc::{RequestId, Response, RpcError};
use crate::session_env::{SessionEnv, SessionEnvError, SessionId};
use clean_kernel::{Declaration, Name, ProofQuality};
use serde::{Deserialize, Serialize};
use std::str::FromStr;
use std::time::{Duration, Instant};
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
    /// Optional timeout in milliseconds for the kernel's check (the server's
    /// default when absent). A check still running at it answers the timeout
    /// error, and the session keeps nothing from it.
    #[serde(default)]
    pub timeout_ms: Option<u64>,
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
    let start = Instant::now();
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
    let timeout = Duration::from_millis(params.timeout_ms.unwrap_or(state.default_timeout_ms));
    let deadline = start.checked_add(timeout);

    let outcome = within(timeout, async {
        // The session map is held only for the look-up (every wait is inside
        // the timeout), so an addDecl never waits for another session's.
        let Some(session) = state.session(&session_id).await else {
            return Ok(Err(RpcError::invalid_params(format!(
                "Unknown session: {session_id}"
            ))));
        };
        // One addDecl at a time per session, in the order they reach the
        // session's lock (tokio's `Mutex` is fair: first come, first served),
        // so each is checked against every declaration accepted before it.
        // The session's lock comes before the work slot: an addDecl queued
        // behind another of its session holds no slot while it waits. That
        // order closes no cycle because no slot holder ever waits for a
        // session (`work.rs`, "Lock order").
        let mut session = session.lock().await;
        let slot = state.work.slot().await?;
        // The kernel's check is work under the request's deadline, on the
        // pool, against a copy of the session. The copy replaces the session
        // only when the declaration is accepted, so a rejected, unclassifiable
        // or interrupted check leaves the session as it was (and a request
        // whose timeout fires drops the copy, and lets the lock go).
        //
        // The copy is made there too, from a share of the session (a session
        // holds a whole environment: copied on the runtime until R87,
        // 2026-10-17). The session's lock, held here, keeps any
        // other `addDecl` from replacing it meanwhile.
        let current = Shared::clone(&session);
        let (candidate, result) = WorkPool::run_in(slot, deadline, move || {
            let mut candidate = SessionEnv::clone(&current);
            drop(current);
            let result =
                add_decl_to_session(&mut candidate, decl, heartbeat_limit, require_foundational);
            (candidate, result)
        })
        .await?;
        // The session the candidate replaces, or the candidate a refusal
        // leaves, holds a whole environment: freed off the runtime
        // (`off_runtime.rs`; the replaced one by its last share).
        if result.accepted {
            *session = Shared::new(candidate);
        } else {
            free_off_runtime(candidate);
        }
        Ok(Ok(result))
    })
    .await;

    match outcome {
        Ok(Ok(result)) => Response::success_typed(id.clone(), &result)
            .unwrap_or_else(|e| Response::error(id, RpcError::internal_error(e.to_string()))),
        Ok(Err(error)) => Response::error(id, error),
        Err(error) => Response::error(id, error.into_rpc_error(timeout)),
    }
}

/// Re-check `decl` into `session` and apply `require_foundational`. Runs on the
/// work pool, on a copy of the session the caller keeps only when the result
/// is accepted: a rejected declaration may be left registered in the copy (a
/// policy rejection, or one the kernel accepted but could not classify).
fn add_decl_to_session(
    session: &mut SessionEnv,
    decl: Declaration,
    heartbeat_limit: u32,
    require_foundational: bool,
) -> AddDeclResult {
    match recheck_and_classify_session(session, decl, heartbeat_limit) {
        // Kernel accepted the value; policy rejects a domain-axiom closure.
        Ok(recheck)
            if require_foundational && recheck.verdict != AddDeclVerdict::KernelVerified =>
        {
            AddDeclResult {
                accepted: false,
                verdict: recheck.verdict,
                reject_reason: Some(format!(
                    "require_foundational: declaration cites domain axioms: {}",
                    recheck.axiom_closure.join(", ")
                )),
                axiom_closure: recheck.axiom_closure,
            }
        }
        Ok(recheck) => AddDeclResult {
            accepted: true,
            verdict: recheck.verdict,
            axiom_closure: recheck.axiom_closure,
            reject_reason: None,
        },
        Err(err) => AddDeclResult {
            accepted: false,
            verdict: AddDeclVerdict::KernelRejected,
            axiom_closure: Vec::new(),
            reject_reason: Some(err.to_string()),
        },
    }
}

// Tests live in `handlers/tests/swarm.rs`, matching the crate convention for
// handler tests (alongside `environment.rs`, `external_cert.rs`, …). This keeps
// the handler module focused and under the 500-line file budget.
