// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

mod source_theorem;

use std::env;
use std::io::{BufRead, BufReader, Write};
use std::net::TcpStream;
use std::path::{Path, PathBuf};
use std::time::Duration;

use clean_kernel::Expr;
use clean_server::{proof_state as server_proof_state, Response};
// The embedded open-obligation path drives the in-process server handlers,
// which are native-only (tokio); the wire/proof-state types above stay on
// wasm.
#[cfg(not(target_arch = "wasm32"))]
use clean_server::{
    handlers::{handle_open_obligation, ServerState},
    RequestId,
};
use serde::{Deserialize, Serialize};
use serde_json::json;

use super::args::{
    ProofStateApplyArgs, ProofStateAttemptArgs, ProofStateByStateArgs, ProofStateExtractArgs,
    ProofStateLifecycleArgs, ProofStateOpenArgs, ProofStateOpenObligationArgs, SnapshotFormat,
};
use super::error::MathError;
use super::handlers::load_project_args;
use super::output::{render_proof_state_report, write_output};
use crate::math_project::{
    load_json, obligation_fingerprint, validate_obligation, ArtifactRef, MathObligation,
};
use source_theorem::{
    parse_source_theorem_state_id, render_source_theorem_snapshot, source_theorem_snapshot,
    source_theorem_state_id, SourceTheoremHandle,
};

const PROOF_STATE_SERVER_ENV: &str = "CLEAN_PROOF_STATE_SERVER";
const CLEAN_SERVER_ENV: &str = "CLEAN_SERVER";

pub(super) fn run_proof_state_open(args: ProofStateOpenArgs) -> Result<(), MathError> {
    let (_path, manifest) = load_project_args(&args.project)?;
    let state = source_theorem_state_id(&manifest.project, &args.file, &args.theorem);
    let report = ProofStateBridgeReport {
        schema_version: "clean-proof-state-v2-bridge-v1",
        operation: "open-theorem",
        state: Some(state),
        status: "opened-adapter",
        detail: format!(
            "theorem `{}` in `{}` is represented as a source-backed CLI handle",
            args.theorem,
            args.file.display()
        ),
    };
    write_output(args.json, &report, |out| {
        render_proof_state_report(out, &report)
    })?;
    Ok(())
}

pub(super) fn run_proof_state_open_obligation(
    args: ProofStateOpenObligationArgs,
) -> Result<(), MathError> {
    let (project_path, project) = load_project_args(&args.project)?;
    let obligation = load_json::<MathObligation>(&args.path)?;
    let obligation_fingerprint = obligation_fingerprint(&obligation);
    let violations = validate_obligation(&obligation, Some(&project));
    if !violations.is_empty() {
        let report = ProofStateOpenObligationReport::blocked(
            &project.project,
            &project.domain_profile,
            "blocked-invalid-obligation",
            format!(
                "open obligation validation reported {} violation(s)",
                violations.len()
            ),
        );
        write_open_obligation_report(args.json, &report)?;
        return Err(MathError::Failed(
            "proof-state open-obligation rejected an invalid obligation".to_owned(),
        ));
    }

    let goal_expr = match parse_serialized_expr("goal.expr", &obligation.goal.expr) {
        Ok(expr) => expr,
        Err(error) => {
            let report =
                blocked_open_obligation_report(&project.project, &project.domain_profile, error);
            write_open_obligation_report(args.json, &report)?;
            return Err(MathError::Failed(
                "proof-state open-obligation requires a serialized kernel goal".to_owned(),
            ));
        }
    };

    let local_context = match server_local_context(&obligation) {
        Ok(local_context) => local_context,
        Err(error) => {
            let report =
                blocked_open_obligation_report(&project.project, &project.domain_profile, error);
            write_open_obligation_report(args.json, &report)?;
            return Err(MathError::Failed(
                "proof-state open-obligation requires serialized local-context types".to_owned(),
            ));
        }
    };

    let artifact_refs: Vec<_> = obligation
        .artifact_refs
        .iter()
        .map(server_artifact_ref)
        .collect();
    let metadata = open_obligation_metadata(
        &project_path,
        &args.path,
        &project.project,
        &obligation_fingerprint,
        &obligation,
        artifact_refs.clone(),
    );

    let request = server_proof_state::OpenObligationRequest {
        schema_version: server_proof_state::OPEN_OBLIGATION_SCHEMA_VERSION.to_owned(),
        environment_id: format!(
            "math-project:{}:obligation:{}",
            project.project, obligation_fingerprint
        ),
        domain_profile: server_domain_profile(&project.domain_profile),
        goal: server_proof_state::ObligationGoalPayload {
            expr: Some(goal_expr),
            pretty: obligation.goal.pretty.clone(),
            type_expr: None,
            type_pp: None,
        },
        local_context,
        artifact_refs,
        metadata: Some(metadata),
        trust_policy: server_trust_policy(&obligation.trust_policy),
        ttl_sec: 600,
        max_states: 4096,
        min_schema_version: server_proof_state::PROOF_STATE_SCHEMA_VERSION.to_owned(),
        max_schema_version: server_proof_state::PROOF_STATE_SCHEMA_VERSION.to_owned(),
        timeout_ms: None,
    };

    let server = effective_server(args.server.as_deref());
    let response = if let Some(server) = server.as_deref() {
        run_open_obligation_in_persistent_server(server, &request)?
    } else {
        run_open_obligation_in_embedded_server(
            project_path
                .parent()
                .unwrap_or_else(|| Path::new("."))
                .to_owned(),
            request,
        )?
    };

    if let Some(error) = response.error {
        let server_code = error
            .data
            .as_ref()
            .and_then(|data: &serde_json::Value| data.get("code"))
            .and_then(serde_json::Value::as_str)
            .unwrap_or("SERVER_OPEN_OBLIGATION_ERROR");
        let report = ProofStateOpenObligationReport::blocked(
            &project.project,
            &project.domain_profile,
            &format!("blocked-server-{server_code}"),
            error.message.clone(),
        );
        write_open_obligation_report(args.json, &report)?;
        return Err(MathError::Failed(format!(
            "server proofState.openObligation failed: {}",
            error.message
        )));
    }

    let result: server_proof_state::OpenObligationResponse =
        serde_json::from_value(response.result.ok_or_else(|| {
            MathError::Failed("server open-obligation returned no result".to_owned())
        })?)
        .map_err(|err| {
            MathError::Failed(format!(
                "server open-obligation returned an invalid response: {err}"
            ))
        })?;

    let report = ProofStateOpenObligationReport {
        schema_version: "clean-cli-proof-state-open-obligation-v1",
        operation: "open-obligation",
        project: project.project,
        domain_profile: project.domain_profile,
        state_id: Some(result.state_id),
        persistence: if server.is_some() {
            "persistent-json-rpc-server"
        } else {
            "process-local-server-state"
        },
        status: "opened-server-state".to_owned(),
        detail: if let Some(server) = server {
            format!(
                "opened by proofState.openObligation on persistent server `{server}`; use the returned state_id with that server address or a proof-state server environment default"
            )
        } else {
            "opened by server proofState.openObligation; this CLI invocation does not persist the proof-state cache for later CLI commands".to_owned()
        },
    };
    write_open_obligation_report(args.json, &report)?;
    Ok(())
}

pub(super) fn run_proof_state_snapshot(args: ProofStateByStateArgs) -> Result<(), MathError> {
    let server = effective_server(args.server.as_deref());
    if let Some(server) = server.as_deref() {
        let format = match args.format {
            SnapshotFormat::Json => "full",
            SnapshotFormat::Llm => "llm",
        };
        let result = call_proof_state_server_or_report(
            args.json,
            "snapshot",
            &args.state,
            server,
            "getProofState",
            json!({
                "state_id": args.state,
                "format": format,
            }),
        )?;
        return write_server_result(args.json, "snapshot", &result);
    }

    if let Some(handle) = parse_source_theorem_state_id(&args.state) {
        return run_source_theorem_snapshot(args.json, args.format, &args.state, handle);
    }

    run_proof_state_bridge(
        "snapshot",
        args.json,
        Some(&args.state),
        format!(
            "snapshot format {:?} requires server-backed state storage",
            args.format
        ),
    )
}

fn run_source_theorem_snapshot(
    json: bool,
    format: SnapshotFormat,
    state: &str,
    handle: SourceTheoremHandle,
) -> Result<(), MathError> {
    match source_theorem_snapshot(state, format, handle) {
        Ok(report) => write_output(json, &report, |out| {
            render_source_theorem_snapshot(out, &report)
        }),
        Err(detail) => run_proof_state_bridge("snapshot", json, Some(state), detail),
    }
}

pub(super) fn run_proof_state_goal(
    operation: &'static str,
    method: &'static str,
    json: bool,
    state: &str,
    goal: &str,
    server: Option<&str>,
) -> Result<(), MathError> {
    let server = effective_server(server);
    if let Some(server) = server.as_deref() {
        let result = call_proof_state_server_or_report(
            json,
            operation,
            state,
            server,
            method,
            json!({
                "state_id": state,
                "goal_id": goal,
            }),
        )?;
        return write_server_result(json, operation, &result);
    }

    run_proof_state_bridge(
        operation,
        json,
        Some(state),
        format!(
            "goal {} requires server-backed proof-state v2 adapters",
            goal
        ),
    )
}

pub(super) fn run_proof_state_apply(args: ProofStateApplyArgs) -> Result<(), MathError> {
    let server = effective_server(args.server.as_deref());
    if let Some(server) = server.as_deref() {
        let result = call_proof_state_server_or_report(
            args.json,
            "apply",
            &args.state,
            server,
            "applyTactic",
            json!({
                "state_id": args.state,
                "goal_id": args.goal,
                "tactic": args.tactic,
                "timeout_ms": null,
            }),
        )?;
        return write_server_result(args.json, "apply", &result);
    }

    run_proof_state_bridge(
        "apply",
        args.json,
        Some(&args.state),
        format!(
            "tactic `{}` for goal `{}` requires server-backed tactic lifecycle",
            args.tactic, args.goal
        ),
    )
}

pub(super) fn run_proof_state_lifecycle(
    args: ProofStateLifecycleArgs,
    operation: &'static str,
    method: &'static str,
) -> Result<(), MathError> {
    let server = effective_server(args.server.as_deref());
    if let Some(server) = server.as_deref() {
        let result = call_proof_state_server_or_report(
            args.json,
            operation,
            &args.state,
            server,
            method,
            json!({
                "state_id": args.state,
            }),
        )?;
        return write_server_result(args.json, operation, &result);
    }

    run_proof_state_bridge(
        operation,
        args.json,
        Some(&args.state),
        "server-backed proof-state lifecycle storage is required".to_owned(),
    )
}

pub(super) fn run_proof_state_attempt(args: ProofStateAttemptArgs) -> Result<(), MathError> {
    let server = effective_server(args.server.as_deref());
    if let Some(server) = server.as_deref() {
        let result = call_proof_state_server_or_report(
            args.json,
            "explain-failure",
            &args.attempt,
            server,
            "proofState.explainFailure",
            json!({
                "attempt_id": args.attempt,
            }),
        )?;
        return write_server_result(args.json, "explain-failure", &result);
    }

    run_proof_state_bridge(
        "explain-failure",
        args.json,
        Some(&args.attempt),
        "attempt telemetry requires server-backed proof-state v2".to_owned(),
    )
}

pub(super) fn run_proof_state_extract(args: ProofStateExtractArgs) -> Result<(), MathError> {
    let server = effective_server(args.server.as_deref());
    if let Some(server) = server.as_deref() {
        let result = call_proof_state_server_or_report(
            args.json,
            "extract",
            &args.state,
            server,
            "extractProof",
            json!({
                "state_id": args.state,
                "format": args.format,
            }),
        )?;
        return write_server_result(args.json, "extract", &result);
    }

    run_proof_state_bridge(
        "extract",
        args.json,
        Some(&args.state),
        format!(
            "extract format `{}` requires a checked proof state or replay evidence",
            args.format
        ),
    )
}

fn run_proof_state_bridge(
    operation: &'static str,
    json: bool,
    state: Option<&str>,
    detail: String,
) -> Result<(), MathError> {
    let report = ProofStateBridgeReport {
        schema_version: "clean-proof-state-v2-bridge-v1",
        operation,
        state: state.map(str::to_owned),
        status: "blocked-server-adapter-required",
        detail,
    };
    write_output(json, &report, |out| render_proof_state_report(out, &report))?;
    Err(MathError::Failed(format!(
        "proof-state operation `{operation}` requires the server-backed v2 adapter"
    )))
}

fn effective_server(cli_server: Option<&str>) -> Option<String> {
    cli_server
        .and_then(normalize_server)
        .or_else(|| env_server(PROOF_STATE_SERVER_ENV))
        .or_else(|| env_server(CLEAN_SERVER_ENV))
}

fn env_server(name: &str) -> Option<String> {
    env::var(name).ok().as_deref().and_then(normalize_server)
}

fn normalize_server(server: &str) -> Option<String> {
    let server = server.trim();
    if server.is_empty() {
        None
    } else {
        Some(server.to_owned())
    }
}

fn parse_serialized_expr(path: impl Into<String>, payload: &str) -> Result<Expr, ExprPayloadError> {
    let path = path.into();
    match serde_json::from_str(payload) {
        Ok(expr) => Ok(expr),
        Err(error) if looks_like_json(payload) => Err(ExprPayloadError::InvalidSerialized {
            path,
            error: error.to_string(),
        }),
        Err(_) => Err(ExprPayloadError::PrettyOnly { path }),
    }
}

fn looks_like_json(payload: &str) -> bool {
    let trimmed = payload.trim_start();
    trimmed.starts_with('{')
        || trimmed.starts_with('[')
        || trimmed.starts_with('"')
        || trimmed.starts_with("null")
}

fn server_local_context(
    obligation: &MathObligation,
) -> Result<Vec<server_proof_state::ObligationLocalHypothesis>, ExprPayloadError> {
    obligation
        .local_context
        .iter()
        .enumerate()
        .map(|(idx, local)| {
            let type_expr = match local.type_expr.as_deref() {
                Some(payload) => Some(parse_serialized_expr(
                    format!("local_context[{idx}].type_expr"),
                    payload,
                )?),
                None => None,
            };
            Ok(server_proof_state::ObligationLocalHypothesis {
                name: local.name.clone(),
                type_expr,
                type_pp: local.type_pp.clone(),
                value_expr: None,
                value_pp: None,
            })
        })
        .collect()
}

fn blocked_open_obligation_report(
    project: &str,
    domain_profile: &str,
    error: ExprPayloadError,
) -> ProofStateOpenObligationReport {
    match error {
        ExprPayloadError::PrettyOnly { path } => ProofStateOpenObligationReport::blocked(
            project,
            domain_profile,
            pretty_only_status(&path),
            format!(
                "{path} must be serialized clean_kernel::Expr JSON; pretty-only obligations cannot open server proof states"
            ),
        ),
        ExprPayloadError::InvalidSerialized { path, error } => {
            ProofStateOpenObligationReport::blocked(
                project,
                domain_profile,
                invalid_serialized_status(&path),
                format!("{path} is not valid serialized clean_kernel::Expr JSON: {error}"),
            )
        }
    }
}

fn pretty_only_status(path: &str) -> &'static str {
    if path == "goal.expr" {
        "blocked-pretty-only-obligation"
    } else {
        "blocked-pretty-only-local-context"
    }
}

fn invalid_serialized_status(path: &str) -> &'static str {
    if path == "goal.expr" {
        "blocked-invalid-serialized-goal"
    } else {
        "blocked-invalid-serialized-local-context"
    }
}

#[derive(Debug)]
enum ExprPayloadError {
    PrettyOnly { path: String },
    InvalidSerialized { path: String, error: String },
}

#[cfg(not(target_arch = "wasm32"))]
fn run_open_obligation_in_embedded_server(
    root: PathBuf,
    request: server_proof_state::OpenObligationRequest,
) -> Result<Response, MathError> {
    std::thread::spawn(move || {
        let runtime = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .map_err(|error| {
                MathError::Failed(format!("failed to start proof-state runtime: {error}"))
            })?;
        let state = ServerState::from_root(&root);
        Ok(runtime.block_on(handle_open_obligation(
            &state,
            RequestId::Number(1),
            request,
        )))
    })
    .join()
    .map_err(|_| MathError::Failed("embedded proof-state server thread panicked".to_owned()))?
}

/// wasm32 variant: the embedded open-obligation path needs the in-process
/// server handlers (tokio), which are native-only.
#[cfg(target_arch = "wasm32")]
fn run_open_obligation_in_embedded_server(
    _root: PathBuf,
    _request: server_proof_state::OpenObligationRequest,
) -> Result<Response, MathError> {
    Err(MathError::Failed(
        "the embedded proof-state server is native-only and unavailable on wasm".to_owned(),
    ))
}

fn run_open_obligation_in_persistent_server(
    server: &str,
    request: &server_proof_state::OpenObligationRequest,
) -> Result<Response, MathError> {
    let value = call_json_rpc(
        server,
        "proofState.openObligation",
        serde_json::to_value(request)?,
    )?;
    serde_json::from_value(value).map_err(|err| {
        MathError::Failed(format!(
            "server proofState.openObligation returned an invalid JSON-RPC response: {err}"
        ))
    })
}

fn call_proof_state_server(
    server: &str,
    method: &'static str,
    params: serde_json::Value,
) -> Result<serde_json::Value, MathError> {
    let response = call_json_rpc(server, method, params)?;
    let envelope: JsonRpcEnvelope = serde_json::from_value(response).map_err(|err| {
        MathError::Failed(format!(
            "server `{method}` returned an invalid JSON-RPC response: {err}"
        ))
    })?;
    if let Some(error) = envelope.error {
        return Err(MathError::Failed(format!(
            "server `{method}` failed: {}",
            error.message
        )));
    }
    envelope.result.ok_or_else(|| {
        MathError::Failed(format!(
            "server `{method}` returned neither result nor error"
        ))
    })
}

fn call_proof_state_server_or_report(
    json_output: bool,
    operation: &'static str,
    state_id: &str,
    server: &str,
    method: &'static str,
    params: serde_json::Value,
) -> Result<serde_json::Value, MathError> {
    match call_proof_state_server(server, method, params) {
        Ok(result) => Ok(result),
        Err(err) => {
            let report = ProofStateBridgeReport {
                schema_version: "clean-proof-state-v2-bridge-v1",
                operation,
                state: Some(state_id.to_owned()),
                status: "blocked-server-rpc-error",
                detail: format!(
                    "persistent proof-state server `{server}` rejected `{method}`: {err}"
                ),
            };
            write_output(json_output, &report, |out| {
                render_proof_state_report(out, &report)
            })?;
            Err(err)
        }
    }
}

fn call_json_rpc(
    server: &str,
    method: &'static str,
    params: serde_json::Value,
) -> Result<serde_json::Value, MathError> {
    // `localhost` is `127.0.0.1`, the one address `clean server` binds: a
    // resolver may answer `::1` first, where another user can listen on the
    // server's port, and the first message carries the token.
    let address = clean_server::client_server_address(server);
    let server: &str = &address;
    // A connection's first message presents the server's launch token
    // (`CLEAN_SERVER_TOKEN`, `CLEAN_SERVER_TOKEN_FILE`, or, for a server on
    // 127.0.0.1, the default token file of a server on that port); the server
    // answers nothing else first.
    let token = clean_server::client_launch_token(server).map_err(|err| {
        MathError::Failed(format!(
            "no launch token for proof-state server `{server}`: {err}"
        ))
    })?;
    let mut stream = TcpStream::connect(server).map_err(|err| {
        MathError::Failed(format!(
            "failed to connect to proof-state server `{server}`: {err}"
        ))
    })?;
    let timeout = Some(Duration::from_secs(30));
    stream.set_read_timeout(timeout)?;
    stream.set_write_timeout(timeout)?;
    let mut reader = BufReader::new(stream.try_clone()?);
    let hello = json!({
        "jsonrpc": "2.0",
        "method": "authenticate",
        "params": { "token": token.as_str() },
        "id": 0,
    });
    writeln!(stream, "{}", serde_json::to_string(&hello)?)?;
    stream.flush()?;
    let admitted: JsonRpcEnvelope =
        serde_json::from_str(&read_response_line(&mut reader, server)?)?;
    if let Some(error) = admitted.error {
        return Err(MathError::Failed(format!(
            "proof-state server `{server}` refused the launch token: {}",
            error.message
        )));
    }

    let request = json!({
        "jsonrpc": "2.0",
        "method": method,
        "params": params,
        "id": 1,
    });
    writeln!(stream, "{}", serde_json::to_string(&request)?)?;
    stream.flush()?;
    serde_json::from_str(&read_response_line(&mut reader, server)?).map_err(Into::into)
}

/// One response line from the proof-state server.
fn read_response_line(
    reader: &mut BufReader<TcpStream>,
    server: &str,
) -> Result<String, MathError> {
    let mut line = String::new();
    if reader.read_line(&mut line)? == 0 {
        return Err(MathError::Failed(format!(
            "proof-state server `{server}` closed the connection without a response"
        )));
    }
    Ok(line)
}

fn write_server_result(
    json_output: bool,
    operation: &'static str,
    result: &serde_json::Value,
) -> Result<(), MathError> {
    write_output(json_output, result, |out| {
        writeln!(out, "operation: {operation}")?;
        writeln!(out, "status: server-backed")?;
        writeln!(out, "{}", serde_json::to_string_pretty(result)?)
    })
}

#[derive(Debug, Deserialize)]
struct JsonRpcEnvelope {
    result: Option<serde_json::Value>,
    error: Option<JsonRpcErrorEnvelope>,
}

#[derive(Debug, Deserialize)]
struct JsonRpcErrorEnvelope {
    message: String,
}

fn server_domain_profile(domain: &str) -> server_proof_state::ObligationDomainProfile {
    match domain {
        "sat-pb" => server_proof_state::ObligationDomainProfile::SatPb,
        "smt" => server_proof_state::ObligationDomainProfile::Smt,
        "arithmetic" => server_proof_state::ObligationDomainProfile::Arithmetic,
        "nn-verify" => server_proof_state::ObligationDomainProfile::NnVerify,
        _ => server_proof_state::ObligationDomainProfile::General,
    }
}

fn server_trust_policy(policy: &str) -> server_proof_state::ObligationTrustPolicy {
    match policy {
        "kernel-checked-imports" => server_proof_state::ObligationTrustPolicy::KernelCheckedImports,
        "allow-trusted-arith" => server_proof_state::ObligationTrustPolicy::AllowTrustedArith,
        _ => server_proof_state::ObligationTrustPolicy::ConstructiveOnly,
    }
}

fn server_artifact_ref(artifact: &ArtifactRef) -> server_proof_state::ObligationArtifactRef {
    server_proof_state::ObligationArtifactRef {
        kind: match artifact.kind.as_str() {
            "opb" => server_proof_state::ObligationArtifactKind::Opb,
            "veripb" => server_proof_state::ObligationArtifactKind::VeriPb,
            "dimacs" => server_proof_state::ObligationArtifactKind::Dimacs,
            "lrat" => server_proof_state::ObligationArtifactKind::Lrat,
            "drat" => server_proof_state::ObligationArtifactKind::Drat,
            "lean" => server_proof_state::ObligationArtifactKind::Lean,
            _ => server_proof_state::ObligationArtifactKind::Other,
        },
        sha256: artifact
            .hash
            .as_deref()
            .and_then(|hash| hash.strip_prefix("sha256:"))
            .map(str::to_owned),
        path: Some(artifact.path.clone()),
        media_type: Some(artifact.kind.clone()),
    }
}

fn open_obligation_metadata(
    project_path: &Path,
    obligation_source_path: &Path,
    project: &str,
    obligation_fingerprint: &str,
    obligation: &MathObligation,
    artifact_refs: Vec<server_proof_state::ObligationArtifactRef>,
) -> server_proof_state::ProofStateMetadata {
    let project_root = project_path.parent().unwrap_or_else(|| Path::new("."));
    server_proof_state::ProofStateMetadata {
        project: Some(project.to_owned()),
        project_path: Some(project_path.display().to_string()),
        project_root: Some(project_root.display().to_string()),
        obligation_fingerprint: Some(obligation_fingerprint.to_owned()),
        obligation_source_path: Some(obligation_source_path.display().to_string()),
        source_origin: obligation
            .metadata
            .get("source_origin")
            .cloned()
            .or_else(|| Some(obligation.producer.system.clone())),
        producer: Some(server_proof_state::ProofStateProducerMetadata {
            system: obligation.producer.system.clone(),
            commit: obligation.producer.commit.clone(),
            command: obligation.producer.command.clone(),
        }),
        artifact_refs,
    }
}

fn write_open_obligation_report(
    json: bool,
    report: &ProofStateOpenObligationReport,
) -> Result<(), MathError> {
    write_output(json, report, |out| {
        if let Some(state_id) = &report.state_id {
            writeln!(out, "state_id: {state_id}")?;
        }
        writeln!(out, "status: {}", report.status)
    })
}

#[derive(Debug, Serialize)]
pub(super) struct ProofStateBridgeReport {
    pub(super) schema_version: &'static str,
    pub(super) operation: &'static str,
    pub(super) state: Option<String>,
    pub(super) status: &'static str,
    pub(super) detail: String,
}

#[derive(Debug, Serialize)]
struct ProofStateOpenObligationReport {
    schema_version: &'static str,
    operation: &'static str,
    project: String,
    domain_profile: String,
    state_id: Option<String>,
    persistence: &'static str,
    status: String,
    detail: String,
}

impl ProofStateOpenObligationReport {
    fn blocked(project: &str, domain_profile: &str, status: &str, detail: String) -> Self {
        Self {
            schema_version: "clean-cli-proof-state-open-obligation-v1",
            operation: "open-obligation",
            project: project.to_owned(),
            domain_profile: domain_profile.to_owned(),
            state_id: None,
            persistence: "none",
            status: status.to_owned(),
            detail,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::source_theorem::find_source_theorem_decl;
    use super::*;
    use clean_parser::{parse_file_with_tactics, SurfaceDecl};
    use std::fs;

    fn parsed_theorems(source: &str) -> Vec<SurfaceDecl> {
        parse_file_with_tactics(source, &Default::default()).expect("theorem fixture parses")
    }

    #[test]
    fn source_theorem_lookup_preserves_component_boundaries() {
        let source = "theorem «A.B» : True := True.intro\nnamespace A\ntheorem B : True := True.intro\nend A\n";
        let decls = parsed_theorems(source);
        let quoted = find_source_theorem_decl(&decls, "«A.B»").expect("quoted theorem");
        let nested = find_source_theorem_decl(&decls, "A.B").expect("nested theorem");
        assert_eq!(quoted.1, "«A.B»");
        assert_eq!(nested.1, "A.B");
        assert_ne!(quoted.0, nested.0);
        assert!(find_source_theorem_decl(&decls, "Missing.B").is_none());
        assert!(find_source_theorem_decl(&decls, "A.B trailing").is_none());
        assert!(find_source_theorem_decl(&decls, ".B").is_none());
    }

    #[test]
    fn source_theorem_short_lookup_requires_unique_structural_name() {
        let decls = parsed_theorems("namespace A\ntheorem chosen : True := True.intro\nend A\nnamespace B\ntheorem chosen : True := True.intro\nend B\n");
        assert!(find_source_theorem_decl(&decls, "chosen").is_none());
        assert_eq!(
            find_source_theorem_decl(&decls, "A.chosen")
                .expect("exact A")
                .1,
            "A.chosen"
        );
        let unique =
            parsed_theorems("namespace «A.B»\ntheorem chosen : True := True.intro\nend «A.B»\n");
        assert_eq!(
            find_source_theorem_decl(&unique, "chosen")
                .expect("unique short")
                .1,
            "«A.B».chosen"
        );
        assert!(find_source_theorem_decl(&unique, "A.B.chosen").is_none());
        assert!(find_source_theorem_decl(&unique, "_root_.chosen").is_none());
    }

    #[test]
    fn source_theorem_quoted_numeral_does_not_accept_numeric_expression() {
        let decls = parsed_theorems("theorem «7» : True := True.intro\n");
        assert!(find_source_theorem_decl(&decls, "«7»").is_some());
        assert!(find_source_theorem_decl(&decls, "7").is_none());
    }

    #[test]
    fn source_theorem_handle_preserves_quoted_whitespace_and_delimiters() {
        let state =
            source_theorem_state_id("project : λ", Path::new("/tmp/a:b.lean"), "«a b:c».«λ 星»");
        let handle = parse_source_theorem_state_id(&state).expect("exact handle");
        assert_eq!(handle.project, "project : λ");
        assert_eq!(handle.theorem, "«a b:c».«λ 星»");
        assert_eq!(handle.file, PathBuf::from("/tmp/a:b.lean"));
        for malformed in [
            "math-theorem-v2:999:x",
            "math-theorem-v2:1:λ1:a/file",
            "math-theorem-v2:not-a-length:x",
        ] {
            assert!(
                parse_source_theorem_state_id(malformed).is_none(),
                "{malformed}"
            );
        }
        let old = parse_source_theorem_state_id("math-theorem:p:A.b:/tmp/a:b.lean")
            .expect("legacy handle");
        assert_eq!(old.theorem, "A.b");
        assert_eq!(old.file, PathBuf::from("/tmp/a:b.lean"));
    }

    #[test]
    fn server_domain_profile_preserves_nn_verify() {
        assert_eq!(
            server_domain_profile("nn-verify"),
            server_proof_state::ObligationDomainProfile::NnVerify
        );
        assert_eq!(
            server_domain_profile("unknown-domain"),
            server_proof_state::ObligationDomainProfile::General
        );
    }

    #[test]
    fn source_theorem_state_id_round_trips_file_and_theorem() {
        let state = source_theorem_state_id(
            "demo project",
            Path::new("/tmp/Demo.lean"),
            "Demo.theorem name",
        );
        let handle = parse_source_theorem_state_id(&state).expect("source theorem handle");

        assert_eq!(handle.project, "demo project");
        assert_eq!(handle.theorem, "Demo.theorem name");
        assert_eq!(handle.file, PathBuf::from("/tmp/Demo.lean"));
    }

    #[test]
    fn source_theorem_snapshot_reports_closed_goal_feedback() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let file = tmp.path().join("Demo.lean");
        fs::write(
            &file,
            "namespace Demo\n\ntheorem solved (h : True) : True := by\n  exact h\n\ntheorem next : True := by\n  exact True.intro\n\nend Demo\n",
        )
        .expect("write theorem");
        let state = source_theorem_state_id("demo", &file, "Demo.solved");
        let handle = parse_source_theorem_state_id(&state).expect("source theorem handle");

        let report =
            source_theorem_snapshot(&state, SnapshotFormat::Llm, handle).expect("snapshot");

        assert_eq!(report.status, "source-backed-theorem-snapshot");
        assert_eq!(report.proof_status, "closed-source-theorem");
        assert!(report.is_solved);
        assert_eq!(report.goals.len(), 1);
        assert!(report.target_debug.contains("True"));
        assert!(report.declaration_source.contains("exact h"));
        assert!(!report.declaration_source.contains("theorem next"));
        assert!(report
            .feedback
            .iter()
            .any(|feedback| feedback.contains("source-backed theorem snapshot")));
    }
}
