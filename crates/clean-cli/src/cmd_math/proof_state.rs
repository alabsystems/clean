// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::env;
use std::fs;
use std::io::{BufRead, BufReader, Write};
use std::net::TcpStream;
use std::path::{Path, PathBuf};
use std::time::Duration;

use clean_kernel::Expr;
use clean_parser::{parse_file_with_tactics, Span, SurfaceDecl, SurfaceExpr};
use clean_server::{
    handlers::{handle_open_obligation, ServerState},
    proof_state as server_proof_state, RequestId, Response,
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

#[derive(Debug)]
struct SourceTheoremHandle {
    project: String,
    theorem: String,
    file: PathBuf,
}

#[derive(Debug, Serialize)]
struct SourceTheoremSnapshotReport {
    schema_version: &'static str,
    operation: &'static str,
    state: String,
    status: &'static str,
    project: String,
    theorem: String,
    file: String,
    line: usize,
    column: usize,
    format: &'static str,
    is_solved: bool,
    proof_status: &'static str,
    binder_count: usize,
    target_debug: String,
    declaration_source: String,
    goals: Vec<SourceTheoremGoal>,
    feedback: Vec<String>,
}

#[derive(Debug, Serialize)]
struct SourceTheoremGoal {
    goal_id: String,
    status: &'static str,
    target_debug: String,
    hypotheses: Vec<String>,
}

fn source_theorem_state_id(project: &str, file: &Path, theorem: &str) -> String {
    format!(
        "math-theorem:{}:{}:{}",
        project.replace(char::is_whitespace, "_"),
        theorem.replace(char::is_whitespace, "_"),
        file.display()
    )
}

fn parse_source_theorem_state_id(state: &str) -> Option<SourceTheoremHandle> {
    let mut parts = state.splitn(4, ':');
    if parts.next()? != "math-theorem" {
        return None;
    }
    Some(SourceTheoremHandle {
        project: parts.next()?.to_owned(),
        theorem: parts.next()?.to_owned(),
        file: PathBuf::from(parts.next()?),
    })
}

fn source_theorem_snapshot(
    state: &str,
    format: SnapshotFormat,
    handle: SourceTheoremHandle,
) -> Result<SourceTheoremSnapshotReport, String> {
    let source = fs::read_to_string(&handle.file).map_err(|err| {
        format!(
            "source-backed theorem snapshot could not read `{}`: {err}",
            handle.file.display()
        )
    })?;
    let patterns = clean_elab::tactic::builtins::builtin_tactic_patterns();
    let decls = parse_file_with_tactics(&source, &patterns).map_err(|err| {
        format!(
            "source-backed theorem snapshot could not parse `{}`: {err}",
            handle.file.display()
        )
    })?;

    let Some((span, parsed_name, binders, target_debug)) =
        find_source_theorem_decl(&decls, &handle.theorem)
    else {
        return Err(format!(
            "source-backed theorem snapshot could not find theorem `{}` in `{}`",
            handle.theorem,
            handle.file.display()
        ));
    };

    let (line, column) = line_column_for_offset(&source, span.start);
    let declaration_source = source_declaration_slice(&source, span.start).unwrap_or_else(|| {
        source
            .get(span.start..span.end)
            .unwrap_or_default()
            .trim()
            .to_owned()
    });
    let proof_status =
        if declaration_source.contains("sorry") || declaration_source.contains("admit") {
            "closed-with-trust-debt"
        } else {
            "closed-source-theorem"
        };
    let mut feedback = vec![
        "source-backed theorem snapshot: the declaration is already closed in the source file"
            .to_owned(),
        "for live tactic application, use a persistent proof-state server".to_owned(),
    ];
    if proof_status == "closed-with-trust-debt" {
        feedback.push(
            "proof text contains `sorry` or `admit`; trust audit must reject this as proof debt"
                .to_owned(),
        );
    }

    let goal = SourceTheoremGoal {
        goal_id: format!("source:{}", parsed_name),
        status: proof_status,
        target_debug: target_debug.clone(),
        hypotheses: binders,
    };

    Ok(SourceTheoremSnapshotReport {
        schema_version: "clean-cli-source-theorem-snapshot-v1",
        operation: "snapshot",
        state: state.to_owned(),
        status: "source-backed-theorem-snapshot",
        project: handle.project,
        theorem: handle.theorem,
        file: handle.file.display().to_string(),
        line,
        column,
        format: match format {
            SnapshotFormat::Json => "json",
            SnapshotFormat::Llm => "llm",
        },
        is_solved: true,
        proof_status,
        binder_count: goal.hypotheses.len(),
        target_debug,
        declaration_source,
        goals: vec![goal],
        feedback,
    })
}

fn find_source_theorem_decl(
    decls: &[SurfaceDecl],
    requested_name: &str,
) -> Option<(Span, String, Vec<String>, String)> {
    find_source_theorem_decl_in_scope(decls, requested_name, "")
}

fn find_source_theorem_decl_in_scope(
    decls: &[SurfaceDecl],
    requested_name: &str,
    namespace: &str,
) -> Option<(Span, String, Vec<String>, String)> {
    let requested_short = requested_name.rsplit('.').next().unwrap_or(requested_name);
    decls.iter().find_map(|decl| match decl {
        SurfaceDecl::Namespace { name, decls, .. } => {
            let nested = if namespace.is_empty() {
                name.clone()
            } else {
                format!("{namespace}.{name}")
            };
            find_source_theorem_decl_in_scope(decls, requested_name, &nested)
        }
        SurfaceDecl::Section { decls, .. } => {
            find_source_theorem_decl_in_scope(decls, requested_name, namespace)
        }
        SurfaceDecl::Theorem {
            span,
            name,
            binders,
            ty,
            proof,
            ..
        } => {
            let full_name = if namespace.is_empty() {
                name.clone()
            } else {
                format!("{namespace}.{name}")
            };
            if name != requested_name && name != requested_short && full_name != requested_name {
                return None;
            }
            let declaration_span = Span::new(span.start, proof.span().end);
            Some((
                declaration_span,
                full_name,
                binders.iter().map(|binder| format!("{binder:?}")).collect(),
                surface_expr_debug(ty),
            ))
        }
        _ => None,
    })
}

fn surface_expr_debug(expr: &SurfaceExpr) -> String {
    format!("{expr:?}")
}

fn line_column_for_offset(source: &str, offset: usize) -> (usize, usize) {
    let mut line = 1;
    let mut line_start = 0;
    for (idx, ch) in source.char_indices() {
        if idx >= offset {
            break;
        }
        if ch == '\n' {
            line += 1;
            line_start = idx + 1;
        }
    }
    (line, offset.saturating_sub(line_start) + 1)
}

fn source_declaration_slice(source: &str, start: usize) -> Option<String> {
    if start >= source.len() {
        return None;
    }
    let line_start = source[..start].rfind('\n').map_or(0, |idx| idx + 1);
    let mut offset = line_start;
    let mut end = source.len();
    let mut seen_start_line = false;

    for line in source[line_start..].split_inclusive('\n') {
        if seen_start_line && is_unindented_declaration_boundary(line) {
            end = offset;
            break;
        }
        seen_start_line = true;
        offset += line.len();
    }

    let slice = source.get(line_start..end)?.trim();
    (!slice.is_empty()).then(|| slice.to_owned())
}

fn is_unindented_declaration_boundary(line: &str) -> bool {
    let Some(first) = line.chars().next() else {
        return false;
    };
    if first.is_whitespace() {
        return false;
    }

    let trimmed = line.trim_start();
    const BOUNDARIES: &[&str] = &[
        "@[",
        "/--",
        "/-!",
        "#",
        "abbrev ",
        "axiom ",
        "class ",
        "def ",
        "end ",
        "example ",
        "inductive ",
        "instance ",
        "lemma ",
        "namespace ",
        "noncomputable ",
        "opaque ",
        "private ",
        "protected ",
        "section ",
        "set_option ",
        "structure ",
        "theorem ",
    ];
    BOUNDARIES
        .iter()
        .any(|boundary| trimmed.starts_with(boundary))
}

fn render_source_theorem_snapshot(
    out: &mut dyn Write,
    report: &SourceTheoremSnapshotReport,
) -> std::io::Result<()> {
    writeln!(out, "operation: {}", report.operation)?;
    writeln!(out, "status: {}", report.status)?;
    writeln!(out, "theorem: {}", report.theorem)?;
    writeln!(
        out,
        "file: {}:{}:{}",
        report.file, report.line, report.column
    )?;
    writeln!(out, "proof_status: {}", report.proof_status)?;
    writeln!(out, "target: {}", report.target_debug)?;
    for feedback in &report.feedback {
        writeln!(out, "- {feedback}")?;
    }
    Ok(())
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
    let mut stream = TcpStream::connect(server).map_err(|err| {
        MathError::Failed(format!(
            "failed to connect to proof-state server `{server}`: {err}"
        ))
    })?;
    let timeout = Some(Duration::from_secs(30));
    stream.set_read_timeout(timeout)?;
    stream.set_write_timeout(timeout)?;

    let request = json!({
        "jsonrpc": "2.0",
        "method": method,
        "params": params,
        "id": 1,
    });
    writeln!(stream, "{}", serde_json::to_string(&request)?)?;
    stream.flush()?;

    let mut reader = BufReader::new(stream);
    let mut line = String::new();
    let bytes = reader.read_line(&mut line)?;
    if bytes == 0 {
        return Err(MathError::Failed(format!(
            "proof-state server `{server}` closed the connection without a response"
        )));
    }
    serde_json::from_str(&line).map_err(Into::into)
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
    use super::*;

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

        assert_eq!(handle.project, "demo_project");
        assert_eq!(handle.theorem, "Demo.theorem_name");
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
