// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use clean_kernel::{env::DeclarationTrustSummary, Environment, Expr};
use clean_server::{
    handlers::{handle_apply_tactic, handle_open_obligation, ApplyTacticParams, ServerState},
    proof_state as server_proof_state, RequestId, Response,
};
use serde::Serialize;
use serde_json::Value;
use sha2::{Digest, Sha256};

use super::args::{
    ArtifactReplayArgs, ArtifactValidateArgs, CertificateExtractArgs, MathArtifactCommands,
    MathCertificateCommands, MathCommands, MathIssuePlanArgs, MathObligationCommands,
    MathProfileCommands, MathProjectCommands, MathProofStateCommands, MathTaskCommands,
    MathTaskListArgs, MathTaskStatusArgs, MathTaskStatusValue, MathTaskUpdateArgs,
    MathTheoremIndexArgs, ObligationOpenArgs, ObligationProveArgs, ObligationValidateArgs,
    ProfileInspectArgs, ProjectInitArgs, ProjectInitLayout, ProjectStatusArgs,
};
use super::artifact::{load_artifact, replay_artifact, ArtifactEnvelopeReport};
use super::error::MathError;
use super::output::{
    fail_on_violations, render_artifact, render_certificate, render_hygiene, render_project_status,
    write_output,
};
use super::proof_state::{
    run_proof_state_apply, run_proof_state_attempt, run_proof_state_extract, run_proof_state_goal,
    run_proof_state_lifecycle, run_proof_state_open, run_proof_state_open_obligation,
    run_proof_state_snapshot,
};
use super::theorem_index::wrap_theorem_index_report;
use crate::math_project::task_lifecycle::{
    list_tasks, task_status, update_task, TaskStatus, TaskUpdate,
};
use crate::math_project::{
    apply_issue_plan_open_dedupe, built_in_profile, certificate_summary, display_project_relative,
    hygiene_report, issue_plan_report, load_json, load_project, obligation_fingerprint,
    obligation_report, open_obligation_report, pilot_manifest, project_dashboard_report,
    project_status_report, replay_cache_roots, resolve_project_path, validate_obligation,
    write_json, ArtifactReplayAdapterRegistry, DomainProfile, DomainProfileRegistry,
    DomainTacticNormalizerPlan, IssuePlanFilingMetadata, IssuePlanRow, KernelProofEvidence,
    MathObligation, MathProjectError, MathProjectManifest, ReplayCacheEntry, ReplayCacheIndex,
    ReplayCacheRoots, ReplayCacheWrite, ValidationViolation, CERTIFICATE_SCHEMA_VERSION,
    DEFAULT_REPLAY_CACHE_ROOT, KERNEL_PROOF_EVIDENCE_SCHEMA_VERSION,
    REPLAY_CACHE_INDEX_SCHEMA_VERSION, REPLAY_CACHE_ROOTS_SCHEMA_VERSION,
};
use clean_kernel::cert::{CertVerifier, ProofCert};
use clean_kernel::TypeChecker;

pub(crate) fn handle_math_command(command: MathCommands) -> Result<(), MathError> {
    match command {
        MathCommands::Project { command } => match command {
            MathProjectCommands::Status(args) => run_project_status(args),
            MathProjectCommands::Init(args) => run_project_init(args),
            MathProjectCommands::Hygiene(args) => run_project_hygiene(args),
            MathProjectCommands::Dashboard(args) => run_project_dashboard(args),
        },
        MathCommands::Profile { command } => match command {
            MathProfileCommands::Inspect(args) => run_profile_inspect(args),
        },
        MathCommands::TheoremIndex(args) => run_theorem_index(args),
        MathCommands::Obligation { command } => match command {
            MathObligationCommands::Validate(args) => run_obligation_validate(args),
            MathObligationCommands::Open(args) => run_obligation_open(args),
            MathObligationCommands::Prove(args) => run_obligation_prove(args),
        },
        MathCommands::Artifact { command } => match command {
            MathArtifactCommands::Validate(args) => run_artifact_validate(args),
            MathArtifactCommands::Replay(args) => run_artifact_replay(args),
        },
        MathCommands::Certificate { command } => match command {
            MathCertificateCommands::Extract(args) => run_certificate_extract(args),
        },
        MathCommands::IssuePlan(args) => run_issue_plan(args),
        MathCommands::Task { command } => match command {
            MathTaskCommands::List(args) => run_task_list(args),
            MathTaskCommands::Status(args) => run_task_status(args),
            MathTaskCommands::Update(args) => run_task_update(args),
        },
        MathCommands::ProofState { command } => match command {
            MathProofStateCommands::Open(args) => run_proof_state_open(args),
            MathProofStateCommands::OpenObligation(args) => run_proof_state_open_obligation(args),
            MathProofStateCommands::Snapshot(args) => run_proof_state_snapshot(args),
            MathProofStateCommands::SearchTheorems(args) => run_proof_state_goal(
                "search-theorems",
                "proofState.searchTheorems",
                args.json,
                &args.state,
                &args.goal,
                args.server.as_deref(),
            ),
            MathProofStateCommands::SearchTactics(args) => run_proof_state_goal(
                "search-tactics",
                "proofState.searchTactics",
                args.json,
                &args.state,
                &args.goal,
                args.server.as_deref(),
            ),
            MathProofStateCommands::Apply(args) => run_proof_state_apply(args),
            MathProofStateCommands::Retain(args) => {
                run_proof_state_lifecycle(args, "retain", "proofState.retain")
            }
            MathProofStateCommands::Close(args) => {
                run_proof_state_lifecycle(args, "close", "proofState.close")
            }
            MathProofStateCommands::ExplainFailure(args) => run_proof_state_attempt(args),
            MathProofStateCommands::Extract(args) => run_proof_state_extract(args),
        },
    }
}

fn run_project_status(args: ProjectStatusArgs) -> Result<(), MathError> {
    let (path, manifest) = match load_project_args(&args.project) {
        Ok(project) => project,
        Err(MathError::Project(err)) if args.json => {
            let resolved = resolve_project_path(&args.project);
            let report = ProjectLoadDiagnosticReport::from_error(&resolved, &err);
            write_output(true, &report, |_| Ok(()))?;
            return Err(MathError::Project(err));
        }
        Err(err) => return Err(err),
    };
    let report = project_status_report(&path, &manifest);
    write_output(args.json, &report, |out| {
        render_project_status(out, &report)
    })?;
    fail_on_violations(&report.violations, "project status")?;
    Ok(())
}

fn run_project_init(args: ProjectInitArgs) -> Result<(), MathError> {
    let project_name = args
        .project_name
        .unwrap_or_else(|| format!("{}-pilot", args.domain));
    let manifest = pilot_manifest(&args.domain, &project_name)?;
    let output_path = match args.layout {
        ProjectInitLayout::Manifest => {
            write_json(&args.output, &manifest)?;
            args.output
        }
        ProjectInitLayout::Full => write_full_project_layout(&args.output, &manifest)?,
    };
    let report = InitReport {
        schema_version: "clean-math-project-init-v1",
        path: output_path.display().to_string(),
        layout: args.layout.as_str(),
        project: manifest.project,
        domain_profile: manifest.domain_profile,
    };
    write_output(args.json, &report, |out| {
        writeln!(
            out,
            "wrote {} for project {} ({})",
            report.path, report.project, report.domain_profile
        )
    })?;
    Ok(())
}

fn write_full_project_layout(
    root: &Path,
    manifest: &MathProjectManifest,
) -> Result<PathBuf, MathError> {
    for directory in [
        "theorem_packs",
        "obligations",
        "artifacts",
        "evidence",
        "reports",
    ] {
        create_dir(root.join(directory))?;
    }

    write_seed_file(
        &root.join("theorem_packs").join("Pilot.lean"),
        "theorem pilot_seed_true : True := True.intro\n",
    )?;
    write_json(
        &root.join("obligations").join("pilot.json"),
        &seed_obligation(manifest),
    )?;
    write_seed_file(
        &root.join("artifacts").join("README.md"),
        "# Artifacts\n\nPlace external proof artifacts for replay here.\n",
    )?;
    write_seed_file(
        &root.join("evidence").join("README.md"),
        "# Evidence\n\nPlace replay evidence JSON reports here.\n",
    )?;
    write_seed_file(
        &root.join("reports").join("README.md"),
        "# Reports\n\nPlace generated project reports here.\n",
    )?;

    let manifest_path = root.join("math-project.json");
    write_json(&manifest_path, manifest)?;
    Ok(manifest_path)
}

fn seed_obligation(manifest: &MathProjectManifest) -> MathObligation {
    MathObligation {
        schema_version: "clean-obligation-v1".to_owned(),
        project: manifest.project.clone(),
        domain_profile: manifest.domain_profile.clone(),
        producer: crate::math_project::ObligationProducer {
            system: "clean-math-project-init".to_owned(),
            commit: "seed-layout-v1".to_owned(),
            command: None,
        },
        goal: crate::math_project::ObligationGoal {
            expr: crate::math_project::GoalExpr::string("True"),
            pretty: "True".to_owned(),
        },
        local_context: Vec::new(),
        side_conditions: Vec::new(),
        artifact_refs: Vec::new(),
        metadata: [("seed".to_owned(), "layout-full".to_owned())].into(),
        trust_policy: manifest.trust_policy.name.clone(),
    }
}

fn create_dir(path: PathBuf) -> Result<(), MathError> {
    fs::create_dir_all(&path).map_err(|source| {
        MathProjectError::Io {
            path: path.to_owned(),
            source,
        }
        .into()
    })
}

fn write_seed_file(path: &Path, contents: &str) -> Result<(), MathError> {
    fs::write(path, contents).map_err(|source| {
        MathProjectError::Io {
            path: path.to_owned(),
            source,
        }
        .into()
    })
}

fn run_project_hygiene(args: ProjectStatusArgs) -> Result<(), MathError> {
    let (path, manifest) = load_project_args(&args.project)?;
    let report = hygiene_report(&path, &manifest);
    write_output(args.json, &report, |out| render_hygiene(out, &report))?;
    fail_on_violations(&report.violations, "project hygiene")?;
    if report.status == "fail" {
        return Err(MathError::Failed("project hygiene failed".to_owned()));
    }
    Ok(())
}

fn run_project_dashboard(args: ProjectStatusArgs) -> Result<(), MathError> {
    let (path, manifest) = load_project_args(&args.project)?;
    let report = project_dashboard_report(&path, &manifest);
    write_output(args.json, &report, |out| {
        writeln!(out, "project: {}", report.project)?;
        writeln!(out, "status: {}", report.status)?;
        writeln!(out, "obligations: {}", report.obligations.total)?;
        writeln!(
            out,
            "cached_replay_reports: {}",
            report.replay.cached_reports
        )?;
        writeln!(out, "hygiene: {}", report.hygiene.status)
    })?;
    Ok(())
}

fn run_profile_inspect(args: ProfileInspectArgs) -> Result<(), MathError> {
    let profile = if let Some(project) = &args.project {
        let project_path = resolve_project_path(project);
        DomainProfileRegistry::for_project_path(&project_path).profile(&args.domain)?
    } else {
        built_in_profile(&args.domain)?
    };
    let report = ProfileInspectReport::from_profile(profile);
    write_output(args.json, &report, |out| {
        writeln!(out, "{}: {}", report.name, report.description)?;
        writeln!(out, "semantic_heads: {}", report.semantic_heads.join(", "))?;
        writeln!(out, "normalizers: {}", report.normalizers.join(", "))?;
        writeln!(
            out,
            "tactic_plan: {}",
            report
                .tactic_normalizer_plan
                .tactic_recommendations
                .iter()
                .map(|tactic| tactic.name.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        )?;
        writeln!(
            out,
            "replay_adapters: {}",
            report
                .artifact_replay_registry
                .adapters
                .iter()
                .map(|adapter| format!("{}:{}", adapter.id, adapter.status.lifecycle))
                .collect::<Vec<_>>()
                .join(", ")
        )
    })?;
    Ok(())
}

#[derive(Debug, Serialize)]
struct ProfileInspectReport {
    schema_version: String,
    name: String,
    description: String,
    semantic_heads: Vec<String>,
    normalizers: Vec<String>,
    tactic_recommendations: Vec<String>,
    artifact_formats: Vec<String>,
    certificate_extractors: Vec<String>,
    ranking_signals: Vec<String>,
    blocker_kinds: Vec<String>,
    tactic_normalizer_plan: DomainTacticNormalizerPlan,
    artifact_replay_registry: ArtifactReplayAdapterRegistry,
}

impl ProfileInspectReport {
    fn from_profile(profile: DomainProfile) -> Self {
        let tactic_normalizer_plan = profile.tactic_normalizer_plan();
        let artifact_replay_registry = profile.artifact_replay_registry();
        Self {
            schema_version: profile.schema_version,
            name: profile.name,
            description: profile.description,
            semantic_heads: profile.semantic_heads,
            normalizers: profile.normalizers,
            tactic_recommendations: profile.tactic_recommendations,
            artifact_formats: profile.artifact_formats,
            certificate_extractors: profile.certificate_extractors,
            ranking_signals: profile.ranking_signals,
            blocker_kinds: profile.blocker_kinds,
            tactic_normalizer_plan,
            artifact_replay_registry,
        }
    }
}

fn run_theorem_index(args: MathTheoremIndexArgs) -> Result<(), MathError> {
    let (path, manifest) = load_project_args(&args.project)?;
    let root = path.parent().unwrap_or_else(|| Path::new("."));
    let requested_paths = manifest
        .theorem_packs
        .iter()
        .map(PathBuf::from)
        .collect::<Vec<_>>();
    let factory_report = crate::factory::theorem_index::build_theorem_index(
        root,
        &manifest.domain_profile,
        &requested_paths,
    )?;
    let report = wrap_theorem_index_report(&path, &manifest, factory_report);
    write_output(args.json, &report, |out| {
        writeln!(out, "project: {}", report.project.name)?;
        writeln!(out, "profile: {}", report.profile)?;
        writeln!(out, "theorem_candidates: {}", report.candidates.len())
    })?;
    if report.factory_report.has_errors() {
        return Err(MathError::Failed(
            "project theorem index contains error diagnostics".to_owned(),
        ));
    }
    Ok(())
}

fn run_obligation_validate(args: ObligationValidateArgs) -> Result<(), MathError> {
    let project = if let Some(project_path) = &args.project {
        Some(load_project_args(project_path)?.1)
    } else {
        None
    };
    let obligation = load_json::<MathObligation>(&args.path)?;
    let report = obligation_report(&args.path, &obligation, project.as_ref());
    write_output(args.json, &report, |out| {
        writeln!(out, "project: {}", report.project)?;
        writeln!(out, "domain_profile: {}", report.domain_profile)?;
        writeln!(out, "fingerprint: {}", report.fingerprint)?;
        writeln!(out, "status: {}", report.status)
    })?;
    fail_on_violations(&report.violations, "obligation validation")?;
    Ok(())
}

fn run_obligation_open(args: ObligationOpenArgs) -> Result<(), MathError> {
    let (_project_path, project) = load_project_args(&args.project)?;
    let obligation = load_json::<MathObligation>(&args.path)?;
    let violations = validate_obligation(&obligation, Some(&project));
    fail_on_violations(&violations, "open obligation")?;
    let report = open_obligation_report(&project, &obligation);
    write_output(args.json, &report, |out| {
        writeln!(out, "state_id: {}", report.state_id)?;
        writeln!(out, "status: {}", report.status)
    })?;
    Ok(())
}

fn run_obligation_prove(args: ObligationProveArgs) -> Result<(), MathError> {
    let (project_path, project) = load_project_args(&args.project)?;
    let obligation = load_json::<MathObligation>(&args.path)?;
    let violations = validate_obligation(&obligation, Some(&project));
    fail_on_violations(&violations, "prove obligation")?;
    let fingerprint = obligation_fingerprint(&obligation);
    if args.proof_state {
        let root = project_path
            .parent()
            .unwrap_or_else(|| Path::new("."))
            .to_owned();
        let report =
            run_obligation_prove_embedded(root, &project, &obligation, fingerprint.clone())?;
        write_proof_attempt_report(args.json, &report)?;
        if report.status == "closed" {
            return Ok(());
        }
        return Err(MathError::Failed(
            "proof-state tactic attempts did not close the obligation".to_owned(),
        ));
    }

    let report = ProofAttemptReport {
        schema_version: "clean-math-proof-attempt-v1",
        project: project.project,
        obligation_fingerprint: fingerprint,
        status: "blocked-no-proof-search-v2",
        tactic_attempts: Vec::new(),
        details: vec![
            "obligation parsed and fingerprinted".to_owned(),
            "pass --proof-state to opt in to embedded server-backed proof-state closure".to_owned(),
        ],
    };
    write_proof_attempt_report(args.json, &report)?;
    Err(MathError::Failed(
        "proof closure is not implemented by the CLI-local adapter".to_owned(),
    ))
}

fn run_obligation_prove_embedded(
    root: PathBuf,
    project: &MathProjectManifest,
    obligation: &MathObligation,
    fingerprint: String,
) -> Result<ProofAttemptReport, MathError> {
    let goal_expr = match parse_serialized_expr_for_prove("goal.expr", &obligation.goal.expr) {
        Ok(expr) => expr,
        Err(detail) => {
            return Ok(ProofAttemptReport::blocked(
                &project.project,
                fingerprint,
                "blocked-pretty-only-obligation",
                detail,
            ));
        }
    };
    let local_context = match prove_server_local_context(obligation) {
        Ok(local_context) => local_context,
        Err(detail) => {
            return Ok(ProofAttemptReport::blocked(
                &project.project,
                fingerprint,
                "blocked-pretty-only-local-context",
                detail,
            ));
        }
    };
    let local_assumption = local_assumption_trust(&goal_expr, obligation, &local_context, project);
    if let Some(blocker) = local_assumption.blocker {
        return Ok(ProofAttemptReport::blocked(
            &project.project,
            fingerprint,
            "blocked-untrusted-local-assumption",
            blocker,
        ));
    }
    let tactics = prove_tactic_candidates(
        &project.domain_profile,
        local_assumption.has_accepted_candidate,
    );

    let request = server_proof_state::OpenObligationRequest {
        schema_version: server_proof_state::OPEN_OBLIGATION_SCHEMA_VERSION.to_owned(),
        environment_id: format!(
            "math-project:{}:obligation:{}",
            project.project, fingerprint
        ),
        domain_profile: prove_server_domain_profile(&project.domain_profile),
        goal: server_proof_state::ObligationGoalPayload {
            expr: Some(goal_expr),
            pretty: obligation.goal.pretty.clone(),
            type_expr: None,
            type_pp: None,
        },
        local_context,
        artifact_refs: Vec::new(),
        metadata: None,
        trust_policy: prove_server_trust_policy(&obligation.trust_policy),
        ttl_sec: 600,
        max_states: 128,
        min_schema_version: server_proof_state::PROOF_STATE_SCHEMA_VERSION.to_owned(),
        max_schema_version: server_proof_state::PROOF_STATE_SCHEMA_VERSION.to_owned(),
    };

    run_embedded_proof_attempt(root, project, fingerprint, request, tactics)
}

fn run_artifact_validate(args: ArtifactValidateArgs) -> Result<(), MathError> {
    let artifact = load_artifact(&args.path)?;
    let report = ArtifactEnvelopeReport::from_artifact(&args.path, &artifact);
    write_output(args.json, &report, |out| render_artifact(out, &report))?;
    Ok(())
}

fn run_artifact_replay(args: ArtifactReplayArgs) -> Result<(), MathError> {
    let project = if let Some(project_path) = &args.project {
        Some(load_project_args(project_path)?)
    } else {
        None
    };
    let cache_requested = args.cache || args.cache_dir.is_some();
    if cache_requested && project.is_none() {
        return Err(MathError::Failed(
            "artifact replay cache writes require --project so the project root is known"
                .to_owned(),
        ));
    }
    let profile = project
        .as_ref()
        .map(|(project_path, manifest)| {
            DomainProfileRegistry::for_project_path(project_path).profile(&manifest.domain_profile)
        })
        .transpose()?;
    let artifact = load_artifact(&args.path)?;
    let mut report = replay_artifact(
        &args.path,
        project
            .as_ref()
            .map(|(_, manifest)| manifest.project.clone()),
        &artifact,
        profile.as_ref(),
    );
    if let Some((project_path, manifest)) = &project {
        report.linked_obligations =
            linked_obligations_for_artifact(project_path, manifest, Some(&args.path), &artifact);
    }
    if cache_requested {
        if let Some((project_path, manifest)) = &project {
            report.cache = Some(write_replay_cache(
                project_path,
                manifest,
                args.cache_dir.as_deref(),
                &report,
            )?);
        }
    }
    write_output(args.json, &report, |out| {
        writeln!(out, "artifact_kind: {}", report.artifact_kind)?;
        writeln!(out, "evidence_kind: {}", report.evidence_kind)?;
        writeln!(out, "kernel_certified: {}", report.kernel_certified)?;
        writeln!(out, "replay_status: {}", report.replay_status)?;
        writeln!(out, "adapter: {}", report.replay_adapter)?;
        if let Some(descriptor_id) = &report.adapter_descriptor_id {
            writeln!(out, "adapter_descriptor: {descriptor_id}")?;
        }
        if let Some(lifecycle) = &report.adapter_lifecycle {
            writeln!(out, "adapter_lifecycle: {lifecycle}")?;
        }
        writeln!(
            out,
            "linked_obligations: {}",
            report.linked_obligations.len()
        )
    })?;
    if report.replay_status != "pass" {
        return Err(MathError::Failed(format!(
            "artifact replay {}",
            report.replay_status
        )));
    }
    Ok(())
}

fn write_replay_cache(
    project_path: &Path,
    manifest: &MathProjectManifest,
    cache_dir_arg: Option<&Path>,
    report: &crate::math_project::ArtifactReplayReport,
) -> Result<ReplayCacheWrite, MathError> {
    let root = project_path.parent().unwrap_or_else(|| Path::new("."));
    let cache_dir = match cache_dir_arg {
        Some(path) if path.is_absolute() => path.to_owned(),
        Some(path) => root.join(path),
        None => root.join(DEFAULT_REPLAY_CACHE_ROOT),
    };
    create_dir(cache_dir.join("reports"))?;
    let report_name = replay_cache_report_name(report);
    let report_path = cache_dir.join("reports").join(report_name);
    write_json(&report_path, report)?;

    let entry = ReplayCacheEntry {
        report_path: display_project_relative(root, &report_path),
        artifact_path: report.artifact_path.clone(),
        proof_hash: report.proof_hash.clone(),
        replay_status: report.replay_status.to_owned(),
        replay_adapter: report.replay_adapter.clone(),
        linked_obligations: report.linked_obligations.clone(),
    };
    let index_path = cache_dir.join("index.json");
    let mut index =
        load_json::<ReplayCacheIndex>(&index_path).unwrap_or_else(|_| ReplayCacheIndex {
            schema_version: REPLAY_CACHE_INDEX_SCHEMA_VERSION.to_owned(),
            project: manifest.project.clone(),
            project_root: root.display().to_string(),
            reports: Vec::new(),
        });
    index.schema_version = REPLAY_CACHE_INDEX_SCHEMA_VERSION.to_owned();
    index.project = manifest.project.clone();
    index.project_root = root.display().to_string();
    index.reports.retain(|existing| {
        existing.report_path != entry.report_path
            && !(existing.artifact_path == entry.artifact_path
                && existing.proof_hash == entry.proof_hash)
    });
    index.reports.push(entry);
    index.reports.sort_by(|left, right| {
        left.artifact_path
            .cmp(&right.artifact_path)
            .then_with(|| left.proof_hash.cmp(&right.proof_hash))
            .then_with(|| left.report_path.cmp(&right.report_path))
    });
    write_json(&index_path, &index)?;
    write_replay_cache_root_registry(root, manifest, &cache_dir)?;

    Ok(ReplayCacheWrite {
        cache_dir: display_project_relative(root, &cache_dir),
        index_path: display_project_relative(root, &index_path),
        report_path: display_project_relative(root, &report_path),
    })
}

fn replay_cache_report_name(report: &crate::math_project::ArtifactReplayReport) -> String {
    let mut hasher = Sha256::new();
    hasher.update(report.artifact_path.as_bytes());
    hasher.update(b"\0");
    hasher.update(report.proof_hash.as_bytes());
    let digest = hasher
        .finalize()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect::<String>();
    format!(
        "{}-{}.json",
        sanitize_cache_stem(&report.proof_hash),
        &digest[..12]
    )
}

fn sanitize_cache_stem(value: &str) -> String {
    let mut stem = value
        .chars()
        .map(|ch| {
            if ch.is_ascii_alphanumeric() || ch == '-' || ch == '_' {
                ch
            } else {
                '-'
            }
        })
        .collect::<String>();
    stem.truncate(80);
    if stem.is_empty() {
        "replay".to_owned()
    } else {
        stem
    }
}

fn write_replay_cache_root_registry(
    root: &Path,
    manifest: &MathProjectManifest,
    cache_dir: &Path,
) -> Result<(), MathError> {
    let registry_dir = root.join(DEFAULT_REPLAY_CACHE_ROOT);
    create_dir(registry_dir.clone())?;
    let registry_path = registry_dir.join("roots.json");
    let mut registry =
        load_json::<ReplayCacheRoots>(&registry_path).unwrap_or_else(|_| ReplayCacheRoots {
            schema_version: REPLAY_CACHE_ROOTS_SCHEMA_VERSION.to_owned(),
            project: manifest.project.clone(),
            roots: Vec::new(),
        });
    registry.schema_version = REPLAY_CACHE_ROOTS_SCHEMA_VERSION.to_owned();
    registry.project = manifest.project.clone();
    let cache_root = display_project_relative(root, cache_dir);
    if !registry.roots.iter().any(|root| root == &cache_root) {
        registry.roots.push(cache_root);
        registry.roots.sort();
    }
    write_json(&registry_path, &registry)?;
    Ok(())
}

fn run_certificate_extract(args: CertificateExtractArgs) -> Result<(), MathError> {
    let (path, manifest) = load_project_args(&args.project)?;
    let (obligation_id, obligation) =
        certificate_obligation_from_arg(&path, &manifest, &args.obligation);
    let obligation_goal = obligation
        .as_ref()
        .and_then(serialized_certificate_obligation_goal);
    let mut report = certificate_summary(&manifest, &obligation_id, None);
    if let Some(artifact_arg) = args.artifact {
        apply_certificate_artifact_evidence(
            &mut report,
            &path,
            &manifest,
            &obligation_id,
            artifact_arg,
        )?;
    }
    apply_certificate_manifest_kernel_evidence(
        &mut report,
        &path,
        &manifest,
        &obligation_id,
        obligation_goal.as_ref(),
    );
    enforce_kernel_certified_closure(&mut report);
    write_output(args.json, &report, |out| render_certificate(out, &report))?;
    if report.proof_status != "closed" {
        return Err(MathError::Failed(
            "certificate summary is blocked until checked kernel proof evidence is linked"
                .to_owned(),
        ));
    }
    Ok(())
}

fn run_issue_plan(args: MathIssuePlanArgs) -> Result<(), MathError> {
    let (path, manifest) = load_project_args(&args.project)?;
    let mut report = issue_plan_report(&path, &manifest);
    if let Some(snapshot_path) = args.dedupe_open {
        let snapshot = load_json::<Value>(&snapshot_path)?;
        apply_issue_plan_open_dedupe(&mut report, &snapshot);
    }
    if let Some(export_dir) = args.export_dir {
        let export = export_issue_plan_files(
            &report.project,
            &report.domain_profile,
            &export_dir,
            args.write,
            &report.rows,
        )?;
        write_output(args.json, &export, |out| {
            writeln!(out, "project: {}", export.project)?;
            writeln!(out, "export_dir: {}", export.export_dir)?;
            writeln!(
                out,
                "mode: {}",
                if export.write { "write" } else { "dry-run" }
            )?;
            writeln!(out, "created: {}", export.created)?;
            writeln!(out, "skipped_existing: {}", export.skipped_existing)?;
            for file in &export.files {
                writeln!(
                    out,
                    "- [{}] {}",
                    file.status,
                    file.markdown_path
                        .as_deref()
                        .unwrap_or(file.dedupe_key.as_str())
                )?;
            }
            Ok(())
        })?;
        return Ok(());
    }
    write_output(args.json, &report, |out| {
        writeln!(out, "project: {}", report.project)?;
        writeln!(out, "rows: {}", report.rows.len())?;
        for row in &report.rows {
            writeln!(
                out,
                "- [{}][{}] {} / {}: {}",
                row.priority, row.dedupe_status, row.phase, row.workstream, row.title
            )?;
        }
        Ok(())
    })?;
    Ok(())
}

#[derive(Debug, Serialize)]
struct IssuePlanExportReport {
    schema_version: &'static str,
    project: String,
    domain_profile: String,
    export_dir: String,
    write: bool,
    total_rows: usize,
    created: usize,
    skipped_existing: usize,
    files: Vec<IssuePlanExportFile>,
}

#[derive(Debug, Serialize)]
struct IssuePlanExportFile {
    dedupe_key: String,
    title: String,
    status: &'static str,
    reason: &'static str,
    markdown_path: Option<String>,
    json_path: Option<String>,
}

#[derive(Debug, Serialize)]
struct IssuePlanFile<'a> {
    schema_version: &'static str,
    project: &'a str,
    domain_profile: &'a str,
    dedupe_key: &'a str,
    filing_key: &'a str,
    dedupe_status: &'a str,
    phase: &'a str,
    phase_title: &'a str,
    workstream: &'a str,
    title: &'a str,
    priority: &'a str,
    scope: &'a str,
    files: &'a [String],
    labels: &'a [String],
    owners: &'a [String],
    blocking_categories: &'a [String],
    filing_metadata: &'a IssuePlanFilingMetadata,
    dependencies: &'a [String],
    acceptance: &'a [String],
    verification_command: &'a str,
    issue_body: &'a str,
}

fn export_issue_plan_files(
    project: &str,
    domain_profile: &str,
    export_dir: &Path,
    write: bool,
    rows: &[IssuePlanRow],
) -> Result<IssuePlanExportReport, MathError> {
    let mut existing_keys = collect_existing_issue_keys(export_dir)?;
    let mut files = Vec::new();
    let mut created = 0usize;
    let mut skipped_existing = 0usize;

    if write {
        create_dir(export_dir.to_owned())?;
    }

    for row in rows {
        let stem = issue_file_stem(row);
        let markdown_path = export_dir.join(format!("{stem}.md"));
        let json_path = export_dir.join(format!("{stem}.json"));
        if existing_keys.contains(&row.dedupe_key) {
            skipped_existing += 1;
            files.push(IssuePlanExportFile {
                dedupe_key: row.dedupe_key.clone(),
                title: row.title.clone(),
                status: "skipped_existing",
                reason: "dedupe_key_already_present",
                markdown_path: Some(markdown_path.display().to_string()),
                json_path: Some(json_path.display().to_string()),
            });
            continue;
        }

        if write {
            write_issue_markdown(&markdown_path, row)?;
            write_issue_json(&json_path, project, domain_profile, row)?;
            existing_keys.insert(row.dedupe_key.clone());
        }
        created += 1;
        files.push(IssuePlanExportFile {
            dedupe_key: row.dedupe_key.clone(),
            title: row.title.clone(),
            status: if write { "written" } else { "planned" },
            reason: if write { "created" } else { "dry_run" },
            markdown_path: Some(markdown_path.display().to_string()),
            json_path: Some(json_path.display().to_string()),
        });
    }

    Ok(IssuePlanExportReport {
        schema_version: "clean-math-issue-file-export-v1",
        project: project.to_owned(),
        domain_profile: domain_profile.to_owned(),
        export_dir: export_dir.display().to_string(),
        write,
        total_rows: rows.len(),
        created,
        skipped_existing,
        files,
    })
}

fn collect_existing_issue_keys(export_dir: &Path) -> Result<BTreeSet<String>, MathError> {
    let mut keys = BTreeSet::new();
    if !export_dir.exists() {
        return Ok(keys);
    }
    let entries = fs::read_dir(export_dir).map_err(|source| MathProjectError::Io {
        path: export_dir.to_owned(),
        source,
    })?;
    for entry in entries {
        let entry = entry.map_err(|source| MathProjectError::Io {
            path: export_dir.to_owned(),
            source,
        })?;
        let path = entry.path();
        if path.is_file() {
            collect_issue_keys_from_file(&path, &mut keys)?;
        }
    }
    Ok(keys)
}

fn collect_issue_keys_from_file(path: &Path, keys: &mut BTreeSet<String>) -> Result<(), MathError> {
    let contents = fs::read_to_string(path).map_err(|source| MathProjectError::Io {
        path: path.to_owned(),
        source,
    })?;
    if path.extension().and_then(|ext| ext.to_str()) == Some("json") {
        if let Ok(value) = serde_json::from_str::<Value>(&contents) {
            collect_issue_keys_from_json(&value, keys);
        }
    }
    for token in contents
        .split(|ch: char| !(ch.is_ascii_alphanumeric() || ch == '-' || ch == '_' || ch == ':'))
    {
        if token.starts_with("clean-math-issue-") {
            keys.insert(token.to_owned());
        }
    }
    Ok(())
}

fn collect_issue_keys_from_json(value: &Value, keys: &mut BTreeSet<String>) {
    match value {
        Value::Object(map) => {
            for (key, value) in map {
                if key == "dedupe_key" {
                    if let Some(dedupe_key) = value.as_str() {
                        keys.insert(dedupe_key.to_owned());
                    }
                }
                collect_issue_keys_from_json(value, keys);
            }
        }
        Value::Array(items) => {
            for item in items {
                collect_issue_keys_from_json(item, keys);
            }
        }
        _ => {}
    }
}

fn write_issue_markdown(path: &Path, row: &IssuePlanRow) -> Result<(), MathError> {
    let contents = format!(
        "# {}\n\n{}\n\n## Acceptance Criteria\n{}\n\n## Verification\n\n```sh\n{}\n```\n",
        row.title,
        row.issue_body.trim(),
        row.acceptance
            .iter()
            .map(|criterion| format!("- {criterion}"))
            .collect::<Vec<_>>()
            .join("\n"),
        row.verification_command
    );
    fs::write(path, contents).map_err(|source| {
        MathProjectError::Io {
            path: path.to_owned(),
            source,
        }
        .into()
    })
}

fn write_issue_json(
    path: &Path,
    project: &str,
    domain_profile: &str,
    row: &IssuePlanRow,
) -> Result<(), MathError> {
    let file = IssuePlanFile {
        schema_version: "clean-math-issue-file-v1",
        project,
        domain_profile,
        dedupe_key: &row.dedupe_key,
        filing_key: &row.filing_key,
        dedupe_status: &row.dedupe_status,
        phase: row.phase,
        phase_title: row.phase_title,
        workstream: &row.workstream,
        title: &row.title,
        priority: row.priority,
        scope: &row.scope,
        files: &row.files,
        labels: &row.labels,
        owners: &row.owners,
        blocking_categories: &row.blocking_categories,
        filing_metadata: &row.filing_metadata,
        dependencies: &row.dependencies,
        acceptance: &row.acceptance,
        verification_command: &row.verification_command,
        issue_body: &row.issue_body,
    };
    let contents = serde_json::to_string_pretty(&file)?;
    fs::write(path, format!("{contents}\n")).map_err(|source| {
        MathProjectError::Io {
            path: path.to_owned(),
            source,
        }
        .into()
    })
}

fn issue_file_stem(row: &IssuePlanRow) -> String {
    format!(
        "{}-{}-{}",
        slug_segment(row.phase),
        slug_segment(&row.workstream),
        row.dedupe_key
    )
}

fn slug_segment(value: &str) -> String {
    let mut slug = String::new();
    let mut last_dash = false;
    for ch in value.chars() {
        if ch.is_ascii_alphanumeric() {
            slug.push(ch.to_ascii_lowercase());
            last_dash = false;
        } else if !last_dash {
            slug.push('-');
            last_dash = true;
        }
    }
    let slug = slug.trim_matches('-');
    if slug.is_empty() {
        "issue".to_owned()
    } else {
        slug.to_owned()
    }
}

fn run_task_list(args: MathTaskListArgs) -> Result<(), MathError> {
    let (path, manifest) = load_project_args(&args.project)?;
    let report = list_tasks(&path, &manifest)?;
    write_output(args.json, &report, |out| {
        writeln!(out, "project: {}", report.project)?;
        writeln!(out, "task_file: {}", report.task_file)?;
        writeln!(out, "tasks: {}", report.total)?;
        for task in &report.tasks {
            writeln!(
                out,
                "- [{}] {} {}",
                task.status.as_str(),
                task.id,
                task.title
            )?;
        }
        Ok(())
    })?;
    Ok(())
}

fn run_task_status(args: MathTaskStatusArgs) -> Result<(), MathError> {
    let (path, manifest) = load_project_args(&args.project)?;
    let report = task_status(&path, &manifest, &args.obligation)?;
    write_output(args.json, &report, |out| {
        writeln!(out, "task: {}", report.task.id)?;
        writeln!(out, "status: {}", report.task.status.as_str())?;
        writeln!(out, "title: {}", report.task.title)?;
        writeln!(out, "notes: {}", report.task.notes.len())?;
        writeln!(out, "blockers: {}", report.task.blockers.len())
    })?;
    Ok(())
}

fn run_task_update(args: MathTaskUpdateArgs) -> Result<(), MathError> {
    let (path, manifest) = load_project_args(&args.project)?;
    let update = TaskUpdate {
        status: args.status.map(task_status_from_arg),
        append_notes: args.notes,
        append_blockers: args.blockers,
        clear_notes: args.clear_notes,
        clear_blockers: args.clear_blockers,
    };
    let report = update_task(&path, &manifest, &args.obligation, update)?;
    write_output(args.json, &report, |out| {
        writeln!(out, "task: {}", report.task.id)?;
        writeln!(out, "status: {}", report.task.status.as_str())?;
        writeln!(out, "notes: {}", report.task.notes.len())?;
        writeln!(out, "blockers: {}", report.task.blockers.len())
    })?;
    Ok(())
}

fn task_status_from_arg(status: MathTaskStatusValue) -> TaskStatus {
    match status {
        MathTaskStatusValue::Open => TaskStatus::Open,
        MathTaskStatusValue::InProgress => TaskStatus::InProgress,
        MathTaskStatusValue::Blocked => TaskStatus::Blocked,
        MathTaskStatusValue::Done => TaskStatus::Done,
    }
}

pub(super) fn load_project_args(path: &Path) -> Result<(PathBuf, MathProjectManifest), MathError> {
    let resolved = resolve_project_path(path);
    let manifest = load_project(&resolved)?;
    Ok((resolved, manifest))
}

#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
fn obligation_id_from_arg(arg: &str) -> String {
    let path = Path::new(arg);
    if path.exists() {
        if let Ok(obligation) = load_json::<MathObligation>(path) {
            return obligation_fingerprint(&obligation);
        }
    }
    arg.to_owned()
}

fn certificate_obligation_from_arg(
    project_path: &Path,
    manifest: &MathProjectManifest,
    arg: &str,
) -> (String, Option<MathObligation>) {
    let path = Path::new(arg);
    if path.exists() {
        if let Ok(obligation) = load_json::<MathObligation>(path) {
            let fingerprint = obligation_fingerprint(&obligation);
            return (fingerprint, Some(obligation));
        }
    }

    let obligation_id = arg.to_owned();
    let root = project_path.parent().unwrap_or_else(|| Path::new("."));
    for source in &manifest.obligation_sources {
        let source_path = resolve_project_relative_path(root, source);
        let Ok(obligation) = load_json::<MathObligation>(&source_path) else {
            continue;
        };
        if obligation_fingerprint(&obligation) == obligation_id {
            return (obligation_id, Some(obligation));
        }
    }
    (obligation_id, None)
}

fn serialized_certificate_obligation_goal(obligation: &MathObligation) -> Option<Expr> {
    parse_serialized_expr_for_prove("goal.expr", &obligation.goal.expr).ok()
}

fn apply_certificate_artifact_evidence(
    report: &mut crate::math_project::CertificateSummary,
    project_path: &Path,
    manifest: &MathProjectManifest,
    obligation_id: &str,
    artifact_arg: String,
) -> Result<(), MathError> {
    if let Some(artifact_path) = resolve_artifact_arg_path(project_path, &artifact_arg) {
        let artifact = load_artifact(&artifact_path)?;
        if let Some(replay) = cached_certificate_replay_for_artifact(
            project_path,
            manifest,
            obligation_id,
            Some(&artifact_path),
            &artifact.proof_hash,
        ) {
            apply_cached_certificate_replay(report, replay);
            apply_unchecked_artifact_kernel_claim(report, &artifact);
            return Ok(());
        }
        let profile = DomainProfileRegistry::for_project_path(project_path)
            .profile(&manifest.domain_profile)?;
        let replay = replay_artifact(
            &artifact_path,
            Some(manifest.project.clone()),
            &artifact,
            Some(&profile),
        );
        let linked = linked_obligations_for_artifact(
            project_path,
            manifest,
            Some(&artifact_path),
            &artifact,
        );
        let linked_to_obligation = linked
            .iter()
            .any(|fingerprint| fingerprint == obligation_id);

        report.artifact = Some(artifact.proof_hash.clone());
        report.evidence_kind = "replay_only".to_owned();
        report.kernel_certified = false;
        report.proof_status = match replay.replay_status {
            "pass" if linked_to_obligation && replay.trusted_assumptions.is_empty() => {
                "replay-only-artifact-linked-awaiting-kernel-proof".to_owned()
            }
            "pass" if linked_to_obligation => "artifact-replay-trusted-assumptions".to_owned(),
            "pass" => "replayed-artifact-unlinked".to_owned(),
            "fail" => "artifact-replay-failed".to_owned(),
            "blocked" => "artifact-replay-blocked".to_owned(),
            other => format!("artifact-replay-{other}"),
        };
        record_artifact_evidence_status(report);
        report.trust_summary.insert(
            "evidence_kind".to_owned(),
            Value::String(report.evidence_kind.clone()),
        );
        report.trust_summary.insert(
            "kernel_certified".to_owned(),
            Value::Bool(report.kernel_certified),
        );
        report.trust_summary.insert(
            "artifact_path".to_owned(),
            Value::String(artifact_path.display().to_string()),
        );
        report.trust_summary.insert(
            "artifact_replay_status".to_owned(),
            Value::String(replay.replay_status.to_owned()),
        );
        report.trust_summary.insert(
            "artifact_replay_adapter".to_owned(),
            Value::String(replay.replay_adapter),
        );
        if !replay.diagnostics.is_empty() {
            report.trust_summary.insert(
                "artifact_evidence_diagnostics".to_owned(),
                serde_json::to_value(&replay.diagnostics).unwrap_or(Value::Array(Vec::new())),
            );
        }
        apply_unchecked_artifact_kernel_claim(report, &artifact);
        report.trust_summary.insert(
            "trusted_assumptions".to_owned(),
            Value::Array(
                replay
                    .trusted_assumptions
                    .into_iter()
                    .map(Value::String)
                    .collect(),
            ),
        );
        insert_linked_obligations(report, linked);
        return Ok(());
    }

    if let Some(replay) = cached_certificate_replay_for_artifact(
        project_path,
        manifest,
        obligation_id,
        None,
        &artifact_arg,
    ) {
        apply_cached_certificate_replay(report, replay);
        return Ok(());
    }

    let linked = linked_obligations_for_hash(project_path, manifest, &artifact_arg);
    let linked_to_obligation = linked
        .iter()
        .any(|fingerprint| fingerprint == obligation_id);
    report.artifact = Some(artifact_arg);
    report.evidence_kind = "artifact_hash_only".to_owned();
    report.kernel_certified = false;
    report.trust_summary.insert(
        "evidence_kind".to_owned(),
        Value::String(report.evidence_kind.clone()),
    );
    report.trust_summary.insert(
        "kernel_certified".to_owned(),
        Value::Bool(report.kernel_certified),
    );
    report.proof_status = if linked_to_obligation {
        "artifact-hash-linked-replay-not-attested".to_owned()
    } else if linked.is_empty() {
        "artifact-hash-unlinked".to_owned()
    } else {
        "artifact-hash-linked-to-different-obligation".to_owned()
    };
    record_artifact_evidence_status(report);
    insert_linked_obligations(report, linked);
    Ok(())
}

#[derive(Debug)]
struct CheckedCertificateKernelEvidence {
    evidence: KernelProofEvidence,
    evidence_path: String,
    evidence_kind: &'static str,
    trust_summary: Value,
}

#[derive(Debug, Clone, Copy)]
enum KernelEvidencePayloadKind {
    Explicit,
    CertificateSummary,
    ProofStateExtract,
}

fn apply_certificate_manifest_kernel_evidence(
    report: &mut crate::math_project::CertificateSummary,
    project_path: &Path,
    manifest: &MathProjectManifest,
    obligation_id: &str,
    obligation_goal: Option<&Expr>,
) {
    let root = project_path.parent().unwrap_or_else(|| Path::new("."));
    let mut rejection: Option<(String, &'static str)> = None;

    for evidence_ref in &manifest.evidence {
        let evidence_path = resolve_project_relative_path(root, evidence_ref);
        let display_path = display_project_relative(root, &evidence_path);
        let Ok(value) = load_json::<Value>(&evidence_path) else {
            continue;
        };
        let Some(kind) = kernel_evidence_payload_kind(&value) else {
            continue;
        };
        if !kernel_evidence_links_obligation(&value, obligation_id) {
            continue;
        }

        match checked_certificate_kernel_evidence(
            &value,
            kind,
            obligation_id,
            obligation_goal,
            &display_path,
        ) {
            Ok(candidate) => {
                apply_checked_certificate_kernel_evidence(report, candidate);
                return;
            }
            Err(status) => {
                rejection.get_or_insert((display_path, status));
            }
        }
    }

    if let Some((path, status)) = rejection {
        report.trust_summary.insert(
            "kernel_certification_status".to_owned(),
            Value::String(status.to_owned()),
        );
        report.trust_summary.insert(
            "rejected_kernel_evidence_path".to_owned(),
            Value::String(path),
        );
        if report.proof_status == "closed" {
            report.proof_status = "blocked-until-checked-kernel-proof".to_owned();
        }
    }
}

fn kernel_evidence_payload_kind(value: &Value) -> Option<KernelEvidencePayloadKind> {
    if value
        .get("verification")
        .and_then(|verification| verification.get("verified"))
        .is_some()
        && value.get("proof_expr").is_some()
    {
        return Some(KernelEvidencePayloadKind::ProofStateExtract);
    }
    if value.get("schema_version").and_then(Value::as_str)
        == Some(KERNEL_PROOF_EVIDENCE_SCHEMA_VERSION)
    {
        return Some(KernelEvidencePayloadKind::Explicit);
    }
    if value.get("schema").and_then(Value::as_str) == Some(CERTIFICATE_SCHEMA_VERSION)
        || value.get("kernel_evidence").is_some()
    {
        return Some(KernelEvidencePayloadKind::CertificateSummary);
    }
    None
}

fn kernel_evidence_links_obligation(value: &Value, obligation_id: &str) -> bool {
    value.get("obligation").and_then(Value::as_str) == Some(obligation_id)
        || value.get("obligation_fingerprint").and_then(Value::as_str) == Some(obligation_id)
        || value
            .get("linked_obligations")
            .and_then(Value::as_array)
            .is_some_and(|linked| {
                linked
                    .iter()
                    .any(|fingerprint| fingerprint.as_str() == Some(obligation_id))
            })
}

fn kernel_evidence_declares_other_obligation(value: &Value, obligation_id: &str) -> bool {
    let declared = value.get("obligation").and_then(Value::as_str);
    let declared_fingerprint = value.get("obligation_fingerprint").and_then(Value::as_str);
    declared.is_some_and(|declared| declared != obligation_id)
        || declared_fingerprint.is_some_and(|declared| declared != obligation_id)
        || value
            .get("linked_obligations")
            .and_then(Value::as_array)
            .is_some_and(|linked| {
                !linked
                    .iter()
                    .any(|fingerprint| fingerprint.as_str() == Some(obligation_id))
            })
}

fn checked_certificate_kernel_evidence(
    value: &Value,
    kind: KernelEvidencePayloadKind,
    obligation_id: &str,
    obligation_goal: Option<&Expr>,
    evidence_path: &str,
) -> Result<CheckedCertificateKernelEvidence, &'static str> {
    match kind {
        KernelEvidencePayloadKind::ProofStateExtract => {
            checked_proof_state_kernel_evidence(value, obligation_id, evidence_path)
        }
        KernelEvidencePayloadKind::Explicit => checked_explicit_kernel_evidence(
            value,
            obligation_id,
            obligation_goal,
            evidence_path,
            false,
        ),
        KernelEvidencePayloadKind::CertificateSummary => checked_explicit_kernel_evidence(
            value,
            obligation_id,
            obligation_goal,
            evidence_path,
            true,
        ),
    }
}

fn checked_proof_state_kernel_evidence(
    value: &Value,
    _obligation_id: &str,
    _evidence_path: &str,
) -> Result<CheckedCertificateKernelEvidence, &'static str> {
    if value.get("is_solved").and_then(Value::as_bool) != Some(true) {
        return Err("kernel-evidence-unsolved-proof-state");
    }
    if value
        .get("verification")
        .and_then(|verification| verification.get("verified"))
        .and_then(Value::as_bool)
        != Some(true)
    {
        return Err("kernel-evidence-not-checked");
    }
    let Some(trust_summary) = value.get("trust_summary") else {
        return Err("kernel-evidence-missing-trust-summary");
    };
    if !kernel_trust_summary_is_clean(trust_summary) || kernel_evidence_has_hidden_trust_debt(value)
    {
        return Err("kernel-evidence-trust-debt");
    }
    Err("kernel-evidence-proof-state-diagnostic-only")
}

fn checked_explicit_kernel_evidence(
    value: &Value,
    obligation_id: &str,
    obligation_goal: Option<&Expr>,
    evidence_path: &str,
    allow_certificate_summary_trust_shape: bool,
) -> Result<CheckedCertificateKernelEvidence, &'static str> {
    if kernel_evidence_has_hidden_trust_debt(value) {
        return Err("kernel-evidence-trust-debt");
    }
    let evidence_value = value.get("kernel_evidence").unwrap_or(value);
    if kernel_evidence_has_hidden_trust_debt(evidence_value) {
        return Err("kernel-evidence-trust-debt");
    }
    if kernel_evidence_declares_other_obligation(evidence_value, obligation_id) {
        return Err("kernel-evidence-obligation-mismatch");
    }
    let evidence = KernelProofEvidence {
        theorem: string_field(evidence_value, "theorem").unwrap_or_default(),
        proof_hash: string_field(evidence_value, "proof_hash").unwrap_or_default(),
        checker: string_field(evidence_value, "checker").unwrap_or_default(),
        source: string_field(evidence_value, "source")
            .unwrap_or_else(|| format!("kernel-evidence:{evidence_path}")),
        checked: evidence_value
            .get("checked")
            .and_then(Value::as_bool)
            .unwrap_or(false),
    };
    if !checked_kernel_evidence_is_complete(&evidence) {
        return Err("kernel-evidence-incomplete");
    }
    if !checked_kernel_evidence_source_accepted(&evidence.source) {
        return Err("kernel-evidence-unaccepted-source");
    }
    let trust_summary = kernel_trust_summary_for_explicit_evidence(
        value,
        evidence_value,
        allow_certificate_summary_trust_shape,
    )
    .ok_or("kernel-evidence-missing-trust-summary")?;
    if !kernel_trust_summary_is_clean(trust_summary) {
        return Err("kernel-evidence-trust-debt");
    }
    verify_kernel_evidence_payload(evidence_value, obligation_goal)?;
    Ok(CheckedCertificateKernelEvidence {
        evidence,
        evidence_path: evidence_path.to_owned(),
        evidence_kind: "kernel_checked",
        trust_summary: trust_summary.clone(),
    })
}

fn kernel_trust_summary_for_explicit_evidence<'a>(
    value: &'a Value,
    evidence_value: &'a Value,
    allow_certificate_summary_trust_shape: bool,
) -> Option<&'a Value> {
    if let Some(summary) = evidence_value.get("trust_summary") {
        return Some(summary);
    }
    if !allow_certificate_summary_trust_shape {
        return None;
    }
    evidence_value
        .get("kernel_trust_summary")
        .or_else(|| value.get("kernel_trust_summary"))
        .or_else(|| {
            let summary = value.get("trust_summary")?;
            if summary.get("fully_verified").is_some() {
                Some(summary)
            } else {
                summary.get("kernel_trust_summary")
            }
        })
}

fn verify_kernel_evidence_payload(
    evidence_value: &Value,
    obligation_goal: Option<&Expr>,
) -> Result<(), &'static str> {
    let proof_expr = parse_kernel_evidence_expr(evidence_value, "checked_proof_expr")
        .ok_or("kernel-evidence-incomplete")??;
    let target_expr = parse_kernel_evidence_expr(evidence_value, "checked_target_expr")
        .ok_or("kernel-evidence-incomplete")??;
    let certificate =
        parse_kernel_evidence_certificate(evidence_value).ok_or("kernel-evidence-incomplete")??;
    let obligation_goal = obligation_goal.ok_or("kernel-evidence-missing-obligation-goal")?;

    if !DeclarationTrustSummary::from_expr(&proof_expr).is_fully_verified() {
        return Err("kernel-evidence-trust-debt");
    }

    let computed_proof_hash =
        sha256_json_expr(&proof_expr).map_err(|_| "kernel-evidence-proof-hash-failed")?;
    if evidence_value.get("proof_hash").and_then(Value::as_str) != Some(&computed_proof_hash) {
        return Err("kernel-evidence-proof-hash-mismatch");
    }
    let computed_target_hash =
        sha256_json_expr(&target_expr).map_err(|_| "kernel-evidence-target-hash-failed")?;
    if evidence_value
        .get("target_hash")
        .and_then(Value::as_str)
        .is_some_and(|target_hash| target_hash != computed_target_hash)
    {
        return Err("kernel-evidence-target-hash-mismatch");
    }

    let env = Environment::with_prelude();
    let mut verifier = CertVerifier::with_mode(&env, env.mode());
    let verified_type = verifier
        .verify(&certificate, &proof_expr)
        .map_err(|_| "kernel-evidence-certificate-rejected")?;
    let tc = TypeChecker::with_mode(&env, env.mode());
    if !tc.is_def_eq(&verified_type, &target_expr) {
        return Err("kernel-evidence-target-mismatch");
    }
    if !tc.is_def_eq(&target_expr, obligation_goal) {
        return Err("kernel-evidence-obligation-goal-mismatch");
    }
    Ok(())
}

fn parse_kernel_evidence_expr(
    evidence_value: &Value,
    key: &str,
) -> Option<Result<Expr, &'static str>> {
    evidence_value.get(key).map(|value| {
        serde_json::from_value(value.clone()).map_err(|_| "kernel-evidence-invalid-expr")
    })
}

fn parse_kernel_evidence_certificate(
    evidence_value: &Value,
) -> Option<Result<ProofCert, &'static str>> {
    evidence_value
        .get("proof_certificate")
        .map(|value| match value {
            Value::String(serialized) => {
                serde_json::from_str(serialized).map_err(|_| "kernel-evidence-invalid-certificate")
            }
            value => serde_json::from_value(value.clone())
                .map_err(|_| "kernel-evidence-invalid-certificate"),
        })
}

fn sha256_json_expr(expr: &Expr) -> Result<String, serde_json::Error> {
    let bytes = serde_json::to_vec(expr)?;
    let digest = Sha256::digest(bytes);
    Ok(format!(
        "sha256:{}",
        digest
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect::<String>()
    ))
}

fn string_field(value: &Value, key: &str) -> Option<String> {
    value
        .get(key)
        .and_then(Value::as_str)
        .filter(|field| !field.trim().is_empty())
        .map(str::to_owned)
}

fn apply_checked_certificate_kernel_evidence(
    report: &mut crate::math_project::CertificateSummary,
    candidate: CheckedCertificateKernelEvidence,
) {
    report.theorem = candidate.evidence.theorem.clone();
    report.evidence_kind = candidate.evidence_kind.to_owned();
    report.kernel_evidence = Some(candidate.evidence);
    report.proof_status = "closed".to_owned();
    report.trust_summary.insert(
        "evidence_kind".to_owned(),
        Value::String(report.evidence_kind.clone()),
    );
    report.trust_summary.insert(
        "kernel_evidence_source".to_owned(),
        Value::String(candidate.evidence_path),
    );
    report
        .trust_summary
        .insert("kernel_trust_summary".to_owned(), candidate.trust_summary);
}

#[derive(Debug)]
struct CachedCertificateReplay {
    report_path: String,
    artifact_path: String,
    proof_hash: String,
    replay_status: String,
    replay_adapter: String,
    linked_obligations: Vec<String>,
    trusted_assumptions: Vec<String>,
}

fn cached_certificate_replay_for_artifact(
    project_path: &Path,
    manifest: &MathProjectManifest,
    obligation_id: &str,
    artifact_path: Option<&Path>,
    proof_hash: &str,
) -> Option<CachedCertificateReplay> {
    let root = project_path.parent().unwrap_or_else(|| Path::new("."));
    let artifact_canonical = artifact_path.and_then(|path| path.canonicalize().ok());
    for cache_root in replay_cache_roots(root, manifest) {
        let index_path = cache_root.join("index.json");
        let Ok(index) = load_json::<ReplayCacheIndex>(&index_path) else {
            continue;
        };
        if index.schema_version != REPLAY_CACHE_INDEX_SCHEMA_VERSION
            || index.project != manifest.project
        {
            continue;
        }
        for entry in index.reports {
            if entry.proof_hash != proof_hash {
                continue;
            }
            if !artifact_path_matches_cache_entry(root, artifact_canonical.as_deref(), &entry) {
                continue;
            }
            let report_path = resolve_project_relative_path(root, &entry.report_path);
            let Ok(replay) = load_json::<Value>(&report_path) else {
                continue;
            };
            if replay.get("schema_version").and_then(Value::as_str)
                != Some(crate::math_project::ARTIFACT_REPLAY_SCHEMA_VERSION)
            {
                continue;
            }
            if replay.get("proof_hash").and_then(Value::as_str) != Some(proof_hash) {
                continue;
            }
            let linked_obligations = replay_string_array(&replay, "linked_obligations");
            if !linked_obligations
                .iter()
                .any(|fingerprint| fingerprint == obligation_id)
            {
                continue;
            }
            return Some(CachedCertificateReplay {
                report_path: display_project_relative(root, &report_path),
                artifact_path: replay
                    .get("artifact_path")
                    .and_then(Value::as_str)
                    .unwrap_or(&entry.artifact_path)
                    .to_owned(),
                proof_hash: proof_hash.to_owned(),
                replay_status: replay
                    .get("replay_status")
                    .and_then(Value::as_str)
                    .unwrap_or(&entry.replay_status)
                    .to_owned(),
                replay_adapter: replay
                    .get("replay_adapter")
                    .and_then(Value::as_str)
                    .unwrap_or(&entry.replay_adapter)
                    .to_owned(),
                linked_obligations,
                trusted_assumptions: replay_string_array(&replay, "trusted_assumptions"),
            });
        }
    }
    None
}

fn artifact_path_matches_cache_entry(
    root: &Path,
    artifact_canonical: Option<&Path>,
    entry: &ReplayCacheEntry,
) -> bool {
    let Some(artifact_canonical) = artifact_canonical else {
        return true;
    };
    let cache_artifact_path = resolve_project_relative_path(root, &entry.artifact_path);
    cache_artifact_path
        .canonicalize()
        .is_ok_and(|cached| cached == artifact_canonical)
}

fn resolve_project_relative_path(root: &Path, path: &str) -> PathBuf {
    let path = PathBuf::from(path);
    if path.is_absolute() {
        path
    } else {
        root.join(path)
    }
}

fn replay_string_array(replay: &Value, key: &str) -> Vec<String> {
    replay
        .get(key)
        .and_then(Value::as_array)
        .map(|values| {
            values
                .iter()
                .filter_map(Value::as_str)
                .map(str::to_owned)
                .collect()
        })
        .unwrap_or_default()
}

fn apply_cached_certificate_replay(
    report: &mut crate::math_project::CertificateSummary,
    replay: CachedCertificateReplay,
) {
    report.artifact = Some(replay.proof_hash);
    report.evidence_kind = "replay_only".to_owned();
    report.kernel_certified = false;
    report.proof_status = match replay.replay_status.as_str() {
        "pass" if replay.trusted_assumptions.is_empty() => {
            "replay-only-artifact-linked-awaiting-kernel-proof".to_owned()
        }
        "pass" => "artifact-replay-trusted-assumptions".to_owned(),
        "fail" => "artifact-replay-failed".to_owned(),
        "blocked" => "artifact-replay-blocked".to_owned(),
        other => format!("artifact-replay-{other}"),
    };
    record_artifact_evidence_status(report);
    report.trust_summary.insert(
        "evidence_kind".to_owned(),
        Value::String(report.evidence_kind.clone()),
    );
    report.trust_summary.insert(
        "kernel_certified".to_owned(),
        Value::Bool(report.kernel_certified),
    );
    report.trust_summary.insert(
        "artifact_path".to_owned(),
        Value::String(replay.artifact_path),
    );
    report.trust_summary.insert(
        "artifact_replay_status".to_owned(),
        Value::String(replay.replay_status),
    );
    report.trust_summary.insert(
        "artifact_replay_adapter".to_owned(),
        Value::String(replay.replay_adapter),
    );
    report.trust_summary.insert(
        "replay_evidence_source".to_owned(),
        Value::String("project-replay-cache".to_owned()),
    );
    report.trust_summary.insert(
        "replay_cache_report_path".to_owned(),
        Value::String(replay.report_path),
    );
    report.trust_summary.insert(
        "trusted_assumptions".to_owned(),
        Value::Array(
            replay
                .trusted_assumptions
                .into_iter()
                .map(Value::String)
                .collect(),
        ),
    );
    insert_linked_obligations(report, replay.linked_obligations);
}

fn record_artifact_evidence_status(report: &mut crate::math_project::CertificateSummary) {
    report.trust_summary.insert(
        "artifact_evidence_status".to_owned(),
        Value::String(report.proof_status.clone()),
    );
}

fn apply_unchecked_artifact_kernel_claim(
    report: &mut crate::math_project::CertificateSummary,
    artifact: &clean_verify::proof_artifact_v1::ProofArtifactV1,
) {
    let Some(certification) = &artifact.certification else {
        report.trust_summary.insert(
            "kernel_certification_status".to_owned(),
            Value::String("absent".to_owned()),
        );
        return;
    };

    report.trust_summary.insert(
        "artifact_certification_evidence_kind".to_owned(),
        Value::String(match certification.evidence_kind {
            clean_verify::proof_artifact_v1::CertificationEvidenceKind::ReplayOnly => {
                "replay_only".to_owned()
            }
            clean_verify::proof_artifact_v1::CertificationEvidenceKind::KernelCertified => {
                "kernel_certified".to_owned()
            }
        }),
    );

    if certification.evidence_kind
        != clean_verify::proof_artifact_v1::CertificationEvidenceKind::KernelCertified
    {
        report.trust_summary.insert(
            "kernel_certification_status".to_owned(),
            Value::String("absent".to_owned()),
        );
        return;
    }

    let claim = serde_json::json!({
        "theorem": certification.kernel_theorem.as_deref().unwrap_or(""),
        "proof_hash": certification.proof_term_hash.as_deref().unwrap_or(""),
        "checker": certification.checker.as_deref().unwrap_or(""),
        "source": "proof-artifact-v1-certification",
        "checked": false
    });
    report
        .trust_summary
        .insert("claimed_kernel_evidence".to_owned(), claim);
    report.trust_summary.insert(
        "kernel_certification_status".to_owned(),
        Value::String("untrusted-artifact-claim".to_owned()),
    );
}

fn checked_kernel_evidence_is_complete(evidence: &KernelProofEvidence) -> bool {
    evidence.checked
        && !evidence.theorem.trim().is_empty()
        && !evidence.proof_hash.trim().is_empty()
        && !evidence.checker.trim().is_empty()
        && checked_kernel_evidence_source_accepted(&evidence.source)
}

fn checked_kernel_evidence_source_accepted(source: &str) -> bool {
    let source = source.trim();
    source == "explicit-kernel-evidence"
        || source.starts_with("kernel-evidence:")
        || source.starts_with("clean-kernel:")
}

fn report_trust_clean_for_kernel_closure(report: &crate::math_project::CertificateSummary) -> bool {
    if report.synthetic_sorry {
        return false;
    }
    if report
        .trust_summary
        .get("kernel_evidence_hidden_trust_debt")
        .and_then(Value::as_bool)
        == Some(true)
    {
        return false;
    }
    if report
        .trust_summary
        .get("trusted_assumptions")
        .and_then(Value::as_array)
        .is_some_and(|assumptions| !assumptions.is_empty())
    {
        return false;
    }
    report
        .trust_summary
        .get("kernel_trust_summary")
        .is_some_and(kernel_trust_summary_is_clean)
}

fn kernel_trust_summary_is_clean(summary: &Value) -> bool {
    if summary.get("fully_verified").and_then(Value::as_bool) != Some(true) {
        return false;
    }
    for key in ["trusted_assumptions", "trust_debt", "accepted_trust_debt"] {
        if nonempty_array_field(summary, key) {
            return false;
        }
    }
    for key in [
        "sorry_count",
        "ay_count",
        "arith_count",
        "kernel_check_failures",
    ] {
        if summary.get(key).and_then(Value::as_u64).unwrap_or(0) != 0 {
            return false;
        }
    }
    if summary
        .get("sorry_provenance")
        .is_some_and(sorry_provenance_has_debt)
    {
        return false;
    }
    if summary
        .get("ay_provenance")
        .is_some_and(numeric_object_has_debt)
    {
        return false;
    }
    if summary
        .get("arith_provenance")
        .is_some_and(numeric_object_has_debt)
    {
        return false;
    }
    true
}

fn sorry_provenance_has_debt(value: &Value) -> bool {
    value
        .get("has_explicit_sorry")
        .and_then(Value::as_bool)
        .unwrap_or(false)
        || value
            .get("has_synthetic_sorry")
            .and_then(Value::as_bool)
            .unwrap_or(false)
}

fn numeric_object_has_debt(value: &Value) -> bool {
    value.as_object().is_some_and(|object| {
        object
            .values()
            .any(|value| value.as_u64().unwrap_or(0) != 0)
    })
}

fn kernel_evidence_has_hidden_trust_debt(value: &Value) -> bool {
    value.get("synthetic_sorry").and_then(Value::as_bool) == Some(true)
        || nonempty_array_field(value, "trusted_assumptions")
        || nonempty_array_field(value, "trust_debt")
        || nonempty_array_field(value, "accepted_trust_debt")
        || value
            .get("metadata")
            .is_some_and(value_contains_hidden_trust_marker)
        || value
            .get("trust_marker")
            .is_some_and(value_contains_hidden_trust_marker)
        || value
            .get("trust_markers")
            .is_some_and(value_contains_hidden_trust_marker)
}

fn nonempty_array_field(value: &Value, key: &str) -> bool {
    value
        .get(key)
        .and_then(Value::as_array)
        .is_some_and(|values| !values.is_empty())
}

fn value_contains_hidden_trust_marker(value: &Value) -> bool {
    match value {
        Value::String(value) => hidden_trust_marker_string(value),
        Value::Array(values) => values.iter().any(value_contains_hidden_trust_marker),
        Value::Object(object) => object.values().any(value_contains_hidden_trust_marker),
        _ => false,
    }
}

fn hidden_trust_marker_string(value: &str) -> bool {
    [
        "synthetic_sorry",
        "sorryAx",
        "trustedArith",
        "trustedAy",
        "explicit_sorry",
        "trusted_arith",
        "trusted_ay",
    ]
    .iter()
    .any(|marker| value.contains(marker))
        || value.trim() == "sorry"
}

fn enforce_kernel_certified_closure(report: &mut crate::math_project::CertificateSummary) {
    let checked_kernel_evidence = report
        .kernel_evidence
        .as_ref()
        .is_some_and(checked_kernel_evidence_is_complete);
    let trust_clean = report_trust_clean_for_kernel_closure(report);
    let artifact_blocker = artifact_evidence_kernel_closure_blocker(report);

    if !(checked_kernel_evidence && trust_clean && artifact_blocker.is_none()) {
        report.kernel_certified = false;
        if let Some((artifact_status, kernel_status)) = artifact_blocker {
            if report.proof_status == "closed" {
                report.proof_status = artifact_status;
            }
            report.trust_summary.insert(
                "artifact_evidence_closure_blocker".to_owned(),
                Value::String(kernel_status.to_owned()),
            );
            report.trust_summary.insert(
                "kernel_certification_status".to_owned(),
                Value::String(kernel_status.to_owned()),
            );
        } else {
            if report.proof_status == "closed" {
                report.proof_status = if trust_clean {
                    "blocked-until-checked-kernel-proof".to_owned()
                } else {
                    "blocked-kernel-evidence-trust-debt".to_owned()
                };
            }
            if !report
                .trust_summary
                .contains_key("kernel_certification_status")
            {
                report.trust_summary.insert(
                    "kernel_certification_status".to_owned(),
                    Value::String("absent".to_owned()),
                );
            }
        }
    } else {
        report.kernel_certified = true;
        report.proof_status = "closed".to_owned();
        report.trust_summary.insert(
            "kernel_certification_status".to_owned(),
            Value::String("checked-kernel-proof".to_owned()),
        );
    }

    report.trust_summary.insert(
        "kernel_certified".to_owned(),
        Value::Bool(report.kernel_certified),
    );
}

fn artifact_evidence_kernel_closure_blocker(
    report: &crate::math_project::CertificateSummary,
) -> Option<(String, &'static str)> {
    let artifact_status = report
        .trust_summary
        .get("artifact_evidence_status")
        .and_then(Value::as_str)?;
    let kernel_status = match artifact_status {
        "replayed-artifact-unlinked"
        | "artifact-hash-unlinked"
        | "artifact-hash-linked-to-different-obligation" => "artifact-evidence-unlinked",
        "artifact-replay-failed" => "artifact-evidence-replay-failed",
        "artifact-replay-blocked" => "artifact-evidence-replay-blocked",
        status if status.starts_with("artifact-replay-fail") => "artifact-evidence-replay-failed",
        status if status.starts_with("artifact-replay-block") => "artifact-evidence-replay-blocked",
        _ => return None,
    };
    Some((artifact_status.to_owned(), kernel_status))
}

fn resolve_artifact_arg_path(project_path: &Path, artifact_arg: &str) -> Option<PathBuf> {
    let artifact_path = Path::new(artifact_arg);
    if artifact_path.exists() {
        return Some(artifact_path.to_owned());
    }
    let root = project_path.parent().unwrap_or_else(|| Path::new("."));
    let project_relative = root.join(artifact_arg);
    project_relative.exists().then_some(project_relative)
}

fn insert_linked_obligations(
    report: &mut crate::math_project::CertificateSummary,
    linked: Vec<String>,
) {
    report.trust_summary.insert(
        "linked_obligations".to_owned(),
        Value::Array(linked.iter().cloned().map(Value::String).collect()),
    );
}

fn linked_obligations_for_artifact(
    project_path: &Path,
    manifest: &MathProjectManifest,
    artifact_path: Option<&Path>,
    artifact: &clean_verify::proof_artifact_v1::ProofArtifactV1,
) -> Vec<String> {
    let hashes = [
        artifact.problem_hash.as_str(),
        artifact.model_hash.as_str(),
        artifact.proof_hash.as_str(),
    ];
    linked_obligations_for_artifact_ref(project_path, manifest, artifact_path, &hashes)
}

fn linked_obligations_for_hash(
    project_path: &Path,
    manifest: &MathProjectManifest,
    artifact_hash: &str,
) -> Vec<String> {
    linked_obligations_for_artifact_ref(project_path, manifest, None, &[artifact_hash])
}

fn linked_obligations_for_artifact_ref(
    project_path: &Path,
    manifest: &MathProjectManifest,
    artifact_path: Option<&Path>,
    artifact_hashes: &[&str],
) -> Vec<String> {
    let root = project_path.parent().unwrap_or_else(|| Path::new("."));
    let artifact_canonical = artifact_path.and_then(|path| path.canonicalize().ok());
    let hash_set = artifact_hashes
        .iter()
        .copied()
        .filter(|hash| !hash.trim().is_empty())
        .collect::<BTreeSet<_>>();
    let mut linked = BTreeSet::new();

    for source in &manifest.obligation_sources {
        let source_path = root.join(source);
        let Ok(obligation) = load_json::<MathObligation>(&source_path) else {
            continue;
        };
        if obligation.artifact_refs.iter().any(|artifact_ref| {
            artifact_ref
                .hash
                .as_deref()
                .is_some_and(|hash| hash_set.contains(hash))
                || artifact_canonical.as_ref().is_some_and(|artifact_path| {
                    root.join(&artifact_ref.path)
                        .canonicalize()
                        .is_ok_and(|reference_path| reference_path == *artifact_path)
                })
        }) {
            linked.insert(obligation_fingerprint(&obligation));
        }
    }

    linked.into_iter().collect()
}

#[derive(Debug, Serialize)]
struct InitReport {
    schema_version: &'static str,
    path: String,
    layout: &'static str,
    project: String,
    domain_profile: String,
}

#[derive(Debug, Serialize)]
struct ProjectLoadDiagnosticReport {
    schema_version: &'static str,
    project_path: String,
    status: &'static str,
    violations: Vec<ValidationViolation>,
}

impl ProjectLoadDiagnosticReport {
    fn from_error(path: &Path, err: &MathProjectError) -> Self {
        let code = match err {
            MathProjectError::Json { .. } => "MP000",
            MathProjectError::Io { .. } => "MP000",
            MathProjectError::UnknownDomain(_) | MathProjectError::Validation(_) => "MP000",
        };
        let diagnostic_path = match err {
            MathProjectError::Json { source, .. } if source.is_syntax() || source.is_eof() => {
                "manifest_json"
            }
            MathProjectError::Json { .. } => "manifest_schema",
            MathProjectError::Io { .. } => "manifest_path",
            MathProjectError::UnknownDomain(_) | MathProjectError::Validation(_) => "manifest",
        };
        Self {
            schema_version: "clean-math-project-load-diagnostic-v1",
            project_path: path.display().to_string(),
            status: "fail",
            violations: vec![ValidationViolation {
                code,
                severity: "error",
                path: diagnostic_path.to_owned(),
                message: err.to_string(),
            }],
        }
    }
}

#[derive(Debug, Serialize)]
struct ProofAttemptReport {
    schema_version: &'static str,
    project: String,
    obligation_fingerprint: String,
    status: &'static str,
    tactic_attempts: Vec<ProofTacticAttempt>,
    details: Vec<String>,
}

impl ProofAttemptReport {
    fn blocked(
        project: &str,
        obligation_fingerprint: String,
        status: &'static str,
        detail: String,
    ) -> Self {
        Self {
            schema_version: "clean-math-proof-attempt-v1",
            project: project.to_owned(),
            obligation_fingerprint,
            status,
            tactic_attempts: Vec::new(),
            details: vec![detail],
        }
    }
}

#[derive(Debug, Serialize)]
struct ProofTacticAttempt {
    tactic: String,
    status: &'static str,
    detail: String,
}

fn write_proof_attempt_report(json: bool, report: &ProofAttemptReport) -> Result<(), MathError> {
    write_output(json, report, |out| {
        writeln!(out, "status: {}", report.status)?;
        writeln!(
            out,
            "obligation_fingerprint: {}",
            report.obligation_fingerprint
        )
    })
}

fn run_embedded_proof_attempt(
    root: PathBuf,
    project: &MathProjectManifest,
    fingerprint: String,
    request: server_proof_state::OpenObligationRequest,
    tactics: Vec<String>,
) -> Result<ProofAttemptReport, MathError> {
    let project_name = project.project.clone();
    std::thread::spawn(move || {
        let runtime = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .map_err(|error| {
                MathError::Failed(format!("failed to start proof-state runtime: {error}"))
            })?;
        runtime.block_on(async move {
            let state = ServerState::from_root(&root).with_env(Environment::with_prelude());
            let open = handle_open_obligation(&state, RequestId::Number(1), request).await;
            embedded_proof_attempt_from_open(&state, open, &project_name, fingerprint, tactics)
                .await
        })
    })
    .join()
    .map_err(|_| MathError::Failed("embedded proof-state prove thread panicked".to_owned()))?
}

async fn embedded_proof_attempt_from_open(
    state: &ServerState,
    open: Response,
    project: &str,
    fingerprint: String,
    tactics: Vec<String>,
) -> Result<ProofAttemptReport, MathError> {
    if let Some(error) = open.error {
        return Ok(ProofAttemptReport::blocked(
            project,
            fingerprint,
            "blocked-server-open-obligation",
            error.message,
        ));
    }
    let opened: server_proof_state::OpenObligationResponse =
        serde_json::from_value(open.result.ok_or_else(|| {
            MathError::Failed("server open-obligation returned no result".to_owned())
        })?)
        .map_err(|err| {
            MathError::Failed(format!(
                "server open-obligation returned an invalid response: {err}"
            ))
        })?;
    let Some(goal_id) = opened
        .initial_snapshot
        .as_ref()
        .and_then(|snapshot| snapshot.goals.first())
        .map(|goal| goal.goal_id.clone())
    else {
        return Ok(ProofAttemptReport {
            schema_version: "clean-math-proof-attempt-v1",
            project: project.to_owned(),
            obligation_fingerprint: fingerprint,
            status: "blocked-no-goals",
            tactic_attempts: Vec::new(),
            details: vec!["opened proof state did not expose a focused goal".to_owned()],
        });
    };

    let mut attempts = Vec::new();
    for (idx, tactic) in tactics.into_iter().enumerate() {
        let response = handle_apply_tactic(
            state,
            RequestId::Number(idx as i64 + 2),
            ApplyTacticParams {
                state_id: opened.state_id.clone(),
                goal_id: goal_id.clone(),
                tactic: tactic.clone(),
                timeout_ms: Some(1000),
            },
        )
        .await;
        if let Some(error) = response.error {
            attempts.push(ProofTacticAttempt {
                tactic,
                status: "blocked-rpc-error",
                detail: error.message,
            });
            continue;
        }
        let result: server_proof_state::ApplyTacticResult =
            serde_json::from_value(response.result.ok_or_else(|| {
                MathError::Failed("server applyTactic returned no result".to_owned())
            })?)
            .map_err(|err| {
                MathError::Failed(format!(
                    "server applyTactic returned an invalid response: {err}"
                ))
            })?;
        if result.success && result.is_solved {
            attempts.push(ProofTacticAttempt {
                tactic,
                status: "closed",
                detail: format!("closed proof state {}", result.new_state_id),
            });
            return Ok(ProofAttemptReport {
                schema_version: "clean-math-proof-attempt-v1",
                project: project.to_owned(),
                obligation_fingerprint: fingerprint,
                status: "closed",
                tactic_attempts: attempts,
                details: vec![
                    "embedded proof-state tactic attempt closed the obligation".to_owned()
                ],
            });
        }
        attempts.push(ProofTacticAttempt {
            tactic,
            status: if result.success {
                "applied-not-closed"
            } else {
                "failed"
            },
            detail: result
                .error
                .map(|error| error.message)
                .unwrap_or_else(|| "tactic did not close the proof state".to_owned()),
        });
    }

    Ok(ProofAttemptReport {
        schema_version: "clean-math-proof-attempt-v1",
        project: project.to_owned(),
        obligation_fingerprint: fingerprint,
        status: "blocked-unproved",
        tactic_attempts: attempts,
        details: vec!["all conservative proof-state tactic attempts failed to close".to_owned()],
    })
}

fn prove_tactic_candidates(
    domain_profile: &str,
    has_local_assumption_candidate: bool,
) -> Vec<String> {
    let mut tactics = Vec::new();
    if has_local_assumption_candidate {
        tactics.push("assumption".to_owned());
    }
    tactics.extend(["exact True.intro".to_owned(), "rfl".to_owned()]);
    if built_in_profile(domain_profile)
        .map(|profile| {
            profile
                .normalizers
                .iter()
                .any(|normalizer| normalizer == "cert_simp")
        })
        .unwrap_or(false)
    {
        tactics.push("cert_simp".to_owned());
    }
    tactics
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct LocalAssumptionTrust {
    has_accepted_candidate: bool,
    blocker: Option<String>,
}

fn local_assumption_trust(
    goal: &Expr,
    obligation: &MathObligation,
    local_context: &[server_proof_state::ObligationLocalHypothesis],
    project: &MathProjectManifest,
) -> LocalAssumptionTrust {
    let mut first_blocker = None;
    for (idx, (obligation_local, server_local)) in obligation
        .local_context
        .iter()
        .zip(local_context.iter())
        .enumerate()
    {
        if !server_local.type_expr.as_ref().is_some_and(|ty| ty == goal) {
            continue;
        }
        if accepted_local_assumption_provenance(obligation, idx, &obligation_local.name, project)
            .is_some()
        {
            return LocalAssumptionTrust {
                has_accepted_candidate: true,
                blocker: None,
            };
        }
        first_blocker.get_or_insert_with(|| {
            missing_local_assumption_provenance_blocker(idx, &obligation_local.name, project)
        });
    }

    LocalAssumptionTrust {
        has_accepted_candidate: false,
        blocker: first_blocker,
    }
}

fn accepted_local_assumption_provenance(
    obligation: &MathObligation,
    idx: usize,
    local_name: &str,
    project: &MathProjectManifest,
) -> Option<String> {
    local_assumption_provenance_candidates(obligation, idx, local_name)
        .into_iter()
        .find(|provenance| project_accepts_local_assumption_provenance(provenance, project))
}

fn local_assumption_provenance_candidates(
    obligation: &MathObligation,
    idx: usize,
    local_name: &str,
) -> Vec<String> {
    [
        format!("local_context[{idx}].provenance"),
        format!("local_context[{idx}].trust_provenance"),
        format!("local_context.{local_name}.provenance"),
        format!("local_context.{local_name}.trust_provenance"),
    ]
    .into_iter()
    .filter_map(|key| obligation.metadata.get(&key).cloned())
    .collect()
}

fn project_accepts_local_assumption_provenance(
    provenance: &str,
    project: &MathProjectManifest,
) -> bool {
    let provenance = provenance.trim();
    if provenance.is_empty() {
        return false;
    }
    let normalized = provenance.replace('_', "-").to_ascii_lowercase();
    let Some(trusted) = normalized
        .strip_prefix("trusted:")
        .or_else(|| normalized.strip_prefix("trusted-axiom:"))
        .map(str::trim)
        .filter(|trusted| !trusted.is_empty())
    else {
        return false;
    };
    let forbidden = project
        .trust_policy
        .forbidden_trust_markers
        .iter()
        .map(|marker| marker.replace('_', "-").to_ascii_lowercase())
        .collect::<BTreeSet<_>>();
    if forbidden.contains(trusted) {
        return false;
    }
    project
        .trust_policy
        .allowed_axioms
        .iter()
        .any(|allowed| allowed == "*" || allowed.eq_ignore_ascii_case(trusted))
}

fn missing_local_assumption_provenance_blocker(
    idx: usize,
    local_name: &str,
    project: &MathProjectManifest,
) -> String {
    format!(
        "local_context[{idx}] `{local_name}` has the same serialized type as the goal, but proof-state `assumption` requires accepted local provenance under trust policy `{}`; add metadata `local_context[{idx}].provenance` or `local_context.{local_name}.provenance` with checked-kernel provenance, or link replay/kernel evidence instead",
        project.trust_policy.name
    )
}

fn parse_serialized_expr_for_prove(path: &str, payload: &str) -> Result<Expr, String> {
    match serde_json::from_str(payload) {
        Ok(expr) => Ok(expr),
        Err(error) if looks_like_serialized_json(payload) => Err(format!(
            "{path} is not valid serialized clean_kernel::Expr JSON: {error}"
        )),
        Err(_) => Err(format!(
            "{path} must be serialized clean_kernel::Expr JSON; pretty-only obligations cannot use proof-state closure"
        )),
    }
}

fn looks_like_serialized_json(payload: &str) -> bool {
    let trimmed = payload.trim_start();
    trimmed.starts_with('{')
        || trimmed.starts_with('[')
        || trimmed.starts_with('"')
        || trimmed.starts_with("null")
}

fn prove_server_local_context(
    obligation: &MathObligation,
) -> Result<Vec<server_proof_state::ObligationLocalHypothesis>, String> {
    obligation
        .local_context
        .iter()
        .enumerate()
        .map(|(idx, local)| {
            let Some(payload) = local.type_expr.as_deref() else {
                return Err(format!(
                    "local_context[{idx}].type_expr must be serialized clean_kernel::Expr JSON; pretty-only local-context obligations cannot use proof-state closure"
                ));
            };
            let type_expr =
                Some(parse_serialized_expr_for_prove(
                    &format!("local_context[{idx}].type_expr"),
                    payload,
                )?);
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

fn prove_server_domain_profile(domain: &str) -> server_proof_state::ObligationDomainProfile {
    match domain {
        "sat-pb" => server_proof_state::ObligationDomainProfile::SatPb,
        "smt" => server_proof_state::ObligationDomainProfile::Smt,
        "arithmetic" => server_proof_state::ObligationDomainProfile::Arithmetic,
        "nn-verify" => server_proof_state::ObligationDomainProfile::NnVerify,
        _ => server_proof_state::ObligationDomainProfile::General,
    }
}

fn prove_server_trust_policy(policy: &str) -> server_proof_state::ObligationTrustPolicy {
    match policy {
        "kernel-checked-imports" => server_proof_state::ObligationTrustPolicy::KernelCheckedImports,
        "allow-trusted-arith" => server_proof_state::ObligationTrustPolicy::AllowTrustedArith,
        _ => server_proof_state::ObligationTrustPolicy::ConstructiveOnly,
    }
}
