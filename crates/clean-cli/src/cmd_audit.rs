// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CLI wiring for trust audit commands owned by `clean-cli`.
//!
//! Tier 1 surface: only `clean audit trust-ledger <name>`, a focused
//! per-declaration integrity diagnostic. It walks a declaration's recursive
//! dependency closure and reports the trust levels, axioms, and trust markers
//! affecting it, answering "why isn't this declaration kernel-clean".

use std::collections::{BTreeSet, HashMap, HashSet};
use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::time::Instant;

use anyhow::{bail, Context};
use clap::{Args, Subcommand};
use clean_elab::{
    elaborate_decl_and_register_with_context_and_warning, preprocess_decl_with_context, FileContext,
};
use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};
use clean_kernel::{ConstantKind, Environment};
use clean_mathverse::attempt_log::{
    put_artifact, record_authority_gate_attempt, AttemptStatus, AuthorityGateAttempt,
    AuthorityReceipt, ProofAttempt,
};
use clean_mathverse::authority_scope::authority_gate_goal_hash;
use clean_mathverse::env_fingerprint::EnvFingerprint;
use clean_mathverse::trust::audit_report::{
    AuditFinding, AuditFindingCategory, AuditReport, AuditReportBuilder, AuditSeverity,
    KernelAuditKernel,
};
use clean_mathverse::trust::project_audit::{
    audit_lake_project, project_audit_authority_gate_status,
    project_audit_environment_reconstruction_rejected_status, ProjectAuditAuthorityGateStatus,
    ProjectAuditWorkspace, PROJECT_AUDIT_ARTIFACT_KIND, PROJECT_AUDIT_AUTHORITY_GATE,
    PROJECT_AUDIT_GOAL_SHAPE,
};
use clean_mathverse::types::{AxiomProfile, TrustLevel};
use clean_parser::parse_file_with_tactics;
use serde::Serialize;

use crate::authority_source_guard::AuthoritySourceGuard;

const AUTHORITY_COMMAND_EVIDENCE_ARTIFACT_KIND: &str = "authority-gate/command-evidence";
const AUTHORITY_COMMAND_EVIDENCE_SCHEMA: &str = "clean-authority-command-evidence-v1";
const TRUST_LEDGER_SCHEMA: &str = "clean-recursive-trust-ledger-v1";
const TRUST_LEDGER_AUTHORITY_GATE: &str = "trust_ledger";
const TRUST_LEDGER_ARTIFACT_KIND: &str = "authority-gate/trust-ledger";

const OPAQUE_CONSTANT_CATEGORY: &str = "opaque-constant";
const AXIOM_DECLARATION_CATEGORY: &str = "axiom-declaration";

const DESIGN_REF: Reference = Reference {
    kind: RefKind::Design,
    label: "Unified CLI feature index",
    target: "designs/2026-04-18-unified-cli-feature-index.md",
};

const CLI_CRATE_REF: Reference = Reference {
    kind: RefKind::Crate,
    label: "clean-cli",
    target: "clean-cli",
};

const MATHVERSE_CRATE_REF: Reference = Reference {
    kind: RefKind::Crate,
    label: "clean-mathverse",
    target: "clean-mathverse",
};

/// Feature descriptors surfaced by the `clean audit` verb tree.
pub(crate) const FEATURES: &[FeatureDescriptor] = &[
    FeatureDescriptor {
        path: &["audit", "cake"],
        summary: "Audit a Cake/Lake-compatible project trust boundary",
        description: "\
Loads a Cake/Lake-compatible workspace, reconstructs the available Clean \
environment, emits an `AuditReport`, and includes the project-audit \
authority-gate decision. Use \
`--json` for machine-readable output, `--record-attempt` to append a \
`trust_audit` Mathverse proof attempt, and `--report-only` only when you need a \
diagnostic report for a rejected gate. Authority acceptance requires complete \
Lake-project environment reconstruction; `.olean-only` audit evidence is \
diagnostic external-baseline evidence and does not satisfy authority gates.",
        category: Category::Verification,
        stability: Stability::Building,
        examples: &[Example {
            cmd: "clean audit cake . --json",
            what: "emit a JSON audit report for the current Cake/Lake-compatible project",
        }],
        see_also: &["attempts list"],
        references: &[DESIGN_REF, CLI_CRATE_REF, MATHVERSE_CRATE_REF],
        domain_root: Some("audit"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["audit", "soundness"],
        summary: "Emit THE soundness certificate (C1-C5) for the kernel + overlay corpus",
        description: "\
Runs the single mechanical soundness check over the full kernel + math overlay \
environment and prints THE soundness certificate: C1 total re-verification \
(every theorem/definition re-type-checks through the kernel), C2 trusted-axiom \
base enumeration pinned against a checked-in golden, C3 no trust marker \
reachable, C4 carrier-generic refutation resistance (no admitted axiom over any \
concrete carrier is refutable), and C5 deep-nested False-proof rejection. Exits \
non-zero unless the certificate is SOUND. Use `--json` for the machine-readable \
form. Requires the `math-overlays` feature.",
        category: Category::Verification,
        stability: Stability::Building,
        examples: &[Example {
            cmd: "clean audit soundness",
            what: "print the soundness certificate and exit 0 iff SOUND",
        }],
        see_also: &["audit trust-ledger"],
        references: &[DESIGN_REF, CLI_CRATE_REF, MATHVERSE_CRATE_REF],
        domain_root: Some("audit"),
        alternative_forms: &[],
        feature_gate: Some("math-overlays"),
    },
    FeatureDescriptor {
        path: &["audit", "trust-ledger"],
        summary: "Generate a recursive trust ledger for one declaration",
        description: "\
Walks the dependencies of a theorem or constant and reports the trust levels, \
axioms, and trust markers that affect it. This is a focused diagnostic for \
investigating why a declaration is not kernel-clean.",
        category: Category::Verification,
        stability: Stability::Building,
        examples: &[Example {
            cmd: "clean audit trust-ledger Foo.bar --json",
            what: "emit the trust ledger for one declaration",
        }],
        see_also: &["audit cake"],
        references: &[DESIGN_REF, CLI_CRATE_REF, MATHVERSE_CRATE_REF],
        domain_root: Some("audit"),
        alternative_forms: &[],
        feature_gate: None,
    },
];

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct AuthorityCommandEvidence<'a> {
    schema_version: &'static str,
    command: &'static str,
    authority_gate: &'static str,
    authority_schema: &'static str,
    policy: &'static str,
    gate_status: serde_json::Value,
    source_root: String,
    goal_hash: &'a str,
    trust_audit_hash: &'a str,
    report_hash: Option<&'a str>,
    source_digest: Option<&'a str>,
    artifacts: Vec<AuthorityCommandEvidenceArtifact<'a>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct AuthorityCommandEvidenceArtifact<'a> {
    role: &'static str,
    blake3: &'a str,
    byte_len: u64,
    kind: Option<&'a str>,
    logical_name: Option<&'a str>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct TrustLedgerEvidence {
    schema_version: &'static str,
    target: String,
    target_hash: String,
    closure_hash: String,
    status: &'static str,
    failure_mode: Option<&'static str>,
    dependency_hashes: Vec<TrustLedgerDependencyHash>,
    constants: Vec<TrustLedgerConstant>,
    missing_dependencies: Vec<String>,
    opaque_dependencies: Vec<String>,
    hard_failures: Vec<TrustLedgerHardFailure>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct TrustLedgerDependencyHash {
    name: String,
    hash: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct TrustLedgerConstant {
    name: String,
    hash: String,
    declaration_kind: String,
    trust_level: TrustLevel,
    axiom_profile: AxiomProfile,
    source_system: String,
    origin: TrustLedgerOrigin,
    immediate_dependencies: Vec<TrustLedgerDependencyHash>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct TrustLedgerOrigin {
    kind: String,
    module: Option<String>,
    trust: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct TrustLedgerHardFailure {
    name: String,
    failure_mode: &'static str,
    reason: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct TrustLedgerJson<'a> {
    schema_version: &'static str,
    report: serde_json::Value,
    trust_ledger: &'a TrustLedgerEvidence,
    authority_receipt: Option<&'a AuthorityReceipt>,
}

#[derive(Debug, Clone, Subcommand)]
pub(crate) enum AuditCommands {
    /// Audit a Cake/Lake-compatible project trust boundary and emit an AuditReport JSON.
    Cake(AuditLakeArgs),
    /// Generate a recursive trust ledger for a specific theorem or constant.
    TrustLedger(AuditTrustLedgerArgs),
    /// Emit THE soundness certificate (C1-C5) for the kernel + overlay corpus.
    Soundness(AuditSoundnessArgs),
}

#[derive(Debug, Clone, Args)]
pub(crate) struct AuditSoundnessArgs {
    /// Emit the certificate as machine-readable JSON.
    #[arg(long)]
    pub(crate) json: bool,
}

#[derive(Debug, Clone, Args)]
pub(crate) struct AuditLakeArgs {
    /// Lake project root to audit.
    #[arg(value_name = "PROJECT", default_value = ".")]
    pub(crate) project: PathBuf,
    /// Restrict the audit to one module. May be repeated.
    #[arg(long = "module", value_name = "MODULE")]
    pub(crate) modules: Vec<String>,
    /// Load only the selected project .olean files, treating imports as a pinned external baseline.
    #[arg(long)]
    pub(crate) project_oleans_only: bool,
    /// Emit report as JSON.
    #[arg(long)]
    pub(crate) json: bool,
    /// Write report to this path.
    #[arg(long, value_name = "PATH")]
    pub(crate) out: Option<PathBuf>,
    /// Deprecated: audit cake now exits non-zero on rejected gates unless --report-only is set.
    #[arg(long)]
    pub(crate) fail_on_reject: bool,
    /// Emit the rejected gate report without failing the command.
    #[arg(long)]
    pub(crate) report_only: bool,
    /// Append this audit as a trust_audit authority-gate proof attempt.
    #[arg(long)]
    pub(crate) record_attempt: bool,
    /// Repository or project root containing the `.mathverse` attempt log.
    #[arg(long, value_name = "ROOT")]
    pub(crate) root: Option<PathBuf>,
}

#[derive(Debug, Clone, Args)]
pub(crate) struct AuditTrustLedgerArgs {
    /// Theorem or constant name to audit.
    #[arg(value_name = "NAME")]
    pub(crate) name: String,
    /// Emit report as JSON.
    #[arg(long)]
    pub(crate) json: bool,
    /// Write report to this path.
    #[arg(long, value_name = "PATH")]
    pub(crate) out: Option<std::path::PathBuf>,
    /// Append this ledger as a trust_ledger authority-gate proof attempt.
    #[arg(long)]
    pub(crate) record_attempt: bool,
    /// Repository or project root containing the `.mathverse` attempt log.
    #[arg(long, value_name = "ROOT", requires = "record_attempt")]
    pub(crate) root: Option<std::path::PathBuf>,
}

pub(crate) fn handle_audit_command(command: AuditCommands) -> anyhow::Result<()> {
    match command {
        AuditCommands::Cake(args) => run_lake_audit(args),
        AuditCommands::TrustLedger(args) => run_trust_ledger(args),
        AuditCommands::Soundness(args) => run_soundness_certificate(args),
    }
}

/// `clean audit soundness [--json]` — build the canonical kernel + overlay env,
/// emit THE soundness certificate (the five mechanical claims C1-C5), and exit
/// non-zero iff the certificate is NOT sound. Behind the `math-overlays`
/// feature because the certificate runs over the full overlay corpus.
#[cfg(feature = "math-overlays")]
fn run_soundness_certificate(args: AuditSoundnessArgs) -> anyhow::Result<()> {
    let env = Environment::soundness_certificate_env()
        .context("failed to build the soundness-certificate overlay environment")?;
    let cert = env.soundness_certificate();

    if args.json {
        println!(
            "{}",
            cert.to_json()
                .context("failed to serialize the soundness certificate to JSON")?
        );
    } else {
        println!("{cert}");
    }

    if !cert.is_sound() {
        bail!("{SOUNDNESS_NOT_SOUND_MSG}");
    }
    Ok(())
}

/// Failure message for an unsound certificate. The certificate body (claim
/// breakdown) is always printed before this bail, so the message points the
/// caller at it and at the doc that defines each claim.
#[allow(dead_code)] // referenced only under the math-overlays feature
const SOUNDNESS_NOT_SOUND_MSG: &str =
    "soundness certificate is NOT sound — one or more claims (C1-C5, C4') failed; the \
     claim breakdown printed above (or `clean audit soundness --json`) names the failing \
     claim and the offending declarations; see docs/SOUNDNESS_CERTIFICATE.md for what \
     each claim requires";

#[cfg(not(feature = "math-overlays"))]
fn run_soundness_certificate(_args: AuditSoundnessArgs) -> anyhow::Result<()> {
    bail!(
        "clean audit soundness requires the `math-overlays` feature (the certificate \
         runs over the full overlay corpus). Rebuild with \
         `cargo build -p clean-cli --features math-overlays`."
    );
}

fn run_trust_ledger(args: AuditTrustLedgerArgs) -> anyhow::Result<()> {
    let started = Instant::now();
    let attempt_log_root = trust_ledger_attempt_root(&args);
    let source_guard = if args.record_attempt {
        Some(AuthoritySourceGuard::capture_clean(
            attempt_log_root,
            "clean audit trust-ledger --record-attempt",
        )?)
    } else {
        None
    };
    let env = Environment::try_with_prelude().unwrap_or_else(|_| Environment::new());

    let target = clean_kernel::name::Name::from_string(&args.name);
    let (report, ledger) = build_trust_ledger_report(&env, target)?;
    let authority_receipt = if args.record_attempt {
        if let Some(source_guard) = source_guard.as_ref() {
            source_guard.ensure_unchanged("authority evidence write")?;
        }
        let attempt = record_trust_ledger_attempt_at(
            attempt_log_root,
            &ledger,
            &report,
            elapsed_millis_saturating(started),
        )
        .with_context(|| {
            format!(
                "failed to record trust ledger authority-gate attempt under {}",
                attempt_log_root.display()
            )
        })?;
        Some(AuthorityReceipt::from_attempt(&attempt))
    } else {
        None
    };

    if args.json {
        write_trust_ledger_json(
            &report,
            &ledger,
            authority_receipt.as_ref(),
            args.out.as_deref(),
        )
    } else {
        println!("{}", report.summary());
        println!("\nTrust ledger:");
        println!("  target: {}", ledger.target);
        println!("  target_hash: {}", ledger.target_hash);
        println!("  closure_hash: {}", ledger.closure_hash);
        println!("  hard_failures: {}", ledger.hard_failures.len());
        if let Some(receipt) = authority_receipt.as_ref() {
            println!("  attempt_id: {}", receipt.attempt_id);
            if let Some(artifact) = receipt.solver_artifact.as_ref() {
                println!("  solver_artifact: {}", artifact.blake3);
            }
        }
        if !report.is_clean() {
            println!("\nTrust findings:");
            for finding in &report.findings {
                println!("  [{:?}] {}", finding.severity, finding.message);
            }
        }
        Ok(())
    }
}

fn build_trust_ledger_report(
    env: &Environment,
    target: clean_kernel::name::Name,
) -> anyhow::Result<(AuditReport, TrustLedgerEvidence)> {
    let mut builder = AuditReportBuilder::new();
    let mut visited = HashSet::new();
    let mut stack = vec![target.clone()];
    let mut constants = Vec::new();
    let mut missing = BTreeSet::new();
    let mut opaque = BTreeSet::new();
    let mut hard_failures = Vec::new();
    let mut declaration_hashes = HashMap::new();
    let mut immediate_dependency_names = HashMap::<String, Vec<String>>::new();

    while let Some(name) = stack.pop() {
        if !visited.insert(name.clone()) {
            continue;
        }

        let name_text = name.to_string();
        if let Some(ci) = env.get_const(&name) {
            let is_axiom = matches!(ci.kind, ConstantKind::Axiom);
            let is_opaque = matches!(ci.kind, ConstantKind::Opaque);
            let trust = trust_level_for_constant(&name, ci.kind);
            let profile = if is_axiom {
                AxiomProfile::CLASSICAL
            } else {
                AxiomProfile::NONE
            };
            let origin = trust_ledger_origin(env.get_constant_origin(&name));
            let source_system = trust_ledger_source_system(&origin);
            builder.add_constant(trust, &source_system, profile);

            let deps = immediate_const_deps(ci);
            for dep in &deps {
                stack.push(clean_kernel::name::Name::from_string(dep));
            }
            immediate_dependency_names.insert(name_text.clone(), deps.clone());

            let declaration_hash = trust_ledger_declaration_hash(ci, &origin, &deps)?;
            declaration_hashes.insert(name_text.clone(), declaration_hash.clone());

            if is_opaque {
                opaque.insert(name_text.clone());
                let reason = format!(
                    "Constant {name_text} is opaque; recursive trust ledger cannot inspect its proof/value boundary"
                );
                builder.add_finding(AuditFinding {
                    severity: AuditSeverity::Error,
                    category: OPAQUE_CONSTANT_CATEGORY.to_owned(),
                    message: reason.clone(),
                    node_indices: vec![],
                    recommendation: Some("Replace the opaque declaration with inspectable kernel evidence before using this ledger as authority evidence.".to_owned()),
                });
                hard_failures.push(TrustLedgerHardFailure {
                    name: name_text.clone(),
                    failure_mode: "opaque_dependency",
                    reason,
                });
            }
            if trust == TrustLevel::AxiomDependent {
                let reason = format!(
                    "Constant {name_text} is a non-foundational axiom; recursive trust ledger cannot accept axiom-dependent authority evidence"
                );
                builder.add_finding(AuditFinding {
                    severity: AuditSeverity::Error,
                    category: AXIOM_DECLARATION_CATEGORY.to_owned(),
                    message: reason.clone(),
                    node_indices: vec![],
                    recommendation: Some("Replace the non-foundational axiom with reconstructed kernel evidence before using this ledger as authority evidence.".to_owned()),
                });
                hard_failures.push(TrustLedgerHardFailure {
                    name: name_text.clone(),
                    failure_mode: "axiom_dependent",
                    reason,
                });
            } else if trust == TrustLevel::TrustedOracle && !is_opaque {
                let reason = format!(
                    "Constant {name_text} reaches a trusted-oracle marker; recursive trust ledger cannot accept oracle-dependent authority evidence"
                );
                builder.add_finding(AuditFinding {
                    severity: AuditSeverity::Error,
                    category: OPAQUE_CONSTANT_CATEGORY.to_owned(),
                    message: reason.clone(),
                    node_indices: vec![],
                    recommendation: Some("Replace the trusted-oracle marker with inspectable kernel evidence before using this ledger as authority evidence.".to_owned()),
                });
                hard_failures.push(TrustLedgerHardFailure {
                    name: name_text.clone(),
                    failure_mode: "trusted_oracle",
                    reason,
                });
            }

            constants.push(TrustLedgerConstant {
                name: name_text,
                hash: declaration_hash,
                declaration_kind: format!("{:?}", ci.kind),
                trust_level: trust,
                axiom_profile: profile,
                source_system,
                origin,
                immediate_dependencies: Vec::new(),
            });
        } else {
            missing.insert(name_text.clone());
            let reason = format!(
                "Constant {name_text} not found in environment; recursive trust ledger has an unbound dependency"
            );
            builder.add_finding(AuditFinding {
                severity: AuditSeverity::Error,
                category: OPAQUE_CONSTANT_CATEGORY.to_owned(),
                message: reason.clone(),
                node_indices: vec![],
                recommendation: Some("Load or reconstruct the missing dependency before recording authority evidence.".to_owned()),
            });
            hard_failures.push(TrustLedgerHardFailure {
                name: name_text,
                failure_mode: "missing_dependency",
                reason,
            });
        }
    }

    constants.sort_by(|left, right| left.name.cmp(&right.name));
    for constant in &mut constants {
        let deps = immediate_dependency_names
            .get(&constant.name)
            .cloned()
            .unwrap_or_default();
        constant.immediate_dependencies = deps
            .into_iter()
            .map(|name| TrustLedgerDependencyHash {
                hash: declaration_hashes
                    .get(&name)
                    .cloned()
                    .unwrap_or_else(|| missing_dependency_hash(&name)),
                name,
            })
            .collect();
    }

    let target_text = target.to_string();
    let target_dependency_hashes = constants
        .iter()
        .find(|constant| constant.name == target_text)
        .map(|constant| constant.immediate_dependencies.clone())
        .unwrap_or_default();
    let target_hash = if let Some(declaration_hash) = declaration_hashes.get(&target_text) {
        blake3_json(&serde_json::json!({
            "target": target_text,
            "declaration_hash": declaration_hash,
            "dependency_hashes": target_dependency_hashes,
        }))?
    } else {
        missing_dependency_hash(&target_text)
    };

    let missing_dependencies = missing.into_iter().collect::<Vec<_>>();
    let opaque_dependencies = opaque.into_iter().collect::<Vec<_>>();
    hard_failures.sort_by(|left, right| left.name.cmp(&right.name));
    let status = if hard_failures.is_empty() {
        "accepted"
    } else {
        "rejected"
    };
    let failure_mode = trust_ledger_failure_mode(&hard_failures);
    let closure_hash = blake3_json(&serde_json::json!({
        "schema_version": TRUST_LEDGER_SCHEMA,
        "target": target_text,
        "target_hash": target_hash,
        "constants": constants
            .iter()
            .map(|constant| serde_json::json!({
                "name": constant.name,
                "hash": constant.hash,
                "dependency_hashes": constant.immediate_dependencies,
            }))
            .collect::<Vec<_>>(),
        "missing_dependencies": missing_dependencies,
        "opaque_dependencies": opaque_dependencies,
        "hard_failures": hard_failures,
    }))?;

    let ledger = TrustLedgerEvidence {
        schema_version: TRUST_LEDGER_SCHEMA,
        target: target_text,
        target_hash,
        closure_hash,
        status,
        failure_mode,
        dependency_hashes: target_dependency_hashes,
        constants,
        missing_dependencies,
        opaque_dependencies,
        hard_failures,
    };

    Ok((builder.build(), ledger))
}

fn immediate_const_deps(ci: &clean_kernel::env::ConstantInfo) -> Vec<String> {
    let mut deps = Vec::new();
    if let Some(value) = ci.value.as_ref() {
        collect_const_deps(value, &mut deps);
    }
    collect_const_deps(&ci.type_, &mut deps);
    deps.sort();
    deps.dedup();
    deps
}

fn trust_level_for_constant(name: &clean_kernel::name::Name, kind: ConstantKind) -> TrustLevel {
    if matches!(kind, ConstantKind::Axiom) {
        if clean_kernel::is_foundational_axiom(name) {
            TrustLevel::KernelVerified
        } else {
            TrustLevel::AxiomDependent
        }
    } else if matches!(kind, ConstantKind::Opaque) || clean_kernel::is_trust_marker(name) {
        TrustLevel::TrustedOracle
    } else {
        TrustLevel::KernelVerified
    }
}

fn trust_ledger_origin(origin: Option<&clean_kernel::ConstantOrigin>) -> TrustLedgerOrigin {
    match origin {
        Some(clean_kernel::ConstantOrigin::Kernel { trust }) => TrustLedgerOrigin {
            kind: "kernel".to_owned(),
            module: None,
            trust: format!("{trust:?}"),
        },
        Some(clean_kernel::ConstantOrigin::Olean { module, trust }) => TrustLedgerOrigin {
            kind: "olean".to_owned(),
            module: module.clone(),
            trust: format!("{trust:?}"),
        },
        Some(clean_kernel::ConstantOrigin::CleanPayload { module, trust }) => TrustLedgerOrigin {
            kind: "clean_payload".to_owned(),
            module: module.clone(),
            trust: format!("{trust:?}"),
        },
        None => TrustLedgerOrigin {
            kind: "kernel".to_owned(),
            module: None,
            trust: "KernelChecked".to_owned(),
        },
    }
}

fn trust_ledger_source_system(origin: &TrustLedgerOrigin) -> String {
    match origin.kind.as_str() {
        "olean" => "Lean4".to_owned(),
        "clean_payload" => "CleanPayload".to_owned(),
        _ => "Clean".to_owned(),
    }
}

fn trust_ledger_declaration_hash(
    ci: &clean_kernel::env::ConstantInfo,
    origin: &TrustLedgerOrigin,
    immediate_dependencies: &[String],
) -> anyhow::Result<String> {
    blake3_json(&serde_json::json!({
        "name": ci.name.to_string(),
        "level_params": ci.level_params.iter().map(ToString::to_string).collect::<Vec<_>>(),
        "type": ci.type_,
        "value": ci.value,
        "is_reducible": ci.is_reducible,
        "reducibility": ci.reducibility,
        "kind": format!("{:?}", ci.kind),
        "origin": origin,
        "immediate_dependencies": immediate_dependencies,
    }))
}

fn missing_dependency_hash(name: &str) -> String {
    blake3_hex(format!("missing:{name}").as_bytes())
}

fn blake3_json(value: &serde_json::Value) -> anyhow::Result<String> {
    Ok(blake3_hex(&serde_json::to_vec(value)?))
}

fn blake3_hex(bytes: &[u8]) -> String {
    blake3::hash(bytes).to_hex().to_string()
}

fn elapsed_millis_saturating(started: Instant) -> u64 {
    started.elapsed().as_millis().min(u128::from(u64::MAX)) as u64
}

fn trust_ledger_failure_mode(hard_failures: &[TrustLedgerHardFailure]) -> Option<&'static str> {
    if hard_failures
        .iter()
        .any(|failure| failure.failure_mode == "missing_dependency")
    {
        Some("missing_dependency")
    } else if hard_failures
        .iter()
        .any(|failure| failure.failure_mode == "opaque_dependency")
    {
        Some("opaque_dependency")
    } else if hard_failures
        .iter()
        .any(|failure| failure.failure_mode == "axiom_dependent")
    {
        Some("axiom_dependent")
    } else if hard_failures
        .iter()
        .any(|failure| failure.failure_mode == "trusted_oracle")
    {
        Some("trusted_oracle")
    } else {
        None
    }
}

fn trust_ledger_attempt_root(args: &AuditTrustLedgerArgs) -> &Path {
    if let Some(root) = args.root.as_deref() {
        root
    } else {
        Path::new(".")
    }
}

fn record_trust_ledger_attempt_at(
    attempt_log_root: &Path,
    ledger: &TrustLedgerEvidence,
    report: &AuditReport,
    wall_time_ms: u64,
) -> anyhow::Result<ProofAttempt> {
    let artifact_json = trust_ledger_json_value(report, ledger, None)?;
    let artifact_bytes = serde_json::to_vec_pretty(&artifact_json)?;
    let artifact = put_artifact(
        attempt_log_root,
        &artifact_bytes,
        Some(TRUST_LEDGER_ARTIFACT_KIND),
        Some("trust-ledger.json"),
    )?;
    let status = if ledger.hard_failures.is_empty() {
        AttemptStatus::Accepted
    } else {
        AttemptStatus::Rejected {
            reason: format!(
                "trust ledger rejected: failure_mode={}",
                ledger.failure_mode.unwrap_or("unknown_failure")
            ),
        }
    };
    let mut attempt = AuthorityGateAttempt::new(
        TRUST_LEDGER_AUTHORITY_GATE,
        ledger.target_hash.clone(),
        status,
        blake3_hex(&artifact_bytes),
        EnvFingerprint::capture(attempt_log_root)?,
    );
    attempt.wall_time_ms = wall_time_ms;
    attempt.solver_artifact = Some(artifact);
    attempt.failure_mode = ledger.failure_mode.map(str::to_owned);
    attempt.trust_level = if ledger.hard_failures.is_empty() {
        Some(TrustLevel::KernelVerified)
    } else {
        Some(TrustLevel::TrustedOracle)
    };
    attempt.command_evidence = Some(put_authority_command_evidence(
        attempt_log_root,
        AuthorityCommandEvidence {
            schema_version: AUTHORITY_COMMAND_EVIDENCE_SCHEMA,
            command: "clean audit trust-ledger --record-attempt",
            authority_gate: TRUST_LEDGER_AUTHORITY_GATE,
            authority_schema: TRUST_LEDGER_SCHEMA,
            policy: "recursive trust ledger has no hard failures",
            gate_status: attempt_status_evidence(&attempt.status),
            source_root: attempt_log_root.display().to_string(),
            goal_hash: &attempt.goal_hash,
            trust_audit_hash: &attempt.trust_audit_hash,
            report_hash: Some(&attempt.trust_audit_hash),
            source_digest: Some(&ledger.closure_hash),
            artifacts: vec![authority_command_evidence_artifact(
                "trust_ledger_report",
                attempt
                    .solver_artifact
                    .as_ref()
                    .expect("trust ledger artifact is assigned before command evidence"),
            )],
        },
        "trust-ledger-command-evidence.json",
    )?);
    Ok(record_authority_gate_attempt(attempt_log_root, attempt)?)
}

fn put_authority_command_evidence(
    attempt_log_root: &Path,
    evidence: AuthorityCommandEvidence<'_>,
    logical_name: &str,
) -> anyhow::Result<clean_mathverse::attempt_log::ArtifactRef> {
    let bytes = serde_json::to_vec_pretty(&evidence)?;
    Ok(put_artifact(
        attempt_log_root,
        &bytes,
        Some(AUTHORITY_COMMAND_EVIDENCE_ARTIFACT_KIND),
        Some(logical_name),
    )?)
}

fn authority_command_evidence_artifact<'a>(
    role: &'static str,
    artifact: &'a clean_mathverse::attempt_log::ArtifactRef,
) -> AuthorityCommandEvidenceArtifact<'a> {
    AuthorityCommandEvidenceArtifact {
        role,
        blake3: &artifact.blake3,
        byte_len: artifact.byte_len,
        kind: artifact.kind.as_deref(),
        logical_name: artifact.logical_name.as_deref(),
    }
}

fn attempt_status_evidence(status: &AttemptStatus) -> serde_json::Value {
    match status {
        AttemptStatus::Accepted => serde_json::json!({ "kind": "accepted" }),
        AttemptStatus::Rejected { reason } => {
            serde_json::json!({ "kind": "rejected", "reason": reason })
        }
        AttemptStatus::Timeout { after_ms } => {
            serde_json::json!({ "kind": "timeout", "after_ms": after_ms })
        }
    }
}

fn write_trust_ledger_json(
    report: &AuditReport,
    ledger: &TrustLedgerEvidence,
    authority_receipt: Option<&AuthorityReceipt>,
    out: Option<&Path>,
) -> anyhow::Result<()> {
    let value = trust_ledger_json_value(report, ledger, authority_receipt)?;
    write_output(&serde_json::to_string_pretty(&value)?, out)
}

fn trust_ledger_json_value(
    report: &AuditReport,
    ledger: &TrustLedgerEvidence,
    authority_receipt: Option<&AuthorityReceipt>,
) -> anyhow::Result<serde_json::Value> {
    let report = serde_json::from_str(&report.to_json())
        .context("failed to serialize trust ledger audit report JSON")?;
    Ok(serde_json::to_value(TrustLedgerJson {
        schema_version: TRUST_LEDGER_SCHEMA,
        report,
        trust_ledger: ledger,
        authority_receipt,
    })?)
}

// ---------------------------------------------------------------------------
// `clean audit cake` — full Lake-project trust audit
// ---------------------------------------------------------------------------

const PROJECT_AUDIT_COMMAND: &str = "clean audit cake --record-attempt";
const PROJECT_AUDIT_POLICY: &str = "project audit has no warning-or-higher trust findings";

fn run_lake_audit(args: AuditLakeArgs) -> anyhow::Result<()> {
    let started = Instant::now();
    let source_guard = if args.record_attempt {
        Some(AuthoritySourceGuard::capture_clean(
            &args.project,
            PROJECT_AUDIT_COMMAND,
        )?)
    } else {
        None
    };
    let workspace = clean_lake::Workspace::load(&args.project).with_context(|| {
        format!(
            "failed to load Lake workspace from {}",
            args.project.display()
        )
    })?;
    let adapter = LakeAuditWorkspace {
        workspace: &workspace,
        modules: args.modules.clone(),
    };
    let modules = adapter.all_modules();
    let env_load = load_project_environment(&workspace, &modules, args.project_oleans_only);

    let mut report = audit_lake_project(&adapter, &env_load.env);
    if args.project_oleans_only {
        mark_project_olean_external_baseline(&mut report);
    }
    add_environment_reconstruction_finding(&mut report, &env_load);
    let gate_status = lake_audit_gate_status(&report, &env_load, &args);
    let wall_time_ms = elapsed_millis_saturating(started);

    let authority_receipt = if args.record_attempt {
        if let Some(source_guard) = source_guard.as_ref() {
            source_guard.ensure_unchanged("authority evidence write")?;
        }
        let attempt_log_root = args.root.as_deref().unwrap_or(args.project.as_path());
        let attempt = record_project_audit_authority_gate_attempt_at(
            attempt_log_root,
            args.project.as_path(),
            &report,
            &gate_status,
            wall_time_ms,
        )
        .with_context(|| {
            format!(
                "failed to record project audit authority-gate attempt under {}",
                attempt_log_root.display()
            )
        })?;
        Some(AuthorityReceipt::from_attempt(&attempt))
    } else {
        None
    };

    if args.json {
        write_lake_audit_json(
            &report,
            &gate_status,
            authority_receipt.as_ref(),
            args.out.as_deref(),
        )?;
    } else {
        write_lake_audit_text(
            &report,
            &gate_status,
            authority_receipt.as_ref(),
            args.out.as_deref(),
        )?;
    }

    if !args.report_only && !gate_status.is_accepted() {
        bail!(
            "{}",
            authority_gate_rejected_msg(
                gate_status
                    .failure_mode
                    .as_deref()
                    .unwrap_or("unknown_failure")
            )
        );
    }

    Ok(())
}

/// Render the fail-closed authority-gate rejection: names the violated
/// requirement (failure_mode) and how to get the full report without gating.
fn authority_gate_rejected_msg(failure_mode: &str) -> String {
    format!(
        "project audit authority gate rejected: failure_mode={failure_mode} — the gate \
         is fail-closed; the report above details the violated requirement, and \
         re-running with --report-only emits the full report without gating"
    )
}

fn record_project_audit_authority_gate_attempt_at(
    attempt_log_root: &Path,
    source_root: &Path,
    report: &AuditReport,
    gate_status: &ProjectAuditAuthorityGateStatus,
    wall_time_ms: u64,
) -> anyhow::Result<ProofAttempt> {
    let report_json = report.to_json();
    let report_bytes = report_json.as_bytes();
    let report_artifact = put_artifact(
        attempt_log_root,
        report_bytes,
        Some(PROJECT_AUDIT_ARTIFACT_KIND),
        Some("project-audit-report.json"),
    )?;
    let mut attempt = AuthorityGateAttempt::new(
        PROJECT_AUDIT_AUTHORITY_GATE,
        authority_gate_goal_hash(
            source_root,
            PROJECT_AUDIT_AUTHORITY_GATE,
            PROJECT_AUDIT_GOAL_SHAPE,
        )?,
        gate_status.status.clone(),
        blake3_hex(report_bytes),
        EnvFingerprint::capture(source_root)?,
    );
    attempt.wall_time_ms = wall_time_ms;
    attempt.solver_artifact = Some(report_artifact);
    attempt.failure_mode = gate_status.failure_mode.clone();
    attempt.trust_level = gate_status.trust_level;
    attempt.command_evidence = Some(put_authority_command_evidence(
        attempt_log_root,
        AuthorityCommandEvidence {
            schema_version: AUTHORITY_COMMAND_EVIDENCE_SCHEMA,
            command: PROJECT_AUDIT_COMMAND,
            authority_gate: PROJECT_AUDIT_AUTHORITY_GATE,
            authority_schema: PROJECT_AUDIT_GOAL_SHAPE,
            policy: PROJECT_AUDIT_POLICY,
            gate_status: attempt_status_evidence(&attempt.status),
            source_root: source_root.display().to_string(),
            goal_hash: &attempt.goal_hash,
            trust_audit_hash: &attempt.trust_audit_hash,
            report_hash: Some(&attempt.trust_audit_hash),
            source_digest: None,
            artifacts: vec![authority_command_evidence_artifact(
                "project_audit_report",
                attempt
                    .solver_artifact
                    .as_ref()
                    .expect("project audit artifact is assigned before command evidence"),
            )],
        },
        "project-audit-command-evidence.json",
    )?);
    Ok(record_authority_gate_attempt(attempt_log_root, attempt)?)
}

struct LakeAuditWorkspace<'a> {
    workspace: &'a clean_lake::Workspace,
    modules: Vec<String>,
}

impl ProjectAuditWorkspace for LakeAuditWorkspace<'_> {
    fn all_modules(&self) -> Vec<String> {
        if self.modules.is_empty() {
            self.workspace.all_modules()
        } else {
            self.modules.clone()
        }
    }

    fn find_module(&self, module_name: &str) -> Option<PathBuf> {
        self.workspace.find_module(module_name)
    }
}

#[derive(Debug)]
struct EnvironmentLoad {
    env: Environment,
    modules_discovered: usize,
    modules_loaded: usize,
    load_summaries: usize,
    added_constants: usize,
    duplicate_constants: usize,
    skipped_constants: usize,
    search_paths: Vec<PathBuf>,
    project_oleans_only: bool,
    prelude_error: Option<String>,
    module_errors: Vec<ModuleLoadError>,
}

#[derive(Debug)]
struct ModuleLoadError {
    module: String,
    error: String,
}

fn load_project_environment(
    workspace: &clean_lake::Workspace,
    modules: &[String],
    project_oleans_only: bool,
) -> EnvironmentLoad {
    if !project_oleans_only {
        return load_project_source_environment(workspace, modules);
    }

    let (env, prelude_error) = match Environment::try_with_prelude() {
        Ok(env) => (env, None),
        Err(err) => (Environment::new(), Some(err.to_string())),
    };

    let mut modules = modules.to_vec();
    modules.sort();
    modules.dedup();

    let search_paths = project_search_paths(workspace);
    let mut load = EnvironmentLoad {
        env,
        modules_discovered: modules.len(),
        modules_loaded: 0,
        load_summaries: 0,
        added_constants: 0,
        duplicate_constants: 0,
        skipped_constants: 0,
        search_paths,
        project_oleans_only,
        prelude_error,
        module_errors: Vec::new(),
    };

    for module in modules {
        let olean_path = project_olean_path(workspace, &module, &load.search_paths);
        match clean_olean::load_olean_file(&mut load.env, &olean_path) {
            Ok(summary) => {
                load.modules_loaded += 1;
                record_load_summary(&mut load, summary);
            }
            Err(err) => load.module_errors.push(ModuleLoadError {
                module,
                error: format!("{} ({err})", olean_path.display()),
            }),
        }
    }

    load.module_errors
        .sort_by(|left, right| left.module.cmp(&right.module));
    load
}

fn load_project_source_environment(
    workspace: &clean_lake::Workspace,
    requested_modules: &[String],
) -> EnvironmentLoad {
    let (env, prelude_error) = match Environment::try_with_prelude() {
        Ok(env) => (env, None),
        Err(err) => (Environment::new(), Some(err.to_string())),
    };

    let search_paths = project_search_paths(workspace);
    let modules = match source_load_order_for_modules(workspace, requested_modules) {
        Ok(modules) => modules,
        Err(err) => {
            let mut load = EnvironmentLoad {
                env,
                modules_discovered: 0,
                modules_loaded: 0,
                load_summaries: 0,
                added_constants: 0,
                duplicate_constants: 0,
                skipped_constants: 0,
                search_paths,
                project_oleans_only: false,
                prelude_error,
                module_errors: vec![ModuleLoadError {
                    module: "<workspace>".to_owned(),
                    error: err,
                }],
            };
            load.module_errors
                .sort_by(|left, right| left.module.cmp(&right.module));
            return load;
        }
    };

    let mut load = EnvironmentLoad {
        env,
        modules_discovered: modules.len(),
        modules_loaded: 0,
        load_summaries: 0,
        added_constants: 0,
        duplicate_constants: 0,
        skipped_constants: 0,
        search_paths,
        project_oleans_only: false,
        prelude_error,
        module_errors: Vec::new(),
    };

    let patterns = clean_elab::tactic::builtins::builtin_tactic_patterns();
    for module in modules {
        let Some(path) = workspace.find_module(&module) else {
            load.module_errors.push(ModuleLoadError {
                module,
                error: "workspace index did not resolve module source".to_owned(),
            });
            continue;
        };

        let before_constants = load.env.constants().count();
        let source = match fs::read_to_string(&path) {
            Ok(source) => source,
            Err(err) => {
                load.module_errors.push(ModuleLoadError {
                    module,
                    error: format!("{} ({err})", path.display()),
                });
                continue;
            }
        };

        let decls = match parse_file_with_tactics(&source, &patterns) {
            Ok(decls) => decls,
            Err(err) => {
                load.module_errors.push(ModuleLoadError {
                    module,
                    error: format!("{} (parse error: {err})", path.display()),
                });
                continue;
            }
        };

        let mut file_ctx = FileContext::new();
        let mut failed = false;
        for (idx, decl) in decls.iter().enumerate() {
            let processed = preprocess_decl_with_context(decl, &mut file_ctx);
            if let Err(err) = elaborate_decl_and_register_with_context_and_warning(
                &mut load.env,
                &processed,
                &mut file_ctx,
            ) {
                load.module_errors.push(ModuleLoadError {
                    module: module.clone(),
                    error: format!("{} declaration {} failed: {err:?}", path.display(), idx + 1),
                });
                failed = true;
                break;
            }
        }

        if failed {
            continue;
        }

        let after_constants = load.env.constants().count();
        load.modules_loaded += 1;
        load.load_summaries += 1;
        load.added_constants += after_constants.saturating_sub(before_constants);
    }

    load.module_errors
        .sort_by(|left, right| left.module.cmp(&right.module));
    load
}

fn source_load_order_for_modules(
    workspace: &clean_lake::Workspace,
    requested_modules: &[String],
) -> Result<Vec<String>, String> {
    let workspace_modules = workspace_source_module_set(workspace)?;
    let graph = workspace.import_graph().map_err(|err| err.to_string())?;
    let mut roots = if requested_modules.is_empty() {
        workspace_modules.iter().cloned().collect::<Vec<_>>()
    } else {
        requested_modules.to_vec()
    };
    roots.sort();
    roots.dedup();

    for module in &roots {
        if !workspace_modules.contains(module) {
            return Err(format!(
                "requested module `{module}` is not a workspace source module"
            ));
        }
    }

    let mut result = Vec::new();
    let mut visited = HashSet::new();
    let mut visiting = HashSet::new();
    let mut stack = Vec::new();

    for module in roots {
        visit_source_module(
            &module,
            &graph,
            &workspace_modules,
            &mut visited,
            &mut visiting,
            &mut stack,
            &mut result,
        )?;
    }

    Ok(result)
}

fn workspace_source_module_set(
    workspace: &clean_lake::Workspace,
) -> Result<HashSet<String>, String> {
    let package_roots = workspace.package_dirs();
    let mut modules = HashSet::new();

    for module in workspace.all_modules() {
        let path = workspace
            .find_module(&module)
            .ok_or_else(|| format!("workspace index did not resolve `{module}`"))?;
        if !package_roots.iter().any(|root| path.starts_with(root)) {
            modules.insert(module);
        }
    }

    Ok(modules)
}

#[allow(clippy::too_many_arguments)]
fn visit_source_module(
    module: &str,
    graph: &HashMap<String, Vec<String>>,
    workspace_modules: &HashSet<String>,
    visited: &mut HashSet<String>,
    visiting: &mut HashSet<String>,
    stack: &mut Vec<String>,
    result: &mut Vec<String>,
) -> Result<(), String> {
    if visited.contains(module) {
        return Ok(());
    }
    if visiting.contains(module) {
        stack.push(module.to_owned());
        return Err(format!("circular dependency: {}", stack.join(" -> ")));
    }

    visiting.insert(module.to_owned());
    stack.push(module.to_owned());

    let mut deps = graph
        .get(module)
        .into_iter()
        .flatten()
        .filter(|dep| workspace_modules.contains(*dep))
        .cloned()
        .collect::<Vec<_>>();
    deps.sort();
    deps.dedup();

    for dep in deps {
        visit_source_module(
            &dep,
            graph,
            workspace_modules,
            visited,
            visiting,
            stack,
            result,
        )?;
    }

    stack.pop();
    visiting.remove(module);
    visited.insert(module.to_owned());
    result.push(module.to_owned());
    Ok(())
}

fn project_olean_path(
    workspace: &clean_lake::Workspace,
    module: &str,
    search_paths: &[PathBuf],
) -> PathBuf {
    let mut rel_path = PathBuf::new();
    for part in module.split('.') {
        rel_path.push(part);
    }
    rel_path.set_extension("olean");
    search_paths
        .iter()
        .map(|dir| dir.join(&rel_path))
        .find(|path| path.is_file())
        .unwrap_or_else(|| workspace.olean_path(module))
}

fn record_load_summary(load: &mut EnvironmentLoad, summary: clean_olean::LoadSummary) {
    load.load_summaries += 1;
    load.added_constants += summary.added_constants;
    load.duplicate_constants += summary.duplicate_constants;
    load.skipped_constants += summary.skipped_constants.len();
}

fn project_search_paths(workspace: &clean_lake::Workspace) -> Vec<PathBuf> {
    let mut builder = clean_olean::SearchPathBuilder::new()
        .add_lib_path(workspace.lib_dir().join("lean"))
        .add_lib_path(workspace.lib_dir())
        .add_package_root(workspace.root());

    for package_dir in workspace.package_dirs() {
        builder = builder
            .add_lib_path(package_dir.join(".lake/build/lib/lean"))
            .add_lib_path(package_dir.join(".lake/build/lib"))
            .add_lib_path(package_dir.join("build/lib/lean"))
            .add_lib_path(package_dir.join("build/lib"))
            .add_package_root(package_dir);
    }

    builder.with_defaults().build()
}

fn add_environment_reconstruction_finding(report: &mut AuditReport, load: &EnvironmentLoad) {
    let failed_modules = load.module_errors.len();
    let status = if load.prelude_error.is_none()
        && failed_modules == 0
        && load.modules_loaded == load.modules_discovered
    {
        "complete"
    } else {
        "best-effort"
    };

    let mut message = format!(
        "clean project environment reconstruction: status={status}, \
         modules_discovered={}, modules_loaded={}, modules_failed={}, \
         load_summaries={}, added_constants={}, duplicate_constants={}, \
         skipped_constants={}, search_paths={}, project_oleans_only={}",
        load.modules_discovered,
        load.modules_loaded,
        failed_modules,
        load.load_summaries,
        load.added_constants,
        load.duplicate_constants,
        load.skipped_constants,
        load.search_paths.len(),
        load.project_oleans_only
    );

    if let Some(error) = &load.prelude_error {
        message.push_str(&format!(", prelude_error={error}"));
    }

    if let Some(first_error) = load.module_errors.first() {
        message.push_str(&format!(
            ", first_module_error={} ({})",
            first_error.module, first_error.error
        ));
    }

    let recommendation = if status == "best-effort" {
        Some(
            "Build the Lake project first so project .olean files are available; \
             until then audited project constants may be incomplete."
                .to_owned(),
        )
    } else {
        None
    };

    report.findings.push(AuditFinding::structured(
        AuditSeverity::Info,
        AuditFindingCategory::KernelTrust {
            kernel: KernelAuditKernel::Clean,
        },
        message,
        vec![],
        recommendation,
    ));
}

fn mark_project_olean_external_baseline(report: &mut AuditReport) {
    for finding in &mut report.findings {
        if finding.severity != AuditSeverity::Warning {
            continue;
        }
        if finding.category != "kernel-trust:clean" {
            continue;
        }
        let external_dependency_warning = finding.message.contains("Axiom-dependent theorem:")
            || finding.message.contains("Transitive trust dependencies:");
        if !external_dependency_warning || contains_forbidden_project_trust_marker(&finding.message)
        {
            continue;
        }
        finding.severity = AuditSeverity::Info;
        finding.recommendation = Some(
            "Project .olean-only audit: dependency is treated as part of the pinned external Lean baseline; run without --project-oleans-only for full recursive reconstruction."
                .to_owned(),
        );
    }
    report.findings.push(AuditFinding::structured(
        AuditSeverity::Info,
        AuditFindingCategory::KernelTrust {
            kernel: KernelAuditKernel::Clean,
        },
        "project .olean-only audit mode: imported libraries are a pinned external baseline, not recursively reconstructed",
        vec![],
        Some(
            "Use full audit mode before claiming Clean has independent Init/Std/Mathlib parity."
                .to_owned(),
        ),
    ));
}

fn contains_forbidden_project_trust_marker(message: &str) -> bool {
    ["sorry", "sorryAx", "trustedArith", "trustedAy", "unsafe"]
        .iter()
        .any(|marker| message.contains(marker))
}

fn lake_audit_gate_status(
    report: &AuditReport,
    load: &EnvironmentLoad,
    args: &AuditLakeArgs,
) -> ProjectAuditAuthorityGateStatus {
    if !environment_reconstruction_complete(load) {
        return project_audit_environment_reconstruction_rejected_status(
            environment_reconstruction_rejection_reason(load),
        );
    }
    if args.project_oleans_only {
        return project_audit_project_oleans_only_rejected_status();
    }
    project_audit_authority_gate_status(report)
}

fn project_audit_project_oleans_only_rejected_status() -> ProjectAuditAuthorityGateStatus {
    ProjectAuditAuthorityGateStatus {
        status: AttemptStatus::Rejected {
            reason: "project trust audit rejected: --project-oleans-only treats imports as a pinned external baseline and does not recursively reconstruct dependencies"
                .to_string(),
        },
        failure_mode: Some("project_oleans_only_external_baseline".to_string()),
        trust_level: Some(TrustLevel::TrustedOracle),
    }
}

fn environment_reconstruction_complete(load: &EnvironmentLoad) -> bool {
    load.prelude_error.is_none()
        && load.module_errors.is_empty()
        && load.modules_loaded == load.modules_discovered
}

fn environment_reconstruction_rejection_reason(load: &EnvironmentLoad) -> String {
    let mut reason = format!(
        "project trust audit rejected: incomplete environment reconstruction; \
         modules_discovered={}, modules_loaded={}, modules_failed={}",
        load.modules_discovered,
        load.modules_loaded,
        load.module_errors.len()
    );
    if let Some(error) = &load.prelude_error {
        reason.push_str(&format!(", prelude_error={error}"));
    }
    if let Some(first_error) = load.module_errors.first() {
        reason.push_str(&format!(
            ", first_module_error={} ({})",
            first_error.module, first_error.error
        ));
    }
    reason
}

fn write_lake_audit_json(
    report: &AuditReport,
    gate_status: &ProjectAuditAuthorityGateStatus,
    authority_receipt: Option<&AuthorityReceipt>,
    out: Option<&Path>,
) -> anyhow::Result<()> {
    let mut value: serde_json::Value =
        serde_json::from_str(&report.to_json()).context("failed to serialize audit report JSON")?;
    let audit_status = value
        .get("status")
        .cloned()
        .unwrap_or(serde_json::Value::Null);
    value["audit_status"] = audit_status;
    value["authority_gate"] = authority_gate_json(gate_status);
    value["authority_receipt"] = match authority_receipt {
        Some(receipt) => serde_json::to_value(receipt)?,
        None => serde_json::Value::Null,
    };
    value["authority_gate_effective_status"] =
        serde_json::Value::String(authority_gate_status_name(&gate_status.status).to_owned());
    if !gate_status.is_accepted() {
        value["status"] = serde_json::Value::String("AUTHORITY_REJECTED".to_owned());
    }
    write_output(&serde_json::to_string_pretty(&value)?, out)
}

fn write_lake_audit_text(
    report: &AuditReport,
    gate_status: &ProjectAuditAuthorityGateStatus,
    authority_receipt: Option<&AuthorityReceipt>,
    out: Option<&Path>,
) -> anyhow::Result<()> {
    let mut text = report.summary();
    text.push_str("\n\nAuthority gate:\n");
    text.push_str(&format!(
        "  status: {}\n",
        authority_gate_status_name(&gate_status.status)
    ));
    text.push_str(&format!(
        "  failure_mode: {}\n",
        gate_status.failure_mode.as_deref().unwrap_or("none")
    ));
    text.push_str(&format!(
        "  trust_level: {}\n",
        gate_status
            .trust_level
            .map(|level| format!("{level:?}"))
            .unwrap_or_else(|| "unknown".to_owned())
    ));
    if let AttemptStatus::Rejected { reason } = &gate_status.status {
        text.push_str(&format!("  reason: {reason}\n"));
    }
    if let Some(receipt) = authority_receipt {
        text.push_str(&format!("  attempt_id: {}\n", receipt.attempt_id));
        if let Some(artifact) = &receipt.solver_artifact {
            text.push_str(&format!("  solver_artifact: {}\n", artifact.blake3));
        }
    }

    if !report.is_clean() {
        text.push_str("\nTrust findings:\n");
        for finding in &report.findings {
            text.push_str(&format!("  [{:?}] {}\n", finding.severity, finding.message));
        }
    }

    write_output(text.trim_end(), out)
}

fn authority_gate_json(gate_status: &ProjectAuditAuthorityGateStatus) -> serde_json::Value {
    serde_json::json!({
        "status": authority_gate_status_name(&gate_status.status),
        "failure_mode": gate_status.failure_mode,
        "trust_level": gate_status.trust_level.map(|level| format!("{level:?}")),
        "reason": authority_gate_rejection_reason(&gate_status.status),
    })
}

fn authority_gate_status_name(status: &AttemptStatus) -> &'static str {
    match status {
        AttemptStatus::Accepted => "accepted",
        AttemptStatus::Rejected { .. } => "rejected",
        AttemptStatus::Timeout { .. } => "timeout",
    }
}

fn authority_gate_rejection_reason(status: &AttemptStatus) -> Option<&str> {
    match status {
        AttemptStatus::Rejected { reason } => Some(reason.as_str()),
        _ => None,
    }
}

fn collect_const_deps(expr: &clean_kernel::Expr, deps: &mut Vec<String>) {
    use clean_kernel::expr::ExprVisitor;
    struct DepCollector<'a>(&'a mut Vec<String>);
    impl ExprVisitor for DepCollector<'_> {
        type Result = ();

        fn combine(&self, _a: Self::Result, _b: Self::Result) -> Self::Result {}

        fn visit_const(
            &mut self,
            name: &clean_kernel::name::Name,
            _levels: &clean_kernel::LevelVec,
        ) {
            self.0.push(name.to_string());
        }
    }
    DepCollector(deps).visit_expr(expr);
}

fn write_output(contents: &str, out: Option<&Path>) -> anyhow::Result<()> {
    match out {
        Some(path) => {
            if let Some(parent) = path
                .parent()
                .filter(|parent| !parent.as_os_str().is_empty())
            {
                fs::create_dir_all(parent).with_context(|| {
                    format!("failed to create output directory {}", parent.display())
                })?;
            }
            fs::write(path, format!("{contents}\n"))
                .with_context(|| format!("failed to write audit report to {}", path.display()))?;
        }
        None => {
            let mut stdout = io::stdout().lock();
            writeln!(stdout, "{contents}").context("failed to write audit report to stdout")?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::env::{ConstantInfo, Reducibility, TrustedEnvExt};

    #[test]
    fn test_soundness_failure_msg_names_claims_and_doc() {
        // Four-question standard: WHAT (claims C1-C5/C4'), WHERE to find the
        // failing claim (breakdown / --json), WHAT NOW (the defining doc).
        assert!(SOUNDNESS_NOT_SOUND_MSG.contains("C1-C5"));
        assert!(SOUNDNESS_NOT_SOUND_MSG.contains("--json"));
        assert!(SOUNDNESS_NOT_SOUND_MSG.contains("docs/SOUNDNESS_CERTIFICATE.md"));
    }

    #[test]
    fn test_authority_gate_rejected_msg_names_mode_and_remediation() {
        let msg = authority_gate_rejected_msg("missing_receipt");
        assert!(msg.contains("failure_mode=missing_receipt"));
        assert!(
            msg.contains("--report-only"),
            "rejection must name the ungated-report remediation, got: {msg}"
        );
    }

    fn command_evidence_json(root: &Path, attempt: &ProofAttempt) -> serde_json::Value {
        let artifact = attempt
            .command_evidence
            .as_ref()
            .expect("attempt should include command evidence");
        assert_eq!(
            artifact.kind.as_deref(),
            Some(AUTHORITY_COMMAND_EVIDENCE_ARTIFACT_KIND)
        );
        let bytes = fs::read(root.join(".cake/artifacts").join(&artifact.blake3))
            .expect("command evidence artifact should be readable");
        assert_eq!(blake3_hex(&bytes), artifact.blake3);
        serde_json::from_slice(&bytes).expect("command evidence should be JSON")
    }

    fn rejected_report() -> AuditReport {
        let mut builder = AuditReportBuilder::new();
        builder.add_constant(TrustLevel::AxiomDependent, "Lean4", AxiomProfile::CLASSICAL);
        builder.add_finding(AuditFinding::structured(
            AuditSeverity::Warning,
            AuditFindingCategory::AxiomDeclaration,
            "axiom declaration found",
            vec![],
            None,
        ));
        builder.build()
    }

    fn incomplete_env_load() -> EnvironmentLoad {
        EnvironmentLoad {
            env: Environment::new(),
            modules_discovered: 1,
            modules_loaded: 0,
            load_summaries: 0,
            added_constants: 0,
            duplicate_constants: 0,
            skipped_constants: 0,
            search_paths: Vec::new(),
            project_oleans_only: false,
            prelude_error: None,
            module_errors: vec![ModuleLoadError {
                module: "Project".to_owned(),
                error: "missing .olean".to_owned(),
            }],
        }
    }

    fn lake_args(project: &Path, project_oleans_only: bool) -> AuditLakeArgs {
        AuditLakeArgs {
            project: project.to_path_buf(),
            modules: Vec::new(),
            project_oleans_only,
            json: true,
            out: None,
            fail_on_reject: false,
            report_only: false,
            record_attempt: false,
            root: None,
        }
    }

    #[test]
    fn lake_audit_json_includes_authority_gate_status() {
        let dir = tempfile::tempdir().expect("tempdir should be created");
        let out = dir.path().join("audit.json");
        let report = rejected_report();
        let gate_status = project_audit_authority_gate_status(&report);

        write_lake_audit_json(&report, &gate_status, None, Some(&out))
            .expect("json should be written");

        let text = fs::read_to_string(out).expect("json should be readable");
        let json: serde_json::Value = serde_json::from_str(&text).expect("json should parse");
        assert_eq!(json["audit_status"], "CLEAN");
        assert_eq!(json["status"], "AUTHORITY_REJECTED");
        assert_eq!(json["authority_gate_effective_status"], "rejected");
        let authority_gate = &json["authority_gate"];
        assert_eq!(authority_gate["status"], "rejected");
        assert_eq!(authority_gate["failure_mode"], "axiom_declaration");
        assert_eq!(authority_gate["trust_level"], "AxiomDependent");
        assert!(authority_gate["reason"]
            .as_str()
            .expect("reason should be present")
            .contains("project trust audit rejected"));
    }

    #[test]
    fn recorded_project_audit_attempt_serializes_authority_receipt_shape() {
        let dir = tempfile::tempdir().expect("tempdir should be created");
        let report = rejected_report();
        let gate_status = project_audit_authority_gate_status(&report);

        let attempt = record_project_audit_authority_gate_attempt_at(
            dir.path(),
            dir.path(),
            &report,
            &gate_status,
            23,
        )
        .expect("record project audit authority gate");
        let receipt = AuthorityReceipt::from_attempt(&attempt);
        let json = serde_json::to_value(&receipt).expect("receipt serializes");

        assert!(json["attempt_id"].as_str().is_some());
        assert_eq!(json["authority_gate"], "trust_audit");
        assert_eq!(json["status"], "rejected");
        assert!(json["goal_hash"].as_str().is_some());
        assert!(json["trust_audit_hash"].as_str().is_some());
        assert_eq!(json["solver_artifact"]["blake3"], json["trust_audit_hash"]);
        assert_eq!(
            json["command_evidence"]["kind"],
            AUTHORITY_COMMAND_EVIDENCE_ARTIFACT_KIND
        );
        let evidence = command_evidence_json(dir.path(), &attempt);
        assert_eq!(
            evidence["schema_version"],
            AUTHORITY_COMMAND_EVIDENCE_SCHEMA
        );
        assert_eq!(evidence["command"], "clean audit cake --record-attempt");
        assert_eq!(evidence["authority_gate"], PROJECT_AUDIT_AUTHORITY_GATE);
        assert_eq!(evidence["authority_schema"], PROJECT_AUDIT_GOAL_SHAPE);
        assert_eq!(
            evidence["policy"],
            "project audit has no warning-or-higher trust findings"
        );
        assert_eq!(evidence["gate_status"]["kind"], "rejected");
        assert_eq!(evidence["source_root"], dir.path().display().to_string());
        assert_eq!(evidence["goal_hash"], attempt.goal_hash);
        assert_eq!(evidence["trust_audit_hash"], attempt.trust_audit_hash);
        assert_eq!(evidence["report_hash"], attempt.trust_audit_hash);
        assert!(evidence["source_digest"].is_null());
        assert_eq!(evidence["artifacts"][0]["role"], "project_audit_report");
        assert_eq!(
            evidence["artifacts"][0]["kind"],
            PROJECT_AUDIT_ARTIFACT_KIND
        );
    }

    #[test]
    fn lake_audit_json_rejects_incomplete_reconstruction_in_gate_mode() {
        let dir = tempfile::tempdir().expect("tempdir should be created");
        let out = dir.path().join("audit.json");
        let report = AuditReportBuilder::new().build();
        let load = incomplete_env_load();
        let args = lake_args(dir.path(), false);
        let gate_status = lake_audit_gate_status(&report, &load, &args);

        write_lake_audit_json(&report, &gate_status, None, Some(&out))
            .expect("json should be written");

        let text = fs::read_to_string(out).expect("json should be readable");
        let json: serde_json::Value = serde_json::from_str(&text).expect("json should parse");
        let json = &json["authority_gate"];
        assert_eq!(json["status"], "rejected");
        assert_eq!(
            json["failure_mode"],
            "environment_reconstruction_incomplete"
        );
        assert_eq!(json["trust_level"], "TrustedOracle");
        assert!(json["reason"]
            .as_str()
            .expect("reason should be present")
            .contains("incomplete environment reconstruction"));
    }

    #[test]
    fn lake_audit_gate_rejects_project_oleans_only_mode() {
        let dir = tempfile::tempdir().expect("tempdir should be created");
        let mut builder = AuditReportBuilder::new();
        builder.add_constant(TrustLevel::KernelVerified, "Clean", AxiomProfile::NONE);
        let report = builder.build();
        let load = EnvironmentLoad {
            env: Environment::new(),
            modules_discovered: 1,
            modules_loaded: 1,
            load_summaries: 1,
            added_constants: 1,
            duplicate_constants: 0,
            skipped_constants: 0,
            search_paths: Vec::new(),
            project_oleans_only: true,
            prelude_error: None,
            module_errors: Vec::new(),
        };
        let args = lake_args(dir.path(), true);

        let gate_status = lake_audit_gate_status(&report, &load, &args);

        assert!(!gate_status.is_accepted());
        assert_eq!(
            gate_status.failure_mode.as_deref(),
            Some("project_oleans_only_external_baseline")
        );
    }

    #[test]
    fn lake_audit_source_loader_reconstructs_workspace_without_oleans() {
        let dir = tempfile::tempdir().expect("tempdir should be created");
        fs::write(
            dir.path().join("lakefile.lean"),
            "package test\nlean_lib Test\n",
        )
        .expect("lakefile should be written");
        fs::create_dir_all(dir.path().join("Test")).expect("module dir should be created");
        fs::write(
            dir.path().join("Test/A.lean"),
            "namespace Test.A\n\ndef a : Nat := 1\n\nend Test.A\n",
        )
        .expect("A.lean should be written");
        fs::write(
            dir.path().join("Test.lean"),
            "import Test.A\nnamespace Test\n\ndef b : Nat := 2\n\nend Test\n",
        )
        .expect("Test.lean should be written");

        let workspace = clean_lake::Workspace::load(dir.path()).expect("workspace should load");
        let modules = workspace.all_modules();
        let load = load_project_environment(&workspace, &modules, false);

        assert!(
            load.module_errors.is_empty(),
            "source reconstruction should not require .olean dependencies: {:?}",
            load.module_errors
        );
        assert_eq!(load.modules_loaded, load.modules_discovered);
        assert!(
            load.modules_discovered >= 2,
            "expected Test and Test.A modules, got {}",
            load.modules_discovered
        );
        assert!(load
            .env
            .get_const(&clean_kernel::Name::from_string("Test.A.a"))
            .is_some());
        assert!(load
            .env
            .get_const(&clean_kernel::Name::from_string("Test.b"))
            .is_some());
    }

    #[test]
    fn lake_audit_source_loader_respects_requested_module_closure() {
        let dir = tempfile::tempdir().expect("tempdir should be created");
        fs::write(
            dir.path().join("lakefile.lean"),
            "package test\nlean_lib Test\n",
        )
        .expect("lakefile should be written");
        fs::create_dir_all(dir.path().join("Test")).expect("module dir should be created");
        fs::write(
            dir.path().join("Test/Core.lean"),
            "namespace Test.Core\n\ndef core : Nat := 1\n\nend Test.Core\n",
        )
        .expect("Core.lean should be written");
        fs::write(
            dir.path().join("Test/Calibration.lean"),
            "import Test.Core\nnamespace Test.Calibration\n\ndef calibration : Nat := 2\n\nend Test.Calibration\n",
        )
        .expect("Calibration.lean should be written");
        fs::write(
            dir.path().join("Test/Unused.lean"),
            "namespace Test.Unused\n\ndef unused : Nat := 3\n\nend Test.Unused\n",
        )
        .expect("Unused.lean should be written");

        let workspace = clean_lake::Workspace::load(dir.path()).expect("workspace should load");
        let load = load_project_environment(&workspace, &["Test.Calibration".to_owned()], false);

        assert!(
            load.module_errors.is_empty(),
            "requested source closure should reconstruct: {:?}",
            load.module_errors
        );
        assert_eq!(load.modules_discovered, 2);
        assert_eq!(load.modules_loaded, 2);
        assert!(load
            .env
            .get_const(&clean_kernel::Name::from_string("Test.Core.core"))
            .is_some());
        assert!(load
            .env
            .get_const(&clean_kernel::Name::from_string(
                "Test.Calibration.calibration"
            ))
            .is_some());
        assert!(load
            .env
            .get_const(&clean_kernel::Name::from_string("Test.Unused.unused"))
            .is_none());
    }

    #[test]
    fn lake_audit_text_includes_authority_gate_status() {
        let dir = tempfile::tempdir().expect("tempdir should be created");
        let out = dir.path().join("audit.txt");
        let report = rejected_report();
        let gate_status = project_audit_authority_gate_status(&report);

        write_lake_audit_text(&report, &gate_status, None, Some(&out))
            .expect("text should be written");

        let text = fs::read_to_string(out).expect("text should be readable");
        assert!(text.contains("Authority gate:"));
        assert!(text.contains("status: rejected"));
        assert!(text.contains("failure_mode: axiom_declaration"));
        assert!(text.contains("trust_level: AxiomDependent"));
    }

    #[test]
    fn trust_ledger_missing_target_is_hard_failure() {
        let env = Environment::new();
        let target = clean_kernel::Name::from_string("Ledger.Missing");

        let (report, ledger) =
            build_trust_ledger_report(&env, target).expect("ledger should build");

        assert!(!report.is_clean());
        assert_eq!(ledger.status, "rejected");
        assert_eq!(ledger.failure_mode, Some("missing_dependency"));
        assert_eq!(ledger.missing_dependencies, vec!["Ledger.Missing"]);
        assert_eq!(ledger.hard_failures[0].failure_mode, "missing_dependency");
        assert_eq!(ledger.target_hash.len(), 64);
        assert!(ledger.target_hash.chars().all(|ch| ch.is_ascii_hexdigit()));
    }

    #[test]
    fn trust_ledger_non_foundational_axiom_is_hard_failure() {
        let mut env = Environment::new();
        let target = clean_kernel::Name::from_string("Ledger.NonFoundationalAxiom");
        env.extend_constants_unchecked(std::iter::once(ConstantInfo::new_with_reducibility(
            target.clone(),
            Vec::new(),
            clean_kernel::Expr::type_(),
            None,
            Reducibility::Opaque,
            ConstantKind::Axiom,
        )));

        let (report, ledger) =
            build_trust_ledger_report(&env, target).expect("ledger should build");

        assert!(!report.is_clean());
        assert_eq!(ledger.status, "rejected");
        assert_eq!(ledger.failure_mode, Some("axiom_dependent"));
        assert_eq!(ledger.constants[0].trust_level, TrustLevel::AxiomDependent);
        assert_eq!(ledger.hard_failures[0].failure_mode, "axiom_dependent");
    }

    #[test]
    fn trust_ledger_record_attempt_writes_mathverse_evidence() {
        let dir = tempfile::tempdir().expect("tempdir should be created");
        let env = Environment::new();
        let target = clean_kernel::Name::from_string("Ledger.Missing");
        let (report, ledger) =
            build_trust_ledger_report(&env, target).expect("ledger should build");

        let attempt = record_trust_ledger_attempt_at(dir.path(), &ledger, &report, 31)
            .expect("trust ledger attempt should record");
        let receipt = AuthorityReceipt::from_attempt(&attempt);

        assert_eq!(receipt.authority_gate, TRUST_LEDGER_AUTHORITY_GATE);
        assert_eq!(receipt.status, "rejected");
        assert_eq!(receipt.goal_hash, ledger.target_hash);
        assert_eq!(receipt.failure_mode.as_deref(), Some("missing_dependency"));
        assert_eq!(
            receipt
                .solver_artifact
                .as_ref()
                .and_then(|artifact| artifact.kind.as_deref()),
            Some(TRUST_LEDGER_ARTIFACT_KIND)
        );
        assert_eq!(
            receipt
                .command_evidence
                .as_ref()
                .and_then(|artifact| artifact.kind.as_deref()),
            Some(AUTHORITY_COMMAND_EVIDENCE_ARTIFACT_KIND)
        );
        let evidence = command_evidence_json(dir.path(), &attempt);
        assert_eq!(
            evidence["schema_version"],
            AUTHORITY_COMMAND_EVIDENCE_SCHEMA
        );
        assert_eq!(
            evidence["command"],
            "clean audit trust-ledger --record-attempt"
        );
        assert_eq!(evidence["authority_gate"], TRUST_LEDGER_AUTHORITY_GATE);
        assert_eq!(evidence["authority_schema"], TRUST_LEDGER_SCHEMA);
        assert_eq!(
            evidence["policy"],
            "recursive trust ledger has no hard failures"
        );
        assert_eq!(evidence["gate_status"]["kind"], "rejected");
        assert_eq!(evidence["source_root"], dir.path().display().to_string());
        assert_eq!(evidence["goal_hash"], ledger.target_hash);
        assert_eq!(evidence["trust_audit_hash"], attempt.trust_audit_hash);
        assert_eq!(evidence["report_hash"], attempt.trust_audit_hash);
        assert_eq!(evidence["source_digest"], ledger.closure_hash);
        assert_eq!(evidence["artifacts"][0]["role"], "trust_ledger_report");
        assert_eq!(evidence["artifacts"][0]["kind"], TRUST_LEDGER_ARTIFACT_KIND);
        assert!(dir.path().join(".cake/attempts").is_dir());
    }
}
