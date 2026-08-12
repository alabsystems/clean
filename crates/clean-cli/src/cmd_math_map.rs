// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean math-map` bundle-ingest and key-registry commands.
//!
//! The user-facing entry point for the fail-closed MathMap/Harmonic Lean
//! patch-bundle pipeline implemented in `clean_mathverse::math_map`. Nothing in
//! a bundle is trusted: this surface only *drives* the ingest pipeline and
//! reports its verdict. Every default is a refusal — a `Rejected` or `Blocked`
//! ingest exits non-zero unless the operator explicitly asks for diagnostics
//! with `--report-only`.

use std::io::{self, Write};
use std::path::PathBuf;

use anyhow::{bail, Context};
use clap::{Args, Subcommand};
use clean_features::{Category, Example, FeatureDescriptor, RefKind, Reference, Stability};
use clean_mathverse::math_map::{
    ingest_bundle_with_verifier, ingest_bundle_with_verifier_to_attempt_log,
    Ed25519SignatureVerifier, IngestStatus, MathMapIngestConfig, MathMapIngestReport,
    MathMapPolicy, StepStatus, TrustedKeyRegistry,
};
use serde::Serialize;

/// The `clean-mathverse` crate owns the ingest pipeline this surface drives.
/// `RefKind::Crate` (not `Doc`) because the authoritative description of the
/// contract is the module documentation on `clean_mathverse::math_map`, not a
/// standalone markdown page.
const INGEST_CRATE_REF: Reference = Reference {
    kind: RefKind::Crate,
    label: "clean-mathverse (math_map ingest pipeline)",
    target: "clean-mathverse",
};

pub(crate) const FEATURES: &[FeatureDescriptor] = &[
    FeatureDescriptor {
        path: &["math-map", "ingest"],
        summary: "Validate and ingest a MathMap patch bundle (Experimental)",
        description: "\
Experimental MathMap/Harmonic interoperability surface. The command validates \
a `clean-math_map-bundle-v1` directory, cryptographically checks the signed \
bundle metadata against the bundled or caller-provided trusted-key registry, \
runs the configured ingest policy, and can append the result to the Mathverse \
proof-attempt log with `--record-attempt`. Rejected or blocked ingests exit \
non-zero unless `--report-only` is set for diagnostics. `--json` emits the \
full ingest report for release automation and replayable evidence.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[
            Example {
                cmd: "clean math-map ingest /tmp/clean-math_map-bundle-v1 --registry /tmp/trusted-keys.toml --report-only",
                what: "diagnose a MathMap patch bundle with an explicit trusted-key registry",
            },
            Example {
                cmd: "clean math-map ingest /tmp/clean-math_map-bundle-v1 --root . --registry /tmp/trusted-keys.toml --record-attempt --json",
                what: "record an accepted MathMap attempt in the Mathverse log and emit JSON",
            },
        ],
        see_also: &[
            "math-map keys list",
            "math-map keys verify",
            "attempts record-external-patch",
        ],
        references: &[INGEST_CRATE_REF],
        domain_root: Some("math-map"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["math-map", "keys", "list"],
        summary: "List trusted MathMap signing keys (Experimental)",
        description: "\
Experimental MathMap trusted-key registry inspection surface. The command \
loads the bundled registry by default, or a caller-provided registry with \
`--registry`, and prints the trusted MathMap signing keys used by bundle \
signature verification. `--json` emits the registry for automation and docs \
drift checks.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[
            Example {
                cmd: "clean math-map keys list",
                what: "list the bundled trusted MathMap signing keys",
            },
            Example {
                cmd: "clean math-map keys list --registry /tmp/trusted-keys.toml --json",
                what: "emit a caller-provided trusted-key registry as JSON",
            },
        ],
        see_also: &["math-map ingest", "math-map keys verify"],
        references: &[INGEST_CRATE_REF],
        domain_root: Some("math-map"),
        alternative_forms: &[],
        feature_gate: None,
    },
    FeatureDescriptor {
        path: &["math-map", "keys", "verify"],
        summary: "Validate a MathMap trusted-key registry (Experimental)",
        description: "\
Experimental MathMap trusted-key registry validation surface. The command \
loads the bundled registry by default, or a caller-provided registry with \
`--registry`, and fails closed when the registry is malformed or contains \
invalid trusted-key entries. `--json` emits a validation report for release \
and operator automation.",
        category: Category::Dev,
        stability: Stability::Experimental,
        examples: &[
            Example {
                cmd: "clean math-map keys verify",
                what: "validate the bundled trusted-key registry",
            },
            Example {
                cmd: "clean math-map keys verify --registry /tmp/trusted-keys.toml --json",
                what: "validate a caller-provided trusted-key registry and emit JSON",
            },
        ],
        see_also: &["math-map ingest", "math-map keys list"],
        references: &[INGEST_CRATE_REF],
        domain_root: Some("math-map"),
        alternative_forms: &[],
        feature_gate: None,
    },
];

/// MathMap/Harmonic Lean patch-bundle commands.
#[derive(Debug, Clone, Subcommand)]
pub(crate) enum MathMapCommands {
    /// Validate and ingest a MathMap Lean patch bundle.
    Ingest(MathMapIngestArgs),
    /// Trusted key registry operations for MathMap bundle signatures.
    Keys {
        #[command(subcommand)]
        command: MathMapKeyCommands,
    },
}

/// Arguments for `clean math-map ingest`.
#[derive(Debug, Clone, Args)]
pub(crate) struct MathMapIngestArgs {
    /// Path to a `clean-math_map-bundle-v1` directory.
    pub(crate) bundle: PathBuf,
    /// Repository or project root containing the `.mathverse` attempt log.
    #[arg(long, default_value = ".")]
    pub(crate) root: PathBuf,
    /// TOML trusted-key registry path. Defaults to the bundled registry.
    #[arg(long)]
    pub(crate) registry: Option<PathBuf>,
    /// Append the ingest result to the Mathverse proof-attempt log.
    #[arg(long)]
    pub(crate) record_attempt: bool,
    /// Emit diagnostics without failing the process for blocked or rejected ingest.
    #[arg(long)]
    pub(crate) report_only: bool,
    /// Emit the full ingest report JSON.
    #[arg(long)]
    pub(crate) json: bool,
}

/// Subcommands under `clean math-map keys`.
#[derive(Debug, Clone, Subcommand)]
pub(crate) enum MathMapKeyCommands {
    /// List trusted MathMap signing keys.
    List(MathMapKeysListArgs),
    /// Validate a trusted key registry.
    Verify(MathMapKeysVerifyArgs),
}

/// Arguments for `clean math-map keys list`.
#[derive(Debug, Clone, Args)]
pub(crate) struct MathMapKeysListArgs {
    /// TOML trusted-key registry path. Defaults to the bundled registry.
    #[arg(long)]
    pub(crate) registry: Option<PathBuf>,
    /// Emit JSON instead of a human-readable table.
    #[arg(long)]
    pub(crate) json: bool,
}

/// Arguments for `clean math-map keys verify`.
#[derive(Debug, Clone, Args)]
pub(crate) struct MathMapKeysVerifyArgs {
    /// TOML trusted-key registry path. Defaults to the bundled registry.
    #[arg(long)]
    pub(crate) registry: Option<PathBuf>,
    /// Emit JSON instead of a human-readable report.
    #[arg(long)]
    pub(crate) json: bool,
}

/// Machine-readable verdict emitted by `clean math-map keys verify --json`.
#[derive(Debug, Serialize)]
struct KeyRegistryValidationReport {
    generated_by: &'static str,
    registry: String,
    status: &'static str,
    key_count: usize,
    errors: Vec<String>,
}

pub(crate) fn handle_math_map_command(command: MathMapCommands) -> anyhow::Result<()> {
    match command {
        MathMapCommands::Ingest(args) => run_ingest(args),
        MathMapCommands::Keys { command } => handle_key_command(command),
    }
}

fn run_ingest(args: MathMapIngestArgs) -> anyhow::Result<()> {
    let config = MathMapIngestConfig {
        policy: MathMapPolicy::builtin(),
        trusted_keys: load_registry(args.registry.as_ref())?,
    };
    let verifier = Ed25519SignatureVerifier;
    let report = if args.record_attempt {
        ingest_bundle_with_verifier_to_attempt_log(&args.bundle, &args.root, config, &verifier)
            .with_context(|| {
                format!(
                    "failed to write MathMap ingest attempt under {}",
                    args.root.display()
                )
            })?
    } else {
        ingest_bundle_with_verifier(&args.bundle, config, &verifier)
    };

    let stdout = io::stdout();
    let mut out = stdout.lock();
    if args.json {
        writeln!(out, "{}", serde_json::to_string_pretty(&report)?)?;
    } else {
        render_ingest_human(&mut out, &report)?;
    }
    if args.report_only {
        return Ok(());
    }
    fail_unless_ingest_accepted(&report)
}

/// Fail-closed exit-code path: only `IngestStatus::Accepted` returns `Ok`.
///
/// A `Rejected` bundle failed a gate; a `Blocked` bundle is one where no gate
/// rejected but required evidence was absent — which is NOT an acceptance.
/// Both must exit non-zero so an operator (or release automation) can never
/// mistake "we could not tell" for "this bundle is safe to apply".
fn fail_unless_ingest_accepted(report: &MathMapIngestReport) -> anyhow::Result<()> {
    match &report.status {
        IngestStatus::Accepted => Ok(()),
        IngestStatus::Rejected { step, reason } => {
            bail!("MathMap ingest rejected at {step:?}: {reason}")
        }
        IngestStatus::Blocked { reason } => bail!("MathMap ingest blocked: {reason}"),
    }
}

fn handle_key_command(command: MathMapKeyCommands) -> anyhow::Result<()> {
    match command {
        MathMapKeyCommands::List(args) => list_keys(args),
        MathMapKeyCommands::Verify(args) => verify_keys(args),
    }
}

fn list_keys(args: MathMapKeysListArgs) -> anyhow::Result<()> {
    let registry = load_registry(args.registry.as_ref())?;
    let stdout = io::stdout();
    let mut out = stdout.lock();
    if args.json {
        writeln!(out, "{}", serde_json::to_string_pretty(&registry)?)?;
    } else {
        writeln!(out, "MathMap trusted keys: {}", registry.keys.len())?;
        for key in &registry.keys {
            writeln!(
                out,
                "- service={} key={} algorithm={} status={}",
                key.service, key.key_id, key.algorithm, key.status
            )?;
        }
    }
    Ok(())
}

fn verify_keys(args: MathMapKeysVerifyArgs) -> anyhow::Result<()> {
    let registry_label = args
        .registry
        .as_ref()
        .map_or_else(|| "builtin".to_owned(), |path| path.display().to_string());
    let registry = load_registry(args.registry.as_ref())?;
    let errors = registry
        .validation_errors()
        .into_iter()
        .map(|err| format!("{err:?}"))
        .collect::<Vec<_>>();
    let report = KeyRegistryValidationReport {
        generated_by: "clean math-map keys verify",
        registry: registry_label,
        status: if errors.is_empty() {
            "VALID"
        } else {
            "INVALID"
        },
        key_count: registry.keys.len(),
        errors,
    };

    let stdout = io::stdout();
    let mut out = stdout.lock();
    if args.json {
        writeln!(out, "{}", serde_json::to_string_pretty(&report)?)?;
    } else {
        writeln!(
            out,
            "MathMap trusted key registry: {} ({} keys)",
            report.status, report.key_count
        )?;
        for error in &report.errors {
            writeln!(out, "- {error}")?;
        }
    }

    if !report.errors.is_empty() {
        bail!(
            "MathMap trusted key registry is invalid: {} error(s)",
            report.errors.len()
        );
    }
    Ok(())
}

fn load_registry(path: Option<&PathBuf>) -> anyhow::Result<TrustedKeyRegistry> {
    match path {
        Some(path) => TrustedKeyRegistry::load(path).map_err(Into::into),
        None => Ok(TrustedKeyRegistry::builtin()),
    }
}

fn render_ingest_human(out: &mut impl Write, report: &MathMapIngestReport) -> io::Result<()> {
    writeln!(
        out,
        "MathMap ingest: {}",
        ingest_status_label(&report.status)
    )?;
    writeln!(out, "bundle: {}", report.bundle_path)?;
    if let Some(job_id) = &report.job_id {
        writeln!(out, "job: {job_id}")?;
    }
    if let Some(service) = &report.service {
        writeln!(out, "service: {service}")?;
    }
    if let Some(signature) = &report.signature {
        writeln!(
            out,
            "signature: key={} algorithm={} cryptographic={}",
            signature.key_id, signature.algorithm, signature.cryptographic
        )?;
    }
    for step in &report.steps {
        writeln!(
            out,
            "{}. {} {}",
            step.number,
            step.name,
            step_status_label(step.status)
        )?;
        if let Some(failure) = &step.failure {
            writeln!(out, "   failure: {failure:?}")?;
        }
    }
    if let Some(attempt) = &report.proof_attempt {
        writeln!(
            out,
            "proof_attempt: {} {:?}",
            attempt.attempt_id, attempt.attempt_status
        )?;
    }
    Ok(())
}

fn ingest_status_label(status: &IngestStatus) -> &'static str {
    match status {
        IngestStatus::Accepted => "accepted",
        IngestStatus::Rejected { .. } => "rejected",
        IngestStatus::Blocked { .. } => "blocked",
    }
}

fn step_status_label(status: StepStatus) -> &'static str {
    match status {
        StepStatus::NotRun => "not_run",
        StepStatus::Passed => "passed",
        StepStatus::Failed => "failed",
        StepStatus::Skipped => "skipped",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    use clean_mathverse::math_map::{
        PipelineStep, PipelineStepResult, TrustedKey, MATH_MAP_ARTIFACT_KIND,
        MATH_MAP_INGEST_SCHEMA_VERSION,
    };
    use tempfile::NamedTempFile;

    /// Write a TOML registry to a self-cleaning temp file and return the handle.
    /// Each test owns its own file; nothing is shared between tests.
    fn temp_registry(text: &str) -> NamedTempFile {
        let mut file = NamedTempFile::new().expect("create temp registry file");
        file.write_all(text.as_bytes())
            .expect("write temp registry contents");
        file.flush().expect("flush temp registry contents");
        file
    }

    fn blocked_report(steps: Vec<PipelineStepResult>) -> MathMapIngestReport {
        MathMapIngestReport {
            schema_version: MATH_MAP_INGEST_SCHEMA_VERSION.to_owned(),
            artifact_kind: MATH_MAP_ARTIFACT_KIND.to_owned(),
            bundle_path: "bundle".to_owned(),
            bundle_sha256: None,
            job_id: None,
            service: None,
            status: IngestStatus::Blocked {
                reason: "authority gates unavailable".to_owned(),
            },
            steps,
            authority_gates: None,
            signature: None,
            proof_attempt: None,
        }
    }

    #[test]
    fn ingest_human_output_reports_status_and_steps() {
        let report = blocked_report(vec![PipelineStepResult {
            number: 1,
            step: PipelineStep::BundleIntegrity,
            name: "bundle_integrity".to_owned(),
            status: StepStatus::Passed,
            failure: None,
            details: BTreeMap::new(),
        }]);

        let mut out = Vec::new();
        render_ingest_human(&mut out, &report).expect("render");
        let text = String::from_utf8(out).expect("utf8");

        assert!(text.contains("MathMap ingest: blocked"));
        assert!(text.contains("bundle: bundle"));
        assert!(text.contains("1. bundle_integrity passed"));
    }

    #[test]
    fn ingest_cli_status_fails_closed_unless_report_only() {
        let report = blocked_report(Vec::new());

        let err = fail_unless_ingest_accepted(&report).expect_err("blocked ingest exits non-zero");
        assert!(err.to_string().contains("MathMap ingest blocked"));
    }

    #[test]
    fn ingest_cli_status_fails_closed_for_rejected_bundle() {
        let mut report = blocked_report(Vec::new());
        report.status = IngestStatus::Rejected {
            step: PipelineStep::BundleIntegrity,
            reason: "manifest hash mismatch".to_owned(),
        };

        let err = fail_unless_ingest_accepted(&report).expect_err("rejected ingest exits non-zero");
        let text = err.to_string();
        assert!(text.contains("MathMap ingest rejected"), "{text}");
        assert!(text.contains("manifest hash mismatch"), "{text}");
    }

    #[test]
    fn ingest_cli_status_accepts_accepted_bundle() {
        let mut report = blocked_report(Vec::new());
        report.status = IngestStatus::Accepted;

        fail_unless_ingest_accepted(&report).expect("accepted ingest exits zero");
    }

    #[test]
    fn key_validation_report_marks_trusted_placeholder_invalid() {
        let registry = TrustedKeyRegistry {
            schema_version: "clean-math_map-trusted-keys-v1".to_owned(),
            keys: vec![TrustedKey {
                service: "math_map".to_owned(),
                key_id: "placeholder".to_owned(),
                algorithm: "ed25519".to_owned(),
                public_key: clean_mathverse::math_map::keys::PLACEHOLDER_PUBLIC_KEY.to_owned(),
                status: "trusted".to_owned(),
            }],
        };
        let errors = registry.validation_errors();

        assert!(!errors.is_empty());
    }

    #[test]
    fn keys_verify_json_fails_closed_for_trusted_placeholder_registry_file() {
        let registry = temp_registry(
            r#"
schema_version = "clean-math_map-trusted-keys-v1"

[[keys]]
service = "math_map"
key_id = "placeholder"
algorithm = "ed25519"
public_key = "REPLACE_WITH_REAL_MATH_MAP_ED25519_PUBLIC_KEY"
status = "trusted"
"#,
        );

        let err = verify_keys(MathMapKeysVerifyArgs {
            registry: Some(registry.path().to_path_buf()),
            json: true,
        })
        .expect_err("trusted placeholder registry must fail validation");

        assert!(err
            .to_string()
            .contains("MathMap trusted key registry is invalid: 1 error(s)"));
    }

    #[test]
    fn keys_verify_json_accepts_disabled_placeholder_registry_file() {
        let registry = temp_registry(
            r#"
schema_version = "clean-math_map-trusted-keys-v1"

[[keys]]
service = "math_map"
key_id = "math_map-placeholder-disabled"
algorithm = "ed25519"
public_key = "REPLACE_WITH_REAL_MATH_MAP_ED25519_PUBLIC_KEY"
status = "disabled"
"#,
        );

        verify_keys(MathMapKeysVerifyArgs {
            registry: Some(registry.path().to_path_buf()),
            json: true,
        })
        .expect("disabled placeholder registry should validate like the bundled registry");
    }

    #[test]
    fn keys_list_reads_the_builtin_registry_without_a_path() {
        list_keys(MathMapKeysListArgs {
            registry: None,
            json: true,
        })
        .expect("bundled trusted-key registry must list cleanly");
    }
}
