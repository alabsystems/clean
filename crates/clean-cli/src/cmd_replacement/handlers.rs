// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Subcommand dispatch and the top-level status report type.

use super::*;

/// Dispatch entry point for `clean replacement`.
pub(crate) fn handle_replacement_command(
    command: ReplacementCommands,
) -> Result<(), ReplacementError> {
    match command {
        ReplacementCommands::Status(args) => run_status(args),
        ReplacementCommands::ReleaseIssueHygiene(args) => run_release_issue_hygiene(args),
        ReplacementCommands::NativeLibrary { command } => {
            Ok(handle_native_library_command(command)?)
        }
        ReplacementCommands::ValidateReport(args) => run_validate_report(args),
        ReplacementCommands::AxiomAudit(args) => run_axiom_audit(args),
        ReplacementCommands::TacticParity(args) => run_tactic_parity(args),
        ReplacementCommands::TrustCoreEvidence(args) => run_trust_core_evidence(args),
        ReplacementCommands::TrustBoundaryAudit(args) => run_trust_boundary_audit(args),
    }
}

pub(crate) fn run_status(args: ReplacementStatusArgs) -> Result<(), ReplacementError> {
    if args.informational {
        let scorecard = InformationalScorecard::current();
        let stdout = io::stdout();
        let mut out = stdout.lock();
        if args.json {
            writeln!(
                out,
                "{}",
                serde_json::to_string_pretty(&scorecard).map_err(ReplacementError::Serialize)?
            )?;
        } else {
            render_informational_human(&mut out, &scorecard)?;
        }
        return Ok(());
    }

    let report = ReplacementStatusReport::current()?;

    let stdout = io::stdout();
    let mut out = stdout.lock();
    if args.json {
        writeln!(
            out,
            "{}",
            serde_json::to_string_pretty(&report).map_err(ReplacementError::Serialize)?
        )?;
    } else {
        render_human(&mut out, &report)?;
    }
    Ok(())
}

pub(crate) fn run_release_issue_hygiene(
    args: ReleaseIssueHygieneArgs,
) -> Result<(), ReplacementError> {
    let report = ReleaseIssueHygieneReport::from_args(&args);

    let stdout = io::stdout();
    let mut out = stdout.lock();
    if args.json {
        writeln!(
            out,
            "{}",
            serde_json::to_string_pretty(&report).map_err(ReplacementError::Serialize)?
        )?;
    } else {
        render_release_issue_hygiene_human(&mut out, &report)?;
    }

    if report.ready {
        Ok(())
    } else {
        Err(ReplacementError::ReleaseIssueHygieneNotReady {
            message: report.parity_blocker.clone(),
        })
    }
}

pub(crate) fn run_validate_report(args: ValidateReportArgs) -> Result<(), ReplacementError> {
    let validation = ReplacementReportValidation::from_args(&args)?;

    let stdout = io::stdout();
    let mut out = stdout.lock();
    if args.json {
        writeln!(
            out,
            "{}",
            serde_json::to_string_pretty(&validation).map_err(ReplacementError::Serialize)?
        )?;
    } else {
        render_report_validation_human(&mut out, &validation)?;
    }

    if validation.validation_passed {
        Ok(())
    } else {
        Err(ReplacementError::ReportValidation {
            message: validation.failures.join("; "),
        })
    }
}

pub(crate) fn run_axiom_audit(args: AxiomAuditArgs) -> Result<(), ReplacementError> {
    let verification = AxiomAuditVerification::from_args(&args)?;
    if let Some(evidence_path) = &args.evidence {
        let artifact = verification.launch_evidence_artifact();
        write_json_path(evidence_path, &artifact)?;
    }

    let stdout = io::stdout();
    let mut out = stdout.lock();
    if args.json {
        writeln!(
            out,
            "{}",
            serde_json::to_string_pretty(&verification).map_err(ReplacementError::Serialize)?
        )?;
    } else {
        render_axiom_audit_human(&mut out, &verification)?;
    }

    if verification.validation_passed {
        Ok(())
    } else {
        Err(ReplacementError::StaleTrustCoreArtifact {
            message: verification.failures.join("; "),
        })
    }
}

pub(crate) fn run_tactic_parity(args: TacticParityArgs) -> Result<(), ReplacementError> {
    if let Some(command) = args.command {
        return match command {
            TacticParityCommands::DiscoverFullCorpusInputs(args) => {
                run_tactic_parity_discover_full_corpus_inputs(args)
            }
            TacticParityCommands::GenerateFullCorpusFixture(args) => {
                run_tactic_parity_generate_full_corpus_fixture(args)
            }
            TacticParityCommands::ValidateFullCorpus(args) => {
                run_tactic_parity_validate_full_corpus(args)
            }
        };
    }

    let report = TacticParityReport::current();

    let stdout = io::stdout();
    let mut out = stdout.lock();
    if args.json {
        writeln!(
            out,
            "{}",
            serde_json::to_string_pretty(&report).map_err(ReplacementError::Serialize)?
        )?;
    } else {
        render_tactic_parity_human(&mut out, &report)?;
    }
    Ok(())
}

pub(crate) fn run_tactic_parity_discover_full_corpus_inputs(
    args: TacticParityDiscoverFullCorpusInputsArgs,
) -> Result<(), ReplacementError> {
    let discovery = TacticParityFullCorpusInputDiscovery::from_registry_path(&args.registry);

    let stdout = io::stdout();
    let mut out = stdout.lock();
    if args.json {
        writeln!(
            out,
            "{}",
            serde_json::to_string_pretty(&discovery).map_err(ReplacementError::Serialize)?
        )?;
    } else {
        render_tactic_parity_full_corpus_input_discovery_human(&mut out, &discovery)?;
    }
    Ok(())
}

pub(crate) fn run_tactic_parity_generate_full_corpus_fixture(
    args: TacticParityGenerateFullCorpusFixtureArgs,
) -> Result<(), ReplacementError> {
    let generation = TacticParityFullCorpusFixtureGeneration::write_to_path(&args.output)?;

    let stdout = io::stdout();
    let mut out = stdout.lock();
    if args.json {
        writeln!(
            out,
            "{}",
            serde_json::to_string_pretty(&generation).map_err(ReplacementError::Serialize)?
        )?;
    } else {
        render_tactic_parity_full_corpus_fixture_generation_human(&mut out, &generation)?;
    }

    if generation.validation.validation_passed {
        Ok(())
    } else {
        Err(ReplacementError::ReportValidation {
            message: generation.validation.failures.join("; "),
        })
    }
}

pub(crate) fn run_tactic_parity_validate_full_corpus(
    args: TacticParityValidateFullCorpusArgs,
) -> Result<(), ReplacementError> {
    let validation = TacticParityFullCorpusValidation::from_report_path(&args.report);

    let stdout = io::stdout();
    let mut out = stdout.lock();
    if args.json {
        writeln!(
            out,
            "{}",
            serde_json::to_string_pretty(&validation).map_err(ReplacementError::Serialize)?
        )?;
    } else {
        render_tactic_parity_full_corpus_validation_human(&mut out, &validation)?;
    }

    if validation.validation_passed {
        Ok(())
    } else {
        Err(ReplacementError::ReportValidation {
            message: validation.failures.join("; "),
        })
    }
}

pub(crate) fn run_trust_core_evidence(args: TrustCoreEvidenceArgs) -> Result<(), ReplacementError> {
    if args.kernel_soundness && args.deny_sorry {
        return Err(ReplacementError::StaleTrustCoreArtifact {
            message: "--kernel-soundness and --deny-sorry are mutually exclusive".to_string(),
        });
    }
    if args.kernel_soundness {
        let artifact = generate_kernel_soundness_launch_evidence(&args.generated_at)?;
        return write_kernel_soundness_launch_evidence(&args, &artifact);
    }
    if args.deny_sorry {
        let artifact = generate_deny_sorry_launch_evidence(&args.generated_at)?;
        return write_deny_sorry_launch_evidence(&args, &artifact);
    }

    let report = TrustCoreEvidenceReport::current()?;

    let stdout = io::stdout();
    let mut out = stdout.lock();
    if args.json {
        writeln!(
            out,
            "{}",
            serde_json::to_string_pretty(&report).map_err(ReplacementError::Serialize)?
        )?;
    } else {
        render_trust_core_evidence_human(&mut out, &report)?;
    }
    Ok(())
}

pub(crate) fn run_trust_boundary_audit(
    args: TrustBoundaryAuditArgs,
) -> Result<(), ReplacementError> {
    let report = TrustBoundaryAuditReport::from_args(&args)?;
    let markdown = if args.output.is_some() || !args.json {
        Some(render_trust_boundary_audit_markdown(&report))
    } else {
        None
    };

    if let (Some(output), Some(markdown)) = (&args.output, &markdown) {
        if let Some(parent) = output.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(output, markdown)?;
    }

    let stdout = io::stdout();
    let mut out = stdout.lock();
    if args.json {
        writeln!(
            out,
            "{}",
            serde_json::to_string_pretty(&report).map_err(ReplacementError::Serialize)?
        )?;
    } else if let Some(markdown) = markdown {
        writeln!(out, "{markdown}")?;
    }
    Ok(())
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct ReplacementStatusReport {
    pub(crate) schema_version: &'static str,
    pub(crate) generated_by: &'static str,
    pub(crate) target_claim: &'static str,
    pub(crate) launch_ready: bool,
    pub(crate) overall_status: ReplacementStatus,
    pub(crate) zero_trust_gates_passed: bool,
    pub(crate) canonical_epic: IssueRef,
    pub(crate) product_epic: IssueRef,
    pub(crate) proof_system_epic: IssueRef,
    pub(crate) counts: BTreeMap<ReplacementStatus, usize>,
    /// Counts by evidence-derived `effective_status` (M2). When this differs from
    /// `counts`, a row is claiming more than its on-disk evidence supports.
    pub(crate) effective_counts: BTreeMap<ReplacementStatus, usize>,
    pub(crate) zero_trust_gate_counts: BTreeMap<ZeroTrustGateStatus, usize>,
    pub(crate) zero_trust_gates: Vec<ZeroTrustGateRow>,
    pub(crate) proof_system_certification: ProofSystemCertificationEvidence,
    pub(crate) rust_first_tooling: RustFirstToolingStatus,
    pub(crate) readiness_accounting: ReplacementReadinessAccounting,
    pub(crate) rows: Vec<ReplacementRow>,
}

impl ReplacementStatusReport {
    pub(crate) fn current() -> Result<Self, ReplacementError> {
        let trust_core = TrustCoreEvidenceReport::current()?;
        let proof_system_certification = trust_core.proof_system_certification;
        let zero_trust_gates = trust_core.zero_trust_gates;
        let zero_trust_gate_counts = count_zero_trust_gate_status(&zero_trust_gates);
        let zero_trust_gates_passed = zero_trust_gates
            .iter()
            .filter(|gate| gate.required_for_launch)
            .all(|gate| gate.status == ZeroTrustGateStatus::Passed);
        let rows = replacement_rows();
        let counts = count_by_status(&rows);
        let effective_counts = count_by_effective_status(&rows);
        let rust_first_tooling = rust_first_tooling_status();
        // M2: the gate consumes the evidence-derived `effective_status`, not the
        // hand-declared `status`. A row whose evidence file is missing or a stub
        // can no longer hold the scorecard `Green`.
        let rows_ready = rows
            .iter()
            .all(|row| row.effective_status == ReplacementStatus::Green);
        let launch_ready = rows_ready && zero_trust_gates_passed;
        let overall_status = if launch_ready {
            ReplacementStatus::Green
        } else {
            ReplacementStatus::Blocked
        };
        let readiness_accounting = ReplacementReadinessAccounting::from_current(
            &rows,
            &rust_first_tooling,
            zero_trust_gates_passed,
            rows_ready,
            launch_ready,
        );

        Ok(Self {
            schema_version: SCHEMA_VERSION,
            generated_by: "clean replacement status",
            target_claim: TARGET_CLAIM,
            launch_ready,
            overall_status,
            zero_trust_gates_passed,
            canonical_epic: IssueRef::new(3691, "Canonical clean AI-factory execution plan"),
            product_epic: IssueRef::new(3698, "clean full Lean4 ecosystem replacement"),
            proof_system_epic: IssueRef::new(
                3697,
                "clean proof system: zero-trust kernel, Mathverse, and replay certification",
            ),
            counts,
            effective_counts,
            zero_trust_gate_counts,
            zero_trust_gates,
            proof_system_certification,
            rust_first_tooling,
            readiness_accounting,
            rows,
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(crate) struct IssueRef {
    pub(crate) number: u32,
    pub(crate) title: &'static str,
    pub(crate) url: String,
}

impl IssueRef {
    pub(crate) fn new(number: u32, title: &'static str) -> Self {
        Self {
            number,
            title,
            url: format!("https://github.com/alabsystems/clean/issues/{number}"),
        }
    }
}
