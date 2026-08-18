// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Launch evidence generation and lint/aggregate validation.

use super::*;

pub(crate) fn proof_system_verification_audit_lanes(
    audit_source: &str,
    issue_state_source: &str,
) -> Result<Vec<VerificationAuditLaneEvidence>, ReplacementError> {
    for marker in [
        "Verified at (UTC):",
        "Verification method: `gh issue view",
        "Repository: alabsystems/clean",
    ] {
        if !issue_state_source.contains(marker) {
            return Err(ReplacementError::StaleTrustCoreArtifact {
                message: format!(
                    "{VERIFICATION_AUDIT_ISSUE_STATE_EVIDENCE_PATH} missing live verification marker `{marker}`"
                ),
            });
        }
    }

    let mut lanes = Vec::with_capacity(PROOF_SYSTEM_VERIFICATION_AUDIT_LANES.len());
    for expected in PROOF_SYSTEM_VERIFICATION_AUDIT_LANES {
        let audit_marker = format!("| #{} | {}", expected.issue, expected.title);
        if !audit_source.contains(&audit_marker) {
            return Err(ReplacementError::StaleTrustCoreArtifact {
                message: format!(
                    "{VERIFICATION_AUDIT_PATH} missing proof-system audit lane `{audit_marker}`"
                ),
            });
        }

        let open_marker = format!("| #{} | {} | OPEN |", expected.issue, expected.title);
        let closed_marker = format!("| #{} | {} | CLOSED |", expected.issue, expected.title);
        let blocked_marker = format!(
            "| #{} | {} | BLOCKED_VERIFICATION |",
            expected.issue, expected.title
        );
        let (state, blocks_certification) = if issue_state_source.contains(&open_marker) {
            ("open", true)
        } else if issue_state_source.contains(&closed_marker) {
            ("closed", false)
        } else if issue_state_source.contains(&blocked_marker) {
            ("blocked_verification", true)
        } else {
            return Err(ReplacementError::StaleTrustCoreArtifact {
                message: format!(
                    "{VERIFICATION_AUDIT_ISSUE_STATE_EVIDENCE_PATH} missing live issue-state row for #{} `{}`",
                    expected.issue, expected.title
                ),
            });
        };

        if blocks_certification {
            lanes.push(VerificationAuditLaneEvidence {
                issue: IssueRef::new(expected.issue, expected.title),
                audit_path: VERIFICATION_AUDIT_ISSUE_STATE_EVIDENCE_PATH,
                state,
                closure_evidence_gate: expected.closure_evidence_gate,
                blocks_certification,
            });
        }
    }
    Ok(lanes)
}

pub(crate) fn proof_system_replay_parity_rows(
    replacement_rows: &[ReplacementRow],
) -> Result<Vec<ProofSystemReplayParityRow>, ReplacementError> {
    let mut rows = Vec::with_capacity(PROOF_SYSTEM_REPLAY_PARITY_ROW_IDS.len());
    for expected_id in PROOF_SYSTEM_REPLAY_PARITY_ROW_IDS {
        let Some(row) = replacement_rows.iter().find(|row| row.id == *expected_id) else {
            return Err(ReplacementError::StaleTrustCoreArtifact {
                message: format!("missing proof-system replay/parity row `{expected_id}`"),
            });
        };
        rows.push(ProofSystemReplayParityRow {
            row_id: row.id,
            issue: row.issue.clone(),
            status: row.status,
            evidence_artifact: row.evidence_artifact,
            gate_command: row.gate_command,
            blocker: row.blocker,
            blocks_certification: row.status != ReplacementStatus::Green,
        });
    }
    Ok(rows)
}

/// Refuse to write launch evidence from a binary that is not built at HEAD.
///
/// This exists because it actually happened: a `cargo build --locked` failed
/// (sibling `[patch]` path-dependency drift dirties `Cargo.lock`) while its
/// nonzero exit was swallowed by a pipe, so `target/release/clean` stayed
/// ELEVEN DAYS stale and was used to "measure HEAD". Every gate verdict it
/// produced described code that was not in the tree, and nothing detected it.
///
/// `CLEAN_BUILD_GIT_SHA` is stamped by `build.rs`, which already re-runs when
/// HEAD or the checked-out ref moves, so a binary built at another commit is
/// distinguishable at runtime. Uncertainty fails closed: a missing stamp, an
/// absent `git`, or an unreadable HEAD all refuse rather than assume fresh.
///
/// Tree dirtiness is deliberately NOT fatal here. This repository is routinely
/// shared with a co-tenant whose uncommitted files would then block every gate
/// run, and a gate that cannot be run in practice gets worked around instead of
/// respected. Commit mismatch is the failure that actually produced bad
/// measurements; dirtiness is reported by the caller-facing message.
pub(crate) fn validate_binary_matches_head() -> Result<(), ReplacementError> {
    build_provenance_verdict(
        option_env!("CLEAN_BUILD_GIT_SHA"),
        git_stdout(&["rev-parse", "HEAD"]).as_deref(),
    )
    .map_err(|message| ReplacementError::StaleTrustCoreArtifact { message })
}

/// The provenance decision, separated from how its two inputs are obtained.
///
/// Kept pure so it can be tested exhaustively: asserting on the real
/// `validate_binary_matches_head` would be flaky, since the test binary's own
/// stamp goes stale the moment HEAD moves after it was compiled.
pub(crate) fn build_provenance_verdict(
    built_at: Option<&str>,
    head: Option<&str>,
) -> Result<(), String> {
    let Some(built_at) = built_at else {
        return Err(
            "this binary carries no CLEAN_BUILD_GIT_SHA stamp, so it cannot be shown \
                    to match HEAD; rebuild with `cargo build -p clean --bin clean`"
                .to_string(),
        );
    };
    if built_at == "unknown" {
        return Err(
            "this binary was built without git provenance (CLEAN_BUILD_GIT_SHA=unknown); \
             rebuild inside the git checkout before generating launch evidence"
                .to_string(),
        );
    }
    let Some(head) = head else {
        return Err(
            "cannot read `git rev-parse HEAD` to confirm this binary is current; \
             launch evidence must be attributable to a commit"
                .to_string(),
        );
    };
    if built_at == head {
        return Ok(());
    }
    Err(format!(
        "this binary was built at {built_at} but HEAD is {head}; it would describe code \
         that is not in the tree. Rebuild with `cargo build -p clean --bin clean` and \
         re-run. (A stale binary once went undetected for 11 days.)"
    ))
}

/// Run `git <args>`, returning trimmed stdout on a clean exit.
fn git_stdout(args: &[&str]) -> Option<String> {
    let repo_root = repo_artifact_path("Cargo.toml")
        .parent()
        .map(Path::to_path_buf)
        .filter(|path| !path.as_os_str().is_empty())
        .unwrap_or_else(|| PathBuf::from("."));
    let out = Command::new("git")
        .args(args)
        .current_dir(&repo_root)
        .output()
        .ok()?;
    if !out.status.success() {
        return None;
    }
    let text = String::from_utf8_lossy(&out.stdout).trim().to_string();
    (!text.is_empty()).then_some(text)
}

pub(crate) fn validate_source_artifacts(paths: &[&'static str]) -> Result<(), ReplacementError> {
    for path in paths {
        read_repo_artifact(path)?;
    }
    Ok(())
}

/// Runs one gate lane (kernel-soundness or DENY_SORRY) and returns its
/// combined stdout+stderr.
///
/// Injectable so tests can drive the lane-verdict logic without spawning a
/// nested `cargo` (which would deadlock on the build lock).
pub(crate) type KernelSoundnessLaneRunner<'a> =
    &'a dyn Fn(&[&'static str]) -> Result<String, String>;

/// Execute a lane command from the repository root, capturing both streams.
///
/// The elaborator soundness gate writes its `soundness_gate: PASS` marker to
/// stderr, so stdout alone is not enough; this mirrors the `2>&1` redirection
/// in `scripts/kernel_soundness_gate.sh`.
pub(crate) fn run_kernel_soundness_lane_command(argv: &[&'static str]) -> Result<String, String> {
    let Some((program, args)) = argv.split_first() else {
        return Err("lane command is empty".to_string());
    };
    let repo_root = repo_artifact_path("Cargo.toml")
        .parent()
        .map(Path::to_path_buf)
        .filter(|path| !path.as_os_str().is_empty())
        .unwrap_or_else(|| PathBuf::from("."));
    let output = Command::new(program)
        .args(args)
        .current_dir(&repo_root)
        .output()
        .map_err(|error| format!("failed to spawn `{}`: {error}", argv.join(" ")))?;
    let mut combined = String::from_utf8_lossy(&output.stdout).into_owned();
    combined.push_str(&String::from_utf8_lossy(&output.stderr));
    if output.status.success() {
        Ok(combined)
    } else {
        Err(format!(
            "`{}` exited with {}: {combined}",
            argv.join(" "),
            output.status
        ))
    }
}

/// True when libtest output reports exactly `expected` tests, all passing.
fn output_reports_passing_tests(output: &str, expected: u32) -> bool {
    let singular = format!("running {expected} test");
    let plural = format!("{singular}s");
    let ran_expected = output
        .lines()
        .any(|line| line.trim_end() == singular || line.trim_end() == plural);
    let all_passed = output.contains(&format!("test result: ok. {expected} passed; 0 failed"));
    ran_expected && all_passed
}

/// Decide one lane's verdict by executing it. Fails closed on any mismatch.
fn evaluate_kernel_soundness_lane(
    lane: &KernelSoundnessLaneExpectation,
    runner: KernelSoundnessLaneRunner<'_>,
) -> Result<KernelSoundnessLaunchLaneEvidence, ReplacementError> {
    let (matched_expected_count, matched_expected_output) = match lane.command {
        // The preflight lane runs in-process; reaching here means
        // `validate_kernel_differential_artifacts` already returned Ok.
        None => (true, true),
        Some(command) => {
            let output =
                runner(command).map_err(|message| ReplacementError::StaleTrustCoreArtifact {
                    message: format!("kernel soundness lane `{}` failed: {message}", lane.id),
                })?;
            (
                lane.expected_tests
                    .is_none_or(|expected| output_reports_passing_tests(&output, expected)),
                lane.expected_output
                    .is_none_or(|expected| output.contains(expected)),
            )
        }
    };

    if !matched_expected_count || !matched_expected_output {
        return Err(ReplacementError::StaleTrustCoreArtifact {
            message: format!(
                "kernel soundness lane `{}` ran but did not match its expectation \
                 (matched_expected_count={matched_expected_count}, \
                 matched_expected_output={matched_expected_output})",
                lane.id
            ),
        });
    }

    Ok(KernelSoundnessLaunchLaneEvidence {
        id: lane.id.to_string(),
        expected_tests: lane.expected_tests,
        expected_output: lane.expected_output.map(str::to_string),
        matched_expected_count,
        matched_expected_output,
        status: "passed".to_string(),
    })
}

pub(crate) fn generate_kernel_soundness_launch_evidence(
    generated_at: &str,
) -> Result<KernelSoundnessLaunchEvidenceArtifact, ReplacementError> {
    generate_kernel_soundness_launch_evidence_with(generated_at, &run_kernel_soundness_lane_command)
}

pub(crate) fn generate_kernel_soundness_launch_evidence_with(
    generated_at: &str,
    runner: KernelSoundnessLaneRunner<'_>,
) -> Result<KernelSoundnessLaunchEvidenceArtifact, ReplacementError> {
    validate_binary_matches_head()?;
    let baseline = load_lean4_baseline()?;
    let expressions_source = read_repo_artifact(LEAN4_EXPRESSIONS_PATH)?;
    let expressions = active_expressions(&expressions_source);
    let expressions_sha256 = sha256_expressions(&expressions);
    validate_kernel_differential_artifacts(&baseline, expressions.len(), &expressions_sha256)?;

    let mut source_sha256 = BTreeMap::new();
    for path in [
        TRUST_CORE_RUST_SOURCE_PATH,
        LEAN4_BASELINE_PATH,
        LEAN4_EXPRESSIONS_PATH,
    ] {
        source_sha256.insert(path.to_string(), sha256_repo_artifact(path)?);
    }
    source_sha256.insert(
        TRUST_CORE_RUST_MODULE_TREE_KEY.to_string(),
        sha256_repo_module_tree(TRUST_CORE_RUST_MODULE_DIR)?,
    );

    let artifact = KernelSoundnessLaunchEvidenceArtifact {
        schema_version: KERNEL_SOUNDNESS_LAUNCH_EVIDENCE_SCHEMA_VERSION.to_string(),
        generated_by: KERNEL_SOUNDNESS_RUST_GATE_COMMAND.to_string(),
        generated_at: generated_at.to_string(),
        gate_command: KERNEL_SOUNDNESS_RUST_GATE_COMMAND.to_string(),
        status: "passed".to_string(),
        summary: KernelSoundnessLaunchEvidenceSummary {
            expected_steps: KERNEL_SOUNDNESS_EXPECTED_STEPS,
            steps: KERNEL_SOUNDNESS_EXPECTED_STEPS,
            passed: KERNEL_SOUNDNESS_EXPECTED_STEPS,
            failed: 0,
        },
        kernel_differential: KernelSoundnessLaunchDifferentialEvidence {
            baseline_path: LEAN4_BASELINE_PATH.to_string(),
            expressions_path: LEAN4_EXPRESSIONS_PATH.to_string(),
            baseline_schema_version: baseline.schema_version,
            normalization_version: baseline.normalization_version,
            baseline_cases: baseline.cases.len(),
            expression_count: expressions.len(),
            expressions_sha256,
            baseline_sha256: sha256_repo_artifact(LEAN4_BASELINE_PATH)?,
            expressions_file_sha256: sha256_repo_artifact(LEAN4_EXPRESSIONS_PATH)?,
        },
        source_sha256,
        lanes: KERNEL_SOUNDNESS_EXPECTED_LANES
            .iter()
            .map(|lane| evaluate_kernel_soundness_lane(lane, runner))
            .collect::<Result<Vec<_>, _>>()?,
    };
    validate_kernel_soundness_launch_evidence(
        &artifact,
        &baseline,
        artifact.kernel_differential.expression_count,
        &artifact.kernel_differential.expressions_sha256,
    )
    .map_err(|message| ReplacementError::StaleTrustCoreArtifact { message })?;
    Ok(artifact)
}

/// Decide one DENY_SORRY lane's verdict by executing it. Fails closed on any
/// mismatch: an exit-0 run that did not report the expected libtest count is
/// not evidence (the exact shape a filter typo produces).
pub(crate) fn evaluate_deny_sorry_lane(
    lane: &DenySorryLaneExpectation,
    runner: KernelSoundnessLaneRunner<'_>,
) -> Result<DenySorryLaunchLaneEvidence, ReplacementError> {
    let matched_expected_count = match lane.command {
        // The lint and ratchet lanes run in-process before the lane loop;
        // reaching here means validate_sorry_bypass_lint and
        // validate_unchecked_decl_ratchet already returned Ok.
        None => true,
        Some(command) => {
            let output =
                runner(command).map_err(|message| ReplacementError::StaleTrustCoreArtifact {
                    message: format!("DENY_SORRY lane `{}` failed: {message}", lane.id),
                })?;
            lane.expected_tests
                .is_none_or(|expected| output_reports_passing_tests(&output, expected))
        }
    };

    if !matched_expected_count {
        return Err(ReplacementError::StaleTrustCoreArtifact {
            message: format!(
                "DENY_SORRY lane `{}` ran but did not match its expectation \
                 (matched_expected_count=false)",
                lane.id
            ),
        });
    }

    Ok(DenySorryLaunchLaneEvidence {
        id: lane.id.to_string(),
        expected_tests: lane.expected_tests,
        matched_expected_count,
        status: "passed".to_string(),
    })
}

pub(crate) fn generate_deny_sorry_launch_evidence(
    generated_at: &str,
) -> Result<DenySorryLaunchEvidenceArtifact, ReplacementError> {
    generate_deny_sorry_launch_evidence_with(generated_at, &run_kernel_soundness_lane_command)
}

pub(crate) fn generate_deny_sorry_launch_evidence_with(
    generated_at: &str,
    runner: KernelSoundnessLaneRunner<'_>,
) -> Result<DenySorryLaunchEvidenceArtifact, ReplacementError> {
    validate_binary_matches_head()?;
    validate_sorry_bypass_lint()?;
    let ratchet = load_unchecked_decl_ratchet()?;
    validate_unchecked_decl_ratchet(&ratchet)?;
    // Fail fast before spawning any cargo lane: an open ratchet can never
    // yield passing DENY_SORRY evidence (validate_deny_sorry_launch_evidence
    // re-checks this on the finished artifact), so refuse before the
    // expensive lanes rather than after them. Same message either way.
    if ratchet.add_decl_structural_count != 0 || ratchet.add_decl_unchecked_count != 0 {
        return Err(ReplacementError::StaleTrustCoreArtifact {
            message: format!(
                "current ratchet is not closed at 0/0: structural={}, unchecked={}",
                ratchet.add_decl_structural_count, ratchet.add_decl_unchecked_count
            ),
        });
    }

    let mut source_sha256 = BTreeMap::new();
    for path in [TRUST_CORE_RUST_SOURCE_PATH, UNCHECKED_DECL_RATCHET_PATH] {
        source_sha256.insert(path.to_string(), sha256_repo_artifact(path)?);
    }
    source_sha256.insert(
        TRUST_CORE_RUST_MODULE_TREE_KEY.to_string(),
        sha256_repo_module_tree(TRUST_CORE_RUST_MODULE_DIR)?,
    );

    let artifact = DenySorryLaunchEvidenceArtifact {
        schema_version: DENY_SORRY_LAUNCH_EVIDENCE_SCHEMA_VERSION.to_string(),
        generated_by: DENY_SORRY_RUST_GATE_COMMAND.to_string(),
        generated_at: generated_at.to_string(),
        gate_command: DENY_SORRY_RUST_GATE_COMMAND.to_string(),
        status: "passed".to_string(),
        summary: DenySorryLaunchEvidenceSummary {
            expected_steps: DENY_SORRY_EXPECTED_STEPS,
            steps: DENY_SORRY_EXPECTED_STEPS,
            passed: DENY_SORRY_EXPECTED_STEPS,
            failed: 0,
        },
        ratchet: DenySorryLaunchRatchetEvidence {
            path: UNCHECKED_DECL_RATCHET_PATH.to_string(),
            add_decl_structural_count: ratchet.add_decl_structural_count,
            add_decl_unchecked_count: ratchet.add_decl_unchecked_count,
            sha256: sha256_repo_artifact(UNCHECKED_DECL_RATCHET_PATH)?,
        },
        source_sha256,
        lanes: DENY_SORRY_EXPECTED_LANES
            .iter()
            .map(|lane| evaluate_deny_sorry_lane(lane, runner))
            .collect::<Result<Vec<_>, _>>()?,
    };
    validate_deny_sorry_launch_evidence(&artifact, &ratchet)
        .map_err(|message| ReplacementError::StaleTrustCoreArtifact { message })?;
    Ok(artifact)
}

pub(crate) fn write_kernel_soundness_launch_evidence(
    args: &TrustCoreEvidenceArgs,
    artifact: &KernelSoundnessLaunchEvidenceArtifact,
) -> Result<(), ReplacementError> {
    write_generated_launch_evidence(
        args.evidence.as_deref(),
        args.json,
        "kernel soundness launch evidence",
        artifact,
    )
}

pub(crate) fn write_deny_sorry_launch_evidence(
    args: &TrustCoreEvidenceArgs,
    artifact: &DenySorryLaunchEvidenceArtifact,
) -> Result<(), ReplacementError> {
    write_generated_launch_evidence(
        args.evidence.as_deref(),
        args.json,
        "DENY_SORRY launch evidence",
        artifact,
    )
}

pub(crate) fn write_generated_launch_evidence<T: Serialize>(
    evidence_path: Option<&Path>,
    json: bool,
    label: &str,
    artifact: &T,
) -> Result<(), ReplacementError> {
    let rendered =
        serde_json::to_string_pretty(artifact).map_err(ReplacementError::Serialize)? + "\n";
    if let Some(path) = evidence_path {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(path, &rendered)?;
    }

    let stdout = io::stdout();
    let mut out = stdout.lock();
    if json {
        write!(out, "{rendered}")?;
    } else if let Some(path) = evidence_path {
        writeln!(out, "Wrote {label}: {}", path.display())?;
    } else {
        writeln!(out, "{label}: passed")?;
    }
    Ok(())
}

pub(crate) fn validate_axiom_audit_aggregates() -> Result<(), ReplacementError> {
    let source = read_repo_artifact(AXIOM_AUDIT_PATH)?;
    let value: serde_json::Value =
        serde_json::from_str(&source).map_err(|source| ReplacementError::ParseArtifact {
            path: AXIOM_AUDIT_PATH,
            source,
        })?;
    let recomputed = compute_axiom_audit_aggregates(&value)?;
    let stored = [
        ("total_domain_axioms", recomputed.total_domain_axioms),
        ("total_theorems", recomputed.total_theorems),
        ("constructive_theorems", recomputed.constructive_theorems),
        ("total_all_axioms", recomputed.total_all_axioms),
    ];
    let mut mismatches = Vec::new();
    for (key, expected) in stored {
        match value.get(key).and_then(serde_json::Value::as_u64) {
            Some(actual) if actual == u64::from(expected) => {}
            Some(actual) => {
                mismatches.push(format!("{key}: stored {actual}, recomputed {expected}"))
            }
            None => mismatches.push(format!(
                "{key}: missing or non-integer, recomputed {expected}"
            )),
        }
    }
    if mismatches.is_empty() {
        Ok(())
    } else {
        Err(ReplacementError::StaleTrustCoreArtifact {
            message: format!(
                "{AXIOM_AUDIT_PATH} aggregates are stale or invalid: {}",
                mismatches.join("; ")
            ),
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct AxiomAuditAggregates {
    pub(crate) total_domain_axioms: u32,
    pub(crate) total_theorems: u32,
    pub(crate) constructive_theorems: u32,
    pub(crate) total_all_axioms: u32,
}

pub(crate) fn compute_axiom_audit_aggregates(
    value: &serde_json::Value,
) -> Result<AxiomAuditAggregates, ReplacementError> {
    let conjectures = value
        .get("conjectures")
        .and_then(serde_json::Value::as_object)
        .ok_or_else(|| ReplacementError::StaleTrustCoreArtifact {
            message: format!("{AXIOM_AUDIT_PATH}: missing or non-object conjectures field"),
        })?;
    let mut total_domain_axioms = 0u32;
    let mut total_theorems = 0u32;
    let mut constructive_theorems = 0u32;
    for (cid, entry) in conjectures {
        let entry = entry
            .as_object()
            .ok_or_else(|| ReplacementError::StaleTrustCoreArtifact {
                message: format!("{AXIOM_AUDIT_PATH}: conjectures.{cid} is not an object"),
            })?;
        let axioms = axiom_audit_count(entry.get("axioms"), cid, "axioms")?;
        let theorems = axiom_audit_count(entry.get("theorems"), cid, "theorems")?;
        total_domain_axioms = total_domain_axioms.saturating_add(axioms);
        total_theorems = total_theorems.saturating_add(theorems);
        if entry
            .get("constructive")
            .and_then(serde_json::Value::as_bool)
            == Some(true)
        {
            constructive_theorems = constructive_theorems.saturating_add(theorems);
        }
    }
    let total_all_axioms =
        total_domain_axioms.saturating_add(compute_non_conjecture_axiom_total(value)?);
    Ok(AxiomAuditAggregates {
        total_domain_axioms,
        total_theorems,
        constructive_theorems,
        total_all_axioms,
    })
}

pub(crate) fn axiom_audit_count(
    value: Option<&serde_json::Value>,
    cid: &str,
    field: &str,
) -> Result<u32, ReplacementError> {
    match value {
        Some(serde_json::Value::Number(number)) => number
            .as_u64()
            .and_then(|raw| u32::try_from(raw).ok())
            .ok_or_else(|| ReplacementError::StaleTrustCoreArtifact {
                message: format!(
                    "{AXIOM_AUDIT_PATH}: conjectures.{cid}.{field} must be a non-negative u32"
                ),
            }),
        Some(serde_json::Value::Array(values)) => {
            u32::try_from(values.len()).map_err(|_| ReplacementError::StaleTrustCoreArtifact {
                message: format!("{AXIOM_AUDIT_PATH}: conjectures.{cid}.{field} list is too large"),
            })
        }
        None => Ok(0),
        _ => Err(ReplacementError::StaleTrustCoreArtifact {
            message: format!(
                "{AXIOM_AUDIT_PATH}: conjectures.{cid}.{field} must be an integer or list"
            ),
        }),
    }
}

pub(crate) fn compute_non_conjecture_axiom_total(
    value: &serde_json::Value,
) -> Result<u32, ReplacementError> {
    let Some(block) = value.get("non_conjecture_axioms") else {
        return Ok(0);
    };
    let per_prefix = block
        .get("per_prefix")
        .and_then(serde_json::Value::as_object)
        .ok_or_else(|| ReplacementError::StaleTrustCoreArtifact {
            message: format!(
                "{AXIOM_AUDIT_PATH}: non_conjecture_axioms.per_prefix must be an object"
            ),
        })?;
    let mut total = 0u32;
    for (prefix, entry) in per_prefix {
        let count = entry
            .get("count")
            .and_then(serde_json::Value::as_u64)
            .and_then(|raw| u32::try_from(raw).ok())
            .ok_or_else(|| ReplacementError::StaleTrustCoreArtifact {
                message: format!(
                    "{AXIOM_AUDIT_PATH}: non_conjecture_axioms.per_prefix.{prefix}.count must be a non-negative u32"
                ),
            })?;
        total = total.saturating_add(count);
    }
    Ok(total)
}
