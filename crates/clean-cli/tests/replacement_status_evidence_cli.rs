// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end smoke for the replacement launch-gate CLI output.
//!
//! The unit tests in `cmd_replacement.rs` cover the in-process report builders
//! and renderers. This smoke keeps one process-boundary check for the canonical
//! `clean replacement ...` commands so the launch gate cannot drift away from
//! the checked-in fallback-denial evidence.

use std::env;
use std::ffi::OsString;
use std::fs;
use std::io::Read;
#[cfg(unix)]
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, ExitStatus, Output, Stdio};
use std::sync::OnceLock;
use std::thread;
use std::time::{Duration, Instant};

use serde_json::Value;

const CLEAN_CLI_BUILD_TIMEOUT: Duration = Duration::from_secs(120);
const CLEAN_CLI_RUN_TIMEOUT: Duration = Duration::from_secs(30);
const CLEAN_TACTIC_PARITY_CLI_RUN_TIMEOUT: Duration = Duration::from_secs(90);
const CLEAN_CLI_SMOKE_BIN_ENV: &str = "CLEAN_CLI_SMOKE_BIN";
const CARGO_CLEAN_BIN_ENV: &str = "CARGO_BIN_EXE_clean";
#[cfg(unix)]
const CLEAN_CLI_TIMEOUT_KILL_GRACE: Duration = Duration::from_secs(2);

fn workspace_root() -> PathBuf {
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    manifest_dir
        .parent()
        .and_then(Path::parent)
        .map(Path::to_path_buf)
        .expect("workspace root should be two parents above CARGO_MANIFEST_DIR")
}

fn run_clean(args: &[&str]) -> Output {
    run_clean_with_timeout(args, CLEAN_CLI_RUN_TIMEOUT)
}

fn run_clean_with_timeout(args: &[&str], timeout: Duration) -> Output {
    let root = workspace_root();
    let binary = clean_binary();
    let mut command = Command::new(binary);
    command.args(args);

    command.current_dir(root).env("CARGO_TERM_COLOR", "never");
    let output = run_with_timeout(command, timeout, format!("clean {:?}", args));
    assert!(
        output.status.success(),
        "clean {:?} failed with status {}\nstdout:\n{}\nstderr:\n{}",
        args,
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    output
}

fn clean_binary() -> PathBuf {
    if let Some(binary) = env::var_os(CLEAN_CLI_SMOKE_BIN_ENV) {
        let binary = PathBuf::from(binary);
        assert!(
            binary.is_file(),
            "{CLEAN_CLI_SMOKE_BIN_ENV} points to {}, but it is not a file",
            binary.display()
        );
        return binary;
    }

    static CLEAN_BINARY: OnceLock<PathBuf> = OnceLock::new();
    CLEAN_BINARY
        .get_or_init(resolve_or_build_clean_binary)
        .clone()
}

fn resolve_or_build_clean_binary() -> PathBuf {
    if let Some(binary) = cargo_provided_clean_binary() {
        return binary;
    }

    build_clean_binary(built_clean_binary_path())
}

fn cargo_provided_clean_binary() -> Option<PathBuf> {
    env::var_os(CARGO_CLEAN_BIN_ENV)
        .map(PathBuf::from)
        .filter(|binary| binary.is_file())
}

fn build_clean_binary(binary: PathBuf) -> PathBuf {
    let root = workspace_root();
    let cargo = env::var_os("CARGO").unwrap_or_else(|| OsString::from("cargo"));
    let mut command = Command::new(cargo);
    command.args(["build", "--quiet", "-p", "clean", "--bin", "clean"]);
    command.current_dir(root).env("CARGO_TERM_COLOR", "never");

    let output = run_with_timeout(
        command,
        CLEAN_CLI_BUILD_TIMEOUT,
        "cargo build -p clean --bin clean".to_string(),
    );
    assert!(
        output.status.success(),
        "cargo build -p clean --bin clean failed with status {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        binary.is_file(),
        "cargo build -p clean --bin clean succeeded, but {} does not exist",
        binary.display()
    );
    binary
}

fn built_clean_binary_path() -> PathBuf {
    let current_exe =
        env::current_exe().expect("replacement status smoke should know its test binary path");
    let exe_dir = current_exe
        .parent()
        .expect("replacement status smoke binary should have a parent directory");
    let profile_dir = if exe_dir.file_name().and_then(|name| name.to_str()) == Some("deps") {
        exe_dir
            .parent()
            .expect("replacement status smoke deps directory should have a parent")
    } else {
        exe_dir
    };
    profile_dir.join(format!("clean{}", env::consts::EXE_SUFFIX))
}

fn run_with_timeout(mut command: Command, timeout: Duration, context: String) -> Output {
    let command_debug = format!("{command:?}");
    command.stdout(Stdio::piped()).stderr(Stdio::piped());
    configure_child_process(&mut command);
    let mut child = command
        .spawn()
        .unwrap_or_else(|err| panic!("failed to run {context}: {err}"));
    let stdout = child
        .stdout
        .take()
        .unwrap_or_else(|| panic!("spawned {context} child should have piped stdout"));
    let stderr = child
        .stderr
        .take()
        .unwrap_or_else(|| panic!("spawned {context} child should have piped stderr"));
    let stdout_reader = read_to_end_thread(stdout);
    let stderr_reader = read_to_end_thread(stderr);
    let started = Instant::now();

    loop {
        if let Some(status) = child
            .try_wait()
            .unwrap_or_else(|err| panic!("failed to poll {context}: {err}"))
        {
            return Output {
                status,
                stdout: join_reader(stdout_reader, "stdout"),
                stderr: join_reader(stderr_reader, "stderr"),
            };
        }

        if started.elapsed() >= timeout {
            let status = terminate_timed_out_child(&mut child, &context);
            let stdout = join_reader(stdout_reader, "stdout");
            let stderr = join_reader(stderr_reader, "stderr");
            panic!(
                "{context} timed out after {}s while running {command_debug}; killed child status {}\nstdout:\n{}\nstderr:\n{}",
                timeout.as_secs(),
                status,
                String::from_utf8_lossy(&stdout),
                String::from_utf8_lossy(&stderr)
            );
        }

        thread::sleep(Duration::from_millis(100));
    }
}

#[cfg(unix)]
fn configure_child_process(command: &mut Command) {
    command.process_group(0);
}

#[cfg(not(unix))]
fn configure_child_process(_command: &mut Command) {}

#[cfg(unix)]
fn terminate_timed_out_child(child: &mut Child, context: &str) -> ExitStatus {
    signal_process_group(child.id(), "-TERM");
    if let Some(status) = wait_for_child_exit(child, CLEAN_CLI_TIMEOUT_KILL_GRACE, context) {
        // Kill the group after the leader exits too: a `cargo run` grandchild
        // may still hold stdout/stderr pipes open and make reader joins hang.
        signal_process_group(child.id(), "-KILL");
        return status;
    }

    signal_process_group(child.id(), "-KILL");
    let _ = child.kill();
    child
        .wait()
        .unwrap_or_else(|err| panic!("failed to wait for timed-out {context}: {err}"))
}

#[cfg(not(unix))]
fn terminate_timed_out_child(child: &mut Child, context: &str) -> ExitStatus {
    let _ = child.kill();
    child
        .wait()
        .unwrap_or_else(|err| panic!("failed to wait for timed-out {context}: {err}"))
}

#[cfg(unix)]
fn wait_for_child_exit(child: &mut Child, timeout: Duration, context: &str) -> Option<ExitStatus> {
    let started = Instant::now();
    loop {
        if let Some(status) = child
            .try_wait()
            .unwrap_or_else(|err| panic!("failed to poll timed-out {context}: {err}"))
        {
            return Some(status);
        }

        if started.elapsed() >= timeout {
            return None;
        }

        thread::sleep(Duration::from_millis(50));
    }
}

#[cfg(unix)]
fn signal_process_group(pid: u32, signal: &str) {
    let process_group = format!("-{pid}");
    let _ = Command::new("kill")
        .args([signal, process_group.as_str()])
        .status();
}

fn read_to_end_thread<R>(mut reader: R) -> thread::JoinHandle<Vec<u8>>
where
    R: Read + Send + 'static,
{
    thread::spawn(move || {
        let mut output = Vec::new();
        let _ = reader.read_to_end(&mut output);
        output
    })
}

fn join_reader(reader: thread::JoinHandle<Vec<u8>>, stream_name: &str) -> Vec<u8> {
    reader
        .join()
        .unwrap_or_else(|_| panic!("failed to join clean {stream_name} reader thread"))
}

fn run_clean_json(args: &[&str]) -> Value {
    parse_clean_json(args, run_clean(args))
}

fn run_clean_json_with_timeout(args: &[&str], timeout: Duration) -> Value {
    parse_clean_json(args, run_clean_with_timeout(args, timeout))
}

fn parse_clean_json(args: &[&str], output: Output) -> Value {
    serde_json::from_slice(&output.stdout).unwrap_or_else(|err| {
        panic!(
            "clean {:?} did not emit JSON: {err}\nstdout:\n{}\nstderr:\n{}",
            args,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    })
}

fn unchecked_decl_totals() -> (u64, u64, u64) {
    let path = workspace_root()
        .join("data")
        .join("unchecked_decl_ratchet.json");
    let artifact: Value = serde_json::from_str(
        &fs::read_to_string(&path)
            .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display())),
    )
    .unwrap_or_else(|err| panic!("failed to parse {}: {err}", path.display()));
    let structural = artifact["add_decl_structural_count"]
        .as_u64()
        .expect("ratchet structural count should be numeric");
    let unchecked = artifact["add_decl_unchecked_count"]
        .as_u64()
        .expect("ratchet unchecked count should be numeric");
    (structural, unchecked, structural + unchecked)
}

fn find_by_id<'a>(array: &'a Value, id: &str) -> &'a Value {
    array
        .as_array()
        .expect("expected JSON array")
        .iter()
        .find(|entry| entry["id"] == id)
        .unwrap_or_else(|| panic!("missing JSON row with id {id}"))
}

fn find_by_field<'a>(array: &'a Value, field: &str, value: &str) -> &'a Value {
    array
        .as_array()
        .expect("expected JSON array")
        .iter()
        .find(|entry| entry[field] == value)
        .unwrap_or_else(|| panic!("missing JSON row with {field}={value}"))
}

#[test]
fn replacement_status_and_trust_core_evidence_cli_report_fallback_denial_totals() {
    // The `clean replacement status` subprocess reads several real
    // artifacts (kernel-soundness-launch-evidence.json, proof-system
    // certification audit md, etc). On machines that carry only the
    // stub bootstrap of those files, the subprocess exits non-zero.
    // Detect that situation and skip the smoke rather than fail.
    let root = workspace_root();
    let audit_md = root.join("reports/2026-04-27-proof-system-verification-audit-issue-state.md");
    if !audit_md.is_file() {
        eprintln!(
            "SKIP: {} not present — replacement status CLI smoke needs real artifacts",
            audit_md.display()
        );
        return;
    }
    let (structural, unchecked, total) = unchecked_decl_totals();
    let expected_summary_prefix = format!(
        "add_decl_structural_count={structural}, add_decl_unchecked_count={unchecked}, total={total}; "
    );

    let status = run_clean_json(&["replacement", "status", "--json"]);
    assert_eq!(status["generated_by"], "clean replacement status");
    assert_eq!(status["launch_ready"], false);
    assert!(status["zero_trust_gates_passed"].is_boolean());
    let status_kernel = find_by_id(&status["zero_trust_gates"], "kernel-soundness");
    assert_eq!(status_kernel["active_debt_count"], 0);
    assert!(matches!(
        status_kernel["status"].as_str(),
        Some("pending_evidence" | "passed")
    ));
    assert!(status_kernel["evidence_summary"]
        .as_str()
        .expect("kernel soundness evidence summary")
        .contains("reports/kernel-soundness-launch-evidence.json"));
    let status_deny_sorry = find_by_id(&status["zero_trust_gates"], "deny-sorry");
    assert_eq!(status_deny_sorry["active_debt_count"], total);
    assert!(status_deny_sorry["evidence_summary"]
        .as_str()
        .expect("deny-sorry evidence summary")
        .starts_with(&expected_summary_prefix));
    if total == 0 {
        assert!(
            status_deny_sorry["status"] == "pending_evidence"
                || status_deny_sorry["status"] == "passed"
        );
    } else {
        assert_eq!(status_deny_sorry["status"], "blocked");
    }
    let status_axiom_audit = find_by_id(&status["zero_trust_gates"], "axiom-audit");
    assert!(status_axiom_audit["evidence_summary"]
        .as_str()
        .expect("axiom-audit evidence summary")
        .contains("reports/axiom-audit-launch-evidence.json"));
    assert!(matches!(
        status_axiom_audit["status"].as_str(),
        Some("blocked" | "pending_evidence" | "passed")
    ));
    let fallback_row = find_by_id(&status["rows"], "fallback-denial");
    assert_eq!(
        fallback_row["gate_command"],
        "./scripts/deny_sorry_gate.sh && clean replacement trust-core-evidence --json"
    );
    assert_eq!(fallback_row["status"], "Green");
    assert_eq!(
        fallback_row["evidence_artifact"],
        "reports/deny-sorry-launch-evidence.json"
    );

    let proof_row = find_by_id(&status["rows"], "proof-system-certification");
    assert_eq!(proof_row["status"], "InProgress");
    assert_eq!(
        proof_row["evidence_artifact"],
        "clean-trust-core-evidence-v1"
    );
    assert!(proof_row["blocker"]
        .as_str()
        .expect("proof-system blocker")
        .contains("proof-system certification remains in progress"));
    let strict_row = find_by_id(&status["rows"], "strict-reconstruction");
    assert_eq!(strict_row["status"], "Green");
    assert_eq!(
        strict_row["evidence_artifact"],
        "reports/strict-solver-fragment-dashboard.json"
    );
    assert_eq!(status["proof_system_certification"]["status"], "InProgress");
    assert_eq!(
        status["proof_system_certification"]["zero_trust_gates_passed"],
        true
    );
    assert_eq!(
        status["proof_system_certification"]["blocking_verification_audit_lanes"],
        4
    );
    assert_eq!(
        status["proof_system_certification"]["blocking_replay_parity_rows"],
        2
    );

    let evidence = run_clean_json(&["replacement", "trust-core-evidence", "--json"]);
    assert_eq!(
        evidence["generated_by"],
        "clean replacement trust-core-evidence"
    );
    assert_eq!(evidence["launch_ready"], false);
    let ratchet = &evidence["fallback_denial"]["unchecked_decl_ratchet"];
    assert_eq!(ratchet["add_decl_structural_count"], structural);
    assert_eq!(ratchet["add_decl_unchecked_count"], unchecked);
    assert_eq!(
        evidence["fallback_denial"]["launch_evidence_path"],
        "reports/deny-sorry-launch-evidence.json"
    );
    assert_eq!(
        evidence["kernel_differential"]["launch_evidence_path"],
        "reports/kernel-soundness-launch-evidence.json"
    );
    assert!(matches!(
        evidence["kernel_differential"]["launch_evidence_status"].as_str(),
        Some("passed" | "missing" | "stale")
    ));
    assert!(matches!(
        evidence["fallback_denial"]["launch_evidence_status"].as_str(),
        Some("passed" | "missing" | "stale")
    ));
    assert_eq!(
        evidence["axiom_audit"]["launch_evidence_path"],
        "reports/axiom-audit-launch-evidence.json"
    );
    assert!(matches!(
        evidence["axiom_audit"]["launch_evidence_status"].as_str(),
        Some("passed" | "missing" | "stale")
    ));
    assert_eq!(
        evidence["proof_system_certification"]["status"],
        "InProgress"
    );
    assert_eq!(
        evidence["proof_system_certification"]["verification_audit_path"],
        "docs/VERIFICATION_AUDIT.md"
    );
    assert_eq!(
        evidence["proof_system_certification"]["blocking_verification_audit_lanes"],
        4
    );
    assert_eq!(
        evidence["proof_system_certification"]["blocking_replay_parity_rows"],
        2
    );
    assert!(evidence["proof_system_certification"]["evidence_summary"]
        .as_str()
        .expect("proof-system evidence summary")
        .contains("replay_parity_blockers=2"));
    let evidence_kernel = find_by_id(&evidence["zero_trust_gates"], "kernel-soundness");
    assert_eq!(evidence_kernel["active_debt_count"], 0);
    assert!(evidence_kernel["evidence_summary"]
        .as_str()
        .expect("kernel soundness evidence summary")
        .contains("reports/kernel-soundness-launch-evidence.json"));
    let evidence_deny_sorry = find_by_id(&evidence["zero_trust_gates"], "deny-sorry");
    assert_eq!(evidence_deny_sorry["active_debt_count"], total);
    assert!(evidence_deny_sorry["evidence_summary"]
        .as_str()
        .expect("deny-sorry evidence summary")
        .starts_with(&expected_summary_prefix));
    let evidence_axiom_audit = find_by_id(&evidence["zero_trust_gates"], "axiom-audit");
    assert!(evidence_axiom_audit["evidence_summary"]
        .as_str()
        .expect("axiom-audit evidence summary")
        .contains("reports/axiom-audit-launch-evidence.json"));
}

#[test]
fn tactic_parity_cli_reports_arithmetic_and_strict_zero_trust_evidence() {
    let root = workspace_root();
    let audit_md = root.join("reports/2026-04-27-proof-system-verification-audit-issue-state.md");
    if !audit_md.is_file() {
        eprintln!(
            "SKIP: {} not present — tactic-parity CLI smoke needs real artifacts",
            audit_md.display()
        );
        return;
    }
    let report = run_clean_json_with_timeout(
        &["replacement", "tactic-parity", "--json"],
        CLEAN_TACTIC_PARITY_CLI_RUN_TIMEOUT,
    );

    assert_eq!(report["generated_by"], "clean replacement tactic-parity");
    assert_eq!(report["launch_ready"], false);
    assert_eq!(report["tactic_counts"]["ProofCarrying"], 8);
    assert_eq!(report["tactic_counts"]["EvidenceBackedPartial"], 1);
    assert_eq!(report["tactic_counts"]["Lean4ParityGap"], 1);
    for tactic in ["mathverse", "linarith", "nlinarith", "exact"] {
        let row = find_by_field(&report["tactics"], "tactic", tactic);
        assert_eq!(row["lean4_parity_status"], "ProofCarrying");
        assert_eq!(row["trusted_arith_count"], 0);
        assert_eq!(row["trusted_ay_count"], 0);
    }
    assert_eq!(
        find_by_field(&report["tactics"], "tactic", "aesop")["lean4_parity_status"],
        "EvidenceBackedPartial"
    );
    assert_eq!(
        find_by_field(&report["tactics"], "tactic", "grind")["lean4_parity_status"],
        "Lean4ParityGap"
    );

    let count_artifact = &report["lean4_vs_clean_tactic_counts"];
    assert_eq!(
        count_artifact["schema_version"],
        "clean-tactic-parity-count-artifact-v1"
    );
    assert_eq!(
        count_artifact["source_artifact"],
        "reports/tactic-parity-counts.json"
    );
    assert_eq!(count_artifact["summary"]["tactic_row_count"], 8);
    assert_eq!(count_artifact["summary"]["lean4_total"], 56);
    assert_eq!(count_artifact["summary"]["clean_total"], 49);
    assert_eq!(count_artifact["summary"]["clean_gap_total"], 7);
    assert_eq!(
        find_by_field(&count_artifact["tactics"], "tactic", "aesop")["status"],
        "EvidenceBackedPartial"
    );
    assert_eq!(
        find_by_field(&count_artifact["tactics"], "tactic", "aesop")["clean_gap_count"],
        2
    );
    let aesop_blocker =
        &find_by_field(&count_artifact["tactics"], "tactic", "aesop")["remaining_blocker"];
    assert_eq!(aesop_blocker["fail_closed"], true);
    assert_eq!(aesop_blocker["gap_count"], 2);
    assert_eq!(
        aesop_blocker["representative_gap_cases"]
            .as_array()
            .expect("aesop blocker cases")
            .len(),
        2
    );
    assert!(aesop_blocker["representative_gap_cases"]
        .as_array()
        .expect("aesop blocker cases")
        .iter()
        .any(|case| case
            .as_str()
            .expect("aesop blocker case")
            .contains("rule-set option parity")));
    assert!(aesop_blocker["gate_required_to_clear"]
        .as_str()
        .expect("aesop clear gate")
        .contains("clean_gap_count = 0"));
    assert_eq!(
        find_by_field(&count_artifact["tactics"], "tactic", "grind")["status"],
        "Lean4ParityGap"
    );
    assert_eq!(
        find_by_field(&count_artifact["tactics"], "tactic", "grind")["clean_gap_count"],
        5
    );
    let grind_blocker =
        &find_by_field(&count_artifact["tactics"], "tactic", "grind")["remaining_blocker"];
    assert_eq!(grind_blocker["fail_closed"], true);
    assert_eq!(grind_blocker["gap_count"], 5);
    assert_eq!(
        grind_blocker["representative_gap_cases"]
            .as_array()
            .expect("grind blocker cases")
            .len(),
        5
    );
    assert!(grind_blocker["gate_required_to_clear"]
        .as_str()
        .expect("grind clear gate")
        .contains("clean_gap_count = 0"));

    let strict_qf_uf = find_by_field(
        &report["strict_reconstruction"],
        "fragment",
        "ay_verify_strict_qf_uf",
    );
    assert_eq!(report["reconstruction_counts"]["SupportedZeroTrust"], 2);
    assert_eq!(strict_qf_uf["status"], "SupportedZeroTrust");
    assert_eq!(strict_qf_uf["direct_trust_rejected"], true);
    assert_eq!(strict_qf_uf["zero_trust_recovery"], true);
    assert!(strict_qf_uf["evidence"]
        .as_str()
        .expect("strict QF_UF evidence")
        .contains("--features ay-smt"));

    let strict_dashboard = &report["strict_solver_fragment_dashboard"];
    assert_eq!(
        strict_dashboard["schema_version"],
        "clean-strict-solver-fragment-dashboard-v1"
    );
    assert_eq!(
        strict_dashboard["source_artifact"],
        "reports/strict-solver-fragment-dashboard.json"
    );
    assert_eq!(strict_dashboard["row_count"], 10);
    assert_eq!(strict_dashboard["supported_zero_trust_rows"], 3);
    assert_eq!(strict_dashboard["unsupported_reject_and_fallback_rows"], 7);
    assert_eq!(strict_dashboard["direct_trust_rejected_rows"], 10);
    assert_eq!(strict_dashboard["zero_trust_recovery_rows"], 1);
    assert_eq!(strict_dashboard["residual_trust_acceptance_rows"], 0);
    assert_eq!(
        strict_dashboard["strict_reconstruction_gate"]["passed"],
        true
    );
    assert_eq!(
        strict_dashboard["strict_reconstruction_gate"]["row_count"]["observed"],
        10
    );
    assert_eq!(
        strict_dashboard["strict_reconstruction_gate"]["supported_zero_trust_rows"]["observed"],
        3
    );
    assert_eq!(
        strict_dashboard["strict_reconstruction_gate"]["zero_trust_recovery_rows"]["observed"],
        1
    );
    assert_eq!(
        strict_dashboard["strict_reconstruction_gate"]["residual_trust_acceptance_rows"]
            ["observed"],
        0
    );
    assert_eq!(
        strict_dashboard["rows"]
            .as_array()
            .expect("strict dashboard rows")
            .len(),
        10
    );

    assert_eq!(
        find_by_field(
            &report["strict_reconstruction"],
            "fragment",
            "strict_solver_fragment_dashboard"
        )["status"],
        "SupportedZeroTrust"
    );
}
