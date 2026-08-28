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

/// How a `clean replacement …` subprocess's exit status relates to the report
/// it just printed.
///
/// The helper here used to be a bare `assert!(output.status.success())`, and
/// that is one of the two reasons this smoke could never have passed: `clean
/// replacement status` exits **1** whenever any row or zero-trust gate blocks.
/// That is the launch gate's documented contract, not a failure — the handler's
/// own comment gives the reason: *"a gate that reports `launch_ready: false`
/// and then exits 0 is not a gate: `clean replacement status && echo READY`
/// would print READY."*
///
/// So the contract is expressed against `launch_ready` rather than against a
/// hard-coded number, which is both stronger and stable: the code cannot drift
/// from the report it printed in the same breath.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExitPolicy {
    /// Exit 0 **iff** the report says `launch_ready: true`. Both directions.
    TracksLaunchReady,
    /// One direction only: a nonzero exit must never contradict a
    /// `launch_ready: true` report.
    ///
    /// Deliberately weaker, and not laxity: the strict direction for the
    /// sibling *reporting* commands is owned by `cmd_replacement::tests::part_07`
    /// (`trust_core_evidence_gate_exit_status_tracks_its_own_launch_ready` and
    /// `tactic_parity_gate_exit_status_tracks_its_own_launch_ready`), landed in
    /// 85d80dd69. Restating it here would duplicate that gate rather than add
    /// cover, so this asserts the half that holds no matter which of the two
    /// commands' exit contracts is in force.
    NonZeroOnlyWhenNotReady,
}

fn run_clean_with_timeout(args: &[&str], timeout: Duration) -> Output {
    let root = workspace_root();
    let binary = clean_binary();
    let mut command = Command::new(binary);
    command.args(args);

    command.current_dir(root).env("CARGO_TERM_COLOR", "never");
    run_with_timeout(command, timeout, format!("clean {:?}", args))
}

/// Check the exit status against the report the same run produced.
fn assert_exit_policy(args: &[&str], output: &Output, report: &Value, policy: ExitPolicy) {
    let code = output
        .status
        .code()
        .unwrap_or_else(|| panic!("clean {args:?} was killed by a signal, not an exit code"));
    let launch_ready = report["launch_ready"]
        .as_bool()
        .unwrap_or_else(|| panic!("clean {args:?} emitted no boolean `launch_ready`"));
    let context = || {
        format!(
            "clean {:?} exited {code} with launch_ready={launch_ready}\nstderr:\n{}",
            args,
            String::from_utf8_lossy(&output.stderr)
        )
    };
    match policy {
        ExitPolicy::TracksLaunchReady => assert_eq!(
            code == 0,
            launch_ready,
            "a fail-closed gate must exit 0 exactly when it reports launch_ready; {}",
            context()
        ),
        ExitPolicy::NonZeroOnlyWhenNotReady => assert!(
            code == 0 || !launch_ready,
            "the command exited nonzero while reporting launch_ready=true; {}",
            context()
        ),
    }
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

fn run_clean_json(args: &[&str], policy: ExitPolicy) -> Value {
    run_clean_json_with_timeout(args, CLEAN_CLI_RUN_TIMEOUT, policy)
}

fn run_clean_json_with_timeout(args: &[&str], timeout: Duration, policy: ExitPolicy) -> Value {
    let output = run_clean_with_timeout(args, timeout);
    let report = parse_clean_json(args, &output);
    assert_exit_policy(args, &output, &report, policy);
    report
}

fn parse_clean_json(args: &[&str], output: &Output) -> Value {
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

/// The deny-sorry gate's verdict and its printed blocker must describe the same
/// branch — and the branch must be the G6 CLOSURE of the unchecked-decl
/// ratchet, never its raw count.
///
/// Before 2026-08-26 the two halves of this gate disagreed. `gate_checks.rs`
/// blocked on `add_decl_structural_count + add_decl_unchecked_count != 0`,
/// while the gate command it names (`scripts/deny_sorry_gate.sh`), the minting
/// path and the artifact validator had all moved to G6: closed means every
/// counted bypass is *sanctioned*, at or under its pinned cap, and fully
/// accounted. The checked-in ratchet is closed with exactly one sanctioned
/// occurrence, so the row printed "records remaining structural/unchecked
/// trusted fallback callsites" and **no amount of re-minting the evidence could
/// clear it** — the fail-closed branch that fired was not the branch whose
/// remedy the row advertised.
///
/// This asserts the coupling in both directions, so neither half can drift
/// again without a red test.
fn assert_deny_sorry_verdict_matches_its_blocker(gate: &Value) {
    let status = gate["status"]
        .as_str()
        .expect("deny-sorry gate status should be a string");
    let reason = gate["fail_closed_reason"]
        .as_str()
        .expect("deny-sorry gate fail_closed_reason should be a string");

    match status {
        "blocked" => assert!(
            reason.contains("ratchet is not closed"),
            "deny-sorry is blocked, so its blocker must name the closure failure that fired, \
             not a raw debt count; got: {reason}"
        ),
        "pending_evidence" | "passed" => {
            assert!(
                reason.contains("ratchet is closed"),
                "deny-sorry is {status}, so its blocker must say the ratchet is closed; got: {reason}"
            );
            if status == "pending_evidence" {
                assert!(
                    reason.contains("fresh launch-gate evidence artifact"),
                    "a closed ratchet awaiting evidence must advertise the remedy that can \
                     actually clear it; got: {reason}"
                );
            }
        }
        other => panic!("unexpected deny-sorry gate status {other:?}"),
    }

    // The state this checkout measures: the ratchet is CLOSED (one sanctioned,
    // capped `add_decl_unchecked` occurrence — the Metamath PASS-1 proof-drop),
    // so the gate must be clearable by evidence. A genuinely unsanctioned
    // bypass is *supposed* to turn this red.
    assert_ne!(
        status, "blocked",
        "the checked-in unchecked-decl ratchet is closed under G6, so deny-sorry must be \
         clearable by fresh evidence rather than blocked; blocker was: {reason}"
    );
}

/// The certification verdict must follow from the gate verdicts printed beside
/// it, not from a pinned expectation.
///
/// `zero_trust_gates_passed` is "every launch-required zero-trust gate is
/// passed", and the status is then Blocked when that fails, Green when nothing
/// blocks, and InProgress in between. All three are recomputable from the same
/// JSON document, so asserting the derivation catches the summary and the rows
/// disagreeing — which is the failure mode this smoke exists for — without
/// going red every time a launch-evidence artifact is re-minted.
fn assert_psc_status_is_derived(psc: &Value, gates: &Value) {
    let required_gates: Vec<&Value> = gates
        .as_array()
        .expect("zero-trust gates array")
        .iter()
        .filter(|gate| gate["required_for_launch"] == Value::Bool(true))
        .collect();
    assert!(
        !required_gates.is_empty(),
        "no launch-required zero-trust gates: this assertion would be vacuous"
    );
    let derived_passed = required_gates.iter().all(|gate| gate["status"] == "passed");
    assert_eq!(
        psc["zero_trust_gates_passed"],
        Value::Bool(derived_passed),
        "zero_trust_gates_passed must equal `every required gate passed`; gates were {:?}",
        required_gates
            .iter()
            .map(|gate| (gate["id"].as_str(), gate["status"].as_str()))
            .collect::<Vec<_>>()
    );

    let blockers = psc["blocking_verification_audit_lanes"]
        .as_u64()
        .expect("blocking verification audit lanes")
        + psc["blocking_replay_parity_rows"]
            .as_u64()
            .expect("blocking replay parity rows");
    let expected_status = match (derived_passed, blockers) {
        (false, _) => "Blocked",
        (true, 0) => "Green",
        (true, _) => "InProgress",
    };
    assert_eq!(
        psc["status"], expected_status,
        "certification status must follow from gates_passed={derived_passed} and \
         {blockers} blocker(s)"
    );
    assert_eq!(
        psc["launch_ready"],
        Value::Bool(expected_status == "Green"),
        "launch_ready must mean `status is Green`"
    );
}

/// Cross-check the proof-system certification counters against the same report's
/// rows instead of pinning magic numbers.
///
/// `blocking_replay_parity_rows` counts the `PROOF_SYSTEM_REPLAY_PARITY_ROW_IDS`
/// rows whose *declared* status is not Green, so it is derivable from the rows
/// the same command printed. Deriving it is strictly stronger than the literal
/// `2` that stood here (the live value is 1): a magic number goes stale
/// silently, a derivation catches the two halves disagreeing.
fn assert_psc_counts_are_derived(psc: &Value, rows: &Value, issue_state_snapshot: &Path) {
    let replay_rows = psc["replay_parity_rows"]
        .as_array()
        .expect("proof-system replay parity rows");
    for replay_row in replay_rows {
        let row_id = replay_row["row_id"]
            .as_str()
            .expect("replay parity row_id should be a string");
        let scorecard_row = find_by_id(rows, row_id);
        assert_eq!(
            replay_row["status"], scorecard_row["status"],
            "replay-parity row {row_id} disagrees with the scorecard row it mirrors"
        );
        assert_eq!(
            replay_row["blocks_certification"],
            Value::Bool(scorecard_row["status"] != "Green"),
            "replay-parity row {row_id} blocks_certification must be `status != Green`"
        );
    }
    let derived_blockers = replay_rows
        .iter()
        .filter(|replay_row| replay_row["blocks_certification"] == Value::Bool(true))
        .count();
    assert_eq!(
        psc["blocking_replay_parity_rows"],
        Value::from(derived_blockers),
        "blocking_replay_parity_rows must equal the rows that block, not a pinned constant"
    );

    let open_lanes = psc["verification_audit_open_lanes"]
        .as_array()
        .expect("verification audit open lanes")
        .len();
    let blocking_lanes = psc["blocking_verification_audit_lanes"]
        .as_u64()
        .expect("blocking verification audit lanes") as usize;
    let snapshot_present = issue_state_snapshot.is_file();
    if snapshot_present {
        // With the snapshot, the counter summarises the list beside it.
        assert_eq!(
            blocking_lanes, open_lanes,
            "with the issue-state snapshot present, blocking_verification_audit_lanes must \
             equal the open lanes it lists"
        );
    } else {
        // Without it the two fields mean DIFFERENT things, and the surface is
        // right to make them differ: `missing_issue_state_snapshot` counts
        // EVERY lane as blocking because unknown state is not evidence of
        // closure, while the list stays empty because no lane's state is
        // known. Measured on this checkout: blocking=4, list=[]. The
        // fail-closed direction is what must hold — the count may exceed the
        // list, but it must never collapse to zero just because the list is
        // empty, which would turn "we know nothing" into "nothing blocks".
        assert!(
            blocking_lanes >= open_lanes,
            "blocking lanes {blocking_lanes} is below the {open_lanes} it lists"
        );
        assert!(
            blocking_lanes > 0,
            "without the issue-state snapshot every verification-audit lane must count as \
             blocking; a zero here is a fail-OPEN"
        );
    }

    // The issue-state snapshot is the file the retired skip-guard keyed on. It
    // has never existed in any checkout, and the surface handles that
    // fail-closed: every lane counts as blocking until a fresh snapshot is
    // captured, and `evidence_summary` says so. Assert the branch that fires
    // for whichever state this checkout is in, so capturing the snapshot one
    // day is a deliberate change and not a silent one.
    assert_eq!(
        psc["verification_audit_issue_state_evidence_path"],
        "reports/2026-04-27-proof-system-verification-audit-issue-state.md"
    );
    let summary = psc["evidence_summary"]
        .as_str()
        .expect("proof-system evidence summary");
    assert!(summary.contains(&format!("replay_parity_blockers={derived_blockers}")));
    if issue_state_snapshot.is_file() {
        assert!(
            !summary.contains("is missing on this checkout"),
            "the snapshot is present, so the report must not claim it is missing: {summary}"
        );
    } else {
        assert!(
            summary.contains("is missing on this checkout"),
            "without the snapshot the report must fail closed and say so; got: {summary}"
        );
        assert_eq!(
            psc["verification_audit_refresh_required"], true,
            "a missing issue-state snapshot must demand a refresh"
        );
    }
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
    // 2026-08-26: THE SKIP THAT STOOD HERE GUARDED A FILE THAT HAS NEVER
    // EXISTED. It returned early unless
    // `reports/2026-04-27-proof-system-verification-audit-issue-state.md` was a
    // file; that path has **no commit in `git log --all`**, is untracked and is
    // not gitignored, so it has never been present in any checkout and this
    // body had never once executed. Its comment claimed the subprocess "exits
    // non-zero" without the file — the subprocess exits non-zero *by design*
    // whenever the launch gate blocks, which is the fail-closed contract, and
    // the missing snapshot is handled honestly rather than fatally: the report
    // falls back to `missing_issue_state_snapshot`, counts EVERY
    // verification-audit lane as blocking ("unknown state is not evidence of
    // closure"), and says so in `evidence_summary`. That fail-closed path is
    // the one this checkout actually exercises, so it is what gets asserted
    // below instead of skipped.
    let root = workspace_root();
    let issue_state_snapshot =
        root.join("reports/2026-04-27-proof-system-verification-audit-issue-state.md");
    let (structural, unchecked, total) = unchecked_decl_totals();
    let expected_summary_prefix = format!(
        "add_decl_structural_count={structural}, add_decl_unchecked_count={unchecked}, total={total}; "
    );

    let status = run_clean_json(
        &["replacement", "status", "--json"],
        ExitPolicy::TracksLaunchReady,
    );
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
    assert_deny_sorry_verdict_matches_its_blocker(status_deny_sorry);
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
    // The row's gate command moved to the Rust-owned minting form long ago; the
    // string asserted here was the retired `./scripts/deny_sorry_gate.sh && …`
    // shell spelling, and nothing noticed because this body never ran.
    assert_eq!(
        fallback_row["gate_command"],
        "clean replacement trust-core-evidence --deny-sorry --evidence \
         reports/deny-sorry-launch-evidence.json --json && clean replacement \
         trust-core-evidence --json"
    );
    assert_eq!(fallback_row["status"], "Green");
    assert_eq!(
        fallback_row["evidence_artifact"],
        "reports/deny-sorry-launch-evidence.json"
    );
    // `status` is the hand-declared claim; `effective_status` is that claim
    // reconciled against the row's live zero-trust gate and can only ever move
    // toward less confidence. Asserting both keeps a Green declaration from
    // masking a gate that is not passing.
    let fallback_effective = fallback_row["effective_status"]
        .as_str()
        .expect("fallback-denial effective_status");
    assert!(
        matches!(fallback_effective, "Green" | "PendingEvidence"),
        "fallback-denial reconciles against a closed ratchet, so it may await evidence but \
         must not be Blocked; got {fallback_effective}"
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
    // The proof-system certification block. The old assertions here pinned
    // `status == "InProgress"`, `zero_trust_gates_passed == true` and
    // `blocking_replay_parity_rows == 2`; on this tree those read Blocked,
    // false and 1.
    //
    // They are not re-pinned, because two of the three legitimately MOVE: every
    // gate's verdict depends on whether its launch-evidence artifact is fresh,
    // and the artifacts pin a digest over `cmd_replacement/**/*.rs`, so any
    // commit to this module stales them until they are re-minted. A pinned
    // expectation here would be red for one commit and green for the next
    // without anything being wrong. Derive the relationships instead — they
    // hold in both states and catch a real contradiction either way.
    let status_psc = &status["proof_system_certification"];
    assert_psc_status_is_derived(status_psc, &status["zero_trust_gates"]);
    assert_psc_counts_are_derived(status_psc, &status["rows"], &issue_state_snapshot);

    let evidence = run_clean_json(
        &["replacement", "trust-core-evidence", "--json"],
        ExitPolicy::NonZeroOnlyWhenNotReady,
    );
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
    // Same certification block, reached through the sibling command. The two
    // commands must agree field for field; asserting that is what makes this a
    // process-boundary smoke rather than two independent guesses.
    let evidence_psc = &evidence["proof_system_certification"];
    assert_eq!(
        evidence_psc["verification_audit_path"],
        "docs/VERIFICATION_AUDIT.md"
    );
    assert_psc_status_is_derived(evidence_psc, &evidence["zero_trust_gates"]);
    for field in [
        "status",
        "zero_trust_gates_passed",
        "blocking_verification_audit_lanes",
        "blocking_replay_parity_rows",
        "evidence_summary",
    ] {
        assert_eq!(
            evidence_psc[field], status_psc[field],
            "`clean replacement status` and `clean replacement trust-core-evidence` disagree \
             on proof_system_certification.{field}"
        );
    }
    assert_psc_counts_are_derived(evidence_psc, &status["rows"], &issue_state_snapshot);
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
    assert_deny_sorry_verdict_matches_its_blocker(evidence_deny_sorry);
    assert_eq!(
        evidence_deny_sorry["status"], status_deny_sorry["status"],
        "the two commands must report the same deny-sorry verdict"
    );
    let evidence_axiom_audit = find_by_id(&evidence["zero_trust_gates"], "axiom-audit");
    assert!(evidence_axiom_audit["evidence_summary"]
        .as_str()
        .expect("axiom-audit evidence summary")
        .contains("reports/axiom-audit-launch-evidence.json"));
}

#[test]
fn tactic_parity_cli_reports_arithmetic_and_strict_zero_trust_evidence() {
    // The twin of the skip removed above: same nonexistent path, same
    // never-executed body. Its assertions had drifted even further — it pinned
    // `aesop` at EvidenceBackedPartial and `grind` at Lean4ParityGap with 2 and
    // 5 outstanding gaps, and the live surface reports every one of the ten
    // tactics ProofCarrying with `clean_gap_total = 0`.
    let report = run_clean_json_with_timeout(
        &["replacement", "tactic-parity", "--json"],
        CLEAN_TACTIC_PARITY_CLI_RUN_TIMEOUT,
        ExitPolicy::NonZeroOnlyWhenNotReady,
    );

    assert_eq!(report["generated_by"], "clean replacement tactic-parity");
    assert_eq!(report["launch_ready"], false);

    // Every tactic row must be proof-carrying with no trusted arithmetic or
    // trusted `ay` acceptance, and the counts map must account for all of them.
    let tactic_rows = report["tactics"]
        .as_array()
        .expect("tactic-parity tactics array");
    assert_eq!(tactic_rows.len(), 10);
    for row in tactic_rows {
        let tactic = row["tactic"].as_str().expect("tactic name");
        assert_eq!(
            row["lean4_parity_status"], "ProofCarrying",
            "tactic {tactic} is no longer proof-carrying"
        );
        assert_eq!(
            row["trusted_arith_count"], 0,
            "tactic {tactic} accepts trusted arithmetic"
        );
        assert_eq!(
            row["trusted_ay_count"], 0,
            "tactic {tactic} accepts trusted ay results"
        );
    }
    assert_eq!(report["tactic_counts"]["ProofCarrying"], tactic_rows.len());
    for retired in ["EvidenceBackedPartial", "Lean4ParityGap"] {
        assert!(
            report["tactic_counts"][retired].is_null(),
            "no tactic should be {retired} any more, but the counts map still carries it"
        );
    }
    for tactic in [
        "mathverse",
        "linarith",
        "nlinarith",
        "exact",
        "aesop",
        "grind",
    ] {
        assert_eq!(
            find_by_field(&report["tactics"], "tactic", tactic)["lean4_parity_status"],
            "ProofCarrying"
        );
    }

    let count_artifact = &report["lean4_vs_clean_tactic_counts"];
    assert_eq!(
        count_artifact["schema_version"],
        "clean-tactic-parity-count-artifact-v1"
    );
    assert_eq!(
        count_artifact["source_artifact"],
        "reports/tactic-parity-counts.json"
    );
    let count_rows = count_artifact["tactics"]
        .as_array()
        .expect("tactic count rows");
    assert_eq!(
        count_artifact["summary"]["tactic_row_count"],
        count_rows.len()
    );
    assert_eq!(count_artifact["summary"]["lean4_total"], 56);
    assert_eq!(count_artifact["summary"]["clean_total"], 56);
    assert_eq!(count_artifact["summary"]["matched_total"], 56);
    assert_eq!(count_artifact["summary"]["clean_gap_total"], 0);
    assert_eq!(count_artifact["summary"]["partial_rows"], 0);
    assert_eq!(count_artifact["summary"]["parity_gap_rows"], 0);
    assert_eq!(
        count_artifact["summary"]["proof_carrying_rows"],
        count_rows.len()
    );
    // A zero-gap row carries no `remaining_blocker`, and a row with gaps must
    // carry a fail-closed one. Asserting the coupling keeps a silently dropped
    // blocker from reading as parity.
    let mut derived_gap_total = 0_u64;
    for row in count_rows {
        let tactic = row["tactic"].as_str().expect("count row tactic");
        let gap = row["clean_gap_count"]
            .as_u64()
            .expect("count row clean_gap_count");
        derived_gap_total += gap;
        if gap == 0 {
            assert_eq!(row["status"], "ProofCarrying", "tactic {tactic}");
            assert!(
                row["remaining_blocker"].is_null(),
                "tactic {tactic} has no gaps but still carries a remaining_blocker"
            );
        } else {
            let blocker = &row["remaining_blocker"];
            assert_eq!(blocker["fail_closed"], true, "tactic {tactic}");
            assert_eq!(blocker["gap_count"], gap, "tactic {tactic}");
            assert!(blocker["gate_required_to_clear"]
                .as_str()
                .expect("gate_required_to_clear")
                .contains("clean_gap_count = 0"));
        }
    }
    assert_eq!(
        count_artifact["summary"]["clean_gap_total"],
        Value::from(derived_gap_total),
        "clean_gap_total must equal the per-tactic gaps it summarises"
    );

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

/// `clean replacement axiom-audit` must exit zero exactly while its OWN verdict
/// holds — its contract keys on `validation_passed`, not on `launch_ready` like
/// its `trust-core-evidence` / `tactic-parity` siblings (see `run_axiom_audit`
/// in `cmd_replacement/handlers.rs`, which returns `StaleTrustCoreArtifact`
/// when validation fails).
///
/// RESTORED 2026-08-27. A test of this name existed and passed on 2026-08-26
/// and was destroyed by a mutation-proof run in this shared working tree that
/// snapshotted whole files up front and restored them minutes later, after a
/// co-tenant had added it. The body was never committed and is not recoverable;
/// this is a reconstruction from the name and the handler's actual contract, so
/// it may not match the original assertion for assertion.
///
/// Written two-way ON PURPOSE. A one-armed version that only checked the
/// passing case would still pass if the command were changed to exit zero
/// unconditionally — which is precisely the defect
/// `tactic_parity_gate_exit_status_tracks_its_own_launch_ready` was added to
/// catch on a sibling command, and precisely the shape of the vacuous gate
/// found elsewhere in this tree the same week.
#[test]
fn replacement_axiom_audit_cli_exits_zero_while_its_own_verdict_holds() {
    let audit = workspace_root().join("data/axiom_audit.json");
    assert!(
        audit.is_file(),
        "the tracked axiom audit must exist for this smoke: {}",
        audit.display()
    );

    // Arm 1 — the real, tracked audit: verdict holds, so the gate exits zero.
    let audit_arg = audit.to_string_lossy().into_owned();
    let args: Vec<&str> = vec![
        "replacement",
        "axiom-audit",
        "--verify",
        &audit_arg,
        "--json",
    ];
    let output = run_clean_with_timeout(&args, CLEAN_CLI_RUN_TIMEOUT);
    let report = parse_clean_json(&args, &output);
    let passed = report["validation_passed"]
        .as_bool()
        .expect("axiom-audit --json must emit a boolean `validation_passed`");
    let code = output
        .status
        .code()
        .expect("clean replacement axiom-audit was killed by a signal");
    assert!(
        passed,
        "the tracked audit should validate; failures: {}",
        report["failures"]
    );
    assert_eq!(
        code,
        0,
        "a holding verdict must exit zero; stderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );

    // Arm 2 — a tampered audit: the verdict does NOT hold, so the gate must
    // refuse. Without this arm the test would still pass against a command
    // that exits zero unconditionally.
    let mut tampered: Value =
        serde_json::from_slice(&fs::read(&audit).expect("read the tracked audit"))
            .expect("the tracked audit is JSON");
    // Tamper the AGGREGATE the `aggregate_consistency` lane recomputes, not a
    // recorded digest: a wrong total contradicts the per-row data in the same
    // file, which is exactly what that lane exists to catch.
    tampered["total_domain_axioms"] = Value::from(999_999_u64);
    let dir = env::temp_dir().join(format!(
        "clean-axiom-audit-tamper-{}-{}",
        std::process::id(),
        line!()
    ));
    fs::create_dir_all(&dir).expect("create the tamper directory");
    let tampered_path = dir.join("axiom_audit.json");
    fs::write(
        &tampered_path,
        serde_json::to_vec_pretty(&tampered).expect("serialize the tampered audit"),
    )
    .expect("write the tampered audit");

    let tampered_arg = tampered_path.to_string_lossy().into_owned();
    let bad_args: Vec<&str> = vec![
        "replacement",
        "axiom-audit",
        "--verify",
        &tampered_arg,
        "--json",
    ];
    let bad_output = run_clean_with_timeout(&bad_args, CLEAN_CLI_RUN_TIMEOUT);
    let bad_code = bad_output
        .status
        .code()
        .expect("clean replacement axiom-audit was killed by a signal");
    let _ = fs::remove_dir_all(&dir);
    assert_ne!(
        bad_code,
        0,
        "a tampered audit must not exit zero — a gate that cannot say no is not a gate; \
         stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&bad_output.stdout),
        String::from_utf8_lossy(&bad_output.stderr)
    );
}
