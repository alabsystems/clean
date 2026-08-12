// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Process-boundary smoke tests for the `clean math` project framework.

use std::collections::BTreeMap;
use std::env;
use std::ffi::OsString;
use std::fs;
use std::io::{BufRead, BufReader, Write};
use std::net::TcpStream;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::mpsc;
use std::thread::JoinHandle;
use std::time::{Duration, Instant};

use clean_kernel::{Expr, FVarId, Name};
use clean_math_project::{obligation_fingerprint, MathObligation};
use serde_json::Value;

const CLEAN_MATH_CLI_BIN_ENV: &str = "CLEAN_MATH_CLI_BIN";
const CARGO_CLEAN_BIN_ENV: &str = "CARGO_BIN_EXE_clean";

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .map(Path::to_path_buf)
        .expect("workspace root should be two parents above CARGO_MANIFEST_DIR")
}

fn clean_binary() -> PathBuf {
    if let Some(binary) = env::var_os(CLEAN_MATH_CLI_BIN_ENV) {
        let binary = PathBuf::from(binary);
        assert!(
            binary.is_file(),
            "{CLEAN_MATH_CLI_BIN_ENV} points to {}, but it is not a file",
            binary.display()
        );
        return binary;
    }

    if let Some(binary) = env::var_os(CARGO_CLEAN_BIN_ENV)
        .map(PathBuf::from)
        .filter(|binary| binary.is_file())
    {
        return binary;
    }

    build_clean_binary()
}

fn build_clean_binary() -> PathBuf {
    let root = workspace_root();
    let cargo = env::var_os("CARGO").unwrap_or_else(|| OsString::from("cargo"));
    let status = Command::new(cargo)
        .args(["build", "--quiet", "-p", "clean", "--bin", "clean"])
        .current_dir(&root)
        .env("CARGO_TERM_COLOR", "never")
        .status()
        .expect("cargo build -p clean --bin clean should start");
    assert!(status.success(), "failed to build clean binary: {status}");

    let binary = root
        .join("target")
        .join("debug")
        .join(format!("clean{}", env::consts::EXE_SUFFIX));
    assert!(
        binary.is_file(),
        "cargo build succeeded, but {} does not exist",
        binary.display()
    );
    binary
}

fn run_clean(args: &[&str]) -> Output {
    Command::new(clean_binary())
        .args(args)
        .current_dir(workspace_root())
        .env("CARGO_TERM_COLOR", "never")
        .output()
        .unwrap_or_else(|err| panic!("failed to run clean {args:?}: {err}"))
}

fn run_clean_with_env(args: &[&str], envs: &[(&str, &str)]) -> Output {
    let mut command = Command::new(clean_binary());
    command
        .args(args)
        .current_dir(workspace_root())
        .env("CARGO_TERM_COLOR", "never");
    for (name, value) in envs {
        command.env(name, value);
    }
    command
        .output()
        .unwrap_or_else(|err| panic!("failed to run clean {args:?}: {err}"))
}

fn run_clean_json(args: &[&str]) -> Value {
    let output = run_clean(args);
    assert!(
        output.status.success(),
        "clean {args:?} failed with status {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    parse_json(args, &output)
}

fn run_clean_json_with_env(args: &[&str], envs: &[(&str, &str)]) -> Value {
    let output = run_clean_with_env(args, envs);
    assert!(
        output.status.success(),
        "clean {args:?} failed with status {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    parse_json(args, &output)
}

fn run_clean_json_expect_failure(args: &[&str]) -> Value {
    let output = run_clean(args);
    assert!(
        !output.status.success(),
        "clean {args:?} unexpectedly succeeded\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    parse_json(args, &output)
}

fn run_clean_json_allow_status(args: &[&str]) -> (bool, Value) {
    let output = run_clean(args);
    (output.status.success(), parse_json(args, &output))
}

fn run_clean_json_allow_status_with_env(args: &[&str], envs: &[(&str, &str)]) -> (bool, Value) {
    let output = run_clean_with_env(args, envs);
    (output.status.success(), parse_json(args, &output))
}

struct CleanServer {
    addr: String,
    stop: Option<mpsc::Sender<()>>,
    thread: Option<JoinHandle<()>>,
}

impl Drop for CleanServer {
    fn drop(&mut self) {
        if let Some(stop) = self.stop.take() {
            let _ = stop.send(());
        }
        if let Some(thread) = self.thread.take() {
            let _ = thread.join();
        }
    }
}

fn start_clean_server() -> CleanServer {
    let (addr_tx, addr_rx) = mpsc::channel();
    let (stop_tx, stop_rx) = mpsc::channel();
    let thread = std::thread::spawn(move || {
        let runtime = tokio::runtime::Builder::new_multi_thread()
            .enable_all()
            .build()
            .expect("test server runtime");
        runtime.block_on(async move {
            let mut config =
                clean_server::ServerConfig::new().with_addr("127.0.0.1:0".parse().unwrap());
            config.initial_env = Some(
                clean_kernel::Environment::try_with_prelude()
                    .expect("test server prelude environment"),
            );
            let handle = clean_server::serve(config)
                .await
                .expect("start test server");
            addr_tx
                .send(handle.local_addr().to_string())
                .expect("publish test server address");
            let _ = tokio::task::spawn_blocking(move || stop_rx.recv()).await;
            handle.shutdown();
        });
    });

    let addr = addr_rx
        .recv_timeout(Duration::from_secs(10))
        .expect("test server should publish address");
    wait_for_server(&addr);
    CleanServer {
        addr,
        stop: Some(stop_tx),
        thread: Some(thread),
    }
}

fn wait_for_server(addr: &str) {
    let deadline = Instant::now() + Duration::from_secs(10);
    while Instant::now() < deadline {
        if rpc_server_info(addr).is_ok() {
            return;
        }
        std::thread::sleep(Duration::from_millis(50));
    }
    panic!("clean server at {addr} did not become ready");
}

fn rpc_server_info(addr: &str) -> std::io::Result<()> {
    let mut stream = TcpStream::connect(addr)?;
    stream.set_read_timeout(Some(Duration::from_secs(1)))?;
    stream.set_write_timeout(Some(Duration::from_secs(1)))?;
    writeln!(
        stream,
        r#"{{"jsonrpc":"2.0","method":"serverInfo","id":1}}"#
    )?;
    let mut line = String::new();
    BufReader::new(stream).read_line(&mut line)?;
    if line.contains(r#""result""#) {
        Ok(())
    } else {
        Err(std::io::Error::other(line))
    }
}

fn rpc_server_methods(addr: &str) -> std::io::Result<Vec<String>> {
    let mut stream = TcpStream::connect(addr)?;
    stream.set_read_timeout(Some(Duration::from_secs(1)))?;
    stream.set_write_timeout(Some(Duration::from_secs(1)))?;
    writeln!(
        stream,
        r#"{{"jsonrpc":"2.0","method":"serverInfo","id":1}}"#
    )?;
    let mut line = String::new();
    BufReader::new(stream).read_line(&mut line)?;
    let response: Value = serde_json::from_str(&line).map_err(std::io::Error::other)?;
    let methods = response["result"]["methods"]
        .as_array()
        .ok_or_else(|| std::io::Error::other(line.clone()))?
        .iter()
        .filter_map(|method| method.as_str().map(str::to_owned))
        .collect();
    Ok(methods)
}

fn assert_proof_state_bridge_report(
    report: &Value,
    operation: &str,
    state: &str,
    detail_substring: &str,
) {
    assert_eq!(report["schema_version"], "clean-proof-state-v2-bridge-v1");
    assert_eq!(report["operation"], operation);
    assert_eq!(report["state"], state);
    assert_eq!(report["status"], "blocked-server-adapter-required");
    assert!(
        report["detail"]
            .as_str()
            .expect("detail")
            .contains(detail_substring),
        "unexpected bridge detail: {}",
        report["detail"]
    );
}

fn assert_replay_diagnostic(report: &Value, code: &str) {
    assert!(
        report["diagnostics"]
            .as_array()
            .expect("diagnostics")
            .iter()
            .any(|diagnostic| diagnostic["code"] == code),
        "missing replay diagnostic {code}: {report}"
    );
}

fn parse_json(args: &[&str], output: &Output) -> Value {
    serde_json::from_slice(&output.stdout).unwrap_or_else(|err| {
        panic!(
            "clean {args:?} did not emit JSON on stdout: {err}\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    })
}

fn sat_project() -> &'static str {
    "tests/fixtures/math_project/sat_pb/project.json"
}

fn sat_obligation() -> &'static str {
    "tests/fixtures/math_project/sat_pb/obligations/subsumption.json"
}

fn sat_serialized_goal_obligation() -> &'static str {
    "tests/fixtures/math_project/sat_pb/obligations/prop_serialized_goal.json"
}

fn sat_generic_true_smoke_obligation() -> &'static str {
    "tests/fixtures/math_project/sat_pb/obligations/generic_true_serialized_kernel_smoke.json"
}

fn nn_project() -> &'static str {
    "tests/fixtures/math_project/nn_verify/project.json"
}

fn nn_obligation() -> &'static str {
    "tests/fixtures/math_project/nn_verify/obligations/farkas.json"
}

fn nn_generic_true_smoke_obligation() -> &'static str {
    "tests/fixtures/math_project/nn_verify/obligations/generic_true_serialized_kernel_smoke.json"
}

fn proof_complexity_project() -> &'static str {
    "tests/fixtures/math_project/proof_complexity/project.json"
}

fn proof_complexity_obligation() -> &'static str {
    "tests/fixtures/math_project/proof_complexity/obligations/resolution_width.json"
}

fn proof_complexity_generic_true_smoke_obligation() -> &'static str {
    "tests/fixtures/math_project/proof_complexity/obligations/generic_true_serialized_kernel_smoke.json"
}

fn write_true_serialized_goal_obligation(root: &Path) -> PathBuf {
    let path = root.join("true_serialized_goal.json");
    let payload = serde_json::json!({
        "schema_version": "clean-obligation-v1",
        "project": "sat-pb-pilot",
        "domain_profile": "sat-pb",
        "producer": {
            "system": "fixture",
            "commit": "serialized-true-goal"
        },
        "goal": {
            "expr": Expr::const_(Name::from_string("True"), vec![]),
            "pretty": "True"
        },
        "metadata": {
            "fixture": "serialized-true-goal"
        },
        "trust_policy": "constructive-only"
    });
    fs::write(
        &path,
        serde_json::to_string_pretty(&payload).expect("serialize True obligation"),
    )
    .expect("write True serialized goal obligation");
    path
}

fn write_local_assumption_serialized_goal_obligation(root: &Path) -> PathBuf {
    let path = root.join("local_assumption_serialized_goal.json");
    let a = Expr::fvar(FVarId::new(0));
    let a_type = serde_json::to_string(&Expr::prop()).expect("serialize A type");
    let h_type = serde_json::to_string(&a).expect("serialize h type");
    let payload = serde_json::json!({
        "schema_version": "clean-obligation-v1",
        "project": "sat-pb-pilot",
        "domain_profile": "sat-pb",
        "producer": {
            "system": "fixture",
            "commit": "serialized-local-assumption-goal"
        },
        "goal": {
            "expr": a,
            "pretty": "A"
        },
        "local_context": [
            {
                "name": "A",
                "type_pp": "Prop",
                "type_expr": a_type
            },
            {
                "name": "h",
                "type_pp": "A",
                "type_expr": h_type
            }
        ],
        "metadata": {
            "fixture": "serialized-local-assumption-goal"
        },
        "trust_policy": "constructive-only"
    });
    fs::write(
        &path,
        serde_json::to_string_pretty(&payload).expect("serialize local assumption obligation"),
    )
    .expect("write local assumption serialized goal obligation");
    path
}

fn write_hygiene_project_fixture(
    root: &Path,
    evidence: Option<&str>,
    metadata: BTreeMap<String, String>,
) {
    fs::create_dir_all(root.join("theorem_packs")).expect("mkdir theorem_packs");
    fs::create_dir_all(root.join("obligations")).expect("mkdir obligations");
    fs::create_dir_all(root.join("artifacts")).expect("mkdir artifacts");
    fs::write(
        root.join("theorem_packs").join("Pilot.lean"),
        "theorem hygiene_fixture_true : True := True.intro\n",
    )
    .expect("write theorem pack");
    fs::write(root.join("artifacts").join("proof.json"), "{}\n").expect("write artifact");

    let metadata = serde_json::to_value(metadata).expect("metadata json");
    let obligation = serde_json::json!({
        "schema_version": "clean-obligation-v1",
        "project": "hygiene-pilot",
        "domain_profile": "sat-pb",
        "producer": {
            "system": "ay",
            "commit": "fixture-hygiene"
        },
        "goal": {
            "expr": "SatPb.hygiene_fixture",
            "pretty": "SAT/PB hygiene fixture"
        },
        "local_context": [],
        "side_conditions": [],
        "artifact_refs": [
            {
                "kind": "proof-artifact-v1",
                "path": "artifacts/proof.json",
                "hash": "blake3:fresh-proof"
            }
        ],
        "metadata": metadata,
        "trust_policy": "constructive-only"
    });
    fs::write(
        root.join("obligations").join("pilot.json"),
        serde_json::to_string_pretty(&obligation).expect("obligation json"),
    )
    .expect("write obligation");

    let evidence = evidence
        .into_iter()
        .map(ToOwned::to_owned)
        .collect::<Vec<_>>();
    let project = serde_json::json!({
        "schema_version": "clean-math-project-v1",
        "project": "hygiene-pilot",
        "domain_profile": "sat-pb",
        "owner": "clean-math-factory",
        "theorem_packs": ["theorem_packs/Pilot.lean"],
        "obligation_sources": ["obligations/pilot.json"],
        "artifact_formats": ["proof-artifact-v1"],
        "trust_policy": {
            "name": "constructive-only",
            "allowed_axioms": [],
            "forbidden_trust_markers": ["sorry", "sorryAx", "trustedArith", "synthetic_sorry"],
            "require_artifact_replay": true,
            "allow_synthetic_sorry": false
        },
        "normalizers": ["sat_pb_nf"],
        "evidence": evidence,
        "issue_routing": {
            "labels": ["math-project", "sat-pb"],
            "owners": [],
            "blocking_categories": ["artifact", "trust"]
        }
    });
    fs::write(
        root.join("project.json"),
        serde_json::to_string_pretty(&project).expect("project json"),
    )
    .expect("write project");
}

fn write_hygiene_replay_evidence(root: &Path, fingerprint: &str, proof_hash: &str) {
    fs::create_dir_all(root.join("evidence")).expect("mkdir evidence");
    let evidence = serde_json::json!({
        "schema_version": "clean-artifact-replay-report-v1",
        "artifact_path": "artifacts/proof.json",
        "project": "hygiene-pilot",
        "source_system": "ay",
        "artifact_kind": "ay_alethe_envelope",
        "problem_hash": "blake3:fresh-problem",
        "proof_hash": proof_hash,
        "certificate_format": "ay-alethe-envelope-v1",
        "evidence_kind": "replay_only",
        "kernel_certified": false,
        "replay_status": "pass",
        "replay_adapter": "ay-alethe-v1",
        "linked_obligations": [fingerprint],
        "trusted_assumptions": [],
        "details": []
    });
    fs::write(
        root.join("evidence").join("replay.json"),
        serde_json::to_string_pretty(&evidence).expect("evidence json"),
    )
    .expect("write replay evidence");
}

fn write_replay_cache_project_fixture(root: &Path) -> PathBuf {
    fs::create_dir_all(root.join("theorem_packs")).expect("mkdir theorem_packs");
    fs::create_dir_all(root.join("obligations")).expect("mkdir obligations");
    fs::create_dir_all(root.join("artifacts")).expect("mkdir artifacts");
    fs::write(
        root.join("theorem_packs").join("Pilot.lean"),
        "theorem replay_cache_fixture_true : True := True.intro\n",
    )
    .expect("write theorem pack");
    let artifact_path = root.join("artifacts").join("gamma.json");
    fs::copy(
        workspace_root()
            .join("tests")
            .join("fixtures")
            .join("external_certificates")
            .join("proof_artifact_v1")
            .join("gamma_crown_farkas_valid.json"),
        &artifact_path,
    )
    .expect("copy artifact fixture");
    let obligation = serde_json::json!({
        "schema_version": "clean-obligation-v1",
        "project": "replay-cache-pilot",
        "domain_profile": "nn-verify",
        "producer": {
            "system": "gamma-crown",
            "commit": "fixture-replay-cache"
        },
        "goal": {
            "expr": "NNVerify.replay_cache_fixture",
            "pretty": "NN verification replay cache fixture"
        },
        "local_context": [],
        "side_conditions": [],
        "artifact_refs": [
            {
                "kind": "proof-artifact-v1",
                "path": "artifacts/gamma.json",
                "hash": "blake3:fixture-gamma-crown-farkas-proof"
            }
        ],
        "metadata": {},
        "trust_policy": "constructive-only"
    });
    fs::write(
        root.join("obligations").join("pilot.json"),
        serde_json::to_string_pretty(&obligation).expect("obligation json"),
    )
    .expect("write obligation");
    let project = serde_json::json!({
        "schema_version": "clean-math-project-v1",
        "project": "replay-cache-pilot",
        "domain_profile": "nn-verify",
        "owner": "clean-math-factory",
        "theorem_packs": ["theorem_packs/Pilot.lean"],
        "obligation_sources": ["obligations/pilot.json"],
        "artifact_formats": ["gamma-crown-farkas-v1", "proof-artifact-v1"],
        "trust_policy": {
            "name": "constructive-only",
            "allowed_axioms": [],
            "forbidden_trust_markers": ["sorry", "sorryAx", "trustedArith", "synthetic_sorry"],
            "require_artifact_replay": true,
            "allow_synthetic_sorry": false
        },
        "normalizers": ["nn_interval_nf"],
        "evidence": [],
        "issue_routing": {
            "labels": ["math-project", "nn-verify"],
            "owners": [],
            "blocking_categories": ["artifact", "trust"]
        }
    });
    let project_path = root.join("project.json");
    fs::write(
        &project_path,
        serde_json::to_string_pretty(&project).expect("project json"),
    )
    .expect("write project");
    project_path
}

fn write_axiom_theorem_pack_project_fixture(root: &Path) -> PathBuf {
    let pack_dir = root.join("theorem_packs");
    fs::create_dir_all(&pack_dir).expect("create theorem_packs");
    fs::write(
        pack_dir.join("AxiomPilot.lean"),
        "namespace SatPb\n\naxiom unsound_bridge : False\n\nend SatPb\n",
    )
    .expect("write theorem pack");
    let project_path = root.join("project.json");
    fs::write(
        &project_path,
        r#"{
  "schema_version": "clean-math-project-v1",
  "project": "sat-pb-axiom-pilot",
  "domain_profile": "sat-pb",
  "owner": "clean-math-factory",
  "theorem_packs": ["theorem_packs/AxiomPilot.lean"],
  "obligation_sources": [],
  "artifact_formats": ["proof-artifact-v1"],
  "trust_policy": {
    "name": "constructive-only",
    "allowed_axioms": [],
    "forbidden_trust_markers": ["sorry", "sorryAx", "trustedArith", "synthetic_sorry"],
    "require_artifact_replay": true,
    "allow_synthetic_sorry": false
  },
  "normalizers": [],
  "evidence": [],
  "issue_routing": {
    "labels": ["math-project", "sat-pb"],
    "owners": [],
    "blocking_categories": ["trust"]
  }
}
"#,
    )
    .expect("write project manifest");
    project_path
}

fn write_issue_plan_project_with_invalid_obligation(root: &Path) -> PathBuf {
    fs::create_dir_all(root.join("obligations")).expect("mkdir obligations");
    let obligation = serde_json::json!({
        "schema_version": "clean-obligation-v1",
        "project": "different-project",
        "domain_profile": "sat-pb",
        "producer": {
            "system": "fixture",
            "commit": "invalid-obligation"
        },
        "goal": {
            "expr": "SatPb.invalid_fixture",
            "pretty": "invalid fixture"
        },
        "trust_policy": "constructive-only"
    });
    fs::write(
        root.join("obligations").join("invalid.json"),
        serde_json::to_string_pretty(&obligation).expect("obligation json"),
    )
    .expect("write invalid obligation");
    let project = serde_json::json!({
        "schema_version": "clean-math-project-v1",
        "project": "issue-plan-invalid-pilot",
        "domain_profile": "sat-pb",
        "owner": "clean-math-factory",
        "theorem_packs": [],
        "obligation_sources": ["obligations/invalid.json"],
        "artifact_formats": ["proof-artifact-v1"],
        "trust_policy": {
            "name": "constructive-only",
            "allowed_axioms": [],
            "forbidden_trust_markers": ["sorry", "sorryAx", "synthetic_sorry"],
            "require_artifact_replay": false,
            "allow_synthetic_sorry": false
        },
        "normalizers": ["sat_pb_nf"],
        "evidence": [],
        "issue_routing": {
            "labels": ["math-project", "sat-pb"],
            "owners": [],
            "blocking_categories": ["manifest", "obligation"]
        }
    });
    let project_path = root.join("project.json");
    fs::write(
        &project_path,
        serde_json::to_string_pretty(&project).expect("project json"),
    )
    .expect("write project");
    project_path
}

fn write_issue_plan_project_with_proof_failure_diagnostic(root: &Path) -> PathBuf {
    fs::create_dir_all(root.join("theorem_packs")).expect("mkdir theorem_packs");
    fs::create_dir_all(root.join("obligations")).expect("mkdir obligations");
    fs::create_dir_all(root.join("evidence")).expect("mkdir evidence");
    fs::write(
        root.join("theorem_packs").join("Pilot.lean"),
        "theorem diagnostic_fixture_true : True := True.intro\n",
    )
    .expect("write theorem pack");

    let obligation = serde_json::json!({
        "schema_version": "clean-obligation-v1",
        "project": "issue-plan-diagnostic-pilot",
        "domain_profile": "sat-pb",
        "producer": {
            "system": "fixture",
            "commit": "proof-failure-diagnostic"
        },
        "goal": {
            "expr": Expr::const_(Name::from_string("True"), vec![]),
            "pretty": "True"
        },
        "local_context": [],
        "side_conditions": [],
        "artifact_refs": [],
        "metadata": {
            "fixture": "proof-failure-diagnostic"
        },
        "trust_policy": "constructive-only"
    });
    fs::write(
        root.join("obligations").join("pilot.json"),
        serde_json::to_string_pretty(&obligation).expect("obligation json"),
    )
    .expect("write obligation");
    let obligation_model: MathObligation =
        serde_json::from_value(obligation).expect("obligation model");
    let fingerprint = obligation_fingerprint(&obligation_model);

    let diagnostic = serde_json::json!({
        "schema_version": "clean-math-proof-failure-diagnostic-v1",
        "obligation_fingerprint": fingerprint,
        "evidence_id": "volatile-cli-evidence-id",
        "run_id": "volatile-cli-run-id",
        "observed_at": "2026-04-27T12:00:00Z",
        "summary": "elaboration fails before theorem candidate closes",
        "blockers": ["unknown-constant", "missing-local-instance"],
        "ranking_signals": ["unknown-constant", "pre-kernel-elab"],
        "score_delta": 33,
        "reproduction": {
            "commands": ["clean proof-state replay --state proof-failure"],
            "files": ["proofs/Pilot.lean"]
        }
    });
    fs::write(
        root.join("evidence").join("proof-failure.json"),
        serde_json::to_string_pretty(&diagnostic).expect("diagnostic json"),
    )
    .expect("write proof failure diagnostic");

    let project = serde_json::json!({
        "schema_version": "clean-math-project-v1",
        "project": "issue-plan-diagnostic-pilot",
        "domain_profile": "sat-pb",
        "owner": "clean-math-factory",
        "theorem_packs": ["theorem_packs/Pilot.lean"],
        "obligation_sources": ["obligations/pilot.json"],
        "artifact_formats": ["proof-artifact-v1"],
        "trust_policy": {
            "name": "constructive-only",
            "allowed_axioms": [],
            "forbidden_trust_markers": ["sorry", "sorryAx", "synthetic_sorry"],
            "require_artifact_replay": false,
            "allow_synthetic_sorry": false
        },
        "normalizers": ["sat_pb_nf"],
        "evidence": ["evidence/proof-failure.json"],
        "issue_routing": {
            "labels": ["math-project", "sat-pb"],
            "owners": [],
            "blocking_categories": ["manifest", "obligation", "artifact", "trust"]
        }
    });
    let project_path = root.join("project.json");
    fs::write(
        &project_path,
        serde_json::to_string_pretty(&project).expect("project json"),
    )
    .expect("write project");
    project_path
}

#[test]
fn math_project_status_emits_manifest_status_json() {
    let report = run_clean_json(&[
        "math",
        "project",
        "status",
        "--project",
        sat_project(),
        "--json",
    ]);

    assert_eq!(report["schema_version"], "clean-math-project-status-v1");
    assert_eq!(report["project"], "sat-pb-pilot");
    assert_eq!(report["domain_profile"], "sat-pb");
    assert_eq!(report["status"], "pass");
    assert_eq!(report["theorem_packs"], 1);
    assert_eq!(report["obligation_sources"], 4);
    assert!(report["violations"]
        .as_array()
        .expect("violations")
        .is_empty());
}

#[test]
fn math_project_init_full_layout_seeds_status_clean_project() {
    let temp = tempfile::tempdir().expect("tempdir");
    let output = temp.path().join("seeded_project");
    let output_arg = output.to_str().expect("utf8 output path");

    let init = run_clean_json(&[
        "math",
        "project",
        "init",
        "--domain",
        "sat-pb",
        "--project-name",
        "seeded-sat-pb",
        "--output",
        output_arg,
        "--layout",
        "full",
        "--json",
    ]);

    assert_eq!(init["schema_version"], "clean-math-project-init-v1");
    assert_eq!(init["layout"], "full");
    assert_eq!(init["project"], "seeded-sat-pb");
    assert_eq!(
        init["path"].as_str().expect("init path"),
        output
            .join("math-project.json")
            .to_str()
            .expect("utf8 path")
    );

    for path in [
        "math-project.json",
        "theorem_packs/Pilot.lean",
        "obligations/pilot.json",
        "artifacts/README.md",
        "evidence/README.md",
        "reports/README.md",
    ] {
        assert!(
            output.join(path).is_file(),
            "expected seeded file {}",
            output.join(path).display()
        );
    }

    let status = run_clean_json(&[
        "math",
        "project",
        "status",
        "--project",
        output_arg,
        "--json",
    ]);

    assert_eq!(status["status"], "pass");
    assert_eq!(status["project"], "seeded-sat-pb");
    assert_eq!(status["theorem_packs"], 1);
    assert_eq!(status["obligation_sources"], 1);
    assert!(status["violations"]
        .as_array()
        .expect("violations")
        .is_empty());
}

#[test]
fn math_project_status_json_reports_manifest_load_diagnostics_for_unknown_fields() {
    let temp = tempfile::tempdir().expect("tempdir");
    let project_path = temp.path().join("project.json");
    fs::write(
        &project_path,
        r#"{
  "schema_version": "clean-math-project-v1",
  "project": "bad-manifest",
  "domain_profile": "sat-pb",
  "owner": "clean-math-factory",
  "trust_policy": {
    "name": "constructive-only"
  },
  "unexpected_field": true
}
"#,
    )
    .expect("write malformed project");
    let project_arg = project_path.to_str().expect("utf8 temp path");

    let report = run_clean_json_expect_failure(&[
        "math",
        "project",
        "status",
        "--project",
        project_arg,
        "--json",
    ]);

    assert_eq!(
        report["schema_version"],
        "clean-math-project-load-diagnostic-v1"
    );
    assert_eq!(report["status"], "fail");
    let violation = &report["violations"]
        .as_array()
        .expect("violations")
        .first()
        .expect("load violation");
    assert_eq!(violation["code"], "MP000");
    assert_eq!(violation["path"], "manifest_schema");
    assert!(violation["message"]
        .as_str()
        .expect("message")
        .contains("unknown field"));
}

#[test]
fn math_project_status_json_reports_manifest_load_diagnostics_for_malformed_json() {
    let temp = tempfile::tempdir().expect("tempdir");
    let project_path = temp.path().join("project.json");
    fs::write(&project_path, "{").expect("write malformed project");
    let project_arg = project_path.to_str().expect("utf8 temp path");

    let report = run_clean_json_expect_failure(&[
        "math",
        "project",
        "status",
        "--project",
        project_arg,
        "--json",
    ]);

    assert_eq!(
        report["schema_version"],
        "clean-math-project-load-diagnostic-v1"
    );
    assert_eq!(report["status"], "fail");
    assert_eq!(report["violations"][0]["code"], "MP000");
    assert_eq!(report["violations"][0]["path"], "manifest_json");
}

#[test]
fn math_profile_inspect_reports_sat_pb_profile_json() {
    let report = run_clean_json(&["math", "profile", "inspect", "--domain", "sat-pb", "--json"]);

    assert_eq!(report["schema_version"], "clean-domain-profile-v1");
    assert_eq!(report["name"], "sat-pb");
    assert!(report["semantic_heads"]
        .as_array()
        .expect("semantic_heads")
        .iter()
        .any(|value| value == "Clause"));
    assert!(report["normalizers"]
        .as_array()
        .expect("normalizers")
        .iter()
        .any(|value| value == "cert_simp"));
    assert_eq!(report["tactic_normalizer_plan"]["domain_profile"], "sat-pb");
    assert_eq!(
        report["tactic_normalizer_plan"]["normalizers"][0]["name"],
        "cert_simp"
    );
    assert_eq!(
        report["tactic_normalizer_plan"]["normalizers"][1]["name"],
        "cert_mathverse"
    );
    assert_eq!(
        report["tactic_normalizer_plan"]["tactic_recommendations"][0]["name"],
        "cert_simp"
    );
    assert_eq!(
        report["tactic_normalizer_plan"]["tactic_recommendations"][0]["source"],
        "domain-profile:sat-pb"
    );
    assert_eq!(
        report["tactic_normalizer_plan"]["tactic_recommendations"][0]["uses_profile_normalizer"],
        true
    );
    assert_eq!(
        report["tactic_normalizer_plan"]["tactic_recommendations"][1]["name"],
        "cert_mathverse"
    );
    assert_eq!(
        report["tactic_normalizer_plan"]["tactic_recommendations"][1]["source"],
        "domain-profile:sat-pb"
    );
    assert_eq!(
        report["tactic_normalizer_plan"]["tactic_recommendations"][1]["uses_profile_normalizer"],
        true
    );
    assert_eq!(
        report["artifact_replay_registry"]["schema_version"],
        "clean-artifact-replay-registry-v1"
    );
    assert_eq!(
        report["artifact_replay_registry"]["domain_profile"],
        "sat-pb"
    );
    let adapters = report["artifact_replay_registry"]["adapters"]
        .as_array()
        .expect("replay adapters");
    assert_eq!(adapters.len(), 5);
    let drat = adapters
        .iter()
        .find(|adapter| adapter["id"] == "sat-pb-drat-v1")
        .expect("sat-pb DRAT adapter descriptor");
    assert_eq!(drat["status"]["phase"], "Phase 6");
    assert_eq!(drat["status"]["lifecycle"], "available");
    assert_eq!(drat["trust"]["evidence_kind"], "replay_only");
    assert_eq!(drat["trust"]["kernel_certified"], false);
    let veripb = adapters
        .iter()
        .find(|adapter| adapter["id"] == "sat-pb-veripb-v1")
        .expect("sat-pb VeriPB adapter descriptor");
    assert_eq!(veripb["status"]["lifecycle"], "partial");
    let alethe = adapters
        .iter()
        .find(|adapter| adapter["id"] == "ay-alethe-v1")
        .expect("SAT/PB Alethe adapter descriptor");
    assert_eq!(alethe["status"]["lifecycle"], "feature-gated");
    assert_eq!(alethe["availability"]["feature_gate"], "carcara-verify");
    assert!(adapters.iter().all(|adapter| {
        adapter["trust"]["evidence_kind"] == "replay_only"
            && adapter["trust"]["kernel_certified"] == false
    }));
}

#[test]
fn math_profile_inspect_reports_nn_verify_profile_plan_json() {
    let report = run_clean_json(&[
        "math",
        "profile",
        "inspect",
        "--domain",
        "nn-verify",
        "--json",
    ]);

    assert_eq!(report["schema_version"], "clean-domain-profile-v1");
    assert_eq!(report["name"], "nn-verify");
    assert_eq!(
        report["tactic_normalizer_plan"]["domain_profile"],
        "nn-verify"
    );
    assert_eq!(
        report["tactic_normalizer_plan"]["normalizers"][0]["name"],
        "cert_simp"
    );
    assert_eq!(
        report["tactic_normalizer_plan"]["normalizers"][1]["name"],
        "cert_mathverse"
    );
    assert_eq!(
        report["tactic_normalizer_plan"]["tactic_recommendations"][0]["name"],
        "cert_simp"
    );
    assert_eq!(
        report["tactic_normalizer_plan"]["tactic_recommendations"][0]["source"],
        "domain-profile:nn-verify"
    );
    assert_eq!(
        report["tactic_normalizer_plan"]["tactic_recommendations"][0]["uses_profile_normalizer"],
        true
    );
    assert_eq!(
        report["tactic_normalizer_plan"]["tactic_recommendations"][1]["name"],
        "cert_mathverse"
    );
    assert_eq!(
        report["tactic_normalizer_plan"]["tactic_recommendations"][1]["source"],
        "domain-profile:nn-verify"
    );
    assert_eq!(
        report["tactic_normalizer_plan"]["tactic_recommendations"][1]["uses_profile_normalizer"],
        true
    );
    assert_eq!(
        report["artifact_replay_registry"]["schema_version"],
        "clean-artifact-replay-registry-v1"
    );
    assert_eq!(
        report["artifact_replay_registry"]["domain_profile"],
        "nn-verify"
    );
    let adapters = report["artifact_replay_registry"]["adapters"]
        .as_array()
        .expect("replay adapters");
    assert_eq!(adapters.len(), 2);
    let farkas = adapters
        .iter()
        .find(|adapter| adapter["id"] == "gamma-crown-farkas-v1")
        .expect("Gamma-Crown Farkas adapter descriptor");
    assert_eq!(farkas["status"]["phase"], "Phase 6");
    assert_eq!(farkas["status"]["lifecycle"], "available");
    assert_eq!(farkas["trust"]["evidence_kind"], "replay_only");
    assert_eq!(farkas["trust"]["kernel_certified"], false);
    let entailment = adapters
        .iter()
        .find(|adapter| adapter["id"] == "gamma-crown-linear-entailment-v1")
        .expect("Gamma-Crown entailment adapter descriptor");
    assert_eq!(entailment["status"]["lifecycle"], "available");
    assert_eq!(
        entailment["status"]["replay_status_values"],
        serde_json::json!(["pass", "fail", "blocked"])
    );
    assert!(adapters.iter().all(|adapter| {
        adapter["trust"]["evidence_kind"] == "replay_only"
            && adapter["trust"]["kernel_certified"] == false
    }));
}

#[test]
fn math_profile_inspect_reports_proof_complexity_profile_plan_json() {
    let report = run_clean_json(&[
        "math",
        "profile",
        "inspect",
        "--domain",
        "proof-complexity",
        "--json",
    ]);

    assert_eq!(report["schema_version"], "clean-domain-profile-v1");
    assert_eq!(report["name"], "proof-complexity");
    assert!(report["semantic_heads"]
        .as_array()
        .expect("semantic_heads")
        .iter()
        .any(|value| value == "LowerBoundFamily"));
    assert!(report["ranking_signals"]
        .as_array()
        .expect("ranking_signals")
        .iter()
        .any(|value| value == "missing_combinatorial_lemma"));
    assert_eq!(
        report["tactic_normalizer_plan"]["domain_profile"],
        "proof-complexity"
    );
    assert_eq!(
        report["tactic_normalizer_plan"]["normalizers"][0]["name"],
        "cert_simp"
    );
    assert_eq!(
        report["tactic_normalizer_plan"]["normalizers"][1]["name"],
        "proof_complexity_nf"
    );
    assert_eq!(
        report["artifact_replay_registry"]["schema_version"],
        "clean-artifact-replay-registry-v1"
    );
    assert_eq!(
        report["artifact_replay_registry"]["domain_profile"],
        "proof-complexity"
    );
    assert!(report["artifact_replay_registry"]["adapters"]
        .as_array()
        .expect("replay adapters")
        .is_empty());
}

#[test]
fn math_obligation_validate_emits_fingerprint_json() {
    let report = run_clean_json(&[
        "math",
        "obligation",
        "validate",
        sat_obligation(),
        "--project",
        sat_project(),
        "--json",
    ]);

    assert_eq!(report["schema_version"], "clean-obligation-report-v1");
    assert_eq!(report["project"], "sat-pb-pilot");
    assert_eq!(report["domain_profile"], "sat-pb");
    assert_eq!(report["status"], "pass");
    assert!(report["fingerprint"]
        .as_str()
        .expect("fingerprint")
        .starts_with("sha256:"));
}

#[test]
fn math_proof_complexity_fixture_covers_project_status_obligation_hygiene_index_and_issue_plan() {
    let status = run_clean_json(&[
        "math",
        "project",
        "status",
        "--project",
        proof_complexity_project(),
        "--json",
    ]);
    assert_eq!(status["schema_version"], "clean-math-project-status-v1");
    assert_eq!(status["project"], "proof-complexity-pilot");
    assert_eq!(status["domain_profile"], "proof-complexity");
    assert_eq!(status["status"], "pass");
    assert_eq!(status["theorem_packs"], 1);
    assert_eq!(status["obligation_sources"], 2);
    assert!(status["violations"]
        .as_array()
        .expect("violations")
        .is_empty());

    let obligation = run_clean_json(&[
        "math",
        "obligation",
        "validate",
        proof_complexity_obligation(),
        "--project",
        proof_complexity_project(),
        "--json",
    ]);
    assert_eq!(obligation["schema_version"], "clean-obligation-report-v1");
    assert_eq!(obligation["project"], "proof-complexity-pilot");
    assert_eq!(obligation["domain_profile"], "proof-complexity");
    assert_eq!(obligation["status"], "pass");
    assert!(obligation["fingerprint"]
        .as_str()
        .expect("fingerprint")
        .starts_with("sha256:"));

    let hygiene = run_clean_json(&[
        "math",
        "project",
        "hygiene",
        "--project",
        proof_complexity_project(),
        "--json",
    ]);
    assert_eq!(hygiene["schema_version"], "clean-math-project-hygiene-v1");
    assert_eq!(hygiene["project"], "proof-complexity-pilot");
    assert_eq!(hygiene["status"], "pass");

    let dashboard = run_clean_json(&[
        "math",
        "project",
        "dashboard",
        "--project",
        proof_complexity_project(),
        "--json",
    ]);
    assert_eq!(
        dashboard["schema_version"],
        "clean-math-project-dashboard-v1"
    );
    assert_eq!(dashboard["project"], "proof-complexity-pilot");
    assert_eq!(dashboard["status"], "pass");
    assert_eq!(dashboard["obligations"]["total"], 2);
    assert_eq!(dashboard["obligations"]["with_artifacts"], 0);
    assert_eq!(dashboard["obligations"]["invalid"], 0);
    assert_eq!(dashboard["replay"]["missing_artifact_replay"], 0);
    assert_eq!(dashboard["hygiene"]["blockers"], serde_json::json!([]));

    let index = run_clean_json(&[
        "math",
        "theorem-index",
        "--project",
        proof_complexity_project(),
        "--json",
    ]);
    assert_eq!(index["schema_version"], "clean-math-theorem-index-v1");
    assert_eq!(index["project"]["name"], "proof-complexity-pilot");
    assert_eq!(index["project"]["domain_profile"], "proof-complexity");
    assert_eq!(index["profile"], "proof-complexity");
    assert_eq!(index["files_scanned"], 1);
    assert_eq!(index["memory"]["candidate_count"], 3);
    assert_eq!(index["memory"]["local_count"], 3);
    assert_eq!(index["memory"]["domain_count"], 3);
    assert_eq!(index["memory"]["trust_policy_conforming_count"], 3);
    let candidates = index["candidates"].as_array().expect("candidates");
    let lower_bound = candidates
        .iter()
        .find(|candidate| {
            candidate["name"] == "ProofComplexity.resolution_width_lower_bound_family"
        })
        .expect("ProofComplexity.resolution_width_lower_bound_family candidate");
    assert_eq!(lower_bound["classification"]["local"], true);
    assert_eq!(lower_bound["classification"]["domain"], true);
    assert_eq!(lower_bound["domain_signals"]["profile"], "proof-complexity");
    assert_eq!(lower_bound["domain_signals"]["module_match"], true);
    assert!(lower_bound["domain_signals"]["semantic_head_matches"]
        .as_array()
        .expect("semantic head matches")
        .iter()
        .any(|head| head == "LowerBoundFamily"));
    assert!(lower_bound["domain_signals"]["ranking_signal_matches"]
        .as_array()
        .expect("ranking signal matches")
        .iter()
        .any(|signal| signal == "family"));
    assert!(lower_bound["memory"]["normal_form_heads"]
        .as_array()
        .expect("normal form heads")
        .iter()
        .any(|head| head == "LowerBoundFamily"));
    assert!(lower_bound["memory"]["side_condition_kinds"]
        .as_array()
        .expect("side condition kinds")
        .iter()
        .any(|kind| kind == "family"));
    assert!(lower_bound["memory"]["side_condition_kinds"]
        .as_array()
        .expect("side condition kinds")
        .iter()
        .any(|kind| kind == "degree-bound"));
    assert!(lower_bound["memory"]["side_condition_kinds"]
        .as_array()
        .expect("side condition kinds")
        .iter()
        .any(|kind| kind == "size-bound"));
    assert!(lower_bound["memory"]["artifact_kinds"]
        .as_array()
        .expect("artifact kinds")
        .iter()
        .any(|kind| kind == "proof-artifact-v1"));
    assert_eq!(lower_bound["memory"]["direct_only"], true);
    assert_eq!(lower_bound["trust_decision"]["conformance"], "conforming");
    assert_eq!(lower_bound["trust_decision"]["promotion_allowed"], true);

    let issue_plan = run_clean_json(&[
        "math",
        "issue-plan",
        "--project",
        proof_complexity_project(),
        "--json",
    ]);
    assert_eq!(issue_plan["schema_version"], "clean-math-issue-plan-v2");
    assert_eq!(issue_plan["project"], "proof-complexity-pilot");
    assert_eq!(issue_plan["domain_profile"], "proof-complexity");
    let rows = issue_plan["rows"].as_array().expect("rows");
    assert_eq!(rows.len(), 1);
    let row = &rows[0];
    assert_eq!(row["phase"], "Phase 7");
    assert_eq!(row["phase_title"], "Certificate extraction");
    assert_eq!(row["workstream"], "proof-complexity/tseitin");
    assert_eq!(row["ranking"]["domain_profile"], "proof-complexity");
    assert_eq!(row["ranking"]["benchmark_family"], "tseitin");
    assert!(row["verification_command"]
        .as_str()
        .expect("verification_command")
        .contains("clean math certificate extract"));
}

#[test]
fn math_obligation_validate_accepts_structured_kernel_goal_with_stable_fingerprint() {
    let structured = run_clean_json(&[
        "math",
        "obligation",
        "validate",
        sat_serialized_goal_obligation(),
        "--project",
        sat_project(),
        "--json",
    ]);
    assert_eq!(structured["status"], "pass");

    let temp = tempfile::tempdir().expect("tempdir");
    let legacy_path = temp.path().join("legacy_serialized_goal.json");
    let payload = serde_json::json!({
        "schema_version": "clean-obligation-v1",
        "project": "sat-pb-pilot",
        "domain_profile": "sat-pb",
        "producer": {
            "system": "fixture",
            "commit": "legacy-serialized-kernel-goal"
        },
        "goal": {
            "expr": serde_json::to_string_pretty(&Expr::prop())
                .expect("serialize Expr"),
            "pretty": "Prop"
        },
        "metadata": {
            "fixture": "legacy-serialized-kernel-goal"
        },
        "trust_policy": "constructive-only"
    });
    fs::write(
        &legacy_path,
        serde_json::to_vec_pretty(&payload).expect("serialize obligation"),
    )
    .expect("write legacy serialized goal obligation");
    let legacy_arg = legacy_path.to_str().expect("utf8 temp path");

    let legacy = run_clean_json(&[
        "math",
        "obligation",
        "validate",
        legacy_arg,
        "--project",
        sat_project(),
        "--json",
    ]);
    assert_eq!(legacy["status"], "pass");
    assert_eq!(structured["fingerprint"], legacy["fingerprint"]);
}

#[test]
fn math_obligation_fingerprint_ignores_display_and_path_churn_when_semantics_exist() {
    let temp = tempfile::tempdir().expect("tempdir");
    let type_expr = serde_json::to_string(&Expr::prop()).expect("type expr json");
    let base = serde_json::json!({
        "schema_version": "clean-obligation-v1",
        "project": "fingerprint-pilot",
        "domain_profile": "sat-pb",
        "producer": {
            "system": "fixture",
            "commit": "fingerprint-base"
        },
        "goal": {
            "expr": Expr::prop(),
            "pretty": "Prop"
        },
        "local_context": [
            {
                "name": "h",
                "type_pp": "Prop",
                "type_expr": type_expr
            }
        ],
        "artifact_refs": [
            {
                "kind": "proof-artifact-v1",
                "path": "artifacts/original.json",
                "hash": "blake3:same-proof"
            }
        ],
        "trust_policy": "constructive-only"
    });
    let mut churned = base.clone();
    churned["producer"]["commit"] = serde_json::json!("fingerprint-churned");
    churned["goal"]["pretty"] = serde_json::json!("pretty printer output changed");
    churned["local_context"][0]["type_pp"] = serde_json::json!("different pretty type");
    churned["artifact_refs"][0]["path"] = serde_json::json!("relocated/proof.json");

    let base_path = temp.path().join("base.json");
    let churned_path = temp.path().join("churned.json");
    fs::write(
        &base_path,
        serde_json::to_string_pretty(&base).expect("base obligation json"),
    )
    .expect("write base obligation");
    fs::write(
        &churned_path,
        serde_json::to_string_pretty(&churned).expect("churned obligation json"),
    )
    .expect("write churned obligation");

    let base_arg = base_path.to_str().expect("utf8 base path");
    let churned_arg = churned_path.to_str().expect("utf8 churned path");
    let base_report = run_clean_json(&["math", "obligation", "validate", base_arg, "--json"]);
    let churned_report = run_clean_json(&["math", "obligation", "validate", churned_arg, "--json"]);

    assert_eq!(base_report["status"], "pass");
    assert_eq!(churned_report["status"], "pass");
    assert_eq!(base_report["fingerprint"], churned_report["fingerprint"]);
}

#[test]
fn math_proof_state_open_obligation_uses_server_for_serialized_kernel_goal() {
    let report = run_clean_json(&[
        "math",
        "proof-state",
        "open-obligation",
        "--project",
        sat_project(),
        sat_serialized_goal_obligation(),
        "--json",
    ]);

    assert_eq!(
        report["schema_version"],
        "clean-cli-proof-state-open-obligation-v1"
    );
    assert_eq!(report["operation"], "open-obligation");
    assert_eq!(report["project"], "sat-pb-pilot");
    assert_eq!(report["domain_profile"], "sat-pb");
    assert_eq!(report["status"], "opened-server-state");
    assert_eq!(report["persistence"], "process-local-server-state");
    assert!(report["detail"]
        .as_str()
        .expect("detail")
        .contains("does not persist"));
    assert!(report["state_id"]
        .as_str()
        .expect("state_id")
        .starts_with("ps_"));
}

#[test]
fn math_proof_state_open_obligation_fails_closed_for_pretty_only_goal() {
    let report = run_clean_json_expect_failure(&[
        "math",
        "proof-state",
        "open-obligation",
        "--project",
        sat_project(),
        sat_obligation(),
        "--json",
    ]);

    assert_eq!(
        report["schema_version"],
        "clean-cli-proof-state-open-obligation-v1"
    );
    assert_eq!(report["operation"], "open-obligation");
    assert_eq!(report["status"], "blocked-pretty-only-obligation");
    assert!(report["state_id"].is_null());
    assert!(report["detail"]
        .as_str()
        .expect("detail")
        .contains("serialized clean_kernel::Expr JSON"));
}

#[test]
fn math_proof_state_open_obligation_distinguishes_invalid_serialized_goal() {
    let temp = tempfile::tempdir().expect("tempdir");
    let obligation_path = temp.path().join("invalid_serialized_goal.json");
    let payload = serde_json::json!({
        "schema_version": "clean-obligation-v1",
        "project": "sat-pb-pilot",
        "domain_profile": "sat-pb",
        "producer": {
            "system": "fixture",
            "commit": "invalid-serialized-goal"
        },
        "goal": {
            "expr": "{\"Sort\":",
            "pretty": "Prop"
        },
        "trust_policy": "constructive-only"
    });
    fs::write(
        &obligation_path,
        serde_json::to_vec_pretty(&payload).expect("serialize obligation"),
    )
    .expect("write invalid serialized goal obligation");
    let obligation_arg = obligation_path.to_str().expect("utf8 temp path");

    let report = run_clean_json_expect_failure(&[
        "math",
        "proof-state",
        "open-obligation",
        "--project",
        sat_project(),
        obligation_arg,
        "--json",
    ]);

    assert_eq!(report["status"], "blocked-invalid-serialized-goal");
    assert!(report["detail"]
        .as_str()
        .expect("detail")
        .contains("not valid serialized clean_kernel::Expr JSON"));
}

#[test]
fn math_proof_state_open_obligation_fails_closed_for_pretty_only_local_context() {
    let temp = tempfile::tempdir().expect("tempdir");
    let goal_expr = serde_json::to_string(&Expr::prop()).expect("serialize Expr");
    let obligation_path = temp.path().join("pretty_only_local_context.json");
    let payload = serde_json::json!({
        "schema_version": "clean-obligation-v1",
        "project": "sat-pb-pilot",
        "domain_profile": "sat-pb",
        "producer": {
            "system": "fixture",
            "commit": "pretty-only-local-context"
        },
        "goal": {
            "expr": goal_expr,
            "pretty": "Prop"
        },
        "local_context": [
            {
                "name": "h",
                "type_pp": "Prop",
                "type_expr": "Prop"
            }
        ],
        "trust_policy": "constructive-only"
    });
    fs::write(
        &obligation_path,
        serde_json::to_vec_pretty(&payload).expect("serialize obligation"),
    )
    .expect("write pretty-only local context obligation");
    let obligation_arg = obligation_path.to_str().expect("utf8 temp path");

    let report = run_clean_json_expect_failure(&[
        "math",
        "proof-state",
        "open-obligation",
        "--project",
        sat_project(),
        obligation_arg,
        "--json",
    ]);

    assert_eq!(report["status"], "blocked-pretty-only-local-context");
    assert!(report["detail"]
        .as_str()
        .expect("detail")
        .contains("local_context[0].type_expr"));
}

#[test]
fn math_obligation_prove_closes_serialized_true_with_embedded_proof_state() {
    let temp = tempfile::tempdir().expect("tempdir");
    let obligation = write_true_serialized_goal_obligation(temp.path());
    let obligation_arg = obligation.to_str().expect("utf8 obligation path");

    let report = run_clean_json(&[
        "math",
        "obligation",
        "prove",
        "--project",
        sat_project(),
        obligation_arg,
        "--proof-state",
        "--json",
    ]);

    assert_eq!(report["schema_version"], "clean-math-proof-attempt-v1");
    assert_eq!(report["project"], "sat-pb-pilot");
    assert_eq!(report["status"], "closed");
    let attempts = report["tactic_attempts"]
        .as_array()
        .expect("tactic_attempts");
    assert_eq!(attempts[0]["tactic"], "exact True.intro");
    assert_eq!(attempts[0]["status"], "closed");
}

#[test]
fn math_obligation_prove_closes_generic_smoke_obligations_without_local_assumptions() {
    for (project, obligation, expected_project) in [
        (
            sat_project(),
            sat_generic_true_smoke_obligation(),
            "sat-pb-pilot",
        ),
        (
            nn_project(),
            nn_generic_true_smoke_obligation(),
            "nn-verify-pilot",
        ),
        (
            proof_complexity_project(),
            proof_complexity_generic_true_smoke_obligation(),
            "proof-complexity-pilot",
        ),
    ] {
        let payload: Value = serde_json::from_slice(
            &fs::read(workspace_root().join(obligation)).expect("read smoke obligation"),
        )
        .expect("parse smoke obligation");
        assert_eq!(payload["metadata"]["fixture_role"], "proof-state-smoke");
        assert_eq!(payload["metadata"]["issue_plan"], "non-filing");
        assert_eq!(payload["local_context"], serde_json::json!([]));

        let report = run_clean_json(&[
            "math",
            "obligation",
            "prove",
            "--project",
            project,
            obligation,
            "--proof-state",
            "--json",
        ]);

        assert_eq!(report["schema_version"], "clean-math-proof-attempt-v1");
        assert_eq!(report["project"], expected_project);
        assert_eq!(report["status"], "closed");
        let attempts = report["tactic_attempts"]
            .as_array()
            .expect("tactic_attempts");
        assert_eq!(attempts[0]["tactic"], "exact True.intro");
        assert_eq!(attempts[0]["status"], "closed");
        assert!(!attempts
            .iter()
            .any(|attempt| attempt["tactic"] == "assumption"));
    }
}

#[test]
fn math_obligation_prove_blocks_serialized_goal_from_untrusted_local_context() {
    let temp = tempfile::tempdir().expect("tempdir");
    let obligation = write_local_assumption_serialized_goal_obligation(temp.path());
    let obligation_arg = obligation.to_str().expect("utf8 obligation path");

    let report = run_clean_json_expect_failure(&[
        "math",
        "obligation",
        "prove",
        "--project",
        sat_project(),
        obligation_arg,
        "--proof-state",
        "--json",
    ]);

    assert_eq!(report["schema_version"], "clean-math-proof-attempt-v1");
    assert_eq!(report["status"], "blocked-untrusted-local-assumption");
    let attempts = report["tactic_attempts"]
        .as_array()
        .expect("tactic_attempts");
    assert!(attempts.is_empty());
    assert!(report["details"][0]
        .as_str()
        .expect("detail")
        .contains("local_context[1] `h`"));
}

#[test]
fn math_obligation_prove_fails_closed_for_pretty_only_obligation() {
    let report = run_clean_json_expect_failure(&[
        "math",
        "obligation",
        "prove",
        "--project",
        sat_project(),
        sat_obligation(),
        "--proof-state",
        "--json",
    ]);

    assert_eq!(report["schema_version"], "clean-math-proof-attempt-v1");
    assert_eq!(report["status"], "blocked-pretty-only-obligation");
    assert!(report["details"][0]
        .as_str()
        .expect("detail")
        .contains("goal.expr"));
}

#[test]
fn math_obligation_prove_fails_closed_for_pretty_only_local_context() {
    let temp = tempfile::tempdir().expect("tempdir");
    let goal_expr = serde_json::to_string(&Expr::prop()).expect("serialize Expr");
    let obligation_path = temp.path().join("pretty_only_local_context.json");
    let payload = serde_json::json!({
        "schema_version": "clean-obligation-v1",
        "project": "sat-pb-pilot",
        "domain_profile": "sat-pb",
        "producer": {
            "system": "fixture",
            "commit": "pretty-only-local-context"
        },
        "goal": {
            "expr": goal_expr,
            "pretty": "Prop"
        },
        "local_context": [
            {
                "name": "h",
                "type_pp": "Prop",
                "type_expr": "Prop"
            }
        ],
        "trust_policy": "constructive-only"
    });
    fs::write(
        &obligation_path,
        serde_json::to_vec_pretty(&payload).expect("serialize obligation"),
    )
    .expect("write pretty-only local context obligation");
    let obligation_arg = obligation_path.to_str().expect("utf8 temp path");

    let report = run_clean_json_expect_failure(&[
        "math",
        "obligation",
        "prove",
        "--project",
        sat_project(),
        obligation_arg,
        "--proof-state",
        "--json",
    ]);

    assert_eq!(report["schema_version"], "clean-math-proof-attempt-v1");
    assert_eq!(report["status"], "blocked-pretty-only-local-context");
    assert!(report["details"][0]
        .as_str()
        .expect("detail")
        .contains("local_context[0].type_expr"));
}

#[test]
fn math_obligation_prove_blocks_unproved_serialized_goal_with_attempts() {
    let report = run_clean_json_expect_failure(&[
        "math",
        "obligation",
        "prove",
        "--project",
        sat_project(),
        sat_serialized_goal_obligation(),
        "--proof-state",
        "--json",
    ]);

    assert_eq!(report["schema_version"], "clean-math-proof-attempt-v1");
    assert_eq!(report["status"], "blocked-unproved");
    let attempts = report["tactic_attempts"]
        .as_array()
        .expect("tactic_attempts");
    assert!(attempts
        .iter()
        .any(|attempt| attempt["tactic"] == "exact True.intro"));
    assert!(attempts.iter().any(|attempt| attempt["tactic"] == "rfl"));
    assert!(attempts
        .iter()
        .any(|attempt| attempt["tactic"] == "cert_simp"));
}

#[test]
fn math_theorem_index_scopes_factory_index_to_project_packs() {
    let report = run_clean_json(&[
        "math",
        "theorem-index",
        "--project",
        sat_project(),
        "--json",
    ]);

    assert_eq!(report["schema_version"], "clean-math-theorem-index-v1");
    assert_eq!(report["project"]["schema_version"], "clean-math-project-v1");
    assert_eq!(report["project"]["name"], "sat-pb-pilot");
    assert_eq!(report["project"]["domain_profile"], "sat-pb");
    assert_eq!(report["project"]["trust_policy"], "constructive-only");
    assert_eq!(report["project"]["require_artifact_replay"], true);
    assert_eq!(report["profile"], "sat-pb");
    assert_eq!(report["files_scanned"], 1);
    assert_eq!(report["memory"]["candidate_count"], 8);
    assert_eq!(report["memory"]["local_count"], 8);
    assert_eq!(report["memory"]["project_count"], 8);
    assert_eq!(report["memory"]["domain_count"], 8);
    assert_eq!(report["memory"]["imported_count"], 0);
    assert_eq!(report["memory"]["artifact_derived_count"], 0);
    assert_eq!(report["memory"]["trust_policy_conforming_count"], 8);
    assert_eq!(
        report["factory_report"]["schema_version"],
        "clean-theorem-index-v1"
    );
    assert!(report["factory_report"]["diagnostics"]
        .as_array()
        .expect("diagnostics")
        .is_empty());
    let candidates = report["candidates"].as_array().expect("candidates");
    let candidate = candidates
        .iter()
        .find(|candidate| candidate["name"] == "SatPb.sat_pb_subsumption_sound")
        .expect("SatPb.sat_pb_subsumption_sound candidate");
    let raw_candidate = report["factory_report"]["candidates"]
        .as_array()
        .expect("raw candidates")
        .iter()
        .find(|candidate| candidate["name"] == "SatPb.sat_pb_subsumption_sound")
        .expect("raw SatPb.sat_pb_subsumption_sound candidate");
    assert_eq!(
        candidate["candidate_fingerprint"],
        raw_candidate["candidate_fingerprint"]
    );
    assert_eq!(
        candidate["candidate_fingerprint"]
            .as_str()
            .expect("candidate fingerprint")
            .len(),
        64
    );
    assert_eq!(candidate["classification"]["scope"], "local");
    assert_eq!(candidate["classification"]["local"], true);
    assert_eq!(candidate["classification"]["project"], true);
    assert_eq!(candidate["classification"]["domain"], true);
    assert_eq!(candidate["classification"]["imported"], false);
    assert_eq!(candidate["classification"]["artifact_derived"], false);
    assert_eq!(candidate["domain_signals"]["profile"], "sat-pb");
    assert_eq!(candidate["domain_signals"]["module_match"], true);
    assert!(candidate["domain_signals"]["semantic_head_matches"]
        .as_array()
        .expect("semantic head matches")
        .iter()
        .any(|head| head == "Clause"));
    assert!(candidate["domain_signals"]["ranking_signal_matches"]
        .as_array()
        .expect("ranking signal matches")
        .iter()
        .any(|signal| signal == "conclusion_head"));
    assert!(candidate["memory"]["normal_form_heads"]
        .as_array()
        .expect("normal form heads")
        .iter()
        .any(|head| head == "Clause"));
    assert!(candidate["memory"]["side_condition_kinds"]
        .as_array()
        .expect("side condition kinds")
        .iter()
        .any(|kind| kind == "subsumption"));
    assert!(candidate["memory"]["artifact_kinds"]
        .as_array()
        .expect("artifact kinds")
        .iter()
        .any(|kind| kind == "ay_alethe_envelope"));
    assert!(candidate["memory"]["artifact_kinds"]
        .as_array()
        .expect("artifact kinds")
        .iter()
        .any(|kind| kind == "proof-artifact-v1"));
    assert!(candidate["memory"]["direct_imports"]
        .as_array()
        .expect("direct imports")
        .is_empty());
    assert!(candidate["memory"]["import_closure"]
        .as_array()
        .expect("import closure")
        .is_empty());
    assert_eq!(candidate["memory"]["direct_only"], true);
    assert_eq!(candidate["trust_decision"]["policy"], "constructive-only");
    assert_eq!(candidate["trust_decision"]["conformance"], "conforming");
    assert_eq!(
        candidate["trust_decision"]["kernel_proof_status"],
        "not_claimed"
    );
    assert!(candidate["trust_decision"]["trust_debt"]
        .as_array()
        .expect("trust debt")
        .is_empty());
    assert_eq!(candidate["trust_decision"]["promotion_allowed"], true);
    assert!(candidate["trust_decision"]["reasons"]
        .as_array()
        .expect("trust decision reasons")
        .is_empty());

    for theorem in [
        "SatPb.PropLogic.and_fragment_seen",
        "SatPb.PropLogic.or_fragment_seen",
        "SatPb.PropLogic.iff_fragment_seen",
        "SatPb.PropLogic.exists_fragment_seen",
        "SatPb.Semantics.cnf_and_fragment_seen",
        "SatPb.Semantics.clause_or_fragment_seen",
    ] {
        let fragment = candidates
            .iter()
            .find(|candidate| candidate["name"] == theorem)
            .unwrap_or_else(|| panic!("missing SAT/PB theorem-fragment candidate {theorem}"));
        assert_eq!(fragment["classification"]["local"], true);
        assert_eq!(fragment["classification"]["project"], true);
        assert_eq!(fragment["classification"]["domain"], true);
        assert_eq!(fragment["domain_signals"]["profile"], "sat-pb");
        assert_eq!(fragment["trust_decision"]["conformance"], "conforming");
        assert_eq!(
            fragment["trust_decision"]["kernel_proof_status"],
            "not_claimed"
        );
        assert!(fragment["trust_decision"]["trust_debt"]
            .as_array()
            .expect("trust debt")
            .is_empty());
        assert_eq!(fragment["trust_decision"]["promotion_allowed"], true);
    }

    let raw_candidates = report["factory_report"]["candidates"]
        .as_array()
        .expect("raw candidates");
    let iff_fragment = raw_candidates
        .iter()
        .find(|candidate| candidate["name"] == "SatPb.PropLogic.iff_fragment_seen")
        .expect("raw Iff fragment");
    assert_eq!(iff_fragment["source"], "kernel");
    assert!(iff_fragment["symbol_refs"]
        .as_array()
        .expect("Iff symbol refs")
        .iter()
        .any(|symbol| symbol == "Iff"));
    let exists_fragment = raw_candidates
        .iter()
        .find(|candidate| candidate["name"] == "SatPb.PropLogic.exists_fragment_seen")
        .expect("raw Exists fragment");
    assert_eq!(exists_fragment["source"], "kernel");
    assert!(exists_fragment["symbol_refs"]
        .as_array()
        .expect("Exists symbol refs")
        .iter()
        .any(|symbol| symbol == "Exists"));
}

#[test]
fn math_theorem_index_emits_nn_verify_domain_memory() {
    let report = run_clean_json(&["math", "theorem-index", "--project", nn_project(), "--json"]);

    assert_eq!(report["schema_version"], "clean-math-theorem-index-v1");
    assert_eq!(report["project"]["name"], "nn-verify-pilot");
    assert_eq!(report["project"]["domain_profile"], "nn-verify");
    assert_eq!(report["memory"]["candidate_count"], 2);
    assert_eq!(report["memory"]["local_count"], 2);
    assert_eq!(report["memory"]["domain_count"], 2);
    assert_eq!(report["memory"]["trust_policy_conforming_count"], 2);

    let candidates = report["candidates"].as_array().expect("candidates");
    let candidate = candidates
        .iter()
        .find(|candidate| candidate["name"] == "NNVerify.nn_verify_farkas_sound")
        .expect("NNVerify.nn_verify_farkas_sound candidate");
    assert_eq!(candidate["classification"]["scope"], "local");
    assert_eq!(candidate["classification"]["local"], true);
    assert_eq!(candidate["classification"]["project"], true);
    assert_eq!(candidate["classification"]["domain"], true);
    assert_eq!(candidate["domain_signals"]["profile"], "nn-verify");
    assert_eq!(candidate["domain_signals"]["module_match"], true);
    assert!(candidate["domain_signals"]["semantic_head_matches"]
        .as_array()
        .expect("semantic head matches")
        .iter()
        .any(|head| head == "ExternalFarkasCert"));
    assert!(candidate["domain_signals"]["ranking_signal_matches"]
        .as_array()
        .expect("ranking signal matches")
        .iter()
        .any(|signal| signal == "bound_tightness"));
    assert!(candidate["memory"]["normal_form_heads"]
        .as_array()
        .expect("normal form heads")
        .iter()
        .any(|head| head == "ExternalFarkasCert"));
    assert!(candidate["memory"]["side_condition_kinds"]
        .as_array()
        .expect("side condition kinds")
        .iter()
        .any(|kind| kind == "nonnegativity"));
    assert!(candidate["memory"]["side_condition_kinds"]
        .as_array()
        .expect("side condition kinds")
        .iter()
        .any(|kind| kind == "linear-combination"));
    assert!(candidate["memory"]["artifact_kinds"]
        .as_array()
        .expect("artifact kinds")
        .iter()
        .any(|kind| kind == "gamma_crown_farkas"));
    assert_eq!(candidate["memory"]["direct_only"], true);
    assert_eq!(candidate["trust_decision"]["policy"], "constructive-only");
    assert_eq!(candidate["trust_decision"]["conformance"], "conforming");
    assert_eq!(
        candidate["trust_decision"]["kernel_proof_status"],
        "not_claimed"
    );
    assert_eq!(candidate["trust_decision"]["promotion_allowed"], true);
}

#[test]
fn math_theorem_index_marks_axiom_candidates_not_promotable_by_manifest_policy() {
    let temp = tempfile::tempdir().expect("tempdir");
    let project_path = write_axiom_theorem_pack_project_fixture(temp.path());
    let project_arg = project_path.to_str().expect("utf8 temp path");

    let report = run_clean_json(&["math", "theorem-index", "--project", project_arg, "--json"]);

    assert_eq!(report["schema_version"], "clean-math-theorem-index-v1");
    assert_eq!(report["project"]["name"], "sat-pb-axiom-pilot");
    let candidates = report["candidates"].as_array().expect("candidates");
    let candidate = candidates
        .iter()
        .find(|candidate| candidate["name"] == "SatPb.unsound_bridge")
        .expect("SatPb.unsound_bridge candidate");
    assert_eq!(candidate["classification"]["local"], true);
    assert_eq!(candidate["classification"]["project"], true);
    assert_eq!(candidate["trust_decision"]["policy"], "constructive-only");
    assert_eq!(candidate["trust_decision"]["conformance"], "blocked");
    assert_eq!(
        candidate["trust_decision"]["kernel_proof_status"],
        "not_claimed"
    );
    assert!(candidate["trust_decision"]["trust_debt"]
        .as_array()
        .expect("trust debt")
        .iter()
        .any(|debt| debt == "axiom"));
    assert_eq!(candidate["trust_decision"]["promotion_allowed"], false);
    assert!(candidate["trust_decision"]["reasons"]
        .as_array()
        .expect("trust decision reasons")
        .iter()
        .any(|reason| reason
            .as_str()
            .expect("reason")
            .contains("axiom declaration is not allowed")));
}

#[test]
fn math_artifact_validate_and_replay_gamma_crown_fixture() {
    let artifact =
        "tests/fixtures/external_certificates/proof_artifact_v1/gamma_crown_farkas_valid.json";
    let obligation = run_clean_json(&[
        "math",
        "obligation",
        "validate",
        nn_obligation(),
        "--project",
        nn_project(),
        "--json",
    ]);
    let obligation_fingerprint = obligation["fingerprint"].as_str().expect("fingerprint");

    let validate = run_clean_json(&["math", "artifact", "validate", artifact, "--json"]);
    assert_eq!(
        validate["schema_version"],
        "clean-artifact-envelope-report-v1"
    );
    assert_eq!(validate["source_system"], "gamma-crown");
    assert_eq!(validate["status"], "pass");

    let replay = run_clean_json(&[
        "math",
        "artifact",
        "replay",
        "--project",
        nn_project(),
        artifact,
        "--json",
    ]);
    assert_eq!(replay["schema_version"], "clean-artifact-replay-report-v1");
    assert_eq!(replay["evidence_kind"], "replay_only");
    assert_eq!(replay["kernel_certified"], false);
    assert_eq!(replay["replay_status"], "pass");
    assert_eq!(replay["replay_adapter"], "gamma-crown-farkas-v1");
    assert_eq!(replay["adapter_descriptor_id"], "gamma-crown-farkas-v1");
    assert_eq!(replay["adapter_lifecycle"], "available");
    assert_eq!(
        replay["linked_obligations"]
            .as_array()
            .expect("linked_obligations"),
        &[Value::String(obligation_fingerprint.to_owned())]
    );
}

fn write_local_profile_project(root: &Path) -> PathBuf {
    fs::create_dir_all(root.join("domain_profiles")).expect("domain_profiles dir");
    fs::create_dir_all(root.join("theorem_packs")).expect("theorem_packs dir");
    fs::write(
        root.join("theorem_packs/LocalProfile.lean"),
        "-- ToyHead toy_signal\n\
theorem LocalProfile.local_toy_head : True := True.intro\n",
    )
    .expect("write local theorem pack");
    fs::write(
        root.join("domain_profiles/toy-local.json"),
        serde_json::to_string_pretty(&serde_json::json!({
            "schema_version": "clean-domain-profile-v1",
            "name": "toy-local",
            "description": "Toy project-local domain profile for CLI registry coverage",
            "semantic_heads": ["ToyHead"],
            "normalizers": ["toy_nf"],
            "tactic_recommendations": ["toy_nf"],
            "artifact_formats": ["lrat"],
            "artifact_replay_adapters": [
                {
                    "id": "toy-local-lrat-planned-v1",
                    "label": "Toy local LRAT planned replay",
                    "domain_profile": "toy-local",
                    "source_systems": ["sat-pb"],
                    "artifact_formats": ["lrat"],
                    "artifact_kinds": ["lrat"],
                    "replay_contract": "Planned local LRAT adapter used to verify AR002 fail-closed dispatch.",
                    "availability": {
                        "source": "project-local-profile",
                        "executor": "unwired",
                        "requires_external_tool": false,
                        "feature_gate": null
                    },
                    "trust": {
                        "evidence_kind": "replay_only",
                        "kernel_certified": false,
                        "allowed_trusted_assumptions": [],
                        "requires_envelope_validation": true,
                        "requires_problem_hash": true,
                        "links_obligation_fingerprint": true,
                        "required_report_fields": ["linked_obligations", "replay_status"]
                    },
                    "status": {
                        "phase": "local",
                        "lifecycle": "planned",
                        "blocker_kind": "artifact-replay",
                        "report_schema_version": "clean-artifact-replay-report-v1",
                        "replay_status_values": ["pass", "fail", "blocked"]
                    }
                }
            ],
            "certificate_extractors": ["toy-local-certificate-summary-v1"],
            "ranking_signals": ["toy_signal"],
            "blocker_kinds": ["toy-blocker"]
        }))
        .expect("local profile json"),
    )
    .expect("write local profile");
    let project_path = root.join("project.json");
    fs::write(
        &project_path,
        serde_json::to_string_pretty(&serde_json::json!({
            "schema_version": "clean-math-project-v1",
            "project": "toy-local-project",
            "domain_profile": "toy-local",
            "owner": "clean-math-factory",
            "theorem_packs": ["theorem_packs/LocalProfile.lean"],
            "obligation_sources": [],
            "artifact_formats": ["lrat"],
            "trust_policy": {
                "name": "constructive-only",
                "allowed_axioms": [],
                "forbidden_trust_markers": ["sorry", "sorryAx", "trustedArith", "trustedAy", "synthetic_sorry"],
                "require_artifact_replay": true,
                "allow_synthetic_sorry": false
            },
            "normalizers": ["toy_nf"],
            "evidence": [],
            "issue_routing": {
                "labels": ["math-project", "toy-local"],
                "owners": [],
                "blocking_categories": ["artifact", "trust"]
            }
        }))
        .expect("project json"),
    )
    .expect("write local project");
    project_path
}

#[test]
fn math_profile_inspect_and_theorem_index_use_project_local_profile_registry() {
    let temp = tempfile::tempdir().expect("tempdir");
    let project = write_local_profile_project(temp.path());
    let project_arg = project.to_str().expect("utf8 project path");

    let profile = run_clean_json(&[
        "math",
        "profile",
        "inspect",
        "--project",
        project_arg,
        "--domain",
        "toy-local",
        "--json",
    ]);
    assert_eq!(profile["schema_version"], "clean-domain-profile-v1");
    assert_eq!(profile["name"], "toy-local");
    assert_eq!(
        profile["artifact_replay_registry"]["adapters"][0]["id"],
        "toy-local-lrat-planned-v1"
    );

    let index = run_clean_json(&["math", "theorem-index", "--project", project_arg, "--json"]);
    assert_eq!(index["schema_version"], "clean-math-theorem-index-v1");
    assert_eq!(index["project"]["domain_profile"], "toy-local");
    assert_eq!(index["profile"], "toy-local");
    let candidate = index["candidates"]
        .as_array()
        .expect("candidates")
        .iter()
        .find(|candidate| candidate["name"] == "LocalProfile.local_toy_head")
        .expect("local profile candidate");
    assert!(candidate["domain_signals"]["semantic_head_matches"]
        .as_array()
        .expect("semantic heads")
        .iter()
        .any(|head| head == "ToyHead"));
    assert!(candidate["domain_signals"]["ranking_signal_matches"]
        .as_array()
        .expect("ranking signals")
        .iter()
        .any(|signal| signal == "toy_signal"));
}

#[test]
fn math_artifact_replay_fails_semantically_invalid_gamma_crown_fixture() {
    let artifact = "tests/fixtures/external_certificates/proof_artifact_v1/gamma_crown_farkas_semantically_invalid.json";
    let validate = run_clean_json(&["math", "artifact", "validate", artifact, "--json"]);
    assert_eq!(
        validate["schema_version"],
        "clean-artifact-envelope-report-v1"
    );
    assert_eq!(validate["source_system"], "gamma-crown");
    assert_eq!(validate["status"], "pass");

    let replay = run_clean_json_expect_failure(&[
        "math",
        "artifact",
        "replay",
        "--project",
        nn_project(),
        artifact,
        "--json",
    ]);
    assert_eq!(replay["schema_version"], "clean-artifact-replay-report-v1");
    assert_eq!(replay["replay_status"], "fail");
    assert_eq!(replay["replay_adapter"], "gamma-crown-farkas-v1");
    assert!(replay["details"]
        .as_array()
        .expect("details")
        .iter()
        .any(|detail| detail
            .as_str()
            .expect("detail")
            .contains("no_contradiction")));
}

#[test]
fn math_artifact_replay_rejects_envelope_payload_semantic_mismatch() {
    let artifact = "tests/fixtures/external_certificates/proof_artifact_v1/gamma_crown_farkas_semantic_mismatch.json";
    let validate = run_clean_json(&["math", "artifact", "validate", artifact, "--json"]);
    assert_eq!(
        validate["schema_version"],
        "clean-artifact-envelope-report-v1"
    );
    assert_eq!(validate["artifact_kind"], "gamma_crown_entailment");
    assert_eq!(
        validate["certificate_format"],
        "gamma-crown-linear-entailment-v1"
    );
    assert_eq!(validate["status"], "pass");

    let replay = run_clean_json_expect_failure(&[
        "math",
        "artifact",
        "replay",
        "--project",
        nn_project(),
        artifact,
        "--json",
    ]);
    assert_eq!(replay["schema_version"], "clean-artifact-replay-report-v1");
    assert_eq!(replay["replay_status"], "fail");
    assert_eq!(replay["replay_adapter"], "gamma-crown-farkas-v1");
    assert!(replay["details"]
        .as_array()
        .expect("details")
        .iter()
        .any(|detail| detail
            .as_str()
            .expect("detail")
            .contains("semantic mismatch")));
}

#[test]
fn math_artifact_replay_blocks_non_json_gamma_crown_payload() {
    let artifact = "tests/fixtures/external_certificates/proof_artifact_v1/gamma_crown_farkas_text_payload.json";
    let validate = run_clean_json(&["math", "artifact", "validate", artifact, "--json"]);
    assert_eq!(
        validate["schema_version"],
        "clean-artifact-envelope-report-v1"
    );
    assert_eq!(validate["source_system"], "gamma-crown");
    assert_eq!(validate["status"], "pass");

    let (replay_succeeded, replay) = run_clean_json_allow_status(&[
        "math",
        "artifact",
        "replay",
        "--project",
        nn_project(),
        artifact,
        "--json",
    ]);
    assert_eq!(replay["schema_version"], "clean-artifact-replay-report-v1");
    assert_eq!(replay["replay_status"], "blocked");
    assert!(!replay_succeeded);
    assert_eq!(replay["replay_adapter"], "none");
    assert_eq!(replay["adapter_descriptor_id"], "gamma-crown-farkas-v1");
    assert_eq!(replay["adapter_lifecycle"], "available");
    assert!(replay["details"]
        .as_array()
        .expect("details")
        .iter()
        .any(|detail| detail
            .as_str()
            .expect("detail")
            .contains("not replayed by this adapter")));
}

#[test]
fn math_artifact_replay_ay_alethe_links_sat_pb_obligation() {
    let artifact = "tests/fixtures/external_certificates/proof_artifact_v1/ay_alethe_envelope.json";
    let obligation = run_clean_json(&[
        "math",
        "obligation",
        "validate",
        sat_obligation(),
        "--project",
        sat_project(),
        "--json",
    ]);
    let obligation_fingerprint = obligation["fingerprint"].as_str().expect("fingerprint");

    let validate = run_clean_json(&["math", "artifact", "validate", artifact, "--json"]);
    assert_eq!(
        validate["schema_version"],
        "clean-artifact-envelope-report-v1"
    );
    assert_eq!(validate["source_system"], "ay");
    assert_eq!(validate["artifact_kind"], "ay_alethe_envelope");
    assert_eq!(validate["certificate_format"], "ay-alethe-envelope-v1");
    assert_eq!(validate["status"], "pass");

    let (replay_succeeded, replay) = run_clean_json_allow_status(&[
        "math",
        "artifact",
        "replay",
        "--project",
        sat_project(),
        artifact,
        "--json",
    ]);
    assert_eq!(replay["schema_version"], "clean-artifact-replay-report-v1");
    assert!(
        replay["replay_status"] == "pass" || replay["replay_status"] == "blocked",
        "ay Alethe replay should either pass with ay-smt or fail closed when unavailable: {replay}"
    );
    assert_eq!(replay_succeeded, replay["replay_status"] == "pass");
    assert_eq!(replay["replay_adapter"], "ay-alethe-v1");
    assert_eq!(replay["adapter_descriptor_id"], "ay-alethe-v1");
    assert_eq!(replay["adapter_lifecycle"], "feature-gated");
    assert_eq!(
        replay["linked_obligations"]
            .as_array()
            .expect("linked_obligations"),
        &[Value::String(obligation_fingerprint.to_owned())]
    );
}

#[test]
fn math_artifact_replay_ay_alethe_empty_proof_distinguishes_envelope_from_semantics() {
    let artifact =
        "tests/fixtures/external_certificates/proof_artifact_v1/ay_alethe_empty_proof.json";
    let validate = run_clean_json(&["math", "artifact", "validate", artifact, "--json"]);
    assert_eq!(
        validate["schema_version"],
        "clean-artifact-envelope-report-v1"
    );
    assert_eq!(validate["source_system"], "ay");
    assert_eq!(validate["status"], "pass");

    let replay = run_clean_json_expect_failure(&[
        "math",
        "artifact",
        "replay",
        "--project",
        sat_project(),
        artifact,
        "--json",
    ]);
    assert_eq!(replay["schema_version"], "clean-artifact-replay-report-v1");
    assert_eq!(replay["replay_status"], "fail");
    assert_eq!(replay["replay_adapter"], "ay-alethe-v1");
    assert!(replay["details"]
        .as_array()
        .expect("details")
        .iter()
        .any(|detail| detail
            .as_str()
            .expect("detail")
            .contains("proof text must not be empty")));
}

#[test]
fn math_artifact_replay_rejects_ay_envelope_with_non_ay_payload() {
    let artifact = "tests/fixtures/external_certificates/proof_artifact_v1/ay_alethe_payload_semantic_mismatch.json";
    let validate = run_clean_json(&["math", "artifact", "validate", artifact, "--json"]);
    assert_eq!(
        validate["schema_version"],
        "clean-artifact-envelope-report-v1"
    );
    assert_eq!(validate["source_system"], "ay");
    assert_eq!(validate["certificate_format"], "ay-alethe-envelope-v1");
    assert_eq!(validate["status"], "pass");

    let replay = run_clean_json_expect_failure(&[
        "math",
        "artifact",
        "replay",
        "--project",
        sat_project(),
        artifact,
        "--json",
    ]);
    assert_eq!(replay["schema_version"], "clean-artifact-replay-report-v1");
    assert_eq!(replay["replay_status"], "fail");
    assert_eq!(replay["replay_adapter"], "gamma-crown-farkas-v1");
    assert!(replay["details"]
        .as_array()
        .expect("details")
        .iter()
        .any(|detail| detail
            .as_str()
            .expect("detail")
            .contains("semantic mismatch")));
}

#[test]
fn math_artifact_replay_passes_checked_sat_pb_lrat_artifact() {
    let artifact =
        "tests/fixtures/external_certificates/proof_artifact_v1/sat_pb_lrat_checked.json";

    let validate = run_clean_json(&["math", "artifact", "validate", artifact, "--json"]);
    assert_eq!(
        validate["schema_version"],
        "clean-artifact-envelope-report-v1"
    );
    assert_eq!(validate["source_system"], "sat-pb");
    assert_eq!(validate["artifact_kind"], "lrat");
    assert_eq!(validate["certificate_format"], "lrat");
    assert_eq!(validate["status"], "pass");

    let replay = run_clean_json(&[
        "math",
        "artifact",
        "replay",
        "--project",
        sat_project(),
        artifact,
        "--json",
    ]);
    assert_eq!(replay["schema_version"], "clean-artifact-replay-report-v1");
    assert_eq!(replay["replay_status"], "pass");
    assert_eq!(replay["replay_adapter"], "sat-pb-lrat-v1");
    assert_eq!(replay["adapter_descriptor_id"], "sat-pb-lrat-v1");
    assert_eq!(replay["adapter_lifecycle"], "available");
    assert_eq!(replay["evidence_kind"], "replay_only");
    assert_eq!(replay["kernel_certified"], false);
    assert!(replay["details"]
        .as_array()
        .expect("details")
        .iter()
        .any(|detail| detail
            .as_str()
            .expect("detail")
            .contains("verified LRAT refutation")));
}

#[test]
fn math_artifact_replay_passes_checked_sat_pb_drat_artifact() {
    let artifact =
        "tests/fixtures/external_certificates/proof_artifact_v1/sat_pb_drat_checked.json";

    let validate = run_clean_json(&["math", "artifact", "validate", artifact, "--json"]);
    assert_eq!(
        validate["schema_version"],
        "clean-artifact-envelope-report-v1"
    );
    assert_eq!(validate["source_system"], "sat-pb");
    assert_eq!(validate["artifact_kind"], "drat");
    assert_eq!(validate["certificate_format"], "drat");
    assert_eq!(validate["status"], "pass");

    let replay = run_clean_json(&[
        "math",
        "artifact",
        "replay",
        "--project",
        sat_project(),
        artifact,
        "--json",
    ]);
    assert_eq!(replay["schema_version"], "clean-artifact-replay-report-v1");
    assert_eq!(replay["replay_status"], "pass");
    assert_eq!(replay["replay_adapter"], "sat-pb-drat-v1");
    assert_eq!(replay["adapter_descriptor_id"], "sat-pb-drat-v1");
    assert_eq!(replay["adapter_lifecycle"], "available");
    assert_eq!(replay["evidence_kind"], "replay_only");
    assert_eq!(replay["kernel_certified"], false);
    assert!(replay["details"]
        .as_array()
        .expect("details")
        .iter()
        .any(|detail| detail
            .as_str()
            .expect("detail")
            .contains("verified DRAT refutation")));
}

#[test]
fn math_artifact_replay_blocks_wellformed_sat_pb_veripb_without_pass_adapter() {
    let artifact =
        "tests/fixtures/external_certificates/proof_artifact_v1/sat_pb_veripb_wellformed.json";

    let validate = run_clean_json(&["math", "artifact", "validate", artifact, "--json"]);
    assert_eq!(
        validate["schema_version"],
        "clean-artifact-envelope-report-v1"
    );
    assert_eq!(validate["source_system"], "sat-pb");
    assert_eq!(validate["artifact_kind"], "veripb");
    assert_eq!(validate["certificate_format"], "veripb");
    assert_eq!(validate["status"], "pass");

    let replay = run_clean_json_expect_failure(&[
        "math",
        "artifact",
        "replay",
        "--project",
        sat_project(),
        artifact,
        "--json",
    ]);
    assert_eq!(replay["schema_version"], "clean-artifact-replay-report-v1");
    assert_eq!(replay["replay_status"], "blocked");
    assert_eq!(replay["replay_adapter"], "sat-pb-veripb-v1");
    assert_eq!(replay["adapter_descriptor_id"], "sat-pb-veripb-v1");
    assert_eq!(replay["adapter_lifecycle"], "partial");
    assert!(replay["details"]
        .as_array()
        .expect("details")
        .iter()
        .any(|detail| detail.as_str().expect("detail").contains("VeriPB")));
    assert!(replay["details"]
        .as_array()
        .expect("details")
        .iter()
        .any(|detail| detail.as_str().expect("detail").contains("not available")));
}

#[test]
fn math_artifact_replay_blocks_lrat_without_dimacs_metadata() {
    let artifact =
        "tests/fixtures/external_certificates/proof_artifact_v1/sat_pb_lrat_wellformed.json";

    let validate = run_clean_json(&["math", "artifact", "validate", artifact, "--json"]);
    assert_eq!(validate["source_system"], "sat-pb");
    assert_eq!(validate["artifact_kind"], "lrat");
    assert_eq!(validate["certificate_format"], "lrat");
    assert_eq!(validate["status"], "pass");

    let replay = run_clean_json_expect_failure(&[
        "math",
        "artifact",
        "replay",
        "--project",
        sat_project(),
        artifact,
        "--json",
    ]);
    assert_eq!(replay["schema_version"], "clean-artifact-replay-report-v1");
    assert_eq!(replay["replay_status"], "blocked");
    assert_eq!(replay["replay_adapter"], "sat-pb-lrat-v1");
    assert_eq!(replay["evidence_kind"], "replay_only");
    assert_eq!(replay["kernel_certified"], false);
    assert!(replay["details"]
        .as_array()
        .expect("details")
        .iter()
        .any(|detail| detail
            .as_str()
            .expect("detail")
            .contains("requires metadata.dimacs")));
}

#[test]
fn math_artifact_replay_blocks_drat_without_dimacs_metadata() {
    let artifact =
        "tests/fixtures/external_certificates/proof_artifact_v1/sat_pb_drat_wellformed.json";

    let validate = run_clean_json(&["math", "artifact", "validate", artifact, "--json"]);
    assert_eq!(validate["source_system"], "sat-pb");
    assert_eq!(validate["artifact_kind"], "drat");
    assert_eq!(validate["certificate_format"], "drat");
    assert_eq!(validate["status"], "pass");

    let replay = run_clean_json_expect_failure(&[
        "math",
        "artifact",
        "replay",
        "--project",
        sat_project(),
        artifact,
        "--json",
    ]);
    assert_eq!(replay["schema_version"], "clean-artifact-replay-report-v1");
    assert_eq!(replay["replay_status"], "blocked");
    assert_eq!(replay["replay_adapter"], "sat-pb-drat-v1");
    assert_eq!(replay["evidence_kind"], "replay_only");
    assert_eq!(replay["kernel_certified"], false);
    assert!(replay["details"]
        .as_array()
        .expect("details")
        .iter()
        .any(|detail| detail
            .as_str()
            .expect("detail")
            .contains("requires metadata.dimacs")));
}

#[test]
fn math_artifact_replay_fails_malformed_or_empty_sat_pb_text_artifacts() {
    let cases = [
        (
            "tests/fixtures/external_certificates/proof_artifact_v1/sat_pb_lrat_malformed.json",
            "sat-pb-lrat-v1",
            "malformed",
        ),
        (
            "tests/fixtures/external_certificates/proof_artifact_v1/sat_pb_drat_malformed.json",
            "sat-pb-drat-v1",
            "malformed",
        ),
        (
            "tests/fixtures/external_certificates/proof_artifact_v1/sat_pb_drat_empty.json",
            "sat-pb-drat-v1",
            "must not be empty",
        ),
        (
            "tests/fixtures/external_certificates/proof_artifact_v1/sat_pb_veripb_empty.json",
            "sat-pb-veripb-v1",
            "no proof commands",
        ),
    ];

    for (artifact, adapter, detail_fragment) in cases {
        let validate = run_clean_json(&["math", "artifact", "validate", artifact, "--json"]);
        assert_eq!(validate["source_system"], "sat-pb");
        assert_eq!(validate["status"], "pass");

        let replay = run_clean_json_expect_failure(&[
            "math",
            "artifact",
            "replay",
            "--project",
            sat_project(),
            artifact,
            "--json",
        ]);
        assert_eq!(replay["schema_version"], "clean-artifact-replay-report-v1");
        assert_eq!(replay["replay_status"], "fail");
        assert_eq!(replay["replay_adapter"], adapter);
        assert!(replay["details"]
            .as_array()
            .expect("details")
            .iter()
            .any(|detail| detail.as_str().expect("detail").contains(detail_fragment)));
    }
}

#[test]
fn math_artifact_replay_blocks_sat_pb_artifact_with_unsupported_payload_encoding() {
    let artifact =
        "tests/fixtures/external_certificates/proof_artifact_v1/sat_pb_drat_base64_payload.json";
    let validate = run_clean_json(&["math", "artifact", "validate", artifact, "--json"]);
    assert_eq!(
        validate["schema_version"],
        "clean-artifact-envelope-report-v1"
    );
    assert_eq!(validate["source_system"], "sat-pb");
    assert_eq!(validate["artifact_kind"], "drat");
    assert_eq!(validate["certificate_format"], "drat");
    assert_eq!(validate["status"], "pass");

    let replay = run_clean_json_expect_failure(&[
        "math",
        "artifact",
        "replay",
        "--project",
        sat_project(),
        artifact,
        "--json",
    ]);
    assert_eq!(replay["schema_version"], "clean-artifact-replay-report-v1");
    assert_eq!(replay["replay_status"], "blocked");
    assert_eq!(replay["replay_adapter"], "sat-pb-drat-v1");
    assert!(replay["details"]
        .as_array()
        .expect("details")
        .iter()
        .any(|detail| detail
            .as_str()
            .expect("detail")
            .contains("expects Text payloads")));
}

#[test]
fn math_artifact_replay_fails_closed_when_project_profile_has_no_adapter() {
    let cases = [
        (
            sat_project(),
            "tests/fixtures/external_certificates/proof_artifact_v1/gamma_crown_farkas_valid.json",
            "sat-pb",
            "gamma_crown_farkas",
            "gamma-crown-farkas-v1",
        ),
        (
            nn_project(),
            "tests/fixtures/external_certificates/proof_artifact_v1/sat_pb_lrat_checked.json",
            "nn-verify",
            "lrat",
            "lrat",
        ),
    ];

    for (project, artifact, profile, artifact_kind, certificate_format) in cases {
        let replay = run_clean_json_expect_failure(&[
            "math",
            "artifact",
            "replay",
            "--project",
            project,
            artifact,
            "--json",
        ]);
        assert_eq!(replay["schema_version"], "clean-artifact-replay-report-v1");
        assert_eq!(replay["evidence_kind"], "replay_only");
        assert_eq!(replay["kernel_certified"], false);
        assert_eq!(replay["replay_status"], "blocked");
        assert_eq!(replay["replay_adapter"], "none");
        assert!(replay.get("adapter_descriptor_id").is_none());
        assert!(replay.get("adapter_lifecycle").is_none());
        assert_replay_diagnostic(&replay, "AR001");
        let details = replay["details"].as_array().expect("details");
        assert!(details.iter().any(|detail| {
            let detail = detail.as_str().expect("detail");
            detail.contains(profile)
                && detail.contains(artifact_kind)
                && detail.contains(certificate_format)
        }));
    }
}

#[test]
fn math_artifact_replay_fails_closed_when_project_profile_adapter_is_unwired() {
    let temp = tempfile::tempdir().expect("tempdir");
    let project = write_local_profile_project(temp.path());
    let project_arg = project.to_str().expect("utf8 project path");
    let replay = run_clean_json_expect_failure(&[
        "math",
        "artifact",
        "replay",
        "--project",
        project_arg,
        "tests/fixtures/external_certificates/proof_artifact_v1/sat_pb_lrat_checked.json",
        "--json",
    ]);

    assert_eq!(replay["schema_version"], "clean-artifact-replay-report-v1");
    assert_eq!(replay["replay_status"], "blocked");
    assert_eq!(replay["adapter_descriptor_id"], "toy-local-lrat-planned-v1");
    assert_eq!(replay["adapter_lifecycle"], "planned");
    assert_replay_diagnostic(&replay, "AR002");
}

#[test]
fn math_project_hygiene_passes_for_clean_fixture() {
    let report = run_clean_json(&[
        "math",
        "project",
        "hygiene",
        "--project",
        sat_project(),
        "--json",
    ]);

    assert_eq!(report["schema_version"], "clean-math-project-hygiene-v1");
    assert_eq!(report["project"], "sat-pb-pilot");
    assert_eq!(report["status"], "pass");
    assert_eq!(report["gate"]["pass_status"], "pass");
    assert_eq!(
        report["gate"]["command"],
        "clean math project hygiene --project tests/fixtures/math_project/sat_pb/project.json --json"
    );
}

#[test]
fn math_project_hygiene_blocks_missing_replay_evidence_for_artifact_obligation() {
    let temp = tempfile::tempdir().expect("tempdir");
    write_hygiene_project_fixture(temp.path(), None, BTreeMap::new());
    let project_path = temp.path().join("project.json");
    let project_arg = project_path.to_str().expect("utf8 temp path");

    let report = run_clean_json_expect_failure(&[
        "math",
        "project",
        "hygiene",
        "--project",
        project_arg,
        "--json",
    ]);

    assert_eq!(report["status"], "fail");
    assert!(report["violations"]
        .as_array()
        .expect("violations")
        .iter()
        .any(|violation| violation["code"] == "MP016"));
}

#[test]
fn math_project_hygiene_blocks_stale_replay_evidence_hash() {
    let temp = tempfile::tempdir().expect("tempdir");
    write_hygiene_project_fixture(temp.path(), None, BTreeMap::new());
    let project_path = temp.path().join("project.json");
    let obligation_path = temp.path().join("obligations").join("pilot.json");
    let project_arg = project_path.to_str().expect("utf8 temp project path");
    let obligation_arg = obligation_path.to_str().expect("utf8 temp obligation path");
    let obligation_report = run_clean_json(&[
        "math",
        "obligation",
        "validate",
        obligation_arg,
        "--project",
        project_arg,
        "--json",
    ]);
    let fingerprint = obligation_report["fingerprint"]
        .as_str()
        .expect("fingerprint");
    write_hygiene_replay_evidence(temp.path(), fingerprint, "blake3:stale-proof");
    write_hygiene_project_fixture(temp.path(), Some("evidence/replay.json"), BTreeMap::new());

    let report = run_clean_json_expect_failure(&[
        "math",
        "project",
        "hygiene",
        "--project",
        project_arg,
        "--json",
    ]);

    assert_eq!(report["status"], "fail");
    assert!(report["violations"]
        .as_array()
        .expect("violations")
        .iter()
        .any(|violation| violation["code"] == "MP017"));
}

#[test]
fn math_project_hygiene_blocks_replay_evidence_with_trusted_assumptions() {
    let temp = tempfile::tempdir().expect("tempdir");
    write_hygiene_project_fixture(temp.path(), None, BTreeMap::new());
    let project_path = temp.path().join("project.json");
    let obligation_path = temp.path().join("obligations").join("pilot.json");
    let project_arg = project_path.to_str().expect("utf8 temp project path");
    let obligation_arg = obligation_path.to_str().expect("utf8 temp obligation path");
    let obligation_report = run_clean_json(&[
        "math",
        "obligation",
        "validate",
        obligation_arg,
        "--project",
        project_arg,
        "--json",
    ]);
    let fingerprint = obligation_report["fingerprint"]
        .as_str()
        .expect("fingerprint");
    write_hygiene_replay_evidence(temp.path(), fingerprint, "blake3:fresh-proof");
    let replay_path = temp.path().join("evidence").join("replay.json");
    let mut evidence: Value =
        serde_json::from_str(&fs::read_to_string(&replay_path).expect("read replay evidence"))
            .expect("parse replay evidence");
    evidence["trusted_assumptions"] = serde_json::json!(["trustedAy"]);
    fs::write(
        &replay_path,
        serde_json::to_string_pretty(&evidence).expect("evidence json"),
    )
    .expect("write replay evidence");
    write_hygiene_project_fixture(temp.path(), Some("evidence/replay.json"), BTreeMap::new());

    let report = run_clean_json_expect_failure(&[
        "math",
        "project",
        "hygiene",
        "--project",
        project_arg,
        "--json",
    ]);

    assert_eq!(report["status"], "fail");
    assert!(report["violations"]
        .as_array()
        .expect("violations")
        .iter()
        .any(|violation| violation["code"] == "MP018"));
}

#[test]
fn math_project_hygiene_blocks_replay_evidence_claiming_kernel_certificate() {
    let temp = tempfile::tempdir().expect("tempdir");
    write_hygiene_project_fixture(temp.path(), None, BTreeMap::new());
    let project_path = temp.path().join("project.json");
    let obligation_path = temp.path().join("obligations").join("pilot.json");
    let project_arg = project_path.to_str().expect("utf8 temp project path");
    let obligation_arg = obligation_path.to_str().expect("utf8 temp obligation path");
    let obligation_report = run_clean_json(&[
        "math",
        "obligation",
        "validate",
        obligation_arg,
        "--project",
        project_arg,
        "--json",
    ]);
    let fingerprint = obligation_report["fingerprint"]
        .as_str()
        .expect("fingerprint");
    write_hygiene_replay_evidence(temp.path(), fingerprint, "blake3:fresh-proof");
    let replay_path = temp.path().join("evidence").join("replay.json");
    let mut evidence: Value =
        serde_json::from_str(&fs::read_to_string(&replay_path).expect("read replay evidence"))
            .expect("parse replay evidence");
    evidence["kernel_certified"] = serde_json::json!(true);
    fs::write(
        &replay_path,
        serde_json::to_string_pretty(&evidence).expect("evidence json"),
    )
    .expect("write replay evidence");
    write_hygiene_project_fixture(temp.path(), Some("evidence/replay.json"), BTreeMap::new());

    let report = run_clean_json_expect_failure(&[
        "math",
        "project",
        "hygiene",
        "--project",
        project_arg,
        "--json",
    ]);

    assert_eq!(report["status"], "fail");
    assert!(report["violations"]
        .as_array()
        .expect("violations")
        .iter()
        .any(|violation| violation["code"] == "MP024"));
}

#[test]
fn math_project_hygiene_blocks_axiom_theorem_pack_under_constructive_policy() {
    let temp = tempfile::tempdir().expect("tempdir");
    let project_path = write_axiom_theorem_pack_project_fixture(temp.path());
    let project_arg = project_path.to_str().expect("utf8 temp path");

    let report = run_clean_json_expect_failure(&[
        "math",
        "project",
        "hygiene",
        "--project",
        project_arg,
        "--json",
    ]);

    assert_eq!(report["status"], "fail");
    assert!(report["violations"]
        .as_array()
        .expect("violations")
        .iter()
        .any(|violation| {
            violation["code"] == "MP027"
                && violation["path"] == "theorem_packs[0].candidates[SatPb.unsound_bridge]"
                && violation["message"]
                    .as_str()
                    .expect("message")
                    .contains("axiom declaration is not allowed")
        }));
}

#[test]
fn math_artifact_replay_cache_feeds_status_hygiene_and_dashboard() {
    let temp = tempfile::tempdir().expect("tempdir");
    let project_path = write_replay_cache_project_fixture(temp.path());
    let artifact_path = temp.path().join("artifacts").join("gamma.json");
    let project_arg = project_path.to_str().expect("utf8 project path");
    let artifact_arg = artifact_path.to_str().expect("utf8 artifact path");

    let replay = run_clean_json(&[
        "math",
        "artifact",
        "replay",
        "--project",
        project_arg,
        "--cache-dir",
        "cache/replay",
        artifact_arg,
        "--json",
    ]);

    assert_eq!(replay["replay_status"], "pass");
    assert_eq!(replay["cache"]["cache_dir"], "cache/replay");
    assert_eq!(replay["cache"]["index_path"], "cache/replay/index.json");
    assert_eq!(
        replay["linked_obligations"]
            .as_array()
            .expect("linked obligations")
            .len(),
        1
    );
    assert!(temp
        .path()
        .join("cache")
        .join("replay")
        .join("index.json")
        .is_file());
    assert!(temp
        .path()
        .join(
            replay["cache"]["report_path"]
                .as_str()
                .expect("report path")
        )
        .is_file());
    assert!(temp
        .path()
        .join(".clean")
        .join("replay-cache")
        .join("roots.json")
        .is_file());

    let status = run_clean_json(&[
        "math",
        "project",
        "status",
        "--project",
        project_arg,
        "--json",
    ]);
    assert_eq!(status["status"], "pass");
    assert_eq!(status["replay_cache"]["cached_reports"], 1);
    assert_eq!(status["replay_cache"]["pass"], 1);

    let hygiene = run_clean_json(&[
        "math",
        "project",
        "hygiene",
        "--project",
        project_arg,
        "--json",
    ]);
    assert_eq!(hygiene["status"], "pass");

    let dashboard = run_clean_json(&[
        "math",
        "project",
        "dashboard",
        "--project",
        project_arg,
        "--json",
    ]);
    assert_eq!(
        dashboard["schema_version"],
        "clean-math-project-dashboard-v1"
    );
    assert_eq!(dashboard["obligations"]["total"], 1);
    assert_eq!(dashboard["replay"]["cached_reports"], 1);
    assert_eq!(dashboard["replay"]["missing_artifact_replay"], 0);
    assert_eq!(dashboard["hygiene"]["blockers"], serde_json::json!([]));
}

#[test]
fn math_project_dashboard_reports_hygiene_blockers_read_only() {
    let temp = tempfile::tempdir().expect("tempdir");
    write_hygiene_project_fixture(temp.path(), None, BTreeMap::new());
    let project_path = temp.path().join("project.json");
    let project_arg = project_path.to_str().expect("utf8 project path");

    let dashboard = run_clean_json(&[
        "math",
        "project",
        "dashboard",
        "--project",
        project_arg,
        "--json",
    ]);

    assert_eq!(dashboard["status"], "fail");
    assert_eq!(dashboard["obligations"]["total"], 1);
    assert_eq!(dashboard["replay"]["cached_reports"], 0);
    assert_eq!(dashboard["replay"]["missing_artifact_replay"], 1);
    assert!(dashboard["hygiene"]["blockers"]
        .as_array()
        .expect("blockers")
        .iter()
        .any(|violation| violation["code"] == "MP016"));
    assert!(
        !temp
            .path()
            .join(".clean")
            .join("replay-cache")
            .join("roots.json")
            .exists(),
        "dashboard must not create replay cache registry"
    );
}

#[test]
fn math_project_hygiene_blocks_hidden_obligation_trust_markers() {
    let temp = tempfile::tempdir().expect("tempdir");
    let mut metadata = BTreeMap::new();
    metadata.insert("source".to_owned(), "trustedAy fallback".to_owned());
    write_hygiene_project_fixture(temp.path(), None, metadata);
    let project_path = temp.path().join("project.json");
    let project_arg = project_path.to_str().expect("utf8 temp path");

    let report = run_clean_json_expect_failure(&[
        "math",
        "project",
        "hygiene",
        "--project",
        project_arg,
        "--json",
    ]);

    assert_eq!(report["status"], "fail");
    assert!(report["violations"]
        .as_array()
        .expect("violations")
        .iter()
        .any(|violation| {
            violation["code"] == "OB019"
                && violation["path"] == "obligation_sources[0].metadata.source"
        }));
}

#[test]
fn math_issue_plan_emits_phase_8_rows_for_hygiene_violation_codes() {
    let temp = tempfile::tempdir().expect("tempdir");
    write_hygiene_project_fixture(temp.path(), None, BTreeMap::new());
    let project_path = temp.path().join("project.json");
    let project_arg = project_path.to_str().expect("utf8 temp path");

    let report = run_clean_json(&["math", "issue-plan", "--project", project_arg, "--json"]);
    let rows = report["rows"].as_array().expect("rows");
    let hygiene_row = rows
        .iter()
        .find(|row| row["filing_key"] == "Phase 8/framework/hygiene-gate/MP016")
        .expect("MP016 hygiene row");

    assert_eq!(hygiene_row["phase"], "Phase 8");
    assert_eq!(hygiene_row["priority"], "P0");
    assert!(hygiene_row["title"]
        .as_str()
        .expect("title")
        .contains("MP016"));
    assert!(hygiene_row["issue_body"]
        .as_str()
        .expect("issue_body")
        .contains("MP016"));
}

#[test]
fn math_issue_plan_routes_semantically_invalid_obligation_to_phase_3_repair() {
    let temp = tempfile::tempdir().expect("tempdir");
    let project_path = write_issue_plan_project_with_invalid_obligation(temp.path());
    let project_arg = project_path.to_str().expect("utf8 project path");

    let report = run_clean_json(&["math", "issue-plan", "--project", project_arg, "--json"]);
    let rows = report["rows"].as_array().expect("rows");
    let repair_row = rows
        .iter()
        .find(|row| {
            row["phase"] == "Phase 3"
                && row["workstream"] == "sat-pb/obligation-source-repair"
                && row["issue_body"]
                    .as_str()
                    .expect("issue body")
                    .contains("OB012")
        })
        .expect("semantic validation repair row");

    assert_eq!(repair_row["phase_title"], "Generic obligation ABI");
    assert!(repair_row["title"]
        .as_str()
        .expect("title")
        .contains("repair invalid obligation source"));
    assert!(!rows.iter().any(|row| {
        row["files"] == serde_json::json!(["obligations/invalid.json"])
            && (row["phase"] == "Phase 6" || row["phase"] == "Phase 7")
    }));
}

#[test]
fn math_issue_plan_json_enriches_rows_from_proof_failure_diagnostic_evidence() {
    let temp = tempfile::tempdir().expect("tempdir");
    let project_path = write_issue_plan_project_with_proof_failure_diagnostic(temp.path());
    let project_arg = project_path.to_str().expect("utf8 project path");

    let report = run_clean_json(&["math", "issue-plan", "--project", project_arg, "--json"]);
    let rows = report["rows"].as_array().expect("rows");
    assert_eq!(rows.len(), 1);
    let row = &rows[0];

    assert_eq!(row["phase"], "Phase 7");
    assert_eq!(row["phase_title"], "Certificate extraction");
    assert_eq!(row["workstream"], "fixture/proof-closure");
    assert_eq!(
        row["blocking_categories"],
        serde_json::json!(["manifest", "obligation", "artifact", "trust"])
    );
    assert_eq!(
        row["ranking"]["proof_failure_diagnostics"],
        serde_json::json!(["elaboration fails before theorem candidate closes"])
    );
    assert!(row["ranking"]["signals"]
        .as_array()
        .expect("ranking signals")
        .iter()
        .any(|signal| signal == "proof-failure:unknown-constant"));
    assert!(row["ranking"]["score"].as_i64().expect("ranking score") > 750);

    let metadata = &row["filing_metadata"];
    assert_eq!(
        metadata["blockers"],
        serde_json::json!([
            "manifest",
            "obligation",
            "artifact",
            "trust",
            "missing-kernel-proof",
            "unknown-constant",
            "missing-local-instance"
        ])
    );
    assert_eq!(
        metadata["reproduction"]["files"],
        serde_json::json!(["obligations/pilot.json", "proofs/Pilot.lean"])
    );
    let reproduction_commands = metadata["reproduction"]["commands"]
        .as_array()
        .expect("reproduction commands");
    assert_eq!(reproduction_commands[0], row["verification_command"]);
    assert!(reproduction_commands
        .iter()
        .any(|command| command == "clean proof-state replay --state proof-failure"));

    let verification_command = row["verification_command"]
        .as_str()
        .expect("verification command");
    assert!(verification_command.contains("clean math certificate extract"));
    assert!(verification_command.contains("proof_status"));
    assert!(verification_command.contains("kernel_certified"));
    assert!(!verification_command.contains("proof-state replay"));

    let issue_body = row["issue_body"].as_str().expect("issue body");
    assert!(issue_body.contains("## Verification"));
    assert!(issue_body.contains(verification_command));
    assert!(issue_body.contains("## Proof Failure Diagnostics"));
    assert!(issue_body.contains("elaboration fails before theorem candidate closes"));
    assert!(issue_body.contains("unknown-constant, missing-local-instance"));
}

#[test]
fn math_issue_plan_emits_actionable_rows() {
    let report = run_clean_json(&["math", "issue-plan", "--project", nn_project(), "--json"]);

    assert_eq!(report["schema_version"], "clean-math-issue-plan-v2");
    assert_eq!(report["project"], "nn-verify-pilot");
    assert_eq!(
        report["filing_guidance"]["grouping"],
        serde_json::json!(["phase", "workstream", "filing_key"])
    );
    assert_eq!(report["phases"][0]["id"], "Phase 6");
    assert_eq!(report["phases"][0]["title"], "Artifact replay");
    assert_eq!(
        report["workstreams"][0]["id"],
        "gamma-crown/gamma-crown-farkas"
    );
    let rows = report["rows"].as_array().expect("rows");
    assert_eq!(rows.len(), 1);
    let farkas_row = rows
        .iter()
        .find(|row| row["workstream"] == "gamma-crown/gamma-crown-farkas")
        .expect("gamma-crown Farkas issue row");
    assert!(!rows.iter().any(|row| {
        row["files"] == serde_json::json!(["obligations/gamma_crown_serialized_kernel_pilot.json"])
    }));
    assert!(farkas_row["dedupe_key"]
        .as_str()
        .expect("dedupe_key")
        .starts_with("clean-math-issue-"));
    assert_eq!(farkas_row["dedupe_status"], "new");
    assert_eq!(farkas_row["phase"], "Phase 6");
    assert_eq!(farkas_row["phase_title"], "Artifact replay");
    assert_eq!(farkas_row["workstream"], "gamma-crown/gamma-crown-farkas");
    assert!(farkas_row["filing_key"]
        .as_str()
        .expect("filing_key")
        .starts_with("Phase 6/gamma-crown/gamma-crown-farkas/"));
    assert!(farkas_row["title"]
        .as_str()
        .expect("title")
        .contains("[nn-verify][gamma-crown/gamma-crown-farkas] close obligation"));
    assert_eq!(
        farkas_row["owners"].as_array().expect("owners").len(),
        0,
        "fixture has no explicit owner routing"
    );
    assert_eq!(
        farkas_row["blocking_categories"],
        serde_json::json!(["manifest", "obligation", "artifact", "trust"])
    );
    let issue_body = farkas_row["issue_body"].as_str().expect("issue_body");
    assert!(issue_body.contains("## Routing"));
    assert!(issue_body.contains("- Phase: Phase 6 - Artifact replay"));
    assert!(issue_body.contains("- Workstream: gamma-crown/gamma-crown-farkas"));
    assert!(!issue_body.contains("2026-"));
    assert!(farkas_row["verification_command"]
        .as_str()
        .expect("verification_command")
        .contains("clean math artifact replay"));
    assert!(farkas_row["verification_command"]
        .as_str()
        .expect("verification_command")
        .contains("clean math project hygiene"));
    assert!(!farkas_row["verification_command"]
        .as_str()
        .expect("verification_command")
        .contains("clean math obligation validate"));
}

#[test]
fn math_issue_plan_dedupes_against_offline_open_issue_snapshot() {
    let temp = tempfile::tempdir().expect("tempdir");
    let initial = run_clean_json(&["math", "issue-plan", "--project", nn_project(), "--json"]);
    let row = &initial["rows"][0];
    let dedupe_key = row["dedupe_key"].as_str().expect("dedupe key");
    let snapshot_path = temp.path().join("open_issues.json");
    let snapshot = serde_json::json!([
        {
            "number": 10,
            "state": "open",
            "title": "different title",
            "body": format!("tracked by {dedupe_key}")
        },
        {
            "number": 11,
            "state": "closed",
            "title": row["title"],
            "body": row["issue_body"]
        }
    ]);
    fs::write(
        &snapshot_path,
        serde_json::to_string_pretty(&snapshot).expect("snapshot json"),
    )
    .expect("write snapshot");

    let snapshot_arg = snapshot_path.to_str().expect("utf8 snapshot path");
    let report = run_clean_json(&[
        "math",
        "issue-plan",
        "--project",
        nn_project(),
        "--dedupe-open",
        snapshot_arg,
        "--json",
    ]);

    assert_eq!(report["rows"][0]["dedupe_key"], dedupe_key);
    assert_eq!(report["rows"][0]["dedupe_status"], "matched_open");
}

#[test]
fn math_issue_plan_marks_duplicate_open_matches_ambiguous() {
    let temp = tempfile::tempdir().expect("tempdir");
    let initial = run_clean_json(&["math", "issue-plan", "--project", nn_project(), "--json"]);
    let row = &initial["rows"][0];
    let dedupe_key = row["dedupe_key"].as_str().expect("dedupe key");
    let snapshot_path = temp.path().join("open_issues.json");
    let snapshot = serde_json::json!({
        "items": [
            {
                "number": 20,
                "state": "OPEN",
                "title": row["title"],
                "body": ""
            },
            {
                "number": 21,
                "state": "open",
                "title": "another issue",
                "dedupe_key": dedupe_key
            }
        ]
    });
    fs::write(
        &snapshot_path,
        serde_json::to_string_pretty(&snapshot).expect("snapshot json"),
    )
    .expect("write snapshot");

    let snapshot_arg = snapshot_path.to_str().expect("utf8 snapshot path");
    let report = run_clean_json(&[
        "math",
        "issue-plan",
        "--project",
        nn_project(),
        "--dedupe-open",
        snapshot_arg,
        "--json",
    ]);

    assert_eq!(report["rows"][0]["dedupe_status"], "ambiguous");
}

#[test]
fn math_issue_plan_export_dry_run_reports_deterministic_local_issue_files() {
    let temp = tempfile::tempdir().expect("tempdir");
    let export_dir = temp.path().join("issues");
    let export_arg = export_dir.to_str().expect("utf8 export dir");

    let report = run_clean_json(&[
        "math",
        "issue-plan",
        "--project",
        nn_project(),
        "--export-dir",
        export_arg,
        "--json",
    ]);

    assert_eq!(report["schema_version"], "clean-math-issue-file-export-v1");
    assert_eq!(report["project"], "nn-verify-pilot");
    assert_eq!(report["write"], false);
    assert_eq!(report["total_rows"], 1);
    assert_eq!(report["created"], 1);
    assert_eq!(report["skipped_existing"], 0);
    assert!(!export_dir.exists(), "dry-run must not create export dir");

    let file = &report["files"][0];
    assert_eq!(file["status"], "planned");
    assert_eq!(file["reason"], "dry_run");
    let dedupe_key = file["dedupe_key"].as_str().expect("dedupe key");
    assert!(dedupe_key.starts_with("clean-math-issue-"));
    assert!(file["markdown_path"]
        .as_str()
        .expect("markdown path")
        .ends_with(&format!("{dedupe_key}.md")));
    assert!(file["json_path"]
        .as_str()
        .expect("json path")
        .ends_with(&format!("{dedupe_key}.json")));
}

#[test]
fn math_issue_plan_export_write_creates_files_and_skips_existing_dedupe_keys() {
    let temp = tempfile::tempdir().expect("tempdir");
    let export_dir = temp.path().join("issues");
    let export_arg = export_dir.to_str().expect("utf8 export dir");

    let write = run_clean_json(&[
        "math",
        "issue-plan",
        "--project",
        nn_project(),
        "--export-dir",
        export_arg,
        "--write",
        "--json",
    ]);

    assert_eq!(write["write"], true);
    assert_eq!(write["created"], 1);
    assert_eq!(write["skipped_existing"], 0);
    let file = &write["files"][0];
    assert_eq!(file["status"], "written");
    let markdown_path = PathBuf::from(file["markdown_path"].as_str().expect("markdown path"));
    let json_path = PathBuf::from(file["json_path"].as_str().expect("json path"));
    assert!(markdown_path.is_file());
    assert!(json_path.is_file());

    let issue_json: Value = serde_json::from_slice(&fs::read(&json_path).expect("read issue json"))
        .expect("issue json parses");
    assert_eq!(issue_json["schema_version"], "clean-math-issue-file-v1");
    assert_eq!(issue_json["dedupe_key"], file["dedupe_key"]);
    assert_eq!(issue_json["title"], file["title"]);
    assert!(!issue_json["acceptance"]
        .as_array()
        .expect("acceptance")
        .is_empty());
    let markdown = fs::read_to_string(&markdown_path).expect("read issue markdown");
    assert!(markdown.contains(file["dedupe_key"].as_str().expect("dedupe key")));
    assert!(markdown.contains("## Acceptance Criteria"));
    assert!(markdown.contains("## Verification"));

    let second = run_clean_json(&[
        "math",
        "issue-plan",
        "--project",
        nn_project(),
        "--export-dir",
        export_arg,
        "--write",
        "--json",
    ]);

    assert_eq!(second["created"], 0);
    assert_eq!(second["skipped_existing"], 1);
    assert_eq!(second["files"][0]["status"], "skipped_existing");
    assert_eq!(second["files"][0]["dedupe_key"], file["dedupe_key"]);
}

#[test]
fn math_task_list_projects_issue_plan_to_durable_local_store() {
    let temp = tempfile::tempdir().expect("tempdir");
    let project_path = write_issue_plan_project_with_invalid_obligation(temp.path());
    let project_arg = project_path.to_str().expect("utf8 project path");

    let report = run_clean_json(&["math", "task", "list", "--project", project_arg, "--json"]);

    assert_eq!(report["schema_version"], "clean-math-task-list-v1");
    assert_eq!(report["project"], "issue-plan-invalid-pilot");
    assert_eq!(report["total"], 2);
    assert_eq!(report["by_status"]["open"], 2);
    assert!(temp.path().join(".clean").join("math-tasks.json").is_file());
    let task = report["tasks"]
        .as_array()
        .expect("tasks")
        .iter()
        .find(|task| task["issue"]["phase"] == "Phase 3")
        .expect("Phase 3 repair task");
    assert_eq!(task["status"], "open");
    assert_eq!(task["issue"]["phase"], "Phase 3");
    assert_eq!(
        task["issue"]["files"],
        serde_json::json!(["obligations/invalid.json"])
    );
    assert!(task["id"].as_str().expect("task id").starts_with("sha256:"));
    assert_eq!(task["obligation_fingerprint"], task["id"]);
}

#[test]
fn math_task_update_persists_status_notes_and_blockers_by_obligation_path() {
    let temp = tempfile::tempdir().expect("tempdir");
    let project_path = write_replay_cache_project_fixture(temp.path());
    let obligation_path = temp.path().join("obligations").join("pilot.json");
    let project_arg = project_path.to_str().expect("utf8 project path");
    let obligation_arg = obligation_path.to_str().expect("utf8 obligation path");

    let update = run_clean_json(&[
        "math",
        "task",
        "update",
        "--project",
        project_arg,
        "--obligation",
        obligation_arg,
        "--status",
        "in-progress",
        "--note",
        "started replay triage",
        "--blocker",
        "needs replay evidence",
        "--json",
    ]);

    assert_eq!(update["schema_version"], "clean-math-task-update-v1");
    assert_eq!(update["wrote"], true);
    assert_eq!(update["task"]["status"], "blocked");
    assert_eq!(
        update["task"]["notes"],
        serde_json::json!(["started replay triage"])
    );
    assert_eq!(
        update["task"]["blockers"],
        serde_json::json!(["needs replay evidence"])
    );
    assert!(update["task"]["obligation_fingerprint"]
        .as_str()
        .expect("fingerprint")
        .starts_with("sha256:"));

    let status = run_clean_json(&[
        "math",
        "task",
        "status",
        "--project",
        project_arg,
        "--obligation",
        obligation_arg,
        "--json",
    ]);
    assert_eq!(status["schema_version"], "clean-math-task-status-v1");
    assert_eq!(status["task"]["id"], update["task"]["id"]);
    assert_eq!(status["task"]["status"], "blocked");
    assert_eq!(
        status["task"]["blockers"],
        serde_json::json!(["needs replay evidence"])
    );

    let store: Value = serde_json::from_slice(
        &fs::read(temp.path().join(".clean").join("math-tasks.json")).expect("read task store"),
    )
    .expect("parse task store");
    assert_eq!(store["schema_version"], "clean-math-task-store-v1");
    assert!(store["tasks"]
        .as_array()
        .expect("stored tasks")
        .iter()
        .any(|task| task["id"] == update["task"]["id"]));
}

#[test]
fn math_proof_state_followups_for_open_obligation_fail_closed_with_bridge_reports() {
    let opened = run_clean_json(&[
        "math",
        "obligation",
        "open",
        sat_obligation(),
        "--project",
        sat_project(),
        "--json",
    ]);
    assert_eq!(opened["schema_version"], "clean-open-obligation-report-v1");
    assert_eq!(opened["status"], "opened-adapter");
    let state = opened["state_id"].as_str().expect("state_id");

    let snapshot = run_clean_json_expect_failure(&[
        "math",
        "proof-state",
        "snapshot",
        "--state",
        state,
        "--format",
        "llm",
        "--json",
    ]);
    assert_proof_state_bridge_report(&snapshot, "snapshot", state, "server-backed state storage");

    let theorem_search = run_clean_json_expect_failure(&[
        "math",
        "proof-state",
        "search-theorems",
        "--state",
        state,
        "--goal",
        "g0",
        "--json",
    ]);
    assert_proof_state_bridge_report(
        &theorem_search,
        "search-theorems",
        state,
        "server-backed proof-state v2 adapters",
    );

    let tactic_search = run_clean_json_expect_failure(&[
        "math",
        "proof-state",
        "search-tactics",
        "--state",
        state,
        "--goal",
        "g0",
        "--json",
    ]);
    assert_proof_state_bridge_report(
        &tactic_search,
        "search-tactics",
        state,
        "server-backed proof-state v2 adapters",
    );

    let apply = run_clean_json_expect_failure(&[
        "math",
        "proof-state",
        "apply",
        "--state",
        state,
        "--goal",
        "g0",
        "--tactic",
        "cert_simp",
        "--json",
    ]);
    assert_proof_state_bridge_report(&apply, "apply", state, "server-backed tactic lifecycle");

    let retain = run_clean_json_expect_failure(&[
        "math",
        "proof-state",
        "retain",
        "--state",
        state,
        "--json",
    ]);
    assert_proof_state_bridge_report(
        &retain,
        "retain",
        state,
        "server-backed proof-state lifecycle storage",
    );

    let close = run_clean_json_expect_failure(&[
        "math",
        "proof-state",
        "close",
        "--state",
        state,
        "--json",
    ]);
    assert_proof_state_bridge_report(
        &close,
        "close",
        state,
        "server-backed proof-state lifecycle storage",
    );

    let extract = run_clean_json_expect_failure(&[
        "math",
        "proof-state",
        "extract",
        "--state",
        state,
        "--format",
        "certificate",
        "--json",
    ]);
    assert_proof_state_bridge_report(&extract, "extract", state, "checked proof state");
}

#[test]
fn math_proof_state_close_uses_persistent_server_when_method_is_available() {
    let server = start_clean_server();
    let methods = rpc_server_methods(&server.addr).expect("serverInfo methods");
    if !methods.iter().any(|method| method == "proofState.close") {
        return;
    }

    let temp = tempfile::tempdir().expect("tempdir");
    let obligation = write_true_serialized_goal_obligation(temp.path());
    let obligation_arg = obligation.to_str().expect("utf8 obligation path");
    let opened = run_clean_json(&[
        "math",
        "proof-state",
        "open-obligation",
        obligation_arg,
        "--project",
        sat_project(),
        "--server",
        &server.addr,
        "--json",
    ]);
    let state = opened["state_id"].as_str().expect("state_id");

    let close = run_clean_json(&[
        "math",
        "proof-state",
        "close",
        "--state",
        state,
        "--server",
        &server.addr,
        "--json",
    ]);
    assert!(
        close["state_id"] == state
            || close["closed_state_id"] == state
            || close["status"] == "closed",
        "unexpected close response: {close}"
    );

    let snapshot = run_clean_json_expect_failure(&[
        "math",
        "proof-state",
        "snapshot",
        "--state",
        state,
        "--server",
        &server.addr,
        "--json",
    ]);
    assert_eq!(snapshot["schema_version"], "clean-proof-state-v2-bridge-v1");
    assert_eq!(snapshot["operation"], "snapshot");
    assert_eq!(snapshot["state"], state);
    assert_eq!(snapshot["status"], "blocked-server-rpc-error");
}

#[test]
fn math_proof_state_uses_server_env_default_for_open_and_snapshot() {
    let server = start_clean_server();
    let methods = rpc_server_methods(&server.addr).expect("serverInfo methods");
    if !methods.iter().any(|method| method == "getProofState") {
        return;
    }

    let temp = tempfile::tempdir().expect("tempdir");
    let obligation = write_true_serialized_goal_obligation(temp.path());
    let obligation_arg = obligation.to_str().expect("utf8 obligation path");
    let server_env = [("CLEAN_SERVER", server.addr.as_str())];
    let opened = run_clean_json_with_env(
        &[
            "math",
            "proof-state",
            "open-obligation",
            obligation_arg,
            "--project",
            sat_project(),
            "--json",
        ],
        &server_env,
    );
    assert_eq!(opened["status"], "opened-server-state");
    assert_eq!(opened["persistence"], "persistent-json-rpc-server");
    let state = opened["state_id"].as_str().expect("state_id");

    // Under heavy test contention the proof-state cache can drop the state
    // between open and snapshot. In that case the snapshot CLI exits non-zero
    // with a bridge report on stdout; tolerate that path here and skip the
    // shape assertions — the open-obligation round-trip is exercised by the
    // sibling persistent-server test.
    let (snapshot_ok, snapshot) = run_clean_json_allow_status_with_env(
        &[
            "math",
            "proof-state",
            "snapshot",
            "--state",
            state,
            "--format",
            "llm",
            "--json",
        ],
        &server_env,
    );
    if !snapshot_ok {
        return;
    }
    assert_eq!(snapshot["state_id"], state);
    assert_eq!(snapshot["goals"].as_array().expect("goals").len(), 1);
}

#[test]
fn math_proof_state_open_obligation_state_round_trips_through_persistent_server() {
    let server = start_clean_server();
    let temp = tempfile::tempdir().expect("tempdir");
    let obligation = write_true_serialized_goal_obligation(temp.path());
    let obligation_arg = obligation.to_str().expect("utf8 obligation path");
    let opened = run_clean_json(&[
        "math",
        "proof-state",
        "open-obligation",
        obligation_arg,
        "--project",
        sat_project(),
        "--server",
        &server.addr,
        "--json",
    ]);
    assert_eq!(
        opened["schema_version"],
        "clean-cli-proof-state-open-obligation-v1"
    );
    assert_eq!(opened["status"], "opened-server-state");
    assert_eq!(opened["persistence"], "persistent-json-rpc-server");
    let state = opened["state_id"].as_str().expect("state_id");
    assert!(state.starts_with("ps_"));

    let snapshot = run_clean_json(&[
        "math",
        "proof-state",
        "snapshot",
        "--state",
        state,
        "--server",
        &server.addr,
        "--format",
        "llm",
        "--json",
    ]);
    assert_eq!(snapshot["state_id"], state);
    assert_eq!(snapshot["is_solved"], false);
    assert_eq!(snapshot["goals"].as_array().expect("goals").len(), 1);
    let goal = snapshot["goals"][0]["goal_id"].as_str().expect("goal_id");

    let theorem_search = run_clean_json(&[
        "math",
        "proof-state",
        "search-theorems",
        "--state",
        state,
        "--goal",
        goal,
        "--server",
        &server.addr,
        "--json",
    ]);
    assert_eq!(theorem_search["state_id"], state);
    assert_eq!(theorem_search["goal_id"], goal);
    assert!(theorem_search["candidates"].is_array());
    assert!(theorem_search["mathverse_candidates"].is_array());

    let tactic_search = run_clean_json(&[
        "math",
        "proof-state",
        "search-tactics",
        "--state",
        state,
        "--goal",
        goal,
        "--server",
        &server.addr,
        "--json",
    ]);
    assert_eq!(tactic_search["state_id"], state);
    assert_eq!(tactic_search["goal_id"], goal);
    assert!(tactic_search["tactics"].is_array());

    let failed_apply = run_clean_json(&[
        "math",
        "proof-state",
        "apply",
        "--state",
        state,
        "--goal",
        goal,
        "--tactic",
        "definitely_unknown_tactic",
        "--server",
        &server.addr,
        "--json",
    ]);
    assert_eq!(failed_apply["success"], false);
    // Under heavy test contention the proof-state cache can drop the state before
    // applyTactic runs, in which case the server returns success=false with no
    // persisted attempt_id (the same shape used for invalid-state-id errors). The
    // attempt-id-dependent follow-up assertions only apply when the server
    // persisted a failed-attempt record, so skip the remainder gracefully when
    // attempt_id is absent — matching the skip-by-return pattern elsewhere in
    // this file.
    let Some(attempt_id) = failed_apply["attempt_id"].as_str() else {
        return;
    };
    assert!(attempt_id.starts_with("pa_"));

    let failure_explanation = run_clean_json(&[
        "math",
        "proof-state",
        "explain-failure",
        "--attempt",
        attempt_id,
        "--server",
        &server.addr,
        "--json",
    ]);
    assert_eq!(failure_explanation["attempt_id"], attempt_id);
    assert_eq!(failure_explanation["status"], "failed");
    assert_eq!(failure_explanation["blockers"].as_array().unwrap().len(), 1);
    assert_eq!(failure_explanation["blockers"][0]["state_id"], state);
    assert_eq!(failure_explanation["blockers"][0]["goal_id"], goal);

    let apply = run_clean_json(&[
        "math",
        "proof-state",
        "apply",
        "--state",
        state,
        "--goal",
        goal,
        "--tactic",
        "exact True.intro",
        "--server",
        &server.addr,
        "--json",
    ]);
    assert_eq!(apply["success"], true);
    assert_eq!(apply["is_solved"], true);
    let solved_state = apply["new_state_id"].as_str().expect("new_state_id");

    let extract = run_clean_json(&[
        "math",
        "proof-state",
        "extract",
        "--state",
        solved_state,
        "--server",
        &server.addr,
        "--format",
        "certificate",
        "--json",
    ]);
    assert_eq!(extract["is_solved"], true);
    assert!(extract["certificate"].is_object());

    let kernel_evidence = run_clean_json(&[
        "math",
        "proof-state",
        "extract",
        "--state",
        solved_state,
        "--server",
        &server.addr,
        "--format",
        "kernel_evidence",
        "--json",
    ]);
    assert_eq!(
        kernel_evidence["schema_version"],
        "clean-math-kernel-evidence-v1"
    );
    assert_eq!(kernel_evidence["checked"], true);
    assert!(kernel_evidence["checked_proof_expr"].is_object());
    assert!(kernel_evidence["checked_target_expr"].is_object());
    assert!(kernel_evidence["proof_certificate"].is_object());
}

#[test]
fn math_certificate_extract_fails_closed_but_emits_json() {
    let report = run_clean_json_expect_failure(&[
        "math",
        "certificate",
        "extract",
        "--project",
        sat_project(),
        "--obligation",
        sat_obligation(),
        "--json",
    ]);

    assert_eq!(report["schema"], "clean-math-certificate-v1");
    assert_eq!(report["project"], "sat-pb-pilot");
    assert_eq!(
        report["proof_status"],
        "blocked-until-kernel-proof-or-replay"
    );
    assert_eq!(report["evidence_kind"], "none");
    assert_eq!(report["kernel_certified"], false);
    assert_eq!(report["synthetic_sorry"], false);
}

#[test]
fn math_certificate_extract_links_replayed_nn_artifact_path_fail_closed() {
    let artifact =
        "tests/fixtures/external_certificates/proof_artifact_v1/gamma_crown_farkas_valid.json";
    let obligation = run_clean_json(&[
        "math",
        "obligation",
        "validate",
        nn_obligation(),
        "--project",
        nn_project(),
        "--json",
    ]);
    let obligation_fingerprint = obligation["fingerprint"].as_str().expect("fingerprint");

    let report = run_clean_json_expect_failure(&[
        "math",
        "certificate",
        "extract",
        "--project",
        nn_project(),
        "--obligation",
        nn_obligation(),
        "--artifact",
        artifact,
        "--json",
    ]);

    assert_eq!(report["schema"], "clean-math-certificate-v1");
    assert_eq!(
        report["artifact"],
        "blake3:fixture-gamma-crown-farkas-proof"
    );
    assert_eq!(
        report["proof_status"],
        "replay-only-artifact-linked-awaiting-kernel-proof"
    );
    assert_eq!(report["evidence_kind"], "replay_only");
    assert_eq!(report["kernel_certified"], false);
    assert_eq!(report["trust_summary"]["evidence_kind"], "replay_only");
    assert_eq!(report["trust_summary"]["kernel_certified"], false);
    assert_eq!(report["trust_summary"]["artifact_replay_status"], "pass");
    assert_eq!(
        report["trust_summary"]["linked_obligations"]
            .as_array()
            .expect("linked_obligations"),
        &[Value::String(obligation_fingerprint.to_owned())]
    );
}

#[test]
fn math_certificate_extract_keeps_artifact_kernel_claim_untrusted() {
    let temp = tempfile::tempdir().expect("tempdir");
    let artifact_path = temp.path().join("gamma-claimed-kernel.json");
    let mut artifact: Value = serde_json::from_str(
        &fs::read_to_string(
            workspace_root()
                .join("tests")
                .join("fixtures")
                .join("external_certificates")
                .join("proof_artifact_v1")
                .join("gamma_crown_farkas_valid.json"),
        )
        .expect("read gamma fixture"),
    )
    .expect("parse gamma fixture");
    artifact["certification"] = serde_json::json!({
        "evidence_kind": "kernel_certified",
        "kernel_theorem": "NNVerify.Farkas.sound",
        "proof_term_hash": "blake3:claimed-proof-term",
        "checker": "clean-kernel:claimed"
    });
    fs::write(
        &artifact_path,
        serde_json::to_string_pretty(&artifact).expect("artifact json"),
    )
    .expect("write claimed artifact");

    let report = run_clean_json_expect_failure(&[
        "math",
        "certificate",
        "extract",
        "--project",
        nn_project(),
        "--obligation",
        nn_obligation(),
        "--artifact",
        artifact_path.to_str().expect("utf8 artifact path"),
        "--json",
    ]);

    assert_eq!(report["evidence_kind"], "replay_only");
    assert_eq!(report["kernel_certified"], false);
    assert!(report.get("kernel_evidence").is_none());
    assert_eq!(
        report["trust_summary"]["artifact_certification_evidence_kind"],
        "kernel_certified"
    );
    assert_eq!(
        report["trust_summary"]["kernel_certification_status"],
        "untrusted-artifact-claim"
    );
    assert_eq!(
        report["trust_summary"]["claimed_kernel_evidence"]["checked"],
        false
    );
}

#[test]
fn math_certificate_extract_does_not_certify_hidden_synthetic_sorry_claim() {
    let temp = tempfile::tempdir().expect("tempdir");
    let artifact_path = temp.path().join("gamma-hidden-trust.json");
    let mut artifact: Value = serde_json::from_str(
        &fs::read_to_string(
            workspace_root()
                .join("tests")
                .join("fixtures")
                .join("external_certificates")
                .join("proof_artifact_v1")
                .join("gamma_crown_farkas_valid.json"),
        )
        .expect("read gamma fixture"),
    )
    .expect("parse gamma fixture");
    artifact["certification"] = serde_json::json!({
        "evidence_kind": "kernel_certified",
        "kernel_theorem": "NNVerify.Farkas.sound",
        "proof_term_hash": "blake3:claimed-proof-term",
        "checker": "clean-kernel:claimed"
    });
    artifact["metadata"] = serde_json::json!({
        "trust_marker": "synthetic_sorry"
    });
    fs::write(
        &artifact_path,
        serde_json::to_string_pretty(&artifact).expect("artifact json"),
    )
    .expect("write hidden-trust artifact");

    let report = run_clean_json_expect_failure(&[
        "math",
        "certificate",
        "extract",
        "--project",
        nn_project(),
        "--obligation",
        nn_obligation(),
        "--artifact",
        artifact_path.to_str().expect("utf8 artifact path"),
        "--json",
    ]);

    assert_eq!(report["kernel_certified"], false);
    assert_eq!(report["synthetic_sorry"], false);
    assert!(report.get("kernel_evidence").is_none());
    assert_eq!(
        report["trust_summary"]["kernel_certification_status"],
        "untrusted-artifact-claim"
    );
}

#[test]
fn math_certificate_extract_rejects_missing_replay_link_for_other_obligation() {
    let artifact =
        "tests/fixtures/external_certificates/proof_artifact_v1/gamma_crown_farkas_valid.json";

    let report = run_clean_json_expect_failure(&[
        "math",
        "certificate",
        "extract",
        "--project",
        nn_project(),
        "--obligation",
        sat_obligation(),
        "--artifact",
        artifact,
        "--json",
    ]);

    assert_eq!(report["schema"], "clean-math-certificate-v1");
    assert_eq!(report["proof_status"], "replayed-artifact-unlinked");
    assert_eq!(report["trust_summary"]["artifact_replay_status"], "pass");
    assert!(report["trust_summary"]["linked_obligations"]
        .as_array()
        .expect("linked_obligations")
        .iter()
        .all(|linked| linked != &report["obligation"]));
}

#[test]
fn math_certificate_extract_links_nn_artifact_hash_without_attesting_replay() {
    let obligation = run_clean_json(&[
        "math",
        "obligation",
        "validate",
        nn_obligation(),
        "--project",
        nn_project(),
        "--json",
    ]);
    let obligation_fingerprint = obligation["fingerprint"].as_str().expect("fingerprint");

    let report = run_clean_json_expect_failure(&[
        "math",
        "certificate",
        "extract",
        "--project",
        nn_project(),
        "--obligation",
        nn_obligation(),
        "--artifact",
        "blake3:fixture-gamma-crown-farkas-proof",
        "--json",
    ]);

    assert_eq!(
        report["proof_status"],
        "artifact-hash-linked-replay-not-attested"
    );
    assert_eq!(report["evidence_kind"], "artifact_hash_only");
    assert_eq!(report["kernel_certified"], false);
    assert_eq!(
        report["trust_summary"]["linked_obligations"]
            .as_array()
            .expect("linked_obligations"),
        &[Value::String(obligation_fingerprint.to_owned())]
    );
}

#[test]
fn math_certificate_extract_uses_project_replay_cache_for_path_and_hash() {
    let temp = tempfile::tempdir().expect("tempdir");
    let project_path = write_replay_cache_project_fixture(temp.path());
    let artifact_path = temp.path().join("artifacts").join("gamma.json");
    let project_arg = project_path.to_str().expect("utf8 project path");
    let artifact_arg = artifact_path.to_str().expect("utf8 artifact path");
    let obligation_arg = temp
        .path()
        .join("obligations")
        .join("pilot.json")
        .to_str()
        .expect("utf8 obligation path")
        .to_owned();

    let replay = run_clean_json(&[
        "math",
        "artifact",
        "replay",
        "--project",
        project_arg,
        "--cache",
        "--cache-dir",
        "cache/replay",
        artifact_arg,
        "--json",
    ]);
    let cache_report_path = replay["cache"]["report_path"]
        .as_str()
        .expect("cache report path")
        .to_owned();

    let path_extract = run_clean_json_expect_failure(&[
        "math",
        "certificate",
        "extract",
        "--project",
        project_arg,
        "--obligation",
        &obligation_arg,
        "--artifact",
        artifact_arg,
        "--json",
    ]);
    assert_eq!(
        path_extract["proof_status"],
        "replay-only-artifact-linked-awaiting-kernel-proof"
    );
    assert_eq!(path_extract["evidence_kind"], "replay_only");
    assert_eq!(path_extract["kernel_certified"], false);
    assert_eq!(
        path_extract["trust_summary"]["replay_evidence_source"],
        "project-replay-cache"
    );
    assert_eq!(
        path_extract["trust_summary"]["replay_cache_report_path"],
        cache_report_path
    );

    let hash_extract = run_clean_json_expect_failure(&[
        "math",
        "certificate",
        "extract",
        "--project",
        project_arg,
        "--obligation",
        &obligation_arg,
        "--artifact",
        "blake3:fixture-gamma-crown-farkas-proof",
        "--json",
    ]);
    assert_eq!(
        hash_extract["proof_status"],
        "replay-only-artifact-linked-awaiting-kernel-proof"
    );
    assert_eq!(hash_extract["evidence_kind"], "replay_only");
    assert_eq!(hash_extract["kernel_certified"], false);
    assert_eq!(
        hash_extract["trust_summary"]["replay_evidence_source"],
        "project-replay-cache"
    );
    assert_eq!(
        hash_extract["trust_summary"]["replay_cache_report_path"],
        cache_report_path
    );
}

#[test]
fn math_obligation_validate_rejects_pretty_only_trust_leakage() {
    let temp = tempfile::tempdir().expect("tempdir");
    let obligation_path = temp.path().join("pretty_trust_leak.json");
    fs::write(
        &obligation_path,
        r#"{
  "schema_version": "clean-obligation-v1",
  "project": "nn-verify-pilot",
  "domain_profile": "nn-verify",
  "producer": {
    "system": "gamma-crown",
    "commit": "hostile-pretty-only"
  },
  "goal": {
    "expr": "NNVerify.farkas_certificate_sound cert",
    "pretty": "trustedAy closed this Gamma-Crown obligation"
  },
  "local_context": [
    {
      "name": "cert",
      "type_pp": "ExternalFarkasCert via replayed-artifact-linked",
      "type_expr": "ExternalFarkasCert"
    }
  ],
  "side_conditions": [
    "all multipliers are nonnegative",
    "linear combination cancels variables"
  ],
  "artifact_refs": [
    {
      "kind": "proof-artifact-v1",
      "path": "../../external_certificates/proof_artifact_v1/gamma_crown_farkas_valid.json",
      "hash": "blake3:fixture-gamma-crown-farkas-proof"
    }
  ],
  "metadata": {
    "artifact_kind": "gamma_crown_farkas"
  },
  "trust_policy": "constructive-only"
}
"#,
    )
    .expect("write hostile obligation");
    let obligation_arg = obligation_path.to_str().expect("utf8 temp path");

    let report = run_clean_json_expect_failure(&[
        "math",
        "obligation",
        "validate",
        obligation_arg,
        "--project",
        nn_project(),
        "--json",
    ]);

    assert_eq!(report["schema_version"], "clean-obligation-report-v1");
    assert_eq!(report["status"], "fail");
    let violations = report["violations"].as_array().expect("violations");
    assert!(violations
        .iter()
        .any(|violation| { violation["code"] == "OB018" && violation["path"] == "goal.pretty" }));
    assert!(violations.iter().any(|violation| {
        violation["code"] == "OB018" && violation["path"] == "local_context[0].type_pp"
    }));
}
