// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Geometry benchmark command handlers.

use crate::cli::bench::BenchCommands;
use clean_kernel::cert::benchmark::{BenchmarkConfig, BenchmarkRunner};
use clean_kernel::cert::problem::GeometryProblem;
use serde::Serialize;
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;
use std::time::{SystemTime, UNIX_EPOCH};

const SUITE_VERSION: &str = "public-benchmark-suite-v1";
const FRESHNESS_DAYS: u64 = 14;
const PENDING_STATUS: &str = "pending-publication";
const PUBLISHED_STATUS: &str = "published";
const PUBLIC_SUITES: &[&str] = &["kernel-perf", "server-perf"];
const RUNNER: &str = "./scripts/run_public_benchmarks.sh";
const CHECKER: &str = "python3 scripts/check_benchmark_publication.py --check";

const CANONICAL_INPUTS: &[&str] = &[
    "Cargo.toml",
    "Cargo.lock",
    "crates/clean-kernel/Cargo.toml",
    "crates/clean-kernel/benches/kernel_bench.rs",
    "crates/clean-kernel/benches/cert_macro_bench.rs",
    "crates/clean-server/Cargo.toml",
    "crates/clean-server/benches/server_ops.rs",
    "evals/registry/kernel-perf.yaml",
    "evals/registry/server-perf.yaml",
    "scripts/capture_benchmark_env.py",
    "scripts/check_benchmark_publication.py",
    "scripts/run_public_benchmarks.sh",
];

const REQUIRED_RUN_ARTIFACTS: &[&str] = &[
    "run_context.json",
    "raw/kernel_bench.stdout.txt",
    "raw/cert_macro_bench.stdout.txt",
    "raw/server_ops.stdout.txt",
    "logs/kernel_bench.stderr.log",
    "logs/cert_macro_bench.stderr.log",
    "logs/server_ops.stderr.log",
    "raw/criterion/kernel_bench",
    "raw/criterion/cert_macro_bench",
    "raw/criterion/server_ops",
];

/// Handle bench subcommands
pub(crate) fn handle_bench_command(command: BenchCommands) -> anyhow::Result<()> {
    match command {
        BenchCommands::Run {
            suite,
            output,
            verbose,
            timeout,
            no_verify,
            max_problems,
            only,
            skip,
        } => bench_run(
            suite,
            output,
            verbose,
            timeout,
            no_verify,
            max_problems,
            only,
            skip,
        ),
        BenchCommands::List { suite, verbose } => bench_list(suite, verbose),
        BenchCommands::Info { problem, suite } => bench_info(&problem, suite),
        BenchCommands::Verify {
            problem,
            suite,
            verbose,
        } => bench_verify(&problem, suite, verbose),
        BenchCommands::PublicationCheck {
            launch,
            json,
            repo_root,
            publication_root,
            today,
        } => bench_publication_check(launch, json, repo_root, publication_root, today),
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct HashRecord {
    bytes: u64,
    sha256: String,
}

#[derive(Debug, Serialize)]
struct PublicationCheckReport {
    schema_version: u64,
    command: &'static str,
    ok: bool,
    launch: bool,
    repo_root: String,
    publication_root: String,
    current_json: String,
    today: String,
    status: Option<String>,
    current_run: Option<String>,
    publication_commit: Option<String>,
    checked: Vec<&'static str>,
    errors: Vec<String>,
}

fn canonical_commands() -> BTreeMap<&'static str, &'static str> {
    BTreeMap::from([
        (
            "cert_macro_bench",
            "cargo bench --locked --message-format=short -j 1 --package clean-kernel --bench cert_macro_bench -- --output-format bencher",
        ),
        (
            "kernel_bench",
            "cargo bench --locked --message-format=short -j 1 --package clean-kernel --bench kernel_bench -- --output-format bencher",
        ),
        (
            "server_ops",
            "cargo bench --locked --message-format=short -j 1 --package clean-server --bench server_ops -- --output-format bencher",
        ),
    ])
}

fn bench_publication_check(
    launch: bool,
    json: bool,
    repo_root: Option<PathBuf>,
    publication_root: Option<PathBuf>,
    today: Option<String>,
) -> anyhow::Result<()> {
    let repo_root = repo_root
        .unwrap_or(std::env::current_dir()?)
        .canonicalize()
        .unwrap_or_else(|_| PathBuf::from("."));
    let publication_root =
        publication_root.unwrap_or_else(|| repo_root.join("reports/benchmarks/publication"));
    let today = today.unwrap_or_else(today_utc_iso);
    let report = check_publication_evidence(&repo_root, &publication_root, &today, launch);

    if json {
        println!("{}", serde_json::to_string_pretty(&report)?);
    } else if report.ok {
        println!("CLEAN: benchmark publication contract is current");
    } else {
        for error in &report.errors {
            eprintln!("ERROR: {error}");
        }
    }

    if report.ok {
        Ok(())
    } else {
        anyhow::bail!("benchmark publication check failed")
    }
}

fn check_publication_evidence(
    repo_root: &Path,
    publication_root: &Path,
    today: &str,
    launch: bool,
) -> PublicationCheckReport {
    let current_path = publication_root.join("current.json");
    let mut errors = Vec::new();
    let mut checked = vec![
        "current-json",
        "canonical-commands",
        "canonical-inputs",
        "reachable-source-commit",
    ];
    if launch {
        checked.extend([
            "published-status",
            "freshness",
            "required-artifacts",
            "dirty-evidence",
            "publication-commit-artifact-hashes",
        ]);
    }

    let mut status = None;
    let mut current_run = None;
    let mut publication_commit = None;

    let current = match read_json_object(&current_path) {
        Ok(current) => current,
        Err(error) => {
            errors.push(error);
            return publication_report(
                launch,
                repo_root,
                publication_root,
                &current_path,
                today,
                status,
                current_run,
                publication_commit,
                checked,
                errors,
            );
        }
    };

    status = current
        .get("status")
        .and_then(Value::as_str)
        .map(str::to_owned);
    current_run = current
        .get("current_run")
        .and_then(Value::as_str)
        .map(str::to_owned);
    publication_commit = current
        .get("publication_commit")
        .and_then(Value::as_str)
        .map(str::to_owned);

    validate_static_contract(&current, &mut errors);
    validate_source_commit(repo_root, &current, &mut errors);
    validate_input_hashes(repo_root, &current, &mut errors);
    validate_status_and_artifacts(
        repo_root,
        publication_root,
        &current,
        today,
        launch,
        &mut errors,
    );

    publication_report(
        launch,
        repo_root,
        publication_root,
        &current_path,
        today,
        status,
        current_run,
        publication_commit,
        checked,
        errors,
    )
}

fn publication_report(
    launch: bool,
    repo_root: &Path,
    publication_root: &Path,
    current_path: &Path,
    today: &str,
    status: Option<String>,
    current_run: Option<String>,
    publication_commit: Option<String>,
    checked: Vec<&'static str>,
    errors: Vec<String>,
) -> PublicationCheckReport {
    PublicationCheckReport {
        schema_version: 1,
        command: "clean bench publication-check",
        ok: errors.is_empty(),
        launch,
        repo_root: repo_root.display().to_string(),
        publication_root: publication_root.display().to_string(),
        current_json: current_path.display().to_string(),
        today: today.to_owned(),
        status,
        current_run,
        publication_commit,
        checked,
        errors,
    }
}

fn read_json_object(path: &Path) -> Result<serde_json::Map<String, Value>, String> {
    let text = fs::read_to_string(path).map_err(|error| {
        format!(
            "missing benchmark publication pointer: {}: {error}",
            path.display()
        )
    })?;
    let value: Value = serde_json::from_str(&text)
        .map_err(|error| format!("{} must be valid JSON: {error}", path.display()))?;
    value
        .as_object()
        .cloned()
        .ok_or_else(|| format!("{} must contain a JSON object", path.display()))
}

fn validate_static_contract(current: &serde_json::Map<String, Value>, errors: &mut Vec<String>) {
    if current.get("schema_version").and_then(Value::as_u64) != Some(1) {
        errors.push("current.json schema_version must be 1".to_owned());
    }
    if current.get("suite_version").and_then(Value::as_str) != Some(SUITE_VERSION) {
        errors.push(format!(
            "current.json suite_version must be {SUITE_VERSION}"
        ));
    }
    if string_array(current.get("suites")) != Some(PUBLIC_SUITES.to_vec()) {
        errors.push(format!("current.json suites must be {PUBLIC_SUITES:?}"));
    }
    if current.get("commands") != Some(&serde_json::json!(canonical_commands())) {
        errors.push("current.json commands do not match canonical benchmark commands".to_owned());
    }
    if current.get("freshness_days").and_then(Value::as_u64) != Some(FRESHNESS_DAYS) {
        errors.push(format!(
            "current.json freshness_days must be {FRESHNESS_DAYS}"
        ));
    }
    if current.get("runner").and_then(Value::as_str) != Some(RUNNER) {
        errors.push(format!("current.json runner must be {RUNNER}"));
    }
    if current.get("checker").and_then(Value::as_str) != Some(CHECKER) {
        errors.push(format!("current.json checker must be {CHECKER}"));
    }
    validate_utc_timestamp(current.get("updated_at"), "current.json updated_at", errors);
}

fn validate_source_commit(
    repo_root: &Path,
    current: &serde_json::Map<String, Value>,
    errors: &mut Vec<String>,
) {
    let Some(source_commit) = current.get("source_commit").and_then(Value::as_str) else {
        errors.push("current.json source_commit must be a full 40-character git SHA".to_owned());
        return;
    };
    if !is_full_sha(source_commit) {
        errors.push("current.json source_commit must be a full 40-character git SHA".to_owned());
        return;
    }
    if !git_success(
        repo_root,
        &["merge-base", "--is-ancestor", source_commit, "HEAD"],
    ) {
        errors.push(format!(
            "current.json source_commit {source_commit} is not reachable from current repository history"
        ));
    }
}

fn validate_input_hashes(
    repo_root: &Path,
    current: &serde_json::Map<String, Value>,
    errors: &mut Vec<String>,
) {
    let Some(expected_inputs) = current.get("inputs").and_then(Value::as_object) else {
        errors.push("current.json inputs must be an object".to_owned());
        return;
    };
    if expected_inputs.len() != CANONICAL_INPUTS.len()
        || !CANONICAL_INPUTS
            .iter()
            .all(|rel_path| expected_inputs.contains_key(*rel_path))
    {
        errors.push("current.json inputs must exactly match canonical benchmark inputs".to_owned());
        return;
    }

    let source_commit = current.get("source_commit").and_then(Value::as_str);
    for rel_path in CANONICAL_INPUTS {
        let Some(expected) = expected_inputs.get(*rel_path).and_then(Value::as_object) else {
            errors.push(format!("input {rel_path} hash entry must be an object"));
            continue;
        };
        if let Ok(actual) = sha256_file(&repo_root.join(rel_path)) {
            compare_hash_record(expected, &actual, &format!("input {rel_path}"), errors);
        } else {
            errors.push(format!("canonical benchmark input is missing: {rel_path}"));
        }
        if let Some(commit) = source_commit.filter(|commit| is_full_sha(commit)) {
            match git_blob_hash(repo_root, &format!("{commit}:{rel_path}")) {
                Ok(actual) => {
                    compare_hash_record(
                        expected,
                        &actual,
                        &format!("source_commit input {rel_path}"),
                        errors,
                    );
                }
                Err(error) => errors.push(format!(
                    "canonical benchmark input is missing from current.json source_commit {commit}: {rel_path}: {error}"
                )),
            }
        }
    }
}

fn validate_status_and_artifacts(
    repo_root: &Path,
    publication_root: &Path,
    current: &serde_json::Map<String, Value>,
    today: &str,
    launch: bool,
    errors: &mut Vec<String>,
) {
    match current.get("status").and_then(Value::as_str) {
        Some(PENDING_STATUS) => {
            for field in ["current_run", "fresh_until", "artifact_root", "run_context"] {
                if current.get(field).is_some_and(|value| !value.is_null()) {
                    errors.push(format!("current.json {field} must be null while pending"));
                }
            }
            validate_required_artifact_list(current, errors);
            if launch {
                errors.push(
                    "launch benchmark publication requires current.json status 'published'; pending-publication is not sufficient for public performance claims. Run ./scripts/run_public_benchmarks.sh from a clean checkout to create real benchmark artifacts, then commit reports/benchmarks/publication/current.json and the generated run directory, record a reachable publication_commit, and rerun --launch. Do not manually mark pending metadata as published.".to_owned(),
                );
            }
        }
        Some(PUBLISHED_STATUS) => {
            validate_publication_commit_reachable(repo_root, current, errors);
            validate_freshness(current, today, errors);
            validate_published_artifacts(repo_root, publication_root, current, errors);
            if launch {
                validate_launch_dirty_evidence(repo_root, publication_root, current, errors);
                validate_publication_commit_artifacts(repo_root, current, errors);
            }
        }
        Some(other) => errors.push(format!(
            "current.json status must be one of ['pending-publication', 'published'], got {other:?}"
        )),
        None => errors.push(
            "current.json status must be one of ['pending-publication', 'published']".to_owned(),
        ),
    }
}

fn validate_publication_commit_reachable(
    repo_root: &Path,
    current: &serde_json::Map<String, Value>,
    errors: &mut Vec<String>,
) {
    let Some(commit) = current.get("publication_commit").and_then(Value::as_str) else {
        errors
            .push("current.json publication_commit must be a full 40-character git SHA".to_owned());
        return;
    };
    if !is_full_sha(commit) {
        errors
            .push("current.json publication_commit must be a full 40-character git SHA".to_owned());
        return;
    }
    if !git_success(repo_root, &["merge-base", "--is-ancestor", commit, "HEAD"]) {
        errors.push(format!(
            "current.json publication_commit {commit} is not reachable from current repository history"
        ));
    }
}

fn validate_freshness(
    current: &serde_json::Map<String, Value>,
    today: &str,
    errors: &mut Vec<String>,
) {
    let Some(fresh_until) = current.get("fresh_until").and_then(Value::as_str) else {
        errors.push("current.json fresh_until must be an ISO date (YYYY-MM-DD)".to_owned());
        return;
    };
    if !is_iso_date(fresh_until) {
        errors.push("current.json fresh_until must be an ISO date (YYYY-MM-DD)".to_owned());
        return;
    }
    if !is_iso_date(today) {
        errors.push("--today must be an ISO date (YYYY-MM-DD)".to_owned());
        return;
    }
    if fresh_until < today {
        errors.push(format!(
            "benchmark publication metadata is stale: fresh_until={fresh_until} today={today}"
        ));
    }
}

fn validate_published_artifacts(
    repo_root: &Path,
    publication_root: &Path,
    current: &serde_json::Map<String, Value>,
    errors: &mut Vec<String>,
) {
    let Some(run_id) = current.get("current_run").and_then(Value::as_str) else {
        errors.push("current.json current_run must be a non-empty run id".to_owned());
        return;
    };
    if !is_safe_run_id(run_id) {
        errors.push("current.json current_run must be a safe run id".to_owned());
        return;
    }

    let run_dir = publication_root.join(run_id);
    let artifact_root = match repo_relative_path(repo_root, &run_dir) {
        Ok(path) => path,
        Err(error) => {
            errors.push(error);
            return;
        }
    };
    if current.get("artifact_root").and_then(Value::as_str) != Some(artifact_root.as_str()) {
        errors.push(format!(
            "current.json artifact_root must point at {artifact_root}"
        ));
    }
    let expected_run_context = format!("{artifact_root}/run_context.json");
    if current.get("run_context").and_then(Value::as_str) != Some(expected_run_context.as_str()) {
        errors.push(format!(
            "current.json run_context must point at {artifact_root}/run_context.json"
        ));
    }
    validate_required_artifact_list(current, errors);

    let Some(expected_artifacts) = current.get("artifacts").and_then(Value::as_object) else {
        errors.push("current.json artifacts must be an object for published runs".to_owned());
        return;
    };
    if expected_artifacts.len() != REQUIRED_RUN_ARTIFACTS.len()
        || !REQUIRED_RUN_ARTIFACTS
            .iter()
            .all(|rel_path| expected_artifacts.contains_key(*rel_path))
    {
        errors
            .push("current.json artifacts must exactly match required public artifacts".to_owned());
        return;
    }
    for rel_path in REQUIRED_RUN_ARTIFACTS {
        let path = run_dir.join(rel_path);
        let Some(expected) = expected_artifacts.get(*rel_path).and_then(Value::as_object) else {
            errors.push(format!("artifact {rel_path} hash entry must be an object"));
            continue;
        };
        match sha256_artifact(&path) {
            Ok(actual) => compare_hash_record(expected, &actual, &format!("artifact {rel_path}"), errors),
            Err(error) => errors.push(format!(
                "current run directory is missing required artifact: {artifact_root}/{rel_path}: {error}"
            )),
        }
    }
    validate_run_context_schema(&run_dir.join("run_context.json"), errors);
}

fn validate_required_artifact_list(
    current: &serde_json::Map<String, Value>,
    errors: &mut Vec<String>,
) {
    if string_array(current.get("required_artifacts")) != Some(REQUIRED_RUN_ARTIFACTS.to_vec()) {
        errors.push("current.json required_artifacts must match the public contract".to_owned());
    }
}

fn validate_launch_dirty_evidence(
    repo_root: &Path,
    publication_root: &Path,
    current: &serde_json::Map<String, Value>,
    errors: &mut Vec<String>,
) {
    let mut rel_paths =
        vec![
            match repo_relative_path(repo_root, &publication_root.join("current.json")) {
                Ok(path) => path,
                Err(error) => {
                    errors.push(error);
                    return;
                }
            },
        ];
    if let Some(run_id) = current.get("current_run").and_then(Value::as_str) {
        match repo_relative_path(repo_root, &publication_root.join(run_id)) {
            Ok(path) => rel_paths.push(path),
            Err(error) => errors.push(error),
        }
    }
    let rel_refs: Vec<&str> = rel_paths.iter().map(String::as_str).collect();
    match git_output(repo_root, &["status", "--porcelain=v1", "--"], &rel_refs) {
        Ok(status) if status.trim().is_empty() => {}
        Ok(status) => {
            let dirty = parse_git_status_paths(&status);
            errors.push(format!(
                "launch benchmark evidence has uncommitted changes: {}; commit current.json and current run artifacts before publishing public performance claims",
                dirty.join(", ")
            ));
        }
        Err(error) => errors.push(format!(
            "unable to inspect launch benchmark evidence dirtiness: {error}"
        )),
    }
}

fn validate_publication_commit_artifacts(
    repo_root: &Path,
    current: &serde_json::Map<String, Value>,
    errors: &mut Vec<String>,
) {
    let Some(commit) = current
        .get("publication_commit")
        .and_then(Value::as_str)
        .filter(|commit| is_full_sha(commit))
    else {
        return;
    };
    let Some(artifact_root) = current.get("artifact_root").and_then(Value::as_str) else {
        return;
    };
    let Some(expected_artifacts) = current.get("artifacts").and_then(Value::as_object) else {
        return;
    };
    for rel_path in REQUIRED_RUN_ARTIFACTS {
        let Some(expected) = expected_artifacts.get(*rel_path).and_then(Value::as_object) else {
            continue;
        };
        let committed_path = format!("{artifact_root}/{rel_path}");
        match git_artifact_hash(repo_root, commit, &committed_path) {
            Ok(actual) => compare_hash_record(
                expected,
                &actual,
                &format!("publication_commit artifact {rel_path}"),
                errors,
            ),
            Err(error) => errors.push(format!(
                "publication_commit is missing committed benchmark artifact: {commit}:{committed_path}: {error}"
            )),
        }
    }
}

fn string_array(value: Option<&Value>) -> Option<Vec<&str>> {
    value?
        .as_array()?
        .iter()
        .map(Value::as_str)
        .collect::<Option<Vec<_>>>()
}

fn validate_utc_timestamp(value: Option<&Value>, field: &str, errors: &mut Vec<String>) {
    let Some(text) = value.and_then(Value::as_str) else {
        errors.push(format!(
            "{field} must be a UTC timestamp like YYYY-MM-DDTHH:MM:SSZ"
        ));
        return;
    };
    let valid = text.len() == 20
        && text.as_bytes().get(4) == Some(&b'-')
        && text.as_bytes().get(7) == Some(&b'-')
        && text.as_bytes().get(10) == Some(&b'T')
        && text.as_bytes().get(13) == Some(&b':')
        && text.as_bytes().get(16) == Some(&b':')
        && text.as_bytes().get(19) == Some(&b'Z')
        && text
            .bytes()
            .enumerate()
            .all(|(idx, byte)| matches!(idx, 4 | 7 | 10 | 13 | 16 | 19) || byte.is_ascii_digit());
    if !valid {
        errors.push(format!(
            "{field} must be a UTC timestamp like YYYY-MM-DDTHH:MM:SSZ"
        ));
    }
}

fn validate_run_context_schema(path: &Path, errors: &mut Vec<String>) {
    let context = match read_json_object(path) {
        Ok(context) => context,
        Err(error) => {
            errors.push(error);
            return;
        }
    };
    if context.get("command").and_then(Value::as_str) != Some(SUITE_VERSION) {
        errors.push(format!(
            "{} command must be {SUITE_VERSION:?}",
            path.display()
        ));
    }
    if context.get("dirty").and_then(Value::as_bool) != Some(false) {
        errors.push(format!(
            "{} dirty must be false for published benchmarks",
            path.display()
        ));
    }
    let commit = context.get("commit").and_then(Value::as_str).unwrap_or("");
    if !(7..=40).contains(&commit.len())
        || !commit
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        errors.push(format!(
            "{} commit must be a 7-40 character lowercase git SHA",
            path.display()
        ));
    }
    for field in ["branch", "timestamp"] {
        let is_missing_or_empty = match context.get(field).and_then(Value::as_str) {
            Some(value) => value.is_empty(),
            None => true,
        };
        if is_missing_or_empty {
            errors.push(format!(
                "{} {field} must be a non-empty string",
                path.display()
            ));
        }
    }
    validate_utc_timestamp(
        context.get("timestamp"),
        &format!("{} timestamp", path.display()),
        errors,
    );

    for object_name in ["machine", "toolchain"] {
        if !context.get(object_name).is_some_and(Value::is_object) {
            errors.push(format!(
                "{} {object_name} must be an object",
                path.display()
            ));
        }
    }
}

fn compare_hash_record(
    expected: &serde_json::Map<String, Value>,
    actual: &HashRecord,
    label: &str,
    errors: &mut Vec<String>,
) {
    if expected.get("sha256").and_then(Value::as_str) != Some(actual.sha256.as_str()) {
        errors.push(format!("{label} sha256 mismatch"));
    }
    if expected.get("bytes").and_then(Value::as_u64) != Some(actual.bytes) {
        errors.push(format!("{label} byte count mismatch"));
    }
}

fn sha256_file(path: &Path) -> std::io::Result<HashRecord> {
    let mut file = fs::File::open(path)?;
    let mut digest = Sha256::new();
    let mut bytes = 0u64;
    let mut buffer = [0u8; 1024 * 64];
    loop {
        let read = file.read(&mut buffer)?;
        if read == 0 {
            break;
        }
        bytes += read as u64;
        digest.update(&buffer[..read]);
    }
    Ok(HashRecord {
        bytes,
        sha256: digest
            .finalize()
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect::<String>(),
    })
}

fn sha256_bytes(data: &[u8]) -> HashRecord {
    HashRecord {
        bytes: data.len() as u64,
        sha256: Sha256::digest(data)
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect::<String>(),
    }
}

fn sha256_artifact(path: &Path) -> std::io::Result<HashRecord> {
    if path.is_dir() {
        sha256_directory(path)
    } else {
        sha256_file(path)
    }
}

fn sha256_directory(path: &Path) -> std::io::Result<HashRecord> {
    let mut children = Vec::new();
    collect_files(path, path, &mut children)?;
    children.sort_by_key(|(rel_path, _)| path_sort_key(rel_path));
    let mut digest = Sha256::new();
    let mut bytes = 0u64;
    for (rel_path, child) in children {
        let file_hash = sha256_file(&child)?;
        digest.update(rel_path.as_bytes());
        digest.update(b"\0");
        bytes += file_hash.bytes;
        digest.update(file_hash.bytes.to_string().as_bytes());
        digest.update(b"\0");
        digest.update(file_hash.sha256.as_bytes());
        digest.update(b"\0");
    }
    Ok(HashRecord {
        bytes,
        sha256: digest
            .finalize()
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect::<String>(),
    })
}

fn collect_files(
    root: &Path,
    path: &Path,
    out: &mut Vec<(String, PathBuf)>,
) -> std::io::Result<()> {
    for entry in fs::read_dir(path)? {
        let entry = entry?;
        let child = entry.path();
        if child.is_dir() {
            collect_files(root, &child, out)?;
        } else if child.is_file() {
            let rel_path = child
                .strip_prefix(root)
                .unwrap_or(&child)
                .to_string_lossy()
                .replace('\\', "/");
            out.push((rel_path, child));
        }
    }
    Ok(())
}

fn path_sort_key(path: &str) -> Vec<String> {
    path.split('/').map(str::to_owned).collect()
}

fn git_blob_hash(repo_root: &Path, object_name: &str) -> Result<HashRecord, String> {
    git_bytes(repo_root, &["cat-file", "-p", object_name]).map(|bytes| sha256_bytes(&bytes))
}

fn git_artifact_hash(repo_root: &Path, commit: &str, rel_path: &str) -> Result<HashRecord, String> {
    let object_name = format!("{commit}:{rel_path}");
    let object_type = git_output(repo_root, &["cat-file", "-t", &object_name], &[])?
        .trim()
        .to_owned();
    match object_type.as_str() {
        "blob" => git_blob_hash(repo_root, &object_name),
        "tree" => git_tree_hash(repo_root, commit, rel_path),
        other => Err(format!("{object_name} is {other}, not a file or directory")),
    }
}

fn git_tree_hash(repo_root: &Path, commit: &str, rel_path: &str) -> Result<HashRecord, String> {
    let output = git_bytes(repo_root, &["ls-tree", "-rz", "-r", commit, "--", rel_path])?;
    let prefix = format!("{}/", rel_path.trim_end_matches('/'));
    let mut entries = Vec::new();
    for record in output
        .split(|byte| *byte == 0)
        .filter(|record| !record.is_empty())
    {
        let tab = record
            .iter()
            .position(|byte| *byte == b'\t')
            .ok_or_else(|| "git ls-tree output missing path separator".to_owned())?;
        let meta = std::str::from_utf8(&record[..tab])
            .map_err(|error| format!("git ls-tree metadata is not UTF-8: {error}"))?;
        let path = std::str::from_utf8(&record[tab + 1..])
            .map_err(|error| format!("git ls-tree path is not UTF-8: {error}"))?;
        let mut meta_fields = meta.split_whitespace();
        let _mode = meta_fields.next();
        let object_type = meta_fields.next();
        let object_id = meta_fields.next();
        if object_type != Some("blob") {
            return Err(format!("{commit}:{path} is not a file"));
        }
        let object_id =
            object_id.ok_or_else(|| "git ls-tree output missing object id".to_owned())?;
        let child_rel = path
            .strip_prefix(&prefix)
            .ok_or_else(|| format!("{commit}:{path} is outside expected root {rel_path}"))?;
        let data = git_bytes(repo_root, &["cat-file", "-p", object_id])?;
        entries.push((child_rel.to_owned(), sha256_bytes(&data)));
    }
    entries.sort_by_key(|(rel_path, _)| path_sort_key(rel_path));
    let mut digest = Sha256::new();
    let mut bytes = 0u64;
    for (child_rel, file_hash) in entries {
        digest.update(child_rel.as_bytes());
        digest.update(b"\0");
        bytes += file_hash.bytes;
        digest.update(file_hash.bytes.to_string().as_bytes());
        digest.update(b"\0");
        digest.update(file_hash.sha256.as_bytes());
        digest.update(b"\0");
    }
    Ok(HashRecord {
        bytes,
        sha256: digest
            .finalize()
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect::<String>(),
    })
}

fn git_success(repo_root: &Path, args: &[&str]) -> bool {
    Command::new("git")
        .arg("-C")
        .arg(repo_root)
        .args(args)
        .output()
        .is_ok_and(|output| output.status.success())
}

fn git_output(
    repo_root: &Path,
    fixed_args: &[&str],
    trailing_args: &[&str],
) -> Result<String, String> {
    let output = Command::new("git")
        .arg("-C")
        .arg(repo_root)
        .args(fixed_args)
        .args(trailing_args)
        .output()
        .map_err(|error| error.to_string())?;
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).trim().to_owned());
    }
    Ok(String::from_utf8_lossy(&output.stdout).into_owned())
}

fn git_bytes(repo_root: &Path, args: &[&str]) -> Result<Vec<u8>, String> {
    let output = Command::new("git")
        .arg("-C")
        .arg(repo_root)
        .args(args)
        .output()
        .map_err(|error| error.to_string())?;
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).trim().to_owned());
    }
    Ok(output.stdout)
}

fn parse_git_status_paths(status: &str) -> Vec<String> {
    status
        .lines()
        .map(|line| {
            if line.len() >= 4 && (line.starts_with("R ") || line.starts_with("C ")) {
                line.split(" -> ").last().unwrap_or(line).to_owned()
            } else if line.len() >= 3 {
                line[3..].to_owned()
            } else {
                line.to_owned()
            }
        })
        .collect()
}

fn repo_relative_path(repo_root: &Path, path: &Path) -> Result<String, String> {
    let path = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    let repo_root = repo_root
        .canonicalize()
        .unwrap_or_else(|_| repo_root.to_path_buf());
    path.strip_prefix(&repo_root)
        .map(|path| path.to_string_lossy().replace('\\', "/"))
        .map_err(|_| {
            format!(
                "benchmark publication evidence path must live inside repository root: {}",
                path.display()
            )
        })
}

fn is_full_sha(value: &str) -> bool {
    value.len() == 40
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn is_safe_run_id(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && !value.contains('/')
        && !value.contains('\\')
        && !value.contains("..")
        && !Path::new(value).is_absolute()
        && value.bytes().enumerate().all(|(idx, byte)| {
            byte.is_ascii_alphanumeric() || ((idx > 0) && matches!(byte, b'.' | b'_' | b'-'))
        })
}

fn is_iso_date(value: &str) -> bool {
    if value.len() != 10
        || value.as_bytes().get(4) != Some(&b'-')
        || value.as_bytes().get(7) != Some(&b'-')
    {
        return false;
    }
    let year = value[0..4].parse::<u32>().ok();
    let month = value[5..7].parse::<u32>().ok();
    let day = value[8..10].parse::<u32>().ok();
    matches!((year, month, day), (Some(_), Some(1..=12), Some(1..=31)))
}

fn today_utc_iso() -> String {
    let days = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|duration| (duration.as_secs() / 86_400) as i64)
        .unwrap_or(0);
    let (year, month, day) = civil_from_days(days);
    format!("{year:04}-{month:02}-{day:02}")
}

fn civil_from_days(days_since_unix_epoch: i64) -> (i32, u32, u32) {
    let z = days_since_unix_epoch + 719_468;
    let era = if z >= 0 { z } else { z - 146_096 } / 146_097;
    let doe = z - era * 146_097;
    let yoe = (doe - doe / 1_460 + doe / 36_524 - doe / 146_096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = mp + if mp < 10 { 3 } else { -9 };
    let year = y + i64::from(m <= 2);
    (year as i32, m as u32, d as u32)
}

/// Get the default suite directory
fn default_suite_dir() -> PathBuf {
    // Try to find the benchmarks directory relative to cwd or the project root
    let cwd = std::env::current_dir().unwrap_or_default();

    // Check current directory first
    let local = cwd.join("benchmarks/geometry/alphageometry");
    if local.exists() {
        return local;
    }

    // Try project root (for when running from subdirectory)
    let mut dir = cwd.clone();
    while dir.parent().is_some() {
        let candidate = dir.join("benchmarks/geometry/alphageometry");
        if candidate.exists() {
            return candidate;
        }
        dir = dir.parent().unwrap().to_path_buf();
    }

    // Fallback to relative path (will error if not found)
    PathBuf::from("benchmarks/geometry/alphageometry")
}

/// Run geometry benchmarks
fn bench_run(
    suite: Option<PathBuf>,
    output: Option<PathBuf>,
    verbose: bool,
    timeout: u64,
    no_verify: bool,
    max_problems: usize,
    only: Option<String>,
    skip: Option<String>,
) -> anyhow::Result<()> {
    let suite_dir = suite.unwrap_or_else(default_suite_dir);

    if verbose {
        println!("Running benchmarks from: {}", suite_dir.display());
    }

    // Parse comma-separated problem IDs
    let only_problems: Vec<String> = only
        .map(|s| s.split(',').map(|p| p.trim().to_string()).collect())
        .unwrap_or_default();

    let skip_problems: Vec<String> = skip
        .map(|s| s.split(',').map(|p| p.trim().to_string()).collect())
        .unwrap_or_default();

    // Build configuration
    let config = BenchmarkConfig {
        timeout_ms: timeout,
        verify_certs: !no_verify,
        save_certs: output.is_some(),
        max_problems,
        continue_on_error: true,
        skip_problems,
        only_problems,
    };

    // Create runner
    let mut runner = BenchmarkRunner::new(&suite_dir)
        .map_err(|e| anyhow::anyhow!("Failed to create runner: {}", e))?
        .with_config(config);

    // Discover problems first
    let problems = runner
        .discover_problems()
        .map_err(|e| anyhow::anyhow!("Failed to discover problems: {}", e))?;

    println!(
        "Found {} problems in {}",
        problems.len(),
        runner.suite_name()
    );

    if problems.is_empty() {
        println!("No problems found!");
        return Ok(());
    }

    // Run benchmarks
    let start = Instant::now();
    let results = runner
        .run_all()
        .map_err(|e| anyhow::anyhow!("Benchmark failed: {}", e))?;
    let duration = start.elapsed();

    // Print results
    println!();
    println!("=== Benchmark Results ===");
    println!("Suite: {}", runner.suite_name());
    println!("Problems: {}", results.total);
    println!("Solved: {} ({:.1}%)", results.solved, results.solve_rate());
    println!("Unsolved: {}", results.unsolved);
    println!("Errors: {}", results.errors);
    println!("Average solve time: {:.1} ms", results.avg_solve_time_ms());
    println!("Total time: {:.2}s", duration.as_secs_f64());

    if verbose {
        println!();
        println!("=== Problem Details ===");
        for sol in &results.results {
            let status = if sol.solved {
                "✓"
            } else if sol.error.is_some() {
                "✗"
            } else {
                "-"
            };
            print!("  {} {} ({} ms)", status, sol.problem_id, sol.solve_time_ms);
            if let Some(err) = &sol.error {
                print!(" - {}", err);
            }
            println!();
        }
    }

    // Save results if output specified
    if let Some(output_dir) = output {
        runner
            .save_results(&results, &output_dir)
            .map_err(|e| anyhow::anyhow!("Failed to save results: {}", e))?;
        println!();
        println!("Results saved to: {}", output_dir.display());
    }

    // Exit with error code if any problems failed
    if results.errors > 0 {
        std::process::exit(1);
    }

    Ok(())
}

/// List problems in a benchmark suite
fn bench_list(suite: Option<PathBuf>, verbose: bool) -> anyhow::Result<()> {
    let suite_dir = suite.unwrap_or_else(default_suite_dir);

    let runner = BenchmarkRunner::new(&suite_dir)
        .map_err(|e| anyhow::anyhow!("Failed to create runner: {}", e))?;

    let problems = runner
        .discover_problems()
        .map_err(|e| anyhow::anyhow!("Failed to discover problems: {}", e))?;

    println!(
        "Suite: {} ({} problems)",
        runner.suite_name(),
        problems.len()
    );
    println!();

    for problem in &problems {
        if verbose {
            let has_derivation = if problem.derivation.is_some() {
                "✓"
            } else {
                "-"
            };
            let difficulty = problem
                .problem
                .metadata
                .difficulty
                .map(|d| format!("L{}", d))
                .unwrap_or_else(|| "-".to_string());

            let tags = problem.problem.metadata.tags.join(", ");

            println!(
                "  {} {} [{:?}] derivation:{} tags:[{}]",
                problem.id, difficulty, problem.problem.goal, has_derivation, tags
            );

            if let Some(stmt) = &problem.problem.metadata.statement {
                println!("      {}", stmt);
            }
        } else {
            println!("  {}", problem.id);
        }
    }

    Ok(())
}

/// Show info about a specific problem
fn bench_info(problem: &str, suite: Option<PathBuf>) -> anyhow::Result<()> {
    let suite_dir = suite.unwrap_or_else(default_suite_dir);

    // Try to find problem by ID or path
    let problem_path = if PathBuf::from(problem).exists() {
        PathBuf::from(problem)
    } else {
        suite_dir.join(problem)
    };

    let problem_json_path = problem_path.join("problem.json");
    if !problem_json_path.exists() {
        anyhow::bail!(
            "Problem not found: {} (looked for {})",
            problem,
            problem_json_path.display()
        );
    }

    let geo_problem = GeometryProblem::from_file(&problem_json_path)
        .map_err(|e| anyhow::anyhow!("Failed to load problem: {}", e))?;

    println!("Problem: {}", geo_problem.id);
    println!();

    // Objects
    println!("Objects ({}):", geo_problem.objects.len());
    for (name, obj) in &geo_problem.objects {
        let def_str = if let Some(def) = &obj.definition {
            format!(" = {:?}", def)
        } else {
            String::new()
        };
        println!("  {} : {:?}{}", name, obj.obj_type, def_str);
    }
    println!();

    // Constraints
    println!("Constraints ({}):", geo_problem.constraints.len());
    for constraint in &geo_problem.constraints {
        println!("  {:?}", constraint);
    }
    println!();

    // Goal
    println!("Goal: {:?}", geo_problem.goal);
    println!();

    // Metadata
    let meta = &geo_problem.metadata;
    let has_metadata = meta.source.is_some()
        || meta.difficulty.is_some()
        || !meta.tags.is_empty()
        || meta.known_solvable.is_some()
        || meta.statement.is_some();

    if has_metadata {
        println!("Metadata:");
        if let Some(source) = &meta.source {
            println!("  Source: {}", source);
        }
        if let Some(diff) = meta.difficulty {
            println!("  Difficulty: {}", diff);
        }
        if !meta.tags.is_empty() {
            println!("  Tags: {}", meta.tags.join(", "));
        }
        if let Some(solvable) = meta.known_solvable {
            println!("  Known solvable: {}", solvable);
        }
        if let Some(stmt) = &meta.statement {
            println!("  Statement: {}", stmt);
        }
    }

    // Derivation status
    let derivation_json = problem_path.join("derivation.json");
    let derivation_txt = problem_path.join("derivation.txt");
    if derivation_json.exists() || derivation_txt.exists() {
        println!();
        println!("Derivation: Available");
    }

    Ok(())
}

/// Verify a single problem's derivation
fn bench_verify(problem: &str, suite: Option<PathBuf>, verbose: bool) -> anyhow::Result<()> {
    let suite_dir = suite.unwrap_or_else(default_suite_dir);

    // Try to find problem by ID or path
    let problem_path = if PathBuf::from(problem).exists() {
        PathBuf::from(problem)
    } else {
        suite_dir.join(problem)
    };

    let problem_json_path = problem_path.join("problem.json");
    if !problem_json_path.exists() {
        anyhow::bail!(
            "Problem not found: {} (looked for {})",
            problem,
            problem_json_path.display()
        );
    }

    if verbose {
        println!("Verifying problem: {}", problem);
    }

    // Create a runner just for this problem
    let config = BenchmarkConfig {
        verify_certs: true,
        only_problems: vec![problem.to_string()],
        ..Default::default()
    };

    let mut runner = BenchmarkRunner::new(&suite_dir)
        .map_err(|e| anyhow::anyhow!("Failed to create runner: {}", e))?
        .with_config(config);

    let problems = runner
        .discover_problems()
        .map_err(|e| anyhow::anyhow!("Failed to discover problems: {}", e))?;

    if problems.is_empty() {
        anyhow::bail!("Problem not found in suite: {}", problem);
    }

    let result = runner
        .run_single(&problems[0])
        .map_err(|e| anyhow::anyhow!("Verification failed: {}", e))?;

    if result.solved {
        println!(
            "✓ {} verified successfully ({} ms)",
            problem, result.solve_time_ms
        );
        if verbose {
            if let Some(derivation) = &result.derivation {
                println!("  Derivation steps: {}", derivation.len());
            }
        }
        Ok(())
    } else {
        let error = result.error.unwrap_or_else(|| "Unknown error".to_string());
        anyhow::bail!("✗ {} verification failed: {}", problem, error)
    }
}

#[cfg(test)]
mod publication_tests {
    use super::*;
    use tempfile::TempDir;

    fn git(repo: &Path, args: &[&str]) -> String {
        let output = Command::new("git")
            .arg("-C")
            .arg(repo)
            .args(args)
            .output()
            .expect("git should run");
        assert!(
            output.status.success(),
            "git {:?} failed: {}",
            args,
            String::from_utf8_lossy(&output.stderr)
        );
        String::from_utf8(output.stdout)
            .expect("git output should be UTF-8")
            .trim()
            .to_owned()
    }

    fn write_file(path: &Path, text: &str) {
        fs::create_dir_all(path.parent().expect("fixture file parent"))
            .expect("fixture parent should be created");
        fs::write(path, text).expect("fixture file should be written");
    }

    fn write_fixture_repo() -> TempDir {
        let temp = TempDir::new().expect("tempdir");
        git(temp.path(), &["init"]);
        git(temp.path(), &["config", "user.email", "bench@example.com"]);
        git(temp.path(), &["config", "user.name", "Bench Test"]);
        for rel_path in CANONICAL_INPUTS {
            write_file(
                &temp.path().join(rel_path),
                &format!("fixture for {rel_path}\n"),
            );
        }
        git(temp.path(), &["add", "."]);
        git(temp.path(), &["commit", "-m", "fixture"]);
        temp
    }

    fn pending_current(repo: &Path) -> Value {
        let inputs = CANONICAL_INPUTS
            .iter()
            .map(|rel_path| {
                let hash = sha256_file(&repo.join(rel_path)).expect("fixture input hash");
                (
                    (*rel_path).to_owned(),
                    serde_json::json!({
                        "bytes": hash.bytes,
                        "sha256": hash.sha256,
                    }),
                )
            })
            .collect::<serde_json::Map<_, _>>();
        serde_json::json!({
            "schema_version": 1,
            "suite_version": SUITE_VERSION,
            "status": PENDING_STATUS,
            "suites": PUBLIC_SUITES,
            "commands": canonical_commands(),
            "inputs": inputs,
            "freshness_days": FRESHNESS_DAYS,
            "source_commit": git(repo, &["rev-parse", "HEAD"]),
            "publication_commit": null,
            "updated_at": "2026-04-24T00:00:00Z",
            "runner": RUNNER,
            "checker": CHECKER,
            "current_run": null,
            "fresh_until": null,
            "artifact_root": null,
            "run_context": null,
            "required_artifacts": REQUIRED_RUN_ARTIFACTS,
        })
    }

    #[test]
    fn publication_check_missing_current_json_fails_closed() {
        let temp = TempDir::new().expect("tempdir");
        let report = check_publication_evidence(
            temp.path(),
            &temp.path().join("reports/benchmarks/publication"),
            "2026-04-24",
            true,
        );

        assert!(!report.ok);
        assert!(report.launch);
        assert!(report
            .errors
            .iter()
            .any(|error| error.contains("missing benchmark publication pointer")));
        assert!(report
            .checked
            .contains(&"publication-commit-artifact-hashes"));
        serde_json::to_string(&report).expect("report should serialize");
    }

    #[test]
    fn publication_check_launch_rejects_pending_publication_json() {
        let repo = write_fixture_repo();
        let publication_root = repo.path().join("reports/benchmarks/publication");
        fs::create_dir_all(&publication_root).expect("publication root");
        fs::write(
            publication_root.join("current.json"),
            serde_json::to_vec_pretty(&pending_current(repo.path())).expect("current json"),
        )
        .expect("current json write");

        let report = check_publication_evidence(repo.path(), &publication_root, "2026-04-24", true);

        assert!(!report.ok);
        assert_eq!(report.status.as_deref(), Some(PENDING_STATUS));
        assert!(report.errors.iter().any(|error| {
            error.contains("launch benchmark publication requires current.json status 'published'")
        }));
        assert!(report
            .errors
            .iter()
            .all(|error| !error.contains("canonical benchmark input")));
    }
}
