// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The Kernel Arena's Round 2026-09 battery as a must-reject gate: plan item
//! `checkers-arena-battery` of `docs/plans/LEAN4_UPSTREAM_DELTA_2026-10-16.md`.
//!
//! Every one of the archive's 193 tests (71 bad, 122 good, each a lean4export
//! 3.1.0 export of Lean 4.29.1) is run through the NDJSON front door
//! (`clean_export_check`, the engine of `clean olean replay --from-export`),
//! one process per test, under the timeout its YAML states at the round's
//! arena commit. A bad test must exit 1 and a good test 0; a decline (exit 2)
//! or a timeout is allowed only for a row of the reviewed declines table
//! (`tests/fixtures/kernel_arena/round-2026-09/declines.json`). Nothing
//! returns early: every test runs, then every failure is reported at once.
//!
//! Two counts are measured against the `--paranoid` consensus (the kernels
//! `lake check --paranoid` bundles at v4.35.0, as the round ran them):
//! `clean_accepts_consensus_rejects`, which must be 0, and
//! `clean_rejects_consensus_accepts`. With `CLEAN_ARENA_MINT=<file>` the run
//! also writes the round artifact (exit code, wall time and peak RSS per test,
//! the paranoid kernels' verdicts, the totals) to that file;
//! `test_kernel_arena_committed_artifact_is_consistent` re-derives the totals
//! of the committed one and refuses it unless both zero counts hold.
//!
//! A test's expected verdict comes from its directory in the sha256-pinned
//! archive (`bad/` must exit 1, `good/` must exit 0), never from the round
//! table, whose `outcome` must agree with it; a full run must see the
//! archive's 71 bad and 122 good tests.
//!
//! A wrong accept found here is a kernel soundness defect: it is reported, never
//! allowed by a table. The first run (2026-10-17) found one,
//! `bad/bugs/proj-of-subst-prop` (the lean4#14807 class); R85's `is_prop`
//! guard, which landed in parallel, closes it. A RELEASE run holds it as
//! must-reject (the battery against a release `clean_export_check`, the
//! committed artifact's consistency test, and `green_artifact_recheck.sh`'s
//! bad-half leg). A debug run cannot: the kernel's debug-only `infer_type`
//! invariant stops the replay first (exit 2, a debug-only declines row), so a
//! debug battery would stay green with R85 reverted; the battery's release
//! mutation arm (`data/gate_demonstrations.json`) is what shows it bites.

#[path = "support/kernel_arena.rs"]
mod kernel_arena;

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use serde_json::{json, Value};

/// The archive's bad tests (must exit 1) and good tests (must exit 0).
const ARCHIVE_BAD: usize = 71;
const ARCHIVE_GOOD: usize = 122;

/// A test's expected verdict, from its directory in the pinned archive.
fn expected_of(path: &str) -> Option<&'static str> {
    match path.split_once('/').map(|(group, _)| group) {
        Some("bad") => Some("reject"),
        Some("good") => Some("accept"),
        _ => None,
    }
}

/// The checker every test runs through: this build's `clean_export_check`,
/// or the binary `CLEAN_ARENA_CHECKER` names (a release build of the same
/// target, to mint a round artifact at release speed).
fn checker() -> PathBuf {
    std::env::var_os("CLEAN_ARENA_CHECKER").map_or_else(
        || PathBuf::from(env!("CARGO_BIN_EXE_clean_export_check")),
        PathBuf::from,
    )
}

/// The timeout of a test whose YAML states none: the battery's own bound, so
/// a hang fails the battery instead of hanging it.
const DEFAULT_TIMEOUT: Duration = Duration::from_secs(1800);

/// The arena's timeouts are for release builds; a debug test build runs the
/// kernel unoptimized, so its timeouts are scaled by this factor.
const DEBUG_TIMEOUT_FACTOR: u32 = 8;

/// A test is stopped once its resident set passes this many bytes, so one
/// perf export cannot take the host's memory (the arena's own runs reached
/// 6.8 GB on `perf/magma-list-deep-n36` with the official kernel), and the
/// battery's footprint stays what its suite weight says.
const DEFAULT_RSS_CAP_BYTES: u64 = 4 << 30;

/// `CLEAN_ARENA_<what>` as a number, or the default.
fn env_number(what: &str, default: u64) -> u64 {
    std::env::var(format!("CLEAN_ARENA_{what}"))
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(default)
}

/// The resident set of process `pid`, in bytes, when the platform says.
#[cfg(target_os = "macos")]
fn resident_bytes(pid: i32) -> Option<u64> {
    // SAFETY: an all-zero `proc_taskinfo` is a valid value of this plain C
    // struct, and `proc_pidinfo` writes at most `size` bytes into it.
    let mut info: libc::proc_taskinfo = unsafe { std::mem::zeroed() };
    let size = i32::try_from(size_of::<libc::proc_taskinfo>()).ok()?;
    // SAFETY: `info` is a live, exclusively borrowed local of `size` bytes.
    let got = unsafe {
        libc::proc_pidinfo(
            pid,
            libc::PROC_PIDTASKINFO,
            0,
            std::ptr::from_mut(&mut info).cast(),
            size,
        )
    };
    (got == size).then_some(info.pti_resident_size)
}

/// The resident set of process `pid`, in bytes, when the platform says.
#[cfg(not(target_os = "macos"))]
fn resident_bytes(pid: i32) -> Option<u64> {
    let statm = std::fs::read_to_string(format!("/proc/{pid}/statm")).ok()?;
    let pages: u64 = statm.split_whitespace().nth(1)?.parse().ok()?;
    Some(pages * 4096)
}

/// How one test ended.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Ending {
    Exit(i32),
    Signal(i32),
    Timeout,
    MemoryCap,
}

#[derive(Debug, Clone)]
struct Run {
    ending: Ending,
    wall: Duration,
    max_rss_bytes: u64,
    stderr_tail: String,
}

/// Spawn the checker on `file`, wait at most `limit`, and read its exit
/// status and peak RSS from `wait4`.
#[expect(
    clippy::zombie_processes,
    reason = "the child is reaped by `libc::wait4` below, which also returns its resource usage"
)]
fn run_checker(file: &Path, limit: Duration, rss_cap: u64) -> Run {
    let start = Instant::now();
    let stderr_path = file.with_extension("stderr");
    let stderr = std::fs::File::create(&stderr_path).expect("stderr capture file");
    let checker = checker();
    let child = std::process::Command::new(&checker)
        .arg(file)
        .stdout(std::process::Stdio::null())
        .stderr(stderr)
        .spawn()
        .unwrap_or_else(|e| panic!("spawning {}: {e}", checker.display()));
    let pid = i32::try_from(child.id()).expect("pid fits i32");
    let mut status: libc::c_int = 0;
    // SAFETY: an all-zero `rusage` is a valid value of this plain C struct.
    let mut usage: libc::rusage = unsafe { std::mem::zeroed() };
    let mut timed_out = false;
    let mut capped = false;
    loop {
        // SAFETY: `pid` is our own child, not yet reaped; `status` and
        // `usage` are live, exclusively borrowed locals.
        let reaped = unsafe { libc::wait4(pid, &mut status, libc::WNOHANG, &mut usage) };
        if reaped == pid {
            break;
        }
        assert!(reaped == 0, "wait4({pid}) failed");
        if !timed_out && !capped {
            if start.elapsed() > limit {
                timed_out = true;
            } else if resident_bytes(pid).is_some_and(|rss| rss > rss_cap) {
                capped = true;
            }
            if timed_out || capped {
                // SAFETY: signalling our own unreaped child.
                unsafe { libc::kill(pid, libc::SIGKILL) };
            }
        }
        std::thread::sleep(Duration::from_millis(5));
    }
    let wall = start.elapsed();
    let raw_rss = u64::try_from(usage.ru_maxrss).unwrap_or(0);
    // `ru_maxrss` is bytes on macOS and kilobytes on Linux.
    let max_rss_bytes = if cfg!(target_os = "macos") {
        raw_rss
    } else {
        raw_rss.saturating_mul(1024)
    };
    let ending = if timed_out {
        Ending::Timeout
    } else if capped {
        Ending::MemoryCap
    } else if libc::WIFEXITED(status) {
        Ending::Exit(libc::WEXITSTATUS(status))
    } else {
        Ending::Signal(libc::WTERMSIG(status))
    };
    let text = std::fs::read_to_string(&stderr_path).unwrap_or_default();
    let stderr_tail: String = text
        .lines()
        .rev()
        .take(3)
        .collect::<Vec<_>>()
        .into_iter()
        .rev()
        .collect::<Vec<_>>()
        .join(" | ");
    Run {
        ending,
        wall,
        max_rss_bytes,
        stderr_tail: stderr_tail.chars().take(600).collect(),
    }
}

/// One row of the reviewed table: the endings a test may have besides the
/// expected one, whether the row PINS a known gap (the test must still end
/// that way, so the day the gap closes the battery says so), and the checker
/// build profiles the allowance holds for (every profile when the row names
/// none).
#[derive(Debug, Clone)]
struct Reviewed {
    allows: Vec<String>,
    pinned: bool,
    profiles: Option<Vec<String>>,
}

impl Reviewed {
    /// The row lets a test end `ending` under a checker built as `profile`.
    fn allows(&self, ending: &str, profile: &str) -> bool {
        self.allows.iter().any(|a| a == ending)
            && self
                .profiles
                .as_ref()
                .is_none_or(|ps| ps.iter().any(|p| p == profile))
    }
}

/// The reviewed declines table (`declines.json`). A row may allow `decline`,
/// `timeout` or `memory-cap` (resource and representation limits, never a
/// finding) for any test, and `reject` only for a good test, as a PINNED
/// fidelity gap that names the plan item owning it. No row may allow
/// `accept`: a bad test that exits 0 is a wrong accept whatever any table
/// says. An unpinned row may name the build `profiles` its allowance holds
/// for (`debug`, `release`), so an ending only a debug build reaches is not
/// excused in release.
fn declines() -> BTreeMap<String, Reviewed> {
    let path = kernel_arena::round_dir().join("declines.json");
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("{}: the reviewed declines table: {e}", path.display()));
    let value: Value = serde_json::from_str(&text).expect("declines.json is JSON");
    value["rows"]
        .as_array()
        .expect("declines.json has rows")
        .iter()
        .map(|row| {
            let path = row["path"].as_str().expect("row path").to_owned();
            assert!(
                row["review"].as_str().is_some_and(|r| !r.is_empty()),
                "{path}: a declines row needs its review"
            );
            let allows: Vec<String> = row["allows"]
                .as_array()
                .expect("row allows")
                .iter()
                .map(|a| a.as_str().expect("allow").to_owned())
                .collect();
            for ending in &allows {
                assert!(
                    matches!(
                        ending.as_str(),
                        "decline" | "timeout" | "memory-cap" | "reject"
                    ),
                    "{path}: a declines row may not allow {ending:?}"
                );
            }
            let pinned = row["pinned"].as_bool().unwrap_or(false);
            if allows.iter().any(|a| a == "reject") {
                assert!(
                    path.starts_with("good/") && pinned,
                    "{path}: `reject` is allowed only as a pinned fidelity gap of a good test"
                );
                assert!(
                    row["owner"].as_str().is_some_and(|o| !o.is_empty()),
                    "{path}: a fidelity gap names the plan item that owns it"
                );
            }
            let profiles = row.get("profiles").map(|ps| {
                let ps: Vec<String> = ps
                    .as_array()
                    .expect("row profiles is an array")
                    .iter()
                    .map(|p| p.as_str().expect("profile").to_owned())
                    .collect();
                assert!(
                    !ps.is_empty() && ps.iter().all(|p| p == "debug" || p == "release"),
                    "{path}: profiles must name `debug` or `release`"
                );
                assert!(!pinned, "{path}: a pinned gap holds in every profile");
                ps
            });
            (
                path,
                Reviewed {
                    allows,
                    pinned,
                    profiles,
                },
            )
        })
        .collect()
}

/// The build profile of the checker the battery runs: a binary under a
/// `release` directory, else the profile of this test build.
fn checker_profile() -> &'static str {
    if checker().components().any(|c| c.as_os_str() == "release") || !cfg!(debug_assertions) {
        "release"
    } else {
        "debug"
    }
}

fn ending_label(ending: &Ending) -> String {
    match ending {
        Ending::Exit(0) => "accept".to_owned(),
        Ending::Exit(1) => "reject".to_owned(),
        Ending::Exit(2) => "decline".to_owned(),
        Ending::Exit(n) => format!("exit-{n}"),
        Ending::Signal(s) => format!("signal-{s}"),
        Ending::Timeout => "timeout".to_owned(),
        Ending::MemoryCap => "memory-cap".to_owned(),
    }
}

/// The totals an artifact's rows imply.
fn totals(rows: &[Value]) -> Value {
    let count = |pred: &dyn Fn(&Value) -> bool| rows.iter().filter(|r| pred(r)).count();
    let clean = |r: &Value| r["clean"].as_str().unwrap_or_default().to_owned();
    let group = |r: &Value| expected_of(r["path"].as_str().unwrap_or_default());
    json!({
        "tests": rows.len(),
        "bad": count(&|r| group(r) == Some("reject")),
        "good": count(&|r| group(r) == Some("accept")),
        "wrong_accept": count(&|r| group(r) == Some("reject") && clean(r) == "accept"),
        "wrong_reject": count(&|r| group(r) == Some("accept") && clean(r) == "reject"),
        "declines": count(&|r| clean(r) == "decline"),
        "timeouts": count(&|r| clean(r) == "timeout"),
        "memory_caps": count(&|r| clean(r) == "memory-cap"),
        "other_endings": count(&|r| !matches!(clean(r).as_str(), "accept" | "reject" | "decline" | "timeout" | "memory-cap")),
        "clean_accepts_consensus_rejects":
            count(&|r| clean(r) == "accept" && r["consensus"] == "reject"),
        "clean_rejects_consensus_accepts":
            count(&|r| clean(r) == "reject" && r["consensus"] == "accept"),
    })
}

/// Every refusal the gate makes of an artifact's rows and totals.
fn gate(
    rows: &[Value],
    totals: &Value,
    declines: &BTreeMap<String, Reviewed>,
    profile: &str,
) -> Vec<String> {
    let mut failures = Vec::new();
    for key in ["wrong_accept", "clean_accepts_consensus_rejects"] {
        if totals[key] != 0 {
            failures.push(format!("{key} = {} (must be 0)", totals[key]));
        }
    }
    for row in rows {
        let path = row["path"].as_str().unwrap_or_default();
        let clean = row["clean"].as_str().unwrap_or_default();
        let Some(expected) = expected_of(path) else {
            failures.push(format!(
                "{path}: neither a bad/ nor a good/ test of the archive"
            ));
            continue;
        };
        if row["outcome"] != expected {
            failures.push(format!(
                "{path}: the round table's outcome {} disagrees with its archive group \
                 ({expected})",
                row["outcome"]
            ));
        }
        let reviewed = declines.get(path);
        if clean == expected {
            if reviewed.is_some_and(|r| r.pinned) {
                failures.push(format!(
                    "{path}: {clean} as the round expects, but the reviewed table pins a gap \
                     here: the gap closed, delete its row"
                ));
            }
            continue;
        }
        let wrong_accept = expected == "reject" && clean == "accept";
        let allowed = !wrong_accept && reviewed.is_some_and(|r| r.allows(clean, profile));
        if !allowed {
            failures.push(format!(
                "{path}: {clean} (expected {expected}; {}) [{}]",
                if wrong_accept {
                    "WRONG ACCEPT: a kernel soundness defect"
                } else {
                    "not in the reviewed declines table"
                },
                row["stderr_tail"].as_str().unwrap_or_default()
            ));
        }
    }
    failures
}

#[test]
fn test_kernel_arena_round_2026_09_battery() {
    let files = kernel_arena::archive();
    let table = kernel_arena::table();
    assert_eq!(table["archive"]["sha256"], kernel_arena::ARCHIVE_SHA256);
    let declines = declines();
    let rows_in = table["tests"].as_array().expect("table rows");
    assert_eq!(rows_in.len(), kernel_arena::ARCHIVE_FILES);
    let scratch = tempfile::tempdir().expect("scratch dir");
    let factor = u32::try_from(env_number(
        "TIMEOUT_FACTOR",
        if cfg!(debug_assertions) {
            u64::from(DEBUG_TIMEOUT_FACTOR)
        } else {
            1
        },
    ))
    .unwrap_or(DEBUG_TIMEOUT_FACTOR);
    let rss_cap = env_number("RSS_CAP_BYTES", DEFAULT_RSS_CAP_BYTES);
    // `CLEAN_ARENA_ONLY=<prefix>` narrows a run to the tests under one archive
    // directory (a mutation arm's command uses it); an artifact is minted only
    // from a run over every test.
    let only = std::env::var("CLEAN_ARENA_ONLY").unwrap_or_default();
    assert!(
        only.is_empty() || std::env::var_os("CLEAN_ARENA_MINT").is_none(),
        "CLEAN_ARENA_MINT needs a run over every test, not only {only:?}"
    );
    let mut rows = Vec::with_capacity(rows_in.len());
    for row in rows_in {
        let path = row["path"].as_str().expect("row path");
        if !path.starts_with(&only) {
            continue;
        }
        let bytes = files
            .get(path)
            .unwrap_or_else(|| panic!("{path}: in the table, not in the archive"));
        assert_eq!(
            kernel_arena::sha256_hex(bytes),
            row["sha256"],
            "{path}: sha256"
        );
        let file: PathBuf = scratch.path().join(path.replace('/', "__"));
        std::fs::write(&file, bytes).expect("write the test file");
        let limit = row["timeout_s"]
            .as_u64()
            .map_or(DEFAULT_TIMEOUT, |s| Duration::from_secs(s) * factor);
        let run = run_checker(&file, limit, rss_cap);
        eprintln!(
            "arena {path}: {} in {} ms, peak RSS {} MB",
            ending_label(&run.ending),
            run.wall.as_millis(),
            run.max_rss_bytes >> 20
        );
        rows.push(json!({
            "path": path,
            "arena_name": row["arena_name"],
            "outcome": row["outcome"],
            "consensus": row["consensus"],
            "paranoid": row["paranoid"],
            "clean": ending_label(&run.ending),
            "exit_code": match run.ending { Ending::Exit(n) => json!(n), _ => Value::Null },
            "timeout_s": row["timeout_s"],
            "timeout_applied_s": limit.as_secs(),
            "wall_ms": u64::try_from(run.wall.as_millis()).unwrap_or(u64::MAX),
            "max_rss_bytes": run.max_rss_bytes,
            "stderr_tail": run.stderr_tail,
        }));
    }
    // A narrowed run must still run something; a full run must see the whole
    // archive.
    assert!(
        !rows.is_empty(),
        "CLEAN_ARENA_ONLY={only:?} selects no test of the archive"
    );
    let totals = totals(&rows);
    if only.is_empty() {
        assert_eq!(
            (&totals["bad"], &totals["good"]),
            (&json!(ARCHIVE_BAD), &json!(ARCHIVE_GOOD)),
            "the archive's bad and good tests"
        );
    }
    let failures = gate(&rows, &totals, &declines, checker_profile());
    // Only a passing round is minted: a wrong accept is never written into an
    // artifact the recheck leg would then replay as the expected ending.
    match std::env::var_os("CLEAN_ARENA_MINT") {
        Some(out) if failures.is_empty() => {
            mint_artifact(Path::new(&out), &table, factor, rss_cap, &totals, &rows);
        }
        Some(out) => eprintln!(
            "arena: not minting {}: the round failed its gate",
            Path::new(&out).display()
        ),
        None => {}
    }
    assert!(failures.is_empty(), "totals {totals}\n{failures:#?}");
}

/// Write the round artifact (`CLEAN_ARENA_MINT`) for a run over every test.
fn mint_artifact(
    out: &Path,
    table: &Value,
    factor: u32,
    rss_cap: u64,
    totals: &Value,
    rows: &[Value],
) {
    let artifact = json!({
        "schema": "clean.kernel-arena-battery.v1",
        "round": table["round"],
        "doi": table["doi"],
        "arena_commit": table["arena_commit"],
        "archive": table["archive"],
        "results_json_sha256": table["results_json_sha256"],
        "paranoid_kernels": table["paranoid_kernels"],
        "consensus_rule": table["consensus_rule"],
        "checker": "clean_export_check (clean_olean::ndjson, the engine of `clean olean replay --from-export`)",
        "checker_profile": checker_profile(),
        "timeout_factor": factor,
        "rss_cap_bytes": rss_cap,
        "clean_commit": std::env::var("CLEAN_ARENA_COMMIT").unwrap_or_default(),
        "minted": std::env::var("CLEAN_ARENA_DATE").unwrap_or_default(),
        "declines_table": "crates/clean-olean/tests/fixtures/kernel_arena/round-2026-09/declines.json",
        "totals": totals,
        "tests": rows,
    });
    let text = serde_json::to_string_pretty(&artifact).expect("render the artifact");
    std::fs::write(out, text + "\n").expect("write the artifact");
}

/// The newest committed round artifact.
fn committed_artifact() -> (PathBuf, Value) {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../reports/kernel-arena-battery");
    let mut found: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("{}: {e}", dir.display()))
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| {
            p.file_name()
                .and_then(|n| n.to_str())
                .is_some_and(|n| n.starts_with("round-2026-09-") && n.ends_with(".json"))
        })
        .collect();
    found.sort();
    let path = found.pop().expect("a committed round-2026-09 artifact");
    let text = std::fs::read_to_string(&path).expect("read the artifact");
    (
        path,
        serde_json::from_str(&text).expect("the artifact is JSON"),
    )
}

/// The committed artifact agrees with itself, with the vendored round, and
/// with the gate: its totals are what its rows imply, every archived test has
/// exactly one row, and both counts that must be zero are.
#[test]
fn test_kernel_arena_committed_artifact_is_consistent() {
    let (path, artifact) = committed_artifact();
    let table = kernel_arena::table();
    assert_eq!(artifact["archive"], table["archive"], "{}", path.display());
    let rows = artifact["tests"].as_array().expect("artifact rows");
    let mut paths: Vec<&str> = rows.iter().filter_map(|r| r["path"].as_str()).collect();
    paths.sort_unstable();
    paths.dedup();
    let mut expected: Vec<&str> = table["tests"]
        .as_array()
        .expect("table rows")
        .iter()
        .filter_map(|r| r["path"].as_str())
        .collect();
    expected.sort_unstable();
    assert_eq!(
        paths,
        expected,
        "{}: one row per archived test",
        path.display()
    );
    let derived = totals(rows);
    assert_eq!(artifact["totals"], derived, "{}: totals", path.display());
    assert_eq!(
        (&derived["bad"], &derived["good"]),
        (&json!(ARCHIVE_BAD), &json!(ARCHIVE_GOOD)),
        "{}: the archive's bad and good tests",
        path.display()
    );
    // The committed round is a RELEASE round at the arena's own timeouts: its
    // endings are what `green_artifact_recheck.sh` replays with a release
    // `clean`, and no debug-only allowance applies to it.
    assert_eq!(
        (&artifact["checker_profile"], &artifact["timeout_factor"]),
        (&json!("release"), &json!(1)),
        "{}: a committed round is minted by a release checker at timeout factor 1",
        path.display()
    );
    let failures = gate(rows, &artifact["totals"], &declines(), "release");
    assert!(failures.is_empty(), "{}: {failures:#?}", path.display());
}

fn synthetic_row(path: &str, outcome: &str, consensus: &str, clean: &str) -> Value {
    json!({
        "path": path,
        "outcome": outcome,
        "consensus": consensus,
        "clean": clean,
        "stderr_tail": "",
    })
}

/// A row's expected verdict comes from its archive group (`bad/` or `good/`,
/// inside the sha256-pinned archive), never from the unpinned round table: a
/// table row that calls a bad test `accept` is refused, and a bad test that
/// exits 0 under it is still a wrong accept (finding C6).
#[test]
fn test_kernel_arena_gate_takes_the_verdict_from_the_archive_group() {
    let rows = vec![synthetic_row(
        "bad/bugs/proj-of-subst-prop.ndjson",
        "accept",
        "accept",
        "accept",
    )];
    let failures = gate(&rows, &totals(&rows), &BTreeMap::new(), "release");
    assert!(
        failures.iter().any(|f| f.contains("WRONG ACCEPT")),
        "{failures:#?}"
    );
    assert!(
        failures.iter().any(|f| f.contains("archive group")),
        "{failures:#?}"
    );
}

/// The consensus count fails the gate on its own: a good test Clean accepts
/// but the paranoid kernels reject (finding C6's seeded nonzero value).
#[test]
fn test_kernel_arena_gate_refuses_an_accept_the_consensus_rejects() {
    let rows = vec![synthetic_row(
        "good/tutorial/037_boolType.ndjson",
        "accept",
        "reject",
        "accept",
    )];
    let totals = totals(&rows);
    assert_eq!(totals["wrong_accept"], 0);
    assert_eq!(totals["clean_accepts_consensus_rejects"], 1);
    let failures = gate(&rows, &totals, &BTreeMap::new(), "release");
    assert!(
        failures
            .iter()
            .any(|f| f.contains("clean_accepts_consensus_rejects")),
        "{failures:#?}"
    );
}
