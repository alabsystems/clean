// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! LX0(a) — WHAT BLOCKS LEAN PROGRAMS ON THE ONE-BACKEND PATH, measured
//! (`designs/2026-09-30-clean-trust-unified-vision.md` §5, M0/LX0).
//!
//! Every program of the native execution battery
//! (`tests/fixtures/native_exec_battery/`) is run twice through the real
//! `clean` binary, and compared byte for byte with what pinned Lean printed:
//!
//! * the C lane, `clean run` — the comparison column;
//! * the trust-cg lane, `clean run --backend trust-cg --receipt <file>`: the
//!   same core, its trust-ir module licensed `clean-compiler-unvalidated`,
//!   compiled by the external trust-cg, linked with the C runtime, the prelude
//!   shims and the core's entry driver (runtime R0).
//!
//! The SCOPE is `p01_hello` and every program the committed C-lane report
//! (`reports/native-exec-battery.json`) pins `BYTE_EQUAL`; the other programs
//! are measured too and summarized apart. Each trust-cg row lands in exactly
//! one outcome class, with its first blocking cause verbatim:
//! `EMIT_TRUSTIR_REFUSED` (the core refused, at a named step),
//! `TRUSTCG_REFUSED`, `LINK_FAILED`, `RUN_CRASH` (killed by a signal),
//! `WRONG_OUTPUT` (with whether it exited 0), `BYTE_EQUAL`; `TIMEOUT` and
//! `NO_RECEIPT` (clean ended without writing the receipt) exist so nothing is
//! ever folded into another class.
//!
//! THIS IS A MEASUREMENT, NOT A PARITY GATE. It fails when trust-cg is not
//! explicitly selected (`CLEAN_TRUST_CG_BIN`, never a silent `PATH` fallback
//! to a consumer older than the wire Clean writes), when it sees no programs,
//! when a built program's receipt does not name the lane, and when a row's
//! class moves off the committed report
//! (`reports/lx0-trustcg-native-battery-2026-09-30.json`). Re-mint the
//! report deliberately with `CLEAN_LX0_UPDATE=1`, which also writes the `.md`
//! beside it, and records what the lane does with `p01_hello` when the
//! consumer is instead the `trust-cg` a bare `PATH` lookup finds
//! (`path_consumer_probe`; a property of the box, never compared against the
//! pins). Claim: measurement only; no binary claim; lane =
//! clean-compiler-unvalidated.

#![cfg(unix)]

#[path = "native_exec_battery_trustcg/report.rs"]
mod report;
#[path = "native_exec_battery_trustcg/report_md.rs"]
mod report_md;

use std::collections::BTreeMap;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::Mutex;
use std::time::{Duration, Instant};

use report::{json_string_field, json_usize_field, ConsumerProbe, Identity, Row, TrustCgRun};

const UPDATE_ENV: &str = "CLEAN_LX0_UPDATE";
const TIMEOUT: Duration = Duration::from_secs(600);
const REPORT: &str = "reports/lx0-trustcg-native-battery-2026-09-30.json";
const C_REPORT: &str = "reports/native-exec-battery.json";

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn fixture() -> PathBuf {
    repo_root().join("tests/fixtures/native_exec_battery")
}

/// How one `clean run` ended: `None` status means it did not finish in time.
struct Ran {
    status: Option<std::process::ExitStatus>,
    stdout: Vec<u8>,
    stderr: Vec<u8>,
}

/// One program's inputs and Lean's pinned answer.
struct Program {
    name: String,
    source: PathBuf,
    args: Vec<String>,
    stdin: Vec<u8>,
    lean_rc: i32,
    lean_out: Vec<u8>,
    lean_err: Vec<u8>,
}

/// Run `clean run <program> --decl main <extra> -- <args>` in a fresh scratch
/// working directory, feeding `stdin`, with a wall-clock timeout. `trust_cg`
/// overrides the inherited `CLEAN_TRUST_CG_BIN` for this one run.
fn run_clean(program: &Program, extra: &[&str], trust_cg: Option<&Path>) -> Ran {
    let cwd = tempfile::tempdir().expect("scratch cwd");
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_clean"));
    if let Some(trust_cg) = trust_cg {
        cmd.env("CLEAN_TRUST_CG_BIN", trust_cg);
    }
    let mut child = cmd
        .arg("run")
        .arg(&program.source)
        .args(["--decl", "main"])
        .args(extra)
        .arg("--")
        .args(&program.args)
        .current_dir(cwd.path())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn clean run");
    let mut out_pipe = child.stdout.take().expect("stdout pipe");
    let mut err_pipe = child.stderr.take().expect("stderr pipe");
    let out_reader = std::thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = out_pipe.read_to_end(&mut buf);
        buf
    });
    let err_reader = std::thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = err_pipe.read_to_end(&mut buf);
        buf
    });
    if let Some(mut pipe) = child.stdin.take() {
        // A program that never reads stdin closes the pipe first.
        let _ = pipe.write_all(&program.stdin);
    }
    let started = Instant::now();
    let status = loop {
        match child.try_wait().expect("poll clean run") {
            Some(status) => break Some(status),
            None if started.elapsed() > TIMEOUT => {
                let _ = child.kill();
                let _ = child.wait();
                break None;
            }
            None => std::thread::sleep(Duration::from_millis(20)),
        }
    };
    Ran {
        status,
        stdout: out_reader.join().expect("stdout reader"),
        stderr: err_reader.join().expect("stderr reader"),
    }
}

/// The C lane's verdict, by `native_exec_battery.rs`'s own rules.
fn classify_c(ran: &Ran, p: &Program) -> &'static str {
    let Some(status) = ran.status else {
        return "TIMEOUT";
    };
    let code = status.code();
    if code == Some(p.lean_rc) && ran.stdout == p.lean_out && ran.stderr == p.lean_err {
        return "BYTE_EQUAL";
    }
    let err = String::from_utf8_lossy(&ran.stderr);
    if code == Some(1) && ran.stdout.is_empty() && err.lines().any(|l| l.starts_with("Error: ")) {
        return "REFUSED_BUILD";
    }
    if code != Some(0) && err.contains("clean panic: ") && p.lean_out.starts_with(&ran.stdout) {
        return "REFUSED_RUNTIME";
    }
    if code == Some(0) {
        return "WRONG_OUTPUT_EXIT0";
    }
    if err.contains("clean run: program terminated by signal") {
        return "CRASH";
    }
    "WRONG_OUTPUT"
}

fn escape_bytes(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes)
        .escape_debug()
        .take(60)
        .collect()
}

/// Where two byte strings first differ, for a WRONG_OUTPUT row.
fn first_diff(stream: &str, got: &[u8], want: &[u8]) -> Option<String> {
    if got == want {
        return None;
    }
    let at = got
        .iter()
        .zip(want)
        .position(|(a, b)| a != b)
        .unwrap_or(got.len().min(want.len()));
    Some(format!(
        "{stream} differs at byte {at}: got \"{}\", Lean \"{}\"",
        escape_bytes(&got[at..]),
        escape_bytes(&want[at..])
    ))
}

/// The trust-cg lane's outcome, from its receipt and, once built, the run.
fn classify_trustcg(ran: &Ran, receipt: Option<&str>, p: &Program) -> TrustCgRun {
    let mut run = TrustCgRun::default();
    let Some(receipt) = receipt else {
        run.outcome = if ran.status.is_none() {
            "TIMEOUT"
        } else {
            "NO_RECEIPT"
        };
        run.cause = report::stderr_line(&ran.stderr);
        return run;
    };
    for label in [
        "\"lowered\": \"clean-compiler-unvalidated\"",
        "\"runtime\": \"C via cc\"",
    ] {
        assert!(
            receipt.contains(label),
            "{}: the receipt does not carry {label}:\n{receipt}",
            p.name
        );
    }
    run.step = json_string_field(receipt, "step").unwrap_or_default();
    run.cause = json_string_field(receipt, "cause").unwrap_or_default();
    run.module_digest = json_string_field(receipt, "module_digest").unwrap_or_default();
    run.kernel_tv_certified = json_usize_field(receipt, "kernel_tv_certified");
    run.bodies_unvalidated = json_usize_field(receipt, "bodies_unvalidated");
    run.driver_entry = json_string_field(receipt, "driver_entry").unwrap_or_default();
    run.outcome = match json_string_field(receipt, "stage").as_deref() {
        Some("core") => "EMIT_TRUSTIR_REFUSED",
        Some("trust-cg") => "TRUSTCG_REFUSED",
        Some("link") => "LINK_FAILED",
        Some("built") => "BUILT",
        other => panic!("{}: unknown receipt stage {other:?}:\n{receipt}", p.name),
    };
    if run.outcome != "BUILT" {
        return run;
    }
    run.rc = ran.status.and_then(|s| s.code());
    let Some(status) = ran.status else {
        run.outcome = "TIMEOUT";
        return run;
    };
    let err = String::from_utf8_lossy(&ran.stderr);
    if status.code() == Some(p.lean_rc) && ran.stdout == p.lean_out && ran.stderr == p.lean_err {
        run.outcome = "BYTE_EQUAL";
    } else if status.code() != Some(0)
        && err.contains("clean panic: ")
        && p.lean_out.starts_with(&ran.stdout)
    {
        // The runtime stopped itself with a named fail-closed error after
        // printing at most a prefix of Lean's output: the C battery's
        // REFUSED_RUNTIME, by the same rule (native_exec_battery.rs).
        run.outcome = "REFUSED_RUNTIME";
        run.cause = err
            .lines()
            .filter(|l| l.contains("clean panic"))
            .collect::<Vec<_>>()
            .join(" | ");
    } else if err.contains("clean run: program terminated by signal") {
        run.outcome = "RUN_CRASH";
        run.cause = err
            .lines()
            .filter(|l| l.contains("terminated by signal") || l.contains("clean panic"))
            .collect::<Vec<_>>()
            .join(" | ");
    } else {
        run.outcome = "WRONG_OUTPUT";
        run.exit_zero = Some(status.code() == Some(0));
        let diffs: Vec<String> = [
            first_diff("stdout", &ran.stdout, &p.lean_out),
            first_diff("stderr", &ran.stderr, &p.lean_err),
            (status.code() != Some(p.lean_rc))
                .then(|| format!("exit {:?}, Lean {}", status.code(), p.lean_rc)),
        ]
        .into_iter()
        .flatten()
        .collect();
        run.cause = diffs.join("; ");
    }
    run
}

fn load_programs() -> Vec<Program> {
    let programs_dir = fixture().join("programs");
    let expected = fixture().join("expected");
    let mut names: Vec<String> = std::fs::read_dir(&programs_dir)
        .expect("read programs/")
        .filter_map(|entry| {
            let path = entry.ok()?.path();
            (path.extension()? == "lean").then(|| path.file_stem()?.to_str().map(String::from))?
        })
        .collect();
    names.sort();
    names
        .into_iter()
        .map(|name| {
            let read = |ext: &str| {
                std::fs::read(expected.join(format!("{name}.{ext}")))
                    .unwrap_or_else(|e| panic!("expected/{name}.{ext}: {e}"))
            };
            let lean_rc = String::from_utf8_lossy(&read("rc"))
                .trim()
                .parse()
                .unwrap_or_else(|e| panic!("expected/{name}.rc: {e}"));
            Program {
                args: std::fs::read_to_string(programs_dir.join(format!("{name}.args")))
                    .map(|s| {
                        s.lines()
                            .filter(|l| !l.is_empty())
                            .map(String::from)
                            .collect()
                    })
                    .unwrap_or_default(),
                stdin: std::fs::read(programs_dir.join(format!("{name}.stdin")))
                    .unwrap_or_default(),
                source: programs_dir.join(format!("{name}.lean")),
                lean_rc,
                lean_out: read("stdout"),
                lean_err: read("stderr"),
                name,
            }
        })
        .collect()
}

/// `p` through the trust-cg lane (with `trust_cg` in place of the selected
/// consumer when given), classified.
fn run_trustcg_lane(p: &Program, trust_cg: Option<&Path>) -> TrustCgRun {
    let receipt_dir = tempfile::tempdir().expect("receipt dir");
    let receipt_path = receipt_dir.path().join("receipt.json");
    let receipt_arg = receipt_path.to_str().expect("utf-8 receipt path");
    let ran = run_clean(
        p,
        &["--backend", "trust-cg", "--receipt", receipt_arg],
        trust_cg,
    );
    let receipt = std::fs::read_to_string(&receipt_path).ok();
    let programs = fixture().join("programs").display().to_string();
    let mut trustcg = classify_trustcg(&ran, receipt.as_deref(), p);
    trustcg.cause = trustcg.cause.replace(&programs, "<programs>");
    trustcg
}

/// The `trust-cg` a bare `PATH` lookup finds, when it is not the selected one
/// (on an aterm box: the packaged consumer a user gets by default).
fn path_trust_cg(selected: &Path) -> Option<PathBuf> {
    let found = std::env::split_paths(&std::env::var_os("PATH")?)
        .map(|dir| dir.join("trust-cg"))
        .find(|candidate| candidate.is_file())?;
    let canon = |p: &Path| std::fs::canonicalize(p).unwrap_or_else(|_| p.to_path_buf());
    (canon(&found) != canon(selected)).then_some(found)
}

/// `p01_hello` through the lane with the `PATH` consumer instead of the
/// selected one: what the one-backend path does with the trust-cg a user has.
fn probe_path_consumer(selected: &Path, programs: &[Program]) -> Option<ConsumerProbe> {
    let path = path_trust_cg(selected)?;
    let hello = programs.iter().find(|p| p.name == "p01_hello")?;
    Some(ConsumerProbe {
        version: report::tool_version(&path),
        path: path.display().to_string(),
        program: hello.name.clone(),
        run: run_trustcg_lane(hello, Some(&path)),
    })
}

fn measure(p: &Program) -> Row {
    let c_ran = run_clean(p, &[], None);
    let c_lane = classify_c(&c_ran, p);
    let trustcg = run_trustcg_lane(p, None);
    Row {
        name: p.name.clone(),
        in_scope: false,
        c_lane,
        c_lane_pinned: String::new(),
        lean_rc: p.lean_rc,
        trustcg,
    }
}

#[test]
fn lx0_trustcg_native_battery_measurement() {
    let selected = std::env::var_os("CLEAN_TRUST_CG_BIN").unwrap_or_else(|| {
        panic!(
            "CLEAN_TRUST_CG_BIN is not set: this measurement names its trust-cg explicitly \
             (the PATH one may predate the trust-ir wire Clean writes); point it at a trust-cg \
             that accepts --recognize-authority"
        )
    });
    let identity = Identity::measure(Path::new(&selected), &repo_root());
    let c_pins = report::read_pins(
        &std::fs::read_to_string(repo_root().join(C_REPORT)).expect("the committed C-lane report"),
        "verdict",
    );
    let programs = load_programs();
    assert!(
        programs.len() >= 40,
        "the battery must see its programs: {}",
        programs.len()
    );
    let in_scope = |name: &str| {
        name == "p01_hello" || c_pins.get(name).map(String::as_str) == Some("BYTE_EQUAL")
    };
    let scoped = programs.iter().filter(|p| in_scope(&p.name)).count();
    assert!(
        scoped > 0,
        "no program is in scope: the C-lane pins were not read"
    );

    let queue = Mutex::new(programs.iter().collect::<Vec<_>>());
    let rows: Mutex<Vec<Row>> = Mutex::new(Vec::new());
    let threads = std::thread::available_parallelism()
        .map_or(2, |n| n.get())
        .min(4);
    std::thread::scope(|scope| {
        for _ in 0..threads {
            scope.spawn(|| loop {
                let Some(p) = queue.lock().expect("queue").pop() else {
                    break;
                };
                let mut row = measure(p);
                row.in_scope = in_scope(&p.name);
                row.c_lane_pinned = c_pins.get(&p.name).cloned().unwrap_or_default();
                eprintln!(
                    "lx0: {:<28} c={:<18} trust-cg={} {}",
                    row.name, row.c_lane, row.trustcg.outcome, row.trustcg.cause
                );
                rows.lock().expect("rows").push(row);
            });
        }
    });
    let mut rows = rows.into_inner().expect("rows");
    rows.sort_by(|a, b| a.name.cmp(&b.name));
    assert_eq!(rows.iter().filter(|r| r.in_scope).count(), scoped);

    let report_path = repo_root().join(REPORT);
    if std::env::var_os(UPDATE_ENV).is_some() {
        // Minting only: the PATH consumer is a property of the box, so it is
        // recorded beside the pins and never compared against them.
        let probe = probe_path_consumer(Path::new(&selected), &programs);
        if let Some(probe) = &probe {
            eprintln!(
                "lx0: PATH consumer {} ({}) on {}: {} {}",
                probe.path, probe.version, probe.program, probe.run.outcome, probe.run.cause
            );
        }
        let json = report::render_json(&rows, &identity, probe.as_ref());
        std::fs::write(&report_path, json).expect("write the LX0 report");
        std::fs::write(
            report_path.with_extension("md"),
            report_md::render_md(&rows, &identity, probe.as_ref()),
        )
        .expect("write the LX0 summary");
    }
    // The lane's claim, independent of any pin (the C battery's invariant): no
    // program prints bytes pinned Lean does not and exits 0.
    let wrong_exit0: Vec<&str> = rows
        .iter()
        .filter(|r| r.trustcg.outcome == "WRONG_OUTPUT" && r.trustcg.exit_zero == Some(true))
        .map(|r| r.name.as_str())
        .collect();
    assert!(
        wrong_exit0.is_empty(),
        "programs that printed bytes pinned Lean does not and exited 0 through the trust-cg \
         lane (WRONG_OUTPUT_EXIT0 must be 0):\n  {}",
        wrong_exit0.join("\n  ")
    );
    // The pins, read back from the file on disk: a mint run checks the report it
    // just wrote, so no mode skips the comparison.
    let committed = std::fs::read_to_string(&report_path).unwrap_or_else(|e| {
        panic!(
            "{REPORT} is absent ({e}); an absent pin set is a FAILURE. Mint it deliberately: \
             {UPDATE_ENV}=1 CLEAN_TRUST_CG_BIN=<trust-cg> cargo test --locked -p clean \
             --features trust-ir-backend --test native_exec_battery_trustcg"
        )
    });
    let pins = report::read_pins(&committed, "outcome");
    let live: BTreeMap<String, String> = rows
        .iter()
        .map(|r| (r.name.clone(), r.trustcg.outcome.to_owned()))
        .collect();
    let drift: Vec<String> = live
        .iter()
        .filter(|(name, outcome)| pins.get(*name) != Some(outcome))
        .map(|(name, outcome)| {
            format!(
                "{name}: live {outcome}, pinned {}",
                pins.get(name).map_or("<none>", String::as_str)
            )
        })
        .collect();
    assert!(
        drift.is_empty(),
        "an LX0 outcome moved off {REPORT} (trust-cg {}): a move is a RESULT; re-mint \
         deliberately with {UPDATE_ENV}=1 and say why in the commit:\n  {}",
        identity.trust_cg_version,
        drift.join("\n  ")
    );
}
