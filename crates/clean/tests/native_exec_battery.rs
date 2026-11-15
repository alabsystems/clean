// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! THE NATIVE EXECUTION BATTERY — `clean run` never prints a wrong answer at
//! exit status 0.
//!
//! Every program under `tests/fixtures/native_exec_battery/programs/` is run
//! through the real `clean run` and compared, byte for byte, with what pinned
//! Lean v4.30.0-rc2 printed for it (`expected/`, minted by
//! `scripts/native_exec_battery_expected.py` from `lean --run`). Each program
//! lands in exactly one verdict:
//!
//! * `BYTE_EQUAL` — stdout, stderr and exit status identical to Lean's;
//! * `REFUSED_BUILD` — `clean run` refused to build it with a named error
//!   (`Error: …`, empty stdout, status 1);
//! * `REFUSED_RUNTIME` — it stopped itself with a named fail-closed runtime
//!   error (`clean panic: …`), nonzero, after printing at most a PREFIX of
//!   Lean's stdout;
//! * `WRONG_OUTPUT_EXIT0` — status 0 and different bytes: the class this
//!   battery exists to hold at ZERO;
//! * `WRONG_OUTPUT`, `CRASH` (a signal with no named error), `TIMEOUT`.
//!
//! The battery FAILS when any program is outside the first three, and when any
//! verdict differs from the one committed in `reports/native-exec-battery.json`
//! — that report is the pin set and the `compile-runtime` scorecard row's
//! evidence at once. A verdict that flips is a RESULT: re-pin deliberately with
//! `CLEAN_NATIVE_EXEC_UPDATE=1` and say why in the commit. An ABSENT report is
//! a failure, never a pass (the fail-open path the everyday battery had).
//!
//! The programs are the 2026-09-24 audit's compiler/runtime battery and the
//! critic's reproductions (`reports/lean4-replacement-audit-2026-09-24/`), plus
//! the P0_EXEC probes; see the fixture's README. The driver is the real `clean`
//! binary: a capability does not count without its production caller.

#![cfg(unix)]

use std::collections::BTreeMap;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::Mutex;
use std::time::{Duration, Instant};

const UPDATE_ENV: &str = "CLEAN_NATIVE_EXEC_UPDATE";
const REPORT_SCHEMA: &str = "clean-native-exec-battery-v1";
const TIMEOUT: Duration = Duration::from_secs(600);
const ALLOWED: [&str; 3] = ["BYTE_EQUAL", "REFUSED_BUILD", "REFUSED_RUNTIME"];
const VERDICTS: [&str; 7] = [
    "BYTE_EQUAL",
    "REFUSED_BUILD",
    "REFUSED_RUNTIME",
    "WRONG_OUTPUT_EXIT0",
    "WRONG_OUTPUT",
    "CRASH",
    "TIMEOUT",
];

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn fixture() -> PathBuf {
    repo_root().join("tests/fixtures/native_exec_battery")
}

fn report_path() -> PathBuf {
    repo_root().join("reports/native-exec-battery.json")
}

/// How one program ran: `None` status means it did not finish in time.
struct Ran {
    status: Option<std::process::ExitStatus>,
    stdout: Vec<u8>,
    stderr: Vec<u8>,
}

/// Run `clean run <program> --decl main -- <args>` in a fresh scratch working
/// directory, feeding `stdin`, with a wall-clock timeout.
fn run_program(program: &Path, args: &[String], stdin: &[u8]) -> Ran {
    let cwd = tempfile::tempdir().expect("scratch cwd");
    let mut child = Command::new(env!("CARGO_BIN_EXE_clean"))
        .arg("run")
        .arg(program)
        .args(["--decl", "main", "--"])
        .args(args)
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
        // A program that never reads its stdin closes the pipe first; that is
        // not an error of the battery.
        let _ = pipe.write_all(stdin);
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

/// The verdict, by the rules in the module doc.
fn classify(ran: &Ran, lean_rc: i32, lean_out: &[u8], lean_err: &[u8]) -> &'static str {
    let Some(status) = ran.status else {
        return "TIMEOUT";
    };
    let code = status.code();
    if code == Some(lean_rc) && ran.stdout == lean_out && ran.stderr == lean_err {
        return "BYTE_EQUAL";
    }
    let err = String::from_utf8_lossy(&ran.stderr);
    if code == Some(1) && ran.stdout.is_empty() && err.lines().any(|l| l.starts_with("Error: ")) {
        return "REFUSED_BUILD";
    }
    if code != Some(0) && err.contains("clean panic: ") && lean_out.starts_with(&ran.stdout) {
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

/// The named error a refusal carries — its `(tag)` when it has one, else its
/// first `Error:`/`clean panic:` line — with checkout-specific paths removed so
/// the report does not depend on where the tree lives.
fn refusal_name(stderr: &[u8], programs: &Path) -> String {
    let text = String::from_utf8_lossy(stderr);
    let line = text
        .lines()
        .map(str::trim)
        .find(|l| l.starts_with("Error:") || l.starts_with("clean panic:"))
        .unwrap_or("");
    let trimmed = line.trim_end_matches('.');
    if let Some(open) = trimmed.rfind('(') {
        let tag = &trimmed[open + 1..trimmed.len().saturating_sub(1)];
        if trimmed.ends_with(')')
            && !tag.is_empty()
            && tag.chars().all(|c| c.is_ascii_lowercase() || c == '-')
        {
            return tag.to_string();
        }
    }
    let prefix = programs.display().to_string();
    let line = line.replace(&prefix, "<programs>");
    line.chars().take(160).collect()
}

fn json_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out
}

struct Row {
    name: String,
    verdict: &'static str,
    refusal: String,
    clean_rc: Option<i32>,
    lean_rc: i32,
}

/// The report is written ONE PROGRAM PER LINE so the pins can be read back
/// without a JSON parser (`read_pins`), and the file diffs one verdict per line.
fn render_report(rows: &[Row], lean_version: &str, passed: bool) -> String {
    let count = |v: &str| rows.iter().filter(|r| r.verdict == v).count();
    let counts: Vec<String> = VERDICTS
        .iter()
        .map(|v| format!("\"{v}\": {}", count(v)))
        .collect();
    let mut out = String::from("{\n");
    out.push_str(&format!(" \"schema_version\": \"{REPORT_SCHEMA}\",\n"));
    out.push_str(&format!(
        " \"status\": \"{}\",\n",
        if passed { "passed" } else { "failed" }
    ));
    out.push_str(
        " \"generated_by\": \"CLEAN_NATIVE_EXEC_UPDATE=1 cargo test --locked -p clean --test native_exec_battery\",\n",
    );
    out.push_str(
        " \"claim\": \"every program is byte-identical to pinned Lean or refused with a named error; WRONG_OUTPUT_EXIT0 is 0. This measures fail-closedness, not parity: read BYTE_EQUAL for how much runs.\",\n",
    );
    out.push_str(&format!(" \"lean\": \"{}\",\n", json_escape(lean_version)));
    out.push_str(&format!(" \"counts\": {{{}}},\n", counts.join(", ")));
    out.push_str(&format!(
        " \"wrong_output_exit0\": {},\n",
        count("WRONG_OUTPUT_EXIT0")
    ));
    out.push_str(" \"programs\": [\n");
    for (i, row) in rows.iter().enumerate() {
        let clean_rc = row
            .clean_rc
            .map_or_else(|| "null".to_string(), |c| c.to_string());
        out.push_str(&format!(
            "  {{\"name\": \"{}\", \"verdict\": \"{}\", \"clean_rc\": {}, \"lean_rc\": {}, \"refusal\": \"{}\"}}{}\n",
            json_escape(&row.name),
            row.verdict,
            clean_rc,
            row.lean_rc,
            json_escape(&row.refusal),
            if i + 1 == rows.len() { "" } else { "," }
        ));
    }
    out.push_str(" ]\n}\n");
    out
}

/// Read the pinned verdicts back out of a report written by `render_report`.
fn read_pins(report: &str) -> BTreeMap<String, String> {
    let field = |line: &str, key: &str| -> Option<String> {
        let start = line.find(&format!("\"{key}\": \""))? + key.len() + 5;
        let end = start + line[start..].find('"')?;
        Some(line[start..end].to_string())
    };
    report
        .lines()
        .filter_map(|line| Some((field(line, "name")?, field(line, "verdict")?)))
        .collect()
}

#[test]
fn native_exec_battery_is_byte_identical_or_refused() {
    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
    assert!(
        Command::new(&cc)
            .arg("--version")
            .output()
            .is_ok_and(|o| o.status.success()),
        "a C compiler (`{cc}`) is required: `clean run` links, and a battery that does not \
         run is not a gate"
    );

    let programs_dir = fixture().join("programs");
    let expected_dir = fixture().join("expected");
    let mut names: Vec<String> = std::fs::read_dir(&programs_dir)
        .expect("read programs/")
        .filter_map(|entry| {
            let path = entry.ok()?.path();
            (path.extension()? == "lean").then(|| path.file_stem()?.to_str().map(String::from))?
        })
        .collect();
    names.sort();
    assert!(
        names.len() >= 40,
        "the battery must see its programs, or it gates nothing: found {}",
        names.len()
    );

    // Run every program, a few at a time (each `clean run` elaborates the
    // prelude and links with `cc`).
    let queue = Mutex::new(names.clone());
    let results: Mutex<Vec<Row>> = Mutex::new(Vec::new());
    let threads = std::thread::available_parallelism()
        .map_or(2, |n| n.get())
        .min(6);
    std::thread::scope(|scope| {
        for _ in 0..threads {
            scope.spawn(|| loop {
                let Some(name) = queue.lock().expect("queue").pop() else {
                    break;
                };
                let read = |ext: &str| {
                    std::fs::read(expected_dir.join(format!("{name}.{ext}")))
                        .unwrap_or_else(|e| panic!("expected/{name}.{ext}: {e}"))
                };
                let lean_rc: i32 = String::from_utf8_lossy(&read("rc"))
                    .trim()
                    .parse()
                    .unwrap_or_else(|e| panic!("expected/{name}.rc: {e}"));
                let (lean_out, lean_err) = (read("stdout"), read("stderr"));
                let args: Vec<String> =
                    std::fs::read_to_string(programs_dir.join(format!("{name}.args")))
                        .map(|s| {
                            s.lines()
                                .filter(|l| !l.is_empty())
                                .map(String::from)
                                .collect()
                        })
                        .unwrap_or_default();
                let stdin =
                    std::fs::read(programs_dir.join(format!("{name}.stdin"))).unwrap_or_default();
                let ran = run_program(&programs_dir.join(format!("{name}.lean")), &args, &stdin);
                let verdict = classify(&ran, lean_rc, &lean_out, &lean_err);
                let refusal = if verdict.starts_with("REFUSED") {
                    refusal_name(&ran.stderr, &programs_dir)
                } else {
                    String::new()
                };
                if !ALLOWED.contains(&verdict) {
                    eprintln!(
                        "native-exec-battery: {name} is {verdict}\n  clean status {:?}\n  \
                         clean stdout {:?}\n  lean  stdout {:?}\n  clean stderr {:?}",
                        ran.status,
                        String::from_utf8_lossy(&ran.stdout),
                        String::from_utf8_lossy(&lean_out),
                        String::from_utf8_lossy(&ran.stderr)
                    );
                }
                results.lock().expect("results").push(Row {
                    name,
                    verdict,
                    refusal,
                    clean_rc: ran.status.and_then(|s| s.code()),
                    lean_rc,
                });
            });
        }
    });
    let mut rows = results.into_inner().expect("results");
    rows.sort_by(|a, b| a.name.cmp(&b.name));

    let bad: Vec<String> = rows
        .iter()
        .filter(|r| !ALLOWED.contains(&r.verdict))
        .map(|r| format!("{} is {}", r.name, r.verdict))
        .collect();
    let lean_version = std::fs::read_to_string(expected_dir.join("LEAN_VERSION"))
        .expect("expected/LEAN_VERSION")
        .trim()
        .to_string();

    if std::env::var_os(UPDATE_ENV).is_some() {
        std::fs::write(
            report_path(),
            render_report(&rows, &lean_version, bad.is_empty()),
        )
        .expect("write reports/native-exec-battery.json");
    }
    // The claim itself, independent of any pin: no program may print bytes
    // pinned Lean does not, whatever the committed report says.
    assert!(
        bad.is_empty(),
        "programs neither byte-identical to pinned Lean nor refused with a named error \
         (WRONG_OUTPUT_EXIT0 must be 0):\n  {}",
        bad.join("\n  ")
    );
    if std::env::var_os(UPDATE_ENV).is_none() {
        let committed = std::fs::read_to_string(report_path()).unwrap_or_else(|e| {
            panic!(
                "reports/native-exec-battery.json is absent ({e}); an absent pin set is a \
                 FAILURE, never a pass. Mint it deliberately: {UPDATE_ENV}=1 cargo test \
                 --locked -p clean --test native_exec_battery"
            )
        });
        assert!(
            committed.contains(&format!("\"schema_version\": \"{REPORT_SCHEMA}\"")),
            "reports/native-exec-battery.json is not a {REPORT_SCHEMA} report"
        );
        let pins = read_pins(&committed);
        let live: BTreeMap<String, String> = rows
            .iter()
            .map(|r| (r.name.clone(), r.verdict.to_string()))
            .collect();
        let drift: Vec<String> = live
            .iter()
            .filter(|(name, verdict)| pins.get(*name) != Some(verdict))
            .map(|(name, verdict)| {
                format!(
                    "{name}: live {verdict}, pinned {}",
                    pins.get(name).map_or("<none>", String::as_str)
                )
            })
            .chain(
                pins.keys()
                    .filter(|name| !live.contains_key(*name))
                    .map(|name| format!("{name}: pinned, but no such program")),
            )
            .collect();
        assert!(
            drift.is_empty(),
            "a verdict moved off its pin in reports/native-exec-battery.json -- a flip is a \
             RESULT: re-pin deliberately with {UPDATE_ENV}=1 and say why in the commit:\n  {}",
            drift.join("\n  ")
        );
    }
}
