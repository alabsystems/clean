// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A LEAN-DEFINED ADVICE-REPLAYING CHECKER, COMPILED AND RUN BY CLEAN — unit
//! X1 (and the measuring half of X3) of
//! `docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md`.
//!
//! The plan's `kcheck` is a Lean definition that replays untrusted advice, and
//! the owner's directive (§2.1) is that it reaches bytes through Clean's
//! lowering in fact. This file measures how far that is true today on a small
//! real instance of the same shape,
//! `tests/fixtures/advice_replay_checker/programs/advice_replay.lean`: a de
//! Bruijn term type, an advice type (reduction steps naming a path and a
//! rule), a fuel-bounded replay in `Except`, and a `main` that prints one
//! verdict line per embedded case — nine honest cases and eight corrupted
//! ones that must be REFUSED.
//!
//! What is asserted, always on EXACT BYTES (never "it built and exited 0"; see
//! `tostring_instances_cli.rs` for the bug that rule was bought with):
//!
//! * the checker's stdout through the real `clean run` is the text pinned
//!   Lean v4.30.0-rc2 printed for the same file
//!   (`expected/advice_replay.stdout`, minted by
//!   `scripts/native_exec_battery_expected.py --fixture …`), and that text is
//!   spelled out below so a reader sees the verdicts;
//! * NEGATIVE CONTROL: the same checker with its structural comparison removed
//!   (`advice_replay_no_compare.lean`, which this file re-derives from the
//!   checker so the two cannot drift) prints Lean's bytes for THAT program,
//!   which accept three of the corrupted cases — so the assertion above
//!   follows the checker's logic and would catch a wrong acceptance;
//! * every construct probe (`c*.lean`, one construct `kcheck` needs per file;
//!   `r4_items` names the current R4 probes; c24/c32/c33 are retained acyclic
//!   controls, superseded by real cycles c34/c35/c36) and both lanes
//!   land on the outcome pinned in `data/kcheck_execution_gaps.json`. A
//!   refusal is pinned BY NAME (the refusing text must appear), so the day a
//!   gap closes its row fails here and the list must be burned down
//!   deliberately. A program that exits 0 with other bytes fails whatever the
//!   pins say; one that dies on a signal is pinned as `CRASHED` only when what
//!   it printed is a prefix of Lean's bytes.
//!
//! The trust-ir / trust-cg lane (`clean run --backend trust-cg`, the
//! `trust-ir-backend` feature) is measured by the last test, against the same
//! file. It is a measurement: every body on that lane is stamped
//! `clean-compiler-unvalidated`, the runtime is C linked by the host `cc`, and
//! nothing here claims the plan's §2.1 items hold.
//!
//! The elaborator's verdict apart from any backend (`clean check`) is held in
//! the `elaborator` submodule: the ten R4 items of the design's recursion
//! pattern, and the programs pinned Lean rejects (the negative controls).

#![cfg(unix)]

use std::collections::BTreeSet;
use std::ffi::OsStr;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Stdio};
use std::time::{Duration, Instant};

use serde_json::Value;

#[path = "advice_replay_checker/elaborator.rs"]
mod elaborator;

const FIXTURE: &str = "tests/fixtures/advice_replay_checker";
const GAPS: &str = "data/kcheck_execution_gaps.json";
const SCHEMA: &str = "clean-kcheck-execution-gaps-v1";
const TIMEOUT: Duration = Duration::from_secs(600);

/// The checker and its mutant; every other program is a construct probe.
const CHECKER: &str = "advice_replay";
const MUTANT: &str = "advice_replay_no_compare";

/// What pinned Lean prints for the checker, and what `clean run` must print.
const VERDICTS: &str = "\
beta-root: ACCEPT steps=1 nf=5
add-small: ACCEPT steps=1 nf=5
add-bignat: ACCEPT steps=2 nf=36893488147419103239
succ-bignat: ACCEPT steps=1 nf=18446744073709551616
twice-succ: ACCEPT steps=6 nf=42
under-binder: ACCEPT steps=1 nf=(fun (#0 #0))
capture-shift: ACCEPT steps=1 nf=(fun (fun #1))
open-stuck: ACCEPT steps=1 nf=(#3 2)
empty-advice: ACCEPT steps=0 nf=9
corrupt-wrong-rule: REFUSE step 0: beta does not apply
corrupt-bad-path: REFUSE step 0 leaves the term
corrupt-swapped-steps: REFUSE step 0: beta does not apply
corrupt-truncated: REFUSE replayed term is not the claim
corrupt-claim-off-by-one: REFUSE replayed term is not the claim
corrupt-claim-not-normal: REFUSE claim is not a normal form
corrupt-fuel-short: REFUSE out of fuel at step 3
corrupt-capture: REFUSE replayed term is not the claim
";

/// The comparison the mutant drops, exactly as the checker spells it.
const COMPARISON: &str = "  if !(Tm.beq reached claim) then\n    throw .mismatch\n";

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn fixture() -> PathBuf {
    repo_root().join(FIXTURE)
}

fn program(name: &str) -> PathBuf {
    fixture().join("programs").join(format!("{name}.lean"))
}

/// What pinned Lean printed on stdout for `name`. Every program of this
/// fixture exits 0 with an empty stderr under Lean; `the_fixture_is_whole`
/// holds the committed bytes to that.
fn lean_stdout(name: &str) -> Vec<u8> {
    let path = fixture().join("expected").join(format!("{name}.stdout"));
    std::fs::read(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

fn program_names() -> Vec<String> {
    let dir = fixture().join("programs");
    let mut names: Vec<String> = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("{}: {e}", dir.display()))
        .filter_map(|entry| {
            let path = entry.ok()?.path();
            (path.extension()? == "lean").then(|| path.file_stem()?.to_str().map(String::from))?
        })
        .collect();
    names.sort();
    names
}

/// Require a C compiler, fail-closed: both lanes link with the host `cc`, and
/// a silent skip would retire the byte assertions (see `tostring_instances_cli.rs`).
fn require_cc(test: &str) {
    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
    let found = Command::new(&cc)
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false);
    assert!(
        found,
        "{test}: a C compiler is required by this byte-exact suite and `{cc}` did not run"
    );
}

/// How one `clean run` ended: `None` status means it did not finish in time.
struct Ran {
    status: Option<ExitStatus>,
    stdout: Vec<u8>,
    stderr: Vec<u8>,
}

/// `clean run <source> --decl main <extra>` in a fresh scratch directory.
fn clean_run(source: &Path, extra: &[&str]) -> Ran {
    let mut args = vec![
        OsStr::new("run"),
        source.as_os_str(),
        OsStr::new("--decl"),
        OsStr::new("main"),
    ];
    args.extend(extra.iter().map(|arg| OsStr::new(*arg)));
    clean_cmd(&args)
}

/// `clean <args>` in a fresh scratch directory, killed after [`TIMEOUT`].
fn clean_cmd(args: &[&OsStr]) -> Ran {
    let cwd = tempfile::tempdir().expect("scratch cwd");
    let mut child = Command::new(env!("CARGO_BIN_EXE_clean"))
        .args(args)
        .current_dir(cwd.path())
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn clean");
    let mut out_pipe = child.stdout.take().expect("stdout pipe");
    let mut err_pipe = child.stderr.take().expect("stderr pipe");
    let out_reader = std::thread::spawn(move || {
        let mut buf = Vec::new();
        out_pipe.read_to_end(&mut buf).map(|_| buf)
    });
    let err_reader = std::thread::spawn(move || {
        let mut buf = Vec::new();
        err_pipe.read_to_end(&mut buf).map(|_| buf)
    });
    let started = Instant::now();
    let status = loop {
        match child.try_wait().expect("poll clean") {
            Some(status) => break Some(status),
            None if started.elapsed() > TIMEOUT => {
                child.kill().expect("kill a timed-out clean");
                child.wait().expect("reap a timed-out clean");
                break None;
            }
            None => std::thread::sleep(Duration::from_millis(20)),
        }
    };
    Ran {
        status,
        stdout: out_reader
            .join()
            .expect("stdout reader")
            .expect("read stdout"),
        stderr: err_reader
            .join()
            .expect("stderr reader")
            .expect("read stderr"),
    }
}

fn text(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).into_owned()
}

/// One lane's result for one program: the outcome class and the text that
/// names a refusal (empty for `BYTE_EQUAL`, and for the elaborator's
/// `ACCEPTED`).
#[derive(Debug, PartialEq, Eq)]
struct Outcome {
    class: &'static str,
    refusal: String,
}

/// The C lane's outcome, by the native execution battery's rules
/// (`native_exec_battery.rs`). Anything outside its three allowed classes is
/// a failure of this suite, whatever the pins say.
fn classify_c(name: &str, ran: &Ran, lean_out: &[u8]) -> Outcome {
    let status = ran
        .status
        .unwrap_or_else(|| panic!("{name}: `clean run` did not finish in {TIMEOUT:?}"));
    let err = text(&ran.stderr);
    if status.code() == Some(0) && ran.stdout == lean_out && ran.stderr.is_empty() {
        return Outcome {
            class: "BYTE_EQUAL",
            refusal: String::new(),
        };
    }
    if status.code() == Some(1) && ran.stdout.is_empty() {
        if let Some(line) = err.lines().find(|l| l.starts_with("Error: ")) {
            return Outcome {
                class: "REFUSED_BUILD",
                refusal: line.to_string(),
            };
        }
    }
    if status.code() != Some(0) && lean_out.starts_with(&ran.stdout) {
        if let Some(outcome) = stopped_after_a_prefix(&err) {
            return outcome;
        }
    }
    panic!(
        "{name}: `clean run` neither printed pinned Lean's bytes nor refused by name \
         (status {status:?}).\n--- stdout\n{}\n--- Lean\n{}\n--- stderr\n{err}",
        text(&ran.stdout),
        text(lean_out)
    );
}

/// A built program that stopped after printing a prefix of Lean's bytes: the
/// runtime stopped itself by name (`REFUSED_RUNTIME`), or the process died on
/// a signal (`CRASHED`, pinned by the line `clean run` prints for it). A crash
/// is not a refusal; it is pinned so that the gap behind it is listed, and so
/// that the day it stops crashing the row fails.
fn stopped_after_a_prefix(err: &str) -> Option<Outcome> {
    if let Some(line) = err.lines().find(|l| l.contains("clean panic: ")) {
        return Some(Outcome {
            class: "REFUSED_RUNTIME",
            refusal: line.to_string(),
        });
    }
    err.lines()
        .find(|l| l.starts_with("clean run: program terminated by signal "))
        .map(|line| Outcome {
            class: "CRASHED",
            refusal: line.to_string(),
        })
}

fn gaps() -> Value {
    let path = repo_root().join(GAPS);
    let raw = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "{}: {e}. The gap list is this suite's pin set; an absent one is a failure",
            path.display()
        )
    });
    let value: Value =
        serde_json::from_str(&raw).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    assert_eq!(value["schema_version"], SCHEMA, "{GAPS}: schema");
    value
}

fn str_field<'v>(row: &'v Value, field: &str, what: &str) -> &'v str {
    row[field]
        .as_str()
        .unwrap_or_else(|| panic!("{GAPS}: {what} has no string `{field}`: {row}"))
}

fn rows<'v>(value: &'v Value, field: &str) -> &'v [Value] {
    value[field]
        .as_array()
        .unwrap_or_else(|| panic!("{GAPS}: `{field}` is not an array"))
}

fn pinned_row<'v>(pins: &'v Value, name: &str) -> &'v Value {
    rows(pins, "programs")
        .iter()
        .find(|row| row["name"] == name)
        .unwrap_or_else(|| {
            panic!(
                "{GAPS}: no `programs` row for `{name}`. Every program under {FIXTURE}/programs \
                 is pinned on both lanes; add its row"
            )
        })
}

/// Compare one lane's live outcome with its pin. A refusal is pinned by the
/// text that names it, which the live refusal must CONTAIN (the full line
/// carries scratch paths).
fn check_pin(name: &str, lane: &str, live: &Outcome, pin: &Value, failures: &mut Vec<String>) {
    let class = str_field(pin, "outcome", name);
    if class != live.class {
        failures.push(format!(
            "{name} [{lane}]: live {} ({}), pinned {class}",
            live.class, live.refusal
        ));
        return;
    }
    let needle = pin["refusal"].as_str().unwrap_or_default();
    if live.class == "BYTE_EQUAL" || live.class == "ACCEPTED" {
        if !needle.is_empty() {
            failures.push(format!(
                "{name} [{lane}]: pinned {class} with a refusal text"
            ));
        }
    } else if needle.is_empty() {
        failures.push(format!(
            "{name} [{lane}]: a refusal is pinned by name; `refusal` is empty. Live: {}",
            live.refusal
        ));
    } else if !live.refusal.contains(needle) {
        failures.push(format!(
            "{name} [{lane}]: refused, but not by the pinned name.\n    live:   {}\n    pinned: {needle}",
            live.refusal
        ));
    }
}

fn report(lane: &str, failures: &[String]) {
    assert!(
        failures.is_empty(),
        "{lane}: an outcome moved off {GAPS}. A move is a RESULT. A refusal that closed means a \
         gap closed: re-pin its row and retire the gap it cites; a new refusal is a new gap and \
         needs its row there, with the refusing source site:\n  {}",
        failures.join("\n  ")
    );
}

/// The committed bytes are what this suite believes Lean printed, so their
/// shape is checked before anything is compared with them.
#[test]
fn the_fixture_is_whole() {
    let names = program_names();
    assert!(
        names.len() >= 20,
        "the suite must see its programs: {names:?}"
    );
    for name in &names {
        let expected = fixture().join("expected");
        let read = |ext: &str| {
            std::fs::read(expected.join(format!("{name}.{ext}")))
                .unwrap_or_else(|e| panic!("expected/{name}.{ext}: {e}"))
        };
        assert_eq!(text(&read("rc")).trim(), "0", "{name}: Lean's exit status");
        assert!(read("stderr").is_empty(), "{name}: Lean's stderr");
        assert!(!read("stdout").is_empty(), "{name}: Lean's stdout");
    }
    assert_eq!(
        text(&lean_stdout(CHECKER)),
        VERDICTS,
        "the verdicts spelled in this file are not the bytes minted from pinned Lean"
    );
    let (accepted, refused): (Vec<&str>, Vec<&str>) =
        VERDICTS.lines().partition(|l| l.contains(": ACCEPT "));
    assert_eq!(accepted.len(), 9, "honest cases");
    assert_eq!(refused.len(), 8, "corrupted cases");
    for line in VERDICTS.lines() {
        assert_eq!(
            line.starts_with("corrupt-"),
            line.contains(": REFUSE "),
            "a corrupted case is refused and an honest one accepted: {line}"
        );
    }
    // The mutant is the checker minus its comparison, and nothing else.
    let checker = std::fs::read_to_string(program(CHECKER)).expect("the checker");
    assert_eq!(
        checker.matches(COMPARISON).count(),
        1,
        "the checker spells its structural comparison once"
    );
    assert_eq!(
        std::fs::read_to_string(program(MUTANT)).expect("the mutant"),
        checker.replace(COMPARISON, ""),
        "{MUTANT}.lean must be {CHECKER}.lean with the comparison removed"
    );
}

/// THE UNIT'S ACCEPTANCE: the Lean-defined checker, elaborated by Clean,
/// lowered by clean-compiler, emitted as C and run, prints pinned Lean's
/// verdicts byte for byte.
#[test]
fn clean_run_prints_the_checkers_verdicts_byte_for_byte() {
    require_cc("clean_run_prints_the_checkers_verdicts_byte_for_byte");
    let ran = clean_run(&program(CHECKER), &[]);
    assert_eq!(
        ran.status.and_then(|s| s.code()),
        Some(0),
        "`clean run` of the checker failed.\nstdout={}\nstderr={}",
        text(&ran.stdout),
        text(&ran.stderr)
    );
    assert_eq!(
        text(&ran.stdout),
        VERDICTS,
        "`clean run` printed other verdicts than pinned Lean; stderr={}",
        text(&ran.stderr)
    );
    assert!(
        ran.stderr.is_empty(),
        "stderr must be empty: {}",
        text(&ran.stderr)
    );
}

/// NEGATIVE CONTROL for the acceptance above. A checker that skips the
/// structural comparison accepts three corrupted cases; `clean run` must print
/// exactly that (Lean's bytes for the mutant), which the acceptance assertion
/// refuses for the stated reason: a corrupted case reads ACCEPT.
#[test]
fn a_checker_without_its_comparison_is_caught_by_the_same_bytes() {
    require_cc("a_checker_without_its_comparison_is_caught_by_the_same_bytes");
    let lean = text(&lean_stdout(MUTANT));
    let wrongly_accepted: Vec<&str> = lean
        .lines()
        .filter(|l| l.starts_with("corrupt-") && l.contains(": ACCEPT "))
        .map(|l| l.split(':').next().unwrap_or(l))
        .collect();
    assert_eq!(
        wrongly_accepted,
        [
            "corrupt-truncated",
            "corrupt-claim-off-by-one",
            "corrupt-capture"
        ],
        "the mutant accepts exactly the cases only the comparison refuses"
    );
    let ran = clean_run(&program(MUTANT), &[]);
    assert_eq!(
        ran.status.and_then(|s| s.code()),
        Some(0),
        "`clean run` of the mutant failed: stderr={}",
        text(&ran.stderr)
    );
    assert_eq!(
        text(&ran.stdout),
        lean,
        "`clean run` did not follow the mutant's logic"
    );
    assert_ne!(
        text(&ran.stdout),
        VERDICTS,
        "the mutant printed the checker's verdicts: the byte assertion would not see a checker \
         that accepts corrupted advice"
    );
}

/// Every program on the C lane, against its pin. This is where each current
/// refusal is pinned by name, and where a closed gap fails loudly.
#[test]
fn every_program_lands_on_its_pinned_c_lane_outcome() {
    require_cc("every_program_lands_on_its_pinned_c_lane_outcome");
    let pins = gaps();
    let mut failures = Vec::new();
    for name in program_names() {
        let ran = clean_run(&program(&name), &[]);
        let live = classify_c(&name, &ran, &lean_stdout(&name));
        eprintln!("x1: {name:<40} c={} {}", live.class, live.refusal);
        check_pin(
            &name,
            "c",
            &live,
            &pinned_row(&pins, &name)["c_lane"],
            &mut failures,
        );
    }
    report("the C lane", &failures);
}

/// The gap list is the tracked artifact later units burn down, so it must be
/// about what is there: every program has a row and every row a program,
/// every pinned refusal is explained by a gap, every gap cites a program that
/// is refused on the lane it names, and every refusing source site still holds
/// the text it is cited for.
#[test]
fn the_gap_list_accounts_for_every_refusal() {
    let pins = gaps();
    let on_disk: BTreeSet<String> = program_names().into_iter().collect();
    let pinned: BTreeSet<String> = rows(&pins, "programs")
        .iter()
        .map(|row| str_field(row, "name", "a program row").to_string())
        .collect();
    assert_eq!(pinned, on_disk, "{GAPS} `programs` vs {FIXTURE}/programs");

    let gap_rows = rows(&pins, "gaps");
    let gap_ids: BTreeSet<&str> = gap_rows
        .iter()
        .map(|gap| str_field(gap, "id", "a gap"))
        .collect();
    assert_eq!(gap_ids.len(), gap_rows.len(), "gap ids are unique");

    let mut cited: BTreeSet<&str> = BTreeSet::new();
    for row in rows(&pins, "programs") {
        let name = str_field(row, "name", "a program row");
        for lane in ["c_lane", "trust_cg_lane"] {
            let pin = &row[lane];
            let outcome = str_field(pin, "outcome", name);
            let named: Vec<&str> = pin["gaps"]
                .as_array()
                .map(|ids| ids.iter().filter_map(Value::as_str).collect())
                .unwrap_or_default();
            assert_eq!(
                outcome == "BYTE_EQUAL",
                named.is_empty(),
                "{name} [{lane}]: exactly the refused rows cite the gap that refuses them"
            );
            for id in named {
                assert!(gap_ids.contains(id), "{name} [{lane}]: unknown gap `{id}`");
                cited.insert(id);
            }
        }
    }
    for gap in gap_rows {
        let id = str_field(gap, "id", "a gap");
        assert!(
            cited.contains(id),
            "gap `{id}` is cited by no refused program: a gap is pinned by a program that hits it"
        );
        for field in ["construct", "needed_for", "stage", "refusal"] {
            assert!(
                !str_field(gap, field, id).is_empty(),
                "gap `{id}`: empty `{field}`"
            );
        }
        check_site(id, &gap["site"]);
        for site in gap["more_sites"].as_array().into_iter().flatten() {
            check_site(id, site);
        }
    }
    // The summary a reader quotes is the rows' own count, not a second claim.
    let count = |keep: &dyn Fn(&Value) -> bool| -> u64 {
        rows(&pins, "programs")
            .iter()
            .filter(|row| ![CHECKER, MUTANT].contains(&str_field(row, "name", "a program row")))
            .filter(|row| keep(row))
            .count() as u64
    };
    let equal_on = |row: &Value, lane: &str| row[lane]["outcome"] == "BYTE_EQUAL";
    let summary = &pins["summary"];
    for (field, live) in [
        ("programs", rows(&pins, "programs").len() as u64),
        ("probes", count(&|_| true)),
        (
            "probes_byte_equal_on_both_lanes",
            count(&|row| equal_on(row, "c_lane") && equal_on(row, "trust_cg_lane")),
        ),
        (
            "probes_not_byte_equal_on_either_lane",
            count(&|row| !equal_on(row, "c_lane") && !equal_on(row, "trust_cg_lane")),
        ),
        ("open_gaps", gap_rows.len() as u64),
    ] {
        assert_eq!(
            summary[field].as_u64(),
            Some(live),
            "{GAPS}: `summary.{field}` is not what the rows say"
        );
    }
    // What the trust-cg lane does not give even where it prints the right
    // bytes. Each row cites the source line that makes it so.
    let shortfalls = rows(&pins, "lane_shortfalls");
    assert!(
        !shortfalls.is_empty(),
        "{GAPS}: the trust-cg lane's shortfalls are part of the measurement"
    );
    for shortfall in shortfalls {
        let id = str_field(shortfall, "id", "a lane shortfall");
        assert!(
            !str_field(shortfall, "what", id).is_empty(),
            "shortfall `{id}`: empty `what`"
        );
        check_site(id, &shortfall["site"]);
    }
}

/// A cited source site: the file exists, the row names a line, and the file
/// still holds the cited text. The LINE is a reader's pointer and may drift;
/// the text is what is held.
fn check_site(id: &str, site: &Value) {
    let file = str_field(site, "file", id);
    let needle = str_field(site, "needle", id);
    assert!(
        site["line"].as_u64().is_some_and(|line| line > 0),
        "`{id}`: the site names a line"
    );
    let source = std::fs::read_to_string(repo_root().join(file))
        .unwrap_or_else(|e| panic!("`{id}`: cited site {file}: {e}"));
    assert!(
        source.contains(needle),
        "`{id}`: {file} no longer holds the cited text `{needle}`; the refusal moved or closed, \
         so re-measure and update the row"
    );
}

/// X3's measuring half: every program through the trust-ir / trust-cg lane,
/// against its pin. The consumer is named explicitly (`CLEAN_TRUST_CG_BIN`),
/// as the LX0 battery requires, because the `PATH` one may predate the wire
/// Clean writes.
#[cfg(feature = "trust-ir-backend")]
#[test]
fn every_program_lands_on_its_pinned_trust_cg_lane_outcome() {
    require_cc("every_program_lands_on_its_pinned_trust_cg_lane_outcome");
    let selected = std::env::var_os("CLEAN_TRUST_CG_BIN").unwrap_or_else(|| {
        panic!(
            "CLEAN_TRUST_CG_BIN is not set: this measurement names its trust-cg explicitly; \
             point it at one that accepts --recognize-authority"
        )
    });
    assert!(
        Path::new(&selected).is_file(),
        "CLEAN_TRUST_CG_BIN={selected:?} is not a file"
    );
    let pins = gaps();
    let mut failures = Vec::new();
    for name in program_names() {
        let live = trust_cg_outcome(&name);
        eprintln!("x1: {name:<40} trust-cg={} {}", live.class, live.refusal);
        check_pin(
            &name,
            "trust-cg",
            &live,
            &pinned_row(&pins, &name)["trust_cg_lane"],
            &mut failures,
        );
    }
    report("the trust-cg lane", &failures);
}

/// One program through `clean run --backend trust-cg --receipt <file>`. The
/// receipt must say what the lane is (bodies `clean-compiler-unvalidated`, the
/// runtime C via `cc`) and, for a program that was built, that no body rode
/// outside that stamp or a kernel-TV claim.
#[cfg(feature = "trust-ir-backend")]
fn trust_cg_outcome(name: &str) -> Outcome {
    let receipt_dir = tempfile::tempdir().expect("receipt dir");
    let receipt_path = receipt_dir.path().join("receipt.json");
    let receipt_arg = receipt_path.to_str().expect("utf-8 receipt path");
    let ran = clean_run(
        &program(name),
        &["--backend", "trust-cg", "--receipt", receipt_arg],
    );
    let status = ran
        .status
        .unwrap_or_else(|| panic!("{name}: the trust-cg lane did not finish in {TIMEOUT:?}"));
    let raw = std::fs::read_to_string(&receipt_path).unwrap_or_else(|e| {
        panic!(
            "{name}: the trust-cg lane wrote no receipt ({e}); stderr={}",
            text(&ran.stderr)
        )
    });
    let receipt: Value =
        serde_json::from_str(&raw).unwrap_or_else(|e| panic!("{name}: receipt: {e}\n{raw}"));
    assert_eq!(
        receipt["lowered"], "clean-compiler-unvalidated",
        "{name}: {raw}"
    );
    assert_eq!(receipt["runtime"], "C via cc", "{name}: {raw}");
    let refused = |class: &'static str| Outcome {
        class,
        refusal: format!(
            "{}: {}",
            receipt["step"].as_str().unwrap_or_default(),
            receipt["cause"].as_str().unwrap_or_default()
        ),
    };
    match receipt["stage"].as_str() {
        Some("core") => return refused("EMIT_TRUSTIR_REFUSED"),
        Some("trust-cg") => return refused("TRUSTCG_REFUSED"),
        Some("link") => return refused("LINK_FAILED"),
        Some("built") => {}
        other => panic!("{name}: unknown receipt stage {other:?}:\n{raw}"),
    }
    assert!(
        receipt["bodies_unvalidated"].as_u64().unwrap_or(0) > 0,
        "{name}: a built program has bodies, and on this lane they are unvalidated: {raw}"
    );
    // Shortfall `no-body-is-licensed` of the gap list, pinned: the day a body
    // of one of these programs carries a kernel-TV certificate this fails, and
    // that row is re-measured.
    assert_eq!(
        receipt["kernel_tv_certified"].as_u64(),
        Some(0),
        "{name}: a body is kernel-TV certified; update `lane_shortfalls` in {GAPS}: {raw}"
    );
    let lean_out = lean_stdout(name);
    let err = text(&ran.stderr);
    if status.code() == Some(0) && ran.stdout == lean_out && ran.stderr.is_empty() {
        return Outcome {
            class: "BYTE_EQUAL",
            refusal: String::new(),
        };
    }
    if status.code() != Some(0) && lean_out.starts_with(&ran.stdout) {
        if let Some(outcome) = stopped_after_a_prefix(&err) {
            return outcome;
        }
    }
    panic!(
        "{name}: the trust-cg lane built a program that neither printed pinned Lean's bytes nor \
         stopped itself by name (status {status:?}).\n--- stdout\n{}\n--- Lean\n{}\n--- stderr\n{err}",
        text(&ran.stdout),
        text(&lean_out)
    );
}

/// Pinned Lean must have formed one shared Nat structural group, not split
/// an acyclic `mutual` block. The mint records the exact input as well as its
/// hash, and every compiled member must use every member's `_f` auxiliary.
#[test]
fn lean_compiled_each_call_cycle_as_one_mutual_group() {
    let artifact: Value = serde_json::from_slice(
        &std::fs::read(fixture().join("mutual_groups.json")).expect("Lean mutual-group evidence"),
    )
    .expect("JSON");
    assert!(artifact["lean_version"]
        .as_str()
        .expect("Lean version")
        .contains("version 4.30.0-rc2,"));
    assert_eq!(
        artifact["lean_version"].as_str().expect("Lean identity"),
        std::fs::read_to_string(fixture().join("expected/LEAN_VERSION"))
            .expect("pinned Lean identity")
            .trim()
    );
    let probes = artifact["probes"].as_array().expect("probes");
    assert_eq!(probes.len(), 3);
    let pins = gaps();
    for (probe, item) in probes.iter().zip(["i", "ix", "x"]) {
        let name = probe["program"].as_str().expect("program");
        let r4 = rows(&pins, "r4_items")
            .iter()
            .find(|r| r["item"] == item)
            .expect("item");
        assert_eq!(r4["program"], name);
        assert_eq!(
            probe["source"].as_str().expect("minted source"),
            std::fs::read_to_string(program(name)).expect("live source")
        );
        let members = probe["members"].as_array().expect("members");
        assert_eq!(members.len(), 3);
        let names: BTreeSet<&str> = members
            .iter()
            .map(|m| m.as_str().expect("member"))
            .collect();
        assert_eq!(
            names,
            BTreeSet::from(["whnf", "conv", if item == "i" { "infer" } else { "walk" }])
        );
        let bytes = text(&lean_stdout(name));
        assert!(
            bytes.contains("cycle: ACCEPT"),
            "{name}: no successful cycle execution"
        );
        assert!(
            bytes.contains("cycle-depth: REFUSE depth"),
            "{name}: no depth refusal through the cycle"
        );
        for member in members {
            let used = probe["used_constants"][member.as_str().expect("member")]
                .as_array()
                .expect("constant uses");
            assert!(
                used.iter().any(|n| n == "Nat.brecOn"),
                "{name}: not structural recursion on Nat"
            );
            for callee in members {
                let auxiliary = format!("{}._f", callee.as_str().expect("callee"));
                assert!(
                    used.iter().any(|n| n.as_str() == Some(&auxiliary)),
                    "{name}: {member} does not use {auxiliary}"
                );
            }
        }
    }
}

/// These are sampled depths, not a claim about every depth between them.
/// Both lane sweeps execute every named program and read its minted outcome.
#[test]
fn head_loop_samples_are_pinned_on_both_lanes() {
    let pins = gaps();
    let samples = rows(&pins, "head_loop_samples");
    assert_eq!(samples.len(), 3);
    let base =
        std::fs::read_to_string(program("c27_r4_iv_head_loop_million")).expect("million probe");
    for (sample, steps) in samples.iter().zip([10000_u64, 100000, 1000000]) {
        assert_eq!(sample["steps"].as_u64(), Some(steps));
        let name = sample["program"].as_str().expect("sample program");
        let expected_source = base
            .replace("1000000", &steps.to_string())
            .replace("1000001", &(steps + 1).to_string());
        assert_eq!(
            std::fs::read_to_string(program(name)).expect("sample source"),
            expected_source
        );
        let row = pinned_row(&pins, name);
        for lane in ["c_lane", "trust_cg_lane"] {
            assert_eq!(
                sample[lane], row[lane],
                "the sample and execution pin must agree"
            );
            let measured = &sample["measurement"][lane];
            assert_eq!(measured["pin"]["outcome"], row[lane]["outcome"]);
            assert_eq!(measured["pin"]["refusal"], row[lane]["refusal"]);
            let args = measured["command"].as_array().expect("measured command");
            assert!(args.iter().any(|a| a == "run"));
            assert!(args.iter().any(|a| a
                .as_str()
                .is_some_and(|a| a.ends_with(&format!("/{name}.lean")))));
            assert_eq!(
                args.iter().any(|a| a == "trust-cg"),
                lane == "trust_cg_lane"
            );
            let out = measured["stdout"].as_str().expect("measured stdout");
            let err = measured["stderr"].as_str().expect("measured stderr");
            let code = measured["exit_code"].as_i64().expect("measured exit code");
            match row[lane]["outcome"].as_str().expect("sample outcome") {
                "BYTE_EQUAL" => {
                    assert_eq!(code, 0);
                    assert_eq!(out.as_bytes(), lean_stdout(name));
                    assert!(err.is_empty());
                }
                "CRASHED" => {
                    assert_ne!(code, 0);
                    assert!(lean_stdout(name).starts_with(out.as_bytes()));
                    assert!(err
                        .lines()
                        .any(|l| l.starts_with("clean run: program terminated by signal ")));
                }
                other => panic!("head-loop sample {name} has no execution measurement: {other}"),
            }
            if lane == "trust_cg_lane" {
                assert_eq!(measured["receipt"]["stage"], "built");
            }
        }
        assert!(
            sample["measurement"].is_object(),
            "sample must carry both production callers' measurements"
        );
    }
}

/// The same live predicate must refuse the original acyclic mutual block.
/// This runs inside the caller's heavy-gate reservation, using pinned elan Lean.
#[test]
fn lean_mutual_group_predicate_refuses_acyclic_c24() {
    let output = Command::new("python3")
        .arg(repo_root().join("scripts/x1_mutual_evidence.py"))
        .arg("--negative-control")
        .current_dir(repo_root())
        .output()
        .expect("run mutual negative control");
    assert!(output.status.success(), "{}", text(&output.stderr));
    assert!(
        text(&output.stdout).contains("X1_MUTUAL_NEGATIVE_CONTROL=refused acyclic c24"),
        "{}",
        text(&output.stdout)
    );
}
