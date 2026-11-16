// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit Q1 of `docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md`, through
//! its production caller: `clean_export_write` writes the `theories/cic_l`
//! closure (every module of its `ORDER`, compiled by pinned Lean, with the
//! part of `Init` it rests on) as a lean4export NDJSON 3.1.0 export, and the
//! bytes are then
//!
//! - read back by Clean's reader and written again, byte-identical, and
//!   written a second time by this process from its own load, byte-identical
//!   (the output is a function of the constants, in any process);
//! - accepted by the fenced reference entry over foundational axioms only;
//! - accepted by pinned Lean's own kernel (`scripts/lean_export_replay.sh`:
//!   `Lean.Environment.replay` from an empty environment), once parsed by
//!   Clean's reading of the format written in Lean
//!   (`scripts/lean_export_replay/Replay.lean`) and once by lean4export's own
//!   parser at the commit `scripts/lean_export_mint.sh` pins
//!   (`--reader upstream`, `scripts/lean_export_replay/Upstream.lean`), so
//!   that in the second no step of the verdict is Clean's;
//! - refused by all three, for the stated reason, with a planted axiom and
//!   with a planted ill-typed body. Each control changes the bytes only.
//!
//! The upstream reader needs the mint script's pinned lean4export checkout,
//! as every test here needs the pinned toolchain: build it once with
//! `scripts/lean_export_mint.sh --toolchain <the pinned tag> --module
//! Init.Prelude`. Without it those steps fail, naming that command.
//!
//! What this does not show: that upstream's `lake check` (Lean v4.35 and
//! later) reads the file; no toolchain here ships it.

use std::collections::{BTreeSet, HashMap};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::{Mutex, OnceLock, PoisonError};

use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_olean::ndjson::{
    check_export_reader, check_export_round_trip, reference_check_export_reader, write_export,
    ExportCheckOptions, ExportReferenceReport, ExportWriteError, ExportWriteMeta,
    ExportWriteSummary, EXPORTER_NAME, LEAN_FOUNDATIONAL_AXIOMS,
};
use clean_olean::test_support::compiled_fixture_dir;
use clean_olean::{load_module_with_deps_shared, require_pinned_lean_lib_path};
use serde_json::Value;

/// The ground theorem both controls are planted at.
const SUBJECT: &str = "CICL.ListSupportCases.identity";

/// A definition whose type Lean wrote over a level that is not a fixed point
/// of the kernel's simplifying level constructors.
const LEVEL_SUBJECT: &str = "CICL.ConstantPayload.ctorElimType";

/// The reader, the loader and the entry recurse on terms.
const STACK_BYTES: usize = 1024 * 1024 * 1024;

/// One heavy step at a time: each holds an environment or runs Lean.
static HEAVY: Mutex<()> = Mutex::new(());

struct Minted {
    _dir: tempfile::TempDir,
    path: PathBuf,
    bytes: Vec<u8>,
    summary: ExportWriteSummary,
    modules: Vec<String>,
    lean_paths: Vec<PathBuf>,
    meta: ExportWriteMeta,
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("the repository root")
}

/// The modules of `theories/cic_l/ORDER`, as Lean names them.
fn theory_modules() -> Vec<String> {
    let order = repo_root().join("theories/cic_l/ORDER");
    let text = std::fs::read_to_string(&order)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", order.display()));
    let modules: Vec<String> = text
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(|line| line.replace('/', "."))
        .collect();
    assert!(!modules.is_empty(), "{} names no module", order.display());
    modules
}

/// `meta.lean` of the pinned toolchain, from its own `lean`.
fn pinned_meta() -> ExportWriteMeta {
    let lean = clean_olean::pinned_lean_binary().expect("the pinned Lean binary");
    let ask = |flag: &str| -> String {
        let out = Command::new(&lean)
            .arg(flag)
            .output()
            .unwrap_or_else(|e| panic!("cannot run {} {flag}: {e}", lean.display()));
        assert!(out.status.success(), "{} {flag} failed", lean.display());
        String::from_utf8(out.stdout)
            .expect("UTF-8")
            .trim()
            .to_owned()
    };
    let version = ask("--version");
    let lean_version = version
        .split_once("version ")
        .and_then(|(_, rest)| rest.split_once(','))
        .map(|(v, _)| v.to_owned())
        .unwrap_or_else(|| panic!("cannot read a version in `{version}`"));
    ExportWriteMeta {
        lean_version,
        lean_githash: ask("--githash"),
    }
}

fn on_big_stack<T: Send + 'static>(work: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(STACK_BYTES)
        .spawn(work)
        .expect("spawn")
        .join()
        .expect("the worker panicked")
}

/// The export of the CIC_L closure, written once by the binary.
fn minted() -> &'static Minted {
    static MINTED: OnceLock<Minted> = OnceLock::new();
    MINTED.get_or_init(|| {
        let lib = require_pinned_lean_lib_path().expect("install the repository-pinned Lean");
        let compiled = compiled_fixture_dir("cic_l_level");
        let modules = theory_modules();
        let meta = pinned_meta();
        let dir = tempfile::tempdir().expect("a temporary directory");
        let path = dir.path().join("cic_l.ndjson");
        let mut command = Command::new(env!("CARGO_BIN_EXE_clean_export_write"));
        for module in &modules {
            command.args(["--module", module]);
        }
        command
            .arg("--lean-path")
            .arg(&compiled)
            .arg("--lean-path")
            .arg(&lib)
            .args(["--lean-version", &meta.lean_version])
            .args(["--lean-githash", &meta.lean_githash])
            .args(["--targets-containing", "CICL."])
            .arg("--out")
            .arg(&path);
        let out = command.output().expect("run clean_export_write");
        assert!(
            out.status.success(),
            "clean_export_write failed: {}\n{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        let line: Value = serde_json::from_slice(&out.stdout).expect("one JSON line");
        let summary: ExportWriteSummary =
            serde_json::from_value(line["written"].clone()).expect("the written summary");
        let bytes = std::fs::read(&path).expect("the published export");
        assert!(
            !path.with_extension("ndjson.partial").exists(),
            "a partial file was left beside the export"
        );
        eprintln!("Q1 export: {line}");
        Minted {
            _dir: dir,
            path,
            bytes,
            summary,
            modules,
            lean_paths: vec![compiled, lib],
            meta,
        }
    })
}

fn reference(bytes: Vec<u8>) -> ExportReferenceReport {
    reference_permitted(bytes, &LEAN_FOUNDATIONAL_AXIOMS)
}

fn reference_permitted(bytes: Vec<u8>, permitted: &[&str]) -> ExportReferenceReport {
    // Measure the production command used by the quorum, and require its
    // report and exit code to match the library verdict exactly.
    let file = tempfile::NamedTempFile::new().expect("an export file");
    std::fs::write(file.path(), &bytes).expect("write export bytes");
    let mut command = Command::new(env!("CARGO_BIN_EXE_clean_export_check"));
    command.args(["--reference", "--json"]).arg(file.path());
    for axiom in permitted {
        command.args(["--permit", axiom]);
    }
    let out = command.output().expect("run the reference quorum member");
    let permitted: Vec<String> = permitted.iter().map(|s| (*s).to_owned()).collect();
    let report = on_big_stack(move || {
        let permitted: Vec<&str> = permitted.iter().map(String::as_str).collect();
        reference_check_export_reader(bytes.as_slice(), &permitted)
    });
    assert_eq!(
        out.status.code(),
        Some(i32::from(!report.accepted)),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let line: Value = serde_json::from_slice(&out.stdout).expect("reference JSON report");
    assert_eq!(line, serde_json::to_value(&report).expect("report JSON"));
    report
}

/// `scripts/lean_export_replay.sh <export> --permit <each foundational axiom>`.
fn lean_replay(export: &Path) -> Output {
    let mut command = Command::new(repo_root().join("scripts/lean_export_replay.sh"));
    command.arg(export);
    for axiom in LEAN_FOUNDATIONAL_AXIOMS {
        command.args(["--permit", axiom]);
    }
    command.output().expect("run scripts/lean_export_replay.sh")
}

/// `scripts/lean_export_replay.sh --reader upstream <export> --permit <each
/// foundational axiom>`: lean4export's own parser, then Lean's kernel.
fn lean_replay_upstream(export: &Path) -> Output {
    let mut command = Command::new(repo_root().join("scripts/lean_export_replay.sh"));
    command.args(["--reader", "upstream"]).arg(export);
    for axiom in LEAN_FOUNDATIONAL_AXIOMS {
        command.args(["--permit", axiom]);
    }
    let out = command
        .output()
        .expect("run scripts/lean_export_replay.sh --reader upstream");
    assert_ne!(
        out.status.code(),
        Some(2),
        "the upstream reader did not judge the export (exit 2); without the pinned \
         lean4export checkout, build it once with `scripts/lean_export_mint.sh --toolchain \
         <the pinned tag> --module Init.Prelude`: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    out
}

/// The index → rendered name table of an export's name records.
fn names_of(bytes: &[u8]) -> HashMap<u64, String> {
    let mut names: HashMap<u64, String> = HashMap::new();
    names.insert(0, String::new());
    for line in bytes.split(|b| *b == b'\n') {
        if !line.starts_with(br#"{"in":"#) {
            continue;
        }
        let record: Value = serde_json::from_slice(line).expect("a name record");
        let (pre, part) = if let Some(s) = record.get("str") {
            (&s["pre"], s["str"].as_str().expect("str").to_owned())
        } else {
            let n = &record["num"];
            (&n["pre"], n["i"].as_u64().expect("i").to_string())
        };
        let pre = &names[&pre.as_u64().expect("pre")];
        let rendered = if pre.is_empty() {
            part
        } else {
            format!("{pre}.{part}")
        };
        names.insert(record["in"].as_u64().expect("in"), rendered);
    }
    names
}

/// The line number and record of the theorem `SUBJECT`.
fn subject_record(bytes: &[u8]) -> (usize, Value) {
    let names = names_of(bytes);
    let mut found = Vec::new();
    for (number, line) in bytes.split(|b| *b == b'\n').enumerate() {
        if !line.starts_with(br#"{"thm":"#) {
            continue;
        }
        let record: Value = serde_json::from_slice(line).expect("a thm record");
        let name = record["thm"]["name"].as_u64().expect("name");
        if names[&name] == SUBJECT {
            found.push((number, record));
        }
    }
    assert_eq!(found.len(), 1, "{SUBJECT} is declared once");
    let (number, record) = found.remove(0);
    assert_eq!(
        record["thm"]["levelParams"],
        serde_json::json!([]),
        "{SUBJECT} is a ground theorem"
    );
    (number, record)
}

/// The export with two records appended: the axiom `planted_axiom`, stating
/// what `SUBJECT` states, and the theorem `planted_theorem`, proved by it.
fn with_planted_axiom(minted: &Minted) -> Vec<u8> {
    let (_, subject) = subject_record(&minted.bytes);
    let stated = subject["thm"]["type"].clone();
    let axiom = minted.summary.names as u64 + 1;
    let theorem = axiom + 1;
    let proof = minted.summary.exprs as u64;
    let mut bytes = minted.bytes.clone();
    for record in [
        serde_json::json!({"in": axiom, "str": {"pre": 0, "str": "planted_axiom"}}),
        serde_json::json!({"axiom": {"isUnsafe": false, "levelParams": [], "name": axiom,
            "type": stated}}),
        serde_json::json!({"in": theorem, "str": {"pre": 0, "str": "planted_theorem"}}),
        serde_json::json!({"ie": proof, "const": {"name": axiom, "us": []}}),
        serde_json::json!({"thm": {"all": [theorem], "levelParams": [], "name": theorem,
            "type": stated, "value": proof}}),
    ] {
        bytes.extend_from_slice(record.to_string().as_bytes());
        bytes.push(b'\n');
    }
    bytes
}

/// The export with `SUBJECT`'s proof replaced by its own statement: a
/// proposition where a proof of it is owed.
fn with_ill_typed_body(minted: &Minted) -> Vec<u8> {
    let (number, mut subject) = subject_record(&minted.bytes);
    let stated = subject["thm"]["type"].clone();
    assert_ne!(subject["thm"]["value"], stated);
    subject["thm"]["value"] = stated;
    let mut bytes = Vec::with_capacity(minted.bytes.len());
    for (index, line) in minted.bytes.split(|b| *b == b'\n').enumerate() {
        if line.is_empty() {
            continue;
        }
        if index == number {
            bytes.extend_from_slice(subject.to_string().as_bytes());
        } else {
            bytes.extend_from_slice(line);
        }
        bytes.push(b'\n');
    }
    bytes
}

fn write_beside(minted: &Minted, name: &str, bytes: &[u8]) -> PathBuf {
    let path = minted.path.with_file_name(name);
    std::fs::write(&path, bytes).expect("write a mutated export");
    path
}

#[path = "ndjson_export_writer/cases.rs"]
mod cases;
#[path = "ndjson_export_writer/level_control.rs"]
mod level_control;
