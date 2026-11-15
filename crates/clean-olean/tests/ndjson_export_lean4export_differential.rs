// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit Q1 of `docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md`: Clean's
//! export writer against lean4export itself.
//!
//! The fixture `tests/fixtures/lean/v4.30.0-rc2/lean4export_minted/
//! prelude_roots.ndjson.gz` is lean4export, built at its pinned commit for
//! pinned Lean v4.30.0-rc2 and run by `scripts/lean_export_mint.sh` over
//! `Init.Prelude` with `--export-mdata` and the roots in [`ROOTS`] (the
//! sidecar beside it records the exporter commit, its binary's hash, the
//! command and the export's sha256; the file was then compressed with
//! `gzip -9 -n`). `clean_export_write` writes the cone of the same roots from
//! the same toolchain's `Init.Prelude` `.olean`, and
//! `scripts/lean_export_differential.py` compares the two files, each read on
//! its own by code that is not Clean's, declaration by declaration.
//!
//! The raw bytes differ by the format's design, and that script normalizes
//! what differs by design: each writer numbers its tables and orders its
//! records its own way; lean4export writes binder names, `mdata` payloads,
//! the `all` of a definition, and a block's recursors in its `NameSet`'s
//! order, and Clean's kernel terms keep none of those. The same declarations
//! are declared on both sides. What else differs is measured, explained and
//! pinned here, so the test fails the day either list changes:
//!
//! - [`BINDER_INFO_ONLY`]: declarations that differ in binder annotations
//!   alone. lean4export's expression table is a `HashMap Expr Nat`, and
//!   Lean's `BEq Expr` (`Expr.eqv`) ignores binder annotations, so it writes
//!   a term equal to an earlier one up to annotations as that earlier term.
//!   Pinned Lean's environment holds the annotations Clean wrote: the last
//!   test here reads Clean's export with lean4export's own parser and
//!   compares every constant with the one Lean imports
//!   (`scripts/lean_export_replay.sh --reader upstream --against
//!   Init.Prelude`), and only [`HINT_ONLY`] differs there (decision of
//!   2026-11-13 in `docs/DECISIONS.md`).
//! - [`HINT_ONLY`]: definitions whose unfolding hint differs, Clean writing
//!   `abbrev` where Lean stored `regular 1`. The `.olean` loader promotes
//!   Lean's parameter-annotation identities to `Reducible`
//!   (`import/convert.rs`), the kernel keeps no other record of the hint, and
//!   the writer writes what the kernel holds. A hint orders unfolding in
//!   Lean's kernel and decides no acceptance.
//!
//! The controls show a changed binder annotation, a changed hint and a
//! missing declaration are each found by the differential, and a changed
//! binder annotation by the comparison with Lean's environment.
//!
//! `scripts/lean_export_differential.sh` runs the same comparison over the
//! `theories/cic_l` closure, where lean4export has to be built first; the
//! measurement is recorded in `docs/DECISIONS.md`.

use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use clean_olean::require_pinned_lean_lib_path;
use serde_json::Value;

/// The roots both exports were written for: a definition by structural
/// recursion, a polymorphic one, a structure projection, an array primitive,
/// the quotient, a nested inductive (three recursors), a theorem, an axiom,
/// an opaque constant and a hash over a nested type.
const ROOTS: [&str; 10] = [
    "Nat.add",
    "List.map",
    "String.utf8ByteSize",
    "Array.push",
    "Quot.lift",
    "Lean.Syntax",
    "of_decide_eq_true",
    "sorryAx",
    "Lean.Macro.MethodsRefPointed",
    "Lean.Name.hash",
];

/// Declarations that differ from lean4export's in binder annotations alone
/// (module docs).
const BINDER_INFO_ONLY: [&str; 5] = [
    "Nat.ble_succ_eq_true",
    "Nat.eq_or_lt_of_le",
    "Nat.eq_or_lt_of_le.match_3",
    "_private.Init.Prelude.0.Nat.pred_le_pred.match_1_1",
    "_private.Init.Prelude.0.Or.elim.match_1_1",
];

/// Definitions whose hint differs from lean4export's, and nothing else
/// (module docs).
const HINT_ONLY: [&str; 2] = ["optParam", "outParam"];

const LEAN_TAG: &str = "v4.30.0-rc2";
const LEAN_VERSION: &str = "4.30.0-rc2";
const LEAN_GITHASH: &str = "3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc";
const LEAN4EXPORT_COMMIT: &str = "12581a6b680d8478175596338eb2d53383a323e3";

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("the repository root")
}

fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/lean/v4.30.0-rc2/lean4export_minted")
}

/// lean4export's bytes, decompressed, checked against the sidecar's sha256.
fn lean4export_bytes() -> Vec<u8> {
    let path = fixture_dir().join("prelude_roots.ndjson.gz");
    let compressed = std::fs::read(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    let mut bytes = Vec::new();
    flate2::read::GzDecoder::new(compressed.as_slice())
        .read_to_end(&mut bytes)
        .expect("a gzip stream");
    let sidecar_path = fixture_dir().join("prelude_roots.ndjson.sidecar.json");
    let sidecar: Value = serde_json::from_slice(
        &std::fs::read(&sidecar_path).unwrap_or_else(|e| panic!("{}: {e}", sidecar_path.display())),
    )
    .expect("the sidecar is JSON");
    let sha = {
        use sha2::Digest;
        hex(&sha2::Sha256::digest(&bytes))
    };
    assert_eq!(
        sidecar["export"]["sha256"].as_str(),
        Some(sha.as_str()),
        "the fixture is not the export the sidecar records"
    );
    assert_eq!(
        sidecar["exporter"]["commit"].as_str(),
        Some(LEAN4EXPORT_COMMIT)
    );
    assert_eq!(
        sidecar["exporter"]["kind"].as_str(),
        Some("lean4export-repo")
    );
    assert_eq!(sidecar["toolchain"].as_str(), Some(LEAN_TAG));
    assert_eq!(sidecar["lean_githash"].as_str(), Some(LEAN_GITHASH));
    assert_eq!(sidecar["modules"], serde_json::json!(["Init.Prelude"]));
    assert_eq!(sidecar["decls"], serde_json::json!(ROOTS));
    assert_eq!(sidecar["options"], serde_json::json!(["--export-mdata"]));
    bytes
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Clean's export of the cone of [`ROOTS`] from the pinned `Init.Prelude`.
fn clean_export(dir: &Path) -> PathBuf {
    let lib = require_pinned_lean_lib_path().expect("install the repository-pinned Lean");
    let out = dir.join("clean.ndjson");
    let mut command = Command::new(env!("CARGO_BIN_EXE_clean_export_write"));
    command
        .args(["--module", "Init.Prelude", "--lean-path"])
        .arg(&lib)
        .args([
            "--lean-version",
            LEAN_VERSION,
            "--lean-githash",
            LEAN_GITHASH,
        ]);
    for root in ROOTS {
        command.args(["--target", root]);
    }
    let output = command
        .arg("--out")
        .arg(&out)
        .output()
        .expect("run clean_export_write");
    assert!(
        output.status.success(),
        "clean_export_write failed: {}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    out
}

/// `scripts/lean_export_differential.py compare <clean> <lean4export>`.
fn compare(clean: &Path, lean4export: &Path) -> (Output, Value) {
    let output = Command::new("python3")
        .arg("-I")
        .arg(repo_root().join("scripts/lean_export_differential.py"))
        .arg("compare")
        .arg(clean)
        .arg(lean4export)
        .output()
        .expect("run scripts/lean_export_differential.py");
    let verdict: Value = serde_json::from_slice(&output.stdout).unwrap_or_else(|e| {
        panic!(
            "no JSON verdict ({e}): {}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    });
    (output, verdict)
}

/// The bytes with the first occurrence of `from` (on a line starting with
/// `prefix`) replaced by `to`.
fn replace_once(bytes: &[u8], prefix: &[u8], from: &[u8], to: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(bytes.len());
    let mut done = false;
    for line in bytes.split_inclusive(|b| *b == b'\n') {
        if !done && line.starts_with(prefix) {
            if let Some(at) = line.windows(from.len()).position(|w| w == from) {
                out.extend_from_slice(&line[..at]);
                out.extend_from_slice(to);
                out.extend_from_slice(&line[at + from.len()..]);
                done = true;
                continue;
            }
        }
        out.extend_from_slice(line);
    }
    assert!(done, "no line starting with {prefix:?} holds {from:?}");
    out
}

#[test]
fn test_export_writer_states_what_lean4export_states_for_the_prelude_roots() {
    let dir = tempfile::tempdir().expect("a temporary directory");
    let theirs_bytes = lean4export_bytes();
    let theirs = dir.path().join("lean4export.ndjson");
    std::fs::write(&theirs, &theirs_bytes).expect("write lean4export's export");
    let ours = clean_export(dir.path());

    let (output, verdict) = compare(&ours, &theirs);
    assert_eq!(output.status.code(), Some(1), "{verdict:#}");
    assert_eq!(verdict["left"]["exporter"]["name"], "clean-export");
    assert_eq!(verdict["right"]["exporter"]["name"], "lean4export");
    assert_eq!(verdict["same_lean"], true);
    let declared = verdict["left"]["declarations"].as_u64().expect("a count");
    assert!(declared > 300, "the cone of the roots is small: {declared}");
    assert_eq!(verdict["right"]["declarations"].as_u64(), Some(declared));
    // The same declarations on both sides, grouped alike.
    assert_eq!(verdict["only_left_count"], 0, "{verdict:#}");
    assert_eq!(verdict["only_right_count"], 0, "{verdict:#}");
    assert_eq!(verdict["grouped_otherwise_count"], 0, "{verdict:#}");
    // What differs is exactly the measured, explained lists (module docs).
    assert_eq!(verdict["verdict"], "different");
    assert_eq!(verdict["differing"], hint_only(), "{verdict:#}");
    assert_eq!(
        verdict["binder_info_only"],
        serde_json::json!(BINDER_INFO_ONLY)
    );
    eprintln!(
        "Q1 lean4export differential (Init.Prelude roots): {declared} declarations; {} differ \
         in binder annotations alone (lean4export's), {} in the hint alone (the loader's)",
        BINDER_INFO_ONLY.len(),
        HINT_ONLY.len()
    );
}

/// [`HINT_ONLY`] as the comparison lists it.
fn hint_only() -> Value {
    Value::Array(
        HINT_ONLY
            .iter()
            .map(|name| serde_json::json!({"declaration": name, "fields": ["hints"]}))
            .collect(),
    )
}

/// The index of the name record spelling `dotted` (each component a string).
fn name_index(bytes: &[u8], dotted: &str) -> u64 {
    let mut names: std::collections::HashMap<u64, String> = [(0, String::new())].into();
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
        let index = record["in"].as_u64().expect("in");
        if rendered == dotted {
            return index;
        }
        names.insert(index, rendered);
    }
    panic!("no name record spells {dotted}")
}

#[test]
fn test_export_writer_differential_finds_a_changed_binder_hint_or_declaration() {
    let dir = tempfile::tempdir().expect("a temporary directory");
    let theirs_bytes = lean4export_bytes();
    let ours = clean_export(dir.path());
    let planted = |name: &str, bytes: &[u8]| -> Value {
        let path = dir.path().join(name);
        std::fs::write(&path, bytes).expect("write a planted export");
        let (output, verdict) = compare(&ours, &path);
        assert_eq!(output.status.code(), Some(1), "{name}: {verdict:#}");
        assert_eq!(verdict["verdict"], "different", "{name}");
        verdict
    };

    // One binder's annotation: the declarations over that term move in or
    // out of the binder-only list; nothing else changes.
    let binder = planted(
        "binder.ndjson",
        &replace_once(
            &theirs_bytes,
            br#"{"forallE":"#,
            br#""binderInfo":"default""#,
            br#""binderInfo":"implicit""#,
        ),
    );
    assert_ne!(
        binder["binder_info_only"],
        serde_json::json!(BINDER_INFO_ONLY),
        "{binder:#}"
    );
    assert_eq!(binder["differing"], hint_only(), "{binder:#}");
    assert_eq!(binder["only_left_count"], 0);
    assert_eq!(binder["only_right_count"], 0);

    // `Nat.add`'s hint: it joins the hint-only list, in its hints alone.
    let nat_add = name_index(&theirs_bytes, "Nat.add");
    let hint = planted(
        "hint.ndjson",
        &replace_once(
            &theirs_bytes,
            format!(r#"{{"def":{{"all":[{nat_add}],"#).as_bytes(),
            br#"{"regular":"#,
            br#"{"regular":9"#,
        ),
    );
    assert_eq!(hint["differing_count"], 3, "{hint:#}");
    assert!(
        hint["differing"]
            .as_array()
            .expect("a list")
            .contains(&serde_json::json!({"declaration": "Nat.add", "fields": ["hints"]})),
        "{hint:#}"
    );

    // The last declaration dropped: Clean declares names lean4export does not.
    let mut lines: Vec<&[u8]> = theirs_bytes.split_inclusive(|b| *b == b'\n').collect();
    let declaration_kinds: [&[u8]; 6] = [
        br#"{"axiom":"#,
        br#"{"def":"#,
        br#"{"thm":"#,
        br#"{"opaque":"#,
        br#"{"quot":"#,
        br#"{"inductive":"#,
    ];
    let last = lines
        .iter()
        .rposition(|line| declaration_kinds.iter().any(|kind| line.starts_with(kind)))
        .expect("a declaration record");
    lines.remove(last);
    let dropped = planted("dropped.ndjson", &lines.concat());
    assert!(dropped["only_left_count"].as_u64() > Some(0), "{dropped:#}");
    assert_eq!(dropped["only_right_count"], 0);
}

/// `scripts/lean_export_replay.sh --reader upstream <export> --against
/// Init.Prelude`: lean4export's own parser reads the export, Lean imports
/// `Init.Prelude`, and `scripts/lean_export_replay/Compare.lean` compares
/// every constant the export declares with Lean's, field by field and with
/// binder annotations. The verdict is the last line of stdout.
fn against_lean(export: &Path) -> (Output, Value) {
    let output = Command::new(repo_root().join("scripts/lean_export_replay.sh"))
        .args(["--toolchain", LEAN_TAG, "--reader", "upstream"])
        .arg(export)
        .args(["--against", "Init.Prelude"])
        .output()
        .expect("run scripts/lean_export_replay.sh --against");
    assert_ne!(
        output.status.code(),
        Some(2),
        "the comparison did not judge the export (exit 2); without the pinned lean4export \
         checkout, build it once with `scripts/lean_export_mint.sh --toolchain {LEAN_TAG} \
         --module Init.Prelude`: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    let last = stdout.lines().last().unwrap_or_default();
    let verdict: Value = serde_json::from_str(last).unwrap_or_else(|e| {
        panic!(
            "no JSON verdict ({e}): {stdout}\n{}",
            String::from_utf8_lossy(&output.stderr)
        )
    });
    (output, verdict)
}

/// A comparison's `differing` list, ordered by name.
fn by_name(list: &Value) -> Vec<Value> {
    let mut entries = list.as_array().expect("a list").clone();
    entries.sort_by_key(|entry| entry["name"].as_str().unwrap_or_default().to_owned());
    entries
}

#[test]
fn test_export_writer_states_what_leans_environment_holds_for_the_prelude_roots() {
    let dir = tempfile::tempdir().expect("a temporary directory");
    let ours = clean_export(dir.path());

    let (output, verdict) = against_lean(&ours);
    assert_eq!(output.status.code(), Some(1), "{verdict:#}");
    assert_eq!(verdict["reader"], "lean4export Export.parseStream");
    assert_eq!(verdict["modules"], serde_json::json!(["Init.Prelude"]));
    assert_eq!(verdict["lean_version"], LEAN_VERSION);
    assert_eq!(verdict["lean_githash"], LEAN_GITHASH);
    let compared = verdict["compared"].as_u64().expect("a count");
    assert!(compared > 300, "the cone of the roots is small: {compared}");
    // Every constant is in Lean's environment, and every one but the
    // loader's promoted hints (module docs) is equal to Lean's, binder
    // annotations included: the declarations in [`BINDER_INFO_ONLY`] among
    // them, so the annotations that differ from lean4export's are Lean's.
    assert_eq!(verdict["absent"], serde_json::json!([]), "{verdict:#}");
    let hints: Vec<Value> = HINT_ONLY
        .iter()
        .map(|name| serde_json::json!({"name": name, "fields": ["hints regular 1 vs abbrev"]}))
        .collect();
    assert_eq!(by_name(&verdict["differing"]), hints, "{verdict:#}");
    assert_eq!(
        verdict["equal"].as_u64(),
        Some(compared - HINT_ONLY.len() as u64)
    );
    eprintln!(
        "Q1 against Lean's environment (Init.Prelude roots): {compared} constants compared, \
         {} equal, {} differing in the hint alone",
        compared - HINT_ONLY.len() as u64,
        HINT_ONLY.len()
    );

    // Control: one binder annotation changed in Clean's export is found, in
    // the type, value or recursor rules of a constant over that term.
    let ours_bytes = std::fs::read(&ours).expect("read Clean's export");
    let planted = dir.path().join("binder.ndjson");
    std::fs::write(
        &planted,
        replace_once(
            &ours_bytes,
            br#"{"forallE":"#,
            br#""binderInfo":"default""#,
            br#""binderInfo":"implicit""#,
        ),
    )
    .expect("write the planted export");
    let (output, verdict) = against_lean(&planted);
    assert_eq!(output.status.code(), Some(1), "{verdict:#}");
    let differing = verdict["differing"].as_array().expect("a list");
    assert!(
        differing.iter().any(|entry| {
            entry["fields"]
                .as_array()
                .expect("fields")
                .iter()
                .any(|field| ["type", "value", "rules"].contains(&field.as_str().unwrap_or("")))
        }),
        "a changed binder annotation was not found: {verdict:#}"
    );
    assert!(verdict["differing_count"].as_u64() > Some(HINT_ONLY.len() as u64));
}
