// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
//! CL-03 exercises the source producer and the independent replay CLI in separate processes.

use clean_kernel::name::Name;
use serde_json::Value;
use std::collections::BTreeMap;
use std::fs;
use std::path::Path;
use std::process::{Command, Output};

fn write_project(root: &Path) {
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/export_ndjson");
    for file in [
        "lakefile.toml",
        "lean-toolchain",
        "ExportSupport.lean",
        "Roundtrip.lean",
        "UseRecOn.lean",
    ] {
        fs::copy(fixture.join(file), root.join(file)).expect("copy source-only fixture");
    }
}

fn export(root: &Path, entry: &str, output: &Path) -> Output {
    Command::new(env!("CARGO_BIN_EXE_clean"))
        .current_dir(root)
        .env(
            "LEAN_PATH",
            clean_olean::pinned_lean_lib_path().expect("pinned Lean library"),
        )
        .args(["check", "--export-ndjson"])
        .arg(output)
        .arg(entry)
        .output()
        .expect("run source exporter")
}

fn replay(root: &Path, filename: &str, code: i32) -> Value {
    let output = Command::new(env!("CARGO_BIN_EXE_clean"))
        .current_dir(root)
        .env_remove("LEAN_PATH")
        .args(["olean", "replay", "--from-export", filename, "--json"])
        .output()
        .expect("start a fresh replay process");
    assert_eq!(output.status.code(), Some(code), "{output:?}");
    let report: Value = serde_json::from_slice(&output.stdout).expect("JSON replay report");
    assert_eq!(report["exit_code"], code);
    assert!(report["reader_error"].is_null(), "{report}");
    assert!(report["decline_reason"].is_null(), "{report}");
    for field in ["budget_exhausted", "not_replayable"] {
        assert_eq!(report[field], 0, "{report}");
    }
    report
}

// Count the actual declaration names in the serialized records. An inductive block is one
// JSON line but declares every type, constructor and recursor it contains.
fn wire_roster(lines: &[Value]) -> BTreeMap<String, (&'static str, usize)> {
    let mut names = BTreeMap::from([(0, Name::anon())]);
    let mut roster = BTreeMap::new();
    for (index, record) in lines.iter().enumerate() {
        if let Some(id) = record["in"].as_u64() {
            let part = record.get("str").unwrap_or(&record["num"]);
            let parent = names[&part["pre"].as_u64().expect("name prefix")].clone();
            let name = match part["str"].as_str() {
                Some(s) => parent.str(s),
                None => parent.num(part["i"].as_u64().expect("numeric name")),
            };
            assert!(names.insert(id, name).is_none());
        }
        let mut add = |entry: &Value, kind| {
            let id = entry["name"].as_u64().expect("declaration name");
            let name = names[&id].to_unambiguous_string();
            assert!(roster.insert(name, (kind, index + 1)).is_none());
        };
        for kind in ["axiom", "def", "thm", "opaque", "quot"] {
            if let Some(entry) = record.get(kind) {
                add(entry, kind);
            }
        }
        if let Some(block) = record.get("inductive") {
            for (members, kind) in [
                ("types", "inductive"),
                ("ctors", "constructor"),
                ("recs", "recursor"),
            ] {
                for entry in block[members].as_array().expect("inductive members") {
                    add(entry, kind);
                }
            }
        }
    }
    roster
}

fn ndjson_records(bytes: &str) -> Vec<Value> {
    bytes
        .lines()
        .map(|line| serde_json::from_str(line).expect("NDJSON record"))
        .collect()
}

fn assert_full_replay(root: &Path, filename: &str, roster: &BTreeMap<String, (&str, usize)>) {
    let honest = replay(root, filename, 0);
    assert_eq!(honest["exit"], "accept");
    assert_eq!(honest["declarations"], roster.len());
    assert_eq!(honest["admitted"], roster.len());
    assert_eq!(honest["refused"], 0);
    assert!(honest["first_refusal"].is_null());
    let mut expected = roster.clone();
    for row in honest["records"].as_array().expect("named verdicts") {
        let name = row["name"].as_str().expect("reported name");
        let (kind, line) = expected
            .remove(name)
            .expect("one verdict per exported name");
        assert_eq!(row["kind"], kind);
        assert_eq!(row["line"], line);
        assert_eq!(row["verdict"], "admitted", "{row}");
    }
    assert!(expected.is_empty(), "missing verdicts: {expected:?}");
}

#[test]
fn fresh_replay_admits_every_exported_name_and_refuses_another_theorems_proof() {
    let project = tempfile::tempdir().expect("source project");
    let reader = tempfile::tempdir().expect("standalone replay directory");
    write_project(project.path());
    let path = reader.path().join("honest.ndjson");
    let produced = export(project.path(), "Roundtrip.lean", &path);
    assert!(produced.status.success(), "{produced:?}");
    let bytes = fs::read_to_string(&path).expect("exported NDJSON");
    let mut lines = ndjson_records(&bytes);
    let roster = wire_roster(&lines);
    for (name, kind) in [
        ("ExportChain", "inductive"),
        ("ExportChain.stop", "constructor"),
        ("ExportChain.link", "constructor"),
        ("ExportChain.rec", "recursor"),
        ("ExportChain.casesOn", "def"),
        ("ExportChain.recOn", "def"),
        ("exportCopy", "def"),
        ("exportMeaning", "def"),
        ("exportFirst", "thm"),
        ("exportSecond", "thm"),
    ] {
        assert_eq!(roster.get(name).map(|entry| entry.0), Some(kind), "{name}");
    }
    assert!(
        !roster.contains_key("exportUnused"),
        "unreferenced declaration in a source import"
    );

    assert_full_replay(reader.path(), "honest.ndjson", &roster);

    // Both expressions already exist and were admitted. Use the earlier theorem as donor
    // so its expression index is in scope when the reader reaches the modified theorem.
    let mut theorems = ["exportFirst", "exportSecond"];
    theorems.sort_by_key(|name| roster[*name].1);
    let [donor, target] = theorems;
    let original = &lines[roster[donor].1 - 1]["thm"];
    let proof = original["value"].clone();
    let statement = original["type"].clone();
    let replaced_line = roster[target].1 - 1;
    let subject = &mut lines[replaced_line]["thm"];
    assert_ne!(proof, subject["value"]);
    assert_ne!(statement, subject["type"]);
    subject["value"] = proof;
    let mut corrupted = String::new();
    for (index, line) in bytes.lines().enumerate() {
        if index == replaced_line {
            corrupted.push_str(&lines[index].to_string());
        } else {
            corrupted.push_str(line);
        }
        corrupted.push('\n');
    }
    fs::write(reader.path().join("swapped.ndjson"), corrupted).expect("alter one theorem's proof");
    let bad = replay(reader.path(), "swapped.ndjson", 1);
    assert_eq!(bad["exit"], "reject");
    assert_eq!(bad["declarations"], roster.len());
    assert_eq!(bad["admitted"], roster.len() - 1);
    assert_eq!(bad["refused"], 1);
    let first = &bad["first_refusal"];
    assert_eq!(first["name"], target);
    assert!(
        first["reason"]
            .as_str()
            .expect("kernel refusal")
            .contains("TypeMismatch"),
        "{first}"
    );
    let wrong = bad["records"]
        .as_array()
        .expect("named verdicts")
        .iter()
        .find(|row| row["name"] == target)
        .expect("target verdict");
    assert_eq!(wrong["verdict"], "refused");
    assert_eq!(wrong["reason"], first["reason"]);
}

#[test]
fn an_import_contributes_only_the_eliminator_used_by_the_checked_source() {
    let project = tempfile::tempdir().expect("source project");
    let reader = tempfile::tempdir().expect("standalone replay directory");
    write_project(project.path());
    let path = reader.path().join("reachable.ndjson");
    let produced = export(project.path(), "UseRecOn.lean", &path);
    assert!(produced.status.success(), "{produced:?}");
    let bytes = fs::read_to_string(path).expect("exported NDJSON");
    let roster = wire_roster(&ndjson_records(&bytes));
    let expected = [
        ("ExportChain", "inductive"),
        ("ExportChain.stop", "constructor"),
        ("ExportChain.link", "constructor"),
        ("ExportChain.rec", "recursor"),
        ("ExportChain.recOn", "def"),
        ("useRecOn", "def"),
    ];
    assert_eq!(
        roster.len(),
        expected.len(),
        "complete reachable names: {roster:?}"
    );
    for (name, kind) in expected {
        assert_eq!(roster.get(name).map(|entry| entry.0), Some(kind), "{name}");
    }
    assert_full_replay(reader.path(), "reachable.ndjson", &roster);
}

#[test]
fn a_late_source_error_preserves_the_previous_export() {
    let project = tempfile::tempdir().expect("source project");
    write_project(project.path());
    let source = project.path().join("Roundtrip.lean");
    let mut broken = fs::read_to_string(&source).expect("fixture");
    broken.push_str("\ntheorem exportBroken (p q : Prop) (h : p) : q := h\n");
    fs::write(source, broken).expect("wrong proof after valid declarations");
    let path = project.path().join("existing.ndjson");
    let previous = b"previous export must survive\n";
    fs::write(&path, previous).expect("existing destination");
    let result = export(project.path(), "Roundtrip.lean", &path);
    assert_eq!(result.status.code(), Some(1), "{result:?}");
    assert_eq!(fs::read(&path).expect("preserved destination"), previous);
}
