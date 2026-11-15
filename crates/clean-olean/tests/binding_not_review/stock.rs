// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
//! Existing hash-qualified STOCK EXCEPTION binary only. Never build a checker.
use super::{data, identity};
use clean_kernel::Name;
use clean_olean::ndjson::ExportWriteSummary;
use serde_json::{json, Value};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const BINARY_SHA: &str = "dbb08c48e43294221ab46faba9bed63962987672511cf94747a9e9a4b0fceee7";
const INPUT_SHA: &str = "5f839c14fb0fdd1869ca74ea8543842914c81b3349a6fdf5b523afa20ed73257";

pub(super) struct Stock {
    binary: PathBuf,
    inputs: BTreeMap<String, String>,
}
impl Stock {
    pub(super) fn existing(repo: &Path) -> Self {
        let path = repo.join("reports/self-proof-ck0-shared-2026-11-14/stock-build-inputs.json");
        assert_eq!(
            data::file_sha(&path),
            INPUT_SHA,
            "qualified stock source manifest"
        );
        let inputs: BTreeMap<String, String> =
            serde_json::from_value(data::read(&path)).expect("stock input hashes");
        assert_eq!(
            inputs.len(),
            164,
            "exact historical stock build input census"
        );
        let tracked = Command::new("git")
            .args(["ls-files", "-z", "--", "crates/clean-ck0"])
            .current_dir(repo)
            .output()
            .expect("tracked ck0 input census");
        assert!(tracked.status.success());
        let mut actual: BTreeSet<String> = tracked
            .stdout
            .split(|c| *c == 0)
            .filter(|s| !s.is_empty())
            .map(|s| String::from_utf8(s.to_vec()).expect("source path UTF8"))
            // Match the authoritative receipt.py source census exactly.
            // README, Lean fixtures and sidecars were never build inputs.
            .filter(|s| {
                matches!(
                    Path::new(s).extension().and_then(|x| x.to_str()),
                    Some("rs" | "toml" | "ndjson")
                )
            })
            .collect();
        actual.extend(
            [
                ".cargo/config.toml",
                "Cargo.lock",
                "Cargo.toml",
                "rust-toolchain.toml",
            ]
            .map(str::to_owned),
        );
        assert_eq!(
            actual,
            inputs.keys().cloned().collect(),
            "no omitted/added stock build inputs"
        );
        let binary =
            PathBuf::from(std::env::var_os("HOME").expect("HOME for hash-qualified checker cache"))
                .join(".cache/clean-kstar/sha256")
                .join(BINARY_SHA)
                .join("ck0-replay");
        let this = Self { binary, inputs };
        this.unchanged(repo);
        this
    }
    pub(super) fn unchanged(&self, repo: &Path) {
        assert_eq!(
            data::file_sha(&self.binary),
            BINARY_SHA,
            "existing stock checker bytes"
        );
        for (p, h) in &self.inputs {
            assert_eq!(data::file_sha(&repo.join(p)), *h, "stock input {p}");
        }
    }
    fn run(&self, path: &Path, args: &[String]) -> Output {
        assert_eq!(data::file_sha(&self.binary), BINARY_SHA);
        eprintln!(
            "binding-not stock binary={} sha256={BINARY_SHA} export={} args={args:?}",
            self.binary.display(),
            path.display()
        );
        Command::new(&self.binary)
            .arg(path)
            .args(args)
            .output()
            .expect("existing stock ck0; no availability skip or fallback build")
    }
    pub(super) fn replay(&self, path: &Path, summary: &ExportWriteSummary, own: &BTreeSet<Name>) {
        let out = self.run(path, &[]);
        data::command_ok("binding-not stock full export", &out);
        checked_rows(&out, summary, own, false);
    }
    pub(super) fn target(
        &self,
        path: &Path,
        summary: &ExportWriteSummary,
        own: &BTreeSet<Name>,
        name: &Name,
        pin: &str,
        axioms: &BTreeSet<String>,
    ) {
        let args = vec![
            "--target-json".into(),
            identity::name_json(name).to_string(),
            "--statement-sha256".into(),
            pin.into(),
        ];
        let out = self.run(path, &args);
        data::command_ok("binding-not stock statement target", &out);
        let rows = checked_rows(&out, summary, own, true);
        let target = rows
            .iter()
            .find(|v| v["kind"] == "target")
            .expect("target verdict");
        assert_eq!(target["name"], identity::name_json(name));
        assert_eq!(target["statement_sha256"], pin);
        assert_eq!(target["matched"], true);
        assert_eq!(
            shown_names(&target["axioms"]),
            *axioms,
            "stock target exact axiom closure"
        );
    }
    pub(super) fn wrong_pin(&self, path: &Path, name: &Name, pin: &str) {
        let wrong = format!(
            "{}{}",
            if pin.starts_with('0') { '1' } else { '0' },
            &pin[1..]
        );
        let out = self.run(
            path,
            &[
                "--target-json".into(),
                identity::name_json(name).to_string(),
                "--statement-sha256".into(),
                wrong,
            ],
        );
        eprintln!(
            "binding-not stock wrong pin status={} stderr={}",
            out.status,
            String::from_utf8_lossy(&out.stderr)
        );
        assert_eq!(out.status.code(), Some(2));
        assert!(out.stdout.is_empty());
        let refusal = data::parse(
            std::str::from_utf8(&out.stderr)
                .expect("stock refusal UTF8")
                .trim(),
        );
        assert_eq!(refusal["kind"], "export-refused");
        assert_eq!(refusal["reason"], "target-policy");
        assert!(data::string(&refusal, "detail").contains("statement pin mismatch"));
    }
    pub(super) fn false_statement(&self, path: &Path, bytes: &[u8], name: &Name) {
        let forged = forge_false(bytes, name);
        let mutant = path.with_file_name("binding-not-actual-proof-at-False.ndjson");
        std::fs::write(&mutant, &forged).expect("write actual proof/False mutant");
        let out = self.run(&mutant, &[]);
        eprintln!(
            "binding-not stock actual-proof/False mutant sha256={} status={}\n{}\n{}",
            identity::sha(&forged),
            out.status,
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        assert_eq!(
            out.status.code(),
            Some(1),
            "genuine kernel refusal, not parser/availability failure"
        );
        assert!(
            out.stderr.is_empty(),
            "export parser error cannot count as semantic refusal"
        );
        let rows = parse_rows(&out);
        let target: Vec<_> = rows
            .iter()
            .filter(|r| r["kind"] == "declaration" && r["name"] == identity::name_json(name))
            .collect();
        assert_eq!(target.len(), 1);
        assert_eq!(target[0]["accepted"], false);
        assert_eq!(target[0]["reason"], "type-check");
        assert!(data::string(target[0], "detail").contains("type mismatch"));
        let coverage: Vec<_> = rows.iter().filter(|r| r["kind"] == "coverage").collect();
        assert_eq!(coverage.len(), 1);
        validate_coverage(&rows);
        assert!(
            coverage[0]["refused"]["type-check"]
                .as_u64()
                .expect("type-check refusal count")
                > 0
        );
    }
}

fn parse_rows(out: &Output) -> Vec<Value> {
    std::str::from_utf8(&out.stdout)
        .expect("stock JSON UTF8")
        .lines()
        .map(data::parse)
        .collect()
}
fn shown_names(v: &Value) -> BTreeSet<String> {
    v.as_array()
        .expect("structured axiom names")
        .iter()
        .map(|n| {
            n.as_array()
                .expect("name components")
                .iter()
                .map(|p| {
                    let fields = data::object(p);
                    assert_eq!(fields.len(), 1);
                    if let Some(s) = p["str"].as_str() {
                        s.to_owned()
                    } else {
                        p["num"]
                            .as_u64()
                            .expect("numeric name component")
                            .to_string()
                    }
                })
                .collect::<Vec<_>>()
                .join(".")
        })
        .collect()
}
fn validate_coverage(rows: &[Value]) {
    let declarations: Vec<_> = rows.iter().filter(|r| r["kind"] == "declaration").collect();
    let coverage: Vec<_> = rows.iter().filter(|r| r["kind"] == "coverage").collect();
    assert_eq!(coverage.len(), 1);
    let mut reasons = BTreeMap::<String, u64>::new();
    let mut accepted = 0u64;
    for row in &declarations {
        if row["accepted"].as_bool().expect("accepted boolean") {
            accepted += 1;
        } else {
            *reasons
                .entry(data::string(row, "reason").to_owned())
                .or_default() += 1;
        }
    }
    assert_eq!(
        coverage[0]["refused"],
        json!(reasons),
        "actual reason-count map"
    );
    assert_eq!(coverage[0]["accepted"], json!(accepted));
    assert_eq!(coverage[0]["total"], json!(declarations.len()));
    assert_eq!(
        accepted + reasons.values().sum::<u64>(),
        declarations.len() as u64
    );
}

fn checked_rows(
    out: &Output,
    summary: &ExportWriteSummary,
    own: &BTreeSet<Name>,
    target: bool,
) -> Vec<Value> {
    let rows = parse_rows(out);
    let mut declarations = BTreeSet::new();
    let mut coverage = Vec::new();
    let mut targets = 0;
    for row in &rows {
        match data::string(row, "kind") {
            "declaration" => {
                assert_eq!(row["accepted"], true, "stock refused {row}");
                assert!(
                    declarations.insert(identity::canonical(&row["name"])),
                    "duplicate stock declaration"
                );
            }
            "coverage" => coverage.push(row),
            "target" => targets += 1,
            other => panic!("unexpected stock row {other}"),
        }
    }
    assert_eq!(targets, usize::from(target));
    assert_eq!(coverage.len(), 1);
    validate_coverage(&rows);
    assert!(data::object(&coverage[0]["refused"]).is_empty());
    assert_eq!(
        coverage[0]["total"].as_u64(),
        Some(summary.declarations as u64)
    );
    assert_eq!(coverage[0]["accepted"], coverage[0]["total"]);
    assert_eq!(declarations.len(), summary.declarations);
    for name in own {
        assert!(
            declarations.contains(&identity::canonical(&identity::name_json(name))),
            "stock omitted {name}"
        );
    }
    let allowed: BTreeSet<_> = ["propext", "Quot.sound", "Classical.choice"]
        .map(str::to_owned)
        .into();
    assert!(shown_names(&coverage[0]["axioms"]).is_subset(&allowed));
    rows
}

/// Add a fresh False constant-expression row and change only the actual
/// target theorem's type reference. All original expression/proof rows stay
/// intact. The stock reader accepts nonmonotone, unique table indices.
fn forge_false(bytes: &[u8], target: &Name) -> Vec<u8> {
    let mut rows: Vec<Value> = std::str::from_utf8(bytes)
        .expect("export UTF8")
        .lines()
        .map(data::parse)
        .collect();
    let mut names: BTreeMap<u64, Value> = [(0, json!([]))].into();
    let mut false_name = None;
    let mut target_name = None;
    for row in &rows {
        if let Some(id) = row["in"].as_u64() {
            let (parent, part) = if !row["str"].is_null() {
                (
                    row["str"]["pre"].as_u64().expect("name parent"),
                    json!({"str":row["str"]["str"]}),
                )
            } else {
                (
                    row["num"]["pre"].as_u64().expect("name parent"),
                    json!({"num":row["num"]["i"]}),
                )
            };
            let mut parts = names[&parent].as_array().expect("name spine").clone();
            parts.push(part);
            let full = json!(parts);
            if full == identity::name_json(&Name::from_string("False")) {
                false_name = Some(id);
            }
            if full == identity::name_json(target) {
                target_name = Some(id);
            }
            assert!(names.insert(id, full).is_none());
        }
    }
    let false_name = false_name.expect("honest production export includes False control root");
    let target_name = target_name.expect("actual theorem name");
    let thms: Vec<_> = rows
        .iter()
        .enumerate()
        .filter(|(_, r)| r["thm"]["name"].as_u64() == Some(target_name))
        .collect();
    assert_eq!(thms.len(), 1);
    let (thm_at, thm) = thms[0];
    let proof = thm["thm"]["value"].clone();
    let old_type = thm["thm"]["type"].clone();
    assert!(
        rows[..thm_at].iter().any(|r| r["inductive"]["types"]
            .as_array()
            .is_some_and(|ds| ds.iter().any(|d| d["name"].as_u64() == Some(false_name)))),
        "False declared before actual target theorem"
    );
    let fresh = rows
        .iter()
        .filter_map(|r| r["ie"].as_u64())
        .max()
        .expect("honest expression table")
        .checked_add(1)
        .expect("fresh expression index");
    rows[thm_at]["thm"]["type"] = json!(fresh);
    assert_ne!(rows[thm_at]["thm"]["type"], old_type);
    assert_eq!(rows[thm_at]["thm"]["value"], proof, "actual proof retained");
    rows.insert(
        thm_at,
        json!({"ie":fresh,"const":{"name":false_name,"us":[]}}),
    );
    let mut out = rows
        .iter()
        .map(|r| serde_json::to_string(r).expect("mutant JSON"))
        .collect::<Vec<_>>()
        .join("\n")
        .into_bytes();
    out.push(b'\n');
    out
}
