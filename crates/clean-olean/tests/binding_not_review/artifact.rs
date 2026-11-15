// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
//! Checked artifact transport, with independent serialized type/value identity.
//! This is an untrusted producer; the caller still runs all three kernels.

use super::{data, guards, identity, ROOT};
use serde_json::{json, Value};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::Instant;

const PRODUCER: &str = include_str!(
    "../../../../reports/2026-11-14-extension-binding-not-review/artifact/SlimRoot.lean"
);
const CENSUS: &str = include_str!(
    "../../../../reports/2026-11-14-extension-binding-not-review/artifact/ValueCensus.lean"
);
const IMPORTS: [&str; 6] = [
    "Init.Prelude",
    "Init.Core",
    "Init.Tactics",
    "Init.Data.Int.Basic",
    "Init.Data.Nat.Bitwise.Basic",
    "Init.Data.Nat.Gcd",
];

pub(super) struct Derived {
    pub(super) compiled: PathBuf,
    original: PathBuf,
    original_parts: Vec<PathBuf>,
    derived_parts: Vec<PathBuf>,
}

impl Derived {
    pub(super) fn unchanged(&self) {
        assert_eq!(
            parts(&self.original),
            self.original_parts,
            "original artifact-part census changed"
        );
        assert_eq!(
            parts(&self.compiled),
            self.derived_parts,
            "derived artifact-part census changed"
        );
    }
}

fn parts(directory: &Path) -> Vec<PathBuf> {
    let base = directory.join(format!("{ROOT}.olean"));
    assert!(base.is_file(), "required artifact {}", base.display());
    ["", ".server", ".private"]
        .into_iter()
        .map(|suffix| PathBuf::from(format!("{}{suffix}", base.display())))
        .filter(|path| path.is_file())
        .map(|path| path.canonicalize().expect("artifact part path"))
        .collect()
}

fn bind(value: &Value, path: &Path, book: &mut BTreeMap<PathBuf, String>) {
    let path = path.canonicalize().expect("receipt input path");
    assert_eq!(
        value["path"],
        path.to_string_lossy().as_ref(),
        "receipt physical path"
    );
    let hash = data::file_sha(&path);
    assert_eq!(value["sha256"], hash, "receipt file content");
    if let Some(previous) = book.insert(path, hash.clone()) {
        assert_eq!(previous, hash, "input changed during transport");
    }
}

fn bind_parts(rows: &Value, expected: &[PathBuf], book: &mut BTreeMap<PathBuf, String>) {
    let rows = rows.as_array().expect("artifact part receipts");
    let names: BTreeSet<_> = rows
        .iter()
        .map(|row| data::string(row, "path").to_owned())
        .collect();
    assert_eq!(names.len(), rows.len(), "duplicate artifact part receipt");
    assert_eq!(
        names,
        expected
            .iter()
            .map(|p| p.to_string_lossy().into_owned())
            .collect()
    );
    for path in expected {
        let row = rows
            .iter()
            .find(|row| row["path"] == path.to_string_lossy().as_ref())
            .expect("part receipt");
        bind(row, path, book);
    }
}

fn run(directory: &Path, label: &str, mut command: Command) -> Output {
    let argv: Vec<_> = std::iter::once(command.get_program())
        .chain(command.get_args())
        .map(|value| value.to_string_lossy().into_owned())
        .collect();
    let cwd = command
        .get_current_dir()
        .map(|path| path.to_string_lossy().into_owned());
    let environment: BTreeMap<_, _> = command
        .get_envs()
        .map(|(key, value)| {
            (
                key.to_string_lossy().into_owned(),
                value.map(|v| v.to_string_lossy().into_owned()),
            )
        })
        .collect();
    let started = Instant::now();
    let output = command.output().unwrap_or_else(|error| {
        std::fs::write(
            directory.join(format!("{label}.receipt.json")),
            json!({
                "argv":argv,"spawn_error":error.to_string(),"proof_credit":false
            })
            .to_string(),
        )
        .expect("retain failed spawn");
        panic!("{label} failed to start: {error}");
    });
    std::fs::write(directory.join(format!("{label}.stdout")), &output.stdout)
        .expect("retain stdout");
    std::fs::write(directory.join(format!("{label}.stderr")), &output.stderr)
        .expect("retain stderr");
    std::fs::write(directory.join(format!("{label}.receipt.json")), json!({
        "argv":argv,"cwd":cwd,"environment":environment,
        "exit_code":output.status.code(),"success":output.status.success(),
        "elapsed_ms":started.elapsed().as_millis(),"stdout_sha256":identity::sha(&output.stdout),
        "stderr_sha256":identity::sha(&output.stderr),"proof_credit":false
    }).to_string()).expect("retain process receipt");
    data::command_ok(label, &output);
    output
}

fn lean_command(lean: &Path, source: &Path, cwd: &Path) -> Command {
    let mut command = Command::new(lean);
    command
        .arg("--run")
        .arg(source)
        .current_dir(cwd)
        .env_remove("LEAN_PATH")
        .env_remove("LEAN_SRC_PATH")
        .env("PATH", pinned_path(lean));
    command
}

fn pinned_path(lean: &Path) -> std::ffi::OsString {
    let mut paths = vec![lean.parent().expect("pinned Lean bin").to_path_buf()];
    paths.extend(std::env::split_paths(
        &std::env::var_os("PATH").unwrap_or_default(),
    ));
    std::env::join_paths(paths).expect("pinned Lean PATH")
}

type Rows = BTreeMap<String, Value>;

fn fields(value: &Value, expected: &[&str]) -> Result<(), String> {
    let actual: BTreeSet<_> = value
        .as_object()
        .ok_or("receipt object")?
        .keys()
        .map(String::as_str)
        .collect();
    if actual != expected.iter().copied().collect() {
        return Err("receipt fields".into());
    }
    Ok(())
}

fn name_identity(name: &str) -> Value {
    name.split('.')
        .fold(json!(["anon"]), |parent, part| json!(["str", parent, part]))
}

fn census(text: &str, expected: &BTreeMap<String, String>) -> Result<Rows, String> {
    let mut rows = BTreeMap::new();
    let mut counts = Vec::new();
    for line in text.lines().filter(|line| !line.trim().is_empty()) {
        if let Some(raw) = line.strip_prefix("SLIM_VALUE_ROW ") {
            let row = data::try_parse(raw)?;
            fields(&row, &["declaration", "origin", "identity"])?;
            let name = row["declaration"]
                .as_str()
                .ok_or("declaration name")?
                .to_owned();
            let kind = expected.get(&name).ok_or("foreign declaration")?;
            if row["origin"] != ROOT {
                return Err("foreign origin".into());
            }
            let value = &row["identity"];
            fields(value, &["metadata", "type", "value", "exprs"])?;
            let metadata = &value["metadata"];
            let wanted = if kind == "theorem" {
                vec!["name", "kind", "level_params", "all"]
            } else {
                vec!["name", "kind", "level_params", "all", "hints", "safety"]
            };
            fields(metadata, &wanted)?;
            if metadata["name"] != name_identity(&name) || metadata["kind"] != *kind {
                return Err("compiled metadata identity".into());
            }
            if kind != "theorem" && metadata["safety"] != "safe" {
                return Err("unsafe declaration".into());
            }
            let nodes = value["exprs"].as_array().ok_or("expression DAG")?;
            if nodes.is_empty() {
                return Err("empty expression DAG".into());
            }
            for key in ["type", "value"] {
                if value[key]
                    .as_u64()
                    .is_none_or(|index| index >= nodes.len() as u64)
                {
                    return Err("type/value DAG root".into());
                }
            }
            if !metadata["level_params"].is_array() || !metadata["all"].is_array() {
                return Err("metadata name arrays".into());
            }
            if rows.insert(name, row).is_some() {
                return Err("duplicate declaration".into());
            }
        } else if let Some(raw) = line.strip_prefix("SLIM_VALUE_COUNT ") {
            counts.push(raw.parse::<usize>().map_err(|_| "census count")?);
        } else {
            return Err("unexpected census output".into());
        }
    }
    if expected.len() != 32
        || counts != [32]
        || rows.len() != 32
        || rows.keys().collect::<BTreeSet<_>>() != expected.keys().collect()
    {
        return Err("complete 32-declaration census".into());
    }
    Ok(rows)
}

fn equal(original: &Rows, derived: &Rows) -> Result<(), String> {
    if original.keys().collect::<BTreeSet<_>>() != derived.keys().collect() {
        return Err("serialized declaration set".into());
    }
    for (name, row) in original {
        if identity::canonical(row) != identity::canonical(&derived[name]) {
            return Err(format!("serialized type/value/metadata mismatch: {name}"));
        }
    }
    Ok(())
}

fn comparison_controls(original: &Rows, text: &str, expected: &BTreeMap<String, String>) {
    let first = original.keys().next().expect("actual census");
    for key in ["type", "value"] {
        let mut changed = original.clone();
        let row = &mut changed.get_mut(first).expect("actual row")["identity"];
        let index = row[key].as_u64().expect("actual root");
        assert!(row["exprs"].as_array().expect("DAG").len() > 1);
        row[key] = json!(if index == 0 { 1 } else { 0 });
        assert_eq!(
            equal(original, &changed),
            Err(format!("serialized type/value/metadata mismatch: {first}"))
        );
    }
    let mut changed = original.clone();
    changed.get_mut(first).expect("actual row")["identity"]["metadata"]["level_params"]
        .as_array_mut()
        .expect("actual params")
        .push(name_identity("forgedUniverse"));
    assert!(equal(original, &changed).is_err());
    for field in [1, 2] {
        let mut changed = original.clone();
        let node = changed
            .values_mut()
            .flat_map(|row| row["identity"]["exprs"].as_array_mut().expect("DAG"))
            .find(|node| matches!(node[0].as_str(), Some("lam" | "pi")))
            .expect("actual binder");
        if field == 1 {
            node[1] = name_identity("forgedBinder");
        } else {
            node[2] = json!(if node[2] == "default" {
                "implicit"
            } else {
                "default"
            });
        }
        assert!(
            equal(original, &changed).is_err(),
            "raw binder identity must be retained"
        );
    }
    let first_line = text
        .lines()
        .find(|line| line.starts_with("SLIM_VALUE_ROW "))
        .expect("actual row line");
    assert_eq!(
        census(&format!("{text}\n{first_line}\n"), expected),
        Err("duplicate declaration".into())
    );
    let missing = text
        .lines()
        .filter(|line| *line != first_line)
        .collect::<Vec<_>>()
        .join("\n");
    assert!(census(&missing, expected).is_err());
    assert!(census(
        &text.replace("SLIM_VALUE_COUNT 32", "SLIM_VALUE_COUNT 31"),
        expected
    )
    .is_err());
    assert!(census(&format!("{text}\nSLIM_VALUE_ROW invalid"), expected).is_err());
    let raw = first_line
        .strip_prefix("SLIM_VALUE_ROW ")
        .expect("actual row JSON");
    let duplicate = format!("{{\"declaration\":{},{}", json!(first), &raw[1..]);
    assert!(data::try_parse(&duplicate).is_err(), "duplicate JSON key");
    eprintln!("binding-not artifact controls: changed type/value/params/binder-name/binder-info, missing/duplicate rows/count/malformed/duplicate-key refused");
}

pub(super) fn derive(
    repo: &Path,
    lean: &Path,
    lib: &Path,
    full: &Path,
    manifest: &Value,
    book: &mut BTreeMap<PathBuf, String>,
) -> Derived {
    let tools = repo.join("reports/2026-11-14-extension-binding-not-review/artifact");
    let producer = tools.join("SlimRoot.lean");
    let value_driver = tools.join("ValueCensus.lean");
    for (path, compiled_source) in [(&producer, PRODUCER), (&value_driver, CENSUS)] {
        assert_eq!(
            data::file_sha(path),
            identity::sha(compiled_source.as_bytes()),
            "tool differs from compiled test input"
        );
        book.insert(path.clone(), data::file_sha(path));
    }
    let expected = guards::inventory(manifest).expect("complete source manifest");
    assert_eq!(expected.len(), 32);
    let full = full.canonicalize().expect("full compiled directory");
    let original_parts = parts(&full);
    for path in &original_parts {
        book.insert(path.clone(), data::file_sha(path));
    }
    std::fs::create_dir_all(env!("CARGO_TARGET_TMPDIR")).expect("artifact output parent");
    let retained = tempfile::Builder::new()
        .prefix("binding-not-artifact-")
        .tempdir_in(env!("CARGO_TARGET_TMPDIR"))
        .expect("owned artifact directory")
        .keep();
    eprintln!("binding-not retained transport {}", retained.display());
    let compiled = retained.join("compiled");
    let bin = lean.parent().expect("Lean bin");
    let lean_path = std::env::join_paths([full.as_path(), lib]).expect("original search path");
    let mut checker = Command::new(bin.join("leanchecker"));
    checker
        .args(["--fresh", ROOT])
        .current_dir(&full)
        .env("LEAN_PATH", &lean_path)
        .env_remove("LEAN_SRC_PATH")
        .env("PATH", pinned_path(lean));
    run(&retained, "original-leanchecker", checker);
    let package = repo.join("theories/binding_not_review");
    let mut command = lean_command(lean, &producer, &retained);
    command
        .arg(package.join("manifest.json"))
        .arg(package.join("BindingNotReview.lean"))
        .arg(&full)
        .arg(&compiled)
        .arg(&producer);
    let output = run(&retained, "checked-producer", command);
    let receipt_path = compiled.join("producer-receipt.json");
    let receipt = data::read(&receipt_path);
    let stdout = std::str::from_utf8(&output.stdout)
        .expect("producer UTF8")
        .trim();
    assert_eq!(
        data::parse(
            stdout
                .strip_prefix("SLIM_PRODUCER ")
                .expect("one producer receipt")
        ),
        receipt
    );
    assert_eq!(receipt["schema"], "binding-not-slim-prototype/v1");
    assert_eq!(receipt["proof_credit"], false);
    assert_eq!(receipt["serialized_reload_checked"], false);
    assert_eq!(receipt["in_memory_type_value_metadata_exact"], true);
    assert_eq!(receipt["declaration_count"], 32);
    assert_eq!(receipt["max_rec_depth"], 512);
    assert!(receipt["max_heartbeats"].as_u64().is_some_and(|n| n > 0));
    assert_eq!(receipt["fresh_direct_imports"], json!(IMPORTS));
    bind(&receipt["manifest"], &package.join("manifest.json"), book);
    bind(
        &receipt["logical_source"],
        &package.join("BindingNotReview.lean"),
        book,
    );
    bind(&receipt["producer"], &producer, book);
    bind(&receipt["lean"], lean, book);
    bind(&receipt["sha256_tool"], Path::new("/usr/bin/shasum"), book);
    let derived_parts = parts(&compiled);
    bind_parts(&receipt["original_artifacts"], &original_parts, book);
    bind_parts(&receipt["derived_artifacts"], &derived_parts, book);
    let lib = lib.canonicalize().expect("pinned library path");
    let mut imports = BTreeSet::new();
    for row in receipt["fresh_import_identity"]
        .as_array()
        .expect("fresh import identities")
    {
        assert!(
            imports.insert(identity::canonical(&row["module"])),
            "duplicate imported module"
        );
        let mut paths = BTreeSet::new();
        for part in row["artifacts"].as_array().expect("import artifact parts") {
            let path = PathBuf::from(data::string(part, "path"));
            assert!(
                path.starts_with(&lib) && paths.insert(path.clone()),
                "foreign/duplicate pinned import part"
            );
            bind(part, &path, book);
        }
        assert!(!paths.is_empty());
    }
    assert!(!imports.is_empty());
    // NEW processes: never import both roots of the same name in one process.
    let mut command = lean_command(lean, &value_driver, &retained);
    command.arg(&full);
    let original = run(&retained, "original-values", command);
    let mut command = lean_command(lean, &value_driver, &retained);
    command.arg(&compiled);
    let copied = run(&retained, "derived-values", command);
    let original_text = std::str::from_utf8(&original.stdout).expect("original value census UTF8");
    let copied_text = std::str::from_utf8(&copied.stdout).expect("derived value census UTF8");
    let original_rows =
        census(original_text, &expected).expect("strict original type/value census");
    let copied_rows = census(copied_text, &expected).expect("strict derived type/value census");
    equal(&original_rows, &copied_rows)
        .expect("all serialized type/value/metadata identities exact");
    comparison_controls(&original_rows, original_text, &expected);
    let metadata: BTreeSet<_> = original_rows
        .values()
        .map(|row| identity::canonical(&row["identity"]["metadata"]))
        .collect();
    let receipt_metadata: BTreeSet<_> = receipt["declarations"]
        .as_array()
        .expect("all copied metadata")
        .iter()
        .map(identity::canonical)
        .collect();
    assert_eq!(
        receipt["declarations"].as_array().expect("metadata").len(),
        32
    );
    assert_eq!(metadata.len(), 32);
    assert_eq!(
        metadata, receipt_metadata,
        "actual serialized metadata equals producer receipt"
    );
    std::fs::write(retained.join("comparison.json"), json!({
        "schema":"binding-not-artifact-comparison/v1","declarations":32,
        "original_sha256":identity::sha(&original.stdout),"derived_sha256":identity::sha(&copied.stdout),
        "type_value_metadata_identical":true,"proof_credit":false
    }).to_string()).expect("retain comparison");
    book.insert(receipt_path.clone(), data::file_sha(&receipt_path));
    for item in std::fs::read_dir(&retained).expect("retained transport outputs") {
        let path = item.expect("retained item").path();
        if path.is_file() {
            book.insert(path.clone(), data::file_sha(&path));
        }
    }
    let result = Derived {
        compiled,
        original: full,
        original_parts,
        derived_parts,
    };
    result.unchanged();
    for (path, hash) in book.iter() {
        assert_eq!(
            data::file_sha(path),
            *hash,
            "transport input bookend {}",
            path.display()
        );
    }
    eprintln!("binding-not artifact: all 32 compiled declarations preserved; derived artifact awaits caller's full kernel/pin/negative qualification");
    result
}
