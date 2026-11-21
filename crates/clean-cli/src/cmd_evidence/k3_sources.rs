// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The source-identity portion of the K3 receipt check.

mod imports;

use super::k3_inputs::{canonical_root, find_regular_file};
use super::read_unique_map;
use crate::EvidenceCheckError;
use serde::de::{value::MapAccessDeserializer, MapAccess, Visitor};
use serde::{Deserialize, Deserializer, Serialize};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::fs;
use std::io;
use std::marker::PhantomData;
use std::path::Path;

pub(super) const RECORD: &str = "data/kcheck_coverage.json";
const PACKAGES: &[&str] = &[
    "cic_l",
    "cic_l_model",
    "kcheck_spec",
    "kcheck_labelled",
    "kcheck_run",
];
const PACKAGE_FILES: &[&str] = &[
    "lakefile.toml",
    "lakefile.lean",
    "lean-toolchain",
    "lake-manifest.json",
];
const BUILD_ROOTS: &[&str] = &["KCheckRun", "KCheckRunMain"];
const TOOLCHAIN: &str = "theories/kcheck_run/lean-toolchain";
// This is also the stable reason used by the Python coverage projection.
pub(super) const SOURCES_MOVED: &str = "the Lean sources of the recorded run have moved; re-mint with scripts/kcheck_coverage.py --write";

#[derive(Debug)]
pub(super) struct MovedSources {
    count: usize,
    first: String,
}

impl From<MovedSources> for EvidenceCheckError {
    fn from(moved: MovedSources) -> Self {
        Self::Unavailable(format!(
            "{SOURCES_MOVED}\n{} moved, first {}",
            moved.count, moved.first
        ))
    }
}

#[derive(Debug)]
pub(super) enum SourcePinsError {
    Moved(MovedSources),
    Check(EvidenceCheckError),
}

impl From<EvidenceCheckError> for SourcePinsError {
    fn from(error: EvidenceCheckError) -> Self {
        Self::Check(error)
    }
}

impl From<SourcePinsError> for EvidenceCheckError {
    fn from(error: SourcePinsError) -> Self {
        match error {
            SourcePinsError::Moved(moved) => moved.into(),
            SourcePinsError::Check(error) => error,
        }
    }
}

#[derive(Deserialize)]
#[serde(transparent)]
struct SourceReceipt(#[serde(deserialize_with = "read_object")] SourceRecord);

#[derive(Deserialize)]
struct SourceRecord {
    schema: String,
    #[serde(deserialize_with = "read_source_digests")]
    sources: BTreeMap<String, String>,
    #[serde(deserialize_with = "read_object")]
    run: RunFacts,
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub(super) struct RunFacts {
    pub(super) command: String,
    pub(super) executable_sha256: String,
    pub(super) lean_toolchain: String,
    pub(super) lean_version: String,
}

// Derived structs also accept positional arrays. A K3 receipt uses named fields.
pub(super) fn read_object<'de, D, T>(input: D) -> Result<T, D::Error>
where
    D: Deserializer<'de>,
    T: Deserialize<'de>,
{
    struct ObjectVisitor<T>(PhantomData<T>);

    impl<'de, T: Deserialize<'de>> Visitor<'de> for ObjectVisitor<T> {
        type Value = T;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("a JSON object")
        }

        fn visit_map<A: MapAccess<'de>>(self, map: A) -> Result<T, A::Error> {
            T::deserialize(MapAccessDeserializer::new(map))
        }
    }

    input.deserialize_map(ObjectVisitor(PhantomData))
}

pub(super) fn read_source_digests<'de, D: Deserializer<'de>>(
    input: D,
) -> Result<BTreeMap<String, String>, D::Error> {
    read_unique_map(input, "source path")
}

fn sha256_spelling(digest: &str) -> bool {
    digest.len() == 64
        && digest
            .bytes()
            .all(|ch| ch.is_ascii_digit() || (b'a'..=b'f').contains(&ch))
}

fn source_path(relative: &str) -> bool {
    let Some(tail) = relative.strip_prefix("theories/") else {
        return false;
    };
    tail.split('/').all(|part| {
        !part.is_empty()
            && !part.ends_with('.')
            && part
                .bytes()
                .all(|ch| ch.is_ascii_alphanumeric() || matches!(ch, b'.' | b'_' | b'-' | b'\''))
    })
}

pub(super) fn validate_source_header(
    schema: &str,
    sources: &BTreeMap<String, String>,
    run: &RunFacts,
) -> Result<(), EvidenceCheckError> {
    if schema != "clean.kcheck_coverage.v1" {
        return Err(EvidenceCheckError::Invalid(format!(
            "{RECORD} has unsupported schema {schema:?}"
        )));
    }
    for (relative, digest) in sources {
        if !source_path(relative) {
            return Err(EvidenceCheckError::Invalid(format!(
                "{RECORD} `sources` names {relative:?}, which is not a normalized path under theories/"
            )));
        }
        if !sha256_spelling(digest) {
            return Err(EvidenceCheckError::Invalid(format!(
                "{RECORD} `sources` gives {relative} no lowercase sha256"
            )));
        }
    }
    if run.command.is_empty() || run.lean_version.is_empty() || run.lean_toolchain.is_empty() {
        return Err(EvidenceCheckError::Invalid(format!(
            "{RECORD} requires the four recorded run facts"
        )));
    }
    if !sha256_spelling(&run.executable_sha256) {
        return Err(EvidenceCheckError::Invalid(format!(
            "{RECORD} gives the recorded executable no lowercase sha256"
        )));
    }
    Ok(())
}

fn sha256_bytes(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn verify_listed_sources<'a>(
    root: &Path,
    sources: &'a BTreeMap<String, String>,
) -> Result<BTreeMap<&'a str, Vec<u8>>, SourcePinsError> {
    let mut observed = BTreeMap::new();
    let mut moved = Vec::new();
    for (relative, expected) in sources {
        let Some(path) = find_regular_file(root, relative)? else {
            moved.push(relative);
            continue;
        };
        let bytes = match fs::read(&path) {
            Ok(bytes) => bytes,
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                moved.push(relative);
                continue;
            }
            Err(error) => {
                return Err(
                    EvidenceCheckError::Unavailable(format!("{}: {error}", path.display())).into(),
                )
            }
        };
        if sha256_bytes(&bytes) == *expected {
            observed.insert(relative.as_str(), bytes);
        } else {
            moved.push(relative);
        }
    }
    if let Some(first) = moved.first() {
        return Err(SourcePinsError::Moved(MovedSources {
            count: moved.len(),
            first: first.to_string(),
        }));
    }
    Ok(observed)
}

fn locate_module(root: &Path, module: &str) -> Result<Option<String>, EvidenceCheckError> {
    let tail = module.replace('.', "/");
    let mut hits = Vec::new();
    for package in PACKAGES {
        let relative = format!("theories/{package}/{tail}.lean");
        if find_regular_file(root, &relative)?.is_some() {
            hits.push(relative);
        }
    }
    if hits.len() > 1 {
        return Err(EvidenceCheckError::Invalid(format!(
            "module {module} is in more than one package: {hits:?}"
        )));
    }
    Ok(hits.pop())
}

// Match Python's str.strip() and regex whitespace on the same UTF-8 text.
pub(super) fn python_whitespace(ch: char) -> bool {
    ch.is_whitespace() || matches!(ch, '\u{1c}'..='\u{1f}')
}

fn source_text<'a>(bytes: &'a [u8], relative: &str) -> Result<&'a str, EvidenceCheckError> {
    std::str::from_utf8(bytes)
        .map_err(|error| EvidenceCheckError::Invalid(format!("{relative} is not UTF-8: {error}")))
}

fn required_sources(
    root: &Path,
    observed: &BTreeMap<&str, Vec<u8>>,
) -> Result<BTreeSet<String>, EvidenceCheckError> {
    let mut seen = BTreeSet::new();
    let mut pending: Vec<_> = BUILD_ROOTS
        .iter()
        .map(|module| (*module).to_owned())
        .collect();
    while let Some(module) = pending.pop() {
        let Some(relative) = locate_module(root, &module)? else {
            // An unresolved non-root name belongs to the recorded toolchain.
            continue;
        };
        if !seen.insert(relative.clone()) {
            continue;
        }
        let unlisted;
        let bytes = if let Some(bytes) = observed.get(relative.as_str()) {
            bytes
        } else {
            unlisted = fs::read(root.join(&relative))
                .map_err(|error| EvidenceCheckError::Unavailable(format!("{relative}: {error}")))?;
            &unlisted
        };
        pending.extend(imports::imports(source_text(bytes, &relative)?, &relative)?);
    }
    for module in BUILD_ROOTS {
        if !locate_module(root, module)?.is_some_and(|relative| seen.contains(&relative)) {
            return Err(EvidenceCheckError::Invalid(format!(
                "theories/kcheck_run has no module {module}"
            )));
        }
    }
    for package in PACKAGES {
        for file in PACKAGE_FILES {
            let relative = format!("theories/{package}/{file}");
            if find_regular_file(root, &relative)?.is_some() {
                seen.insert(relative);
            }
        }
    }
    Ok(seen)
}

/// Verify the already validated source pins under a canonical repository root.
pub(super) fn verify_source_pins(
    root: &Path,
    sources: &BTreeMap<String, String>,
    run: &RunFacts,
) -> Result<usize, SourcePinsError> {
    let observed = verify_listed_sources(root, sources)?;
    let required = required_sources(root, &observed)?;
    let listed: BTreeSet<_> = sources.keys().map(String::as_str).collect();
    let required: BTreeSet<_> = required.iter().map(String::as_str).collect();
    let missing: Vec<_> = required.difference(&listed).collect();
    if let Some(first) = missing.first() {
        return Err(EvidenceCheckError::Invalid(format!(
            "{RECORD} `sources` omits {} file(s) the executable is built from (first: {first})",
            missing.len()
        ))
        .into());
    }
    let extra: Vec<_> = listed.difference(&required).collect();
    if let Some(first) = extra.first() {
        return Err(EvidenceCheckError::Invalid(format!(
            "{RECORD} `sources` lists {} file(s) the executable is not built from (first: {first})",
            extra.len()
        ))
        .into());
    }
    let bytes = observed.get(TOOLCHAIN).ok_or_else(|| {
        EvidenceCheckError::Invalid(format!("{TOOLCHAIN} is absent from the executable sources"))
    })?;
    let toolchain = source_text(bytes, TOOLCHAIN)?.trim_matches(python_whitespace);
    if run.lean_toolchain != toolchain {
        return Err(EvidenceCheckError::Invalid(format!(
            "{RECORD} names toolchain {:?}, but {TOOLCHAIN} pins {toolchain:?}",
            run.lean_toolchain
        ))
        .into());
    }
    Ok(observed.len())
}

fn source_identity(root: &Path) -> Result<(usize, String), EvidenceCheckError> {
    let root = canonical_root(root)?;
    let record_path = find_regular_file(&root, RECORD)?
        .ok_or_else(|| EvidenceCheckError::Unavailable(format!("{RECORD} does not exist")))?;
    let bytes = fs::read(&record_path).map_err(|error| {
        EvidenceCheckError::Unavailable(format!("{}: {error}", record_path.display()))
    })?;
    let SourceReceipt(record) = serde_json::from_str(source_text(&bytes, RECORD)?)
        .map_err(|error| EvidenceCheckError::Invalid(format!("{RECORD}: {error}")))?;
    validate_source_header(&record.schema, &record.sources, &record.run)?;
    let files = verify_source_pins(&root, &record.sources, &record.run)?;
    Ok((files, record.run.lean_toolchain))
}

pub(super) fn run(root: &Path) -> Result<(), EvidenceCheckError> {
    let (files, toolchain) = source_identity(root)?;
    println!("K3 source identity matches {files} files and Lean toolchain {toolchain:?}");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::{json, Value};

    const MAIN: &str = "theories/kcheck_run/KCheckRunMain.lean";
    const LIBRARY: &str = "theories/kcheck_run/KCheckRun.lean";
    const BRIDGE: &str = "theories/kcheck_labelled/KCheck/Bridge.lean";
    const UNREACHED: &str = "theories/kcheck_labelled/KCheck/Unused.lean";
    const PIN: &str = "leanprover/lean4:v0.0.0-test";

    fn write(root: &Path, name: &str, contents: &str) {
        let path = root.join(name);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, contents).unwrap();
    }

    fn fixture() -> (tempfile::TempDir, Value) {
        let root = tempfile::tempdir().unwrap();
        let files = [
            (MAIN, "import KCheckRun\n"),
            (
                LIBRARY,
                "private meta import all KCheck.Bridge\nimport Init.NotationExtra\n",
            ),
            (
                BRIDGE,
                "prelude\n/- import KCheck.Unused -/\ndef note := \"\nimport KCheck.Unused\"\n",
            ),
            (TOOLCHAIN, "leanprover/lean4:v0.0.0-test\n"),
            ("theories/cic_l/lakefile.toml", "name = \"cic_l\"\n"),
        ];
        let mut sources = BTreeMap::new();
        for (name, body) in files {
            write(root.path(), name, body);
            sources.insert(name, sha256_bytes(body.as_bytes()));
        }
        write(root.path(), UNREACHED, "prelude\n");
        let record = json!({
            "schema": "clean.kcheck_coverage.v1",
            "sources": sources,
            "run": {"command": "example", "executable_sha256": "0".repeat(64),
                    "lean_toolchain": PIN, "lean_version": "example"}
        });
        write(root.path(), RECORD, &record.to_string());
        (root, record)
    }

    fn invalid(root: &Path, expected: &str) {
        match source_identity(root) {
            Err(EvidenceCheckError::Invalid(reason)) => {
                assert!(reason.contains(expected), "{reason}")
            }
            other => panic!("expected invalid source record: {other:?}"),
        }
    }

    #[test]
    fn matches_the_exact_closure_and_ignores_unreachable_modules() {
        let (root, mut record) = fixture();
        assert_eq!(source_identity(root.path()).unwrap(), (5, PIN.to_owned()));
        write(root.path(), UNREACHED, "import Missing.External\n");
        assert_eq!(source_identity(root.path()).unwrap().0, 5);
        record["sources"].as_object_mut().unwrap().remove(BRIDGE);
        write(root.path(), RECORD, &record.to_string());
        invalid(root.path(), "omits 1 file(s)");
    }

    #[test]
    fn moved_listed_bytes_precede_missing_closure_and_wrong_toolchain() {
        let (root, mut record) = fixture();
        record["run"]["lean_toolchain"] = json!("different-pin");
        write(root.path(), RECORD, &record.to_string());
        invalid(root.path(), "pins");
        let SourceReceipt(receipt) = serde_json::from_str(&record.to_string()).unwrap();
        for removed in [false, true] {
            if removed {
                fs::remove_file(root.path().join(MAIN)).unwrap();
            } else {
                write(root.path(), MAIN, "-- edited\nimport KCheckRun\n");
            }
            let error =
                verify_source_pins(root.path(), &receipt.sources, &receipt.run).unwrap_err();
            assert!(matches!(
                &error,
                SourcePinsError::Moved(moved) if moved.count == 1 && moved.first == MAIN
            ));
            assert!(
                matches!(EvidenceCheckError::from(error), EvidenceCheckError::Unavailable(reason)
                    if reason == format!("{SOURCES_MOVED}\n1 moved, first {MAIN}"))
            );
        }
    }

    #[test]
    fn refuses_duplicate_modules_and_extra_build_files() {
        let (root, _) = fixture();
        let second_module = "theories/kcheck_spec/KCheck/Bridge.lean";
        write(root.path(), second_module, "prelude\n");
        invalid(root.path(), "more than one package");
        fs::remove_file(root.path().join(second_module)).unwrap();
        write(
            root.path(),
            "theories/kcheck_run/lakefile.lean",
            "-- alternate\n",
        );
        invalid(root.path(), "omits 1 file(s)");
    }

    #[test]
    fn requires_objects_and_the_literal_schema() {
        let (root, mut record) = fixture();
        let run_array = json!(["example", "0".repeat(64), PIN, "example"]);
        let receipt_array = json!([record["schema"], record["sources"], run_array]);
        write(root.path(), RECORD, &receipt_array.to_string());
        invalid(root.path(), "a JSON object");
        record["run"] = run_array;
        write(root.path(), RECORD, &record.to_string());
        invalid(root.path(), "a JSON object");

        let (root, mut record) = fixture();
        record["schema"] = json!({"clean.kcheck_coverage.v1": null});
        write(root.path(), RECORD, &record.to_string());
        invalid(root.path(), "expected a string");
        record["schema"] = json!("clean.kcheck_coverage.v2");
        write(root.path(), RECORD, &record.to_string());
        invalid(root.path(), "unsupported schema");

        let (root, record) = fixture();
        let mut invalid_utf8 = record.to_string().into_bytes();
        invalid_utf8.pop();
        invalid_utf8.extend_from_slice(b",\"unread_packet_field\":\"\xff\"}");
        fs::write(root.path().join(RECORD), invalid_utf8).unwrap();
        invalid(root.path(), "is not UTF-8");
    }

    #[test]
    fn refuses_unsafe_paths_and_invalid_digests_before_source_reads() {
        let (root, record) = fixture();
        fs::remove_file(root.path().join(MAIN)).unwrap();
        for unsafe_path in [
            "theories/../escape.lean",
            "theories/./x",
            "theories//x",
            "theories/C:x",
            "theories/a\\b",
            "theories/trailing.",
        ] {
            let mut invalid_record = record.clone();
            invalid_record["sources"][unsafe_path] = json!("0".repeat(64));
            write(root.path(), RECORD, &invalid_record.to_string());
            invalid(root.path(), "not a normalized path under theories/");
        }
        let mut invalid_record = record;
        invalid_record["sources"][MAIN] = json!("F".repeat(64));
        write(root.path(), RECORD, &invalid_record.to_string());
        invalid(root.path(), "no lowercase sha256");
    }

    #[cfg(unix)]
    #[test]
    fn refuses_links_in_source_and_record_parents() {
        let (root, _) = fixture();
        let outside = tempfile::tempdir().unwrap();
        for parent in ["data", "theories/kcheck_run"] {
            let directory = root.path().join(parent);
            let saved = directory.with_extension("saved");
            fs::rename(&directory, &saved).unwrap();
            std::os::unix::fs::symlink(outside.path(), &directory).unwrap();
            invalid(root.path(), "symbolic link");
            fs::remove_file(&directory).unwrap();
            fs::rename(saved, directory).unwrap();
        }
    }
}
