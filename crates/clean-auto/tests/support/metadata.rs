// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Resolve API-probe metadata from the test's exact Cargo dependency graph.
//! No newest-file selection: another build's metadata must not satisfy a probe.

use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

pub struct Metadata {
    pub artifact: PathBuf,
    search_paths: BTreeSet<PathBuf>,
}

impl Metadata {
    pub fn configure(&self, command: &mut Command) {
        for path in &self.search_paths {
            command
                .arg("-L")
                .arg(format!("dependency={}", path.display()));
        }
    }
}

struct Unit {
    compiler: u64,
    fingerprint: u64,
    crate_name: String,
    output: PathBuf,
    artifact_hash: String,
    dependencies: Vec<(String, u64)>,
}

fn dependencies(value: &Value) -> Vec<(String, u64)> {
    value["deps"]
        .as_array()
        .expect("Cargo fingerprint must enumerate dependencies")
        .iter()
        .map(|dependency| {
            (
                dependency[1]
                    .as_str()
                    .expect("Cargo dependency name")
                    .to_owned(),
                dependency[3]
                    .as_u64()
                    .expect("Cargo dependency fingerprint"),
            )
        })
        .collect()
}

fn read_json(path: &Path) -> Value {
    serde_json::from_slice(&fs::read(path).expect("read Cargo fingerprint"))
        .expect("parse Cargo fingerprint")
}

fn load_libraries(directory: &Path, output: &Path, artifact_hash: &str) -> Vec<Unit> {
    fs::read_dir(directory)
        .expect("read Cargo fingerprint directory")
        .map(|entry| entry.expect("read Cargo fingerprint entry").path())
        .filter_map(|path| {
            let name = path.file_name()?.to_str()?;
            let crate_name = name.strip_prefix("lib-")?.strip_suffix(".json")?.to_owned();
            let value = read_json(&path);
            let digest = fs::read_to_string(path.with_extension("")).expect("read Cargo unit hash");
            let digest = digest.trim();
            assert_eq!(digest.len(), 16, "Cargo unit hash must be eight bytes");
            let mut bytes = [0; 8];
            for (index, byte) in bytes.iter_mut().enumerate() {
                *byte = u8::from_str_radix(&digest[index * 2..index * 2 + 2], 16)
                    .expect("Cargo unit hash must be hex");
            }
            Some(Unit {
                compiler: value["rustc"].as_u64().expect("Cargo compiler identity"),
                fingerprint: u64::from_le_bytes(bytes),
                crate_name,
                output: output.to_path_buf(),
                artifact_hash: artifact_hash.to_owned(),
                dependencies: dependencies(&value),
            })
        })
        .collect()
}

fn directories(path: &Path) -> Vec<PathBuf> {
    fs::read_dir(path)
        .expect("read Cargo unit directory")
        .map(|entry| entry.expect("read Cargo unit entry").path())
        .filter(|path| path.is_dir())
        .collect()
}

pub fn clean_auto() -> Metadata {
    let executable = std::env::current_exe().expect("API test executable path");
    for_executable(&executable)
}

pub fn for_executable(executable: &Path) -> Metadata {
    let directory = executable.parent().expect("API test executable directory");
    let file_name = executable
        .file_stem()
        .and_then(|name| name.to_str())
        .expect("API test name");
    let (test_name, test_hash) = file_name
        .rsplit_once('-')
        .expect("Cargo test artifact hash");
    let (profile, test_fingerprint, modern) = if directory.file_name().is_some_and(|n| n == "out") {
        let unit = directory.parent().expect("Cargo isolated test unit");
        assert_eq!(unit.file_name().and_then(|n| n.to_str()), Some(test_hash));
        let package = unit.parent().expect("Cargo isolated package");
        let build = package.parent().expect("Cargo isolated build directory");
        assert_eq!(build.file_name().and_then(|n| n.to_str()), Some("build"));
        (
            build.parent().expect("Cargo profile").to_path_buf(),
            unit.join("fingerprint")
                .join(format!("test-integration-test-{test_name}.json")),
            true,
        )
    } else {
        assert_eq!(directory.file_name().and_then(|n| n.to_str()), Some("deps"));
        let profile = directory.parent().expect("Cargo profile").to_path_buf();
        let fingerprint = profile
            .join(".fingerprint")
            .join(format!("{}-{test_hash}", env!("CARGO_PKG_NAME")))
            .join(format!("test-integration-test-{test_name}.json"));
        (profile, fingerprint, false)
    };
    let test = read_json(&test_fingerprint);
    let compiler = test["rustc"].as_u64().expect("test compiler identity");
    let root = dependencies(&test)
        .into_iter()
        .find(|(name, _)| name == "clean_auto")
        .expect("the API test must depend on clean_auto");
    let mut libraries = Vec::new();
    if modern {
        for package in directories(&profile.join("build")) {
            for unit in directories(&package) {
                let fingerprint = unit.join("fingerprint");
                if fingerprint.is_dir() {
                    libraries.extend(load_libraries(
                        &fingerprint,
                        &unit.join("out"),
                        unit.file_name()
                            .and_then(|name| name.to_str())
                            .expect("unit hash"),
                    ));
                }
            }
        }
    } else {
        for unit in directories(&profile.join(".fingerprint")) {
            let (_, hash) = unit
                .file_name()
                .and_then(|name| name.to_str())
                .expect("Cargo unit name")
                .rsplit_once('-')
                .expect("Cargo unit hash");
            libraries.extend(load_libraries(&unit, &profile.join("deps"), hash));
        }
    }
    // Cargo records a dependency's local alias, which can differ from its
    // library target name (`libc_errno` / `errno`, for example). The exact
    // unit fingerprint identifies that target independently of the alias.
    let mut by_identity: BTreeMap<u64, &Unit> = BTreeMap::new();
    for unit in libraries.iter().filter(|unit| unit.compiler == compiler) {
        let previous = by_identity.insert(unit.fingerprint, unit);
        assert!(
            previous.is_none(),
            "ambiguous Cargo library identity for {}",
            unit.crate_name
        );
    }
    let root_unit = by_identity
        .get(&root.1)
        .expect("exact clean_auto dependency metadata");
    assert_eq!(root_unit.crate_name, "clean_auto");
    let mut artifact = root_unit
        .output
        .join(format!("libclean_auto-{}.rlib", root_unit.artifact_hash));
    if !artifact.is_file() {
        artifact.set_extension("rmeta");
    }
    assert!(
        artifact.is_file(),
        "the exact clean_auto library artifact must exist"
    );
    let mut pending = vec![root];
    let mut visited = BTreeSet::new();
    let mut search_paths = BTreeSet::new();
    while let Some(identity) = pending.pop() {
        if !visited.insert(identity.clone()) {
            continue;
        }
        // Build-script executables affect the fingerprint, but are not Rust
        // metadata dependencies of a library.
        if identity.0 == "build_script_build" {
            continue;
        }
        let unit = by_identity
            .get(&identity.1)
            .unwrap_or_else(|| panic!("missing exact Cargo library dependency {identity:?}"));
        search_paths.insert(unit.output.clone());
        pending.extend(unit.dependencies.iter().cloned());
    }
    Metadata {
        artifact,
        search_paths,
    }
}
