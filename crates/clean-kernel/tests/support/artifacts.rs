// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Locate the library named by this test's Cargo dependency fingerprint.
//!
//! Trust puts each compilation unit in build/<package>/<unit>/out. Cargo's
//! conventional layout puts artifacts in deps and fingerprints beside it.
//! Neither layout permits choosing a library by modification time: another
//! feature set or compiler may have produced the newest file.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

pub struct Library {
    pub artifact: PathBuf,
    pub search_dirs: Vec<PathBuf>,
}

fn directories(path: &Path) -> Result<Vec<PathBuf>, String> {
    fs::read_dir(path)
        .map_err(|e| format!("read {}: {e}", path.display()))?
        .map(|entry| {
            entry
                .map(|e| e.path())
                .map_err(|e| format!("read directory entry: {e}"))
        })
        .filter(|entry| entry.as_ref().map_or(true, |p| p.is_dir()))
        .collect()
}

pub fn clean_kernel(executable: &Path, test_name: &str) -> Result<Library, String> {
    let out = executable.parent().ok_or("test executable has no parent")?;
    let unit = out.parent().ok_or("test directory has no parent")?;
    let per_unit = unit.join("fingerprint").is_dir();
    let (test_fingerprint, candidates, search_dirs) = if per_unit {
        let package = unit.parent().ok_or("unit has no package directory")?;
        let build = package.parent().ok_or("package has no build directory")?;
        let candidates = directories(package)?
            .into_iter()
            .map(|p| (p.join("fingerprint"), p.join("out")))
            .collect::<Vec<_>>();
        let mut search_dirs = BTreeSet::new();
        for package in directories(build)? {
            for unit in directories(&package)? {
                let out = unit.join("out");
                if out.is_dir() {
                    search_dirs.insert(out);
                }
            }
        }
        (
            unit.join("fingerprint")
                .join(format!("test-integration-test-{test_name}.json")),
            candidates,
            search_dirs.into_iter().collect(),
        )
    } else {
        let stem = executable
            .file_stem()
            .and_then(|s| s.to_str())
            .ok_or("test executable name is not UTF-8")?;
        let hash = stem
            .strip_prefix(&format!("{test_name}-"))
            .ok_or("test executable name has no target hash")?;
        let fingerprints = unit.join(".fingerprint");
        let candidates = directories(&fingerprints)?
            .into_iter()
            .filter(|p| {
                p.file_name()
                    .and_then(|s| s.to_str())
                    .is_some_and(|s| s.starts_with("clean-kernel-"))
            })
            .map(|p| (p, out.to_path_buf()))
            .collect::<Vec<_>>();
        (
            fingerprints
                .join(format!("clean-kernel-{hash}"))
                .join(format!("test-integration-test-{test_name}.json")),
            candidates,
            vec![out.to_path_buf()],
        )
    };
    let text = fs::read_to_string(&test_fingerprint)
        .map_err(|e| format!("read {}: {e}", test_fingerprint.display()))?;
    let record: serde_json::Value =
        serde_json::from_str(&text).map_err(|e| format!("parse test fingerprint: {e}"))?;
    let deps = record["deps"].as_array().ok_or("fingerprint has no deps")?;
    let matches = deps
        .iter()
        .filter(|dep| dep[1].as_str() == Some("clean_kernel"))
        .collect::<Vec<_>>();
    if matches.len() != 1 {
        return Err(format!(
            "expected one clean_kernel dependency, got {}",
            matches.len()
        ));
    }
    let expected = matches[0][3]
        .as_u64()
        .ok_or("clean_kernel dependency has no fingerprint")?;
    // Cargo writes the u64 fingerprint as eight little-endian hex bytes.
    let expected = expected
        .to_le_bytes()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect::<String>();
    let mut artifacts = BTreeSet::new();
    for (fingerprint_dir, artifact_dir) in candidates {
        let fingerprint = fingerprint_dir.join("lib-clean_kernel");
        if !fingerprint.is_file() {
            continue;
        }
        let actual = fs::read_to_string(&fingerprint)
            .map_err(|e| format!("read {}: {e}", fingerprint.display()))?;
        if actual.trim() != expected {
            continue;
        }
        let unit_name = if per_unit {
            fingerprint_dir.parent().and_then(Path::file_name)
        } else {
            fingerprint_dir.file_name()
        }
        .and_then(|s| s.to_str())
        .ok_or("library unit name is not UTF-8")?;
        let hash = if per_unit {
            unit_name
        } else {
            unit_name
                .strip_prefix("clean-kernel-")
                .ok_or("bad library unit name")?
        };
        let stem = artifact_dir.join(format!("libclean_kernel-{hash}"));
        let rlib = stem.with_extension("rlib");
        let rmeta = stem.with_extension("rmeta");
        let artifact = if rlib.is_file() { rlib } else { rmeta };
        if !artifact.is_file() {
            return Err(format!(
                "matching fingerprint has no library: {}",
                fingerprint.display()
            ));
        }
        artifacts.insert(artifact);
    }
    if artifacts.len() != 1 {
        return Err(format!(
            "expected one library matching fingerprint {expected}, got {}",
            artifacts.len()
        ));
    }
    Ok(Library {
        artifact: artifacts.into_iter().next().ok_or("missing library")?,
        search_dirs,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const TARGET: &str = "probe";
    const EXPECTED: u64 = 0x0102_0304_0506_0708;

    fn write(path: &Path, content: &str) {
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, content).unwrap();
    }

    fn record(path: &Path) {
        write(
            path,
            &format!(r#"{{"deps":[[0,"clean_kernel",false,{EXPECTED}]]}}"#),
        );
    }

    fn trust_library(package: &Path, hash: &str, fingerprint: &str) -> PathBuf {
        write(
            &package.join(hash).join("fingerprint/lib-clean_kernel"),
            fingerprint,
        );
        let artifact = package
            .join(hash)
            .join(format!("out/libclean_kernel-{hash}.rlib"));
        write(&artifact, "fixture");
        artifact
    }

    fn trust_test(package: &Path) -> PathBuf {
        record(&package.join("test/fingerprint/test-integration-test-probe.json"));
        let executable = package.join("test/out/probe-test");
        write(&executable, "fixture");
        executable
    }

    #[test]
    fn per_unit_uses_recorded_dependency_not_newer_wrong_library() {
        let temp = tempfile::tempdir().unwrap();
        let package = temp.path().join("build/clean-kernel");
        let executable = trust_test(&package);
        let expected = trust_library(&package, "right", "0807060504030201");
        trust_library(&package, "wrong", "1111111111111111");
        let dependency = temp.path().join("build/serde/unit/out");
        fs::create_dir_all(&dependency).unwrap();
        let found = clean_kernel(&executable, TARGET).unwrap();
        assert_eq!(found.artifact, expected);
        assert!(found.search_dirs.contains(&dependency));
    }

    #[test]
    fn conventional_layout_can_use_rmeta() {
        let temp = tempfile::tempdir().unwrap();
        let profile = temp.path();
        record(&profile.join(".fingerprint/clean-kernel-test/test-integration-test-probe.json"));
        write(
            &profile.join(".fingerprint/clean-kernel-right/lib-clean_kernel"),
            "0807060504030201",
        );
        let artifact = profile.join("deps/libclean_kernel-right.rmeta");
        write(&artifact, "fixture");
        let found = clean_kernel(&profile.join("deps/probe-test"), TARGET).unwrap();
        assert_eq!(found.artifact, artifact);
        assert_eq!(found.search_dirs, vec![profile.join("deps")]);
    }

    #[test]
    fn missing_dependency_does_not_fall_back_to_another_library() {
        let temp = tempfile::tempdir().unwrap();
        let package = temp.path().join("build/clean-kernel");
        let executable = trust_test(&package);
        trust_library(&package, "wrong", "1111111111111111");
        assert!(clean_kernel(&executable, TARGET)
            .err()
            .unwrap()
            .contains("got 0"));
    }

    #[test]
    fn ambiguous_dependency_is_refused() {
        let temp = tempfile::tempdir().unwrap();
        let package = temp.path().join("build/clean-kernel");
        let executable = trust_test(&package);
        trust_library(&package, "one", "0807060504030201");
        trust_library(&package, "two", "0807060504030201");
        assert!(clean_kernel(&executable, TARGET)
            .err()
            .unwrap()
            .contains("got 2"));
    }

    #[test]
    fn missing_matching_artifact_is_refused() {
        let temp = tempfile::tempdir().unwrap();
        let package = temp.path().join("build/clean-kernel");
        let executable = trust_test(&package);
        write(
            &package.join("right/fingerprint/lib-clean_kernel"),
            "0807060504030201",
        );
        assert!(clean_kernel(&executable, TARGET)
            .err()
            .unwrap()
            .contains("has no library"));
    }
}
