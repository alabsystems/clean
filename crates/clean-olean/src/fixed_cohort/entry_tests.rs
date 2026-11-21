// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Public-entry custody controls: fake bytes are never parsed or admitted.
use super::*;

fn fixture(directory: &Path, companion: Option<&str>) -> String {
    let bytes = b"custody control, not a mathematical artifact";
    for module in ["Library", "Model"] {
        std::fs::write(directory.join(format!("{module}.olean")), bytes).unwrap();
    }
    let mut model = serde_json::json!({"base":hash(bytes)});
    if let Some(part) = companion {
        let extension = if part == "ir" {
            "ir".to_owned()
        } else {
            format!("olean.{part}")
        };
        std::fs::write(directory.join(format!("Model.{extension}")), bytes).unwrap();
        model[part] = serde_json::json!(hash(bytes));
    }
    serde_json::json!({"schema":"entry-control", "ir_commit":"untrusted-data", "lean_version":"4.30.0-rc2", "lean_githash":"untrusted-data", "source_sha256":{}, "modules":{"Library":{"base":hash(bytes)},"Model":model}}).to_string()
}

fn both_entries_refuse(directory: &Path, manifest: &str, reason: &str) {
    let full = match open_replay(
        directory,
        manifest,
        "entry-control",
        &["Library"],
        &["Library.goal"],
    ) {
        Ok(_) => panic!("full-model entry must refuse before parsing"),
        Err(error) => error,
    };
    assert!(full.contains(reason), "{full}");
    let source = match open_source_context(directory, manifest, "entry-control", &["Model"], &[]) {
        Ok(_) => panic!("source-context entry must refuse before partition/loading"),
        Err(error) => error,
    };
    assert!(source.contains(reason), "{source}");
}

#[test]
fn both_public_entries_inventory_unimported_physical_artifacts_before_loading() {
    let directory = tempfile::tempdir().unwrap();
    let manifest = fixture(directory.path(), None);
    for extra in ["Unimported.olean", "Unimported.ir", "Library.ir"] {
        let path = directory.path().join(extra);
        std::fs::write(&path, b"unimported physical input").unwrap();
        both_entries_refuse(
            directory.path(),
            &manifest,
            "physical artifact population differs",
        );
        std::fs::remove_file(path).unwrap();
    }
}

#[cfg(unix)]
#[test]
fn both_public_entries_refuse_identical_byte_source_and_companion_symlinks() {
    use std::os::unix::fs::symlink;
    for part in [None, Some("ir"), Some("server"), Some("private")] {
        let directory = tempfile::tempdir().unwrap();
        let manifest = fixture(directory.path(), part);
        let extension = match part {
            None => "olean".to_owned(),
            Some("ir") => "ir".to_owned(),
            Some(part) => format!("olean.{part}"),
        };
        let path = directory.path().join(format!("Model.{extension}"));
        let outside = tempfile::NamedTempFile::new().unwrap();
        std::fs::copy(&path, outside.path()).unwrap();
        std::fs::remove_file(&path).unwrap();
        symlink(outside.path(), &path).unwrap();
        both_entries_refuse(directory.path(), &manifest, "symlink");
    }
}
