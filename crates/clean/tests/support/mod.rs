// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Shared helpers for Lake native-artifact integration fixtures.

use std::path::Path;

/// Stage the source-closure sidecar required by Clean's native-artifact
/// freshness gate.
///
/// Keep this byte-for-byte aligned with the production contract in
/// `clean-cli/src/cmd_lake/build.rs`: canonical paths are sorted, then each
/// source contributes its little-endian byte length followed by its bytes to
/// the BLAKE3 digest. Paths themselves are deliberately not hashed.
pub fn write_fresh_source_closure_sidecar(
    project_dir: &Path,
    artifact_name: &str,
    source_rel_paths: &[&str],
) {
    let mut sources: Vec<_> = source_rel_paths
        .iter()
        .map(|path| {
            let path = project_dir.join(path);
            std::fs::canonicalize(&path).unwrap_or(path)
        })
        .collect();
    sources.sort();

    let mut hasher = blake3::Hasher::new();
    for source in sources {
        let bytes = std::fs::read(&source)
            .unwrap_or_else(|err| panic!("read fixture source {}: {err}", source.display()));
        hasher.update(&(bytes.len() as u64).to_le_bytes());
        hasher.update(&bytes);
    }

    let sidecar = project_dir
        .join(".lake/build/bin")
        .join(format!("{artifact_name}.srchash"));
    std::fs::create_dir_all(sidecar.parent().expect("sidecar parent")).expect("create sidecar dir");
    std::fs::write(&sidecar, hasher.finalize().to_hex().to_string())
        .unwrap_or_else(|err| panic!("write fixture sidecar {}: {err}", sidecar.display()));
}
