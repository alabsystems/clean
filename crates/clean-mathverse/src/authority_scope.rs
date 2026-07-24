// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Project-scoped authority-gate hashing.

use std::fs;
use std::path::{Path, PathBuf};

use crate::error::MathverseResult;

const AUTHORITY_SCOPE_SCHEMA: &str = "clean-authority-scope-v1";

/// Compute a deterministic source-tree digest for authority-gate evidence.
///
/// Runtime products and append-only evidence are intentionally excluded:
/// accepting a gate must depend on the project source/control inputs, not on
/// previous reports, build artifacts, or `.mathverse` logs.
pub fn project_source_tree_digest(root: impl AsRef<Path>) -> MathverseResult<String> {
    let root = root.as_ref();
    let mut files = Vec::new();
    collect_scope_files(root, root, &mut files)?;
    files.sort();

    let mut hasher = blake3::Hasher::new();
    hasher.update(AUTHORITY_SCOPE_SCHEMA.as_bytes());
    hasher.update(&[0]);
    for file in files {
        let rel = file
            .strip_prefix(root)
            .unwrap_or(file.as_path())
            .to_string_lossy()
            .replace('\\', "/");
        let bytes = fs::read(&file)?;
        hasher.update(rel.as_bytes());
        hasher.update(&[0]);
        hasher.update(&(bytes.len() as u64).to_le_bytes());
        hasher.update(&[0]);
        hasher.update(&bytes);
        hasher.update(&[0]);
    }

    Ok(hasher.finalize().to_hex().to_string())
}

/// Compute the goal hash an authority-gate attempt must carry for `root`.
pub fn authority_gate_goal_hash(
    root: impl AsRef<Path>,
    gate: &str,
    gate_scope: &str,
) -> MathverseResult<String> {
    let source_digest = project_source_tree_digest(root)?;
    Ok(authority_gate_goal_hash_from_scope(
        gate,
        gate_scope,
        &source_digest,
    ))
}

/// Compute an authority-gate goal hash from an already-computed scope digest.
#[must_use]
pub fn authority_gate_goal_hash_from_scope(
    gate: &str,
    gate_scope: &str,
    source_digest: &str,
) -> String {
    let mut hasher = blake3::Hasher::new();
    hasher.update(AUTHORITY_SCOPE_SCHEMA.as_bytes());
    hasher.update(&[0]);
    hasher.update(gate.as_bytes());
    hasher.update(&[0]);
    hasher.update(gate_scope.as_bytes());
    hasher.update(&[0]);
    hasher.update(source_digest.as_bytes());
    hasher.finalize().to_hex().to_string()
}

fn collect_scope_files(root: &Path, dir: &Path, files: &mut Vec<PathBuf>) -> MathverseResult<()> {
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        let file_type = entry.file_type()?;
        if file_type.is_dir() {
            if !is_ignored_dir(&path) {
                collect_scope_files(root, &path, files)?;
            }
        } else if file_type.is_file() && is_scope_file(root, &path) {
            files.push(path);
        }
    }
    Ok(())
}

fn is_ignored_dir(path: &Path) -> bool {
    matches!(
        path.file_name().and_then(|name| name.to_str()),
        Some(
            ".cake"
                | ".git"
                | ".lake"
                | ".mathverse"
                | "target"
                | "reports"
                | "node_modules"
                | ".claude"
                | ".gemini"
                | ".codex"
        )
    )
}

fn is_scope_file(root: &Path, path: &Path) -> bool {
    let Some(name) = path.file_name().and_then(|name| name.to_str()) else {
        return false;
    };
    if matches!(
        name,
        "lakefile.lean" | "lake-manifest.json" | "lean-toolchain" | "Cargo.toml" | "Cargo.lock"
    ) {
        return true;
    }
    if path
        .strip_prefix(root)
        .ok()
        .is_some_and(|rel| rel.starts_with("bakeoff"))
    {
        return true;
    }
    matches!(
        path.extension().and_then(|ext| ext.to_str()),
        Some("lean" | "rs" | "toml" | "json" | "tsv" | "md")
    )
}
