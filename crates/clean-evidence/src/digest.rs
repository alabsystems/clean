// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The input byte framing used in the existing TrustCore evidence records.

use sha2::{Digest, Sha256};
use std::{fs, io, path::Path};
use walkdir::WalkDir;

/// SHA-256 of one input file, in lowercase hexadecimal.
pub fn sha256_file(path: &Path) -> io::Result<String> {
    Ok(hex_digest(&Sha256::digest(fs::read(path)?)))
}

/// Hash the regular Rust files under a module root, excluding its top-level
/// `tests/` directory. Each entry contributes its slash-separated relative
/// name, a NUL separator, a little-endian u64 byte length and the file bytes.
/// Names sort lexically. Directory symlinks and symlinked files are omitted.
pub fn sha256_module_tree(root: &Path) -> io::Result<String> {
    if !fs::symlink_metadata(root)?.is_dir() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("{} is not a directory", root.display()),
        ));
    }

    let tests = root.join("tests");
    let mut entries = Vec::new();
    for entry in WalkDir::new(root)
        .follow_links(false)
        .follow_root_links(false)
        .into_iter()
        .filter_entry(|entry| entry.path() != tests)
    {
        let entry = entry.map_err(io::Error::from)?;
        if !entry.file_type().is_file() || entry.path().extension() != Some("rs".as_ref()) {
            continue;
        }
        let relative = entry.path().strip_prefix(root).map_err(io::Error::other)?;
        let name = relative
            .to_str()
            .ok_or_else(|| io::Error::other(format!("non-UTF-8 input path: {relative:?}")))?
            .replace('\\', "/");
        entries.push((name, entry.into_path()));
    }
    entries.sort_unstable_by(|left, right| left.0.cmp(&right.0));
    if entries.windows(2).any(|pair| pair[0].0 == pair[1].0) {
        return Err(io::Error::other("duplicate normalized module path"));
    }

    let mut hasher = Sha256::new();
    for (name, path) in entries {
        let content = fs::read(path)?;
        hasher.update(name.as_bytes());
        hasher.update([0]);
        hasher.update((content.len() as u64).to_le_bytes());
        hasher.update(&content);
    }
    Ok(hex_digest(&hasher.finalize()))
}

fn hex_digest(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(bytes.len() * 2);
    for &byte in bytes {
        output.push(char::from(HEX[usize::from(byte >> 4)]));
        output.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    output
}
