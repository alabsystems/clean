// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Inspect the fixed and normalized paths used by the K3 diagnostics.

use crate::EvidenceCheckError;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

pub(super) fn canonical_root(root: &Path) -> Result<PathBuf, EvidenceCheckError> {
    root.canonicalize()
        .map_err(|error| EvidenceCheckError::Unavailable(format!("{}: {error}", root.display())))
}

/// The caller supplies a fixed, generated, or already validated relative path.
/// Inspect each component without following a link before opening the file.
pub(super) fn find_regular_file(
    root: &Path,
    relative: &str,
) -> Result<Option<PathBuf>, EvidenceCheckError> {
    let mut path = root.to_owned();
    let mut components = relative.split('/').peekable();
    while let Some(part) = components.next() {
        path.push(part);
        let metadata = match fs::symlink_metadata(&path) {
            Ok(metadata) => metadata,
            Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
            Err(error) => {
                return Err(EvidenceCheckError::Unavailable(format!(
                    "{}: {error}",
                    path.display()
                )));
            }
        };
        if metadata.file_type().is_symlink() {
            return Err(EvidenceCheckError::Invalid(format!(
                "{} is a symbolic link in K3 inputs",
                path.display()
            )));
        }
        if components.peek().is_none() {
            return Ok(metadata.is_file().then_some(path));
        }
        if !metadata.is_dir() {
            return Ok(None);
        }
    }
    Ok(None)
}
