// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! File I/O operations: readFile, writeFile, appendFile, readDir, pathExists,
//! removeFile.
//!
//! All paths are treated as UTF-8 strings, matching Lean 4's `System.FilePath`
//! representation. Errors are mapped to [`IoError::FileError`] with the path
//! and underlying OS error preserved.

use std::fs;
use std::io::Write;
use std::path::Path;

use super::{IoError, IoRuntime, IoValue};

impl IoRuntime {
    /// Read the full contents of a file as a UTF-8 string. Implements `IO.FS.readFile`.
    pub(super) fn exec_read_file(&self, path: &str) -> Result<IoValue, IoError> {
        let content = fs::read_to_string(path).map_err(|e| IoError::FileError {
            path: path.to_owned(),
            source: e,
        })?;
        Ok(IoValue::String(content))
    }

    /// Write content to a file (create or truncate). Implements `IO.FS.writeFile`.
    pub(super) fn exec_write_file(&self, path: &str, content: &str) -> Result<IoValue, IoError> {
        fs::write(path, content).map_err(|e| IoError::FileError {
            path: path.to_owned(),
            source: e,
        })?;
        Ok(IoValue::Unit)
    }

    /// Append content to a file (create if missing). Implements `IO.FS.appendFile`.
    pub(super) fn exec_append_file(&self, path: &str, content: &str) -> Result<IoValue, IoError> {
        let mut file = fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)
            .map_err(|e| IoError::FileError {
                path: path.to_owned(),
                source: e,
            })?;
        file.write_all(content.as_bytes())
            .map_err(|e| IoError::FileError {
                path: path.to_owned(),
                source: e,
            })?;
        Ok(IoValue::Unit)
    }

    /// List directory entries as a list of filename strings. Implements `IO.FS.readDir`.
    ///
    /// Returns `IoValue::List` of `IoValue::String` entries (just the file names,
    /// not full paths). Entries are sorted alphabetically for deterministic output.
    pub(super) fn exec_read_dir(&self, path: &str) -> Result<IoValue, IoError> {
        let entries = fs::read_dir(path).map_err(|e| IoError::FileError {
            path: path.to_owned(),
            source: e,
        })?;

        let mut names: Vec<String> = Vec::new();
        for entry in entries {
            let entry = entry.map_err(|e| IoError::FileError {
                path: path.to_owned(),
                source: e,
            })?;
            let name = entry.file_name().to_string_lossy().into_owned();
            names.push(name);
        }
        names.sort();

        let values = names.into_iter().map(IoValue::String).collect();
        Ok(IoValue::List(values))
    }

    /// Check whether a path exists. Implements `IO.FS.pathExists`.
    ///
    /// Returns `IoValue::Bool(true)` if the path exists, `false` otherwise.
    pub(super) fn exec_path_exists(&self, path: &str) -> Result<IoValue, IoError> {
        Ok(IoValue::Bool(Path::new(path).exists()))
    }

    /// Remove a file. Implements `IO.FS.removeFile`.
    ///
    /// Returns `IoValue::Unit` on success.
    pub(super) fn exec_remove_file(&self, path: &str) -> Result<IoValue, IoError> {
        fs::remove_file(path).map_err(|e| IoError::FileError {
            path: path.to_owned(),
            source: e,
        })?;
        Ok(IoValue::Unit)
    }
}
