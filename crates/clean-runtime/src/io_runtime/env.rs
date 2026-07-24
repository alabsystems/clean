// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Environment operations: getEnv, currentDir.
//!
//! `IO.getEnv` reads a single environment variable, returning an empty string
//! when the variable is not set (matching Lean 4 behavior).
//!
//! `IO.currentDir` returns the current working directory as a string.

use super::{IoError, IoRuntime, IoValue};

impl IoRuntime {
    /// Read an environment variable, returning empty string if unset.
    /// Implements `IO.getEnv`.
    pub(super) fn exec_get_env(&self, name: &str) -> Result<IoValue, IoError> {
        match std::env::var(name) {
            Ok(val) => Ok(IoValue::String(val)),
            Err(std::env::VarError::NotPresent) => Ok(IoValue::String(String::new())),
            Err(e) => Err(IoError::EnvError {
                name: name.to_owned(),
                source: e,
            }),
        }
    }

    /// Get the current working directory. Implements `IO.currentDir`.
    pub(super) fn exec_current_dir(&self) -> Result<IoValue, IoError> {
        let dir = std::env::current_dir().map_err(IoError::CurrentDirError)?;
        Ok(IoValue::String(dir.to_string_lossy().into_owned()))
    }
}
