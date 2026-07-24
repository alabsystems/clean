// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Process operations: spawn/output, exit.
//!
//! `IO.Process.output` runs a subprocess and captures its stdout, stderr, and
//! exit code. The result is returned as an `IoValue::Pair` of exit code and
//! a pair of stdout/stderr strings, matching Lean 4's `IO.Process.Output`
//! structure.
//!
//! `IO.Process.exit` returns a special `IoError::ProcessExit` error that the
//! caller (e.g., the `#eval` driver) can interpret as a clean shutdown request.

use std::process::Command;

use super::{IoError, IoRuntime, IoValue};

impl IoRuntime {
    /// Run a subprocess and capture its output. Implements `IO.Process.output`.
    ///
    /// Returns a triple encoded as nested pairs:
    /// `(exitCode : Int, (stdout : String, stderr : String))`
    ///
    /// This matches how Lean 4's `IO.Process.Output` would be destructured.
    pub(super) fn exec_process_output(
        &self,
        cmd: &str,
        args: &[String],
    ) -> Result<IoValue, IoError> {
        let output = Command::new(cmd)
            .args(args)
            .output()
            .map_err(|e| IoError::ProcessError {
                cmd: cmd.to_owned(),
                source: e,
            })?;

        let exit_code = output.status.code().unwrap_or(-1);
        let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
        let stderr = String::from_utf8_lossy(&output.stderr).into_owned();

        // Encode as (exitCode, (stdout, stderr))
        let stdout_stderr = IoValue::Pair(
            Box::new(IoValue::String(stdout)),
            Box::new(IoValue::String(stderr)),
        );
        Ok(IoValue::Pair(
            Box::new(IoValue::Int(i64::from(exit_code))),
            Box::new(stdout_stderr),
        ))
    }
}
