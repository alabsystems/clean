// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Console I/O operations: println, print, eprintln, getLine.
//!
//! Stdout and stderr output is captured into internal buffers on the
//! [`IoRuntime`] so tests can inspect output without writing to the real
//! process streams. Stdin reads consume from a pre-loaded line buffer,
//! falling back to real stdin when the buffer is exhausted.

use std::io::{self, BufRead};

use super::{IoError, IoRuntime, IoValue};

impl IoRuntime {
    /// Print a line to stdout (appends newline). Implements `IO.println`.
    pub(super) fn exec_println(&self, s: &str) -> Result<IoValue, IoError> {
        self.stdout_buf.borrow_mut().push(s.to_owned());
        Ok(IoValue::Unit)
    }

    /// Print a string to stdout (no trailing newline). Implements `IO.print`.
    ///
    /// The string is still captured as a single entry in the stdout buffer.
    /// For test inspection, callers can distinguish print vs println by
    /// checking whether the action was `Print` or `PrintLn`.
    pub(super) fn exec_print(&self, s: &str) -> Result<IoValue, IoError> {
        self.stdout_buf.borrow_mut().push(s.to_owned());
        Ok(IoValue::Unit)
    }

    /// Print a line to stderr (appends newline). Implements `IO.eprintln`.
    pub(super) fn exec_eprintln(&self, s: &str) -> Result<IoValue, IoError> {
        self.stderr_buf.borrow_mut().push(s.to_owned());
        Ok(IoValue::Unit)
    }

    /// Read a single line from the stdin source. Implements `IO.getLine`.
    ///
    /// Consumes pre-loaded lines in FIFO order. When the buffer is exhausted,
    /// falls back to reading from real stdin.
    pub(super) fn exec_getline(&self) -> Result<IoValue, IoError> {
        let mut lines = self.stdin_lines.borrow_mut();
        if let Some(line) = lines.first().cloned() {
            lines.remove(0);
            Ok(IoValue::String(line))
        } else {
            // Fall back to real stdin.
            let stdin = io::stdin();
            let mut buf = String::new();
            stdin
                .lock()
                .read_line(&mut buf)
                .map_err(IoError::StdinError)?;
            // Strip trailing newline to match Lean behavior.
            if buf.ends_with('\n') {
                buf.pop();
                if buf.ends_with('\r') {
                    buf.pop();
                }
            }
            Ok(IoValue::String(buf))
        }
    }
}
